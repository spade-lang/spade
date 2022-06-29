use std::collections::HashMap;

use local_impl::local_impl;
use spade_common::{id_tracker::ExprIdTracker, location_info::Loc, name::NameID};
use spade_hir::{
    symbol_table::FrozenSymtab, ExprKind, Expression, ItemList, Pattern, Pipeline, Statement,
};
use spade_mir as mir;
use spade_typeinference::TypeState;

use crate::{
    error::Error, monomorphisation::MonoState, substitution::Substitutions, Context, ExprLocal,
    Manglable, MirLowerable, NameIDLocal, Result, StatementLocal, TypeStateLocal,
};

pub fn handle_pattern(pat: &Pattern, live_vars: &mut Vec<NameID>) {
    // Add this variable to the live vars list
    for name in pat.get_names() {
        live_vars.push(name.clone());
    }
}

pub fn generate_pipeline<'a>(
    pipeline: &Pipeline,
    types: &TypeState,
    symtab: &mut FrozenSymtab,
    idtracker: &mut ExprIdTracker,
    item_list: &ItemList,
    // Map of names generated by codegen to the original name in the source code.
    name_map: &mut HashMap<NameID, NameID>,
    mono_state: &mut MonoState,
) -> Result<mir::Entity> {
    let Pipeline {
        head: _,
        name,
        inputs,
        body,
    } = pipeline;

    let clock = &inputs[0].0;

    let mut subs = Substitutions::new();

    // Skip because the clock should not be pipelined
    for input in inputs.iter().skip(1).map(|var| var.0.clone()) {
        subs.set_available(input, 0)
    }

    let mut statements = vec![];

    let (body_statements, result) = if let ExprKind::Block(block) = &body.kind {
        (&block.statements, &block.result)
    } else {
        panic!("Pipeline body was not a block");
    };

    // Lower inputs to make sure they are available before adding the pipeline registers
    // for them
    let lowered_inputs = inputs
        .iter()
        .map(|(name_id, _)| {
            let name = name_id.1.tail().to_string();
            let val_name = name_id.value_name();
            let ty = types
                .type_of_name(name_id, symtab.symtab(), &item_list.types)
                .to_mir_type();

            (name, val_name, ty)
        })
        .collect::<Vec<_>>();

    for statement in body_statements {
        match &statement.inner {
            Statement::Binding(pat, _, expr) => {
                let time = expr.inner.kind.available_in()?;
                for name in pat.get_names() {
                    subs.set_available(name, time)
                }
            }
            Statement::Register(reg) => {
                let time = reg.inner.value.kind.available_in()?;
                for name in reg.pattern.get_names() {
                    subs.set_available(name, time)
                }
            }
            Statement::Declaration(_) => todo!(),
            Statement::PipelineRegMarker => {
                let live_vars = subs.next_stage(symtab);

                // Generate pipeline regs for previous live vars
                for reg in &live_vars {
                    if name_map
                        .insert(reg.new.clone(), reg.original.clone())
                        .is_some()
                    {
                        // NOTE: Panic because this should not occur in user code
                        panic!("inserted duplicate in name map");
                    }

                    statements.push(mir::Statement::Register(mir::Register {
                        name: reg.new.value_name(),
                        ty: types
                            .type_of_name(&reg.original, symtab.symtab(), &item_list.types)
                            .to_mir_type(),
                        clock: clock.value_name(),
                        reset: None,
                        value: reg.previous.value_name(),
                    }));
                }
            }
            Statement::Label(_) => {
                // Labels have no effect on codegen
            }
            Statement::Assert(_) => {
                // Assertions have no effect on pipeline state
            }
        }
    }

    let mut ctx = Context {
        symtab,
        idtracker,
        types,
        subs: &mut subs,
        item_list,
        mono_state,
    };

    for statement in body_statements {
        statements.append(&mut statement.lower(&mut ctx)?);
    }

    statements.append(&mut result.lower(&mut ctx)?);

    let output = result.variable(&subs);

    let output_type = types
        .expr_type(result, symtab.symtab(), &item_list.types)?
        .to_mir_type();

    Ok(mir::Entity {
        name: name.mangled(),
        inputs: lowered_inputs,
        output: output?,
        output_type,
        statements,
    })
}

/// Computes the time at which the specified expressions will be available. If there
/// is a mismatch, an error is returned
pub fn try_compute_availability(
    exprs: &[impl std::borrow::Borrow<Loc<Expression>>],
) -> Result<usize> {
    let mut result = None;
    for expr in exprs {
        let a = expr.borrow().kind.available_in()?;

        result = match result {
            None => Some(a),
            Some(prev) if a == prev => result,
            // NOTE: Safe index. This branch can only be reached in iteration 2 of the loop
            _ => {
                return Err(Error::AvailabilityMismatch {
                    prev: exprs[0].borrow().clone().map(|_| result.unwrap()),
                    new: expr.borrow().clone().map(|_| a),
                })
            }
        }
    }
    Ok(result.unwrap_or(0))
}

#[local_impl]
impl PipelineAvailability for ExprKind {
    fn available_in(&self) -> Result<usize> {
        match self {
            ExprKind::Identifier(_) => Ok(0),
            ExprKind::IntLiteral(_) => Ok(0),
            ExprKind::BoolLiteral(_) => Ok(0),
            ExprKind::TupleLiteral(inner) => try_compute_availability(inner),
            ExprKind::ArrayLiteral(elems) => try_compute_availability(elems),
            ExprKind::Index(lhs, idx) => try_compute_availability(&[lhs.as_ref(), idx.as_ref()]),
            ExprKind::TupleIndex(lhs, _) => lhs.inner.kind.available_in(),
            ExprKind::FieldAccess(lhs, _) => lhs.inner.kind.available_in(),
            ExprKind::EntityInstance(_, _) | ExprKind::FnCall(_, _) => Ok(0),
            ExprKind::BinaryOperator(lhs, _, rhs) => {
                try_compute_availability(&[lhs.as_ref(), rhs.as_ref()])
            }
            ExprKind::UnaryOperator(_, val) => val.inner.kind.available_in(),
            ExprKind::Match(_, values) => {
                try_compute_availability(&values.iter().map(|(_, expr)| expr).collect::<Vec<_>>())
            }
            ExprKind::Block(inner) => {
                // NOTE: Do we want to allow delayed values inside blocks? That could lead to some
                // strange issues like
                // {
                //      let x = inst(10) subpipe();
                //      x // Will appear as having availability 1
                // }
                inner.result.kind.available_in()
            }
            ExprKind::PipelineInstance {
                depth,
                name: _,
                args: _,
            } => {
                // FIXME: Re-add this check to allow nested pipelines
                // let arg_availability = try_compute_availability(
                //     &args.iter().map(|arg| &arg.value).collect::<Vec<_>>(),
                // )?;
                Ok(depth.inner as usize)
            }
            ExprKind::If(_, t, f) => try_compute_availability(&[t.as_ref(), f.as_ref()]),
            ExprKind::PipelineRef { .. } => Ok(0),
        }
    }
}
