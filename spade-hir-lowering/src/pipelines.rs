use spade_common::{id_tracker::ExprIdTracker, name::NameID};
use spade_hir::{symbol_table::FrozenSymtab, ExprKind, ItemList, Pattern, Pipeline, Statement};
use spade_mir as mir;
use spade_typeinference::TypeState;

use crate::{
    substitution::Substitutions, ExprLocal, MirLowerable, NameIDLocal, Result, StatementLocal,
    TypeStateLocal,
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
        subs.set_available(input)
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
            let name = name_id.1.to_string();
            let val_name = name_id.value_name();
            let ty = types
                .type_of_name(name_id, symtab.symtab(), &item_list.types)
                .to_mir_type();

            (name, val_name, ty)
        })
        .collect::<Vec<_>>();

    for statement in body_statements {
        match &statement.inner {
            Statement::Binding(pat, _, _) => {
                for name in pat.get_names() {
                    subs.set_available(name)
                }
            }
            Statement::Register(reg) => {
                for name in reg.pattern.get_names() {
                    subs.set_available(name)
                }
            }
            Statement::Declaration(_) => todo!(),
            Statement::PipelineRegMarker => {
                let live_vars = subs.next_stage(symtab);

                // Generate pipeline regs for previous live vars
                for reg in &live_vars {
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
        }
    }

    for statement in body_statements {
        statements.append(&mut statement.lower(symtab, idtracker, types, &mut subs, item_list)?);
    }

    statements.append(&mut result.lower(symtab, idtracker, types, &mut subs, item_list)?);

    let output = result.variable(&subs);

    let output_type = types
        .expr_type(&result, symtab.symtab(), &item_list.types)?
        .to_mir_type();

    Ok(mir::Entity {
        name: name.1.to_string(),
        inputs: lowered_inputs,
        output: output?,
        output_type,
        statements,
    })
}
