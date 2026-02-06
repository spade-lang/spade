use std::collections::BTreeMap;
use std::rc::Rc;

use spade_common::id_tracker::{ExprIdTracker, NameIdTracker};
use spade_common::location_info::{Loc, WithLocation};
use spade_common::name::{NameID, Path};
use spade_diagnostics::diag_anyhow;
use spade_mir::types::Type;
use spade_mir::{Binding, Operator, Register, Statement, UnitName, ValueName};
use spade_typeinference::equation::{KnownTypeVar, TypedExpression};
use spade_typeinference::{HasType, TypeState};

use crate::monomorphisation::MirOutput;
use crate::Result;

#[derive(Clone)]
enum InlinedStatements<'a> {
    Normal(Vec<&'a Statement>),
    InlinedCall {
        outer_output_name: &'a ValueName,
        inner_output_name: &'a ValueName,
        ty: &'a Type,
        loc: &'a Option<Loc<()>>,
        target: InlinedEntity<'a>,
        name_map: Rc<BTreeMap<ValueName, ValueName>>,
        input_expr_map: Rc<Vec<(ValueName, ValueName)>>,
        type_map: Rc<Vec<(ValueName, KnownTypeVar)>>,
    },
}

impl<'a> InlinedStatements<'a> {
    fn finalize(
        &self,
        name_map: &BTreeMap<ValueName, ValueName>,
        idtracker: &ExprIdTracker,
        type_state: &mut TypeState,
        new_statements: &mut Vec<Statement>,
        nameidtracker: &NameIdTracker,
    ) -> Result<()> {
        let get_final_name = |source_name| name_map.get(source_name).unwrap_or(source_name).clone();
        match self {
            InlinedStatements::Normal(stmts) => {
                new_statements.reserve(stmts.len());
                for stmt in stmts {
                    let new = match stmt {
                        Statement::Error => Statement::Error,
                        Statement::Binding(binding) => Statement::Binding(Binding {
                            name: get_final_name(&binding.name),
                            operator: binding.operator.clone(),
                            operands: binding
                                .operands
                                .iter()
                                .map(|op| get_final_name(op))
                                .collect(),
                            ty: binding.ty.clone(),
                            loc: binding.loc,
                        }),
                        Statement::Register(reg) => Statement::Register(Register {
                            name: get_final_name(&reg.name),
                            ty: reg.ty.clone(),
                            clock: get_final_name(&reg.clock),
                            reset: match &reg.reset {
                                Some((trig, val)) => {
                                    Some((get_final_name(trig), get_final_name(val)))
                                }
                                None => None,
                            },
                            initial: reg.initial.clone(),
                            value: get_final_name(&reg.value),
                            loc: reg.loc.clone(),
                            traced: None,
                        }),
                        Statement::Constant(value_name, ty, constant_value) => Statement::Constant(
                            get_final_name(value_name),
                            ty.clone(),
                            constant_value.clone(),
                        ),
                        Statement::Assert(val) => {
                            Statement::Assert(get_final_name(&val).at_loc(val))
                        }
                        Statement::Set { target, value } => Statement::Set {
                            target: get_final_name(target).at_loc(target),
                            value: get_final_name(value).at_loc(value),
                        },
                        Statement::WalTrace {
                            name,
                            val,
                            suffix,
                            ty,
                        } => Statement::WalTrace {
                            name: get_final_name(name),
                            val: get_final_name(val),
                            suffix: suffix.clone(),
                            ty: ty.clone(),
                        },
                    };
                    new_statements.push(new);
                }
                Ok(())
            }
            InlinedStatements::InlinedCall {
                outer_output_name,
                inner_output_name,
                type_map,
                ty,
                loc,
                target,
                input_expr_map,
                name_map: target_name_map,
            } => {
                let new_name_map = target_name_map
                    .keys()
                    .chain(name_map.keys())
                    .chain(type_map.iter().map(|(n, _)| n))
                    .map(|k| {
                        let new_name = match k {
                            ValueName::Named(_, name, value_name_source) => ValueName::Named(
                                nameidtracker.next(),
                                name.clone(),
                                value_name_source.clone(),
                            ),
                            ValueName::Expr(_) => ValueName::Expr(idtracker.next()),
                        };
                        (k.clone(), new_name)
                    })
                    .chain(
                        input_expr_map
                            .iter()
                            .map(|(from, to)| (from.clone(), get_final_name(to))),
                    )
                    .collect::<BTreeMap<_, _>>();

                for (dest, source_ty) in type_map.iter() {
                    let dest = new_name_map.get(dest).unwrap_or(dest);
                    let dest_type = match dest {
                        ValueName::Named(id, name, _) => {
                            // NOTE: The name here is somewhat artificial, but since we only do actual
                            // comparison based on the ID, it is fine
                            TypedExpression::Name(NameID(*id, Path::from_strs(&[name])))
                        }
                        ValueName::Expr(expr_id) => TypedExpression::Id(*expr_id),
                    };

                    let tvar = source_ty.insert(type_state);
                    type_state.add_equation(dest_type.clone(), tvar);
                }

                let result_binding = Statement::Binding(Binding {
                    name: name_map
                        .get(outer_output_name)
                        .unwrap_or(&outer_output_name)
                        .clone(),
                    operator: Operator::Alias,
                    operands: vec![new_name_map
                        .get(&inner_output_name)
                        .ok_or_else(|| {
                            diag_anyhow!(
                                loc.unwrap_or(().nowhere()),
                                "Did not find the output in an entity being inlined"
                            )
                        })?
                        .clone()],
                    ty: (*ty).clone(),
                    loc: (*loc).clone(),
                });

                for stmts in &target.statements {
                    stmts.finalize(
                        &new_name_map,
                        idtracker,
                        type_state,
                        new_statements,
                        nameidtracker,
                    )?;
                }
                new_statements.push(result_binding);

                Ok(())
            }
        }
    }
}

#[derive(Clone)]
struct InlinedEntity<'a> {
    base_entity: &'a MirOutput,
    statements: Vec<InlinedStatements<'a>>,
}

impl<'a> InlinedEntity<'a> {
    fn finalize(
        &self,
        idtracker: &ExprIdTracker,
        nameidtracker: &NameIdTracker,
    ) -> Result<MirOutput> {
        let mut result = self.base_entity.clone();
        let mut new_statements = vec![];
        for stmt in &self.statements {
            stmt.finalize(
                &BTreeMap::new(),
                idtracker,
                &mut result.type_state,
                &mut new_statements,
                nameidtracker,
            )?;
        }
        result.mir.statements = new_statements;
        Ok(result)
    }
}

fn perform_inlining<'a>(
    target: &'a MirOutput,
    source_map: &'a BTreeMap<UnitName, MirOutput>,
    idtracker: &ExprIdTracker,
    nameidtracker: &NameIdTracker,
    cache: &'_ mut BTreeMap<UnitName, InlinedEntity<'a>>,
) -> Result<InlinedEntity<'a>> {
    if let Some(cached) = cache.get(&target.mir.name) {
        Ok(cached.clone())
    } else {
        let Some(source) = source_map.get(&target.mir.name) else {
            panic!(
                "Attempted to inline an entity which did not exist ({})",
                target.mir.name
            );
        };

        let mut stmts_iter = source.mir.statements.iter();
        let mut current_normal = vec![];
        let mut new_stmts = vec![];
        while let Some(stmt) = stmts_iter.next() {
            match stmt {
                Statement::Binding(Binding {
                    name: output_name,
                    operator:
                        Operator::Instance {
                            name: callee,
                            params: _, // Type parameters are not important for inlining
                            argument_names: _, // Argument names are also unimportant
                            loc: _,
                            verilog_attr_groups: _,
                        },
                    operands,
                    ty,
                    loc,
                }) => {
                    // Check if this should be inlined
                    if let Some(callee) = source_map.get(callee) {
                        if callee.mir.inline {
                            new_stmts.push(InlinedStatements::Normal(std::mem::take(
                                &mut current_normal,
                            )));

                            let input_expr_map = callee
                                .mir
                                .inputs
                                .iter()
                                .zip(operands.iter())
                                .map(|(input, operand)| (input.val_name.clone(), operand.clone()))
                                .collect::<Vec<_>>();

                            let name_generator = |current_name: &ValueName| match current_name {
                                ValueName::Named(_, path, value_name_source) => ValueName::Named(
                                    nameidtracker.next(),
                                    path.clone(),
                                    value_name_source.clone(),
                                ),
                                ValueName::Expr(_) => ValueName::Expr(idtracker.next()),
                            };

                            // Build a map of names in the callee to new unique names in the caller
                            let inner_expr_map = callee
                                .mir
                                .statements
                                .iter()
                                .filter_map(|stmt| match stmt {
                                    Statement::Binding(binding) => {
                                        Some((binding.name.clone(), name_generator(&binding.name)))
                                    }
                                    Statement::Register(register) => Some((
                                        register.name.clone(),
                                        name_generator(&register.name),
                                    )),
                                    Statement::Constant(name, _, _) => {
                                        Some((name.clone(), name_generator(name)))
                                    }
                                    Statement::Error => None,
                                    Statement::Assert(_) => None,
                                    Statement::Set { .. } => None,
                                    Statement::WalTrace { .. } => None,
                                })
                                .collect::<Vec<_>>();

                            let mut type_map = vec![];
                            for (source, dest) in &inner_expr_map {
                                let source_type = match source {
                                    ValueName::Named(id, name, _) => {
                                        // NOTE: The path::from_strs here is a lie,
                                        // but we only need this for lookups so
                                        // we're fine
                                        TypedExpression::Name(NameID(
                                            *id,
                                            Path::from_strs(&[&name]),
                                        ))
                                    }
                                    ValueName::Expr(expr_id) => TypedExpression::Id(*expr_id),
                                };

                                let source_ty =
                                    source_type.try_get_type(&callee.type_state).and_then(|ty| {
                                        ty.resolve(&callee.type_state)
                                            .into_known(&callee.type_state)
                                    });

                                if let Some(source_ty) = source_ty {
                                    type_map.push((dest.clone(), source_ty));
                                };
                            }

                            let expr_map = inner_expr_map.into_iter().collect::<BTreeMap<_, _>>();

                            let inlined_callee = perform_inlining(
                                callee,
                                source_map,
                                idtracker,
                                nameidtracker,
                                cache,
                            )?;

                            new_stmts.push(InlinedStatements::InlinedCall {
                                outer_output_name: output_name,
                                target: inlined_callee,
                                name_map: Rc::new(expr_map),
                                type_map: Rc::new(type_map),
                                inner_output_name: &callee.mir.output,
                                input_expr_map: Rc::new(input_expr_map),
                                ty,
                                loc,
                            });
                        } else {
                            current_normal.push(stmt)
                        }
                    } else {
                        current_normal.push(stmt)
                    }
                }
                other_stmt => current_normal.push(other_stmt),
            }
        }
        new_stmts.push(InlinedStatements::Normal(current_normal));

        cache.insert(
            target.mir.name.clone(),
            InlinedEntity {
                base_entity: target,
                statements: new_stmts,
            },
        );
        Ok(cache.get(&target.mir.name).unwrap().clone())
    }
}

pub fn do_inlining(
    mut mir_entities: Vec<MirOutput>,
    idtracker: &ExprIdTracker,
    nameidtracker: &NameIdTracker,
) -> Result<Vec<MirOutput>> {
    let source_map = mir_entities
        .iter()
        .cloned()
        .map(|e| (e.mir.name.clone(), e.clone()))
        .collect::<BTreeMap<_, _>>();

    let mut cache = BTreeMap::new();
    let partial = mir_entities
        .iter_mut()
        .filter(|entity| !entity.mir.inline)
        .map(|entity| perform_inlining(entity, &source_map, idtracker, nameidtracker, &mut cache))
        .collect::<Result<Vec<_>>>()?;

    partial
        .into_iter()
        .map(|inlined| inlined.finalize(idtracker, nameidtracker))
        .collect()
}
