use std::collections::HashMap;

use crate::Result;
use spade_common::{
    id_tracker::ExprIdTracker,
    location_info::WithLocation,
    name::{NameID, Path},
};
use spade_diagnostics::{diag_anyhow, diag_bail};
use spade_mir::{Binding, Operator, Register, Statement, UnitName, ValueName};
use spade_typeinference::equation::TypedExpression;

use crate::monomorphisation::MirOutput;

fn perform_inlining(
    entity: &MirOutput,
    name_map: &HashMap<UnitName, MirOutput>,
    inlined: &mut HashMap<UnitName, MirOutput>,
    idtracker: &mut ExprIdTracker,
    type_ctx: &spade_typeinference::Context,
) -> Result<MirOutput> {
    if let Some(entity) = inlined.get(&entity.mir.name) {
        Ok(entity.clone())
    } else {
        let mut entity = entity.clone();

        let new_statements = entity
            .mir
            .statements
            .iter()
            .map(|stmt| match stmt {
                Statement::Binding(Binding {
                    name,
                    operator:
                        Operator::Instance {
                            name: iname,
                            params,
                            argument_names: _,
                            loc: _iloc,
                        },
                    operands,
                    ty: _,
                    loc,
                }) => {
                    let Some(target) = name_map.get(iname) else {
                        return Ok(vec![stmt.clone()]);
                    };

                    let target = perform_inlining(&target, name_map, inlined, idtracker, type_ctx)?;

                    if target.mir.inline {
                        if !params.is_empty() {
                            diag_bail!(
                                loc.unwrap_or(().nowhere()),
                                "Found inline mir entity with params"
                            );
                        }

                        let input_expr_map = target
                            .mir
                            .inputs
                            .iter()
                            .zip(operands.iter())
                            .map(|(input, operand)| (input.val_name.clone(), operand.clone()))
                            .collect::<Vec<_>>();

                        // Build a map of names in the callee to new unique names in the caller
                        let inner_expr_map = target
                            .mir
                            .statements
                            .iter()
                            .filter_map(|stmt| match stmt {
                                Statement::Binding(binding) => {
                                    Some((binding.name.clone(), ValueName::Expr(idtracker.next())))
                                }
                                Statement::Register(register) => {
                                    Some((register.name.clone(), ValueName::Expr(idtracker.next())))
                                }
                                Statement::Constant(name, _, _) => {
                                    Some((name.clone(), ValueName::Expr(idtracker.next())))
                                }
                                Statement::Assert(_) => None,
                                Statement::Set { .. } => None,
                                Statement::WalTrace { .. } => None,
                            })
                            .collect::<Vec<_>>();

                        for (source, dest) in &inner_expr_map {
                            let source_type = match source {
                                ValueName::Named(id, name, _) => {
                                    // NOTE: The path::from_strs here is a lie,
                                    // but we only need // this for lookups so
                                    // we're fine
                                    TypedExpression::Name(NameID(*id, Path::from_strs(&[&name])))
                                }
                                ValueName::Expr(expr_id) => TypedExpression::Id(*expr_id),
                            };
                            let dest_type = match dest {
                                ValueName::Named(_id, _name, _) => {
                                    diag_bail!(
                                        loc.unwrap_or(().nowhere()),
                                        "Found a ValueName::Named ({dest}) dest during inlining"
                                    )
                                }
                                ValueName::Expr(expr_id) => TypedExpression::Id(*expr_id),
                            };
                            if let Ok(source_ty) = target.type_state.type_of(&source_type) {
                                entity
                                    .type_state
                                    .add_equation(dest_type.clone(), source_ty);
                            };
                        }

                        let expr_map = input_expr_map
                            .into_iter()
                            .chain(inner_expr_map)
                            .collect::<HashMap<_, _>>();

                        target
                            .mir
                            .statements
                            .iter()
                            .map(|stmt| {
                                let map_name = |op: ValueName| {
                                    expr_map.get(&op).cloned().ok_or_else(|| {
                                        diag_anyhow!(
                                            loc.unwrap_or(().nowhere()),
                                            "Did not find a mapping for {op} while inlining"
                                        )
                                    })
                                };
                                Ok(match stmt.clone() {
                                    Statement::Binding(Binding {
                                        name,
                                        operator,
                                        operands,
                                        ty,
                                        loc,
                                    }) => Statement::Binding(Binding {
                                        name: map_name(name)?,
                                        operator,
                                        operands: operands
                                            .into_iter()
                                            .map(map_name)
                                            .collect::<Result<Vec<_>>>()?,
                                        ty,
                                        loc,
                                    }),
                                    Statement::Register(Register {
                                        name,
                                        ty,
                                        clock,
                                        reset,
                                        initial,
                                        value,
                                        loc,
                                        traced,
                                    }) => Statement::Register(Register {
                                        name: map_name(name)?,
                                        ty,
                                        clock: map_name(clock)?,
                                        reset: reset
                                            .map(|(trig, val)| -> Result<_> {
                                                Ok((map_name(trig)?, map_name(val)?))
                                            })
                                            .transpose()?,
                                        initial,
                                        value: map_name(value)?,
                                        loc,
                                        traced,
                                    }),
                                    Statement::Constant(name, ty, constant_value) => {
                                        Statement::Constant(map_name(name)?, ty, constant_value)
                                    }
                                    Statement::Assert(loc) => {
                                        Statement::Assert(loc.try_map(map_name)?)
                                    }
                                    Statement::Set { target, value } => Statement::Set {
                                        target: target.try_map(map_name)?,
                                        value: value.try_map(map_name)?,
                                    },
                                    Statement::WalTrace {
                                        name,
                                        val,
                                        suffix,
                                        ty,
                                    } => Statement::WalTrace {
                                        name: map_name(name)?,
                                        val: map_name(val)?,
                                        suffix,
                                        ty,
                                    },
                                })
                            })
                            .chain(vec![Ok(Statement::Binding(Binding {
                                name: name.clone(),
                                operator: Operator::Alias,
                                operands: vec![expr_map
                                    .get(&target.mir.output)
                                    .ok_or_else(|| {
                                        diag_anyhow!(
                                            loc.unwrap_or(().nowhere()),
                                            "Did not find a mapping for {}",
                                            target.mir.output
                                        )
                                    })?
                                    .clone()],
                                ty: target.mir.output_type,
                                loc: loc.clone(),
                            }))])
                            .collect()
                    } else {
                        Ok(vec![stmt.clone()])
                    }
                }
                _ => Ok(vec![stmt.clone()]),
            })
            .collect::<Result<Vec<_>>>()?
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();

        entity.mir.statements = new_statements;

        inlined.insert(entity.mir.name.clone(), entity.clone());
        Ok(entity)
    }
}

pub fn do_inlining(
    mut mir_entities: Vec<MirOutput>,
    idtracker: &mut ExprIdTracker,
    type_ctx: &spade_typeinference::Context,
) -> Result<Vec<MirOutput>> {
    let name_map = mir_entities
        .iter()
        .cloned()
        .map(|e| (e.mir.name.clone(), e.clone()))
        .collect::<HashMap<_, _>>();

    let mut inlined = HashMap::new();

    mir_entities
        .iter_mut()
        .filter_map(|entity| {
            if !entity.mir.inline {
                Some(perform_inlining(
                    entity,
                    &name_map,
                    &mut inlined,
                    idtracker,
                    type_ctx,
                ))
            } else {
                None
            }
        })
        .collect()
}
