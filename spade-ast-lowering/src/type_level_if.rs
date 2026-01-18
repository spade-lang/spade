use spade_common::location_info::Loc;
use spade_common::location_info::WithLocation;
use spade_common::name::Identifier;
use spade_common::name::PathSegment;
use spade_diagnostics::diag_bail;
use spade_diagnostics::Diagnostic;
use spade_hir::expression::CallKind;
use spade_hir::expression::Safety;
use spade_hir::symbol_table::Thing;
use spade_hir::ArgumentList;
use spade_hir::Binding;
use spade_hir::Block;
use spade_hir::ExecutableItem;
use spade_hir::Expression;
use spade_hir::PatternKind;
use spade_hir::Statement;
use spade_hir::TypeExpression;
use spade_hir::UnitKind;
use spade_hir::UnitName;
use spade_hir::{ExprKind, Unit};

use crate::Context;
use crate::Result;

// For pipelining reasons, if we have a unit like
// {
//     reg;
//     gen if ... {
//         result1
//     } else {
//         result2
//     }
// }
// we want to convert it into
// {
//     gen if ... {
//         reg;
//         result1
//     } else {
//         reg;
//         result2
//     }
// }
// This performs that replacement
pub fn absorb_statements(
    body: &Loc<Expression>,
    outer_statements: &Vec<Loc<Statement>>,
    ctx: &mut Context,
) -> Result<Loc<Expression>> {
    body.try_map_ref(|expr| match &expr.kind {
        ExprKind::TypeLevelIf(cond, on_true, on_false) => Ok(ExprKind::TypeLevelIf(
            cond.clone(),
            Box::new(absorb_statements(on_true, outer_statements, ctx)?),
            Box::new(absorb_statements(on_false, outer_statements, ctx)?),
        )
        .with_id(ctx.idtracker.next())),
        ExprKind::Block(block) => Ok(ExprKind::Block(Box::new(Block {
            statements: outer_statements
                .iter()
                .chain(block.statements.iter())
                .cloned()
                .collect(),
            result: block.result.clone(),
        }))
        .with_id(ctx.idtracker.next())),
        ExprKind::Error => Ok(ExprKind::Error.with_id(ctx.idtracker.next())),
        _ => Err(Diagnostic::bug(
            body,
            "The body of a gen if can only be a block or another gen if",
        )
        .primary_label(format!("Invalid body of gen if"))),
    })
}

pub fn expand_type_level_if(mut unit: Loc<Unit>, ctx: &mut Context) -> Result<Loc<Unit>> {
    let Ok(body) = unit.body.assume_block() else {
        unit.body.kind = ExprKind::Error;
        return Ok(unit);
    };

    let expand_body =
        |new_body: &Loc<Expression>, name_segment: PathSegment, ctx: &mut Context| -> Result<_> {
            let mut new_unit = unit.clone();
            let absorbed = absorb_statements(&new_body, &body.statements, ctx)?;
            new_unit.body = match &absorbed.kind {
                ExprKind::TypeLevelIf(_, _, _) => {
                    let loc = absorbed.loc();
                    ExprKind::Block(Box::new(Block {
                        statements: vec![],
                        result: Some(absorbed),
                    }))
                    .with_id(ctx.idtracker.next())
                    .at_loc(&loc)
                }
                ExprKind::Block(_) => absorbed,
                ExprKind::Error => absorbed,
                _ => diag_bail!(absorbed, "Non tlif or body"),
            };

            let new_name = unit.name.name_id().1.clone().push_segment(name_segment);
            let new_nameid = ctx.symtab.add_thing(
                new_name,
                Thing::Unit(new_unit.head.clone().at_loc(&unit)),
                None,
            );
            new_unit.name = UnitName::WithID(new_nameid.clone().at_loc(&unit.head.name));

            let new_unit = expand_type_level_if(new_unit, ctx)?;
            ctx.item_list.add_executable(
                new_nameid.clone().at_loc(&unit.head.name),
                ExecutableItem::Unit(new_unit),
            )?;

            Ok(new_nameid.at_loc(&unit.head.name))
        };

    let call_expanded = |expanded_name, ctx: &mut Context| {
        let kind = match &unit.head.unit_kind.inner {
            UnitKind::Function(_) => CallKind::Function,
            UnitKind::Entity => CallKind::Entity(().nowhere()),
            UnitKind::Pipeline {
                depth,
                depth_typeexpr_id: _,
            } => CallKind::Pipeline {
                inst_loc: ().nowhere(),
                depth: depth.clone(),
                depth_typeexpr_id: ctx.idtracker.next(),
            },
        };

        let args = ArgumentList::Positional(
            unit.inputs
                .iter()
                .map(|(name, _)| {
                    ExprKind::Identifier(name.inner.clone())
                        .with_id(ctx.idtracker.next())
                        .at_loc(&name)
                })
                .collect(),
        )
        .at_loc(&unit.head.inputs);

        let turbofish = if !unit.head.unit_type_params.is_empty() {
            Some(
                ArgumentList::Positional(
                    unit.head
                        .unit_type_params
                        .iter()
                        .map(|p| {
                            TypeExpression::TypeSpec(spade_hir::TypeSpec::Generic(p.name.clone()))
                                .at_loc(p)
                        })
                        .collect(),
                )
                .at_loc(&unit),
            )
        } else {
            None
        };

        ExprKind::Call {
            kind,
            callee: expanded_name,
            args,
            turbofish,
            safety: Safety::Unsafe, // This essentially skips the safety check as we don't want to virtually generate a unsafe block around the generated call
            verilog_attr_groups: vec![],
        }
        .with_id(ctx.idtracker.next())
        .at_loc(&unit.body)
    };

    match body.result.as_ref().map(|e| &e.kind) {
        Some(ExprKind::TypeLevelIf(cond, on_true, on_false)) => {
            let on_true = expand_body(&on_true, PathSegment::IfT, ctx)?;
            let on_false = expand_body(&on_false, PathSegment::IfF, ctx)?;

            let new_on_true = call_expanded(on_true, ctx);
            let new_on_false = call_expanded(on_false, ctx);

            let new_result =
                ExprKind::TypeLevelIf(cond.clone(), Box::new(new_on_true), Box::new(new_on_false))
                    .with_id(ctx.idtracker.next())
                    .at_loc(&unit.body);

            let result_name = ctx
                .symtab
                .add_local_variable(Identifier::intern("result").at_loc(&unit));

            let result_binding = Statement::Binding(Binding {
                pattern: PatternKind::Name {
                    name: result_name.clone().at_loc(&unit),
                    pre_declared: false,
                }
                .with_id(ctx.idtracker.next())
                .at_loc(&unit),
                ty: None,
                value: new_result,
                wal_trace: None,
            })
            .at_loc(&unit);

            let pipeline_depth = match &unit.head.unit_kind.inner {
                UnitKind::Function(_) => None,
                UnitKind::Entity => None,
                UnitKind::Pipeline {
                    depth,
                    depth_typeexpr_id: _,
                } => Some(depth),
            };
            let pipeline_reg = pipeline_depth
                .map(|depth| {
                    vec![Statement::PipelineRegMarker(Some(
                        spade_hir::PipelineRegMarkerExtra::Count {
                            count: depth.clone(),
                            count_typeexpr_id: ctx.idtracker.next(),
                        },
                    ))
                    .at_loc(&depth)]
                })
                .unwrap_or_default();

            unit.body = ExprKind::Block(Box::new(Block {
                statements: vec![result_binding]
                    .into_iter()
                    .chain(pipeline_reg)
                    .collect(),
                result: Some(
                    ExprKind::Identifier(result_name)
                        .with_id(ctx.idtracker.next())
                        .at_loc(&unit),
                ),
            }))
            .with_id(ctx.idtracker.next())
            .at_loc(&unit.body);

            Ok(expand_type_level_if(unit, ctx)?)
        }
        _ => Ok(unit),
    }
}
