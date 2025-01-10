use spade_common::location_info::Loc;
use spade_common::location_info::WithLocation;
use spade_common::name::Identifier;
use spade_hir::expression::CallKind;
use spade_hir::symbol_table::Thing;
use spade_hir::ArgumentList;
use spade_hir::Block;
use spade_hir::ExecutableItem;
use spade_hir::Expression;
use spade_hir::TypeExpression;
use spade_hir::UnitKind;
use spade_hir::UnitName;
use spade_hir::{ExprKind, Unit};

use crate::Context;
use crate::Result;

pub fn expand_type_level_if(mut unit: Loc<Unit>, ctx: &mut Context) -> Result<Loc<Unit>> {
    let body = unit.body.assume_block();

    let expand_body =
        |new_body: &Loc<Expression>, name_suffix: &str, ctx: &mut Context| -> Result<_> {
            let mut new_unit = unit.clone();
            new_unit.body = ExprKind::Block(Box::new(Block {
                statements: body.statements.clone(),
                result: Some(new_body.clone()),
            }))
            .with_id(ctx.idtracker.next())
            .at_loc(&new_body);

            let new_name = unit
                .name
                .name_id()
                .1
                .clone()
                .push_ident(Identifier(name_suffix.to_string()).nowhere());
            let new_nameid = ctx
                .symtab
                .add_thing(new_name, Thing::Unit(new_unit.head.clone().at_loc(&unit)));
            new_unit.name = UnitName::WithID(new_nameid.clone().at_loc(&unit.head.name));
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

        // TODO: What does this do we are in a method
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

        let turbofish = Some(
            ArgumentList::Positional(
                unit.head
                    .get_type_params()
                    .iter()
                    .map(|p| {
                        TypeExpression::TypeSpec(spade_hir::TypeSpec::Generic(p.name_id.clone().at_loc(p)))
                            .at_loc(p)
                    })
                    .collect(),
            )
            .at_loc(&unit),
        );

        ExprKind::Call {
            kind,
            callee: expanded_name,
            args,
            turbofish,
        }
        .with_id(ctx.idtracker.next())
        .at_loc(&unit.body)
    };

    match body.result.as_ref().map(|e| &e.kind) {
        Some(ExprKind::TypeLevelIf(cond, on_true, on_false)) => {
            let on_true = expand_body(&on_true, "T", ctx)?;
            let on_false = expand_body(&on_false, "F", ctx)?;

            let new_on_true = call_expanded(on_true, ctx);
            let new_on_false = call_expanded(on_false, ctx);

            let new_result =
                ExprKind::TypeLevelIf(cond.clone(), Box::new(new_on_true), Box::new(new_on_false))
                    .with_id(ctx.idtracker.next())
                    .at_loc(&unit.body);

            unit.body = ExprKind::Block(Box::new(Block {
                statements: vec![],
                result: Some(new_result),
            }))
            .with_id(ctx.idtracker.next())
            .at_loc(&unit.body);

            Ok(unit)
        }
        _ => Ok(unit),
    }
}
