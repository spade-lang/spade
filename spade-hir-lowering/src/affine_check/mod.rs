use spade_common::{
    location_info::{Loc, WithLocation},
    name::NameID,
};
use spade_hir::{
    expression::NamedArgument, symbol_table::SymbolTable, ArgumentList, Expression, Register,
    Statement, TypeList, TypeSpec,
};
use spade_typeinference::TypeState;
use tracing::trace;

use self::{
    affine_state::{AffineState, UsageInfo},
    error::{Error, Result},
};

mod affine_state;
pub mod error;

pub struct AffineCtx<'a> {
    pub type_state: &'a TypeState,
    pub symtab: &'a SymbolTable,
    pub types: &'a TypeList,
}

/// Checks for affine type errors in a function-like. Reports errors if an affine
/// type is not used exactly once
#[tracing::instrument(level = "trace", skip_all)]
pub fn check_affine_types(
    inputs: &[(Loc<NameID>, Loc<TypeSpec>)],
    body: &Loc<Expression>,
    type_state: &TypeState,
    symtab: &SymbolTable,
    types: &TypeList,
) -> Result<()> {
    let ctx = AffineCtx {
        types,
        symtab,
        type_state,
    };

    let mut affine_state = AffineState::new();

    for (name, _) in inputs {
        affine_state.push_new_name(name, &ctx)
    }

    visit_expression(body, &mut affine_state, &ctx)?;

    affine_state.consume_expression(&body)?;

    affine_state.check_unused().map_err(|(alias, witness)| {
        // TODO: Rewrite this using the new error reporting
        Error::UnusedAffineItem {
            definition: alias.loc(),
            witness,
        }
    })?;

    Ok(())
}

#[tracing::instrument(level = "trace", skip_all)]
fn visit_expression(
    expr: &Loc<Expression>,
    affine_state: &mut AffineState,
    ctx: &AffineCtx,
) -> Result<()> {
    let produces_new_resource = match &expr.kind {
        spade_hir::ExprKind::Identifier(_) => false,
        spade_hir::ExprKind::IntLiteral(_) => true,
        spade_hir::ExprKind::BoolLiteral(_) => true,
        spade_hir::ExprKind::TupleLiteral(_) => true,
        spade_hir::ExprKind::ArrayLiteral(_) => true,
        spade_hir::ExprKind::Index(_, _) => true,
        // TODO
        spade_hir::ExprKind::TupleIndex(_, _) => false,
        // TODO
        spade_hir::ExprKind::FieldAccess(_, _) => false,
        // TODO
        spade_hir::ExprKind::BinaryOperator(_, _, _) => true,
        // TODO
        spade_hir::ExprKind::UnaryOperator(_, _) => true,
        // TODO
        spade_hir::ExprKind::Match(_, _) => true,
        spade_hir::ExprKind::Block(_) => true,
        spade_hir::ExprKind::FnCall(_, _) => true,
        spade_hir::ExprKind::EntityInstance(_, _) => true,
        spade_hir::ExprKind::PipelineInstance { .. } => true,
        spade_hir::ExprKind::If(_, _, _) => true,
        spade_hir::ExprKind::PipelineRef { stage: _, name: _, declares_name: _ } => false,
    };

    if produces_new_resource {
        trace!("Pushing expression {}", expr.id);
        affine_state.push_new_expression(&expr.map_ref(|e| e.id), ctx);
    }

    match &expr.kind {
        spade_hir::ExprKind::Identifier(name) => {
            affine_state.add_alias_name(expr.id.at_loc(expr), &name.clone().at_loc(expr), ctx)
            // affine_state.consume_name(&name.clone().at_loc(expr))?
        }
        spade_hir::ExprKind::IntLiteral(_) => {}
        spade_hir::ExprKind::BoolLiteral(_) => {}
        spade_hir::ExprKind::TupleLiteral(inner) => {
            for (i, expr) in inner.iter().enumerate() {
                visit_expression(expr, affine_state, ctx)?;
                trace!("visited tuple literal member {i}");
                affine_state.consume_expression(&expr)?;
            }
        }
        spade_hir::ExprKind::ArrayLiteral(inner) => {
            for expr in inner {
                visit_expression(expr, affine_state, ctx)?;
                trace!("Consuming array literal inner");
                affine_state.consume_expression(&expr)?;
            }
        }
        spade_hir::ExprKind::Index(target, idx) => {
            visit_expression(target, affine_state, ctx)?;
            visit_expression(idx, affine_state, ctx)?;
            // Since array indices are not static, we have to just consume here
            affine_state.consume_expression(target)?;
            affine_state.consume_expression(idx)?;
        }
        spade_hir::ExprKind::TupleIndex(base, idx) => {
            visit_expression(base, affine_state, ctx)?;
            affine_state.alias_tuple_memeber(expr.id.at_loc(expr), base.id, idx)
        }
        spade_hir::ExprKind::FieldAccess(base, field) => {
            visit_expression(base, affine_state, ctx)?;
            affine_state.alias_struct_memeber(expr.id.at_loc(expr), base.id, field)
        }
        spade_hir::ExprKind::BinaryOperator(lhs, _, rhs) => {
            visit_expression(lhs, affine_state, ctx)?;
            visit_expression(rhs, affine_state, ctx)?;
            // TODO
        }
        spade_hir::ExprKind::UnaryOperator(_, operand) => {
            visit_expression(operand, affine_state, ctx)?;
            // TODO
        }
        // TODO
        spade_hir::ExprKind::Match(cond, variants) => {
            visit_expression(cond, affine_state, ctx)?;
            for (pat, expr) in variants {
                affine_state.push_pattern(pat, &ctx);
                visit_expression(expr, affine_state, ctx)?;
            }
        }
        spade_hir::ExprKind::Block(b) => {
            for statement in &b.statements {
                match &statement.inner {
                    Statement::Binding(pattern, _, value) => {
                        visit_expression(value, affine_state, ctx)?;
                        affine_state.consume_expression(&value)?;
                        affine_state.push_pattern(pattern, ctx)
                    }
                    Statement::Register(reg) => {
                        let Register {
                            pattern,
                            clock,
                            reset,
                            value,
                            value_type: _,
                        } = &reg.inner;

                        visit_expression(clock, affine_state, ctx)?;
                        if let Some((trig, val)) = &reset {
                            visit_expression(trig, affine_state, ctx)?;
                            visit_expression(val, affine_state, ctx)?;
                        }

                        visit_expression(value, affine_state, ctx)?;

                        affine_state.consume_expression(&value)?;

                        affine_state.push_pattern(&pattern, ctx)
                    }
                    Statement::Declaration(names) => {
                        for name in names {
                            affine_state.push_new_name(name, ctx)
                        }
                    }
                    Statement::PipelineRegMarker => {}
                    Statement::Label(_) => {}
                    Statement::Assert(_) => {}
                    Statement::Set { .. } => {}
                }
            }
            visit_expression(&b.result, affine_state, ctx)?;
            trace!("Consuming block {}", expr.id);
            affine_state.consume_expression(&b.result)?;
        }
        spade_hir::ExprKind::FnCall(_, list)
        | spade_hir::ExprKind::EntityInstance(_, list)
        | spade_hir::ExprKind::PipelineInstance {
            depth: _,
            name: _,
            args: list,
        } => match &list.inner {
            ArgumentList::Named(args) => {
                for arg in args {
                    match arg {
                        NamedArgument::Full(_, expr) | NamedArgument::Short(_, expr) => {
                            visit_expression(expr, affine_state, ctx)?;
                            affine_state.consume_expression(expr)?;
                        }
                    }
                }
            }
            ArgumentList::Positional(args) => {
                for arg in args {
                    visit_expression(arg, affine_state, ctx)?;
                    affine_state.consume_expression(arg)?;
                    // TODO: Consume
                }
            }
        },
        spade_hir::ExprKind::If(cond, on_true, on_false) => {
            visit_expression(cond, affine_state, ctx)?;
            visit_expression(on_true, affine_state, ctx)?;
            visit_expression(on_false, affine_state, ctx)?;
            // TODO
        }
        spade_hir::ExprKind::PipelineRef { stage: _, name, declares_name } => {
            if *declares_name {
                affine_state.push_new_name(name, ctx);
            }
            affine_state.add_alias_name(expr.id.at_loc(expr), &name.clone(), ctx)
            // affine_state.consume_name(&name)?
        }
    }
    Ok(())
}
