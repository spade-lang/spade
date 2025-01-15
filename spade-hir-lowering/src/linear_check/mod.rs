use num::ToPrimitive;
use tracing::trace;

use spade_common::{
    location_info::{Loc, WithLocation},
    name::{NameID, Path},
};
use spade_diagnostics::diagnostic::Subdiagnostic;
use spade_diagnostics::{diag_bail, Diagnostic};
use spade_hir::{
    expression::{NamedArgument, UnaryOperator},
    symbol_table::SymbolTable,
    ArgumentList, Binding, ExprKind, Expression, PipelineRegMarkerExtra, Register, Statement,
    TypeList, TypeSpec,
};
use spade_typeinference::TypeState;

use self::linear_state::{is_linear, LinearState};
use crate::error::Result;

mod linear_state;

pub struct LinearCtx<'a> {
    pub type_state: &'a TypeState,
    pub symtab: &'a SymbolTable,
    pub types: &'a TypeList,
}

/// Checks for linear type errors in a function-like. Reports errors if an linear
/// type is not used exactly once
pub fn check_linear_types(
    inputs: &[(Loc<NameID>, Loc<TypeSpec>)],
    body: &Loc<Expression>,
    type_state: &TypeState,
    symtab: &SymbolTable,
    types: &TypeList,
) -> Result<()> {
    let ctx = LinearCtx {
        types,
        symtab,
        type_state,
    };

    let mut linear_state = LinearState::new();

    for (name, _) in inputs {
        linear_state.push_new_name(name, &ctx)
    }

    visit_expression(body, &mut linear_state, &ctx)?;

    linear_state.consume_expression(body)?;

    linear_state.check_unused().map_err(|(alias, witness)| {
        let self_description = match &alias.inner {
            linear_state::ItemReference::Name(n) => format!("{n}{}", witness.motivation()),
            linear_state::ItemReference::Anonymous(_) => {
                format!("This has a field {} that", witness.motivation())
            }
        };
        Diagnostic::error(&alias, format!("{self_description} is unused"))
            .primary_label(format!("{self_description} is unused"))
            .note(format!(
                "{self_description} is a ~& value which must be set"
            ))
    })?;

    Ok(())
}

pub fn visit_statement(
    stmt: &Loc<Statement>,
    linear_state: &mut LinearState,
    ctx: &LinearCtx,
) -> Result<()> {
    match &stmt.inner {
        Statement::Binding(Binding {
            pattern,
            ty: _,
            value,
            wal_trace: _,
        }) => {
            visit_expression(value, linear_state, ctx)?;
            linear_state.consume_expression(value)?;
            linear_state.push_pattern(pattern, ctx)?
        }
        Statement::Register(reg) => {
            let Register {
                pattern,
                clock,
                reset,
                initial,
                value,
                value_type: _,
                attributes: _,
            } = &reg;

            linear_state.push_pattern(pattern, ctx)?;

            visit_expression(clock, linear_state, ctx)?;
            if let Some((trig, val)) = &reset {
                visit_expression(trig, linear_state, ctx)?;
                visit_expression(val, linear_state, ctx)?;
            }
            initial
                .as_ref()
                .map(|i| visit_expression(i, linear_state, ctx))
                .transpose()?;

            visit_expression(value, linear_state, ctx)?;

            linear_state.consume_expression(value)?;
        }
        Statement::Declaration(names) => {
            for name in names {
                linear_state.push_new_name(name, ctx)
            }
        }
        Statement::PipelineRegMarker(cond) => match cond {
            Some(PipelineRegMarkerExtra::Count {
                count: _,
                count_typeexpr_id: _,
            }) => {}
            Some(PipelineRegMarkerExtra::Condition(cond)) => {
                visit_expression(cond, linear_state, ctx)?;
            }
            None => {}
        },
        Statement::Label(_) => {}
        Statement::Assert(_) => {}
        Statement::WalSuffixed { .. } => {}
        Statement::Set { target, value } => {
            visit_expression(target, linear_state, ctx)?;
            visit_expression(value, linear_state, ctx)?;
            linear_state.consume_expression(target)?;
            linear_state.consume_expression(value)?;
        }
    }
    Ok(())
}

#[tracing::instrument(level = "trace", skip_all)]
fn visit_expression(
    expr: &Loc<Expression>,
    linear_state: &mut LinearState,
    ctx: &LinearCtx,
) -> Result<()> {
    let produces_new_resource = match &expr.kind {
        spade_hir::ExprKind::Identifier(_) => false,
        spade_hir::ExprKind::IntLiteral(_, _) => true,
        spade_hir::ExprKind::TypeLevelInteger(_) => true,
        spade_hir::ExprKind::BoolLiteral(_) => true,
        spade_hir::ExprKind::BitLiteral(_) => true,
        spade_hir::ExprKind::TupleLiteral(_) => true,
        spade_hir::ExprKind::ArrayLiteral(_) => true,
        spade_hir::ExprKind::ArrayShorthandLiteral(_, _) => true,
        spade_hir::ExprKind::CreatePorts => true,
        spade_hir::ExprKind::Index(_, _) => true,
        spade_hir::ExprKind::RangeIndex { .. } => true,
        spade_hir::ExprKind::TupleIndex(_, _) => false,
        spade_hir::ExprKind::FieldAccess(_, _) => false,
        spade_hir::ExprKind::BinaryOperator(_, _, _) => true,
        spade_hir::ExprKind::UnaryOperator(_, _) => true,
        spade_hir::ExprKind::Match(_, _) => true,
        spade_hir::ExprKind::Block(_) => true,
        spade_hir::ExprKind::Call { .. } => true,
        spade_hir::ExprKind::If(_, _, _) => true,
        spade_hir::ExprKind::TypeLevelIf(_, _, _) => true,
        spade_hir::ExprKind::StageValid | spade_hir::ExprKind::StageReady => true,
        spade_hir::ExprKind::PipelineRef {
            stage: _,
            name: _,
            declares_name: _,
            depth_typeexpr_id: _,
        } => false,
        spade_hir::ExprKind::MethodCall { .. } => diag_bail!(
            expr,
            "method call should have been lowered to function by this point"
        ),
        spade_hir::ExprKind::Null => false,
    };

    if produces_new_resource {
        trace!("Pushing expression {}", expr.id.0);
        linear_state.push_new_expression(&expr.map_ref(|e| e.id), ctx);
    }

    match &expr.kind {
        spade_hir::ExprKind::Identifier(name) => {
            linear_state.add_alias_name(expr.id.at_loc(expr), &name.clone().at_loc(expr))?
        }
        spade_hir::ExprKind::IntLiteral(_, _) => {}
        spade_hir::ExprKind::TypeLevelInteger(_) => {}
        spade_hir::ExprKind::BoolLiteral(_) => {}
        spade_hir::ExprKind::BitLiteral(_) => {}
        spade_hir::ExprKind::StageValid | spade_hir::ExprKind::StageReady => {}
        spade_hir::ExprKind::TupleLiteral(inner) => {
            for (i, expr) in inner.iter().enumerate() {
                visit_expression(expr, linear_state, ctx)?;
                trace!("visited tuple literal member {i}");
                linear_state.consume_expression(expr)?;
            }
        }
        spade_hir::ExprKind::ArrayLiteral(inner) => {
            for expr in inner {
                visit_expression(expr, linear_state, ctx)?;
                trace!("Consuming array literal inner");
                linear_state.consume_expression(expr)?;
            }
        }
        spade_hir::ExprKind::ArrayShorthandLiteral(inner, _) => {
            visit_expression(inner, linear_state, ctx)?;
            // FIXME: should allow `[instance of ~&T; 0]` and `[instance of ~&T; 1]` here
            // try to consume twice. if we get an error, add a note
            linear_state.consume_expression(inner)?;
            if let Err(mut diag) = linear_state.consume_expression(inner) {
                diag.push_subdiagnostic(Subdiagnostic::span_note(
                    expr,
                    "The resource is used in this array initialization",
                ));
                return Err(diag);
            }
        }
        spade_hir::ExprKind::CreatePorts => {}
        spade_hir::ExprKind::Index(target, idx_expr) => {
            visit_expression(target, linear_state, ctx)?;
            visit_expression(idx_expr, linear_state, ctx)?;

            if is_linear(
                &ctx.type_state
                    .concrete_type_of(target, ctx.symtab, ctx.types)?,
            ) {
                let idx = match &idx_expr.kind {
                    ExprKind::IntLiteral(value, _) => value,
                    _ => {
                        return Err(Diagnostic::error(
                            expr,
                            "Array with mutable wires cannot be indexed by non-constant values",
                        )
                        .primary_label("Array with mutable wires indexed by non-constant")
                        .secondary_label(idx_expr.loc(), "Expected constant"))
                    }
                };

                let idx = idx.to_u128().ok_or_else(|| {
                    Diagnostic::error(
                        target.loc(),
                        "Array indices > 2^64 are not allowed on mutable wires",
                    )
                })?;

                // If the array has mutable wires, we need to guarantee statically that they are
                // used exactly once. To do that, we need to ensure that the array is indexed by a
                // statically known index. However, this check is only required if the array actually
                // has linear type
                linear_state.alias_array_member(
                    expr.id.at_loc(expr),
                    target.id,
                    &idx.at_loc(idx_expr),
                )?;
            } else {
                linear_state.consume_expression(target)?;
            }

            linear_state.consume_expression(idx_expr)?;
        }
        spade_hir::ExprKind::RangeIndex {
            target,
            start: _,
            end: _,
        } => {
            visit_expression(target, linear_state, ctx)?;
            // We don't track individual elements of arrays, so we'll have to consume the
            // whole thing here
            linear_state.consume_expression(target)?;
        }
        spade_hir::ExprKind::TupleIndex(base, idx) => {
            visit_expression(base, linear_state, ctx)?;
            linear_state.alias_tuple_member(expr.id.at_loc(expr), base.id, idx)?
        }
        spade_hir::ExprKind::FieldAccess(base, field) => {
            visit_expression(base, linear_state, ctx)?;
            linear_state.alias_struct_member(expr.id.at_loc(expr), base.id, field)?
        }
        spade_hir::ExprKind::BinaryOperator(lhs, _, rhs) => {
            visit_expression(lhs, linear_state, ctx)?;
            visit_expression(rhs, linear_state, ctx)?;
            linear_state.consume_expression(lhs)?;
            linear_state.consume_expression(rhs)?;
        }
        spade_hir::ExprKind::UnaryOperator(op, operand) => {
            visit_expression(operand, linear_state, ctx)?;
            match op.inner {
                UnaryOperator::Sub
                | UnaryOperator::Not
                | UnaryOperator::BitwiseNot
                | UnaryOperator::Reference => {
                    linear_state.consume_expression(operand)?;
                }
                UnaryOperator::Dereference => {}
            }
        }
        spade_hir::ExprKind::Match(cond, variants) => {
            visit_expression(cond, linear_state, ctx)?;
            for (pat, expr) in variants {
                linear_state.push_pattern(pat, ctx)?;
                visit_expression(expr, linear_state, ctx)?;
            }
        }
        spade_hir::ExprKind::Block(b) => {
            for statement in &b.statements {
                visit_statement(statement, linear_state, ctx)?;
            }
            if let Some(result) = &b.result {
                visit_expression(result, linear_state, ctx)?;
                trace!("Consuming block {}", expr.id.0);
                linear_state.consume_expression(result)?;
            }
        }
        spade_hir::ExprKind::Call {
            kind: _,
            callee,
            args: list,
            turbofish: _,
        } => {
            // The read_mut_wire function is special and should not consume the port
            // it is reading.
            // FIXME: When spade is more generic and can handle the * operator
            // doing more fancy things, we should consider getting rid of this function
            let consume = ctx
                .symtab
                .try_lookup_final_id(&Path::from_strs(&["std", "ports", "read_mut_wire"]).nowhere())
                .map(|n| n != callee.inner)
                .unwrap_or(true);

            match &list.inner {
                ArgumentList::Named(args) => {
                    for arg in args {
                        match arg {
                            NamedArgument::Full(_, expr) | NamedArgument::Short(_, expr) => {
                                visit_expression(expr, linear_state, ctx)?;
                                if consume {
                                    linear_state.consume_expression(expr)?;
                                }
                            }
                        }
                    }
                }
                ArgumentList::Positional(args) => {
                    for arg in args {
                        visit_expression(arg, linear_state, ctx)?;
                        if consume {
                            linear_state.consume_expression(arg)?;
                        }
                    }
                }
            }
        }
        spade_hir::ExprKind::If(cond, on_true, on_false) => {
            visit_expression(cond, linear_state, ctx)?;
            visit_expression(on_true, linear_state, ctx)?;
            visit_expression(on_false, linear_state, ctx)?;
        }
        spade_hir::ExprKind::PipelineRef {
            stage: _,
            name,
            declares_name,
            depth_typeexpr_id: _,
        } => {
            if *declares_name {
                linear_state.push_new_name(name, ctx);
            }
            linear_state.add_alias_name(expr.id.at_loc(expr), &name.clone())?
        }
        spade_hir::ExprKind::TypeLevelIf(_, _, _) => {
            diag_bail!(expr, "Type level if should have been lowered")
        }
        spade_hir::ExprKind::MethodCall { .. } => diag_bail!(
            expr,
            "method call should have been lowered to function by this point"
        ),
        spade_hir::ExprKind::Null { .. } => {
            diag_bail!(expr, "Null expression created before linear check")
        }
    }
    Ok(())
}
