use num::BigUint;
use spade_common::location_info::Loc;
use spade_diagnostics::{diag_bail, Diagnostic};
use spade_hir::{symbol_table::FrozenSymtab, Expression, ItemList};
use spade_typeinference::TypeState;

use crate::MirLowerable;

use super::pass::Pass;

pub struct DisallowZeroSize<'a> {
    pub type_state: &'a TypeState,
    pub items: &'a ItemList,
    pub symtab: &'a FrozenSymtab,
}

impl<'a> Pass for DisallowZeroSize<'a> {
    fn visit_expression(&mut self, expression: &mut Loc<Expression>) -> crate::error::Result<()> {
        let type_of = |expr: &Loc<Expression>| -> Result<_, Diagnostic> {
            self.type_state
                .expr_type(expr, self.symtab.symtab(), &self.items.types)
                .map(|t| t.to_mir_type())
        };

        match &expression.kind {
            spade_hir::ExprKind::Identifier(_) => Ok(()),
            spade_hir::ExprKind::TypeLevelInteger(_) | spade_hir::ExprKind::IntLiteral(_, _) => {
                Ok(())
            }
            spade_hir::ExprKind::BoolLiteral(_) => Ok(()),
            spade_hir::ExprKind::BitLiteral(_) => Ok(()),
            spade_hir::ExprKind::CreatePorts => Ok(()),
            spade_hir::ExprKind::TupleLiteral(_) => Ok(()),
            spade_hir::ExprKind::ArrayLiteral(_) => Ok(()),
            spade_hir::ExprKind::ArrayShorthandLiteral(_, _) => Ok(()),
            spade_hir::ExprKind::Index(_, _) => Ok(()),
            spade_hir::ExprKind::RangeIndex { .. } => Ok(()),
            spade_hir::ExprKind::TupleIndex(_, _) => Ok(()),
            spade_hir::ExprKind::FieldAccess(_, _) => Ok(()),
            spade_hir::ExprKind::MethodCall { .. } => Ok(()),
            spade_hir::ExprKind::Call { .. } => Ok(()),
            spade_hir::ExprKind::BinaryOperator(lhs, op, rhs) => {
                let check = |operand| {
                    if type_of(operand)?.size() == BigUint::ZERO {
                        Err(Diagnostic::error(
                            operand,
                            format!("Operator {op} does not support zero size operands"),
                        )
                        .primary_label("Zero size operand")
                        .secondary_label(op, "is not supported by this operator"))
                    } else {
                        Ok(())
                    }
                };
                check(lhs)?;
                check(rhs)?;
                Ok(())
            }
            spade_hir::ExprKind::UnaryOperator(unary_operator, operand) => {
                match &unary_operator.inner {
                    spade_hir::expression::UnaryOperator::Sub
                    | spade_hir::expression::UnaryOperator::Not
                    | spade_hir::expression::UnaryOperator::BitwiseNot => {
                        if type_of(operand)?.size() == BigUint::ZERO {
                            Err(Diagnostic::error(
                                operand.loc(),
                                format!(
                                    "Operator {unary_operator} does not support zero size operands"
                                ),
                            )
                            .primary_label("Zero size operand")
                            .secondary_label(
                                unary_operator.loc(),
                                format!("is not supported by {unary_operator}"),
                            ))
                        } else {
                            Ok(())
                        }
                    }
                    spade_hir::expression::UnaryOperator::Dereference
                    | spade_hir::expression::UnaryOperator::Reference => Ok(()),
                }
            }
            spade_hir::ExprKind::Match(_cond, operands) => {
                if let Some((_cond, val)) = operands.first() {
                    if type_of(val)?.size() == BigUint::ZERO {
                        return Err(Diagnostic::error(
                            val,
                            "Match expressions cannot produce zero size values",
                        )
                        .primary_label("Zero size value"));
                    }
                }
                Ok(())
            }
            spade_hir::ExprKind::Block(_) => Ok(()),
            spade_hir::ExprKind::If(_, _, _) => Ok(()),
            spade_hir::ExprKind::TypeLevelIf(_, _, _) => {
                diag_bail!(expression.loc(), "Type level if should have been lowered")
            }
            spade_hir::ExprKind::PipelineRef { .. } => Ok(()),
            spade_hir::ExprKind::StageValid => Ok(()),
            spade_hir::ExprKind::StageReady => Ok(()),
            spade_hir::ExprKind::Null => Ok(()),
        }
    }

    fn visit_unit(&mut self, _unit: &mut spade_hir::Unit) -> crate::error::Result<()> {
        Ok(())
    }
}
