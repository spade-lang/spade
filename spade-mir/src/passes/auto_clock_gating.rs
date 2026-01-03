use num::BigUint;
use spade_common::{id_tracker::ExprIdTracker, location_info::Loc, num_ext::InfallibleToBigUint};

use crate::{types::Type, Binding, Operator, Register, Statement, ValueName};

use super::MirPass;

/// Splits an 2 variant enum with variant 0 having payload of size 0 and variant 1
/// having another size into a tag and payload
fn split_trivial_tag_value(
    value: &ValueName,
    variants: &Vec<Vec<Type>>,
    statements: &mut Vec<Statement>,
    expr_idtracker: &ExprIdTracker,
    loc: &Option<Loc<()>>,
) -> (ValueName, ValueName) {
    let tag_name = ValueName::Expr(expr_idtracker.next());
    let payload_name = ValueName::Expr(expr_idtracker.next());

    let payload_size = variants[1].iter().map(|v| v.size()).sum::<BigUint>();
    statements.push(Statement::Binding(Binding {
        name: tag_name.clone(),
        operator: Operator::RangeIndexBits {
            start: payload_size.clone(),
            end_exclusive: &payload_size + 1u32.to_biguint(),
        },
        operands: vec![value.clone()],
        ty: Type::Bool,
        loc: *loc,
    }));
    statements.push(Statement::Binding(Binding {
        name: payload_name.clone(),
        operator: Operator::RangeIndexBits {
            start: 0u32.to_biguint(),
            end_exclusive: payload_size,
        },
        operands: vec![value.clone()],
        ty: Type::Tuple(variants[1].clone()),
        loc: *loc,
    }));

    (tag_name, payload_name)
}

impl Register {
    fn perform_trivial_gating(&self, expr_idtracker: &ExprIdTracker) -> Option<Vec<Statement>> {
        // FIXME: For now, we'll not split registers initial values because those would need
        // special treatment since their values are comptime-evaluated
        if self.initial.is_some() {
            return None;
        }
        match &self.ty {
            crate::types::Type::Enum(variants) => {
                if variants.len() == 2 && variants[0].len() == 0 {
                    let mut new_statements = vec![];

                    let tag_reg_name = ValueName::Expr(expr_idtracker.next());
                    let payload_reg_name = ValueName::Expr(expr_idtracker.next());
                    let payload_reg_value_name = ValueName::Expr(expr_idtracker.next());

                    let payload_type = Type::Tuple(variants[1].clone());

                    let (value_tag, value_payload) = split_trivial_tag_value(
                        &self.value,
                        variants,
                        &mut new_statements,
                        expr_idtracker,
                        &self.loc,
                    );
                    let (reset_tag, reset_payload) =
                        if let Some((reset_trig, reset_val)) = &self.reset {
                            let (tag, payload) = split_trivial_tag_value(
                                reset_val,
                                variants,
                                &mut new_statements,
                                expr_idtracker,
                                &self.loc,
                            );
                            (
                                Some((reset_trig.clone(), tag)),
                                Some((reset_trig.clone(), payload)),
                            )
                        } else {
                            (None, None)
                        };

                    new_statements.push(Statement::Register(Register {
                        name: tag_reg_name.clone(),
                        ty: Type::Bool,
                        clock: self.clock.clone(),
                        reset: reset_tag,
                        initial: self.initial.as_ref().map(|_| panic!("Had initial")),
                        value: value_tag.clone(),
                        loc: self.loc,
                        // FIXME: wal-tracing breaks with this change
                        traced: None,
                    }));
                    new_statements.push(Statement::Binding(Binding {
                        name: payload_reg_value_name.clone(),
                        operator: Operator::Select,
                        operands: vec![
                            value_tag.clone(),
                            value_payload.clone(),
                            payload_reg_name.clone(),
                        ],
                        ty: payload_type.clone(),
                        loc: self.loc,
                    }));
                    new_statements.push(Statement::Register(Register {
                        name: payload_reg_name.clone(),
                        ty: payload_type,
                        clock: self.clock.clone(),
                        reset: reset_payload,
                        initial: self.initial.as_ref().map(|_| panic!("Had initial")),
                        value: payload_reg_value_name,
                        loc: self.loc,
                        // FIXME: wal-tracing breaks with this change
                        traced: None,
                    }));
                    new_statements.push(Statement::Binding(Binding {
                        name: self.name.clone(),
                        operator: Operator::Concat,
                        operands: vec![tag_reg_name.clone(), payload_reg_name.clone()],
                        ty: self.ty.clone(),
                        loc: self.loc,
                    }));

                    Some(new_statements)
                } else {
                    None
                }
            }
            _ => None,
        }
    }
}

pub struct AutoGating {}

impl MirPass for AutoGating {
    fn transform_statements(
        &self,
        stmts: &[Statement],
        expr_idtracker: &ExprIdTracker,
    ) -> Vec<Statement> {
        stmts
            .iter()
            .flat_map(|stmt| match stmt {
                Statement::Register(reg) => reg
                    .perform_trivial_gating(expr_idtracker)
                    .unwrap_or_else(|| vec![stmt.clone()]),
                other => vec![other.clone()],
            })
            .collect()
    }

    fn name(&self) -> &'static str {
        "enum_clock_gating"
    }
}
