use std::collections::HashMap;

use spade_common::id_tracker::ExprIdTracker;

use crate::{types::Type, Binding, Operator, Statement, ValueName};

use super::MirPass;

pub struct NoSelectX {}

impl MirPass for NoSelectX {
    fn transform_statements(
        &self,
        stmts: &[Statement],
        expr_idtracker: &mut ExprIdTracker,
    ) -> Vec<Statement> {
        let enum_constructors = stmts
            .iter()
            .filter_map(|stmt| match stmt {
                Statement::Binding(Binding {
                    name,
                    operator:
                        Operator::ConstructEnum {
                            variant: _,
                            variant_count,
                        },
                    operands,
                    ty: _,
                    loc: _,
                }) => {
                    // Targeting specifically to the enum type
                    if *variant_count == 2 {
                        Some((name, operands))
                    } else {
                        None
                    }
                }
                _ => None,
            })
            .collect::<HashMap<_, _>>();

        stmts
            .iter()
            .flat_map(|stmt| match stmt {
                Statement::Binding(Binding {
                    name,
                    operator: Operator::Match,
                    operands,
                    ty,
                    loc,
                }) if operands.len() == 4 => {
                    if let (Some(v1), Some(v2)) = (
                        enum_constructors.get(&operands[1]),
                        enum_constructors.get(&operands[3]),
                    ) {
                        let (tag, value, tag_stmts) = match (v1.as_slice(), v2.as_slice()) {
                            ([val], []) => (operands[0].clone(), val.clone(), vec![]),
                            ([], [val]) => {
                                let not_name = ValueName::Expr(expr_idtracker.next());
                                let tag_name = ValueName::Expr(expr_idtracker.next());
                                let s = vec![
                                    Statement::Binding(Binding {
                                        name: not_name.clone(),
                                        operator: Operator::Not,
                                        operands: vec![operands[0].clone()],
                                        ty: Type::Bool,
                                        loc: None,
                                    }),
                                    Statement::Binding(Binding {
                                        name: tag_name,
                                        operator: Operator::LogicalAnd,
                                        operands: vec![not_name.clone(), operands[2].clone()],
                                        ty: Type::Bool,
                                        loc: None,
                                    }),
                                ];
                                (not_name.clone(), val.clone(), s)
                            }
                            _ => return vec![stmt.clone()],
                        };

                        // Create a new binding for the tag
                        tag_stmts
                            .into_iter()
                            .chain(vec![Statement::Binding(Binding {
                                name: name.clone(),
                                operator: Operator::Concat,
                                operands: vec![tag, value],
                                ty: ty.clone(),
                                loc: loc.clone(),
                            })])
                            .collect()
                    } else {
                        vec![stmt.clone()]
                    }
                }
                _ => vec![stmt.clone()],
            })
            .collect()
    }

    fn name(&self) -> &'static str {
        "no_select_x"
    }
}
