use std::collections::HashMap;

use num::BigUint;

use crate::{Binding, Operator, Statement, ValueName};

use super::MirPass;

pub struct DeduplicateMutWires {}

impl MirPass for DeduplicateMutWires {
    fn name(&self) -> &'static str {
        "DeduplicateMutWires"
    }

    fn transform_statements(
        &self,
        stmts: &[Statement],
        _expr_idtracker: &mut spade_common::id_tracker::ExprIdTracker,
    ) -> Vec<Statement> {
        replace_duplicate_mut_wires(stmts)
    }
}

fn recursive_lookup(map: &HashMap<&ValueName, ValueName>, name: ValueName) -> Option<ValueName> {
    if let n @ Some(next) = map.get(&name) {
        if let Some(deeper) = recursive_lookup(map, next.clone()) {
            Some(deeper)
        } else {
            n.cloned()
        }
    } else {
        None
    }
}

fn replace_duplicate_mut_wires(stmts: &[Statement]) -> Vec<Statement> {
    let mut seen_statements: HashMap<(&Operator, &Vec<ValueName>, &crate::types::Type), ValueName> =
        HashMap::new();
    let mut replaced_names = HashMap::new();

    for stmt in stmts {
        match stmt {
            Statement::Binding(Binding {
                name,
                operator,
                operands,
                ty,
                loc: _,
            }) => {
                // We're only interested in mut wires
                if ty.backward_size() != BigUint::ZERO && operator != &Operator::Nop {
                    if let Some(prev_name) = seen_statements.get(&(operator, operands, ty)) {
                        replaced_names.insert(
                            name,
                            recursive_lookup(&replaced_names, prev_name.clone())
                                .unwrap_or(prev_name.clone()),
                        );
                    }
                }
                seen_statements.insert((operator, operands, ty), name.clone());
            }
            Statement::Register(_) => {
                // Empty, registers cannot contain mut wires
            }
            Statement::Constant(_, _, _)
            | Statement::Assert(_)
            | Statement::Set { .. }
            | Statement::WalTrace { .. } => {}
        }
    }

    let get_replacement = |v: ValueName| replaced_names.get(&v).cloned().unwrap_or(v);

    let iter_result = stmts
        .into_iter()
        .filter_map(|stmt| match stmt.clone() {
            Statement::Binding(Binding {
                name,
                operator,
                operands,
                ty,
                loc,
            }) => {
                if replaced_names.contains_key(&name) {
                    None
                } else {
                    Some(Statement::Binding(Binding {
                        name,
                        operator,
                        operands: operands.into_iter().map(get_replacement).collect(),
                        ty,
                        loc,
                    }))
                }
            }
            // Unchanged things since they don't consume nor create mut wires
            s @ Statement::Register(_)
            | s @ Statement::Constant(_, _, _)
            | s @ Statement::Assert(_) => Some(s),
            Statement::Set { target, value } => {
                // If we replaced a mut wire with another, the other one is going to do
                // the assignment. Doing it here is going to cause issues
                if replaced_names.contains_key(&target.inner) {
                    None
                } else {
                    Some(Statement::Set {
                        target: target.map(|t| get_replacement(t)),
                        value: value.map(|v| get_replacement(v)),
                    })
                }
            }
            Statement::WalTrace {
                name,
                val,
                suffix,
                ty,
            } => Some(Statement::WalTrace {
                name: get_replacement(name),
                val: get_replacement(val),
                suffix,
                ty,
            }),
        })
        .collect::<Vec<_>>();

    if !replaced_names.is_empty() {
        replace_duplicate_mut_wires(&iter_result)
    } else {
        iter_result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{self as spade_mir, assert_same_mir, entity, types::Type};
    use colored::Colorize;
    use spade_common::id_tracker::ExprIdTracker;

    #[test]
    fn deduplicate_pass_works() {
        // For now, it doesn't matter that this is riddled with type errors :)
        let input = entity! {&["name"]; (
                "c", n(0, "c"), Type::Bool,
                "a", n(1, "a"), Type::int(16),
                "b", n(2, "b"), Type::int(16)
            ) -> Type::int(16); {
                // These should not be deduplicated since they have zero backward size
                (e(0); Type::int(16); Select; n(0, "c"), n(1, "a"), n(2, "b"));
                (e(1); Type::int(16); Select; n(0, "c"), n(1, "a"), n(2, "b"));

                // These should be deduplicated since they have non-zero backward size
                (e(1); Type::backward(Type::int(16)); Select; n(0, "c"), n(1, "a"), n(2, "b"));
                (e(2); Type::backward(Type::int(16)); Select; n(0, "c"), n(1, "a"), n(2, "b"));

                // Users have the relevant thing removed
                (e(3); Type::int(16); Sub; e(1));
                (e(4); Type::int(16); Sub; e(2));

                // Recursive replacement once the above have been resolved
                (e(11); Type::backward(Type::int(16)); Select; n(0, "c"), n(1, "a"), e(1));
                (e(12); Type::backward(Type::int(16)); Select; n(0, "c"), n(1, "a"), e(2));

                (e(13); Type::int(16); Sub; e(11));
                (e(14); Type::int(16); Sub; e(12));

                // NOPs should not be replaced
                (e(21); Type::backward(Type::int(16)); Nop; );
                (e(22); Type::backward(Type::int(16)); Nop; );

                (e(13); Type::int(16); Sub; e(21));
                (e(14); Type::int(16); Sub; e(22));
            } => e(0)
        };
        let expected = entity! {&["name"]; (
                "c", n(0, "c"), Type::Bool,
                "a", n(1, "a"), Type::int(16),
                "b", n(2, "b"), Type::int(16)
            ) -> Type::int(16); {
                // These should not be deduplicated since they have zero backward size
                (e(0); Type::int(16); Select; n(0, "c"), n(1, "a"), n(2, "b"));
                (e(1); Type::int(16); Select; n(0, "c"), n(1, "a"), n(2, "b"));

                // These should be deduplicated since they have non-zero backward size
                (e(1); Type::backward(Type::int(16)); Select; n(0, "c"), n(1, "a"), n(2, "b"));

                // Users have the relevant thing removed
                (e(3); Type::int(16); Sub; e(1));
                (e(4); Type::int(16); Sub; e(1));

                // Recursive replacement once the above have been resolved
                (e(11); Type::backward(Type::int(16)); Select; n(0, "c"), n(1, "a"), e(1));

                (e(13); Type::int(16); Sub; e(11));
                (e(14); Type::int(16); Sub; e(11));

                // NOPs should not be replaced
                (e(21); Type::backward(Type::int(16)); Nop; );
                (e(22); Type::backward(Type::int(16)); Nop; );

                (e(13); Type::int(16); Sub; e(21));
                (e(14); Type::int(16); Sub; e(22));
            } => e(0)
        };

        let mut deduplicated = input.clone();
        deduplicated.statements = DeduplicateMutWires {}
            .transform_statements(&input.statements, &mut ExprIdTracker::new());

        assert_same_mir!(&expected, &deduplicated);
    }
}
