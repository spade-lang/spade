use rustc_hash::FxHashMap as HashMap;
use spade_common::id_tracker::ExprIdTracker;

use crate::{passes::MirPass, Binding, Entity, Operator, Statement, ValueName};

pub struct ConcatFold {}

struct ConcatTree<'a> {
    non_concat_uses: usize,
    children: &'a Vec<ValueName>,
}

impl<'a> ConcatTree<'a> {
    fn collapse(&self, map: &HashMap<&ValueName, ConcatTree>) -> Vec<ValueName> {
        self.children
            .iter()
            .flat_map(|child| {
                map.get(child)
                    .map(|subtree| subtree.collapse(map))
                    .unwrap_or(vec![child.clone()])
            })
            .collect()
    }
}

impl MirPass for ConcatFold {
    fn name(&self) -> &'static str {
        "concat_fold"
    }

    fn transform_statements(
        &self,
        stmts: &[Statement],
        _expr_idtracker: &ExprIdTracker,
        entity: &Entity,
    ) -> Vec<Statement> {
        let mut concat_trees = HashMap::default();

        for s in stmts {
            match s {
                Statement::Binding(Binding {
                    name,
                    operator: Operator::Concat | Operator::Alias,
                    operands,
                    ty: _,
                    loc: _,
                }) => {
                    concat_trees.insert(
                        name,
                        ConcatTree {
                            non_concat_uses: 0,
                            children: operands,
                        },
                    );
                }
                _ => {}
            }
        }

        for s in stmts {
            match s {
                Statement::Binding(Binding {
                    name: _,
                    operator,
                    operands: _,
                    ty: _,
                    loc: _,
                }) => {
                    if !matches!(operator, Operator::Concat | Operator::Alias) {
                        s.for_each_input(|i| {
                            concat_trees.get_mut(i).map(|t| t.non_concat_uses += 1);
                        });
                    }
                }
                _ => s.for_each_input(|i| {
                    concat_trees.get_mut(i).map(|t| t.non_concat_uses += 1);
                }),
            }
        }

        concat_trees
            .get_mut(&entity.output)
            .map(|t| t.non_concat_uses += 1);

        stmts
            .iter()
            .filter_map(|s| match s {
                Statement::Binding(binding) if matches!(binding.operator, Operator::Concat) => {
                    if let Some(tree) = concat_trees.get(&binding.name) {
                        if tree.non_concat_uses == 0 {
                            None
                        } else {
                            Some(Statement::Binding(Binding {
                                name: binding.name.clone(),
                                operator: Operator::Concat,
                                operands: tree.collapse(&concat_trees),
                                ty: binding.ty.clone(),
                                loc: binding.loc,
                            }))
                        }
                    } else {
                        Some(s.clone())
                    }
                }
                _ => Some(s.clone()),
            })
            .collect()
    }
}
