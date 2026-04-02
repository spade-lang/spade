use std::collections::{BTreeMap, VecDeque};

use crate::{Entity, MirInput, Operator, Statement, ValueName};
use itertools::Itertools;
use num::BigUint;
use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};

fn try_rename(name: &mut ValueName, replacements: &HashMap<ValueName, ValueName>) {
    if let Some(replacement) = replacements.get(name) {
        *name = (*replacement).clone();
    }
}

/// Resolves aliases where a var name is only aliased once.
///
/// That is if a -> b, then all occurrences of a will be replaced by b
/// unless a is also aliased for something else
pub fn flatten_aliases(entity: &mut Entity) {
    let mut edges = BTreeMap::default();
    // Some things are unaliasable, like input names and constants. Keep
    // track of those here to avoid problems
    let mut unaliasable = HashSet::default();
    let mut types = HashMap::default();

    for MirInput { val_name: val, .. } in &entity.inputs {
        unaliasable.insert(val.clone());
    }

    // Build an undirected "graph" of aliases
    for stmt in &entity.statements {
        match stmt {
            Statement::Binding(binding) => {
                if let Operator::Alias = binding.operator {
                    types.insert(binding.name.clone(), binding.ty.clone());
                    types.insert(binding.operands[0].clone(), binding.ty.clone());
                    edges
                        .entry(binding.name.clone())
                        .or_insert(vec![])
                        .push(binding.operands[0].clone());
                    edges
                        .entry(binding.operands[0].clone())
                        .or_insert(vec![])
                        .push(binding.name.clone());
                }
            }
            Statement::Register(_) => {}
            Statement::Constant(_, _, _) => {}
            Statement::Assert(_) => {}
            Statement::Set { .. } => {}
            Statement::WalTrace { .. } => {}
            Statement::Error => {}
        }
    }

    // Find all components of that graph
    let mut alias_clusters = vec![];

    while let Some((source, _edges)) = edges.first_key_value() {
        let mut this_cluster = HashSet::default();
        let mut to_visit = VecDeque::new();
        to_visit.push_front(source.clone());

        while let Some(node) = to_visit.pop_front() {
            if let Some((_, edges)) = edges.remove_entry(&node) {
                for edge in edges.clone() {
                    to_visit.push_back(edge);
                }
            }
            this_cluster.insert(node);
        }
        alias_clusters.push(this_cluster);
    }

    // These are the nodes we will remove and replace by a representative
    let mut final_aliases = HashMap::default();
    // In order to improve debugging, We will re-create aliases from non-representative
    // value names to the representatitve where possible, i.e. where the value doesn't
    // have a backward size
    let mut new_aliases = vec![];
    for cluster in alias_clusters {
        // For each cluster, find a representative for the cluster that
        // will be the canonical element
        let Some(representative) = cluster
            .iter()
            .sorted_by_key(|node| {
                if unaliasable.contains(node) {
                    return 0;
                };
                match node {
                    ValueName::Named(_, _, _) => 1,
                    ValueName::Expr(_) => 2,
                }
            })
            .next()
            .cloned()
        else {
            continue;
        };

        for node in cluster {
            if node != representative {
                final_aliases.insert(node.clone(), representative.clone());

                if matches!(node, ValueName::Named(_, _, _))
                    && types
                        .get(&node)
                        .map(|ty| ty.backward_size() == BigUint::ZERO)
                        .unwrap_or(false)
                {
                    new_aliases.push((representative.clone(), node));
                }
            }
        }
    }

    // Remove any aliases that are now inlined
    entity.statements.retain(|stmt| {
        if let Statement::Binding(binding) = stmt {
            !(binding.operator == Operator::Alias
                && final_aliases.contains_key(&binding.operands[0]))
                && !(binding.operator == Operator::Alias
                    && final_aliases.contains_key(&binding.name))
        } else {
            true
        }
    });

    for stmt in &mut entity.statements {
        match stmt {
            Statement::Binding(binding) => {
                try_rename(&mut binding.name, &final_aliases);
                for op in &mut binding.operands {
                    try_rename(op, &final_aliases);
                }
            }
            Statement::Register(reg) => {
                try_rename(&mut reg.name, &final_aliases);
                try_rename(&mut reg.value, &final_aliases);
            }
            Statement::Constant(name, _, _) => {
                try_rename(name, &final_aliases);
            }
            Statement::Assert(name) => try_rename(name, &final_aliases),
            Statement::Set { target, value } => {
                try_rename(target, &final_aliases);
                try_rename(value, &final_aliases);
            }
            Statement::WalTrace {
                name,
                val,
                suffix: _,
                ty: _,
            } => {
                try_rename(name, &final_aliases);
                try_rename(val, &final_aliases);
            }
            Statement::Error => {}
        }
    }

    for (representative, other) in new_aliases {
        entity.statements.push(Statement::Binding(crate::Binding {
            name: other,
            operator: Operator::Alias,
            operands: vec![representative.clone()],
            ty: types
                .get(&representative)
                .cloned()
                .expect("Found an alias without a type")
                .clone(),
            loc: None,
        }));
    }

    try_rename(&mut entity.output, &final_aliases);
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::Type;
    use crate::assert_same_mir;
    use crate::entity;
    use crate::{self as spade_mir};
    use colored::Colorize;

    #[test]
    fn aliasing_replaces_definitions() {
        let mut input = entity!("pong"; ("_i_op", n(0, "op"), Type::int(6)) -> Type::int(6); {
            (e(0); Type::int(6); Add; n(0, "op"), e(1));
            (n(0, "a"); Type::int(6); Alias; e(0))
        } => e(10));

        let expected = entity!("pong"; ("_i_op", n(0, "op"), Type::int(6)) -> Type::int(6); {
            (n(0, "a"); Type::int(6); Add; n(0, "op"), e(1))
        } => e(10));

        flatten_aliases(&mut input);

        assert_eq!(input, expected);
    }

    #[test]
    fn three_level_aliasing_replaces_definitions() {
        let mut input = entity!("pong"; ("_i_op", n(0, "op"), Type::int(6)) -> Type::int(6); {
            (e(1); Type::Bool; Add;); (e(10); Type::Bool; Add;); // We need some dummy signals
            (e(0); Type::int(6); Add; n(0, "op"), e(1));
            (e(20); Type::int(6); Alias; e(0));
            (e(21); Type::int(6); Alias; e(20));
            (n(1, "c"); Type::int(6); Alias; e(21));
        } => e(10));

        let expected = entity!("pong"; ("_i_op", n(0, "op"), Type::int(6)) -> Type::int(6); {
            (e(1); Type::Bool; Add;);
            (e(10); Type::Bool; Add;);
            (n(1, "c"); Type::int(6); Add; n(0, "op"), e(1))
        } => e(10));

        flatten_aliases(&mut input);

        assert_same_mir!(&input, &expected);
    }

    #[test]
    fn three_level_aliasing_replaces_definitions_in_other_order() {
        let mut input = entity!("pong"; ("_i_op", n(0, "op"), Type::int(6)) -> Type::int(6); {
            (e(1); Type::Bool; Add;); (e(10); Type::Bool; Add;); // We need some dummy signals
            (e(0); Type::int(6); Add; n(0, "op"), e(1));
            (e(20); Type::int(6); Alias; e(0));
            (n(1, "c"); Type::int(6); Alias; e(20));
            (e(21); Type::int(6); Alias; n(1, "c"));
        } => e(10));

        let expected = entity!("pong"; ("_i_op", n(0, "op"), Type::int(6)) -> Type::int(6); {
            (e(1); Type::Bool; Add;);
            (e(10); Type::Bool; Add;);
            (n(1, "c"); Type::int(6); Add; n(0, "op"), e(1))
        } => e(10));

        flatten_aliases(&mut input);

        assert_same_mir!(&input, &expected);
    }

    #[test]
    fn aliasing_replaces_uses() {
        let mut input = entity!("pong"; ("_i_op", n(0, "op"), Type::int(6)) -> Type::int(6); {
            (e(0); Type::int(6); Add; n(0, "op"), e(1));
            (n(0, "a"); Type::int(6); Alias; e(1))
        } => e(10));

        let expected = entity!("pong"; ("_i_op", n(0, "op"), Type::int(6)) -> Type::int(6); {
            (e(0); Type::int(6); Add; n(0, "op"), n(0, "a"));
        } => e(10));

        flatten_aliases(&mut input);

        assert_eq!(input, expected);
    }

    #[test]
    fn aliasing_replaces_in_registers() {
        let mut input = entity!("pong"; ("_i_op", n(0, "op"), Type::int(6)) -> Type::int(6); {
            (reg e(1); Type::int(6); clock (n(0, "clk")); e(0));
            (n(1, "a"); Type::int(6); Alias; e(1));
            (n(2, "b"); Type::int(6); Alias; e(0));
        } => e(10));

        let expected = entity!("pong"; ("_i_op", n(0, "op"), Type::int(6)) -> Type::int(6); {
            (reg n(1, "a"); Type::int(6); clock (n(0, "clk")); n(2, "b"))
        } => e(10));

        flatten_aliases(&mut input);

        assert_eq!(input, expected);
    }

    #[test]
    fn named_aliases_are_handled_correctly() {
        let mut input = entity!("pong"; ("_i_op", n(0, "op"), Type::int(6)) -> Type::int(6); {
            (e(0); Type::int(6); Add; n(0, "op"), e(1));
            (n(0, "a"); Type::int(6); Alias; e(1));
            (n(0, "b"); Type::int(6); Alias; e(1));
        } => n(0, "b"));

        let expected = entity!("pong"; ("_i_op", n(0, "op"), Type::int(6)) -> Type::int(6); {
            (e(0); Type::int(6); Add; n(0, "op"), n(0, "a"));
            (n(0, "b"); Type::int(6); Alias; n(0, "a"));
        } => n(0, "a"));

        flatten_aliases(&mut input);

        assert_same_mir!(&input, &expected);
    }

    #[test]
    fn aliasing_inv_wires_does_not_create_alias_copies() {
        let mut input = entity!("pong"; ("_i_op", n(0, "op"), Type::int(6)) -> Type::int(6); {
            (e(0); Type::int(6); Add; n(0, "op"), e(1));
            (n(0, "a"); Type::Backward(Box::new(Type::int(6))); Alias; e(1));
            (n(0, "b"); Type::Backward(Box::new(Type::int(6))); Alias; e(1));
        } => n(0, "b"));

        let expected = entity!("pong"; ("_i_op", n(0, "op"), Type::int(6)) -> Type::int(6); {
            (e(0); Type::int(6); Add; n(0, "op"), n(0, "a"));
        } => n(0, "a"));

        flatten_aliases(&mut input);

        assert_same_mir!(&input, &expected);
    }

    #[test]
    fn inputs_are_not_aliased() {
        let mut input = entity!("pong"; ("_i_op", n(0, "op"), Type::int(6)) -> Type::int(6); {
            (n(0, "a"); Type::int(6); Alias; n(0, "op"));
        } => e(10));

        let expected = entity!("pong"; ("_i_op", n(0, "op"), Type::int(6)) -> Type::int(6); {
            (n(0, "a"); Type::int(6); Alias; n(0, "op"));
        } => e(10));

        flatten_aliases(&mut input);

        assert_eq!(input, expected);
    }

    #[test]
    fn outputs_are_aliased() {
        let mut input = entity!("pong"; ("_i_op", n(0, "op"), Type::int(6)) -> Type::int(6); {
            (n(0, "a"); Type::int(6); Alias; e(0));
        } => e(0));

        let expected = entity!("pong"; ("_i_op", n(0, "op"), Type::int(6)) -> Type::int(6); {
        } => n(0, "a"));

        flatten_aliases(&mut input);

        assert_eq!(input, expected);
    }

    #[test]
    fn aliases_in_pipelines_work_correctly() {
        let inst_name = spade_mir::UnitName::_test_from_strs(&["A"]);

        let mut input = entity!("pl"; (
                "clk", n(3, "clk"), Type::Bool,
            ) -> Type::int(16); {
                (reg n(10, "x__s1"); Type::int(16); clock(n(3, "clk")); n(0, "x_"));
                // Stage 0
                (e(0); Type::int(16); simple_instance((inst_name.clone(), vec![])););
                (n(0, "x_"); Type::int(16); Alias; e(0));
                // Stage 1
                (n(1, "x"); Type::int(16); Alias; n(0, "x_"));
            } => n(1, "x")
        );

        let expected = entity!("pl"; (
                "clk", n(3, "clk"), Type::Bool,
            ) -> Type::int(16); {
                (reg n(10, "x__s1"); Type::int(16); clock(n(3, "clk")); n(0, "x_"));
                (n(0, "x_"); Type::int(16); simple_instance((inst_name.clone(), vec![])););
                // Stage 0
                (n(1, "x"); Type::int(16); Alias; n(0, "x_"));
                // Stage 1
            } => n(0, "x_")
        );

        flatten_aliases(&mut input);

        assert_same_mir!(&input, &expected);
    }
}
