use std::collections::{HashMap, HashSet};

use crate::{Entity, Operator, Statement, ValueName};

fn try_rename(name: &mut ValueName, replacements: &HashMap<ValueName, ValueName>) {
    if let Some(replacement) = replacements.get(name) {
        *name = replacement.clone();
    }
}

/// Resolves aliases where a var name is only aliased once.
///
/// That is if a -> b, then all occurrences of a will be replaced by b
/// unless a is also aliased for something else
pub fn flatten_aliases(entity: &mut Entity) {
    let mut aliased_by = HashMap::new();
    // Some things are unaliasable, like input names and constats. Keep
    // track of those here to avoid problems
    let mut unaliasable = HashSet::new();

    for (_, val, _) in &entity.inputs {
        unaliasable.insert(val.clone());
    }

    for stmt in &entity.statements {
        match stmt {
            Statement::Binding(binding) => {
                if let Operator::Alias = binding.operator {
                    aliased_by
                        .entry(binding.operands[0].clone())
                        .or_insert(vec![])
                        .push(binding.name.clone());
                }
            }
            Statement::Register(_) => {}
            Statement::Constant(id, _, _) => {
                unaliasable.insert(ValueName::Expr(*id).clone());
            }
            Statement::Assert(_) => {}
            Statement::Set { .. } => {}
        }
    }

    // Filter out any aliases we shouldn't alias because they have too many aliases
    let mut aliases = aliased_by
        .into_iter()
        .filter_map(|(k, v)| {
            if v.len() == 1 && !unaliasable.contains(&k) {
                Some((k, v[0].clone()))
            } else {
                None
            }
        })
        .collect::<HashMap<_, _>>();

    // Remove any aliases that are now inlined
    entity.statements.retain(|stmt| {
        if let Statement::Binding(binding) = stmt {
            !(binding.operator == Operator::Alias && aliases.contains_key(&binding.operands[0]))
        } else {
            true
        }
    });

    // Resolve chained aliases, i.e. a -> b -> c should alias both a and b to c
    let mut changed = true;
    while changed {
        changed = false;

        let prev_aliases = aliases.clone();
        for (from, to) in prev_aliases {
            for alias_for in aliases.values_mut() {
                if alias_for == &from {
                    *alias_for = to.clone();
                    changed = true;
                }
            }
        }
    }

    for stmt in &mut entity.statements {
        match stmt {
            Statement::Binding(ref mut binding) => {
                try_rename(&mut binding.name, &aliases);
                for op in &mut binding.operands {
                    try_rename(op, &aliases);
                }
            }
            Statement::Register(reg) => {
                try_rename(&mut reg.name, &aliases);
                try_rename(&mut reg.value, &aliases);
            }
            Statement::Constant(_, _, _) => {}
            Statement::Assert(_) => {}
            Statement::Set { .. } => {}
        }
    }

    try_rename(&mut entity.output, &aliases);
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::entity;
    use crate::Type;
    use crate::{self as spade_mir, ConstantValue};

    #[test]
    fn aliasing_replaces_definitions() {
        let mut input = entity!("pong"; ("_i_op", n(0, "op"), Type::Int(6)) -> Type::Int(6); {
            (e(0); Type::Int(6); Add; n(0, "op"), e(1));
            (n(0, "a"); Type::Int(6); Alias; e(0))
        } => e(10));

        let expected = entity!("pong"; ("_i_op", n(0, "op"), Type::Int(6)) -> Type::Int(6); {
            (n(0, "a"); Type::Int(6); Add; n(0, "op"), e(1))
        } => e(10));

        flatten_aliases(&mut input);

        assert_eq!(input, expected);
    }

    #[test]
    fn three_level_aliasing_replaces_definitions() {
        let mut input = entity!("pong"; ("_i_op", n(0, "op"), Type::Int(6)) -> Type::Int(6); {
            (e(0); Type::Int(6); Add; n(0, "op"), e(1));
            (n(0, "a"); Type::Int(6); Alias; e(0));
            (n(2, "b"); Type::Int(6); Alias; n(0, "a"));
            (n(1, "c"); Type::Int(6); Alias; n(2, "b"));
        } => e(10));

        let expected = entity!("pong"; ("_i_op", n(0, "op"), Type::Int(6)) -> Type::Int(6); {
            (n(1, "c"); Type::Int(6); Add; n(0, "op"), e(1))
        } => e(10));

        flatten_aliases(&mut input);

        assert_eq!(input, expected);
    }

    #[test]
    fn aliasing_replaces_uses() {
        let mut input = entity!("pong"; ("_i_op", n(0, "op"), Type::Int(6)) -> Type::Int(6); {
            (e(0); Type::Int(6); Add; n(0, "op"), e(1));
            (n(0, "a"); Type::Int(6); Alias; e(1))
        } => e(10));

        let expected = entity!("pong"; ("_i_op", n(0, "op"), Type::Int(6)) -> Type::Int(6); {
            (e(0); Type::Int(6); Add; n(0, "op"), n(0, "a"));
        } => e(10));

        flatten_aliases(&mut input);

        assert_eq!(input, expected);
    }

    #[test]
    fn aliasing_replaces_in_registers() {
        let mut input = entity!("pong"; ("_i_op", n(0, "op"), Type::Int(6)) -> Type::Int(6); {
            (reg e(1); Type::Int(6); clock (n(0, "clk")); e(0));
            (n(1, "a"); Type::Int(6); Alias; e(1));
            (n(2, "b"); Type::Int(6); Alias; e(0));
        } => e(10));

        let expected = entity!("pong"; ("_i_op", n(0, "op"), Type::Int(6)) -> Type::Int(6); {
            (reg n(1, "a"); Type::Int(6); clock (n(0, "clk")); n(2, "b"))
        } => e(10));

        flatten_aliases(&mut input);

        assert_eq!(input, expected);
    }

    // NOTE: This is purely a limitation based on the fact that constants can not have names,
    // only IDs. If this is lifted we should probably alias them too
    #[test]
    fn aliasing_does_not_replace_constants() {
        let mut input = entity!("pong"; ("_i_op", n(0, "op"), Type::Int(6)) -> Type::Int(6); {
            (const 0; Type::Int(10); ConstantValue::Int(6));
            (n(1, "a"); Type::Int(6); Alias; e(0));
        } => e(10));

        let expected = entity!("pong"; ("_i_op", n(0, "op"), Type::Int(6)) -> Type::Int(6); {
            (const 0; Type::Int(10); ConstantValue::Int(6));
            (n(1, "a"); Type::Int(6); Alias; e(0));
        } => e(10));

        flatten_aliases(&mut input);

        assert_eq!(input, expected);
    }

    #[test]
    fn aliasing_does_not_happen_when_multiple_aliases_are_present() {
        let mut input = entity!("pong"; ("_i_op", n(0, "op"), Type::Int(6)) -> Type::Int(6); {
            (e(0); Type::Int(6); Add; n(0, "op"), e(1));
            (n(0, "a"); Type::Int(6); Alias; e(1));
            (n(0, "b"); Type::Int(6); Alias; e(1));
        } => e(10));

        let expected = entity!("pong"; ("_i_op", n(0, "op"), Type::Int(6)) -> Type::Int(6); {
            (e(0); Type::Int(6); Add; n(0, "op"), e(1));
            (n(0, "a"); Type::Int(6); Alias; e(1));
            (n(0, "b"); Type::Int(6); Alias; e(1));
        } => e(10));

        flatten_aliases(&mut input);

        assert_eq!(input, expected);
    }

    #[test]
    fn inputs_are_not_aliased() {
        let mut input = entity!("pong"; ("_i_op", n(0, "op"), Type::Int(6)) -> Type::Int(6); {
            (n(0, "a"); Type::Int(6); Alias; n(0, "op"));
        } => e(10));

        let expected = entity!("pong"; ("_i_op", n(0, "op"), Type::Int(6)) -> Type::Int(6); {
            (n(0, "a"); Type::Int(6); Alias; n(0, "op"));
        } => e(10));

        flatten_aliases(&mut input);

        assert_eq!(input, expected);
    }

    #[test]
    fn outputs_are_aliased() {
        let mut input = entity!("pong"; ("_i_op", n(0, "op"), Type::Int(6)) -> Type::Int(6); {
            (n(0, "a"); Type::Int(6); Alias; e(0));
        } => e(0));

        let expected = entity!("pong"; ("_i_op", n(0, "op"), Type::Int(6)) -> Type::Int(6); {
        } => n(0, "a"));

        flatten_aliases(&mut input);

        assert_eq!(input, expected);
    }

    #[test]
    fn aliases_in_pipelines_work_correctly() {
        let mut input = entity!("pl"; (
                "clk", n(3, "clk"), Type::Bool,
            ) -> Type::Int(16); {
                (reg n(10, "x__s1"); Type::Int(16); clock(n(3, "clk")); n(0, "x_"));
                // Stage 0
                (e(0); Type::Int(16); Instance(("A".to_string(), None)););
                (n(0, "x_"); Type::Int(16); Alias; e(0));
                // Stage 1
                (n(1, "x"); Type::Int(16); Alias; n(0, "x_"));
            } => n(1, "x")
        );

        let expected = entity!("pl"; (
                "clk", n(3, "clk"), Type::Bool,
            ) -> Type::Int(16); {
                (reg n(10, "x__s1"); Type::Int(16); clock(n(3, "clk")); n(1, "x"));
                // Stage 0
                (n(1, "x"); Type::Int(16); Instance(("A".to_string(), None)););
                // Stage 1
            } => n(1, "x")
        );

        flatten_aliases(&mut input);

        assert_eq!(input, expected);
    }
}
