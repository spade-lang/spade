use crate::{Entity, MirInput, Operator, Statement, ValueName};
use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};

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
    let mut aliased_by = HashMap::default();
    // Some things are unaliasable, like input names and constants. Keep
    // track of those here to avoid problems
    let mut unaliasable = HashSet::default();

    for MirInput { val_name: val, .. } in &entity.inputs {
        unaliasable.insert(val.clone());
    }

    for stmt in &entity.statements {
        match stmt {
            Statement::Binding(binding) => {
                if let Operator::Alias = binding.operator {
                    match (binding.name.clone(), binding.operands[0].clone()) {
                        // Names should only alias expressions, not other names.
                        (ValueName::Named(_, _, _), ValueName::Named(_, _, _)) => {}
                        // If an expression aliases a name, flip it such that the
                        // name aliases the expression
                        (n @ ValueName::Named(_, _, _), e @ ValueName::Expr(_))
                        | (e @ ValueName::Expr(_), n @ ValueName::Named(_, _, _)) => {
                            aliased_by.entry(e).or_insert(vec![]).push(n);
                        }
                        (l, r) => {
                            aliased_by.entry(r).or_insert(vec![]).push(l);
                        }
                    }
                }
            }
            Statement::Register(_) => {}
            Statement::Constant(id, _, _) => {
                unaliasable.insert(ValueName::Expr(*id).clone());
            }
            Statement::Assert(_) => {}
            Statement::Set { .. } => {}
            Statement::WalTrace { .. } => {}
            Statement::Error => {}
        }
    }

    // Filter out any aliases we shouldn't alias because they have too many aliases
    // Also filter out any aliases which alias away an explicit name
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
                && !(binding.operator == Operator::Alias && aliases.contains_key(&binding.name))
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
            Statement::Set { target, value } => {
                try_rename(target, &aliases);
                try_rename(value, &aliases);
            }
            Statement::WalTrace {
                name,
                val,
                suffix: _,
                ty: _,
            } => {
                try_rename(name, &aliases);
                try_rename(val, &aliases);
            }
            Statement::Error => {}
        }
    }

    try_rename(&mut entity.output, &aliases);
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::assert_same_mir;
    use crate::entity;
    use crate::Type;
    use crate::{self as spade_mir, ConstantValue};
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

    // NOTE: This is purely a limitation based on the fact that constants cannot have names,
    // only IDs. If this is lifted we should probably alias them too
    #[test]
    fn aliasing_does_not_replace_constants() {
        let mut input = entity!("pong"; ("_i_op", n(0, "op"), Type::int(6)) -> Type::int(6); {
            (const 0; Type::int(10); ConstantValue::int(6));
            (n(1, "a"); Type::int(6); Alias; e(0));
        } => e(10));

        let expected = entity!("pong"; ("_i_op", n(0, "op"), Type::int(6)) -> Type::int(6); {
            (const 0; Type::int(10); ConstantValue::int(6));
            (n(1, "a"); Type::int(6); Alias; e(0));
        } => e(10));

        flatten_aliases(&mut input);

        assert_eq!(input, expected);
    }

    #[test]
    fn aliasing_does_not_happen_when_multiple_aliases_are_present() {
        let mut input = entity!("pong"; ("_i_op", n(0, "op"), Type::int(6)) -> Type::int(6); {
            (e(0); Type::int(6); Add; n(0, "op"), e(1));
            (n(0, "a"); Type::int(6); Alias; e(1));
            (n(0, "b"); Type::int(6); Alias; e(1));
        } => e(10));

        let expected = entity!("pong"; ("_i_op", n(0, "op"), Type::int(6)) -> Type::int(6); {
            (e(0); Type::int(6); Add; n(0, "op"), e(1));
            (n(0, "a"); Type::int(6); Alias; e(1));
            (n(0, "b"); Type::int(6); Alias; e(1));
        } => e(10));

        flatten_aliases(&mut input);

        assert_eq!(input, expected);
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
            } => n(1, "x")
        );

        flatten_aliases(&mut input);

        assert_same_mir!(&input, &expected);
    }
}
