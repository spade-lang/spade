use spade_common::id_tracker::{ExprIdTracker, NameIdTracker};

use crate::{types::Type, Binding, ConstantValue, Entity, Operator, Statement, ValueName};

pub fn wal_alias(
    source: &ValueName,
    prefix: &str,
    suffix: &str,
    ty: &Type,
    idtracker: &mut Option<&mut NameIdTracker>,
) -> Statement {
    // Because we know that traced_name is now unique, we also
    // know that any signals we generate with that name will be unique.
    // Therefore, we are free to generate `n(0, <name>_...)`
    let new_name = ValueName::Named(
        idtracker.as_mut().map(|t| t.next()).unwrap_or_default(),
        format!("{prefix}{suffix}"),
        source.into(),
    );

    Statement::Binding(Binding {
        name: new_name,
        operator: Operator::Alias,
        operands: vec![source.clone()],
        ty: ty.clone(),
        loc: None,
    })
}

// NOTE: This pass must run after both flatten_aliases and make_names_predictable
// after the pass is run.
// NOTE: idtracker must be set to None for *codegen* to be correct, but it can be set
// to an ID tracker for testing purposes, for mir diffing to work
pub fn insert_wal_signals(
    entity: &mut Entity,
    expr_idtracker: &mut ExprIdTracker,
    name_idtracker: &mut Option<&mut NameIdTracker>,
) {
    let new_statements = entity
        .statements
        .iter()
        .flat_map(|s| {
            match s {
                Statement::Register(reg) => {
                    if let Some(traced_name) = &reg.traced {
                        let prefix = traced_name.unescaped_var_name();
                        let mut result = vec![
                            // Emit the register itself
                            s.clone(),
                            wal_alias(
                                traced_name,
                                &prefix,
                                "__wal_fsm_state",
                                &reg.ty,
                                name_idtracker,
                            ),
                            wal_alias(
                                &reg.clock,
                                &prefix,
                                "__wal_fsm_clk",
                                &Type::Bool,
                                name_idtracker,
                            ),
                        ];
                        let rst_signal = if let Some(rst) = &reg.reset {
                            rst.0.clone()
                        } else {
                            let id = expr_idtracker.next();
                            result.push(Statement::Constant(
                                id,
                                Type::Bool,
                                ConstantValue::Bool(false),
                            ));
                            ValueName::Expr(id)
                        };
                        result.push(wal_alias(
                            &rst_signal,
                            &prefix,
                            "__wal_fsm_rst",
                            &Type::Bool,
                            name_idtracker,
                        ));
                        result
                    } else {
                        vec![s.clone()]
                    }
                }
                Statement::WalTrace {
                    name,
                    val,
                    suffix,
                    ty,
                } => {
                    vec![wal_alias(
                        val,
                        &name.unescaped_var_name(),
                        suffix,
                        ty,
                        name_idtracker,
                    )]
                }
                other => vec![other.clone()],
            }
        })
        .collect();
    entity.statements = new_statements;
}

#[cfg(test)]
mod test {
    use spade_common::id_tracker::{ExprIdTracker, NameIdTracker};

    use crate::{self as spade_mir, assert_same_mir, ConstantValue};
    use crate::{entity, types::Type};

    use super::insert_wal_signals;
    use colored::Colorize;

    #[test]
    fn traced_register_has_wal_tracing_applied() {
        let mut input = entity!(&["name"]; (
            "clk", n(1, "clk"), Type::Bool,
            "x", n(2, "x"), Type::Bool,
            "rst", n(3, "rst"), Type::Bool,
        ) -> Type::Bool; {
            (const 0; Type::Bool; ConstantValue::Bool(true));
            (traced(n(0, "state"))
                reg n(0, "state"); Type::int(5); clock(n(1, "clk")); reset (n(3, "rst"), e(0)); n(2, "x"));
        } => n(2, "x"));

        let expected = entity!(&["name"]; (
            "clk", n(0, "clk"), Type::Bool,
            "x", n(2, "x"), Type::Bool,
            "rst", n(3, "rst"), Type::Bool,
        ) -> Type::Bool; {
            (const 0; Type::Bool; ConstantValue::Bool(true));
            (traced(n(1, "state"))
                reg n(1, "state"); Type::int(5); clock(n(0, "clk")); reset (n(3, "rst"), e(0)); n(2, "x"));
            (n(10, "state__wal_fsm_state"); Type::int(5); Alias; n(1, "state"));
            (n(11, "state__wal_fsm_clk"); Type::Bool; Alias; n(0, "clk"));
            (n(12, "state__wal_fsm_rst"); Type::Bool; Alias; n(3, "rst"));
        } => n(2, "x"));

        insert_wal_signals(
            &mut input,
            &mut ExprIdTracker::new(),
            &mut Some(&mut NameIdTracker::new_at(100)),
        );

        assert_same_mir!(&input, &expected);
    }

    #[test]
    fn traced_register_without_reset_has_wal_tracing_applied() {
        let mut input = entity!(&["name"]; (
            "clk", n(0, "clk"), Type::Bool,
            "x", n(2, "x"), Type::Bool,
        ) -> Type::Bool; {
            (const 0; Type::Bool; ConstantValue::Bool(true));
            (traced(n(1, "state"))
                reg n(1, "state"); Type::int(5); clock(n(0, "clk")); n(2, "x"));
        } => n(2, "x"));

        let expected = entity!(&["name"]; (
            "clk", n(0, "clk"), Type::Bool,
            "x", n(2, "x"), Type::Bool,
        ) -> Type::Bool; {
            (const 0; Type::Bool; ConstantValue::Bool(true));
            (traced(n(1, "state"))
                reg n(1, "state"); Type::int(5); clock(n(0, "clk")); n(2, "x"));
            (n(10, "state_n1__wal_fsm_state"); Type::int(5); Alias; n(1, "state"));
            (n(11, "state_n1__wal_fsm_clk"); Type::Bool; Alias; n(0, "clk"));
            (const 10; Type::Bool; ConstantValue::Bool(false));
            (n(12, "state_n1__wal_fsm_rst"); Type::Bool; Alias; e(10));
        } => n(2, "x"));

        insert_wal_signals(
            &mut input,
            &mut ExprIdTracker::new_at(10),
            &mut Some(&mut NameIdTracker::new_at(100)),
        );

        assert_same_mir!(&input, &expected);
    }

    #[test]
    fn traced_suffix_has_tracing_applied() {
        let inner = vec![
            ("a".to_string(), Type::int(4)),
            ("b".to_string(), Type::int(8)),
        ];
        let ty = Type::Struct(inner);

        let mut input = entity!(&["name"]; (
            "x", n(2, "x"), ty.clone(),
        ) -> Type::Bool; {
            (n(0, "y"); ty.clone(); Alias; n(2, "x"));
            (e(0); Type::int(4); IndexTuple((0)); n(0, "y"));
            (wal_trace(n(0, "y"), e(0), "__a__wal_suffix__", Type::int(4)));
            (e(1); Type::int(8); IndexTuple((1)); n(0, "y"));
            (wal_trace(n(0, "y"), e(1), "__b__wal_suffix__", Type::int(8)))
        } => n(2, "x"));

        let expected = entity!(&["name"]; (
            "x", n(2, "x"), ty.clone(),
        ) -> Type::Bool; {
            (n(0, "y"); ty.clone(); Alias; n(2, "x"));
            (e(0); Type::int(4); IndexTuple((0)); n(0, "y"));
            (n(4, "y__a__wal_suffix__"); Type::int(4); Alias; e(0));
            (e(1); Type::int(8); IndexTuple((1)); n(0, "y"));
            (n(5, "y__b__wal_suffix__"); Type::int(8); Alias; e(1));
        } => n(2, "x"));

        insert_wal_signals(
            &mut input,
            &mut ExprIdTracker::new_at(10),
            &mut Some(&mut NameIdTracker::new_at(100)),
        );

        assert_same_mir!(&input, &expected);
    }
}
