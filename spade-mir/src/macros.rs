/// Macros for writing mir.
/// Requires the crate to be in scope, i.e. `use spade_mir;`

#[macro_export]
macro_rules! value_name {
    (n($id:expr, $debug_name:expr)) => {
        spade_mir::ValueName::_test_named($id, $debug_name.to_string())
    };
    (e($id:expr)) => {
        spade_mir::ValueName::Expr(spade_common::id_tracker::ExprID($id))
    };
}

#[macro_export]
macro_rules! if_tracing {
    () => {None};
    ($traced_kind:ident $traced_name:tt) => {Some(spade_mir::value_name!($traced_kind $traced_name))}
}

#[macro_export]
macro_rules! optional_reset {
    () => {None};
    (($rst_trig_kind:ident $rst_trig_name:tt, $rst_val_kind:ident $rst_val_name:tt)) => {
        Some((
            spade_mir::value_name!($rst_trig_kind $rst_trig_name),
            spade_mir::value_name!($rst_val_kind $rst_val_name)
        ))
    }
}

#[macro_export]
macro_rules! optional_initial {
    () => {
        None
    };
    (($val:expr)) => {
        Some($val)
    };
}

#[macro_export]
macro_rules! statement {
    // Normal constants
    (
        const $id:expr; $ty:expr; $value:expr
    ) => {
        spade_mir::Statement::Constant(spade_mir::ValueName::Expr(spade_common::id_tracker::ExprID($id)), $ty, $value)
    };
    // Bindings
    (
        $name_kind:ident $name:tt;
        $type:expr;
        $operator:ident $(($operator_args:tt))?$({$operator_struct_args:tt})?;
        $($arg_kind:ident $arg_name:tt),*
    ) => {
        spade_mir::Statement::Binding(spade_mir::Binding {
            name: spade_mir::value_name!($name_kind $name),
            operator: spade_mir::Operator::$operator$($operator_args)?,
            operands: vec![
                $(spade_mir::value_name!($arg_kind $arg_name)),*
            ],
            ty: $type,
            loc: None,
        })
    };
    //register with async reset
    (
        $(traced($traced_kind:ident $traced_name:tt))?
        reg $name_kind:ident $name:tt;
        $type:expr;
        clock ($clk_name_kind:ident $clk_name:tt);
        $(reset $reset:tt)?
        $(initial $initial:tt)?;
        $val_kind:ident $val_name:tt
    ) => {
        spade_mir::Statement::Register(spade_mir::Register {
            name: spade_mir::value_name!($name_kind $name),
            ty: $type,
            clock: spade_mir::value_name!($clk_name_kind $clk_name),
            reset: spade_mir::optional_reset!($($reset)?),
            initial: spade_mir::optional_initial!($($initial)?),
            value: spade_mir::value_name!($val_kind $val_name),
            loc: None,
            traced: spade_mir::if_tracing!($($traced_kind $traced_name)?)
        })
    };
    // Register without reset
    (
        $(traced($traced_kind:ident $traced_name:tt))?
        reg $name_kind:ident $name:tt;
        $type:expr;
        clock ($clk_name_kind:ident $clk_name:tt);
        $val_kind:ident $val_name:tt
    ) => {
        spade_mir::Statement::Register(spade_mir::Register {
            name: spade_mir::value_name!($name_kind $name),
            ty: $type,
            clock: spade_mir::value_name!($clk_name_kind $clk_name),
            reset: None,
            initial: None,
            value: spade_mir::value_name!($val_kind $val_name),
            loc: None,
            traced: spade_mir::if_tracing!($($traced_kind $traced_name)?)
        })
    };
    // Set statement
    (set; $lhs_kind:ident $lhs_name:tt; $rhs_kind:ident $rhs_name:tt) => {
        spade_mir::Statement::Set{
            target: spade_mir::value_name!($lhs_kind $lhs_name).nowhere(),
            value: spade_mir::value_name!($rhs_kind $rhs_name).nowhere()
        }
    };
    (
        assert; $name_kind:ident $name:tt
    ) => {
        spade_mir::Statement::Assert(spade_mir::value_name!($name_kind $name).nowhere())
    };
    (wal_trace ($name_kind:ident $name_name:tt, $val_kind:ident $val_name:tt, $suffix:expr, $ty:expr) ) => {
        spade_mir::Statement::WalTrace{
            name: spade_mir::value_name!($name_kind $name_name),
            val: spade_mir::value_name!($val_kind $val_name),
            suffix: $suffix.into(),
            ty: $ty
        }
    }
}

/// Example
/// ```
/// use spade_mir as mir;
/// use spade_mir::entity;
/// use spade_mir::types::Type;
/// entity!("pong"; ("_i_clk", n(0, "clk"), Type::Bool) -> Type::int(6); {
///     (e(0); Type::int(6); Add; n(1, "value"));
///     (const 0; Type::int(10); ConstantValue::Int(6));
///     (reg n(1, "value"); Type::int(6); clock (n(0, "clk")); e(0))
/// } => n(1, "value"));
/// ```
#[macro_export]
macro_rules! entity {
    ($name:expr; (
            $( $arg_name:expr, $arg_intern_kind:ident $arg_intern_name:tt, $arg_type:expr ),* $(,)?
        ) -> $output_type:expr; {
            $( $statement:tt );*
            $(;)?
        } => $output_name_kind:ident $output_name:tt
    ) => {
        spade_mir::Entity {
            name: spade_mir::unit_name::IntoUnitName::_test_into_unit_name($name),
            inline: false,
            inputs: vec![
                $(
                    spade_mir::MirInput {
                        name: $arg_name.to_string(),
                        val_name: spade_mir::value_name!($arg_intern_kind $arg_intern_name),
                        ty: $arg_type,
                        no_mangle: None
                    }
                ),*
            ],
            output: spade_mir::value_name!($output_name_kind $output_name),
            output_type: $output_type,
            statements: vec![
                $( spade_mir::statement! $statement ),*
            ],
            verilog_attr_groups: vec![],
        }
    }
}

#[macro_export]
macro_rules! assert_same_mir {
    ($got:expr, $expected:expr) => {{
        let mut var_map = spade_mir::diff::VarMap::new();

        if !spade_mir::diff::compare_entity($got, $expected, &mut var_map) {
            let (got, expected) =
                spade_mir::diff_printing::translated_strings($got, $expected, &var_map);

            println!("{}:\n{}", "got".red(), got);
            println!("{}", "==============================================".red());
            println!("{}:\n{}", "expected".green(), expected);
            println!(
                "{}",
                "==============================================".green()
            );
            println!("{}", prettydiff::diff_chars(&got, &expected));
            println!(
                "{}",
                "==============================================".yellow()
            );
            panic!("Code mismatch")
        }
    }};
}

#[cfg(test)]
mod tests {
    use spade_common::id_tracker::ExprID;
    use spade_common::name::{NameID, Path};
    use spade_mir::unit_name::UnitNameKind;

    use crate::{self as spade_mir, MirInput, UnitName};
    use crate::{types::Type, Binding, ConstantValue, Operator, Register, Statement, ValueName};

    #[test]
    fn value_name_parsing_works() {
        assert_eq!(
            value_name!(n(0, "test")),
            ValueName::_test_named(0, "test".to_string())
        );
        assert_eq!(value_name!(e(0)), ValueName::Expr(ExprID(0)));
    }

    #[test]
    fn binding_parsing_works() {
        let expected = Statement::Binding(Binding {
            name: ValueName::Expr(ExprID(0)),
            operator: Operator::Add,
            operands: vec![
                ValueName::Expr(ExprID(1)),
                ValueName::_test_named(1, "test".to_string()),
            ],
            ty: Type::Bool,
            loc: None,
        });

        assert_eq!(
            statement!(e(0); Type::Bool; Add; e(1), n(1, "test")),
            expected
        );
    }

    #[test]
    fn named_parsing_works() {
        let expected = Statement::Binding(Binding {
            name: ValueName::_test_named(0, "string".to_string()),
            operator: Operator::Add,
            operands: vec![
                ValueName::Expr(ExprID(1)),
                ValueName::_test_named(1, "test".to_string()),
            ],
            ty: Type::Bool,
            loc: None,
        });

        assert_eq!(
            statement!(n(0, "string"); Type::Bool; Add; e(1), n(1, "test")),
            expected
        );
    }

    #[test]
    fn register_parsing_works() {
        let expected = Statement::Register(Register {
            name: ValueName::_test_named(0, "test".into()),
            ty: Type::int(5),
            clock: ValueName::_test_named(1, "clk".into()),
            reset: None,
            initial: None,
            value: ValueName::Expr(ExprID(0)),
            loc: None,
            traced: Some(ValueName::Expr(ExprID(2))),
        });

        assert_eq!(
            statement!(traced(e(2)) reg n(0, "test"); Type::int(5); clock (n(1, "clk")); e(0)),
            expected
        );
    }

    #[test]
    fn register_with_reset_parsing_works() {
        let expected = Statement::Register(Register {
            name: ValueName::_test_named(0, "test".into()),
            ty: Type::int(5),
            clock: ValueName::_test_named(1, "clk".into()),
            reset: Some((ValueName::Expr(ExprID(1)), ValueName::Expr(ExprID(2)))),
            initial: None,
            value: ValueName::Expr(ExprID(0)),
            loc: None,
            traced: None,
        });

        assert_eq!(
            statement!(reg n(0, "test"); Type::int(5); clock (n(1, "clk")); reset (e(1), e(2)); e(0)),
            expected
        );
    }

    #[test]
    fn entity_parsing_works() {
        let expected = crate::Entity {
            name: UnitName {
                kind: UnitNameKind::Escaped {
                    name: "pong".to_string(),
                    path: vec!["pong".to_string()],
                },
                source: NameID(0, Path::from_strs(&["pong"])),
            },
            inline: false,
            inputs: vec![MirInput {
                name: "_i_clk".to_string(),
                val_name: ValueName::_test_named(0, "clk".to_string()),
                ty: Type::Bool,
                no_mangle: None,
            }],
            output: ValueName::_test_named(1, "value".to_string()),
            output_type: Type::int(6),
            statements: vec![
                statement!(e(0); Type::int(6); Add; n(1, "value")),
                statement!(reg n(1, "value"); Type::int(6); clock (n(0, "clk")); e(0)),
            ],
            verilog_attr_groups: vec![],
        };

        let result = entity!(&["pong"]; ("_i_clk", n(0, "clk"), Type::Bool) -> Type::int(6); {
                (e(0); Type::int(6); Add; n(1, "value"));
                (reg n(1, "value"); Type::int(6); clock (n(0, "clk")); e(0))
            } => n(1, "value"));

        assert_eq!(result, expected);
    }

    #[test]
    fn constant_parsing_works() {
        let expected = Statement::Constant(
            ValueName::Expr(ExprID(0)),
            Type::int(10),
            ConstantValue::int(6),
        );

        let result = statement!(const 0; Type::int(10); ConstantValue::int(6));

        assert_eq!(result, expected);
    }
}
