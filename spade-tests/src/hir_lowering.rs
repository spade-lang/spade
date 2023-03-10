#[cfg(test)]
mod tests {
    use crate::{
        build_and_compare_entities, build_entity, build_items, build_items_with_stdlib,
        snapshot_error,
    };
    use colored::Colorize;
    use spade_common::{
        location_info::WithLocation, num_ext::InfallibleToBigInt, num_ext::InfallibleToBigUint,
    };
    use spade_mir::{
        self,
        diff::{compare_entity, VarMap},
        diff_printing::translated_strings,
        entity, statement,
        types::Type,
        ConstantValue,
    };

    #[macro_export]
    macro_rules! assert_same_mir {
        ($got:expr, $expected:expr) => {
            let mut var_map = VarMap::new();

            if !compare_entity($got, $expected, &mut var_map) {
                let (got, expected) = translated_strings($got, $expected, &var_map);

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
        };
    }

    #[test]
    fn entity_definitions_are_correct() {
        let code = r#"
        entity name(a: int<16>, b: int<16>) -> int<16> {
            a
        }
        "#;

        let expected = entity!(&["name"]; (
                "a", n(0, "a"), Type::int(16),
                "b", n(1, "b"), Type::int(16)
        ) -> Type::int(16); {
        } => n(0, "a"));

        assert_same_mir!(&build_entity!(code), &expected);
    }

    #[test]
    fn if_expressions_have_correct_codegen() {
        let code = r#"
        entity name(c: bool, a: int<16>, b: int<16>) -> int<16> {
            if c
                a
            else
                b
        }
        "#;

        let expected = entity! {&["name"]; (
                "c", n(0, "c"), Type::Bool,
                "a", n(1, "a"), Type::int(16),
                "b", n(2, "b"), Type::int(16)
            ) -> Type::int(16); {
                (e(0); Type::int(16); Select; n(0, "c"), n(1, "a"), n(2, "b"))
            } => e(0)
        };

        assert_same_mir!(&build_entity!(code), &expected);
    }

    #[test]
    fn bool_literals_codegen() {
        let code = r#"
        entity always_true() -> bool {
            true
        }
        "#;

        let expected = entity! {&["always_true"]; () -> Type::Bool; {
            (const 0; Type::Bool; ConstantValue::Bool(true))
        } => e(0)};

        assert_same_mir!(&build_entity!(code), &expected);
    }

    #[test]
    fn negative_literals_give_correct_mir() {
        let code = "fn a() -> int<32> {
            -1
        }";

        let expected = entity! {&["a"]; () -> Type::int(32); {
            (const 0; Type::int(32); ConstantValue::int(-1))
        } => e(0)};

        assert_same_mir!(&build_entity!(code), &expected);
    }

    #[test]
    fn an_adder_is_buildable() {
        let code = r#"
        entity name(a: int<16>, b: int<16>) -> int<17> {
            a + b
        }
        "#;

        let expected = entity!(&["name"]; (
                "a", n(0, "a"), Type::int(16),
                "b", n(1, "b"), Type::int(16)
            ) -> Type::int(17); {
                (e(0); Type::int(17); Add; n(0, "a"), n(1, "b"))
            } => e(0)
        );

        assert_same_mir!(&build_entity!(code), &expected);
    }

    #[test]
    fn a_subtractor_is_buildable() {
        let code = r#"
        entity name(a: int<16>, b: int<16>) -> int<17> {
            a - b
        }
        "#;

        let expected = entity!(&["name"]; (
                "a", n(0, "a"), Type::int(16),
                "b", n(1, "b"), Type::int(16)
            ) -> Type::int(17); {
                (e(0); Type::int(17); Sub; n(0, "a"), n(1, "b"))
            } => e(0)
        );

        assert_same_mir!(&build_entity!(code), &expected);
    }

    #[test]
    fn a_left_shifter_is_buildable() {
        let code = r#"
        entity name(a: int<16>, b: int<16>) -> int<16> {
            a << b
        }
        "#;

        let expected = entity!(&["name"]; (
                "a", n(0, "a"), Type::int(16),
                "b", n(1, "b"), Type::int(16)
            ) -> Type::int(16); {
                (e(0); Type::int(16); LeftShift; n(0, "a"), n(1, "b"))
            } => e(0)
        );

        assert_same_mir!(&build_entity!(code), &expected);
    }

    #[test]
    fn a_right_shifter_is_buildable() {
        let code = r#"
        entity name(a: int<16>, b: int<16>) -> int<16> {
            a >> b
        }
        "#;

        let expected = entity!(&["name"]; (
                "a", n(0, "a"), Type::int(16),
                "b", n(1, "b"), Type::int(16)
            ) -> Type::int(16); {
                (e(0); Type::int(16); RightShift; n(0, "a"), n(1, "b"))
            } => e(0)
        );

        assert_same_mir!(&build_entity!(code), &expected);
    }

    #[test]
    fn a_arithmetic_right_shifter_is_buildable() {
        let code = r#"
        entity name(a: int<16>, b: int<16>) -> int<16> {
            a >>> b
        }
        "#;

        let expected = entity!(&["name"]; (
                "a", n(0, "a"), Type::int(16),
                "b", n(1, "b"), Type::int(16)
            ) -> Type::int(16); {
                (e(0); Type::int(16); ArithmeticRightShift; n(0, "a"), n(1, "b"))
            } => e(0)
        );

        assert_same_mir!(&build_entity!(code), &expected);
    }

    #[test]
    fn equals_operator_codegens_correctly() {
        let code = r#"
        entity name(a: int<16>, b: int<16>) -> bool {
            a == b
        }
        "#;

        let expected = entity!(&["name"]; (
                "a", n(0, "a"), Type::int(16),
                "b", n(1, "b"), Type::int(16)
            ) -> Type::Bool; {
                (e(0); Type::Bool; Eq; n(0, "a"), n(1, "b"))
            } => e(0)
        );

        assert_same_mir!(&build_entity!(code), &expected);
    }

    #[test]
    fn logical_and_operator_codegens_correctly() {
        let code = r#"
        entity name(a: bool, b: bool) -> bool {
            a && b
        }
        "#;

        let expected = entity!(&["name"]; (
                "a", n(0, "a"), Type::Bool,
                "b", n(1, "b"), Type::Bool
            ) -> Type::Bool; {
                (e(0); Type::Bool; LogicalAnd; n(0, "a"), n(1, "b"))
            } => e(0)
        );

        assert_same_mir!(&build_entity!(code), &expected);
    }

    #[test]
    fn logical_or_operator_codegens_correctly() {
        let code = r#"
        entity name(a: bool, b: bool) -> bool {
            a || b
        }
        "#;

        let expected = entity!(&["name"]; (
                "a", n(0, "a"), Type::Bool,
                "b", n(1, "b"), Type::Bool
            ) -> Type::Bool; {
                (e(0); Type::Bool; LogicalOr; n(0, "a"), n(1, "b"))
            } => e(0)
        );

        assert_same_mir!(&build_entity!(code), &expected);
    }

    #[test]
    fn bitwise_and_operator_codegens_correctly() {
        let code = r#"
        entity name(a: int<16>, b: int<16>) -> int<16> {
            a & b
        }
        "#;

        let expected = entity!(&["name"]; (
                "a", n(0, "a"), Type::int(16),
                "b", n(1, "b"), Type::int(16)
            ) -> Type::int(16); {
                (e(0); Type::int(16); BitwiseAnd; n(0, "a"), n(1, "b"))
            } => e(0)
        );

        assert_same_mir!(&build_entity!(code), &expected);
    }

    #[test]
    fn xor_operator_codegens_correctly() {
        let code = r#"
        entity name(a: bool, b: bool) -> bool {
            a ^^ b
        }
        "#;

        let expected = entity!(&["name"]; (
                "a", n(0, "a"), Type::Bool,
                "b", n(1, "b"), Type::Bool
            ) -> Type::Bool; {
                (e(0); Type::Bool; LogicalXor; n(0, "a"), n(1, "b"))
            } => e(0)
        );

        assert_same_mir!(&build_entity!(code), &expected);
    }

    #[test]
    fn bitwise_xor_operator_codegens_correctly() {
        let code = r#"
        entity name(a: int<3>, b: int<3>) -> int<3> {
            a ^ b
        }
        "#;

        let expected = entity!(&["name"]; (
                "a", n(0, "a"), Type::int(3),
                "b", n(1, "b"), Type::int(3)
            ) -> Type::int(3); {
                (e(0); Type::int(3); BitwiseXor; n(0, "a"), n(1, "b"))
            } => e(0)
        );

        assert_same_mir!(&build_entity!(code), &expected);
    }

    #[test]
    fn bitwise_or_operator_codegens_correctly() {
        let code = r#"
        entity name(a: int<16>, b: int<16>) -> int<16> {
            a | b
        }
        "#;

        let expected = entity!(&["name"]; (
                "a", n(0, "a"), Type::int(16),
                "b", n(1, "b"), Type::int(16)
            ) -> Type::int(16); {
                (e(0); Type::int(16); BitwiseOr; n(0, "a"), n(1, "b"))
            } => e(0)
        );

        assert_same_mir!(&build_entity!(code), &expected);
    }

    #[test]
    fn greater_than_operator_codegens_correctly() {
        let code = r#"
        entity name(a: int<16>, b: int<16>) -> bool {
            a > b
        }
        "#;

        let expected = entity!(&["name"]; (
                "a", n(0, "a"), Type::int(16),
                "b", n(1, "b"), Type::int(16)
            ) -> Type::Bool; {
                (e(0); Type::Bool; Gt; n(0, "a"), n(1, "b"))
            } => e(0)
        );

        assert_same_mir!(&build_entity!(code), &expected);
    }

    #[test]
    fn less_than_operator_codegens_correctly() {
        let code = r#"
        entity name(a: int<16>, b: int<16>) -> bool {
            a < b
        }
        "#;

        let expected = entity!(&["name"]; (
                "a", n(0, "a"), Type::int(16),
                "b", n(1, "b"), Type::int(16)
            ) -> Type::Bool; {
                (e(0); Type::Bool; Lt; n(0, "a"), n(1, "b"))
            } => e(0)
        );

        assert_same_mir!(&build_entity!(code), &expected);
    }

    #[test]
    fn greater_than_or_equals_operator_codegens_correctly() {
        let code = r#"
        entity name(a: int<16>, b: int<16>) -> bool {
            a >= b
        }
        "#;

        let expected = entity!(&["name"]; (
                "a", n(0, "a"), Type::int(16),
                "b", n(1, "b"), Type::int(16)
            ) -> Type::Bool; {
                (e(0); Type::Bool; Ge; n(0, "a"), n(1, "b"))
            } => e(0)
        );

        assert_same_mir!(&build_entity!(code), &expected);
    }

    #[test]
    fn less_than_or_equals_operator_codegens_correctly() {
        let code = r#"
        entity name(a: int<16>, b: int<16>) -> bool {
            a <= b
        }
        "#;

        let expected = entity!(&["name"]; (
                "a", n(0, "a"), Type::int(16),
                "b", n(1, "b"), Type::int(16)
            ) -> Type::Bool; {
                (e(0); Type::Bool; Le; n(0, "a"), n(1, "b"))
            } => e(0)
        );

        assert_same_mir!(&build_entity!(code), &expected);
    }

    #[test]
    fn usub_codegens_correctly() {
        let code = r#"
        entity name(a: int<16>) -> int<16> {
            -a
        }
        "#;

        let expected = entity!(&["name"]; (
                "a", n(0, "a"), Type::int(16),
            ) -> Type::int(16); {
                (e(0); Type::int(16); USub; n(0, "a"))
            } => e(0)
        );

        assert_same_mir!(&build_entity!(code), &expected);
    }

    #[test]
    fn not_codegens_correctly() {
        let code = r#"
        entity name(a: bool) -> bool {
            !a
        }
        "#;

        let expected = entity!(&["name"]; (
                "a", n(0, "a"), Type::Bool,
            ) -> Type::Bool; {
                (e(0); Type::Bool; Not; n(0, "a"))
            } => e(0)
        );

        assert_same_mir!(&build_entity!(code), &expected);
    }

    #[test]
    fn bitwise_not_codegens_correctly() {
        let code = r#"
        entity name(a: int<8>) -> int<8> {
            ~a
        }
        "#;

        let expected = entity!(&["name"]; (
                "a", n(0, "a"), Type::int(8),
            ) -> Type::int(8); {
                (e(0); (Type::int(8)); BitwiseNot; n(0, "a"))
            } => e(0)
        );

        assert_same_mir!(&build_entity!(code), &expected);
    }

    #[test]
    fn registers_work() {
        let code = r#"
        entity name(clk: clock, a: int<16>) -> int<16> {
            reg(clk) res = a;
            res
        }
        "#;

        let expected = entity! {&["name"]; (
                "clk", n(0, "clk"), Type::Bool,
                "a", n(1, "a"), Type::int(16),
            ) -> Type::int(16); {
                (reg n(0, "res"); Type::int(16); clock(n(0, "clk")); n(1, "a"))
            } => n(0, "res")
        };

        assert_same_mir!(&build_entity!(code), &expected);
    }

    #[test]
    fn registers_with_tuple_patterns_work() {
        let code = r#"
        entity name(clk: clock, a: (int<16>, int<8>)) -> int<16> {
            reg(clk) (x, y) = a;
            x
        }
        "#;

        let tup_inner = vec![Type::int(16), Type::int(8)];
        let tup_type = Type::Tuple(tup_inner.clone());
        let expected = entity! {&["name"]; (
                "clk", n(0, "clk"), Type::Bool,
                "a", n(1, "a"), tup_type.clone(),
            ) -> Type::int(16); {
                (reg e(0); tup_type; clock(n(0, "clk")); n(1, "a"));
                (n(2, "x"); Type::int(16); IndexTuple((0, tup_inner.clone())); e(0));
                (n(3, "y"); Type::int(8); IndexTuple((1, tup_inner)); e(0));
            } => n(2, "x")
        };

        assert_same_mir!(&build_entity!(code), &expected);
    }

    #[test]
    fn registers_with_reset_work() {
        let code = r#"
        entity name(clk: clock, rst: bool, a: int<16>) -> int<16> {
            reg(clk) res reset (rst: 0) = a;
            res
        }
        "#;

        let expected = entity! {&["name"]; (
                "clk", n(0, "clk"), Type::Bool,
                "rst", n(2, "rst"), Type::Bool,
                "a", n(1, "a"), Type::int(16),
            ) -> Type::int(16); {
                (const 0; Type::int(16); ConstantValue::int(0));
                (reg n(0, "res");
                    Type::int(16);
                    clock(n(0, "clk"));
                    reset (n(2, "rst"), e(0));
                    n(1, "a"))
            } => n(0, "res")
        };

        assert_same_mir!(&build_entity!(code), &expected);
    }

    #[test]
    fn untyped_let_bindings_work() {
        let code = r#"
        entity name(clk: clock, a: int<16>) -> int<16> {
            let res = a;
            res
        }
        "#;

        let expected = entity! {&["name"]; (
                "clk", n(0, "clk"), Type::Bool,
                "a", n(1, "a"), Type::int(16),
            ) -> Type::int(16); {
                (n(2, "res"); Type::int(16); Alias; n(1, "a"));
            } => n(2, "res")
        };

        assert_same_mir!(&build_entity!(code), &expected);
    }

    #[test]
    fn array_literals_work() {
        let code = r#"
            entity x() -> [int<3>; 3] {
                [0, 1, 2]
            }
        "#;

        let array_type = Type::Array {
            inner: Box::new(Type::int(3)),
            length: 3u32.to_biguint(),
        };

        let expected = entity!(&["x"]; () -> array_type.clone(); {
            (const 0; Type::int(3); ConstantValue::int(0));
            (const 1; Type::int(3); ConstantValue::int(1));
            (const 2; Type::int(3); ConstantValue::int(2));
            (e(4); array_type; ConstructArray; e(0), e(1), e(2));
        } => e(4));

        assert_same_mir!(&build_entity!(code), &expected);
    }

    #[test]
    fn array_indexing_works() {
        let code = r#"
            entity x(a: [int<2>; 5]) -> int<2> {
                let idx: int<3> = 2;
                a[idx]
            }
        "#;

        let array_type = Type::Array {
            inner: Box::new(Type::int(2)),
            length: 5u32.to_biguint(),
        };

        let expected = entity!(&["x"]; (
                "a", n(0, "a"), array_type,
        ) -> Type::int(2); {
            (const 0; Type::int(3); ConstantValue::int(2));
            (n(1, "idx"); Type::int(3); Alias; e(0));
            (e(4); Type::int(2); IndexArray; n(0, "a"), n(1, "idx"));
        } => e(4));

        assert_same_mir!(&build_entity!(code), &expected);
    }

    #[test]
    fn tuple_indexing_and_creation_works() {
        let code = r#"
        entity name(a: int<16>, b: int<8>) -> int<8> {
            let compound = (a, b);
            compound#1
        }
        "#;

        let tup_inner = vec![Type::int(16), Type::int(8)];
        let tup_type = Type::Tuple(tup_inner.clone());
        let expected = entity!(&["name"]; (
                "a", n(0, "a"), Type::int(16),
                "b", n(1, "b"), Type::int(8),
            ) -> Type::int(8); {
                (e(1); tup_type.clone(); ConstructTuple; n(0, "a"), n(1, "b"));
                (n(2, "compound"); tup_type; Alias; e(1));
                (e(0); Type::int(8); IndexTuple((1, tup_inner)); n(2, "compound"));
            } => e(0)
        );

        assert_same_mir!(&build_entity!(code), &expected);
    }

    #[test]
    fn tuple_destructuring_works() {
        let code = r#"
        entity name(x: (int<16>, int<8>)) -> int<16> {
            let (a, b) = x;
            a
        }
        "#;

        let tup_inner = vec![Type::int(16), Type::int(8)];
        let tup_type = Type::Tuple(tup_inner.clone());
        let expected = entity!(&["name"]; (
                "x", n(0, "x"), tup_type.clone(),
            ) -> Type::int(16); {
                // NOTE: This line technically isn't required in this case as it is just an alias,
                // but removing it seems a bit pointless as it would introduce a special case in
                // the code
                (e(0); tup_type; Alias; n(0, "x"));
                (n(1, "a"); Type::int(16); IndexTuple((0, tup_inner.clone())); n(0, "x"));
                (n(2, "b"); Type::int(8); IndexTuple((1, tup_inner)); n(0, "x"))
            } => n(1, "a")
        );

        assert_same_mir!(&build_entity!(code), &expected);
    }

    #[test]
    fn entity_instantiation_works() {
        let code = r#"
            entity sub(a: int<16>) -> int<16> {
                a
            }

            entity top() -> int<16> {
                inst sub(0)
            }
        "#;

        let inst_name = spade_mir::UnitName::from_strs(&["sub"]);

        let mut expected = vec![
            entity!(&["sub"]; (
                    "a", n(0, "a"), Type::int(16)
                ) -> Type::int(16); {
                } => n(0, "a")
            ),
            entity!(&["top"]; () -> Type::int(16); {
                (const 1; Type::int(16); ConstantValue::int(0));
                (e(0); Type::int(16); Instance((inst_name, None)); e(1))
            } => e(0)),
        ];

        let mut result = build_items(code);

        expected.sort_by_key(|e| e.name.clone());
        result.sort_by_key(|e| e.name.clone());

        for (exp, res) in expected.into_iter().zip(result.into_iter()) {
            assert_same_mir!(&res, &exp);
        }
    }

    #[test]
    fn pipeline_instantiation_works() {
        let code = r#"
            pipeline(2) sub(clk: clock, a: int<16>) -> int<16> {
                reg;
                reg;
                a
            }

            entity top(clk: clock) -> int<16> {
                inst(2) sub(clk, 0)
            }
        "#;

        let inst_name = spade_mir::UnitName::from_strs(&["sub"]);

        let mut expected = vec![
            entity!(&["sub"]; (
                    "clk", n(100, "clk"), Type::Bool,
                    "a", n(0, "a"), Type::int(16)
                ) -> Type::int(16); {
                    (reg n(1, "s1_a"); Type::int(16); clock (n(100, "clk")); n(0, "a"));
                    (reg n(2, "s2_a"); Type::int(16); clock (n(100, "clk")); n(1, "s1_a"));
                } => n(2, "s2_a")
            ),
            entity!(&["top"]; ("clk", n(100, "clk"), Type::Bool) -> Type::int(16); {
                (const 1; Type::int(16); ConstantValue::int(0));
                (e(0); Type::int(16); Instance((inst_name, None)); n(100, "clk"), e(1))
            } => e(0)),
        ];

        let mut result = build_items(code);

        expected.sort_by_key(|e| e.name.clone());
        result.sort_by_key(|e| e.name.clone());

        for (exp, res) in expected.into_iter().zip(result.into_iter()) {
            assert_same_mir!(&res, &exp);
        }
    }

    #[test]
    fn pipelines_work() {
        let code = r#"
            pipeline(3) pl(clk: clock, a: int<16>) -> int<18> {
                    let x = a << a;
                reg;
                    let y = x + a;
                reg;
                    let res = y + y;
                reg;
                    res
            }
        "#;

        let expected = entity!(&["pl"]; (
                "clk", n(3, "clk"), Type::Bool,
                "a", n(0, "a"), Type::int(16),
            ) -> Type::int(18); {
                // Pipeline registers
                (reg n(2, "s1_a"); Type::int(16); clock(n(3, "clk")); n(0, "a"));
                (reg n(4, "s1_x"); Type::int(16); clock(n(3, "clk")); n(10, "x"));
                (reg n(21, "s2_a"); Type::int(16); clock(n(3, "clk")); n(2, "s1_a"));
                (reg n(22, "s2_x"); Type::int(16); clock(n(3, "clk")); n(4, "s1_x"));
                (reg n(23, "s2_y"); Type::int(17); clock(n(3, "clk")); n(11, "y"));
                (reg n(31, "s3_a"); Type::int(16); clock(n(3, "clk")); n(21, "s2_a"));
                (reg n(32, "s3_x"); Type::int(16); clock(n(3, "clk")); n(22, "s2_x"));
                (reg n(33, "s3_y"); Type::int(17); clock(n(3, "clk")); n(23, "s2_y"));
                (reg n(34, "s3_res"); Type::int(18); clock(n(3, "clk")); n(6, "res"));
                // Stage 0
                (e(0); Type::int(16); LeftShift; n(0, "a"), n(0, "a"));
                (n(10, "x"); Type::int(16); Alias; e(0));

                // Stage 1
                (e(1); Type::int(17); Add; n(4, "s1_x"), n(2, "s1_a"));
                (n(11, "y"); Type::int(17); Alias; e(1));

                // Stage 3
                (e(2); Type::int(18); Add; n(23, "s2_y"), n(23, "s2_y"));
                (n(6, "res"); Type::int(18); Alias; e(2));
            } => n(34, "s3_res")
        );

        let result = build_entity!(code);

        assert_same_mir!(&result, &expected);
    }

    #[test]
    fn pipelines_with_ports_work() {
        let code = r#"
            pipeline(3) pl(clk: clock, a: &mut int<16>) -> &mut int<16> {
                reg;
                reg;
                reg;
                    a
            }
        "#;

        let expected = entity!(&["pl"]; (
                "clk", n(3, "clk"), Type::Bool,
                "a", n(0, "a"), Type::backward(Type::int(16)),
            ) -> Type::backward(Type::int(16)); {
            } => n(0, "a")
        );

        let result = build_entity!(code);

        assert_same_mir!(&result, &expected);
    }

    #[test]
    fn subpipes_do_not_get_extra_delay() {
        let code = r#"
            pipeline(3) sub(clk: clock) -> int<18> __builtin__

            pipeline(3) pl(clk: clock) -> int<18> {
                    let res = inst(3) sub(clk);
                reg*3;
                    res
            }
        "#;

        let inst_name = spade_mir::UnitName::from_strs(&["sub"]);
        let expected = entity!(&["pl"]; (
                "clk", n(3, "clk"), Type::Bool,
            ) -> Type::int(18); {
                // Stage 0
                (e(0); Type::int(18); Instance((inst_name, None)); n(3, "clk"));
                (n(1, "res"); Type::int(18); Alias; e(0));
            } => n(1, "res")
        );

        let result = build_entity!(code);

        assert_same_mir!(&result, &expected);
    }

    #[test]
    fn pipelines_returning_expressions_work() {
        let code = r#"
            pipeline(3) pl(clk: clock, a: int<16>) -> int<17> {
                reg;
                reg;
                reg;
                a+a
            }
        "#;

        let expected = entity!(&["pl"]; (
                "clk", n(3, "clk"), Type::Bool,
                "a", n(0, "a"), Type::int(16),
            ) -> Type::int(17); {
                // Stage 0
                (reg n(2, "s1_a"); Type::int(16); clock(n(3, "clk")); n(0, "a"));

                // Stage 1
                (reg n(21, "s2_a"); Type::int(16); clock(n(3, "clk")); n(2, "s1_a"));

                // Stage 3
                (reg n(31, "s3_a"); Type::int(16); clock(n(3, "clk")); n(21, "s2_a"));

                // Output
                (e(3); Type::int(17); Add; n(31, "s3_a"), n(31, "s3_a"));
            } => e(3)
        );

        let result = build_entity!(code);

        assert_same_mir!(&result, &expected);
    }

    #[test]
    fn backward_pipeline_references_work() {
        let code = r#"
            pipeline(1) pl(clk: clock, a: int<16>) -> int<16> {
                reg;
                    stage(-1).a
            }
        "#;

        let expected = entity!(&["pl"]; (
                "clk", n(3, "clk"), Type::Bool,
                "a", n(0, "a"), Type::int(16),
            ) -> Type::int(16); {
                (reg n(31, "s1_a"); Type::int(16); clock(n(3, "clk")); n(0, "a"));

                // Output
            } => n(0, "a")
        );

        let result = build_entity!(code);

        assert_same_mir!(&result, &expected);
    }

    #[test]
    fn forward_pipeline_references_work() {
        let code = r#"
            pipeline(2) pl(clk: clock, a: bool) -> int<16> {
                reg;
                    let b = stage(+1).x;
                reg;
                    let x = 0;
                    b
            }
        "#;

        let expected = entity!(&["pl"]; (
                "clk", n(3, "clk"), Type::Bool,
                "a", n(4, "a"), Type::Bool,
            ) -> Type::int(16); {
                (reg n(14, "s1_a"); Type::Bool; clock(n(3, "clk")); n(4, "a"));
                (reg n(24, "s2_a"); Type::Bool; clock(n(3, "clk")); n(14, "s1_a"));
                (reg n(20, "s2_b"); Type::int(16); clock(n(3, "clk")); n(0, "b"));
                // Stage 0
                // Stage 1
                (n(0, "b"); Type::int(16); Alias; n(1, "x"));
                // Stage 2
                (const 1; Type::int(16); ConstantValue::int(0));
                (n(1, "x"); Type::int(16); Alias; e(1));

                // Output
            } => n(20, "s2_b")
        );

        let result = build_entity!(code);

        assert_same_mir!(&result, &expected);
    }

    #[test]
    fn absolute_pipeline_references_work() {
        let code = r#"
            pipeline(2) pl(clk: clock, a: bool) -> int<16> {
                reg;
                    let b = stage(a).x;
                reg;
                    'a
                    let x = 0;
                    b
            }
        "#;

        let expected = entity!(&["pl"]; (
                "clk", n(3, "clk"), Type::Bool,
                "a", n(4, "a"), Type::Bool,
            ) -> Type::int(16); {
                (reg n(14, "s1_a"); Type::Bool; clock(n(3, "clk")); n(4, "a"));
                (reg n(24, "s2_a"); Type::Bool; clock(n(3, "clk")); n(14, "s1_a"));
                (reg n(20, "s2_b"); Type::int(16); clock(n(3, "clk")); n(0, "b"));
                // Stage 0
                // Stage 1
                (n(0, "b"); Type::int(16); Alias; n(1, "x"));
                // Stage 2
                (const 1; Type::int(16); ConstantValue::int(0));
                (n(1, "x"); Type::int(16); Alias; e(1));

                // Output
            } => n(20, "s2_b")
        );

        let result = build_entity!(code);

        assert_same_mir!(&result, &expected);
    }

    #[test]
    fn correct_codegen_for_forward_references() {
        let code = r#"
            entity A() -> int<16> __builtin__

            pipeline(1) pl(clk: clock) -> int<16> {
                    let x_ = inst A();
                reg;
                    let x = stage(-1).x_;
                    x
            }
            "#;

        let inst_name = spade_mir::UnitName::from_strs(&["A"]);

        let expected = entity!(&["pl"]; (
                "clk", n(3, "clk"), Type::Bool,
            ) -> Type::int(16); {
                (reg n(10, "s1_x_"); Type::int(16); clock(n(3, "clk")); n(0, "x_"));
                // Stage 0
                (e(0); Type::int(16); Instance((inst_name, None)););
                (n(0, "x_"); Type::int(16); Alias; e(0));
                // Stage 1
                (n(1, "x"); Type::int(16); Alias; n(0, "x_"));
            } => n(1, "x")
        );

        let result = build_entity!(code);

        assert_same_mir!(&result, &expected);
    }

    #[test]
    fn struct_instantiation_works() {
        let code = r#"
            struct X {payload: bool}

            entity test(payload: bool) -> X {
                X$(payload)
            }
        "#;

        let mir_struct = Type::Tuple(vec![Type::Bool]);

        let expected = vec![entity!(&["test"]; (
                "payload", n(0, "payload"), Type::Bool,
            ) -> mir_struct.clone(); {
                (e(1); mir_struct; ConstructTuple; n(0, "payload"));
            } => e(1)
        )];

        build_and_compare_entities!(code, expected);
    }

    #[test]
    fn struct_field_access_and_creation_works() {
        let code = r#"
        struct X {a: int<16>, b: int<8>}

        entity name(a: int<16>, b: int<8>) -> int<8> {
            let compound = X$(a, b);
            compound.b
        }
        "#;

        let tup_inner = vec![Type::int(16), Type::int(8)];
        let tup_type = Type::Tuple(tup_inner.clone());
        let expected = vec![entity!(&["name"]; (
                "a", n(0, "a"), Type::int(16),
                "b", n(1, "b"), Type::int(8),
            ) -> Type::int(8); {
                (e(1); tup_type.clone(); ConstructTuple; n(0, "a"), n(1, "b"));
                (n(2, "compound"); tup_type; Alias; e(1));
                (e(0); Type::int(8); IndexTuple((1, tup_inner)); n(2, "compound"));
            } => e(0)
        )];

        build_and_compare_entities!(code, &expected);
    }

    #[test]
    fn enum_instantiation_works() {
        let code = r#"
            enum X {
                A{payload: bool},
                B
            }

            entity test(payload: bool) -> X {
                X::A(payload)
            }
        "#;

        let mir_enum = Type::Enum(vec![vec![Type::Bool], vec![]]);

        let expected = vec![entity!(&["test"]; (
                "payload", n(0, "payload"), Type::Bool,
            ) -> mir_enum.clone(); {
                (e(1); mir_enum; ConstructEnum({variant: 0, variant_count: 2}); n(0, "payload"));
            } => e(1)
        )];

        build_and_compare_entities!(code, expected);
    }

    #[test]
    fn enum_instantiation_with_subexpression_works() {
        let code = r#"
            enum X {
                A{payload: int<16>},
                B
            }

            entity test(payload: int<15>) -> X {
                X::A(payload + 1)
            }
        "#;

        let mir_enum = Type::Enum(vec![vec![Type::int(16)], vec![]]);

        let expected = vec![entity!(&["test"]; (
                "payload", n(0, "payload"), Type::int(15),
            ) -> mir_enum.clone(); {
                (const 3; Type::int(15); ConstantValue::int(1));
                (e(2); Type::int(16); Add; n(0, "payload"), e(3));
                (e(1); mir_enum; ConstructEnum({variant: 0, variant_count: 2}); e(2));
            } => e(1)
        )];

        build_and_compare_entities!(code, expected);
    }

    #[test]
    fn enum_instantiation_with_fixed_generics_works() {
        let code = r#"
            enum X {
                A{payload: int<5>},
                B
            }

            entity test(payload: int<5>) -> X {
                X::A(payload)
            }
        "#;

        let mir_enum = Type::Enum(vec![vec![Type::int(5)], vec![]]);

        let expected = vec![entity!(&["test"]; (
                "payload", n(0, "payload"), Type::int(5),
            ) -> mir_enum.clone(); {
                (e(1); mir_enum; ConstructEnum({variant: 0, variant_count: 2}); n(0, "payload"));
            } => e(1)
        )];

        build_and_compare_entities!(code, expected);
    }

    #[test]
    fn enum_instantiation_with_full_generics_works() {
        let code = r#"
            enum Option<T> {
                Some{payload: T},
                None
            }

            entity test(payload: int<5>) -> Option<int<5>> {
                Option::Some(payload)
            }
        "#;

        let mir_enum = Type::Enum(vec![vec![Type::int(5)], vec![]]);

        let expected = vec![entity!(&["test"]; (
                "payload", n(0, "payload"), Type::int(5),
            ) -> mir_enum.clone(); {
                (e(1); mir_enum; ConstructEnum({variant: 0, variant_count: 2}); n(0, "payload"));
            } => e(1)
        )];

        build_and_compare_entities!(code, expected);
    }

    #[test]
    fn enum_match_works() {
        let code = r#"
            enum Option<T> {
                Some{ payload: T },
                None
            }

            entity unwrap_or_0(e: Option<int<16>>) -> int<16> {
                match e {
                    Option::Some(x) => x,
                    other => 0
                }
            }
        "#;

        let mir_type = Type::Enum(vec![vec![Type::int(16)], vec![]]);

        let expected = vec![
            entity! {&["unwrap_or_0"]; ("e", n(0, "e"), mir_type.clone()) -> Type::int(16); {
                // Conditions for branches
                (n(1, "x"); Type::int(16); EnumMember({variant: 0, member_index: 0, enum_type: mir_type.clone()}); n(0, "e"));
                (e(2); Type::Bool; IsEnumVariant({variant: 0, enum_type: mir_type}); n(0, "e"));
                (const 10; Type::Bool; ConstantValue::Bool(true));
                (e(11); Type::Bool; LogicalAnd; e(2), e(10));
                (const 3; Type::Bool; ConstantValue::Bool(true));
                (const 5; Type::int(16); ConstantValue::int(0));
                (e(6); Type::int(16); Match; e(11), n(1, "x"), e(3), e(5));
            } => e(6)},
        ];

        build_and_compare_entities!(code, expected);
    }

    #[test]
    fn boolean_patterns_work() {
        let code = r#"
            entity uwu(e: bool) -> bool {
                match e {
                    true => false,
                    false => true
                }
            }
        "#;

        let expected = vec![
            entity! {&["uwu"]; ("e", n(0, "e"), Type::Bool) -> Type::Bool; {
                // Conditions for branches
                (const 3; Type::Bool; ConstantValue::Bool(false));
                (e(2); Type::Bool; LogicalNot; n(0, "e"));
                (const 4; Type::Bool; ConstantValue::Bool(true));
                (e(6); Type::Bool; Match; n(0, "e"), e(3), e(2), e(4));
            } => e(6)},
        ];

        build_and_compare_entities!(code, expected);
    }

    #[test]
    fn integer_patterns_work() {
        let code = r#"
            entity uwu(e: int<16>) -> bool {
                match e {
                    0 => true,
                    _ => false
                }
            }
        "#;

        let expected = vec![
            entity! {&["uwu"]; ("e", n(0, "e"), Type::int(16)) -> Type::Bool; {
                // Conditions for branches
                (const 1; Type::int(16); ConstantValue::int(0));
                (e(2); Type::Bool; Eq; n(0, "e"), e(1));
                (const 4; Type::Bool; ConstantValue::Bool(true));
                (const 5; Type::Bool; ConstantValue::Bool(true));
                (const 6; Type::Bool; ConstantValue::Bool(false));
                (e(6); Type::Bool; Match; e(2), e(4), e(5), e(6));
            } => e(6)},
        ];

        build_and_compare_entities!(code, expected);
    }

    #[test]
    fn tuple_patterns_conditions_work() {
        let code = r#"
            entity name(a: (bool, bool)) -> int<16> {
                match a {
                    (true, true) => 0,
                    (false, true) => 1,
                    _ => 2,
                }
            }
        "#;

        let tup_inner = vec![Type::Bool, Type::Bool];
        let tup_type = Type::Tuple(tup_inner.clone());
        let expected = entity! {&["name"]; (
                "a", n(0, "a"), tup_type
            ) -> Type::int(16); {
                (e(0); Type::Bool; IndexTuple((0, tup_inner.clone())); n(0, "a"));
                (e(1); Type::Bool; IndexTuple((1, tup_inner.clone())); n(0, "a"));
                (e(3); Type::Bool; LogicalAnd; e(0), e(1));
                (const 10; Type::int(16); ConstantValue::int(0));
                (e(20); Type::Bool; IndexTuple((0, tup_inner.clone())); n(0, "a"));
                (e(21); Type::Bool; IndexTuple((1, tup_inner)); n(0, "a"));
                (e(4); Type::Bool; LogicalNot; e(20));
                (e(5); Type::Bool; LogicalAnd; e(4), e(21));
                (const 11; Type::int(16); ConstantValue::int(1));
                (const 12; Type::Bool; ConstantValue::Bool(true));
                (const 13; Type::int(16); ConstantValue::int(2));
                // Condition for branch 1
                (e(6); Type::int(16); Match; e(3), e(10), e(5), e(11), e(12), e(13))
            } => e(6)
        };

        assert_same_mir!(&build_entity!(code), &expected);
    }

    #[test]
    fn enum_match_with_sub_pattern_conditions_work() {
        let code = r#"
            enum Option<T> {
                Some{ payload: T },
                None
            }

            entity unwrap_or_0(e: Option<int<16>>) -> int<16> {
                match e {
                    Option::Some(10) => 5,
                    Option::Some(x) => x,
                    other => 0
                }
            }
        "#;

        let mir_type = Type::Enum(vec![vec![Type::int(16)], vec![]]);

        let expected = vec![
            entity! {&["unwrap_or_0"]; ("e", n(0, "e"), mir_type.clone()) -> Type::int(16); {
                // Conditions for branch 1
                (e(11); Type::int(16); EnumMember({variant: 0, member_index: 0, enum_type: mir_type.clone()}); n(0, "e"));
                (e(15); Type::Bool; IsEnumVariant({variant: 0, enum_type: mir_type.clone()}); n(0, "e"));
                (const 10; Type::int(16); ConstantValue::int(10));
                (e(12); Type::Bool; Eq; e(11), e(10));
                (e(14); Type::Bool; LogicalAnd; e(15), e(12));
                (const 13; Type::int(16); ConstantValue::int(5));

                // Condition for branch 2
                (n(1, "x"); Type::int(16); EnumMember({variant: 0, member_index: 0, enum_type: mir_type.clone()}); n(0, "e"));
                (e(2); Type::Bool; IsEnumVariant({variant: 0, enum_type: mir_type}); n(0, "e"));
                (const 3; Type::Bool; ConstantValue::Bool(true));
                (e(20); Type::Bool; LogicalAnd; e(2), e(3));

                (const 21; Type::Bool; ConstantValue::Bool(true));
                (const 5; Type::int(16); ConstantValue::int(0));
                (e(6); Type::int(16); Match; e(14), e(13), e(20), n(1, "x"), e(21), e(5));
            } => e(6)},
        ];

        build_and_compare_entities!(code, expected);
    }

    #[test]
    fn struct_match_with_subpatterns_work() {
        let code = r#"
            struct X {
                a: bool,
            }

            fn test(x: X) -> int<10> {
                match x {
                    X(true) => 10,
                    _ => 0
                }
            }
        "#;

        let ty = Type::Tuple(vec![Type::Bool]);

        let expected = vec![
            entity! {&["test"]; ("x", n(0, "x"), ty.clone()) -> Type::int(10); {
                (e(1); Type::Bool; IndexTuple((0, vec![Type::Bool])); n(0, "x"));
                (const 10; Type::Bool; ConstantValue::Bool(true));
                (e(11); Type::Bool; LogicalAnd; e(10), e(1));
                (const 0; Type::int(10); ConstantValue::int(10));
                (const 4; Type::Bool; ConstantValue::Bool(true));
                (const 2; Type::int(10); ConstantValue::int(0));
                (e(3); Type::int(10); Match; e(11), e(0), e(4), e(2));
            } => e(3)},
        ];

        build_and_compare_entities!(code, expected);
    }

    #[test]
    fn registers_with_struct_patterns_work() {
        let code = r#"
        struct X{a: int<16>, b: int<8>}

        entity name(clk: clock, a: X) -> int<16> {
            reg(clk) X(x, y) = a;
            x
        }
        "#;

        let tup_inner = vec![Type::int(16), Type::int(8)];
        let tup_type = Type::Tuple(tup_inner.clone());
        let expected = vec![entity! {&["name"]; (
                "clk", n(0, "clk"), Type::Bool,
                "a", n(1, "a"), tup_type.clone(),
            ) -> Type::int(16); {
                (reg e(0); tup_type; clock(n(0, "clk")); n(1, "a"));
                (n(2, "x"); Type::int(16); IndexTuple((0, tup_inner.clone())); e(0));
                (n(3, "y"); Type::int(8); IndexTuple((1, tup_inner)); e(0));
            } => n(2, "x")
        }];

        build_and_compare_entities!(code, expected);
    }

    #[test]
    fn registers_with_struct_patterns_with_named_bindings_work() {
        let code = r#"
        struct X{a: int<16>, b: int<8>}

        entity name(clk: clock, a: X) -> int<16> {
            reg(clk) X$(b: y, a: x) = a;
            x
        }
        "#;

        let tup_inner = vec![Type::int(16), Type::int(8)];
        let tup_type = Type::Tuple(tup_inner.clone());
        let expected = vec![entity! {&["name"]; (
                "clk", n(0, "clk"), Type::Bool,
                "a", n(1, "a"), tup_type.clone(),
            ) -> Type::int(16); {
                (reg e(0); tup_type; clock(n(0, "clk")); n(1, "a"));
                (n(2, "x"); Type::int(16); IndexTuple((0, tup_inner.clone())); e(0));
                (n(3, "y"); Type::int(8); IndexTuple((1, tup_inner)); e(0));
            } => n(2, "x")
        }];

        build_and_compare_entities!(code, expected);
    }

    #[test]
    fn concatenation_works() {
        let code = r#"
            use std::conv::concat;
            entity name(a: int<16>, b: int<8>) -> int<24> {
                a `concat` b
            }
        "#;

        let expected = vec![entity! {&["name"]; (
                "a", n(0, "a"), Type::int(16),
                "b", n(1, "b"), Type::int(8),
            ) -> Type::int(24); {
                (e(0); Type::int(24); Concat; n(0, "a"), n(1, "b"))
            } => e(0)
        }];

        build_and_compare_entities!(code, expected);
    }

    #[test]
    fn concatenation_infers_size() {
        let code = r#"
            use std::conv::concat;
            entity name(a: int<16>, b: int<8>) -> int<24> {
                let x = a `concat` b;
                0
            }
        "#;

        let expected = vec![entity! {&["name"]; (
                "a", n(0, "a"), Type::int(16),
                "b", n(1, "b"), Type::int(8),
            ) -> Type::int(24); {
                (e(0); Type::int(24); Concat; n(0, "a"), n(1, "b"));
                (n(2, "x"); Type::int(24); Alias; e(0));
                (const 1; Type::int(24); ConstantValue::int(0));
            } => e(1)
        }];

        build_and_compare_entities!(code, expected);
    }

    #[test]
    fn zero_extend_works() {
        let code = r#"
            use std::conv::zext;
            entity name(a: int<16>) -> int<24> {
                zext(a)
            }
        "#;

        let expected = vec![entity! {&["name"]; (
                "a", n(0, "a"), Type::int(16),
            ) -> Type::int(24); {
                (e(0); Type::int(24); ZeroExtend({extra_bits: 8u32.to_biguint()}); n(0, "a"))
            } => e(0)
        }];

        build_and_compare_entities!(code, expected);
    }

    #[test]
    fn assert_statements_lower_correctly() {
        let code = r#"entity name(x: int<16>, y: int<16>) -> int<16> {
            assert x == y;
            x
        }"#;

        let expected = vec![entity! {&["name"]; (
            "x", n(0, "x"), Type::int(16),
            "y", n(1, "y"), Type::int(16),
        ) -> Type::int(16); {
                (e(0); Type::Bool; Eq; n(0, "x"), n(1, "y"));
                (assert; e(0));
            } => n(0, "x")
        }];

        build_and_compare_entities!(code, expected);
    }

    #[test]
    fn div_pow2_works() {
        let code = r#"
            use std::ops::div_pow2;
            entity name(a: int<16>) -> int<16> {
                a `div_pow2` 2
            }
        "#;

        let expected = vec![entity! {&["name"]; (
                "a", n(0, "a"), Type::int(16),
            ) -> Type::int(16); {
                (const 0; Type::int(16); ConstantValue::int(2));
                (e(1); Type::int(16); DivPow2; n(0, "a"), e(0))
            } => e(1)
        }];

        build_and_compare_entities!(code, expected);
    }

    #[test]
    fn free_standing_generic_compiles() {
        let code = r#"
            fn identity<T>(x: T) -> T {
                x
            }
        "#;

        build_items(code);
    }

    #[test]
    fn generic_instantiation_works() {
        let code = r#"
            fn identity<T>(x: T) -> T {
                x
            }

            fn x(x: bool) -> bool {
                identity(x)
            }
        "#;

        let inst_name = spade_mir::UnitName::Escaped {
            name: "identity[56]".to_string(),
            path: vec!["identity".to_string()],
        };

        let expected = vec![
            entity! {&["x"]; (
                "x", n(0, "x"), Type::Bool,
            ) -> Type::Bool; {
                (e(0); Type::Bool; Instance((inst_name.clone(), None)); n(0, "x"))
            } => e(0)},
            // Monomorphised identity function
            entity! {&inst_name; (
                "x", n(0, "x"), Type::Bool,
            ) -> Type::Bool; {
            } => n(0, "x")},
        ];

        build_and_compare_entities!(code, expected);
    }

    snapshot_error! {
        invalid_field_access,
        "
        struct X {}

        entity main(x: X) -> int<8> {
            x.not_a_field
        }
       "
    }

    snapshot_error! {
        mismatched_pipeline_depth_match,
        "
        pipeline(5) X(clk: clock) -> bool __builtin__
        pipeline(4) Y(clk: clock) -> bool __builtin__

        pipeline(5) main(clk: clock, x: bool) -> bool {
                let _ = match x {
                    true => inst(5) X(clk),
                    false => inst(4) Y(clk)
                };
            reg*5;
                x
        }
       "
    }

    snapshot_error! {
        mismatched_pipeline_depth_if,
        "
        pipeline(5) X(clk: clock) -> bool __builtin__
        pipeline(4) Y(clk: clock) -> bool __builtin__

        pipeline(5) main(clk: clock, x: bool) -> bool {
                let _ = if x {
                    inst(5) X(clk)
                }
                else {
                    inst(4) Y(clk)
                };
            reg*5;
                x
        }
       "
    }

    snapshot_error! {
        using_unavailable_variable_causes_error,
        "
        pipeline(5) X(clk: clock) -> bool {reg*5; false}

        pipeline(5) main(clk: clock, x: bool) -> bool {
                let x = inst(5) X(clk);
            reg;
                let res = x;
            reg*4;
                res
        }
       "
    }

    snapshot_error! {
        referring_to_unavailable_variable_causes_error,
        "
        pipeline(5) X(clk: clock) -> bool {reg*5; false}

        pipeline(6) main(clk: clock, x: bool) -> bool {
                let x = inst(5) X(clk);
            reg*5;
                let res = stage(-1).x;
            reg;
                res
        }
       "
    }

    snapshot_error! {
        absolute_referring_to_unavailable_variable_causes_error,
        "
        pipeline(5) X(clk: clock) -> bool {reg*5; false}

        pipeline(6) main(clk: clock, x: bool) -> bool {
                let x = inst(5) X(clk);
            reg*4;
                'here
            reg;
                let res = stage(here).x;
            reg;
                res
        }
       "
    }

    snapshot_error! {
        instantiating_builtin_generic_which_is_non_intrinsic_is_error,
        "
            fn a<T>() -> T __builtin__

            fn main() -> int<32> {
                a()
            }
        "
    }

    #[test]
    fn instantiating_builtin_generic_pipeline_which_is_non_intrinsic_is_error() {
        let code = "
            pipeline(1) a<T>(t: T) -> T {
                reg;
                    t
            }

            entity main() -> int<32> {
                inst(1) a(0)
            }
        ";
        build_items(code);
    }

    snapshot_error! {
        late_type_inference_failures_are_reported_well,
        "
            fn a<N>(x: int<N>, y: int<32>) -> int<33> {
                x + y
            }

            fn main() -> int<33> {
                let x: int<16> = 0;
                let y: int<32> = 0;
                a(x, y)
            }
            "
    }

    #[test]
    fn named_arguments_get_passed_in_correct_order() {
        let code = r#"
            fn sub(x: bool, y: bool) -> bool __builtin__

            fn test(a: bool, b: bool) -> bool {
                sub$(y: a, x: b)
            }
        "#;

        let inst_name = spade_mir::UnitName::from_strs(&["sub"]);

        let expected = vec![entity! {&["test"]; (
            "a", n(0, "a"), Type::Bool,
            "b", n(1, "b"), Type::Bool,
        ) -> Type::Bool; {
            (e(0); Type::Bool; Instance((inst_name, None)); n(1, "b"), n(0, "a"))
        } => e(0)}];

        build_and_compare_entities!(code, expected);
    }

    snapshot_error! {
        graceful_message_if_type_inference_fails_for_register,
        "
            entity x(clk: clock) -> bool {
                reg(clk) x = 0;
                true
            }
        "
    }

    snapshot_error! {
        graceful_message_if_type_inference_fails_for_binding_in_pipeline,
        "
            pipeline(1) x(clk: clock) -> bool {
                    let x = 0;
                reg;
                    true
            }
        "
    }

    #[test]
    fn comptime_exclusion_works() {
        let code = r#"
            $config USE_B = 0

            fn test(a: bool, b: bool, c: bool) -> bool {
                let a_ = a;
                $if USE_B == 0 {let b_ = b;}
                $if USE_B == 1 {let c_ = c;}
                a_
            }
        "#;

        let expected = vec![entity! {&["test"]; (
            "a", n(0, "a"), Type::Bool,
            "b", n(1, "b"), Type::Bool,
            "c", n(2, "c"), Type::Bool,
        ) -> Type::Bool; {
                (n(3, "a_"); Type::Bool; Alias; n(0, "a"));
                (n(4, "b_"); Type::Bool; Alias; n(1, "b"));
        } => n(3, "a_")}];

        build_and_compare_entities!(code, expected);
    }

    #[test]
    fn comptime_exclusion_works_with_many_statements() {
        let code = r#"
            $config X = 1

            fn test(a: bool, b: bool, c: bool) -> bool {
                let a_ = a;
                $if X == 0 {
                    let b_ = b;
                    let c_ = c;
                }
                a_
            }
        "#;

        let expected = vec![entity! {&["test"]; (
            "a", n(0, "a"), Type::Bool,
            "b", n(1, "b"), Type::Bool,
            "c", n(2, "c"), Type::Bool,
        ) -> Type::Bool; {
                (n(3, "a_"); Type::Bool; Alias; n(0, "a"));
        } => n(3, "a_")}];

        build_and_compare_entities!(code, expected);
    }

    #[test]
    fn comptime_exclusion_works_with_else_statements() {
        let code = r#"
            $config X = 1

            fn test(a: bool, b: bool, c: bool) -> bool {
                let a_ = a;
                $if X == 0 {
                    let b_ = b;
                } $else {
                    let c_ = c;
                }
                a_
            }
        "#;

        let expected = vec![entity! {&["test"]; (
            "a", n(0, "a"), Type::Bool,
            "b", n(1, "b"), Type::Bool,
            "c", n(2, "c"), Type::Bool,
        ) -> Type::Bool; {
                (n(3, "a_"); Type::Bool; Alias; n(0, "a"));
                (n(4, "c_"); Type::Bool; Alias; n(2, "c"))
        } => n(3, "a_")}];

        build_and_compare_entities!(code, expected);
    }

    #[test]
    fn comptime_exclusion_works_for_all_operators() {
        let code = r#"
            $config X = 1

            fn test(a: bool, b: bool, c: bool) -> bool {
                $if X < 1 {
                    let a_ = a;
                }
                $if X < 2 {
                    let b_ = a;
                }
                $if X <= 1 {
                    let c_ = a;
                }
                $if X <= 0 {
                    let d_ = a;
                }
                $if X > 0 {
                    let e_ = a;
                }
                $if X > 1 {
                    let f_ = a;
                }
                $if X >= 1 {
                    let g_ = a;
                }
                $if X >= 2 {
                    let h_ = a;
                }
                a
            }
        "#;

        let expected = vec![entity! {&["test"]; (
            "a", n(0, "a"), Type::Bool,
            "b", n(1, "b"), Type::Bool,
            "c", n(2, "c"), Type::Bool,
        ) -> Type::Bool; {
                (n(3, "b_"); Type::Bool; Alias; n(0, "a"));
                (n(4, "c_"); Type::Bool; Alias; n(0, "a"));
                (n(5, "e_"); Type::Bool; Alias; n(0, "a"));
                (n(6, "g_"); Type::Bool; Alias; n(0, "a"));
        } => n(0, "a")}];

        build_and_compare_entities!(code, expected);
    }

    snapshot_error! {
        useful_error_message_when_passing_non_comptime_value_as_comptime,
        "
            fn test() -> bool {
                let x = 0;
                $if x < 1 {
                    let a_ = a;
                }
                false
            }
        "
    }

    snapshot_error! {
        expected_unit,
        "
            fn f() -> bool {
                let x = 0;
                x()
            }
        "
    }

    snapshot_error! {
        expected_type_symbol,
        "
            fn f() -> bool {
                let A = false;
                let a: A = false;
                false
            }
        "
    }

    snapshot_error! {
        expected_value,
        "
            fn ff() -> bool { true }

            entity f(clk: clock) -> bool {
                let a = ff;
                true
            }
        "
    }

    snapshot_error! {
        expected_variable,
        "
            fn ff() -> bool { true }

            pipeline(1) f(clk: clock) -> bool {
                reg;
                    stage(-1).ff
            }
        "
    }

    snapshot_error! {
        is_a_type_bool,
        "
            fn f() -> bool {
                let a = bool;
                bool
            }
        "
    }

    #[test]
    fn assigning_ports_to_variables_works() {
        let code = r#"
            mod std {mod ports{
                entity new_mut_wire<T>() -> &mut T __builtin__
            }}

            entity test() -> &mut int<10> {
                let x = inst std::ports::new_mut_wire();
                x
            }
        "#;

        build_items(code);
    }

    #[test]
    fn struct_method_call_calls_the_right_function() {
        let code = r#"
            struct X {}
            impl X {
                fn a(self) -> bool {
                    true
                }
            }

            entity test(x: X) -> bool {
                x.a()
            }
        "#;

        let inst_name = spade_mir::UnitName::from_strs(&["impl_0", "a"]);

        let x_type = Type::Tuple(vec![]);
        let expected = vec![
            entity! {&["test"]; (
                "x", n(0, "x"), x_type.clone(),
            ) -> Type::Bool; {
                (e(0); Type::Bool; Instance((inst_name, None)); n(0, "x"))
            } => e(0)},
            entity! {&["impl_0", "a"]; (
                "self", n(1, "self"), x_type,
            ) -> Type::Bool; {
                (const 0; Type::Bool; ConstantValue::Bool(true));
            } => e(0)},
        ];

        build_and_compare_entities!(code, expected);
    }

    #[test]
    fn struct_method_call_calls_the_right_function_with_named_args() {
        let code = r#"
            struct X {}
            impl X {
                fn a(self, arg: bool) -> bool {
                    arg
                }
            }

            entity test(x: X) -> bool {
                x.a$(arg: true)
            }
        "#;

        let inst_name = spade_mir::UnitName::from_strs(&["impl_0", "a"]);

        let x_type = Type::Tuple(vec![]);
        let expected = vec![
            entity! {&["test"]; (
                "x", n(0, "x"), x_type.clone(),
            ) -> Type::Bool; {
                (const 1; Type::Bool; ConstantValue::Bool(true));
                (e(0); Type::Bool; Instance((inst_name, None)); n(0, "x"), e(1))
            } => e(0)},
            entity! {&["impl_0", "a"]; (
                "self", n(1, "self"), x_type,
                "arg", n(2, "arg"), Type::Bool,
            ) -> Type::Bool; {
            } => n(2, "arg")},
        ];

        build_and_compare_entities!(code, expected);
    }

    snapshot_error! {
        instantiating_enum_as_entity_gives_decent_error,
        "
        enum X {
            A
        }

        entity x() -> X {
            inst X::A()
        }
        "
    }

    snapshot_error! {
        instantiating_struct_as_entity_gives_decent_error,
        "
        struct X {
            a: bool
        }

        entity x() -> X {
            inst X(true)
        }
        "
    }

    snapshot_error! {
        expect_function_got_entity_error_works,
        "entity x() -> bool {true}

        entity test() -> bool {
            x()
        }"
    }

    snapshot_error! {
        expect_function_got_pipeline_error_works,
        "pipeline(0) x(clk: clock) -> bool {true}

        entity test(clk: clock) -> bool {
            x(clk)
        }"
    }

    snapshot_error! {
        expect_pipeline_got_function_error_works,
        "fn x() -> bool {true}

        entity test() -> bool {
            inst(0) x()
        }"
    }

    snapshot_error! {
        expect_pipeline_got_entity_error_works,
        "entity x(clk: clock) -> bool {true}

        entity test(clk: clock) -> bool {
            inst(0) x(clk)
        }"
    }

    snapshot_error! {
        expect_entity_got_function_error_works,
        "fn x() -> bool {true}

        entity test() -> bool {
            inst x()
        }"
    }

    snapshot_error! {
        expect_entity_got_pipeline_error_works,
        "pipeline(0) x(clk: clock) -> bool {true}

        entity test(clk: clock) -> bool {
            inst x(clk)
        }"
    }

    #[test]
    fn comptime_expression_works() {
        let code = r#"
            $config X = 0

            fn main() -> int<3> {
                let x = $if X == 0 {
                    1
                };
                x
            }
        "#;
        let result = build_entity!(code);

        let expected = entity!(&["main"]; (
        ) -> Type::Int(3u32.to_biguint()); {
            (const 0; Type::Int(3u32.to_biguint()); ConstantValue::Int(1.to_bigint()));
            (n(0, "x"); Type::Int(3u32.to_biguint()); Alias; e(0))
        } => n(0, "x"));

        assert_same_mir!(&result, &expected);
    }

    snapshot_error! {
        non_const_memory_elements_is_error,
        "
            use std::mem::clocked_memory_init;
            use std::mem::read_memory;

            entity test(clk: clock, a: int<8>) -> int<8> {
                // lifeguard spade#151
                let idx: int<1> = 0;
                let mem = inst clocked_memory_init(clk, [(false, idx, 0)], [a, a]);
                inst read_memory(mem, 0)
            }
        "
    }

    #[test]
    fn memory_initial_values_work() {
        let code = r#"
            use std::mem::clocked_memory_init;
            use std::mem::read_memory;

            entity test(clk: clock) -> int<8> {
                // lifeguard spade#151
                let ports: [(bool, int<1>, int<8>); 0] = [];
                let mem: Memory<int<8>, 2> = inst clocked_memory_init(clk, ports, [0, 1]);
                0
            }
        "#;

        let ports_type = Type::Array {
            inner: Box::new(Type::Tuple(vec![
                Type::Bool,
                Type::Int(1u32.to_biguint()),
                Type::Int(8u32.to_biguint()),
            ])),
            length: 0u32.to_biguint(),
        };

        let init_type = Type::Array {
            inner: Box::new(Type::Int(8u32.to_biguint())),
            length: 2u32.to_biguint(),
        };

        let mem_type = Type::Memory {
            inner: Box::new(Type::Int(8u32.to_biguint())),
            length: 2u32.to_biguint(),
        };

        let expected = vec![entity! {&["test"]; (
            "clk", n(0, "clk"), Type::Bool,
        ) -> Type::Int(8u32.to_biguint()); {
            (e(10); ports_type.clone(); ConstructArray;);
            (n(11, "ports"); ports_type; Alias; e(10));
            (const(12); Type::Int(8u32.to_biguint()); ConstantValue::Int(0.to_bigint()));
            (const(13); Type::Int(8u32.to_biguint()); ConstantValue::Int(1.to_bigint()));

            (e(14); init_type; ConstructArray; e(12), e(13));

            (e(1); mem_type.clone(); DeclClockedMemory({
                write_ports: 0u32.to_biguint(),
                addr_w: 1u32.to_biguint(),
                inner_w: 8u32.to_biguint(),
                elems: 2u32.to_biguint(),
                initial: Some(vec![
                    vec![statement!(const 7; Type::Int(8u32.to_biguint()); ConstantValue::Int(0.to_bigint()))],
                    vec![statement!(const 8; Type::Int(8u32.to_biguint()); ConstantValue::Int(1.to_bigint()))],
                ])
            }); n(0, "clk"), n(11, "ports"));
            (n(2, "mem"); mem_type; Alias; e(1));

            (const 0; Type::Int(8u32.to_biguint()); ConstantValue::Int(0.to_bigint()));
        } => e(0)}];

        build_and_compare_entities!(code, expected);
    }
}

#[cfg(test)]
mod argument_list_tests {
    use crate::snapshot_error;

    snapshot_error! {
        too_many_args,
        "fn test(a: bool, b: bool) -> bool __builtin__
        fn main() -> bool {
            test(true, true, true)
        }
        "
    }

    snapshot_error! {
        too_few_args,
        "fn test(a: bool, b: bool) -> bool __builtin__
        fn main() -> bool {
            test(true)
        }
        "
    }

    snapshot_error! {
        shorthand_named_argument_missing,
        "fn test(a: bool, b: bool) -> bool __builtin__
        fn main() -> bool {
            let (a, b, c) = (true, true, true);
            test$(a)
        }
        "
    }

    snapshot_error! {
        shorthand_duplicate_named_argument_missing,
        "fn test(a: bool, b: bool) -> bool __builtin__
        fn main() -> bool {
            let (a, b, c) = (true, true, true);
            test$(a, a, b)
        }
        "
    }

    snapshot_error! {
        long_named_argument_missing,
        "fn test(a: bool, b: bool) -> bool __builtin__
        fn main() -> bool {
            test$(a: true)
        }
        "
    }

    snapshot_error! {
        long_duplicate_named_arg,
        "fn test(a: bool, b: bool) -> bool __builtin__
        fn main() -> bool {
            test$(a: true, a: true, b: true)
        }
        "
    }

    snapshot_error! {
        long_fake_named_arg,
        "fn test(a: bool, b: bool) -> bool __builtin__
        fn main() -> bool {
            test$(a: true, c: true, b: true)
        }
        "
    }

    snapshot_error! {
        named_struct_patterns_errors_if_missing_bindings,
        "struct Test{a: bool, b: bool}

        fn main() -> Test {
            Test$(a: true)
        }
        "
    }

    snapshot_error! {
        named_struct_patterns_errors_if_missing_multiple_bindings,
        "struct Test{a: bool, b: bool}

        fn main() -> Test {
            Test$()
        }
        "
    }

    snapshot_error! {
        named_struct_patterns_errors_if_binding_to_undefined_name,
        "struct Test{a: bool, b: bool}

        fn main() -> Test {
            Test$(a: true, b: true, c: true)
        }
        "
    }

    snapshot_error! {
        named_struct_patterns_errors_if_multiple_bindings_to_same_name,
        "struct Test{a: bool, b: bool}

        fn main() -> Test {
            Test$(a: true, a: true, b: true)
        }
        "
    }

    snapshot_error! {
        truncating_to_larger_value,
        "
        use std::conv::trunc;
        fn main() -> int<8> {
            let a: int<4> = 0;
            let b: int<8> = std::conv::trunc(a);
            b
        }
        "
    }
}
