#[cfg(test)]
mod tests {
    use crate::{build_items, snapshot_error};

    snapshot_error! {
        single_missing_enum_branch_errors,
        "
                enum X {
                    A,
                    B,
                }

                fn uwu(x: X) -> bool {
                    match x {
                        X::A => true,
                    }
                }
                "
    }

    snapshot_error! {
        multiple_missing_enum_branch_errors,
        "
                enum X {
                    A,
                    B,
                    C,
                    D,
                }

                fn uwu(x: X) -> bool {
                    match x {
                        X::A => true,
                    }
                }
                "
    }

    snapshot_error! {
        even_more_missing_enum_branch_errors,
        "
                enum X {
                    A,
                    B,
                    C,
                    D,
                    E,
                    F,
                }

                fn uwu(x: X) -> bool {
                    match x {
                        X::A => true,
                    }
                }
                "
    }

    snapshot_error! {
        missing_subpatterns_error_correctly,
        "
                enum X {
                    A{a: bool},
                    B
                }

                fn uwu(x: X) -> bool {
                    match x {
                        X::B => true,
                    }
                }

            "
    }

    snapshot_error! {
        missing_tuple_patterns_error_correctly,
        "
                enum X {
                    A,
                    B
                }

                fn uwu(x: (X, X)) -> bool {
                    match x {
                        (X::A, X::A) => true,
                    }
                }
            "
    }

    snapshot_error! {
        missing_tuple_patterns_error_correctly2,
        "
                enum X {
                    A,
                    B
                }

                fn uwu(x: (X, X)) -> bool {
                    match x {
                        (X::A, X::A) => true,
                        (X::B, _) => true,
                    }
                }
            "
    }

    snapshot_error! {
        missing_tuple_patterns_error_correctly3,
        "
                enum X {
                    A,
                    B
                }

                fn uwu(x: (X, X)) -> bool {
                    match x {
                        (X::A, X::A) => true,
                        (X::A, X::B) => true,
                    }
                }
            "
    }

    snapshot_error! {
        missing_inner_members_works,
        "
                enum X {
                    A,
                    B
                }

                enum Y {
                    A{x1: X, x2: X},
                }

                fn uwu(y: Y) -> bool {
                    match y {
                        Y::A(X::A, X::A) => true,
                    }
                }
            "
    }

    snapshot_error! {
        missing_inner_members_works2,
        "
                enum X {
                    A,
                    B
                }

                enum Y {
                    A{x1: X, x2: X},
                }

                fn uwu(y: Y) -> bool {
                    match y {
                        Y::A(X::A, X::A) => true,
                        Y::A(X::A, _) => true,
                    }
                }
            "
    }

    snapshot_error! {
        missing_boolean_patterns_work,
        "
                fn uwu(x: bool) -> bool {
                    match x {
                        true => true,
                    }
                }
            "
    }

    snapshot_error! {
        missing_struct_pattern_works,
        "
                struct A {x: bool, y: bool}

                fn uwu(a: A) -> bool {
                    match a {
                        A(true, true) => true,
                    }
                }
            "
    }

    snapshot_error! {
        missing_integer_patterns_reports_correctly,
        "
                fn uwu(a: int<8>) -> bool {
                    match a {
                        0 => true,
                    }
                }
                "
    }

    snapshot_error! {
        missing_integer_patterns_reports_correctly2,
        "
                fn uwu(a: int<8>) -> bool {
                    match a {
                        0 => true,
                        1 => true,
                        4 => true,
                    }
                }
                "
    }

    snapshot_error! {
        zero_more_not_covered_should_not_be_present,
        "
        fn test(in: (bool, bool, bool)) -> bool {
            match in {
                (true, true, true) => true,
                (false, true, true) => true,
                (false, false, true) => true,
                (false, false, false) => true,
            }
        }
        "
    }

    snapshot_error! {
        struct_missing_pattern_message_is_good,
        "
            struct A {
                x: bool,
                y: bool,
            }
        fn test(in: A) -> bool {
            match in {
                A(true, true) => true
            }
        }
        "
    }

    snapshot_error! {
        struct_missing_pattern_message_with_named_args_is_good,
        "
            struct A {
                x: bool,
                y: bool,
            }
        fn test(in: A) -> bool {
            match in {
                A$(y:true, x: true) => true,
                A$(y:true, x: false) => true,
                A$(y:false, x: false) => true,
            }
        }
        "
    }

    snapshot_error! {
        enum_missing_pattern_message_with_named_args_is_good,
        "
            enum A {
                X{a: bool},
                Y
            }
        fn test(in: A) -> bool {
            match in {
                A::Y => true
            }
        }
        "
    }

    #[test]
    fn matching_on_clock_with_wildcard_works() {
        let code = r#"
            entity match_clock(clk: clock) -> bool {
                match clk {
                    _ => true
                }
            }
            "#;

        build_items(code);
    }

    snapshot_error! {
        refutable_pattern_let_binding_errors,
        "
            fn A() -> bool {
                let true = false;
                false
            }
        "
    }

    snapshot_error! {
        refutable_pattern_reg_errors,
        "
            entity A(clk: clock) -> bool {
                reg(clk) true = false;
                false
            }
        "
    }

    snapshot_error! {
        non_exhaustive_pattern_with_sub_integer_range_causes_good_error_message,
        "
        fn test(in: (int<8>, bool)) -> bool {
            match in {
                (val, true) => true,
            }
        }
        "
    }
}
