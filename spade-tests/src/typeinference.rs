use crate::{build_items, snapshot_error};

#[test]
fn type_inference_works_for_arrays() {
    let code = r#"
        entity x() -> [int<2>; 3] {
            [0, 1, 2]
        }
    "#;

    build_items(code);
}

#[test]
fn type_inference_works_for_generics() {
    let code = r#"
    enum Option<T> {
        Some{value: T},
        None
    }
    entity name() -> Option<int<16>> {
        Option::Some(0)
    }
    "#;
    build_items(code);
}

#[test]
fn type_inference_works_for_int_patterns() {
    let code = r#"
    entity name(x: int<16>) -> int<16> {
        match x {
            0 => 0,
            _ => 1
        }
    }
    "#;

    build_items(code);
}

#[test]
fn type_inference_works_for_array_indexing() {
    let code = r#"
    entity name(x: [int<16>; 10]) -> int<16> {
        x[0]
    }
    "#;

    build_items(code);
}

#[test]
fn type_inference_works_for_declared_variables() {
    let code = r#"
    entity name() -> int<16> {
        decl x;
        let a = x;
        let x = 0;
        a
    }
    "#;

    build_items(code);
}

#[test]
fn type_inference_works_for_usub_on_literals() {
    let code = r#"
    entity name() -> int<16> {
        -1
    }
    "#;

    build_items(code);
}

#[test]
fn type_inference_works_for_bools_with_not_operator() {
    let code = r#"
    entity name() -> int<16> {
        let test = !false;
        0
    }
    "#;

    build_items(code);
}

snapshot_error!(
    backward_tuple_indexing_with_type_error_errors_nicely,
    "entity name(x: ~(bool, bool)) -> int<32> {
        x#0
    }"
);

snapshot_error!(
    useful_error_if_indexing_backward_array,
    "
    entity name(x: ~[bool; 10]) -> int<32> {
        x[0]
    }
    "
);

snapshot_error! {
    type_error_on_port_set_mismatch,
    "
    // NOTE: returning bool because we don't support unit types
    entity set_port(p: ~int<10>, v: int<9>) -> bool {
        set p = v;
        false
    }
    "
}

snapshot_error! {
    type_error_on_port_set_to_port,
    "
    // NOTE: returning bool because we don't support unit types
    entity set_port(p: ~int<10>, v: ~int<10>) -> bool {
        set p = v;
        false
    }
    "
}

snapshot_error!(
    return_type_mismatch,
    r#"
    entity main() -> int<1> {
        let a: int<2> = 0;
        a
    }
    "#
);

snapshot_error!(
    type_error_when_overflow_is_possible,
    "
    entity main(a: int<16>, b: int<16>) -> int<16> {
        a + b
    }
    "
);

snapshot_error! {
    multiplication_errors_if_overflow,
    "
    entity main(a: int<14>, b: int<16>) -> int<32> {
        a * b
    }
    "
}

snapshot_error! {
    counter_without_trunc_causes_type_error,
    "
        entity counter(clk: clk, rst: bool) -> int<8> {
            reg(clk) x reset (rst: 0) = x + 1;
            x
        }
    "
}

snapshot_error! {
    type_error_has_replacements_applied,
    "
        entity counter(clk: clk, rst: bool) -> (int<8>, int<8>) {
            decl x, y;

            let x_at_max = x == 8;
            let y_at_max = y == 6;

            reg(clk) x reset (rst: 0) =
                if x_at_max {
                    x
                }
                else {
                    x + 1
                };

            reg(clk) y reset (rst: 0) = {
                    y
                };

            (x, y)
        }
        "
}

snapshot_error! {
    array_index_errors_look_good,
    "
        entity counter(x: [int<8>; 10], idx: int<7>) -> int<8> {
            x[idx]
        }
        "
}

snapshot_error! {
    concatenation_errors_look_good,
    // FIXME: Figure out a way to include stdlib in tests
    // lifeguard spade#125
    "
    mod std{mod conv{ 
        fn concat<#N, #M, #K>(x: int<N>, y: int<M>) -> int<K> __builtin__
    }}
    entity counter(x: int<4>, y:int<3>) -> int<8> {
        x `std::conv::concat` y
    }
    "
}

snapshot_error! {
    variable_declarations_are_typechecked_correctly,
    "
        entity counter() -> int<8> {
            decl x;
            let a = x;
            let x: int<9> = 0;
            x
        }
        "
}

snapshot_error! {
    assertions_require_bools,
    "
        fn test(x: int<32>) -> bool {
            assert x;
            true
        }"
}

snapshot_error! {
    good_error_message_for_reg_with_explicit_type,
    "
        entity test(clk: clk) -> bool {
            reg(clk) (sample_i, audio_val): (int<9>, int<16>) = {
                true
            };

            true
        }
        "
}

snapshot_error! {
    good_error_message_for_reg_pattern_type_mismatch,
    "
        entity test(clk: clk) -> bool {
            reg(clk) (sample_i, audio_val): bool = {
                true
            };

            true
        }
        "
}

snapshot_error! {
    good_error_message_for_reg_pattern_type_mismatch_with_implicit_type,
    "
        entity test(clk: clk) -> bool {
            reg(clk) (sample_i, audio_val) = {
                true
            };

            true
        }
        "
}

snapshot_error! {
    good_error_message_for_let_pattern_type_mismatch_with_implicit_type,
    "
        entity test(clk: clk) -> bool {
            let (x, y) = true;

            true
        }
        "
}

snapshot_error! {
    good_error_message_for_let_pattern_type_mismatch_with_explicit_type,
    "
        entity test(clk: clk) -> bool {
            let (x, y): bool = true;

            true
        }
        "
}

snapshot_error! {
    fields_on_declared_vars_can_be_used,
    "
        struct X {a: bool}

        entity a() -> bool {
            decl x;
            let _: int<32> = x.a;
            let x = X(false);
            true
        }
    "
}

#[test]
fn fields_on_declared_variables_can_be_accessed_in_pipelines() {
    let code = "
        struct A {
            x: bool
        }
        pipeline(1) a(clk: clk) -> int<32> {
                let _ = stage(+1).x.x;
            reg;
                let x = A(false);
                0
        }
        ";

    build_items(code);
}

snapshot_error! {
    field_based_type_inference_works,
    "
        struct A {
            x: bool
        }
        fn a() -> int<32> {
            let a: int<32> = A(true).x;
            a
        }
    "
}

snapshot_error! {
    non_existing_fields_on_declared_variables_in_pipelines,
    "
        struct X {a: bool}

        pipeline(1) a(clk: clk) -> bool {
                let y = stage(+1).x.b;
            reg;
                let x = X(false);
                y
        }
        "
}

snapshot_error! {
    non_existing_fields_on_normal_variables_in_pipelines,
    "
        struct X {a: bool}

        pipeline(1) a(clk: clk) -> bool {
            reg;
                let x = X(false);
                let y = x.b;
                y
        }
        "
}

snapshot_error! {
    field_access_on_declared_non_struct_is_error,
    "
        fn a() -> int<32> {
            decl x;
            let a = x.a;
            let x = 0;
            a
        }
    "
}

#[test]
fn accessing_a_generic_fixed_field_works() {
    let code = "
        struct A<T> {
            a: T
        }

        fn x(a: A<bool>) -> bool {
            a.a
        }
        ";
    build_items(code);
}

snapshot_error! {
    backward_type_in_generic_is_an_error,
    "
    fn takes_generic<T>(x: T) -> bool {true}

    fn x(b: ~bool) -> bool {
        takes_generic(b)
    }
    "
}

snapshot_error! {
    port_type_in_generic_is_an_error,
    "
    struct X {
        x: ~bool
    }
    fn takes_generic<T>(x: T) -> bool {true}

    fn x(b: X) -> bool {
        takes_generic(b)
    }
    "
}

#[test]
fn destructuring_a_read_port_gives_real_values() {
    let code = "
    mod std {mod ports { entity read_port<T>(t: ~T) -> T __builtin__ }}
    struct A {
        x: bool,
        y: int<3>
    }

    struct HasA {
        inner: ~A
    }

    fn takes_normal(x: bool, y: int<3>) -> bool __builtin__

    entity uut(val: HasA) -> bool {
        let A$(x, y) = inst std::ports::read_port(val.inner);
        takes_normal(x, y)
    }
    ";

    build_items(code);
}

snapshot_error! {
    reading_from_port_members_is_a_type_error,
    "
    mod std {mod ports { entity read_port<T>(t: ~T) -> T __builtin__ }}

    use std::ports::read_port;

    struct A {
        x: bool,
        y: int<3>
    }

    fn takes_normal(x: bool, y: int<3>) -> bool __builtin__

    entity uut(val: ~A) -> bool {
        let x = inst read_port(val.x);
        let y = inst read_port(val.y);
        takes_normal(x, y)
    }
    "
}

snapshot_error! {
    reading_from_tuple_members_is_an_error,
    "
    mod std {mod ports { entity read_port<T>(t: ~T) -> T __builtin__ }}

    use std::ports::read_port;

    fn takes_normal(x: bool, y: int<3>) -> bool __builtin__

    entity uut(val: ~(bool, int<3>)) -> bool {
        let x = inst read_port(val#0);
        let y = inst read_port(val#1);
        takes_normal(x, y)
    }
    "
}
