use crate::{build_items, build_items_with_stdlib, snapshot_error};

#[test]
fn visit_unary_operator_works_for_tilde_int() {
    let code = r#"
        entity main() -> int<8> {
            let x: int<8> = 0b01010101;
            ~x
        }
    "#;
    build_items(code);
}

#[test]
fn visit_unary_operator_works_for_tilde_uint() {
    let code = r#"
        entity main() -> uint<8> {
            let x: uint<8> = 0b01010101;
            ~x
        }
    "#;
    build_items(code);
}

#[test]
fn type_inference_works_for_arrays() {
    let code = r#"
        entity x() -> [int<3>; 3] {
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

#[test]
fn entities_without_return_type_typechecks() {
    // NOTE: instantiating an entity without a return type is still a type error,
    // see 'instantiating_entities_without_return_type_errors'.
    let code = r#"
    entity no_output(clk: clock) {}
    "#;

    build_items(code);
}

#[test]
fn entities_with_void_return_type_typechecks() {
    // NOTE: instantiating an entity without a return type is still a type error,
    // see 'instantiating_entities_without_return_type_errors'.
    let code = r#"
    entity no_output(clk: clock) -> void {}
    "#;

    build_items(code);
}

#[test]
fn entities_without_return_type_can_be_instantiated() {
    let code = r#"
    entity no_output(clk: clock) {}

    entity e(clk: clock) -> bool {
        let _ = inst no_output(clk);
        true
    }
    "#;

    build_items(code);
}

snapshot_error!(
    passing_too_many_arguments_to_turbofish_generates_proper_diagnostic,
    "entity foo<T>() -> int<8> { 15 }
    entity main() -> int<8> {
        inst foo::<bool, bool>()
    }"
);

snapshot_error!(
    expected_a_number_when_bitwise_inverting_an_enum_variant,
    "entity main() -> uint<8> {
        ~None
    }"
);

snapshot_error!(
    backward_tuple_indexing_with_type_error_errors_nicely,
    "entity name(x: &mut (bool, bool)) -> int<32> {
        x#0
    }"
);

snapshot_error!(
    useful_error_if_indexing_backward_array,
    "
    entity name(x: &mut [bool; 10]) -> int<32> {
        x[0]
    }
    "
);

snapshot_error!(
    int_as_if_argument,
    "fn a(y: int<1>) -> int<32> {
        if y {3} else {5}
    }"
);

snapshot_error! {
    type_error_on_port_set_mismatch,
    "
    // NOTE: returning bool because we don't support unit types
    entity set_port(p: &mut int<10>, v: int<9>) -> bool {
        set p = v;
        false
    }
    "
}

snapshot_error! {
    type_error_on_port_set_to_port,
    "
    // NOTE: returning bool because we don't support unit types
    entity set_port(p: &mut int<10>, v: &mut int<10>) -> bool {
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
    int_addition_produces_one_more_bit,
    "
        fn add(a: int<8>, b: int<8>) -> int<10> {
            let x = a + b;
            x
        }
    "
}

snapshot_error! {
    uint_addition_produces_one_more_bit,
    "
        fn add(a: uint<8>, b: uint<8>) -> uint<10> {
            a + b
        }
    "
}

snapshot_error! {
    counter_without_trunc_causes_type_error,
    "
        entity counter(clk: clock, rst: bool) -> int<8> {
            reg(clk) x = x + 1;
            x
        }
    "
}

snapshot_error! {
    type_error_has_replacements_applied,
    "
        entity counter(clk: clock, rst: bool) -> (int<8>, int<8>) {
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
        entity counter(x: [int<8>; 10], idx: uint<7>) -> int<8> {
            x[idx]
        }
        "
}

snapshot_error! {
    concatenation_errors_look_good,
    "
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
        entity test(clk: clock) -> bool {
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
        entity test(clk: clock) -> bool {
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
        entity test(clk: clock) -> bool {
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
        entity test(clk: clock) -> bool {
            let (x, y) = true;

            true
        }
        "
}

snapshot_error! {
    good_error_message_for_let_pattern_type_mismatch_with_explicit_type,
    "
        entity test(clk: clock) -> bool {
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
        pipeline(1) a(clk: clock) -> int<32> {
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

        pipeline(1) a(clk: clock) -> bool {
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

        pipeline(1) a(clk: clock) -> bool {
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
    entity takes_generic<T>(x: T) -> bool {true}

    entity x(b: &mut bool) -> bool {
        inst takes_generic(b)
    }
    "
}

snapshot_error! {
    port_type_in_generic_is_an_error,
    "
    struct port X {
        x: &mut bool
    }
    entity takes_generic<T>(x: T) -> bool {true}

    entity x(b: X) -> bool {
        inst takes_generic(b)
    }
    "
}

#[test]
fn destructuring_a_read_mut_wire_gives_real_values() {
    let code = "
    mod std {mod ports { entity read_mut_wire<T>(t: &mut T) -> T __builtin__ }}
    struct A {
        x: bool,
        y: int<3>
    }

    struct port HasA {
        inner: &mut A
    }

    fn takes_normal(x: bool, y: int<3>) -> bool __builtin__

    entity consumer(x: HasA) -> bool __builtin__

    entity uut(val: HasA) -> bool {
        let A$(x, y) = inst std::ports::read_mut_wire(val.inner);
        let _ = inst consumer(val);
        takes_normal(x, y)
    }
    ";

    build_items(code);
}

snapshot_error! {
    reading_from_port_members_is_a_type_error,
    "
    use std::ports::read_mut_wire;

    struct A {
        x: bool,
        y: int<3>
    }

    fn takes_normal(x: bool, y: int<3>) -> bool __builtin__

    entity uut(val: &mut A) -> bool {
        let x = inst read_mut_wire(val.x);
        let y = inst read_mut_wire(val.y);
        takes_normal(x, y)
    }
    "
}

snapshot_error! {
    reading_from_tuple_members_is_an_error,
    "
    use std::ports::read_mut_wire;

    fn takes_normal(x: bool, y: int<3>) -> bool __builtin__

    entity uut(val: &mut (bool, int<3>)) -> bool {
        let x = inst read_mut_wire(val#0);
        let y = inst read_mut_wire(val#1);
        takes_normal(x, y)
    }
    "
}

snapshot_error! {
    dereference_requires_target_type,
    "
    entity x(a: &bool) -> int<8> {
        *a
    }
    "
}

snapshot_error! {
    type_error_on_registers_are_useful,
    "
    entity test(clk: clock, rst: bool) -> bool {
        let shift_clock_initial: int<10> = 0b0000011111;
        reg(clk) shift_clock: int<10> reset(rst: shift_clock_initial) = {
            let upper: int<2> = trunc(shift_clock);
            let rest: int<8> = shift_clock >> 2;
            upper `concat` rest
        };
        true
    }"
}

snapshot_error! {
    wrong_index_size_on_memory_write_port_is_error,
    "
        use std::mem::clocked_memory;
        entity test(clk: clock, idx: uint<32>) -> int<8> {
            let mem: Memory<int<8>, 16> = inst clocked_memory(clk, [(true, idx, 0)]);
            0
        }
    "
}

snapshot_error! {
    wrong_index_size_on_memory_read_port_is_error,
    "
        use std::mem::clocked_memory;
        use std::mem::read_memory;

        entity test(clk: clock, idx: uint<32>) -> int<8> {
            let mem: Memory<int<8>, 32> = inst clocked_memory(clk, []);
            inst read_memory(mem, idx)
        }
    "
}

snapshot_error! {
    too_small_index_size_on_memory_read_port_is_error,
    "
        use std::mem::clocked_memory;
        use std::mem::read_memory;

        entity test(clk: clock, idx: uint<3>) -> int<8> {
            let mem: Memory<int<8>, 16> = inst clocked_memory(clk, [(true, idx, 0)]);
            0
        }
    "
}

#[test]
fn rom_is_describable() {
    let code = "
        use std::mem::clocked_memory_init;
        use std::mem::read_memory;

        entity test(clk: clock, idx: uint<1>) -> int<8> {
            let mem: Memory<int<8>, 2> = inst clocked_memory_init(clk, [(true, 0, 0)], [1, 2]);
            inst read_memory(mem, idx)
        }
    ";
    build_items_with_stdlib(code);
}

snapshot_error! {
    different_types_in_if,
    "
        fn test(b: int<4>) -> int<8> {
            let a = if b == 4 { 3 } else { true };
            7
        }
    "
}

snapshot_error! {
    clock_must_be_of_type_clock,
    "
        entity test(b: int<4>) -> int<8> {
            reg(b) a = 3;
            a
        }
    "
}

snapshot_error! {
    reset_must_be_of_type_bool,
    "
        entity test(clk: clock, b: int<4>) -> int<8> {
            reg(clk) a reset (b: 0) = 3;
            a
        }
    "
}

snapshot_error! {
    reset_mismatch,
    "
        entity test(clk: clock, rst: bool) -> int<8> {
            reg(clk) a reset (rst: true) = 3;
            a
        }
    "
}

snapshot_error! {
    array_type_mismatch,
    "
        fn x() -> bool  {
            let a = [0, true, 2];
            false
        }
    "
}

#[test]
fn unsigned_literals_fit() {
    let code = "fn test() -> uint<8> {
        255
    }";

    build_items(code);
}

#[test]
fn accessing_fields_of_structs_in_inverted_ports_works() {
    let code = "
        struct port Inner {
            x: &bool
        }
        struct port Outer {
            inner: Inner
        }

        entity test(p: ~Outer) -> &mut bool {
            p.inner.x
        }
    ";

    build_items(code);
}

snapshot_error! {
    wal_trace_clk_must_be_clock,
    "
        #[wal_traceable(suffix = __)]
        struct T {}
        fn test(t: T, x: bool) -> bool {
            #[wal_trace(clk=x)]
            let t = t;
            false
        }
    "
}

snapshot_error! {
    wal_trace_rst_must_be_clock,
    "
        #[wal_traceable(suffix = __)]
        struct T {}
        fn test(t: T, x: int<10>) -> bool {
            #[wal_trace(rst=x)]
            let t = t;
            false
        }
    "
}

snapshot_error! {
    pipeline_stage_valid_is_a_bool,
    "pipeline(1) x(clk: clock) -> bool {
            let a: int<8> = stage.valid;
        reg;
            true
    }"
}

snapshot_error! {
    pipeline_stage_ready_is_a_bool,
    "pipeline(1) x(clk: clock) -> bool {
            let a: int<8> = stage.ready;
        reg;
            true
    }"
}

snapshot_error! {
    pipelines_must_have_clock,
    "
    pipeline(4) test(not_a_clock: bool) -> bool {
        reg*4;
            true
    }"
}

snapshot_error! {
    register_initial_value_error,
    "
        entity t(clk: clock) -> bool {
            reg(clk) x initial(0) = true;
            true
        }
    "
}

snapshot_error! {
    unit_omitting_return_type,
    "
    fn empty(a: bool) {
        a
    }

    entity empty2(clk: clock, b: bool) {
        b
    }

    pipeline(4) empty3(clk: clock, c: bool) {
        reg*4;
            c
    }
    "
}

snapshot_error! {
    unit_omitting_return_value,
    "
    fn empty(a: bool) -> bool {
    }

    entity empty2(clk: clock, b: bool) -> bool {
    }

    pipeline(4) empty3(clk: clock, c: bool) -> bool {
        reg*4;
    }
    "
}

snapshot_error! {
    unit_return_expressionless_block,
    "
    fn f() -> bool {
        {}
    }"
}

#[test]
fn tuple_match_regression_1() {
    let code = "
        fn accumulator_mem(
            write: Option<(int<10>, int<40>)>
        ) -> bool __builtin__

        entity accumulators(
            input: (int<10>, int<10>),
        ) {
            let write = match input {
                (idx, 0) => Some((idx, 0)),
                (0, idx) => Some((idx, 0)),
                _ => None()
            };

            let _ = accumulator_mem(write);
        }
    ";
    build_items_with_stdlib(code);
}

#[test]
fn second_integer_resolves_correctly() {
    let code = "
        struct AccMemOut {
            // Data from port 1
            d1: int<40>,
            // Data from port 2
            d2: int<40>
        }

        fn accumulator_mem(
            write: Option<(int<10>, int<40>)>
        ) -> AccMemOut __builtin__

        pipeline(0) accumulators(
            clk: clock,
            rst: bool,
            // Clear the accumulator at the provided index. Takes precedence over
            // new_value
            input: (int<10>, int<10>),
        ) {
                let write = match input {
                    (idx, 0) => Some((idx, 0)),
                    (0, idx) => Some((idx, 0)),
                    (_, _) => None()
                };

                let acc_mem_out = accumulator_mem(write);
        }
    ";
    build_items_with_stdlib(code);
}

#[test]
fn impl_trait_works() {
    let code = "
        trait Trait {}

        fn test<T: Trait>(x: T) {}
    ";

    build_items(code);
}

snapshot_error! {
    impl_of_missing_trait_is_error,
    "
        fn test<T: Trait>(x: T) {}
    "
}

snapshot_error! {
    argument_type_mismatch_positional,
    "
    entity e(clk: clock, a: bool) -> bool {
        a
    }

    entity main(clk: clock) -> bool {
        let a: int<3> = 0;
        inst e(clk, a)
    }
    "
}

snapshot_error! {
    impl_of_non_trait_is_error,
    "
        struct A {}
        fn test<T: A>(x: T) {}
    "
}

snapshot_error! {
    argument_type_mismatch_named,
    "
    entity e(clk: clock, a: bool) -> bool {
        a
    }

    entity main(clk: clock) -> bool {
        let b: int<3> = 0;
        inst e$(clk, a: b)
    }
    "
}

snapshot_error! {
    argument_type_mismatch_shortnamed,
    "
    entity e(clk: clock, a: bool) -> bool {
        a
    }

    entity main(clk: clock) -> bool {
        let a: int<3> = 0;
        inst e$(clk, a)
    }
    "
}

snapshot_error! {
    type_pattern_argument_type_mismatch_positional,
    "
    struct X {
        b: bool,
    }

    entity main() -> bool {
        let x = X$(b: true);
        match x {
            X(0) => true,
            _ => false,
        }
    }
    "
}

snapshot_error! {
    type_pattern_argument_type_mismatch_positional2,
    "
    struct X {
        b: bool,
    }

    entity main(x: X) -> bool {
        match x {
            X(0) => true,
            _ => false,
        }
    }
    "
}

snapshot_error! {
    type_pattern_argument_type_mismatch_positional3,
    "
    struct A {}
    struct B {}

    struct X {
        b: B,
    }

    entity main(x: X) -> bool {
        match x {
            X(A()) => true,
            _ => false,
        }
    }
    "
}
snapshot_error! {
    type_pattern_argument_type_mismatch_named,
    "
    struct X {
        b: bool,
    }

    entity main() -> bool {
        let x = X$(b: true);
        match x {
            X$(b: 0) => true,
            _ => false,
        }
    }
    "
}

snapshot_error! {
    type_pattern_argument_type_mismatch_shortnamed,
    "
    struct X {
        b: bool,
    }

    entity main() -> bool {
        decl b;
        let x: int<8> = b;
        let X$(b) = X(true);
    }
    "
}

snapshot_error! {
    range_indexing_non_array_is_error,
    "
        fn test(x: int<8>) -> [int<8>; 2] {
            x[0:3]
        }
    "
}

snapshot_error! {
    range_index_too_large_is_error,
    "
        fn test(x: [int<8>; 6]) -> [int<8>; 2] {
            x[0:3]
        }
    "
}

snapshot_error! {
    range_index_too_small_is_error,
    "
        fn test(x: [int<8>; 6]) -> [int<8>; 2] {
            x[0:1]
        }
    "
}

snapshot_error! {
    inverse_order_range_index_is_error,
    "
        fn test(x: [int<8>; 6]) -> [int<8>; 2] {
            x[2:0]
        }
    "
}

snapshot_error! {
    end_out_of_range_range_index_is_error,
    "
        fn test(x: [int<8>; 6]) -> [int<8>; 2] {
            x[5:7]
        }
    "
}

snapshot_error! {
    start_out_of_range_range_index_is_error,
    "
        fn test(x: [int<8>; 6]) -> [int<8>; 2] {
            x[6:8]
        }
    "
}

#[test]
fn end_at_array_bound_is_allowed() {
    let code = "
    fn test(x: [int<8>; 6]) -> [int<8>; 2] {
        x[4:6]
    }";

    build_items(code);
}

snapshot_error! {
    zero_size_range_index_is_error,
    "
        fn test(x: [int<8>; 6]) -> [int<8>; 1] {
            x[7:7]
        }
    "
}

snapshot_error! {
    negative_range_index_is_error,
    "
        fn test(x: [int<8>; 6]) -> [int<8>; 1] {
            x[-1:5]
        }
    "
}

snapshot_error! {
    negative_second_range_index_is_error,
    "
        fn test(x: [int<8>; 6]) -> [int<8>; 1] {
            x[1:-5]
        }
    "
}

#[test]
fn unsigned_ints_are_addable() {
    let code = "
        fn test(x: uint<8>, y: uint<8>) -> uint<9> {
            x + y
        }";

    build_items(code);
}

#[test]
fn unsigned_ints_are_multiplyable() {
    let code = "
        fn test(x: uint<8>, y: uint<8>) -> uint<16> {
            x * y
        }";

    build_items(code);
}

#[test]
fn unsigned_ints_are_comparable() {
    let code = "
        fn test(x: uint<8>, y: uint<8>) -> bool {
            x < y && x > y && x <= y && x >= y
        }";

    build_items(code);
}

snapshot_error! {
    int_add_uint_is_disallowed,
    "
        fn test(x: uint<8>, y: int<8>) -> uint<9> {
            x + y
        }
    "
}

snapshot_error! {
    int_add_produces_int,
    "
        fn test(x: int<8>, y: int<8>) -> uint<9> {
            x + y
        }
    "
}

snapshot_error! {
    uint_addition_produces_correct_bit_length,
    "
        fn test(x: uint<8>, y: uint<8>) -> uint<10> {
            x + y
        }
    "
}

snapshot_error! {
    structs_are_not_addable,
    "
        struct A {}
        fn test(x: A, y: A) -> A {
            x + y
        }
    "
}

#[test]
fn literals_can_be_unsigned_ints() {
    let code = "
        fn test() -> uint<8> {
            10
        }
    ";
    build_items(code);
}

#[test]
fn unsigned_literal_fit_upper_range() {
    let code = "
        fn test() -> uint<8> {
            200
        }
    ";
    build_items(code);
}

snapshot_error! {
    unsigned_literals_cannot_be_negative,
    "
        fn test() -> uint<8> {
            -1
        }
    "
}

#[test]
fn chained_int_operations_infer_type() {
    let code = "
            fn test(a: int<16>) -> int<16> {
                // let x = a << a;
                let y = a + a;
                // let res = y + y;
                a
            }
    ";
    build_items(code);
}

#[test]
fn uint_concat_works() {
    let code = "
        fn test(x: uint<16>, y: uint<8>) -> uint<24> {
            x `concat` y
        }
    ";
    build_items_with_stdlib(code);
}

snapshot_error! {uint_concat_does_not_produce_int,
    "
        fn test(x: uint<16>, y: uint<8>) -> int<24> {
            x `concat` y
        }
    "
}

snapshot_error! {
    the_source_of_int_uint_size_mismatches_is_clear,
    "
    fn test(x: uint<16>, y: uint<8>) -> int<24> {
        let z: int<24> = x + y;
        z
    }
    "
}

snapshot_error! {
    the_source_of_int_uint_mismatches_is_clear,
    "
    fn test(x: uint<8>, y: uint<8>) -> int<9> {
        let z: int<9> = x + y;
        z
    }
    "
}

snapshot_error! {
    trunc_requires_number,
    "
        struct A {}

        fn test(a: A) -> int<8> {
            trunc(a)
        }
    "
}

snapshot_error! {
    concat_requires_number,
    "
        struct A {}

        fn test(a: A) -> int<8> {
            a `concat` a
        }
    "
}

snapshot_error! {
    wrong_type_signature_on_let_binding_does_not_double_report,
    "
        fn test() {
            let x: bool = 0;
        }
    "
}

snapshot_error! {
    turbofish_overrides_type,
    "
        fn ret_int<#N>() -> int<N> {
            0
        }

        fn test() {
            let x: int<8> = ret_int::<10>();
        }
    "
}

snapshot_error! {
    turbofish_on_non_generic_error,
    "
        fn ret_int() -> int<8> {
            0
        }

        fn test() {
            let x: int<8> = ret_int::<10>();
        }
    "
}

snapshot_error! {
    turbofish_param_number_mismatch,
    "
        fn ret_int<#A, #B>() -> int<8> {
            0
        }

        fn test() {
            let x: int<8> = ret_int::<10>();
        }
    "
}

snapshot_error! {
    type_params_are_accessible_in_units,
    "
        fn produce_something<T>() -> T __builtin__

        fn test<T>() {

            let a: T = produce_something::<bool>();
        }

        fn main() {
            test::<int<9>>()
        }
    "
}

snapshot_error! {
    type_params_are_accessible_in_units2,
    "
        mod mem {
            fn produce_something<T>() -> T __builtin__

            fn test<#T>() {
                let a: int<T> = produce_something::<int<8>>();
            }

            fn main() {
                test::<int<9>>()
            }
        }
    "
}

snapshot_error! {
    out_of_bounds_type_level_integer_is_error,
    "
        fn return_t<#T>() -> int<8> {
            T
        }

        fn test() -> int<8> {
            return_t::<1024>()
        }
    "
}

#[test]
fn in_bounds_type_level_integer_is_ok() {
    build_items(
        "
        fn return_t<#T>() -> int<8> {
            T
        }

        fn test() -> int<8> {
            return_t::<0>()
        }
    ",
    );
}

snapshot_error! {
    type_parameter_propagation_regression,
    "
        use std::ports::new_mut_wire;
        use std::ports::read_mut_wire;

        struct ReadPort_<W> { }

        struct port FifoRead<#W> { }

        entity fifo_read_side<#W>(
            write_ptr_w: uint<W>,
            ram_read: ReadPort_<W>,
            read_ptr_wire: &mut uint<W>,
        ) -> FifoRead<W> {
            FifoRead$()
        }

        entity fifo<#W>(
            ram_read: ReadPort_<W>
        ) -> FifoRead<W> {
            let read_ptr_wire = inst new_mut_wire();

            let read_ptr_w = inst read_mut_wire(read_ptr_wire);

            let write_ptr_w  = 0;

            let full_w = 0 == read_ptr_w;


            inst fifo_read_side$(
                    write_ptr_w,
                    ram_read,
                    read_ptr_wire,
                )
        }

        entity fifo_test_harness(
            ram_read: ReadPort_<4>
        ) {
            let _ = inst fifo::<4>$(ram_read);
        }
    "
}
