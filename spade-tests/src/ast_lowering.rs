use crate::{build_items, snapshot_error};

snapshot_error! {
    duplicate_definition_of_decl_triggers_errors,
    "
    entity X() -> int<8> {
        decl x;
        let x = 0;
        let x = 1;
        x
    }
    "
}

snapshot_error! {
    declaration_without_definition_triggers_error,
    "
    entity X() -> int<8> {
        decl x;
        x
    }
    "
}

snapshot_error! {
    declaration_after_let_requires_new_definition,
    "
    entity X() -> int<8> {
        let x: int<8> = 0;
        decl x;
        x
    }
    "
}

snapshot_error! {
    negative_stage_index,
    "
    pipeline(3) main(x: int<8>) -> int<8> {
            let a = stage(-1).x;
        reg;
        reg;
        reg;
            0
    }
    "
}

snapshot_error! {
    negative_stage_index_later,
    "
    pipeline(3) main(x: int<8>) -> int<8> {
        reg;
        reg;
            let a = stage(-5).x;
        reg;
            0
    }
    "
}

snapshot_error! {
    stage_index_overflow,
    "
    pipeline(3) main(x: int<8>) -> int<8> {
        reg;
        reg;
        reg;
            stage(+1).x
    }
    "
}

snapshot_error! {
    duplicate_label_error,
    "
    pipeline(3) main(clk: clock) -> int<8> {
        reg;
            'a
        reg;
            'a
        reg;
            0
    }"
}

snapshot_error! {
    undefined_label_error,
    "
    pipeline(3) main(clk: clock) -> int<8> {
        reg;
            'a
            let x = 0;
        reg;
        reg;
            stage(b).x
    }"
}

snapshot_error! {
    multiple_labels_for_same_stage,
    "
    pipeline(3) main(clk: clock) -> int<8> {
        reg;
            'a
            'b
        reg;
        reg;
            0
    }"
}

snapshot_error! {
    single_identifier_enum_lookups_pass_compiler,
    "
    enum X {
        A{x: int<5>},
        B
    }

    use X::A;
    use X::B;

    fn test(x: X) -> X {
        match x {
            A(_) => A(4),
            // If this test works, B, being in scope should not be a variable but remain
            // referring to X::B. In the incorrect behaviour, the single identifier path B
            // binds to X and B() is calling a variable as a function
            B => B(),
        }
    }
    "
}

snapshot_error! {
    match_expressions_open_new_scopes,
    "
    fn test(x: int<32>) -> int<32> {
        let _: int<32> = match x {
            a => 0
        };

        a
    }
    "
}

snapshot_error! {
    unused_attribute_errors_on_builtin_entity,
    "
        #[uwu]
        entity a() -> bool __builtin__
    "
}

snapshot_error! {
    unused_attribute_errors_on_builtin_pipeline,
    "
        #[uwu]
        pipeline(1) a(clk: clock) -> bool __builtin__
    "
}

snapshot_error! {
    unused_attribute_errors_on_entity,
    "
        #[uwu]
        entity a() -> bool {true}
    "
}

snapshot_error! {
    unused_attribute_errors_on_pipeline,
    "
        #[uwu]
        pipeline(1) a(clk: clock) -> bool {reg; true}
    "
}

#[test]
fn nested_use_compiles_correctly() {
    let code = r#"
        mod A {
            struct X {x: bool}
        }

        mod B {
            use lib::A::X;

            fn a() -> X {
                X(true)
            }
        }
    "#;

    build_items(code);
}

#[test]
fn type_inference_works_for_declared_variables() {
    let code = r#"
    enum Option<T> {
        Some{val: T},
        None
    }
    fn test() -> bool {
        let x: Option<(int<8>, int<8>)> = Option::Some((0, 0));

        let _ = match x {
            Option::Some(x) => true,
            _ => false
        };

        match x {
            Option::Some((a, b)) => true,
            _ => false
        }
    }
    "#;

    build_items(code);
}

#[test]
fn use_of_namespace_works() {
    let code = r#"
        mod a {
            mod b {
                struct X {x: bool}
            }
        }

        use a::b;

        fn x() -> b::X {
            b::X(true)
        }
    "#;

    build_items(code);
}

#[test]
fn global_use_statements_work_across_modules() {
    let code = r#"
        mod std {
            enum Option<T> {
                Some{val: T},
                None
            }
        }


        mod submod {
            use std::Option;

            fn x() -> Option<bool> {
                Option::None()
            }
        }
        "#;

    build_items(code);
}

#[test]
fn use_statements_are_visible_before_appearing_in_source_code() {
    let code = r#"
        mod std {
            mod option {
                enum Option<T> {
                    Some{val: T},
                    None
                }
            }
        }

        mod mcp3002 {
            mod adc {
                struct SpiOut {
                    received_data: Option<int<16>>
                }
            }
        }

        use std::option::Option;
        "#;

    build_items(code);
}

snapshot_error! {
    duplicate_item_names,
    "
        fn a() -> bool {
            true
        }
        fn a() -> bool {
            false
        }
    "
}

snapshot_error! {
    duplicate_item_names2,
    "
        fn a() -> bool {
            true
        }
        pipeline(0) a(clk: clock) -> bool {
            false
        }
    "
}

snapshot_error! {
    duplicate_item_names3,
    "
        fn a() -> bool {
            true
        }
        struct a{}
    "
}

snapshot_error! {
    duplicate_item_names4,
    "
        fn a() -> bool {
            true
        }
        enum a{}
    "
}

snapshot_error! {
    duplicate_item_names6,
    "
        fn a() -> bool {
            true
        }
        mod x {fn b() -> bool {true}}
        use x::b as a;
    "
}

snapshot_error! {
    duplicate_item_names7,
    "
        fn b() -> bool {
            true
        }
        mod x {fn b() -> bool {true}}
        use x::b;
    "
}

snapshot_error! {
    inst_function_used,
    "
        // See https://gitlab.com/spade-lang/spade/-/issues/160
        mod a {
            fn foo() -> bool { true }
        }

        use a::foo;

        entity test() -> bool {
            inst foo()
        }
    "
}

snapshot_error! {
    good_error_message_on_empty_match_statement,
    "
        fn match_bool(x: bool) -> bool {
            match x {

            }
        }"
}

snapshot_error! {
    names_do_not_leak_across_match_branches,
    "
        fn test() -> int<10> {
            match Some(true) {
                Some(count) => 0,
                None => count
            }
        }
        "
}

snapshot_error! {
    ports_can_not_contain_values,
    "struct port A {
        x: int<32>,
    }"
}

snapshot_error! {
    non_ports_can_not_contain_ports,
    "struct A {
        x: &int<32>
    }"
}

snapshot_error! {
    non_ports_can_not_contain_tuple_ports,
    "struct A {
        x: (&int<32>, &bool)
    }"
}

snapshot_error! {
    non_ports_can_not_contain_mut_wires,
    "struct A {
        x: &mut int<32>
    }"
}

snapshot_error! {
    non_ports_can_not_contain_transitive_ports,
    "
    struct port P {
        x: &int<32>
    }
    struct A {
        x: P
    }"
}

snapshot_error! {
    tuple_type_specs_can_not_contain_ports_and_values,
    "
    entity x(a: (int<32>, &int<32>)) -> bool __builtin__"
}

snapshot_error! {
    generics_in_ports_can_not_be_bare,
    "
    struct port P<T> {
        x: T
    }
    "
}

snapshot_error! {
    enums_can_not_have_ports,
    "enum X {
        A{x: &int<32>}
    }"
}

snapshot_error! {
    enums_can_not_have_transitive_ports,
    "
    struct port A {}
    enum X {
        A{x: A}
    }"
}

snapshot_error! {
    wires_of_ports_are_disallowed,
    "
    struct port A {}


    entity x(a: &A) -> bool __builtin__
    "
}

snapshot_error! {
    mut_wires_of_ports_are_disallowed,
    "
    struct port A {}


    entity x(a: &mut A) -> bool __builtin__
    "
}

snapshot_error! {
    ports_can_not_impl_functions,
    "
    struct port A {}

    impl A {
        fn test(self) -> bool {true}
    }
    "
}

snapshot_error! {
    no_mangle_generics,
    "
    #[no_mangle]
    fn mangling_time<#N>() -> int<N> __builtin__
    "
}

snapshot_error! {
    duplicate_enum_variants,
    "
    enum E {
        A,
        B,
        A,
    }
    "
}

snapshot_error! {
    generics_given_for_generic_type,
    "
    enum Test<T, U> {
        B { value: T<U> },
    }
    "
}

snapshot_error! {
    multiple_arguments_same_name,
    "fn multiple(foo: bool, bar: bool, foo: bool) __builtin__"
}

snapshot_error! {
    pipeline_depth_mismatch,
    "
    pipeline(3) p(clk: clock, b: bool) -> bool {
        reg;
        reg;
        reg;
            b
    }

    entity top(clk: clock) -> bool {
        inst(2) p(clk, true)
    }
    "
}

snapshot_error! {
    duplicate_declarations,
    "
    fn main() -> bool {
        decl x, x;
        true
    }
    "
}

snapshot_error! {
    undefined_identifiers,
    "
    fn main() -> bool {
        let a = test;
        true
    }
    "
}

// NOTE: This test should be removed once/if we introduce higher order functions
snapshot_error! {
    functions_are_not_returnable_values,
    "
        fn f() -> bool { true }
        fn main() -> bool {
            let x = f;
            true
        }
    "
}

snapshot_error! {
    types_are_not_returnable_values,
    "
        struct test {}
        fn main() -> bool {
            let x = test;
            true
        }
    "
}

snapshot_error! {
    incorrect_stage_count,
    "
        pipeline(3) pipe(clk: clock) -> bool {
            reg;
            reg;
                true
        }
    "
}

snapshot_error! {
    incorrect_stage_count_single,
    "
        pipeline(1) pipe(clk: clock) -> bool {
                true
        }
    "
}

snapshot_error! {
    incorrect_stage_count_only_one,
    "
        pipeline(2) pipe(clk: clock) -> bool {
            reg;
                true
        }
    "
}

snapshot_error! {
    pipeline_without_arguments,
    "
        pipeline(1) pipe() -> bool {
            reg;
                true
        }
    "
}

snapshot_error! {
    pattern_list_length_mismatch_struct,
    "
        struct X {
            a: bool,
            B: bool
        }

        fn main(x: X) -> X {
            let X(a, b, c) = x;
            x
        }

    "
}

snapshot_error! {
    pattern_list_length_mismatch_enum_variant,
    "
    enum X {
        A { one: bool, two: bool }
    }

    fn main(x: X) -> X {
        match x {
            X::A(one, two, three) => x
        }
    }
    "
}

snapshot_error! {
    self_in_free_standing_function,
    "fn a(self) -> bool {true}"
}

snapshot_error! {
    builtin_fn_methods_produce_error,
    "
        struct X {}
        impl X {
            fn x(self, x: bool) -> bool __builtin__
        }
    "
}

snapshot_error! {
    builtin_pipeline_methods_produce_error,
    "
        struct X {}
        impl X {
            // NOTE: This error should change once
            // pipelines as methods are added
            pipeline(1) x(self, x: bool) -> bool __builtin__
        }
    "
}

snapshot_error! {
    named_struct_patterns_errors_if_missing_bindings,
    "
    struct A {x: bool}

    fn test(a: A) -> bool {
        let A$() = a;
        true
    }
    "
}

snapshot_error! {
    named_struct_patterns_errors_if_binding_to_undefined_name,
    "
    struct A {x: bool}

    fn test(a: A) -> bool {
        let A$(y) = a;
        true
    }
    "
}

snapshot_error! {
    named_struct_patterns_errors_if_multiple_bindings_to_same_name,
    "
    struct A {x: bool}

    fn test(a: A) -> bool {
        let A$(x, x) = a;
        true
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

snapshot_error! {
    comptime_pipeline_depth_works,
    r#"
        $config X = 1

        pipeline($if X == 1 {3} $else {2}) test(clk: clock) -> bool {
            reg*2;
                true
        }
    "#
}

snapshot_error! {
    comptime_pipeline_depth_missing_depth_gives_decent_error,
    r#"
        $config X = 0

        pipeline($if X == 1 {3}) test(clk: clock) -> bool {
            reg*2;
                true
        }
    "#
}

snapshot_error! {
    comptime_pipeline_inst_depth_works,
    r#"
        $config X = 1

        pipeline(2) test(clk: clock) -> bool {
            reg*2;
                true
        }

        entity main(clk: clock) -> bool {
            inst($if X == 1 {3} $else {2}) test(clk)
        }
    "#
}

snapshot_error! {
    comptime_pipeline_inst_depth_missing_depth_gives_decent_error,
    r#"
        $config X = 0

        pipeline(2) test(clk: clock) -> bool {
            reg*2;
                true
        }

        entity main(clk: clock) -> bool {
            inst($if X == 1 {3}) test(clk)
        }
    "#
}

snapshot_error! {
    good_error_message_on_empty_comptime_expression,
    "
        $config X = 0
        fn a() -> bool {
            let _ = $if X == 1 {true};
            true
        }
    "
}

snapshot_error! {
    enum_variant_pattern_without_arguments_one,
    "
        enum E {
            Variant { b: bool },
        }

        fn f(e: E) -> bool {
            let E::Variant = e;
            false
        }
    "
}

snapshot_error! {
    enum_variant_pattern_without_arguments_three,
    "
        enum E {
            Variant { b1: bool, b2: bool, b3: bool },
        }

        fn f(e: E) -> bool {
            let E::Variant = e;
            false
        }
    "
}

snapshot_error! {
    negative_pipeline_depth_is_disallowed,
    "pipeline(-1) x() -> bool {
        true
    }"
}

snapshot_error! {
    negative_pipeline_inst_is_disallowed,
    "
    pipeline(0) y(clk: clock) -> bool {
        true
    }
    pipeline(0) x(clk: clock) -> bool {
        inst(-1) y(clk)
    }"
}

snapshot_error! {
    negative_reg_counts_are_disallowed,
    "
        pipeline(0) x(clk: clock) -> bool {
            reg*-10;
                true
        }
    "
}

snapshot_error! {
    inverting_non_port_type,
    "entity x(t: ~int<8>) -> int<8> __builtin__"
}

snapshot_error! {
    unused_attribute_on_parameter_is_an_error,
    "fn test(#[owo] a: bool) -> bool {true}"
}

snapshot_error! {
    no_mangle_on_struct_fields_is_disallowed,
    "struct T {
        #[no_mangle] x: bool,
    }"
}

snapshot_error! {
    no_mangle_on_enum_members_is_disallowed,
    "enum T {
        A{#[no_mangle] x: bool}
    }"
}
