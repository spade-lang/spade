use crate::{build_items, build_items_with_stdlib, code_compiles, snapshot_error, snapshot_mir};

snapshot_error! {
    impl_method_generic_args_length_does_not_match_trait_method_generic_args_length,
    "
    trait X {
        fn foo<T2>(self) -> T2;
    }
    struct A {}
    impl X for A {
        fn foo<U1, U2>(self) -> U2 {
            A()
        }
    }
    "
}

snapshot_error! {
    impl_method_generic_args_length_does_not_match_trait_method_generic_args_length_of_0,
    "
    trait X {
        fn foo(self) -> bool;
    }
    struct A {}
    impl X for A {
        fn foo<U1, U2>(self) -> bool {
            false
        }
    }
    "
}

snapshot_error! {
    impl_method_generic_args_length_of_0_does_not_match_trait_method_generic_args_length,
    "
    trait X {
        fn foo<U1, U2>(self) -> bool;
    }
    struct A {}
    impl X for A {
        fn foo(self) -> bool {
            false
        }
    }
    "
}

snapshot_error! {
    wrong_number_of_generic_arguments_triggers_error,
    "
    struct S<T> {}
    entity x<T, U>() {
        let a: S<T, U> = S();
    }
    "
}

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
    pipeline(3) main(clk: clock, x: int<8>) -> int<8> {
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
    pipeline(3) main(clk: clock, x: int<8>) -> int<8> {
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
    pipeline(3) main(clk: clock, x: int<8>) -> int<8> {
        reg;
        reg;
        reg;
            stage(+1).x
    }
    ",
    false
}

snapshot_error! {
    undefined_label_error,
    "
    pipeline(3) main(clk: clock) -> int<8> {
        reg;
            'a
            let x = 0u8;
        reg;
        reg;
            stage(b).x
    }"
}

code_compiles! {
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
    simple_self_referential_use_lookup_breaks,
    "
    use x::x;
    "
}

code_compiles! {
    use_tree_compiles,
    "
    mod a {
        mod aa {
            mod aaa {}
            mod aab {}
        }
        mod ab {
            mod aba {}
        }
    }
    use a::{
        aa::{
            aaa,
            aab,
        },
        ab::aba as alias,
    };
    "
}

snapshot_error! {
    use_tree_cannot_have_alias,
    "
    mod a {
        mod aa {}
        mod ab {}
    }
    use a::{aa, ab} as nope;
    "
}

snapshot_error! {
    extended_self_referential_use_lookup_breaks,
    "
    use x::y;
    use y::x;
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
    unused_attribute_errors_on_entity_entity,
    "
        #[uwu]
        extern entity a() -> bool;
    "
}

snapshot_error! {
    unused_attribute_errors_on_extern_pipeline,
    "
        #[uwu]
        extern pipeline(1) a(clk: clock) -> bool;
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
fn enum_variant_with_0_arguments_works() {
    let code = r#"
            enum Opt<T> {
                Never,
                Gonna,
                Give { Ephippidae: T },
                You,
                Up,
            }

            use Opt as o;
            use o::Never;

            entity main() -> Opt<int<8>> {
                Never
            }
        "#;

    build_items(code);
}

#[test]
fn none_without_parens_works() {
    let code = r#"
        entity main() -> Option<int<8>> {
            None
        }
    "#;

    build_items_with_stdlib(code);
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
fn complicated_namespace_use_works() {
    let code = r#"
        mod proj {
            mod m1 {
                use proj::m2::a; // compared to complicated_namespace_direct_fails, this adds `proj::`
            }

            mod m2 {
                use b::a;
                mod b {
                    fn a() {}
                }
            }
        }
    "#;

    build_items(code);
}

snapshot_error! {
    complicated_namespace_direct_fails,
    "
    mod proj {
        mod m1 {
            use m2::a; // compared to `complicated_namespace_use_works`, this lacks `proj::`
        }

        mod m2 {
            use b::a;
            mod b {
                fn a() {}
            }
        }
    }
    ",
    false
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

snapshot_error! {
    use_of_nothing_is_error,
    "
        use a::b;
    "
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
        x: inv &int<32>
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
    extern entity x(a: (int<32>, &int<32>)) -> bool;"
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


    extern entity x(a: &A) -> bool;
    "
}

snapshot_error! {
    mut_wires_of_ports_are_disallowed,
    "
    struct port A {}


    extern entity x(a: inv &A) -> bool;
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
    "extern fn multiple(foo: bool, bar: bool, foo: bool);"
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
        let x = false;
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
    extern_fn_methods_produce_error,
    "
        struct X {}
        impl X {
            extern fn x(self, x: bool) -> bool;
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
    single_use_multiple_definition,
    "
    struct A {}
    use A;
    "
}

snapshot_error! {
    single_use_unknown_definition,
    "
    use X;
    fn x(x: X) -> bool { false }
    "
}

snapshot_error! {
    partial_undeclared_name,
    "
    mod mod1 {
        mod mod2 {
            fn yes() -> bool { true }
        }
    }

    fn top() -> bool {
        mod1::yes()
    }
    ",
    false
}

snapshot_error! {
    partial_undeclared_name_2,
    "
    mod a {
        mod c {}
    }
    use a::b::c;
    ",
    false
}

snapshot_error! {
    partial_undeclared_name_3,
    "
    mod wrap {
        mod mod1 {
            mod mod2 {
                fn yes() -> bool { true }
            }
        }

        fn top() -> bool {
            mod1::yes()
        }
    }
    ",
    false
}

snapshot_error! {
    enum_value_creation_error_over_alias_resolves_correctly,
    "
    enum Opt<T> {
        Test1 {value: T},
        Test2,
    }

    use Opt::Test1;

    entity main() -> Opt<int<8>> {
        Test1
    }
    "
}

snapshot_error! {
    unused_broken_alias_still_errors,
    "
    use this_is_unknown::a;
    ",
    false
}

snapshot_error! {
    undeclared_errors_in_alias_not_usecase,
    "
    use aaaaaaa::thing;

    entity t(clk: clock) -> bool {
        thing()
    }
    ",
    false
}

snapshot_error! {
    expect_function_got_entity_error_works,
    "entity x() -> bool {true}

    entity test() -> bool {
        x()
    }"
}

snapshot_error! {
    expect_function_got_entity_error_works_stmt,
    "entity x() -> bool {true}

    entity test() -> bool {
        x();
        false
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
    "pipeline(-1) x(clk: clock) -> bool {
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
    ",
    false
}

snapshot_error! {
    inverting_non_port_type,
    "extern entity x(t: inv int<8>) -> int<8>;"
}

snapshot_error! {
    unused_attribute_on_parameter_is_an_error,
    "fn test(#[owo] a: bool) -> bool {true}"
}

snapshot_error! {
    registers_can_not_be_no_mangle,
    "entity x(clk: clock) -> bool {
        #[no_mangle]
        reg(clk) x = false;
        x
    }"
}

snapshot_error! {
    structs_can_not_be_no_mangle,
    "#[no_mangle]
    struct X {
    }"
}

snapshot_error! {
    no_mangle_can_only_take_all,
    "#[no_mangle(notall)]
    entity foo() {}"
}

snapshot_error! {
    no_mangle_all_compiles_with_no_ports,
    "#[no_mangle(all)]
    entity foo() {}"
}

snapshot_error! {
    no_mangle_all_compiles_with_ports,
    "#[no_mangle(all)]
    entity foo(foo: int<8>) {}"
}

snapshot_error! {
    no_mangle_all_errors_on_output_type,
    "#[no_mangle(all)]
    entity foo() -> int<8> { 0 }"
}

snapshot_error! {
    no_mangle_all_errors_on_output_type_with_valid_suggestion,
    "#[no_mangle(all)]
    entity foo(out: int<8>) -> int<8> {
        let a = out;
        let b = trunc(out + 1);
        b
    }"
}

snapshot_error! {
    no_mangle_all_error_correctly_formats_suggested_inverted_type_for_wire,
    "#[no_mangle(all)]
    entity foo() -> &int<8> {
        let (a, a_inv) = port;
        a
    }"
}

snapshot_error! {
    no_mangle_all_errors_on_output_type_with_valid_suggestion_multiline,
    "#[no_mangle(all)]
    entity foo(
        a: int<8>,
        out: int<8>,
    ) -> int<8> {
        let b = trunc(a + out);
        b
    }"
}

snapshot_error! {
    structs_can_not_be_fsm,
    "#[fsm]
    struct X {
    }"
}

snapshot_error! {
    condition_on_multiplied_stage_is_disallowed,
    "
        pipeline(3) x(clk: clock) -> bool {
            reg[false]*3;
                false
        }
    "
}

snapshot_error! {
    condition_on_multiplied_stage_is_disallowed_single_extra_stage,
    "
        pipeline(2) x(clk: clock) -> bool {
            reg[false]*2;
                false
        }
    "
}

#[test]
fn no_mangle_compiles_on_extern() {
    let code = r#"
        #[no_mangle]
        extern entity drum_v(a: int<16>, b: int<16>) -> int<32>;
    "#;

    build_items(code);
}

snapshot_error! {
    enum_variant_suggestion,
    "
        enum A {
            V1{arg1: bool, arg2: bool},
            V2
        }

        fn a() -> A {
            A::V1
        }
    "
}

#[test]
fn zero_argument_enum_variants_dont_need_args() {
    let code = "
        enum A {
            V1{arg1: bool, arg2: bool},
            V2
        }

        fn a() -> A {
            A::V2
        }
    ";
    build_items(code);
}

snapshot_error! {
    using_generic_as_type_level_integer,
    "
        fn test<T>() -> int<8> {
            T
        }
    "
}

snapshot_error! {
    using_a_type_as_a_type_level_integer,
    "
        struct T {}
        fn test() -> int<8> {
            T
        }
    "
}

#[test]
fn access_pipeline_reg_from_block() {
    let code = r#"
        pipeline(3) main(clk: clock) -> int<8> {
                let a = { stage(+1).b };
            reg;
                let b = 0;
            reg;
            reg;
                a
        }
    "#;

    build_items(code);
}

#[test]
fn access_pipeline_reg_twice() {
    let code = r#"
        pipeline(3) main(clk: clock) -> int<8> {
                let a = stage(+1).b;
                let c = stage(+2).b;
            reg;
                let b = 0;
            reg;
            reg;
                a
        }
    "#;

    build_items(code);
}

snapshot_error! {
    access_undefined_pipeline_reg,
    "
    pipeline(3) main(clk: clock) -> int<8> {
            let a = stage(+2).d;
        reg;
        reg;
            let c = 0;
        reg;
            c
    }
    "
}

snapshot_error! {
    stage_laundering,
    "
    pipeline(3) main(clk: clock) -> int<8> {
            let a = stage(+2).c;
            let b = c; // <-- This should be an error
        reg;
        reg;
            let c = 0;
        reg;
            c
    }
    "
}

#[test]
fn trait_impls_inside_modules_works() {
    let code = r#"
        struct A {}
        trait X {
            fn foo(self) -> bool;
        }

        mod M {
            impl X for A {
                fn foo(self) -> bool {
                    true
                }
            }
        }
    "#;

    build_items(code);
}

snapshot_error! {
    generic_trait_used_without_param_spec,
    "
        trait X<T> {}
        struct S {}
        impl X for S {}
    "
}

snapshot_error! {
    non_generic_trait_used_with_param_spec,
    "
        trait X {}
        struct S {}
        impl<T> X<T> for S {}
    "
}

snapshot_error! {
    generic_trait_used_with_wrong_number_of_params,
    "
        trait X<T, U> {}
        struct S {}
        impl<T> X<T> for S {}
    "
}

code_compiles! {
    impls_on_arrays_work,
    "
        impl [bool; 8] {
            fn func(self) {}
        }

        fn test() {
            [true; 8].func()
        }
    "
}

snapshot_error! {
    trait_spec_match_check_is_structural,
    "
        struct X {}

        trait T {
            fn generic<T1, T2>(self, x: (T1, T2));
        }

        impl T for X {
            fn generic<T2, T1>(self, x: (T1, T2)) {}
        }
    "
}

snapshot_error! {
    tuple_members_must_be_types,
    "
        fn test(x: (bool, 2)) {}
    "
}

snapshot_error! {
    wire_targets_must_be_types,
    "
        fn test(x: &2) {}
    "
}

snapshot_error! {
    inv_targets_must_be_types,
    "
        fn test(x: inv 2) {}
    "
}

snapshot_error! {
    lambda_variables_are_not_visible_externally,
    "
        fn test() {
            let l = fn || {
                let x = 0u8;
            };
            let y = x;
        }
    "
}

snapshot_mir! {
    lambda_captures_work,
    "
        fn test() {
            let x = 0u8;
            let l = fn|| {
                let y = x;
            }.call((,));
        }
    ",
    all
}

code_compiles! {
    lambdas_do_not_clear_the_current_unit_context,
    "
        fn test() {
            let l2 = fn|| {
            };
            let l = fn|| {
            };
        }
    "
}

snapshot_mir! {
    nested_lambdas_can_capture,
    "
        fn test() {
            let x = 0u8;
            let l2 = fn|| {
                let z = 0u8;
                let l: () = fn|| {
                    let y = (x, z);
                }.call((,));
            }.call((,));
        }
    ",
    all
}
