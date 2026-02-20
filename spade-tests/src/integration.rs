use crate::{build_items, code_compiles, snapshot_error, snapshot_mir};

snapshot_error!(
    trait_self_wrong_impl_return_type,
    r#"
        trait X {
            fn fun(self) -> Self;
        }

        struct A {}
        struct B {}

        impl X for A {
            fn fun(self) -> B {
                self
            }
        }
    "#
);

#[test]
fn trait_self_return_type_works() {
    let code = r#"
        trait X {
            fn fun(self) -> Self;
        }

        struct A {}

        impl X for A {
            fn fun(self) -> Self {
                self
            }
        }

        entity main() -> A {
            let a = A();
            a.fun()
        }
    "#;

    build_items(code);
}

#[test]
fn namespacing_works() {
    let code = r#"
        mod X {
            pub entity x() -> int<2> {
                1
            }
        }

        entity top() -> int<2> {
            inst X::x()
        }
    "#;

    build_items(code);
}

snapshot_error!(
    namespacing_adds_to_the_correct_namespace,
    r#"
        mod X {
            entity x() -> int<2> {
                1
            }
        }

        entity top() -> int<2> {
            x()
        }
    "#
);

#[test]
fn use_statements_work() {
    let code = r#"
        mod X {
            pub entity x() -> int<2> {
                1
            }
        }

        use X::x;

        entity top() -> int<2> {
            inst x()
        }
        "#;

    build_items(code);
}

#[test]
fn renaming_use_statements_work() {
    let code = r#"
        mod X {
            pub entity x() -> int<2> {
                1
            }
        }

        use X::x as a;

        entity top() -> int<2> {
            inst a()
        }
        "#;

    build_items(code);
}

/// NOTE This test fails currently
#[test]
fn recursive_use_statements_work() {
    let code = r#"
        mod X {
            pub mod Y {
                pub entity x() -> int<2> {
                    1
                }
            }
            pub use Y::x;
        }

        use X::x as a;

        entity top() -> int<2> {
            inst a()
        }
    "#;

    build_items(code);
}

#[test]
fn using_names_in_namespaces_works() {
    let code = r#"
        mod X {
            enum A {X{a: bool}}

            entity x() -> A {
                A::X(true)
            }
        }
        "#;

    build_items(code);
}

#[test]
fn using_names_of_types_in_namespaces_works() {
    let code = r#"
        mod X {
            struct A {}
            struct B{a: A}
        }
        "#;

    build_items(code);
}

#[test]
fn field_access_works_on_flipped_ports() {
    let code = r#"
        struct port P {p1: &bool, p2: inv &bool}
        entity t(p: inv P) -> bool {
            set p.p1 = &true;
            *p.p2
        }
    "#;
    build_items(code);
}

// NOTE: this is an awful error message at the moment, but it is strange code
// and fixing it would take quite a bit of effort, so we'll leave it be and
// create an issue for it
snapshot_error! {
    pipeline_shadowing_does_not_fail_silently,
    "
    pipeline(2) main(clk: clock, x: int<8>) -> int<8> {
            let x: int<8> = 0;
        reg;
            let x: int<8> = 1;
        reg;
            stage(-2).x
    }
    "
}

// NOTE: When the compiler runs in standalone mode, items added by the user
// are added to the global namespace, which means that items clash with built-in items.
snapshot_error! {
    overwriting_stdlib_gives_useful_error,
    "enum Option<T> {}"
}

#[test]
fn wildcard_type_specs_work() {
    let code = "
        fn test() {
            let x: uint<_> = 8u8;
        }
    ";
    build_items(code);
}

#[test]
fn wildcard_in_turbofish_works() {
    let code = "
        fn generic<A>(a: A) -> A {a}
        fn test() {
            let _ = generic::<_>(true);
        }
    ";
    build_items(code);
}

snapshot_error! {
    const_generic_in_turbofish_works,
    "
        fn sized_zero<#uint Size>() -> uint<Size> {
            0
        }

        fn test() {
            let x: uint<8> = sized_zero::<{1 + 2}>();
        }
    "
}

snapshot_error! {
    const_generic_in_binding_spec_works,
    "
        fn sized_zero<#uint Size>() -> uint<Size> {
            0
        }

        fn test() {
            let x: uint<{1 + 2}> = sized_zero::<8>();
        }
    "
}

snapshot_error! {
    const_generics_cannot_access_runtime_values,
    "
        fn test() {
            let x = 5;
            let y: uint<{x+5}> = 0;
        }
    "
}

code_compiles! {
    type_level_if_works,
    "
    fn inner<#uint N>() -> uint<8> {
        gen if N == 0 {
            0
        } else {
            1
        }
    }

    fn test() -> uint<8> {
        inner::<0>()
    }
    "
}

code_compiles! {
    type_level_if_works_in_methods,
    "
    struct Methodee {}
    impl Methodee {
        fn inner<#uint N>(self) -> uint<8> {
            gen if N == 1 {
                0
            } else {
                1
            }
        }
    }

    fn test() -> uint<8> {
        Methodee().inner::<0>()
    }
    "
}

code_compiles! {
    type_level_if_works_in_methods_on_generic_types,
    "
    struct Methodee<#uint M> {}
    impl<#uint M> Methodee<M> {
        fn inner<#uint N>(self) -> uint<8> {
            gen if N == 1 {
                gen if M == 2 {
                    2
                } else {
                    1
                }
            } else {
                0
            }
        }
    }

    fn test() -> uint<8> {
        Methodee::<1>().inner::<0>()
    }
    "
}

code_compiles! {
    chained_type_level_ifs_work,
    "
    fn inner<#uint N>() -> uint<8> {
        gen if N == 0 {
            0
        } else if N == 1 {
            1
        } else {
            2
        }
    }

    fn test() -> uint<8> {
        inner::<0>()
    }
    "
}

code_compiles! {
    nested_type_level_ifs_work,
    "
    fn inner<#uint N>() -> uint<8> {
        gen if N == 0 {
            gen if N == 1 {
                1
            } else {
                0
            }
        } else {
            2
        }
    }

    fn test() -> uint<8> {
        inner::<1>()
    }
    "
}

code_compiles! {
    type_level_if_bool_works,
    "
        fn test() {
            gen if 0 == 0 {
            } else {}
        }
    "
}

snapshot_error! {
    nested_type_level_is_type_level_if,
    "
        fn test(x: bool) {
            gen if 0 == 0 {
            } else if x {}
            else {}
        }
    "
}

snapshot_error! {
    tlif_pipeline_works,
    "
        pipeline(3) test(clk: clock) {
            gen if 0 == 0 {
                reg*3;
            } else {
                reg*4;
            }
        }
    ",
    false
}

code_compiles! {
    simple_lambda_compiles,
    "
        fn test() -> bool {
            fn |a, b| {a}.call((true, false))
        }
    "
}

snapshot_mir! {
    lambda_capture_generics_are_correct,
    "
        fn generic<#uint N>() -> uint<8> {
            fn || {
                N
            }.call(())
        }

        fn test() -> uint<8> {
            generic::<10>()
        }
    ", all
}

snapshot_mir! {
    multiple_lambda_capture_generics_are_correct,
    "
        fn generic<#uint N>() -> uint<8> {
            fn || {
                N
            }.call(())
        }

        fn test() {
            let a = generic::<10>();
            let b = generic::<20>();
        }
    ", all
}

snapshot_mir! {
    lambdas_capture_impl_params,
    "
        struct S<#uint N> {}
        impl <#uint N> S<N> {
            fn test(self) {
                let l = fn || {
                    let x: uint<8> = N;
                }.call(());
            }
        }

        fn test() {
            S::<5>().test()
        }
    ", all
}

code_compiles! {
    wires_are_allowed_in_fn_args,
    "
        fn a(x: &bool) {}
    "
}

code_compiles! {
    inv_wires_are_allowed_in_fn_args,
    "
        fn a(x: inv &bool) {
            set x = &false;
        }
    "
}

code_compiles! {
    wires_are_allowed_in_fn_output,
    "
        fn a() -> &bool {
            &true
        }
    "
}

code_compiles! {
    inv_wires_are_allowed_in_fn_output,
    "
        fn a() -> inv &bool {
            port#0
        }
    "
}

code_compiles! {
    paren_exprs_work_in_const_context,
    "
        fn test() -> [uint<8>; 0] {
            [0u8][(0)..(0)]
        }
    "
}

code_compiles! {
    pipeline_methods_are_allowed,
    "
        struct X {}

        impl X {
            pipeline(3) a(self, clk: clock) {
                reg * 3;
            }
        }

        entity test(clk: clock) {
            X().inst(3) a(clk)
        }
    "
}

snapshot_mir! {
    pipeline_method_calls_pass_parameters_correctly,
    "
        struct X {x: uint<8>}

        impl X {
            pipeline(3) a(self, clk: clock, val: uint<16>) {
                reg * 3;
            }
        }

        entity test(clk: clock) {
            X(2).inst(3) a(clk, 3)
        }
    ",
    all
}

code_compiles! {
    clocks_are_usable_inside_lambda_clocked_things,
    "
        entity test(clk: clock) {
            let _ = pipeline(1) |clk| {
                clk
            };
        }
    "
}

code_compiles! {
    lambda_pipelines_can_be_defined,
    "
        entity test() {
            let _ = pipeline(1) |clk| {
                reg;
            };
        }
    "
}

code_compiles! {
    lambda_pipelines_can_be_used,
    "
        entity test(clk: clock) -> uint<8> {
            let pl = pipeline(1) |clk, x| {
                reg;
                x
            };

            pl.inst(1) call(clk, (1u8,))
        }
    "
}

code_compiles! {
    zero_parameter_lambda_function_works,
    "
        entity test() {
            let _ = fn || {};
        }
    "
}

snapshot_error! {
    lambda_pipelines_need_correctly_named_clocks,
    "
        entity test() {
            pipeline(1) |not_clk| {
                reg;
            };
        }
    "
}

snapshot_error! {
    lambda_entities_need_correctly_named_clocks,
    "
        entity test() {
            entity |not_clk| {};
        }
    "
}

snapshot_error! {
    lambda_entities_need_clock,
    "
        entity test() {
            entity || {};
        }
    "
}

snapshot_error! {
    lambda_pipelines_need_clock,
    "
        entity test() {
            pipeline(1) || {
                reg;
            };
        }
    "
}

code_compiles! {
    pipeline_inst_supports_wildcard,
    "
        pipeline(1) pl(clk: clock) {
            reg;
        }

        entity test(clk: clock) {
            inst(_) pl(clk)
        }
    "
}

snapshot_error! {
    wildcards_in_pipeline_heads_are_disallowed,
    "
        pipeline(_) pl(clk: clock) {
            reg;
        }

        entity test(clk: clock) {
            inst(_) pl(clk)
        }
    "
}

snapshot_error! {
    wildcards_in_pipeline_reg_count_are_not_allowed,
    "
        pipeline(1) pl(clk: clock) {
            reg * _;
        }

        entity test(clk: clock) {
            inst(_) pl(clk)
        }
    "
}

snapshot_error! {
    lambda_entity_clock_must_be_clock,
    "
        entity test(clk: clock) {
            let _ = entity |clk| {
                let clk: uint<8> = clk;
            }.inst call(clk, ());
        }
    "
}

code_compiles! {
    lambdas_are_hygienic,
    "
        entity test<T>(val: Option<T>) -> Option<T> {
          val
            .map(fn |t| {
              t
            })
        }

        entity concrete1() {
          let _ = inst test(Some(1u8));
        }
        entity concrete2() {
          let _ = inst test(Some(1u9));
        }
    ",
    all
}

snapshot_error! {
    pipelines_check_the_delay_of_last_expression,
    "
        pipeline(1) subpipe(clk: clock) -> bool {
        reg;
            false
        }

        pipeline(0) test(clk: clock) -> bool {
            inst(1) subpipe(clk)
        }
    "
}

snapshot_error! {
    pipelines_check_the_delay_of_last_expression_with_genif,
    "
        pipeline(1) subpipe(clk: clock) -> bool {
        reg;
            false
        }

        pipeline(0) test(clk: clock) -> bool {
            gen if 1 == 1 {
                inst(1) subpipe(clk)
            } else {
                false
            }
        }
    "
}

snapshot_error! {
    methods_cannot_launder_pipeline_latency,
    "
        pipeline(10) test(clk: clock) -> [bool; 8] {
          reg*10;
            [false; 8]
        }

        pipeline(1) main(clk: clock) -> int<8> {
            let x = inst(10) test(clk).to_int();
          reg;
            x
        }
    "
}

snapshot_error! {
    mixed_latency_arguments_is_not_allowed,
    "
        pipeline(10) test(clk: clock) -> [bool; 8] {
          reg*10;
            [false; 8]
        }

        impl [bool; 8] {
            fn takes_an_arg(self, x: uint<8>) -> int<8> {
                0
            }
        }

        pipeline(1) main(clk: clock) -> int<8> {
            let a = 5;
            let x = inst(10) test(clk).takes_an_arg(a);
          reg;
            x
        }
    "
}

code_compiles! {
    mixed_latency_arguments_is_allowed_on_ports,
    "
        pipeline(10) test(clk: clock) -> [bool; 8] {
          reg*10;
            [false; 8]
        }

        impl [bool; 8] {
            entity takes_an_arg(self, clk: clock) -> int<8> {
                0
            }
        }

        pipeline(10) main(clk: clock) -> int<8> {
            let x = inst(10) test(clk).inst takes_an_arg(clk);
          reg * 10;
            x
        }
    "
}

code_compiles! {
    type_level_if_bool_with_output_works,
    "
        fn nested<#uint N>(x: uint<8>, y: uint<8>) -> uint<8> {
            gen if N == 0 {
                x
            } else {
                y
            }
        }

        fn mutiliple_tests() -> (uint<8>, uint<8>) {
            (nested::<0>(0, 1), 0)
        }
    "
}

#[cfg(test)]
mod trait_tests {
    use crate::{build_items, build_items_with_stdlib, code_compiles, snapshot_error};

    snapshot_error! {
        ast_lowering_errors_are_caught_in_impl_blocks,
        "
        struct X {}

        impl X {
            fn x(self) {
                a
            }
        }
        "
    }

    snapshot_error! {
        type_errors_are_caught_in_impl_blocks,
        "
        struct X {}

        impl X {
            fn x(self) -> bool {
                1
            }
        }
        "
    }

    snapshot_error! {
        type_errors_are_ok_in_free_standing_functions,
        "
            fn x() -> bool {
                1
            }
        "
    }

    #[test]
    fn accessing_fields_on_self_works() {
        let code = "
            struct X {
                a: int<8>
            }

            impl X {
                fn x(self) -> int<8> {
                    self.a
                }
            }
        ";

        build_items(code);
    }

    snapshot_error! {
        multiple_anonymous_impls_of_same_function_is_an_error,
        "
            struct X {}

            impl X {
                fn a(self) -> bool {true}
            }

            impl X {
                fn a(self) -> bool {false}
            }
        "
    }

    #[test]
    fn calling_method_does_not_error() {
        let code = "
            struct X {}
            impl X {
                fn test(self) -> bool {true}
            }

            fn main(x: X) -> bool {
                x.test()
            }
        ";
        build_items(code);
    }

    snapshot_error! {
        multiple_same_named_methods_errors,
        "
            struct X {}
            impl X {
                fn test(self) -> bool {true}
            }
            impl X {
                fn test(self) -> bool {false}
            }

            fn main(x: X) -> bool {
                x.test()
            }
            "
    }

    snapshot_error! {
        multiple_impls_of_same_trait_is_error,
        "
            trait A {
                fn a(self);
            }
            struct X {}
            impl A for X {
                fn a(self) {}
            }
            impl A for X {
                fn a(self) {}
            }

            fn main(x: X) -> bool {
                true
            }
        "
    }

    #[test]
    fn multiple_impls_of_same_trait_same_trait_args_different_target_args_works() {
        let code = "
        struct A<#uint I> {}
        trait X<T> {}
        impl X<bool> for A<0> {}
        impl X<bool> for A<1> {}
        ";
        build_items(code);
    }

    #[test]
    fn multiple_impls_of_same_trait_different_type_params_works() {
        let code = "
        trait X<T> {}
        impl X<bool> for bool {}
        impl X<uint<1>> for bool {}
        ";
        build_items(code);
    }

    snapshot_error! {
        multiple_impls_of_same_trait_same_type_params_is_error,
        "
            trait X<T> {}
            impl X<bool> for bool {}
            impl X<bool> for bool {}
        "
    }

    snapshot_error! {
        multiple_impls_of_same_trait_same_type_params_is_error2,
        "
            trait X<T> {}
            struct A<#uint I> {}
            impl X<bool> for A<1> {}
            impl X<bool> for A<1> {}
        "
    }

    snapshot_error! {
        multiple_same_name_traits_is_error,
        "
            trait A {}
            trait A {}

            fn main() {}
        "
    }

    snapshot_error! {
        anonymous_traits_overlap_correctly_mentioned,
        "
            impl int<0> {
                fn x(self) {}
            }

            impl int<2> {
                fn x(self) {}
            }

            impl int<2> {
                fn x(self) {}
            }
        "
    }

    snapshot_error! {
        anonymous_generic_traits_overlap_correctly_mentioned,
        "
        impl int<2> {
            fn x(self) {}
        }

        impl<#uint N> int<N> {
            fn x(self) {}
        }
        "
    }

    snapshot_error! {
        named_trait_overlap_correctly_mentioned,
        "
        trait T<X> {}

        struct Struct {}

        impl<X> T<X> for Struct {}
        impl T<bool> for Struct {}
        "
    }

    snapshot_error! {
        calling_methods_with_the_wrong_number_of_params_errors,
        "
            struct X {}
            impl X {
                fn test(self) -> bool {true}
            }

            fn main(x: X) -> bool {
                x.test(1)
            }
        "
    }

    snapshot_error! {
        calling_methods_with_the_wrong_named_args,
        "
            struct X {}
            impl X {
                fn test(self, x: bool) -> bool {true}
            }

            fn main(x: X) -> bool {
                x.test$(y: 1)
            }
        "
    }

    snapshot_error! {
        method_which_does_not_take_self_is_an_error,
        "
            struct X {}
            impl X {
                fn test(x: bool) -> bool {true}
            }

            fn main(x: X) -> bool {
                x.test$(y: 1)
            }
        "
    }

    snapshot_error! {
        binding_self_causes_reasonable_error,
        "
            struct X {}
            impl X {
                fn test(self, x: bool) -> bool {true}
            }

            fn main(x: X) -> bool {
                x.test$(self: X())
            }
        "
    }

    snapshot_error! {
        duplicate_method_causes_error,
        "
            struct X {}

            impl X {
                fn a(self) -> bool {true}
            }

            impl X {
                fn a(self) -> bool {true}
            }

            fn test(x: X) -> bool {
                x.a()
            }

        "
    }

    snapshot_error! {
        good_suggestion_for_missing_self_in_zero_arg_fn,
        "
            struct X {}

            impl X {
                fn a() -> bool {true}
            }
        "
    }

    #[test]
    fn anonymous_trait_in_module_works() {
        let code = "
            mod m {
                enum ContainerSpot {
                    Empty,
                    Occupied{val: int<8>},
                    NewRow,
                    Done
                }

                impl ContainerSpot {
                    fn is_valid(self, other: ContainerSpot) -> bool {
                        match self {
                            ContainerSpot::Occupied(_) => true,
                            _ => false,
                        }
                    }
                }
            }
        ";

        build_items(code);
    }

    snapshot_error! {
        error_message_on_missing_method,
        "
        struct X {}

        fn t(x: X) {
            x.test()
        }
        "
    }

    #[test]
    fn method_inst_works() {
        let code = "
            struct X {}

            impl X {
                entity a(self) -> bool {true}
            }

            entity main(x: X) -> bool {
                x.inst a()
            }
        ";
        build_items(code);
    }

    snapshot_error! {
        method_non_inst_of_entity_errors_nicely,
        "
            struct X {}

            impl X {
                entity a(self) -> bool {true}
            }

            fn t(x: X) -> bool {
                x.a()
            }
        "
    }

    snapshot_error! {
        method_inst_of_fn_errors_nicely,
        "
            struct X {}

            impl X {
                fn a(self) -> bool {true}
            }

            entity t(x: X) -> bool {
                x.inst a()
            }
        "
    }

    #[test]
    fn impl_trait_compiles() {
        let code = "
            trait X {
                fn a(self, x: Self) -> Self;
            }

            struct A {}
            struct B {}

            impl X for A {
                fn a(self, x: Self) -> Self {
                    A()
                }
            }

            impl X for B {
                fn a(self, x: B) -> B {
                    B()
                }
            }
        ";

        build_items(code);
    }

    snapshot_error! {
        missing_method_in_trait_def_errors,
        "
            trait X {
                fn a(self);
            }

            struct A {}

            impl X for A {
            }
        "
    }

    snapshot_error! {
        missing_2_method_in_trait_def_errors,
        "
            trait X {
                fn a(self);
                fn b(self);
            }

            struct A {}

            impl X for A {
            }
        "
    }

    snapshot_error! {
        missing_3_method_in_trait_def_errors,
        "
            trait X {
                fn a(self);
                fn b(self);
                fn c(self);
            }

            struct A {}

            impl X for A {
            }
        "
    }

    snapshot_error! {
        missing_4_method_in_trait_def_errors,
        "
            trait X {
                fn a(self);
                fn b(self);
                fn c(self);
                fn d(self);
            }

            struct A {}

            impl X for A {
            }
        "
    }

    snapshot_error! {
        unrelated_method_in_impl_block_errors,
        "
            trait X {
                fn a(self) -> bool;
            }

            struct A {}

            impl X for A {
                fn a(self) -> bool{
                    true
                }

                fn b(self) -> bool {
                    true
                }
            }
        "
    }

    snapshot_error! {
        multiple_impls_of_same_method_is_error,
        "
            struct A {}

            impl A {
                fn a(self) -> bool {
                    true
                }

                fn a(self) -> bool {
                    false
                }
            }
        "
    }

    snapshot_error! {
        impls_require_correct_signature_missing_args,
        "
            trait X {
                fn a(self, x: bool) -> bool;
            }

            struct A {}

            impl X for A {
                fn a(self) -> bool{
                    true
                }
            }
        "
    }

    snapshot_error! {
        impls_require_correct_signature_unknown_arg,
        "
            trait X {
                fn a(self) -> bool;
            }

            struct A {}

            impl X for A {
                fn a(self, x: bool) -> bool{
                    true
                }
            }
        "
    }

    snapshot_error! {
        impls_require_correct_signature_wrong_arg_type,
        "
            trait X {
                fn a(self, x: bool) -> bool;
            }

            struct A {}

            impl X for A {
                fn a(self, x: int<10>) -> bool {
                    true
                }
            }
        "
    }

    snapshot_error! {
        impls_require_correct_signature_wrong_arg_type_self,
        "
            trait X {
                fn a(self, x: Self) -> bool;
            }

            struct A {}
            struct B {}

            impl X for A {
                fn a(self, x: Self) -> bool {
                    true
                }
            }

            impl X for B {
                fn a(self, x: A) -> bool {
                    true
                }
            }
        "
    }

    snapshot_error! {
        impls_require_correct_signature_wrong_return_type,
        "
            trait X {
                fn a(self) -> int<10>;
            }

            struct A {}

            impl X for A {
                fn a(self) -> bool {
                    true
                }
            }
        "
    }

    snapshot_error! {
        impls_require_correct_signature_wrong_return_type_self,
        "
            trait X {
                fn a(self) -> Self;
            }

            struct A {}
            struct B {}

            impl X for A {
                fn a(self) -> A {
                    A()
                }
            }

            impl X for B {
                fn a(self) -> A {
                    A()
                }
            }
        "
    }

    snapshot_error! {
        impls_require_argument_name_correctness,
        "
            trait X {
                fn a(self, a: bool) -> bool;
            }

            struct A {}

            impl X for A {
                fn a(self, b: bool) -> bool {
                    true
                }
            }
        "
    }

    snapshot_error! {
        impls_require_argument_position_correctness,
        "
            trait X {
                fn a(self, a: bool, b: bool) -> bool;
            }

            struct A {}

            impl X for A {
                fn a(self, b: bool, a: bool) -> bool {
                    true
                }
            }
        "
    }

    #[test]
    fn impl_blocks_support_generics() {
        let code = r#"
        struct HasGeneric<T> {}
        impl<T> HasGeneric<T> {
            fn test(self) {}
        }
        "#;
        build_items(code);
    }

    snapshot_error! {
        impl_of_tuple_is_error,
        r#"
            struct T {}

            impl (bool, bool) for T {}
        "#
    }

    #[test]
    fn impl_type_parameters_are_visible_in_function_bodies() {
        let code = "
        struct HasGeneric<#uint N> {}

        impl<#uint N> HasGeneric<N> {
            fn get_generic(self) -> int<8> {
                N
            }
        }
        ";

        build_items(code);
    }

    #[test]
    fn generic_function_in_impl_block_works() {
        let code = "
        struct Fp<#uint Size, #uint FracBits> {
            inner: int<Size>
        }
        impl<#uint Size, #uint FracBits> Fp<Size, FracBits> {
            fn add<#uint OutSize>(self, other: Fp<Size, FracBits>) -> Fp<OutSize, FracBits> {
                Fp(self.inner + other.inner)
            }

            fn sub<#uint OutSize>(self, other: Fp<Size, FracBits>) -> Fp<OutSize, FracBits> {
                Fp(self.inner - other.inner)
            }
        }
        ";

        build_items(code);
    }

    #[test]
    fn mutually_exclusive_methods_are_allowed() {
        let code = "
            impl uint<8> {
                fn method(self) {}
            }

            impl uint<16> {
                fn method(self) {}
            }
        ";
        build_items(code);
    }

    snapshot_error! {
        conflicting_method_impls_are_disallowed_inner_generic,
        "
            impl<T> uint<T> {
                fn method(self) {}
            }

            impl uint<16> {
                fn method(self) {}
            }
        "
    }

    snapshot_error! {
        conflicting_method_impls_are_disallowed_inner_tuple,
        "
            struct X<T> {}
            impl<T> X<T> {
                fn method(self) {}
            }

            impl X<(bool, bool)> {
                fn method(self) {}
            }
        "
    }

    #[test]
    fn non_conflicting_method_impls_are_allowed_inner_tuple() {
        let code = "
            struct X<T> {}
            impl<T> X<(T, bool)> {
                fn method(self) {}
            }

            impl X<(bool, uint<8>)> {
                fn method(self) {}
            }
        ";
        build_items(code);
    }

    snapshot_error! {
        conflicting_method_impls_are_disallowed_inner_array_type,
        "
            struct X<T> {}
            impl<T> X<[T; 3]> {
                fn method(self) {}
            }

            impl X<[bool; 3]> {
                fn method(self) {}
            }
        "
    }

    snapshot_error! {
        conflicting_method_impls_are_disallowed_inner_array_size,
        "
            struct X<T> {}
            impl<#uint N> X<[bool; N]> {
                fn method(self) {}
            }

            impl X<[bool; 3]> {
                fn method(self) {}
            }
        "
    }

    #[test]
    fn non_conflicting_method_impls_are_allowed_array_different_size() {
        let code = "
            struct X<T> {}
            impl X<[bool; 4]> {
                fn method(self) {}
            }

            impl X<[bool; 3]> {
                fn method(self) {}
            }
        ";
        build_items(code);
    }

    #[test]
    fn method_selection_works_multiple_exclusive_candidates() {
        let code = "
            impl uint<8> {
                fn method(self) {}
            }
            impl uint<9> {
                fn method(self) {}
            }

            fn test(x: uint<8>) {
                x.method()
            }
        ";
        build_items(code);
    }

    #[test]
    fn method_selection_works_on_generic_impl() {
        let code = "
            impl<#uint N> uint<N> {
                fn method(self) {}
            }
            fn test(x: uint<8>) {
                x.method()
            }
        ";
        build_items(code);
    }

    snapshot_error! {
        blanket_impl_is_disallowed_gracefully,
        "
            impl<T> T {
                fn method(self) {}
            }
        "
    }

    #[test]
    fn method_selection_works_when_type_is_not_fully_known_until_later() {
        let code = "
            impl uint<3> {
                fn method(self) {}
            }

            entity test() {
                decl crc;

                let to_transmit = std::conv::bits_to_uint(crc).method();

                let crc = [true, true, true];
            }
        ";
        build_items_with_stdlib(code);
    }

    snapshot_error! {
        irrelevant_methods_are_not_suggested,
        "
            impl uint<8> {
                fn method(self) {}
            }

            entity test(x: uint<10>) {
                x.method()
            }
        "
    }

    #[test]
    fn impl_inner_type_expr() {
        let code = "
            trait T<#uint N> {
                fn method(self);
            }

            struct X {}
            impl T<8> for X {
                fn method(self) {}
            }

            fn use_method(x: X) {
                x.method()
            }
        ";
        build_items(code);
    }

    snapshot_error! {
        struct_impls_are_specific,
        "
            struct Struct<T1, T2> {x: T1, y: T2}

            impl Struct<bool, bool> {
                fn method(self) {}
            }

            fn test() {
                Struct(true, 0u8).method()
            }
        "
    }

    snapshot_error! {
        array_impls_are_specific1,
        "
            impl [bool; 8] {
                fn method(self) {}
            }

            fn test() {
                [0u8; 8].method()
            }
        "
    }

    snapshot_error! {
        method_resolution_errors_gracefully_on_generic_types,
        "
            impl [bool; 8] {
                fn method(self) {}
            }

            fn test() {
                [0; 8].method()
            }
        "
    }

    snapshot_error! {
        multiple_traits_with_ambiguous_methods,
        "
            trait A {
                fn method(self);
            }
            trait B {
                fn method(self);
            }

            fn test<T>(x: T)
                where T: A + B
            {
                x.method()
            }
        "
    }

    code_compiles! {
        method_call_on_array_works,
        "
            impl [bool; 8] {
                fn method(self) {}
            }

            fn test() {
                [true; 8].method()
            }
        "
    }

    code_compiles! {
        method_call_on_wire_works,
        "
            impl &bool {
                entity method(self) {}
            }

            entity test() {
                (&true).inst method()
            }
        "
    }

    code_compiles! {
        method_call_on_inv_wire_works,
        "
            impl inv &bool {
                entity method(self) {
                    set self = &true;
                }
            }

            entity test(x: inv& bool) {
                x.inst method()
            }
        "
    }
}

#[cfg(test)]
mod unsafe_tests {
    use crate::{build_items, code_compiles, snapshot_error};

    code_compiles! {
        unsafe_invocation_in_unsafe_block,
        "
        unsafe fn method() {}

        fn test() {
            unsafe { method(); }
        }
        "
    }

    snapshot_error! {
        unsafe_invocation_needs_block,
        "
        unsafe fn method() {}

        fn test() {
            method();
        }
        "
    }

    snapshot_error! {
        unsafe_invocation_still_needs_block_in_unsafe_fn,
        "
        unsafe fn method() {}

        unsafe fn test() {
            method();
        }
        "
    }

    snapshot_error! {
        unsafe_cx_resets_for_lambda,
        "
        unsafe fn method() {}

        fn test() {
            unsafe {
                let lambda = fn|| { method(); };
                lambda.call(());
            }
        }
        "
    }

    code_compiles! {
        unsafe_expr_works,
        "
        unsafe fn method() -> bool { true }

        fn test() -> bool {
            unsafe { method() }
        }
        "
    }

    // This compiles we need the warning diagnostic
    snapshot_error! {
        double_unsafe_block_gets_hint,
        "
        unsafe fn method() {}

        fn test() {
            unsafe {
                unsafe {
                    method();
                }
            }
        }
        "
    }

    code_compiles! {
        unsafe_fn_in_trait,
        "
        trait X {
            unsafe fn method(self);
        }

        impl X for bool {
            unsafe fn method(self) { }
        }
        "
    }

    snapshot_error! {
        unsafe_fn_in_trait_impl_requires_unsafe,
        "
        trait X {
            unsafe fn method(self);
        }

        impl X for bool {
            fn method(self) { }
        }
        "
    }

    snapshot_error! {
        unsafe_fn_in_trait_impl_mustnt_have_unsafe,
        "
        trait X {
            fn method(self);
        }

        impl X for bool {
            unsafe fn method(self) { }
        }
        "
    }
}
