use crate::{build_items, snapshot_error};

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
            entity x() -> int<2> {
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
            entity x() -> int<2> {
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
            entity x() -> int<2> {
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
            mod Y {
                entity x() -> int<2> {
                    1
                }
            }
            use Y::x;
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
            set p.p1 = true;
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

#[cfg(test)]
mod trait_tests {
    use crate::{build_items, build_items_with_stdlib, snapshot_error};

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

    snapshot_error! {
        instantiating_pipeline_methods_fails_gracefully,
        "
            struct X {}

            impl X {
                pipeline(10) a(self) -> bool {true}
            }

            fn t(x: X) -> bool {
                x.a()
            }
        "
    }

    snapshot_error! {
        pipelines_in_impl_blocks_are_gracefully_disallowed,
        "
            struct X {}

            impl X {
                pipeline(0) a(self) -> bool {true}
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

    snapshot_error! {
        multiple_impls_of_same_trait_different_type_params_is_error,
        "
            trait X<T> {}
            impl X<bool> for bool {}
            impl X<uint<1>> for bool {}
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
        tuple_has_no_methods,
        "fn a(x: (bool, bool)) -> bool {x.test()}"
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

            fn t(x: X) -> bool {
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
                    Self()
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
        impl_on_tuple_is_error,
        r#"
            impl (bool, bool) {}
        "#
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
        impl_on_unnamed_type,
        "
            impl (bool, bool) {}
        "
    }
}
