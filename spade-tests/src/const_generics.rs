use insta::assert_debug_snapshot;

use crate::{build_items, snapshot_error};

#[test]
fn constrained_ints_in_where_clause_compiles() {
    let code = r#"
        fn test<#uint M, #uint N, #uint O>()
            where O: { M + N + 1 }
        {}
    "#;

    build_items(code);
}

snapshot_error! {
    generic_type_in_const_generic_where_clause_rhs,
    "
        fn test<N, #uint O>()
            where O: { N }
        {}
    "
}

snapshot_error! {
    struct_type_in_const_generic_where_clause,
    "
        struct N {}
        fn test<#uint O>()
            where O: { N }
        {}
    "
}

snapshot_error! {
    int_literal_in_where_clause_trait_bound_rhs,
    "
        fn test<T>()
            where T: 1
        {}
    "
}

snapshot_error! {
    struct_in_where_clause_trait_bound_rhs,
    "
        struct S {}
        fn test<T>()
            where T: S
        {}
    "
}

snapshot_error! {
    enum_in_where_clause_trait_bound_rhs,
    "
        enum E {}
        fn test<T>()
            where T: E
        {}
    "
}

snapshot_error! {
    const_int_in_const_generic_where_clause_rhs,
    "
        fn test<T>()
            where T: { 1 }
        {}
    "
}

snapshot_error! {
    struct_in_const_generic_where_clause_rhs,
    "
        struct S {}
        fn test<T>()
            where T: S
        {}
    "
}

snapshot_error! {
    enum_in_const_generic_where_clause_rhs,
    "
        enum E {}
        fn test<T>()
            where T: E
        {}
    "
}

snapshot_error! {
    trait_in_const_generic_where_clause_rhs,
    "
        trait X {}
        fn test<#uint N>() 
            where N: { X }
        {}
    "
}

snapshot_error! {
    trait_in_const_generic_where_clause_lhs,
    "
        trait X {}
        fn test<#uint N>() 
            where X: { N }
        {}
    "
}

snapshot_error! {
    struct_in_const_generic_where_clause_lhs,
    "
        struct S {}
        fn test<#uint N>() 
            where S: { N }
        {}
    "
}

snapshot_error! {
    generic_type_in_const_generic_where_clause_lhs,
    "
        fn test<T, #uint N>() 
            where T: { N }
        {}
    "
}

snapshot_error! {
    trait_and_const_int_in_where_clause_trait_bound_rhs,
    "
        trait X {}
        fn test<T>()
            where T: { X + 1 }
        {}
    "
}

snapshot_error! {
    int_literal_in_trait_bound_rhs,
    "
        trait X {}
        fn test<T: 1>() {}
    "
}

snapshot_error! {
    struct_in_trait_bound_rhs,
    "
        struct S {}
        fn test<T: S>() {}
    "
}

snapshot_error! {
    enum_in_where_clause_trait_bound_lhs,
    "
        enum E {}
        trait X {}
        fn test()
            where E: X
        {}
    "
}

snapshot_error! {
    generic_int_in_where_clause_trait_bound_lhs,
    "
        trait X {}
        fn test<#uint N>()
            where N: X
        {}
    "
}

snapshot_error! {
    enum_in_trait_bound_rhs,
    "
        enum E {}
        trait X {}
        fn test<T: E>() {}
    "
}

#[test]
fn generic_trait_bound_compiles() {
    let code = r#"
        trait Into<T> {
            fn into(self) -> T;
        }
        impl Into<bool> for uint<1> {
            fn into(self) -> bool {
                self == 1
            }
        }
        
        fn test<T: Into<bool>>(x: T) -> bool {
            1u1.into()
        }
    "#;
    build_items(code);
}

snapshot_error! {
    trait_bound_from_where_clause_not_satisfied,
    "
        trait X {}
        fn test<T>(x: T)
            where T: X
        {
            test(false)
        }
    "
}

snapshot_error! {
    trait_bounds_from_where_clause_not_fully_satisfied,
    "
        trait X {}
        trait Y {}
        impl X for bool {}
        fn test<T>(x: T)
            where T: X + Y
        {
            test(false)
        }
    "
}

snapshot_error! {
    trait_bound_not_satisfied,
    "
        trait X {}
        fn test<T: X>(x: T)
        {
            test(false)
        }
    "
}

snapshot_error! {
    trait_bounds_not_fully_satisfied,
    "
        trait X {}
        trait Y {}
        impl X for bool {}
        fn test<T: X + Y>(x: T)
        {
            test(false)
        }
    "
}

snapshot_error! {
    generic_trait_bound_not_satisfied,
    "
        trait X<T> {}
        impl X<uint<8>> for bool {}
        fn test<T>(x: T)
            where T: X<bool>
        {
            test(false)
        }
    "
}

snapshot_error! {
    generic_trait_bound_not_fully_satisfied,
    "
        trait X<T, R> {}
        impl X<bool, uint<8>> for bool {}
        fn test<T>(x: T)
            where T: X<bool, bool>
        {
            test(false)
        }
    "
}

snapshot_error! {
    simple_unsatisfied_int_constraint_in_where_clause_errors,
    "
        fn add_one<#uint N, #uint O>(in: int<N>) -> int<O>
            where O: { N + 2 }
        {
            in + 1
        }

        fn test() -> int<10> {
            add_one(10i8)
        }
    "
}

snapshot_error! {
    method_exists_but_outside_trait_bound,
    "
        trait X {}
        impl X for bool {}
        impl bool {
            fn test(self) {}
        } 
        fn test<T: X>(it: T) {
            it.test()
        }
        fn main() {
            test(false)
        }
    "
}

snapshot_error! {
    simple_unsatisfied_int_constraint_in_where_clause_errors2,
    "
        fn add_one<#uint N, #uint O>(in: int<N>) -> int<O>
        where O: { N + 2 } {
            0
        }

        fn test() -> int<9> {
            add_one(10i8)
        }
    "
}

snapshot_error! {
    simple_unsatisfied_int_constraint_in_where_clause_on_impl_block_errors,
    "
        impl <#uint N, #uint O> int<N>
        where O: { N + 2 }
        {
            fn add_one(self) -> int<O> {
                self + 1
            }
        }

        fn test() -> int<10> {
            10i8.add_one()
        }
    "
}

snapshot_error! {
    simple_unsatisfied_int_constraint_in_where_clause_on_impl_block_errors2,
    "
        impl <#uint N, #uint O> int<N>
        where O: { N + 2 } {
            fn add_one(self) -> int<O> {
                0
            }
        }

        fn test() -> int<9> {
            10i8.add_one()
        }
    "
}

#[test]
fn int_constraints_in_where_clauses_drive_inference() {
    let code = "
        fn add_one<#uint N, #uint O>(in: int<N>) -> int<O>
        where O: { N + 2 } {
            0
        }

        fn test() {
            let _ = add_one(10i8);
        }
    ";
    build_items(code);
}

#[test]
fn int_constraints_in_where_clauses_on_impl_blocks_drive_inference() {
    let code = "
        impl<#uint N, #uint O> int<N>
        where O: { N + 2 } {
            fn add_one(self) -> int<O> {
                0
            }
        }

        fn test() {
            let _ = 10i8.add_one();
        }
    ";
    build_items(code);
}

snapshot_error! {
    type_expressions_in_generic_parameters_type_check,
    "
        fn foo<#uint N>(value: uint<{N + 1}>) {}

        fn bar() {
            let value: uint<2> = 0;
            foo::<2>(value)
        }
    "
}

snapshot_error! {
    type_expressions_in_generic_parameter_type_check_across_instanmces,
    "
        fn foo<#uint N>(value: uint<{N + 1}>) {}

        fn bar() {
            let _ = foo::<3>(0u3);
            let _ = foo::<4>(0u4);
        }
    "
}

#[test]
fn type_expressions_in_generic_parameter_lower_correctly() {
    let code = "
        fn foo<#uint N>(value: uint<{N + 1}>) {}

        fn bar() {
            let _ = foo::<2>(0u3);
            let _ = foo::<3>(0u4);
        }
    ";
    assert_debug_snapshot!(build_items(code));
}
