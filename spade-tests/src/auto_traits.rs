use crate::{build_items, code_compiles, snapshot_error};

snapshot_error! {
    type_with_inv_is_not_copy,
    "
        struct A {
            x: bool,
            y: inv bool,
        }

        fn needs_copy<T: Copy>(x: T) {}

        fn test(x: A) {
            needs_copy(x)
        }
    ",
    false
}

snapshot_error! {
    type_with_clock_is_not_data,
    "
        struct A {
            x: bool,
            y: clock,
        }

        fn needs_data<T: Data>(x: T) {}

        fn test(x: A) {
            needs_data(x)
        }
    ",
    false
}

code_compiles! {
    type_without_clock_is_data,
    "
        struct A {
            x: bool,
            y: inv bool,
        }

        fn needs_data<T: Data>(x: T) -> T {
            x
        }

        fn test(x: A) -> A {
            needs_data(x)
        }
    "
}

code_compiles! {
    type_without_inv_is_copy,
    "
        struct A {
            x: bool,
            y: clock,
        }

        fn needs_copy<T: Copy>(x: T) {}

        fn test(x: A) {
            needs_copy(x)
        }
    "
}

code_compiles! {
    generic_type_is_data_if_generic_is_data,
    "
        struct A<T> {
            x: bool,
            y: T,
        }

        fn needs_data<T: Data>(x: T) {}

        fn test1(x: bool) {
            needs_data(x)
        }
    "
}

code_compiles! {
    generic_type_is_copy_if_generic_is_copy,
    "
        struct A<T> {
            x: bool,
            y: T,
        }

        fn needs_copy<T: Copy>(x: T) {}

        fn test1(x: bool) {
            needs_copy(x)
        }
    "
}

snapshot_error! {
    generic_type_is_not_data_if_generic_is_not_data,
    "
        fn needs_data<T: Data>(x: T) {}

        fn test1(x: clock) {
            needs_data(x)
        }
    "
}

snapshot_error! {
    generic_type_is_not_copy_if_generic_is_not_copy,
    "
        fn needs_copy<T: Copy>(x: T) {}

        fn test1(x: inv bool) {
            needs_copy(x)
        }
    "
}

code_compiles! {
    generic_type_is_data_if_generic_is_data_recursively,
    "
        struct A<T> {
            x: bool,
            y: T,
        }

        struct B<T> {
            payload: T
        }

        fn needs_data<T: Data>(x: T) {}

        fn test1(x: B<A<bool>>) {
            needs_data(x)
        }
    "
}

snapshot_error! {
    generic_type_is_not_data_if_generic_is_not_data_recursively,
    "
        struct A<T> {
            x: bool,
            y: T,
        }

        struct B<T> {
            payload: T
        }

        fn needs_data<T: Data>(x: T) {}

        fn test1(x: B<A<clock>>) {
            needs_data(x)
        }
    "
}

snapshot_error! {
    generic_type_is_not_copy_if_generic_is_not_copy_recursively,
    "
        struct A<T> {
            x: bool,
            y: T,
        }

        struct B<T> {
            payload: T
        }

        fn needs_copy<T: Copy>(x: T) {}

        fn test1(x: B<A<inv bool>>) {
            needs_copy(x)
        }
    "
}

code_compiles! {
    tuples_are_data,
    "
        struct A {
            x: (bool, bool)
        }

        fn needs_data<T: Data>(x: T) {}

        fn test1(x: A) {
            needs_data(x)
        }
    "
}

code_compiles! {
    tuples_are_copy,
    "
        struct A {
            x: (bool, bool)
        }

        fn needs_copy<T: Copy>(x: T) {}

        fn test1(x: A) {
            needs_copy(x)
        }
    "
}

snapshot_error! {
    tuples_can_deny_data,
    "
        struct A {
            x: (clock, bool)
        }

        fn needs_data<T: Data>(x: T) {}

        fn test1(x: A) {
            needs_data(x)
        }
    "
}

snapshot_error! {
    tuples_can_deny_data_generic,
    "
        struct A<T> {
            x: T
        }

        fn needs_data<T: Data>(x: T) {}

        fn test1(x: A<(clock, bool)>) {
            needs_data(x)
        }
    "
}

snapshot_error! {
    tuples_can_deny_copy,
    "
        struct A {
            x: (inv bool, bool)
        }

        fn needs_copy<T: Copy>(x: T) {}

        fn test1(x: A) {
            needs_copy(x)
        }
    "
}

snapshot_error! {
    tuples_can_deny_copy_generic,
    "
        struct A<T> {
            x: T
        }

        fn needs_copy<T: Copy>(x: T) {}

        fn test1(x: A<(inv clock, bool)>) {
            needs_copy(x)
        }
    "
}

snapshot_error! {
    tuples_alone_are_not_data,
    "
        struct A<T> {
            x: T
        }

        fn needs_data<T: Data>(x: T) {}

        fn test1(x: (clock, bool)) {
            needs_data(x)
        }
    "
}

snapshot_error! {
    tuples_alone_are_not_copy,
    "
        struct A<T> {
            x: T
        }

        fn needs_copy<T: Copy>(x: T) {}

        fn test1(x: (inv bool, bool)) {
            needs_copy(x)
        }
    "
}

snapshot_error! {
    registers_require_data,
    "
        entity test(clk: clock) {
            reg(clk) r = clk;
        }
    "
}

snapshot_error! {
    registers_require_copy,
    "
        entity test(clk: clock) {
            reg(clk) r = port().1;
        }
    "
}

code_compiles! {
    impl_enum_data_requirement_works,
    "
        struct Escaped<T> {}

        struct Outer<T> {}

        impl Outer<Escaped<bool>> {
            fn test(self) {}
        }
    "
}
