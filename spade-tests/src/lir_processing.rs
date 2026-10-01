use crate::{code_compiles, build_items};

code_compiles! {
    simple_io_compiles,
    "
        struct SimpleIO {
            fwd: int<8>,
            back: inv int<8>,
        }

        entity simple_io() -> SimpleIO {
            let (fwd, back) = port();
            SimpleIO { fwd, back }
        }
    "
}

code_compiles! {
    transmute_compiles,
    "
        impl<T, #uint N> [inv T; N] {
            fn transpose(self) -> inv [T; N] {
                unsafe { core::conv::transmute(self) }
            }
        }

        fn transmute_test() -> inv [bool; 1] {
            let x: (bool, _) = port();
            [x.1].transpose()
        }
    "    
}
