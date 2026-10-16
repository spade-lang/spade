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

code_compiles! {
    copy_view_stuff,
    "
    struct S {
        a: bool,
        b: inv T,
    }

    struct T {
        x: bool,
    }

    entity main() {
        let (b, b_inv) = port();
        let s = S(false, b_inv);
        set s.b.x = false;
    }
    "
}

code_compiles! {
    copy_view_tuple_can_be_indexed,
    "
        fn main() {
            let t: (bool, inv bool) = (false, port().1);
            set t.1 = true;

            let x: &(bool, inv bool) = &t;
            let b: &inv bool = x.1;
        }
    "
}
