use crate::build_items;
use crate::snapshot_mir;

snapshot_mir! {
    non_inline_fn_is_not_inlined,
    "
        fn not_inlined() -> uint<8> {
            0
        }

        fn test() -> uint<8> {
            not_inlined()
        }
    "
}

snapshot_mir! {
    simple_constant_is_inlined,
    "
        #[inline]
        fn inlined() -> uint<8> {
            0
        }

        fn test() -> uint<8> {
            inlined()
        }
    "
}

snapshot_mir! {
    less_simple_constant_is_inlined,
    "
        #[inline]
        fn inlined() -> uint<8> {
            let x = 0;
            x
        }

        fn test() -> uint<8> {
            inlined()
        }
    "
}

snapshot_mir! {
    recursion_works,
    "
        #[inline]
        fn recursive<#uint N>() -> uint<8> {
            let x: uint<10> = N;
            gen if N == 0 {
                N
            } else {
                recursive::<{N-1}>()
            }
        }

        fn test() -> uint<8> {
            recursive::<3>()
        }
    "
}

snapshot_mir! {
    two_inlined_recursive,
    "
        fn recursive<#uint N>() -> uint<8> {
            let x: uint<10> = N;
            gen if N == 0 {
                N
            } else {
                recursive::<{N-1}>()
            }
        }

        fn test() {
            let _ = recursive::<3>();
            let _ = recursive::<3>();
        }
    "
}

snapshot_mir! {
    two_inlined,
    "
        #[inline]
        fn inner() {
            let x = true;
        }

        #[inline]
        fn recursive() {
            inner()
        }

        fn test() {
            let _ = recursive();
            let _ = recursive();
        }
    "
}

snapshot_mir! {
    cache_cells_reproducer,
    "
    entity cache_cells() {
        let self_has_value = match 0 {
            addr => addr == 0u8,
        };
        gen if 0 != 0 {
        } else {
        }
    }

    entity test() {
        inst cache_cells()
    }
    "
}

snapshot_mir! {
    simple_inputs,
    "
        #[inline]
        fn inner(a: uint<8>) -> uint<9> {
            a + 2
        }

        fn test() -> uint<9> {
            inner(1)
        }
    "
}

snapshot_mir! {
    recursive_inputs,
    "
        #[inline]
        fn inner(a: uint<8>, b: uint<8>) -> uint<9> {
            a + b
        }

        fn test_inner() -> uint<9> {
            inner(0, 1)
        }

        #[inline]
        fn outer(a: uint<8>) -> uint<9> {
            inner(a, 2)
        }

        fn test() -> uint<9> {
            let val = 1;
            outer(val)
        }
    "
}
