use crate::{build_items, snapshot_mir};

snapshot_mir! {
    no_select_x_works,
    "
        enum Option<T> {
            None,
            Some{val: T}
        }

        #[optimize(no_select_x)]
        fn test(input: Option<uint<8>>) -> Option<uint<9>> {
            match input {
                Option::Some(val) => Option::Some(val + 1),
                Option::None => Option::None
            }
        }
    "
}

snapshot_mir! {
    no_select_x_works2,
    "
        enum Option<T> {
            None,
            Some{val: T}
        }

        #[optimize(no_select_x)]
        fn test(input: Option<uint<8>>) -> Option<uint<9>> {
            match input {
                Option::None => Option::None,
                Option::Some(val) => Option::Some(val + 1),
            }
        }
    "
}
