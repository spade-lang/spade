use crate::{build_items, build_items_with_stdlib, code_compiles, snapshot_error};

snapshot_error! {
    reg_requires_data,
    "
        entity test(clk: clock) {
            reg(clk) r = port;
        }
    "
}
