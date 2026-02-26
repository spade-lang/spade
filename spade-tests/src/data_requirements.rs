use crate::{snapshot_error};

snapshot_error! {
    reg_requires_data,
    "
        entity test(clk: clock) {
            reg(clk) r = port;
        }
    "
}

snapshot_error! {
    pipeline_binding_requires_data,
    "
        pipeline(0) test(clk: clock) {
            let r = port;
        }
    ",
    false
}
