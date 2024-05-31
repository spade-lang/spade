use crate::snapshot_error;

snapshot_error! {
    a_clock_and_reset_must_be_specified,
    "
        fsm test() {}
    "
}

snapshot_error! {
    a_reset_must_be_specified,
    "
        fsm test(clk: clock) {}
    "
}

snapshot_error! {
    the_clock_must_be_clock,
    "
        fsm test(clk: bool, rst: bool) {}
    "
}

snapshot_error! {
    the_reset_must_be_bool,
    "
        fsm test(clk: clock, rst: (bool, bool)) {}
    "
}

snapshot_error! {
    fsm_has_a_scope,
    "fn test() {
        for i in 0..1 {}
        let x = i;
    }"
}

snapshot_error! {
    fsm_has_a_scope_with_let_bindings,
    "fn test() {
        for i in 0..1 {
            let y = 0;
        }
        let x = y;
    }"
}

snapshot_error! {
    for_loop_outside_fsm_is_disallowed,
    "fn test() {
        for i in 0..10 {}
    }"
}

snapshot_error! {
    yield_outside_fsm_is_disallowed,
    "fn test() {
        yield 1;
    }"
}

snapshot_error! {
    yield_of_wrong_type_is_error,
    "fsm test(clk: clock, rst: bool) -> uint<8> {
        yield true;
    }"
}
