use crate::snapshot_error;

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
