use crate::snapshot_error;

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

snapshot_error! {
    enum_generics_must_be_data,
    "
        trait Tr {}
        enum E<T: Tr> {
            A{val: T},
            B,
        }

        fn test(p: inv bool) {
            let _ = E::A(p);
        }
    ",
    false
}

snapshot_error! {
    if_statements_require_data,
    "
        fn test(sel: bool, x: inv bool, y: inv bool) -> inv bool {
            if sel {
                x
            } else {
                y
            }
        }
    ",
    false
}

snapshot_error! {
    match_statement_requires_data,
    "
        fn test(sel: bool, x: inv bool, y: inv bool) -> inv bool {
            match sel {
                _ => x
            }
        }
    ",
    false
}
