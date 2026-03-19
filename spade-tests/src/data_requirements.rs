use crate::{build_items, code_compiles, snapshot_error};

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

snapshot_error! {
    enum_cannot_contain_inv,
    "
        enum Type {
            V0,
            V1{x: inv bool}
        }

        fn test() -> Type {
            Type::V0
        }
    "
}

snapshot_error! {
    enum_cannot_contain_inv_recursive,
    "
        struct RecursivelyInv {
            x: inv bool
        }
        enum Type {
            V0,
            V1{x: RecursivelyInv}
        }

        fn test() -> Type {
            Type::V0
        }
    "
}

snapshot_error! {
    enum_cannot_contain_inout,
    "
        enum Type {
            V0,
            V1{x: inout<bool>}
        }

        fn test() -> Type {
            Type::V0
        }
    "
}

code_compiles! {
    inv_data_can_be_captured,
    "
        entity test(clk: clock) {
            let x: inv bool = port.1;

            let lambda = entity |clk| {
                set x = false;
            };

            lambda.inst call(clk, ());
        }
    "
}

code_compiles! {
    inv_data_can_be_captured_in_pipelines,
    "
        entity test(clk: clock) {
            let x: inv bool = port.1;

            let lambda = pipeline(1) |clk| {
            reg;
                set x = false;
            };

            lambda.inst(1) call(clk, ());
        }
    "
}
