use crate::{build_items, snapshot_error};

snapshot_error! {
    backward_types_can_not_be_put_in_registers,
    "
    entity x(clk: clock, a: ~& bool) -> bool {
        reg(clk) _ = a;
        true
    }
    "
}

snapshot_error! {
    transitive_backward_type_can_not_be_put_in_registers,
    "
    struct port X {
        a: ~& bool,
        b: &bool
    }
    entity x(clk: clock, a: X) -> bool {
        reg(clk) _ = a;
        true
    }
    "
}

snapshot_error! {
    wire_types_can_not_be_stored_in_registers,
    "
    entity x(clk: clock, a: &bool) -> bool {
        reg(clk) _ = a;
        true
    }
    "
}

snapshot_error! {
    wire_read_requires_dereference,
    "
    entity x(a: &bool) -> bool {
        a
    }"
}

#[test]
fn dereferencing_a_reference_works() {
    let code = "entity x(a: &bool) -> bool {
        *a
    }";

    build_items(code);
}

snapshot_error! {
    wires_can_not_be_passed_as_generics,
    "
    entity identity<T>(x: T) -> T {x}

    entity x(p: &bool) -> &bool {
        inst identity(p)
    }
    "
}

snapshot_error! {
    wires_can_not_be_passed_as_generics2,
    "
    entity identity<T>(x: T) -> T {x}

    entity x(p: &bool) -> &bool {
        let x: &bool = inst identity(p);
        x
    }
    "
}

snapshot_error! {
    memory_of_ports_is_disallowed,
    "
    entity A(clk: clock, p: &bool) -> bool {
        let idx: uint<10> = 0;
        let mem: Memory<&bool, 1024> = inst std::mem::clocked_memory(clk, [(true, idx, p)]);

        true
    }"
}

snapshot_error! {
    assigning_value_to_wire_causes_error,
    "
    entity x(x: bool) -> &bool {
        x
    }
    "
}

#[test]
fn wires_can_be_created() {
    let code = "entity x(x: bool) -> &bool {
        &x
    }";

    build_items(code);
}

snapshot_error! {
    assigning_ports_to_ports_is_disallowed,
    "
        entity not_allowed(a: ~& (&bool, &bool), b: (&bool, &bool)) -> bool {
            set a = b;
            true
        }
        "
}

snapshot_error! {
    ports_are_not_allowed_in_functions,
    "
        fn not_allowed(a: &bool) -> bool {
            true
        }
        "
}
