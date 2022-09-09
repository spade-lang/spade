use crate::{build_items, snapshot_error};

#[test]
fn namespacing_works() {
    let code = r#"
        mod X {
            entity x() -> int<2> {
                1
            }
        }

        entity top() -> int<2> {
            inst X::x()
        }
    "#;

    build_items(code);
}

snapshot_error!(
    namespacing_adds_to_the_correct_namespace,
    r#"
        mod X {
            entity x() -> int<2> {
                1
            }
        }

        entity top() -> int<2> {
            x()
        }
    "#
);

#[test]
fn use_statements_work() {
    let code = r#"
        mod X {
            entity x() -> int<2> {
                1
            }
        }

        use X::x;

        entity top() -> int<2> {
            inst x()
        }
        "#;

    build_items(code);
}

#[test]
fn renaming_use_statements_work() {
    let code = r#"
        mod X {
            entity x() -> int<2> {
                1
            }
        }

        use X::x as a;

        entity top() -> int<2> {
            inst a()
        }
        "#;

    build_items(code);
}

/// NOTE This test fails currently
#[test]
fn recursive_use_statements_work() {
    let code = r#"
        mod X {
            mod Y {
                entity x() -> int<2> {
                    1
                }
            }
            use Y::x;
        }

        use X::x as a;

        entity top() -> int<2> {
            inst a()
        }
    "#;

    build_items(code);
}

#[test]
fn using_names_in_namespaces_works() {
    let code = r#"
        mod X {
            enum A {X{a: bool}}

            entity x() -> A {
                A::X(true)
            }
        }
        "#;

    build_items(code);
}

#[test]
fn using_names_of_types_in_namespaces_works() {
    let code = r#"
        mod X {
            struct A {}
            struct B{a: A}
        }
        "#;

    build_items(code);
}

// NOTE: this is an awful error message at the moment, but it is strange code
// and fixing it would take quite a bit of effort, so we'll leave it be and
// create an issue for it
snapshot_error! {
    pipeline_shadowing_does_not_fail_silently,
    "
    pipeline(2) main(clk: clk, x: int<8>) -> int<8> {
            let x: int<8> = 0;
        reg;
            let x: int<8> = 1;
        reg;
            stage(-2).x
    }
    "
}

snapshot_error! {
    backward_types_can_not_be_put_in_registers,
    "
    entity x(clk: clk, a: &mut bool) -> bool {
        reg(clk) _ = a;
        true
    }
    "
}

snapshot_error! {
    transitive_backward_type_can_not_be_put_in_registers,
    "
    struct port X {
        a: &mut bool,
        b: &bool
    }
    entity x(clk: clk, a: X) -> bool {
        reg(clk) _ = a;
        true
    }
    "
}

snapshot_error! {
    wire_types_can_not_be_stored_in_registers,
    "
    entity x(clk: clk, a: &bool) -> bool {
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
    mod std {mod mem {
        entity clocked_memory<#NumElements, #WritePorts, #AddrWidth, D>(
            clk: clk,
            writes: [(bool, int<AddrWidth>, D); WritePorts],
        ) -> Memory<D, NumElements>
            __builtin__
        }
    }
    entity A(clk: clk, p: &bool) -> bool {
        let idx: int<10> = 0;
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
