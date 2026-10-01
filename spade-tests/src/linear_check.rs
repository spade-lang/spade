use crate::{build_items, snapshot_error};

snapshot_error! {
    double_consumption_of_identifier_produces_error,
    "
    entity x(resource: inv bool) -> (inv bool, inv bool) {
        (resource, resource)
    }
    ",
    false
}

snapshot_error! {
    double_consumption_of_identifier_produces_error_in_array,
    "
    entity x(resource: inv bool) -> [inv bool; 2] {
        [resource, resource]
    }
    "
}

snapshot_error! {
    double_consumption_of_identifier_in_pipeline_produces_error,
    "
    pipeline(0) x(clk: clock, wire resource: inv bool) -> (inv bool, inv bool) {
        (resource, resource)
    }
    "
}

snapshot_error! {
    unused_resource_causes_error,
    "
    entity x(resource: inv bool) -> bool {
        true
    }
    "
}

snapshot_error! {
    unused_field_causes_error,
    "
    struct A {
        x: inv bool,
        y: bool
    }
    entity x(resource: A) -> bool {
        true
    }
    "
}

snapshot_error! {
    unused_transitive_field_causes_error,
    "
    struct A {
        x: inv bool,
        y: bool
    }
    struct B {
        a: A
    }
    entity x(resource: B) -> bool {
        true
    }
    "
}

snapshot_error! {
    unused_tuple_member_causes_error,
    "
    entity x(resource: (inv bool, bool)) -> bool {
        true
    }
    "
}

snapshot_error! {
    unused_transitive_tuple_member_causes_error,
    "
    entity x(resource: ((inv  bool, bool), bool)) -> bool {
        true
    }
    "
}

snapshot_error! {
    unused_anonymous_expression_is_reported,
    "
    extern entity producer() -> (inv bool, inv bool);
    extern entity consumer(x: inv bool) -> bool;

    entity x() -> bool {
        inst consumer(inst producer().0)
    }
    "
}

snapshot_error! {
    double_tuple_consumption_causes_error,
    "
    entity x(resource: (inv bool, bool)) -> (inv bool, inv bool) {
        (resource.0, resource.0)
    }
    "
}

snapshot_error! {
    more_than_one_field_consumption_causes_error,
    "
    struct A {
        x: inv bool,
    }
    entity x(a: A) -> (inv bool, inv bool) {
        (a.x, a.x)
    }
    "
}

snapshot_error! {
    consuming_a_field_produces_an_error_when_consuming_whole_struct,
    "
    struct A {
        x: inv bool,
    }

    extern entity consumer(a: inv bool) -> bool;

    entity x(a: A) -> A {
        let _ = inst consumer(a.x);
        a
    }
    "
}

snapshot_error! {
    destructuring_linear_type_requires_use_of_subtypes,
    "
    entity x(a: (inv bool, inv bool)) -> inv bool {
        let (x, y) = a;
        x
    }
    "
}

snapshot_error! {
    using_a_single_linear_field_does_not_use_the_whole_struct,
    "
    struct A {
        a: inv bool,
        b: inv bool,
    }
    entity x(a: A) -> inv bool {
        a.a
    }
    "
}

#[test]
fn linear_checking_on_registers_works() {
    let code = "
    entity test(clk: clock) -> int<8> {
        reg(clk) x = x;
        x
    }
    ";
    build_items(code);
}

snapshot_error! {
    checking_works_with_decld_value,
    "
    extern entity consume(p: inv bool) -> bool;

    entity test() -> bool {
        decl x;
        let _ = inst consume(x);
        let x = port().1;
        let _ = inst consume(x);
        true
    }
    "
}

snapshot_error! {
    function_calls_consume_ports,
    "
        extern entity consumer(x: inv bool) -> bool;

        entity test() -> (bool, bool) {
            let p = port().1;
            (inst consumer(p), inst consumer(p))
        }
    "
}

#[test]
fn set_statement_consumes_port() {
    let code = "
        entity e(p: inv bool) -> bool {
            set p = false;
            false
        }";

    build_items(code);
}

snapshot_error! {
    array_indexing_does_not_use_whole_array,
    "
        entity test() {
            let a = [port().1, port().1];
            set a[0] = 0u8;
        }
    "
}

snapshot_error! {
    double_use_of_linear_array_is_wrong,
    "
        entity test() {
            let a = [port().1, port().1];
            set a[0] = 0u8;
            set a[0] = 0u8;
            set a[1] = 0;
        }
    "
}

snapshot_error! {
    array_index_linear_type_with_non_const_is_error,
    "
        entity test() {
            let idx = 0;
            let a = [port().1, port().1];
            set a[idx] = 0u8;
        }
    "
}

snapshot_error! {
    array_shorthand_uses_mut_wire,
    "
        entity e(p: inv bool) {
            let many_p = [p; 3];
        }
    "
}

snapshot_error! {
    inv_from_pattern_binding_lhs_cannot_be_used,
    "
        entity e(p: inv bool) {
            let q @ r = p;
            set q = false;
        }
    "
}

snapshot_error! {
    inv_from_pattern_binding_rhs_cannot_be_used,
    "
        entity e(p: inv bool) {
            let q @ r = p;
            set r = false;
        }
    "
}

snapshot_error! {
    match_consumes_input,
    "
        fn e(p: (uint<1>, inv bool)) {
            let _ = match p {
                (0, pi) => {
                    set pi = false;
                    false
                },
                (1, pi) => {
                    set pi = true;
                    true
                },
            };

            set p.1 = false;
        }
    "
}
