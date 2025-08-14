use crate::{build_items, build_items_with_stdlib, code_compiles, snapshot_error};

snapshot_error! {
    parameter_implicit_domain_is_disallowed_with_explicit_domains,
    "
        entity test<'a>(a: bool) {}
    ",
    false
}

snapshot_error! {
    output_implicit_domain_is_disallowed_with_explicit_domains,
    "
        entity test<'a>() -> bool {true}
    ",
    false
}

snapshot_error! {
    mixing_two_domains_with_tuples,
    "entity test<'a, 'b>(a: 'a bool, b: 'b bool) -> 'a (bool, bool) {
        (a, b)
    }",
    false
}

snapshot_error! {
    domains_propagate_through_expressions,
    "entity test<'a, 'b>(a: 'a bool, b: 'b bool) -> 'a ((bool, bool), bool) {
        ((a, a), b)
    }",
    false
}

snapshot_error! {
    domains_propagate_through_identifiers,
    "entity test<'a, 'b>(a: 'a bool, b: 'b bool) -> 'a ((bool, bool), bool) {
        let c = (a, a);
        (c, b)
    }",
    false
}

snapshot_error! {
    domains_propagate_through_pipeline_refs,
    "pipeline(1) test<'a, 'b>(clk: 'a clock, a: 'a bool, b: 'b bool) -> 'a ((bool, bool), bool) {
        let c = (a, a);
    reg;
        (stage(+0).c, b)
    }",
    false
}

snapshot_error! {
    arrays_require_same_domain,
    "entity test<'a, 'b>(a: 'a bool, b: 'b bool) -> 'a [bool; 2] {
        [a, b]
    }",
    false
}

snapshot_error! {
    array_shorthand_literals_are_in_the_operand_domain,
    "entity test<'a, 'b>(a: 'a bool) -> 'b [bool; 1] {
        [a; 1]
    }",
    false
}

snapshot_error! {
    index_expression_mixing_domains,
    "entity test<'a, 'b>(a: 'a [bool; 2]) -> 'b bool {
        a[0]
    }",
    false
}

snapshot_error! {
    range_index_expression_mixing_domains,
    "entity test<'a, 'b>(a: 'a [bool; 2]) -> 'b [bool; 1] {
        a[0..1]
    }",
    false
}

snapshot_error! {
    tuple_index_expression_mixing_domains,
    "entity test<'a, 'b>(a: 'a (bool, bool)) -> 'b bool {
        a#0
    }",
    false
}

snapshot_error! {
    unary_operator_expression_mixing_domains,
    "entity test<'a, 'b>(a: 'a bool) -> 'b bool {
        !a
    }",
    false
}

snapshot_error! {
    field_access_expression_mixing_domains,
    "struct T {
        x: bool
    }

    entity test<'a, 'b>(a: 'a T) -> 'b bool {
        a.x
    }",
    false
}

snapshot_error! {
    binary_operator_expression_mixing_domains,
    "entity test<'a, 'b>(a: 'a bool, b: 'b bool) -> 'b bool {
        a && b
    }",
    false
}

snapshot_error! {
    match_expression_mixing_condition_domains,
    "entity test<'a, 'b>(a: 'a bool) -> 'b bool {
        match a {
            true => true,
            false => false,
        }
    }",
    false
}
snapshot_error! {
    match_expression_mixing_true_branch_domains,
    "entity test<'a, 'b>(a: 'a bool) -> 'b bool {
        match true {
            true => a,
            false => false,
        }
    }",
    false
}

snapshot_error! {
    match_expression_mixing_false_branch_domains,
    "entity test<'a, 'b>(a: 'a bool) -> 'b bool {
        match true {
            true => true,
            false => a,
        }
    }",
    false
}

snapshot_error! {
    match_bindings_do_not_allow_mixing_domains,
    "entity test<'a, 'b>(a: 'a bool, b: 'b bool) -> 'b bool {
        match a {
            a => a && b,
            false => a,
        }
    }",
    false
}

snapshot_error! {
    if_expression_mixing_condition_domains,
    "entity test<'a, 'b>(a: 'a bool) -> 'b bool {
        if a {
            true
        } else {
            false
        }
    }",
    false
}

snapshot_error! {
    if_expression_mixing_true_branch_domains,
    "entity test<'a, 'b>(a: 'a bool) -> 'b bool {
        if true {
            a
        } else {
            false
        }
    }",
    false
}

snapshot_error! {
    if_expression_mixing_false_branch_domains,
    "entity test<'a, 'b>(a: 'a bool) -> 'b bool {
        if true {
            true
        } else {
            a
        }
    }",
    false
}

