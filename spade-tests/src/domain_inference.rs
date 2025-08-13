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

snapshot_error!{
    mixing_two_domains_with_tuples,
    "entity test<'a, 'b>(a: 'a bool, b: 'b bool) -> 'a (bool, bool) {
        (a, b)
    }",
    false
}

snapshot_error! {
    domains_propagate_through_expressions,
    "entity test<'a, 'b>(a: 'a bool, b: 'b bool) -> 'a (bool, bool) {
        let c = (a, a);
        (c#0, b)
    }",
    false
}

