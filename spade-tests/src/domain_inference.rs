use crate::{build_items, build_items_with_stdlib, code_compiles, snapshot_error};

snapshot_error!{
    mixing_two_domains_with_tuples,
    "entity test<'a, 'b>(a: 'a bool, b: 'b bool) -> (bool, bool) {
        (a, b)
    }",
    false
}

snapshot_error! {
    domains_propagate_through_expressions,
    "entity test<'a, 'b>(a: 'a bool, b: 'b bool) -> (bool, bool) {
        let c = (a, a);
        (c#0, b)
    }",
    false
}

