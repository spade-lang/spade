use crate::{build_items, build_items_with_stdlib, code_compiles, snapshot_error};

snapshot_error! {
    return_type_domains_cannot_mismatch,
    "
        fn test<'a, 'b>(a: 'a bool)  -> 'b bool {
            a
        }
    ",
    false
}

code_compiles! {
    uniform_tuples_are_in_the_inner_domain,
    "
        fn test<'a>(a: 'a bool, b: 'a bool)  -> 'a (bool, bool) {
            (a, b)
        }
    "
}

snapshot_error! {
    uniform_tuples_are_not_in_another_domain,
    "
        fn test<'a, 'b>(a: 'a bool, b: 'a bool)  -> 'b (bool, bool) {
            (a, b)
        }
    ",
    false
}

snapshot_error! {
    nonuniform_tuples_are_not_in_the_inner_domain,
    "
        fn test<'a, 'b>(a: 'a bool, b: 'b bool)  -> 'a (bool, bool) {
            (a, b)
        }
    ",
    false
}

code_compiles! {
    literals_decay_into_outer,
    "
        fn test<'a>() -> 'a bool {
            true
        }
    "
}

code_compiles! {
    tuples_with_literals_decay,
    "
        fn test<'a>(a: 'a bool) -> 'a (bool, bool) {
            (a, false)
        }
    "
}

snapshot_error! {
    mixed_domain_array_literal_is_error,
    "
        fn test<'a, 'b>(a: 'a bool, b: 'b bool) -> 'a [bool; 2] {
            [a, b]
        }
    ",
    false
}

code_compiles! {
    mixed_const_domain_array_literal_is_accepted,
    "
        fn test<'a>(a: 'a bool) -> 'a [bool; 2] {
            [a, false]
        }
    "
}

code_compiles! {
    set_works_on_same_domain,
    "
        fn test<'a>(a: 'a bool, b: 'a inv &bool) {
            set b = &a;
        }
    "
}

snapshot_error! {
    set_cannot_mix_unrelated_domains,
    "
        fn test<'a, 'b>(a: 'a bool, b: 'b inv &bool) {
            set b = &a;
        }
    ",
    false
}

code_compiles! {
    set_const_is_allowed,
    "
        fn test<'a>(a: 'a inv &bool) {
            set a = &false;
        }
    "
}

snapshot_error! {
    set_cannot_set_specific_to_async,
    "
        fn test<'a>(a: 'async bool, b: 'a inv &bool) {
            set b = &a;
        }
    ",
    false
}

code_compiles! {
    set_can_set_async_to_specific,
    "
        fn test<'a>(a: 'a bool, b: 'async inv &bool) {
            set b = &a;
        }
    "
}

snapshot_error! {
    const_domain_cannot_be_set_with_named,
    "
        fn test<'a>(a: 'a bool, b: 'const inv &bool) {
            set b = &a;
        }
    ",
    false
}

code_compiles! {
    const_domain_can_be_set_from_const,
    "
        fn test(a: 'const bool, b: 'const inv &bool) {
            set b = &a;
        }
    "
}

snapshot_error! {
    registers_need_a_clock,
    "
        entity test(clk: clock, a: 'async bool) {
            reg(clk) x = a;
        }
    ",
    false
}

snapshot_error! {
    mixed_signals_cannot_be_put_in_a_register,
    "
        entity test<'a, 'b>(clk: clock, a: 'a bool, b: 'b bool) {
            reg(clk) x = (a, b);
        }
    ",
    false
}


snapshot_error! {
    recursive_mixed_signals_cannot_be_put_in_a_register,
    "
        entity test<'a, 'b>(clk: clock, a: 'a bool, b: 'b bool) {
            reg(clk) x = (true, (a, b));
        }
    ",
    false
}

code_compiles! {
    const_and_known_can_be_stored_in_register,
    "
        entity test<'a>(clk: 'a clock, a: 'a bool) {
            reg(clk) x = (a, false);
        }
    "
}

snapshot_error! {
    explicit_reg_clock_must_be_in_same_domain_as_value,
    "
        entity test<'a, 'b>(clk: 'a clock, b: 'b bool) {
            reg(clk) x = b;
        }
    ",
    false
}

snapshot_error! {
    register_output_domain_must_be_same_as_input,
    "
        entity test<'a, 'b>(clk: 'a clock, b: 'a bool) -> 'b bool {
            reg(clk) x = b;
            b
        }
    ",
    false
}

snapshot_error! {
    explicit_reg_reset_value_must_be_same_as_value,
    "
        entity test<'a, 'b>(clk: 'a clock, rst_val: 'b bool, b: 'a bool) {
            reg(clk) x reset(false: rst_val) = b;
        }
    ",
    false
}

snapshot_error! {
    explicit_reg_reset_trigger_must_be_same_as_value,
    "
        entity test<'a, 'b>(clk: 'a clock, rst: 'b bool, b: 'a bool) {
            reg(clk) x reset(rst: false) = b;
        }
    ",
    false
}

code_compiles! {
    tuple_destructuring_preserves_domains,
    "
        entity test<'a, 'b>(a: 'a bool, b: 'b bool) -> ('a bool, 'b bool) {
            let (x, y) = (a, b);
            (x, y)
        }
    "
}

code_compiles! {
    array_of_tuples_with_mixed_domains_is_ok,
    "
        entity test<'a, 'b>(a: 'a bool, b: 'b bool) -> ('a bool, 'b bool) {
            let [a, b] = [(a, b), (a, b)];
            a
        }
    "
}

snapshot_error! {
    pipeline_stage_ref_carries_domain_info,
    "
    pipeline(1) test<'a, 'b>(clk: clock, x: 'a bool) -> 'b bool {
        reg;
            stage(-1).x
    }
    ",
    false
}

snapshot_error! {
    tuple_indexing_inherits_non_tuple_domains,
    "
        entity test<'a, 'b>(tup: 'a (bool, bool)) -> 'b bool {
            tup#0
        }
    ",
    false
}

snapshot_error! {
    tuple_indexing_retains_tuple_domains,
    "
        entity test<'a, 'b>(tup: ('a bool, 'b bool)) -> 'b bool {
            tup#0
        }
    ",
    false
}


// snapshot_error! {
//     parameter_implicit_domain_is_disallowed_with_explicit_domains,
//     "
//         entity test<'a>(a: bool) {}
//     ",
//     false
// }

// snapshot_error! {
//     output_implicit_domain_is_disallowed_with_explicit_domains,
//     "
//         entity test<'a>() -> bool {true}
//     ",
//     false
// }

// snapshot_error! {
//     mixing_two_domains_with_tuples,
//     "entity test<'a, 'b>(a: 'a bool, b: 'b bool) -> 'a (bool, bool) {
//         (a, b)
//     }",
//     false
// }

// snapshot_error! {
//     domains_propagate_through_expressions,
//     "entity test<'a, 'b>(a: 'a bool, b: 'b bool) -> 'a ((bool, bool), bool) {
//         ((a, a), b)
//     }",
//     false
// }

// snapshot_error! {
//     domains_propagate_through_identifiers,
//     "entity test<'a, 'b>(a: 'a bool, b: 'b bool) -> 'a ((bool, bool), bool) {
//         let c = (a, a);
//         (c, b)
//     }",
//     false
// }

// snapshot_error! {
//     domains_propagate_through_pipeline_refs,
//     "pipeline(1) test<'a, 'b>(clk: 'a clock, a: 'a bool, b: 'b bool) -> 'a ((bool, bool), bool) {
//         let c = (a, a);
//     reg;
//         (stage(+0).c, b)
//     }",
//     false
// }

// snapshot_error! {
//     arrays_require_same_domain,
//     "entity test<'a, 'b>(a: 'a bool, b: 'b bool) -> 'a [bool; 2] {
//         [a, b]
//     }",
//     false
// }

// snapshot_error! {
//     array_shorthand_literals_are_in_the_operand_domain,
//     "entity test<'a, 'b>(a: 'a bool) -> 'b [bool; 1] {
//         [a; 1]
//     }",
//     false
// }

// snapshot_error! {
//     index_expression_mixing_domains,
//     "entity test<'a, 'b>(a: 'a [bool; 2]) -> 'b bool {
//         a[0]
//     }",
//     false
// }

// snapshot_error! {
//     range_index_expression_mixing_domains,
//     "entity test<'a, 'b>(a: 'a [bool; 2]) -> 'b [bool; 1] {
//         a[0..1]
//     }",
//     false
// }

// snapshot_error! {
//     tuple_index_expression_mixing_domains,
//     "entity test<'a, 'b>(a: 'a (bool, bool)) -> 'b bool {
//         a#0
//     }",
//     false
// }

// snapshot_error! {
//     unary_operator_expression_mixing_domains,
//     "entity test<'a, 'b>(a: 'a bool) -> 'b bool {
//         !a
//     }",
//     false
// }

// snapshot_error! {
//     field_access_expression_mixing_domains,
//     "struct T {
//         x: bool
//     }

//     entity test<'a, 'b>(a: 'a T) -> 'b bool {
//         a.x
//     }",
//     false
// }

// snapshot_error! {
//     binary_operator_expression_mixing_domains,
//     "entity test<'a, 'b>(a: 'a bool, b: 'b bool) -> 'b bool {
//         a && b
//     }",
//     false
// }

// snapshot_error! {
//     match_expression_mixing_condition_domains,
//     "entity test<'a, 'b>(a: 'a bool) -> 'b bool {
//         match a {
//             true => true,
//             false => false,
//         }
//     }",
//     false
// }
// snapshot_error! {
//     match_expression_mixing_true_branch_domains,
//     "entity test<'a, 'b>(a: 'a bool) -> 'b bool {
//         match true {
//             true => a,
//             false => false,
//         }
//     }",
//     false
// }

// snapshot_error! {
//     match_expression_mixing_false_branch_domains,
//     "entity test<'a, 'b>(a: 'a bool) -> 'b bool {
//         match true {
//             true => true,
//             false => a,
//         }
//     }",
//     false
// }

// snapshot_error! {
//     match_bindings_do_not_allow_mixing_domains,
//     "entity test<'a, 'b>(a: 'a bool, b: 'b bool) -> 'b bool {
//         match a {
//             a => a && b,
//             false => a,
//         }
//     }",
//     false
// }

// snapshot_error! {
//     if_expression_mixing_condition_domains,
//     "entity test<'a, 'b>(a: 'a bool) -> 'b bool {
//         if a {
//             true
//         } else {
//             false
//         }
//     }",
//     false
// }

// snapshot_error! {
//     if_expression_mixing_true_branch_domains,
//     "entity test<'a, 'b>(a: 'a bool) -> 'b bool {
//         if true {
//             a
//         } else {
//             false
//         }
//     }",
//     false
// }

// snapshot_error! {
//     if_expression_mixing_false_branch_domains,
//     "entity test<'a, 'b>(a: 'a bool) -> 'b bool {
//         if true {
//             true
//         } else {
//             a
//         }
//     }",
//     false
// }

// snapshot_error! {
//     domain_crossing_is_required_for_noclock_to_registers,
//     "
//         entity test<'a: NoClock>(clk: 'a clock, a: 'a bool) {
//             reg(clk) r = a;
//         }
//     ",
//     false
// }

// snapshot_error! {
//     register_clock_must_match,
//     "
//         entity test<'a: NoClock, 'b>(clk: 'a clock, a: 'b bool) {
//             reg(clk) r = a;
//         }
//     ",
//     false
// }

// snapshot_error! {
//     declarations_work_with_domains,
//     "
//     entity test<'a, 'b>(a: 'a bool, b: 'b bool) {
//         decl c;
//         let x = (c, b);
//         let c = (a, a);
//     }
//     ",
//     false
// }

// snapshot_error! {
//     set_statements_enforce_domains,
//     "
//         entity test<'a, 'b>(a: 'a &bool, b: 'b inv &bool) {
//             set b = a;
//         }
//     ",
//     false
// }

// snapshot_error! {
//     tlif_true_branch_checks_domains,
//     "
//         entity test<'a, 'b>(a: 'a bool) -> 'b bool {
//             gen if 1==1 {
//                 a
//             } else {
//                 true
//             }
//         }
//     ",
//     false
// }

// snapshot_error! {
//     tlif_false_branch_checks_domains,
//     "
//         entity test<'a, 'b>(a: 'a bool) -> 'b bool {
//             gen if 1 == 0 {
//                 true
//             } else {
//                 a
//             }
//         }
//     ",
//     false
// }

// snapshot_error! {
//     call_output_must_be_in_the_right_domain,
//     "
//         fn func(a: bool) -> bool {true}

//         fn test<'a, 'b>(a: 'a bool) -> 'b bool {
//             func(a)
//         }
//     ",
//     false
// }

// snapshot_error! {
//     entity_domain_constraints_propagate,
//     "
//         entity func<'a: HasClock>(a: 'a bool) -> 'a bool {true}

//         entity test<'a: NoClock>(a: 'a bool) -> 'a bool {
//             inst func(a)
//         }
//     ",
//     false
// }

// snapshot_error! {
//     pipeline_domains_need_clocks,
//     "
//         pipeline(1) test<'a: NoClock>(clk: 'a clock) {
//             reg;
//         }
//     ",
//     false
// }

// snapshot_error! {
//     stage_ready_is_in_the_pipeline_domain,
//     "
//         pipeline(1) test<'a, 'b>(clk: 'a clock, other: 'b bool) -> 'b bool {
//             reg;
//             stage.ready && other
//         }
//     ",
//     false
// }

// snapshot_error! {
//     stage_valid_is_in_the_pipeline_domain,
//     "
//         pipeline(1) test<'a, 'b>(clk: 'a clock, other: 'b bool) -> 'b bool {
//             reg;
//             stage.valid && other
//         }
//     ",
//     false
// }

// // TODO: Things left to test
// // unsafe allows domain crossing
// // stage.ready, stage.valid
// // Constraints on the annonymous domain
// // Allow implicit propagation of constraints?
