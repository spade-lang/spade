use std::{rc::Rc, sync::RwLock};

use logos::Logos;
use spade_codespan_reporting::{files::SimpleFiles, term::termcolor::Buffer};
use spade_diagnostics::{emitter::CodespanEmitter, CodeBundle, DiagHandler};

use crate::{build_items, code_compiles, snapshot_error};

snapshot_error! {
    stage_outside_pipeline,
    "
    entity main(x: X) -> int<8> {
        reg; }
    "
}

snapshot_error! {
    register_count_is_required,
    "
    pipeline(3) main(x: X) -> int<8> {
        reg *;
    }
    "
}

snapshot_error! {
    wrong_enum_variant_items_opener,
    "
    enum foo {
        A(int: int<4>),
    }
    "
}

snapshot_error! {
    wrong_enum_variant_items_opener_but_very_wrong,
    "
    enum foo {
        B|bool|,
    }
    "
}

snapshot_error! {
    wrong_argument_list_points_to_correct_token,
    "
    entity foo(clk: clk, a: bool) -> bool {
        reg(clk) a = a;
        a
    }

    entity main(clk: clk) -> bool {
        inst foo{clk, true}
    }
    "
}

snapshot_error! {
    functions_do_not_allow_inst_entity,
    "
    entity Y() -> bool { false }

    fn X() -> bool {
        inst Y()
    }
    "
}

snapshot_error! {
    functions_do_not_allow_inst_pipeline,
    "
    pipeline(2) P() -> bool {
        reg;
            false
    }

    fn X() -> bool {
        inst(2) Y()
    }
    "
}

snapshot_error! {
    missing_pipeline_depth_parens_is_an_error,
    "pipeline a(clk: clock) -> bool {
        true
    }"
}

snapshot_error! {
    negative_tuple_index_error,
    "fn a() -> int<10> {
        x#-10
    }"
}

snapshot_error! {
    tuple_index_out_of_bounds_error,
    "fn a(b: int<2>, c: int<2>) -> int<3> {
        let tup = (b, c);
        tup.2
    }"
}

snapshot_error! {
    unexpected_token,
    "fn a() -> int<8> {
        let x : = 10;
        x
    }"
}

snapshot_error! {
    no_reg_in_function,
    "fn a(clk: clock) -> int<8> {
        reg(clk) x = 10;
        x
    }"
}

snapshot_error! {
    lexer_error_unexpected_symbol,
    "fn a() {
        let x = ¤;
    }"
}

snapshot_error! {
    empty_decl_error,
    "fn a() {
        decl;
    }"
}

#[test]
fn three_generic_end_chars_work() {
    let code = r#"
        struct A<T> {}
        struct X {
            a: A<A<A<bool>>>
        }
        "#;

    build_items(code);
}

snapshot_error! {
    missing_argument_list_for_inst_method_works,
    "entity a() -> bool {
        a.inst b
    }"
}

snapshot_error! {
    missing_pipeline_depth_error,
    "
        entity a() -> bool {
            inst() x()
        }
    "
}

snapshot_error! {
    min_max_compiles,
    "
        entity a(b: int<8>, c: int<8>, d: int<8>) -> int<8> {
            std::ops::min(c, std::ops::max(b, d))
        }
    "
}

snapshot_error! {
    order_compiles,
    "
        entity a(b: int<8>, c: int<8>) -> (int<8>, int<8>) {
            std::ops::order(b, c)
        }
    "
}

snapshot_error! {
    good_eof_error_on_missing_dot_continuation,
    "fn a() -> bool { a."
}

snapshot_error! {
    good_eof_error_on_missing_function_body,
    "fn a() -> bool"
}

snapshot_error! {
    good_eof_error_on_missing_function_body_without_type_signature,
    "fn a() -> bool"
}

snapshot_error! {
    good_error_on_unexpected_body,
    "entity a() -> bool struct"
}

snapshot_error! {
    empty_file_is_valid,
    ""
}

snapshot_error!(
    missing_expression,
    "entity a() -> int<32> {
        if 0 else {4};
    }"
);

snapshot_error!(
    missing_if_block_a,
    "entity a() -> int<32> {
        if true 5 else { 4 }
    }"
);

snapshot_error!(
    missing_if_block_b,
    "entity a() -> int<32> {
        if true { 0 } else 4
    }"
);

snapshot_error!(
    else_match,
    "entity a() -> int<32> {
        if true {
            0
        } else match 5_i16 {
            0 => 1,
            x => x,
        }
    }"
);

snapshot_error! {
    using_empty_identifier_a,
    "
    entity counter(clk: clock, rst: bool, max: int<8>) -> int<8> {
        reg(clk) value reset (rst: 0) =
            if value == max {
                0
            }
            else {
                conv::trunc(value + 1)
            };
        value
    }
    "
}

snapshot_error! {
    using_empty_identifier_b,
    "
    use conv;

    entity counter(clk: clock, rst: bool, max: int<8>) -> int<8> {
        reg(clk) value reset (rst: 0) =
            if value == max {
                0
            }
            else {
                conv::trunc(value + 1)
            };
        value
    }
    "
}

#[test]
fn square_wave_readme_example() {
    let code = r#"
    entity square_wave(clk: clock, rst: bool) -> bool {
       reg(clk) value reset (rst: false) = !value;
        value
    }
    "#;

    build_items(code);
}

#[test]
fn unit_type_is_allowed_to_be_created() {
    let code = r#"
    entity x() -> () {
        ()
    }
    "#;

    build_items(code);
}

snapshot_error! {
    unit_type_error_span_correct,
    "
    entity x() -> uint<8> {
        ()
    }
    "
}

snapshot_error! {
    negated_single_tuple_span_correct,
    "
    entity x() -> uint<8> {
        !(false)
    }
    "
}

#[test]
fn neq_operator_works() {
    let code = r#"
    fn neq(x: int<8>, y: int<8>) -> bool {
        x != y
    }
    "#;

    build_items(code);
}

snapshot_error! {
    tuple_index_points_to_the_right_thing,
    "fn test(a: (bool,)) -> bool {
        a.0.0
    }"
}

#[test]
fn inverted_port_type() {
    let code = r#"
    extern entity square_wave(clk: clock, x: inv inv & bool) -> bool;
    "#;

    build_items(code);
}

code_compiles! {
    verilog_attrs_works_on_entity_declarations,
    r#"
        #[verilog_attrs(single)]
        #[verilog_attrs(standalone, key = "val")]
        entity T() {}
    "#
}

snapshot_error! {
    wal_traceable_with_unexpected_param_is_error,
    "
        #[wal_traceable(a, uses_clk, this_is_not_valid)]
        struct T {}
    "
}

snapshot_error! {
    wal_trace_does_not_accept_duplicate_clk,
    "
        #[wal_trace(clk=x, clk=x)]
        struct T {}
    "
}
snapshot_error! {
    wal_trace_does_not_accept_bad_parameter,
    "
        #[wal_trace(clk=x, not_a_param=x)]
        struct T {}
    "
}

snapshot_error! {
    required_parameter_message_is_helpful,
    "
        fn main() -> bool {
            #[wal_suffix()]
            let x = 0;
            x
        }
    "
}

snapshot_error! {
    multiple_resets_triggers_error,
    "
    entity main() -> bool {
        reg(clk) a reset(true: 0) reset(true: 0) = true;
        true
    }"
}

snapshot_error! {
    multiple_resets_triggers_error_with_initial,
    "
    entity main() -> bool {
        reg(clk) a reset(true: 0) initial(true) reset(true: 0) = true;
        true
    }"
}

snapshot_error! {
    multiple_initial_does_not_pass_compiler,
    "
    entity main() -> bool {
        reg(clk) a reset(true: 0) initial(true) initial(true) = true;
        true
    }"
}

#[test]
fn reset_and_initial_in_either_order_is_valid() {
    let code = r#"
    entity main(clk: clock) -> bool {
        reg(clk) a reset(true: false) initial(true) = true;
        reg(clk) a initial(true) reset(true: false) = true;
        true
    }"#;

    build_items(code);
}

#[test]
fn line_comment_is_handled_correctly() {
    let code = "
        // this is my comment
        struct A {}
    ";

    build_items(code);
}

#[test]
fn line_comment_is_handled_correctly_without_newline() {
    let code = "
        struct A {}
        // this is my comment";

    build_items(code);
}

#[test]
fn block_comment_is_ignored() {
    let code = "
        /* this is an error */
    ";

    build_items(code);
}

#[test]
fn nested_block_comment_is_ignored() {
    let code = "
        /* /* */ this is an error after a block comment */
    ";

    build_items(code);
}

snapshot_error! {
    unterminated_block_comment_is_error,
    "/*/**/"
}

snapshot_error! {
    missing_end_of_range_index_is_error,
    "
        fn top() -> bool {
            let a = [true, true, false];
            a[1..]
        }
    "
}

snapshot_error! {
    incorrect_named_args_gives_good_error,
    "
        fn f(x: bool) -> bool {
            x
        }
        fn top() -> bool {
            let a = true;
            f$(x = a)
        }
    "
}

snapshot_error! {
    missing_semicolon_error_points_to_correct_token,
    "
        fn top() -> bool {
            let a = 1 let b = 2;
            true
        }
    "
}

snapshot_error! {
    multi_linemissing_semicolon_error_points_to_correct_token,
    "
        fn top() -> bool {
            let a = 1
            true
        }
    "
}

snapshot_error! {
    greek_semi_error,
    "
        fn top() -> bool {
            let a = 1;
            true
        }
    "
}

snapshot_error! {
    identifier_in_entity_instance,
    "
        entity a() -> bool {
            inst 123
        }
    "
}

snapshot_error! {
    expected_expression,
    "
        fn top() -> bool {
            let abc = ;
            abc
        }
    "
}

snapshot_error! {
    expected_expression_binop,
    "
        fn top() -> bool {
            let abc = 1+#;
            abc
        }
    "
}

snapshot_error! {
    surrounded_pipeline_depth_wrong_start,
    "
        entity top() -> bool {
            let abc = inst[1) e();
        }
    "
}

snapshot_error! {
    surrounded_pipeline_depth_wrong_end,
    "
        entity top() -> bool {
            let abc = inst(1] e();
        }
    "
}

snapshot_error! {
    surrounded_pipeline_depth_wrong_both,
    "
        entity top() -> bool {
            let abc = inst[1] e();
        }
    "
}

snapshot_error! {
    invalid_top_level_tokens_cause_errors,
    "
        + x() -> bool {
            false
        }

        entity x() -> bool {
            false
        }
    "
}

snapshot_error! {
    tuple_index_no_integer,
    "fn a(y: int<1>) -> int<32> {
        let t = (3, 5);
        t#y
    }"
}

snapshot_error! {
    pipeline_stage_ref_in_entity,
    "
        entity top(clk: clock) -> bool {
            decl x;
            stage(+1).x
        }
    "
}

snapshot_error! {
    pipeline_stage_ref_in_function,
    "
        fn top() -> bool {
            decl x;
            stage(+1).x
        }
    "
}

snapshot_error! {
    stage_ready_or_valid,
    "
        pipeline(0) top() -> bool{
            stage.ident
        }
    "
}

#[test]
fn generic_trait_is_valid() {
    let code = r#"
        trait X<T> {}
    "#;

    build_items(code);
}

#[test]
fn generic_trait2_is_valid() {
    let code = r#"
        trait X<T, U> {}
    "#;

    build_items(code);
}

#[test]
fn generic_impl_is_valid() {
    let code = r#"
        struct S<T> {}
        impl <T> S<T> {}
    "#;

    build_items(code);
}

#[test]
fn generic_trait_impl_is_valid() {
    let code = r#"
        trait X<T> {}
        struct S<T> {}
        impl <T> X<T> for S<T> {}
    "#;

    build_items(code);
}

#[test]
fn generic_param_on_trait_is_valid() {
    let code = r#"
        trait X<T> {}
        struct S {}
        impl X<bool> for S {}
    "#;

    build_items(code);
}

#[test]
fn generic_param_on_trait_and_struct_is_valid() {
    let code = r#"
        trait X<T> {}
        struct S<T> {}
        impl X<S<int<8>>> for S<int<8>> {}
    "#;

    build_items(code);
}

#[test]
fn generic_param_on_struct_is_valid() {
    let code = r#"
        trait X {}
        struct S<T> {}
        impl X for S<int<8>> {}
    "#;

    build_items(code);
}

#[test]
fn where_clause_on_unit_is_valid() {
    let code = r#"
        trait S {}
        fn foo<T>() -> bool where T: S {
            true
        }
        "#;

    build_items(code);
}

#[test]
fn where_clause_on_trait_is_valid() {
    let code = r#"
        trait S {}
        trait T<X> where X: S {}
        "#;

    build_items(code);
}

#[test]
fn where_clause_on_impl_block_is_valid() {
    let code = r#"
        trait S<T> {}
        struct X {}
        impl<T> S<T> for X
            where T: S<bool> {}
        "#;

    build_items(code);
}

snapshot_error! {
    method_turbofish_without_argument_list,
    "
        fn test() {
            a.field::<bool>
        }
    "
}

snapshot_error! {
    inst_method_turbofish_without_argument_list,
    "
        entity test() {
            a.inst field::<bool>
        }
    "
}

snapshot_error! {
    method_with_partial_turbofish,
    "
        fn test() {
            a.field::
        }
    "
}

#[test]
fn array_shorthand_literal_syntax_parses() {
    let code = r#"
        fn top() -> bool {
            let _: [int<2>; 2] = [1; 2];
            let _: [uint<8>; 4] = [0xff; 4];
            let _: [uint<10>; 25] = [5u10; 25];
            true
        }
    "#;
    build_items(code);
}

snapshot_error! {
    array_shorthand_ident_length,
    "
        fn test() {
            let length: uint<8> = 24;
            let _: [uint<2>; 1] = [1u2; length];
        }
    "
}

snapshot_error! {
    array_shorthand_missing_length,
    "
        fn test() {
            let length = 24;
            let _ = [1u2;];
        }
    "
}

snapshot_error! {
    negative_unsigned_integer_literal,
    "
        fn test() {
            let _ = -5u4;
        }
    "
}

snapshot_error! {
    errors_in_statements_are_recoverable,
    "
        fn test() {
            let x = ;
            let y ;
            set z = &true;
        }
    "
}

snapshot_error! {
    errors_in_items_are_recoverable,
    "entity main() {
        not valid syntax
    }

    struct X {
        bool
    }

    enum Y {
        Variant(a)
    }
    "
}

snapshot_error! {
    item_contexts_are_cleared_on_error_recovery,
    "
    use std::ports;

    entity test() {}

    entity int32_to_float32(input: int<32>) -> uint<32> {
        test()
        test()
    }

    entity top(input: int<32>) -> uint<32> {}

    "
}

#[test]
fn where_clause_on_extern_is_valid() {
    let code = r#"
    extern entity foo<#uint N, #uint M>() where N: {M};
    "#;

    build_items(code);
}

snapshot_error! {
    extern_unit_cannot_have_body,
    "
    extern entity foo() {}
    "
}

snapshot_error! {
    non_extern_unit_must_have_body,
    "
    entity foo();
    "
}

snapshot_error! {
    unit_must_not_just_be_head,
    "
    entity foo()
    "
}

snapshot_error! {
    extern_unit_must_end_with_semicolon,
    "
    extern entity foo()
    "
}

snapshot_error! {
    module_outside_doc_comment_hint,
    "
    /// This is my module :3
    mod x {}
    "
}

code_compiles! {
    single_element_tuple_is_describable,
    "
        fn test() -> (bool,) {
            (true,)
        }
    "
}

code_compiles! {
    zero_element_tuple_can_have_comma,
    "
        fn test() -> (,) {
            (,)
        }
    "
}

snapshot_error! {
    error_recovery_on_unit_keyword_is_ok,
    "
        fn not a valid fn() {
            unsafe abc
        }
    "
}

snapshot_error! {
    lambda_accepts_expression_body,
    "
        fn test() {
            let _ = fn || false;
        }
    "
}

snapshot_error! {
    entity_methods_are_not_allowed_in_functions,
    "struct X{}
    impl X {
        entity e(self) {}
    }
    fn test() {
        X().inst e()
    }
    "
}

#[test]
fn parser_extracts_comments() {
    const FILE_ID: usize = 0;

    let code = "
// a simple test


// more simple test


/* basic block comment */

/* nested /* block */ comment */

fn test() {
    let a = 4; // comment inside
    let b = /* comment also inside */ 5;
}
";

    let mut files = SimpleFiles::new();
    files.add("test".into(), code.into());

    let diagnostic_handler = DiagHandler::new(Box::new(CodespanEmitter));

    let code_bundle = Rc::new(RwLock::new(CodeBundle { files }));

    let mut buffer = Buffer::no_color();

    let mut error_handler = spade::error_handling::ErrorHandler::new(
        &mut buffer,
        diagnostic_handler,
        code_bundle.clone(),
    );

    let mut parser =
        spade_parser::Parser::new(spade_parser::lexer::TokenKind::lexer(&code), FILE_ID);

    let _ = match parser.top_level_module_body() {
        Ok(root) => root,
        Err(error) => {
            error_handler.report(&error);
            for error in &parser.diags.errors {
                error_handler.report(error);
            }
            panic!("Exiting due to errors")
        }
    };

    insta::assert_debug_snapshot!(parser.comments());
}

snapshot_error! {
    ascii_char_literal_errors,
    "
        fn test() {
            let x = 'a';
            let y = b'\\a';
            let z = b'abc';
            let w = b'ö';
            let z = b'\\'';
        }
    "
}

code_compiles! {
    ascii_char_literals_in_patterns,
    "
        fn test(x: uint<8>) -> uint<5> {
            match x {
                b'a' => {0},
                _ => {0}
            }
        }
    "
}
