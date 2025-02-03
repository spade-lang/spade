use crate::tests::{init_with_file, InitFileOpt};

#[tokio::test]
async fn let_binding() {
    init_with_file(
        r#"
        fn top() -> int<2> {
            let a = 1;
            //  ^[2] goto-target
            a
        //  ^[1] goto
        }
    "#,
        InitFileOpt::default(),
        None,
        None,
        "",
    )
    .await;
}

#[tokio::test]
async fn let_binding_multiple() {
    init_with_file(
        r#"
        fn top() -> int<2> {
            let a = 1;
            let a = a;
            //  ^[2] goto-target
            a
        //  ^[1] goto
        }
    "#,
        InitFileOpt::default(),
        None,
        None,
        "",
    )
    .await;
}

#[tokio::test]
async fn reg_binding() {
    init_with_file(
        r#"
        entity top(clk: clock) -> int<2> {
            reg(clk) a = 1;
            //       ^[2] goto-target
            a
        //  ^[1] goto
        }
    "#,
        InitFileOpt::default(),
        None,
        None,
        "",
    )
    .await;
}

#[tokio::test]
async fn reg_clock() {
    init_with_file(
        r#"
        entity top(clk: clock) -> int<2> {
            //     ^^^[2] goto-target
            reg(clk) a = 1;
            //  ^[1] goto
            a
        }
    "#,
        InitFileOpt::default(),
        None,
        None,
        "",
    )
    .await;
}

#[tokio::test]
async fn let_binding_tuple_first() {
    init_with_file(
        r#"
        fn top() -> int<2> {
            let (a, b) = (1, 2);
            //   ^[2] goto-target
            a
        //  ^[1] goto
        }
    "#,
        InitFileOpt::default(),
        None,
        None,
        "",
    )
    .await;
}

#[tokio::test]
async fn let_binding_tuple_second() {
    init_with_file(
        r#"
        fn top() -> int<2> {
            let (a, b) = (1, 2);
            //      ^[2] goto-target
            b
        //  ^[1] goto
        }
    "#,
        InitFileOpt::default(),
        None,
        None,
        "",
    )
    .await;
}

#[tokio::test]
async fn parameter() {
    init_with_file(
        r#"
        fn top(a: int<2>) -> int<2> {
            // ^[2] goto-target
            a
        //  ^[1] goto
        }
    "#,
        InitFileOpt::default(),
        None,
        None,
        "",
    )
    .await;
}

#[tokio::test]
async fn struct_declaration() {
    init_with_file(
        r#"
        struct S { a: int<2> }
    //  ^^^^^^^^^^^^^^^^^^^^^^[2] goto-target
        fn top() -> int<2> {
            let s = S$(a: 1);
            //      ^[1] goto
            s.a
        }
    "#,
        InitFileOpt::default(),
        None,
        None,
        "",
    )
    .await;
}

#[tokio::test]
async fn struct_field_from_usage() {
    init_with_file(
        r#"
        struct S { a: int<2> }
        //         ^[2] goto-target
        fn top() -> int<2> {
            let s = S$(a: 1);
            s.a
        //    ^[1] goto
        }
    "#,
        InitFileOpt::default(),
        None,
        None,
        "",
    )
    .await;
}

#[tokio::test]
async fn enum_match_pattern_usage() {
    init_with_file(
        r#"
        enum E {
          A { a: int<2> },
          B { b: int<2> },
        }

        fn top(e: E) -> int<2> {
          match e {
            E::A$(a) =>
          //      ^[2] goto-target
              a,
          //  ^[1] goto
            E::B$(b) => b,
          }
        }
    "#,
        InitFileOpt::default(),
        None,
        None,
        "",
    )
    .await;
}

#[tokio::test]
async fn enum_match_pattern_variant() {
    init_with_file(
        r#"
        enum E {
          A { a: int<2> },
      //  ^[2] goto-target
          B { b: int<2> },
        }

        fn top(e: E) -> int<2> {
          match e {
            E::A$(a) => a,
          //   ^[1] goto
            E::B$(b) => b,
          }
        }
    "#,
        InitFileOpt::default(),
        None,
        None,
        "",
    )
    .await;
}

#[tokio::test]
async fn fn_def_from_if_in_result() {
    init_with_file(
        r#"
        fn foo() -> int<2> { 0 }
    //  ^^^^^^^^^^^^^^^^^^^^^^^^[2] goto-target

        entity top(arg: int<2>) -> int<2> {
            if arg > 1 {
                foo()
           //   ^[1] goto
            }
            else {
                2
            }
        }
    "#,
        InitFileOpt::default(),
        None,
        None,
        "",
    )
    .await;
}

#[tokio::test]
async fn fn_def_from_if_in_binding() {
    init_with_file(
        r#"
        fn foo() -> int<2> { 0 }
    //  ^^^^^^^^^^^^^^^^^^^^^^^^[2] goto-target

        entity top(arg: int<2>) -> int<2> {
            let val = if arg > 1 {
                foo()
           //   ^[1] goto
            }
            else {
                2
            };
            0
        }
    "#,
        InitFileOpt::default(),
        None,
        None,
        "",
    )
    .await;
}

#[tokio::test]
async fn fn_def_from_else_in_result() {
    init_with_file(
        r#"
        fn foo() -> int<2> { 0 }
    //  ^^^^^^^^^^^^^^^^^^^^^^^^[2] goto-target

        entity top(arg: int<2>) -> int<2> {
            let val = if arg > 1 {
                2
            }
            else {
                foo()
           //   ^[1] goto
            };
            0
        }
    "#,
        InitFileOpt::default(),
        None,
        None,
        "",
    )
    .await;
}

#[tokio::test]
async fn fn_def_from_else_in_binding() {
    init_with_file(
        r#"
        fn foo() -> int<2> { 0 }
    //  ^^^^^^^^^^^^^^^^^^^^^^^^[2] goto-target

        entity top(arg: int<2>) -> int<2> {
            let val = if arg > 1 {
                0
            }
            else {
                foo()
           //   ^[1] goto
            };
            0
        }
    "#,
        InitFileOpt::default(),
        None,
        None,
        "",
    )
    .await;
}

#[tokio::test]
async fn hairy_nested_fn_call() {
    init_with_file(
        r#"
            fn rec(arg: int<8>) -> int<8> { 4 }
        //  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^[2] goto-target

            fn rec_call() -> int<8> {
                rec(1 ^ rec( 1 & rec( 5 | rec( 3 & rec( 3 % rec( 1 / rec( 2 ^rec(5 & rec(1 ^ rec(1*1*1*1*rec((1 + 2 * 1 - 1))))))))))))
                                                                                                    //   ^[1] goto
            }
    "#,
        InitFileOpt::default(),
        None,
        None,
        "",
    )
    .await;
}

#[tokio::test]
async fn binding_from_array() {
    init_with_file(
        r#"
        entity ent() -> bool {
            let val = 5;
            //  ^^^[2] goto-target

            let arr = [val, val, val, val, val];
                            //   ^[1] goto
            false
        }
    "#,
        InitFileOpt::default(),
        None,
        None,
        "",
    )
    .await;
}

#[tokio::test]
async fn binding_from_2darray() {
    init_with_file(
        r#"
        entity ent() -> bool {
            let val1 = 5;
            let val2 = 5;
            let val3 = 5;
            //  ^^^^[2] goto-target
            let val4 = 5;
            let val5 = 5;

            let arr = [
                [val1, val2, val3, val4, val5],
                [val1, val2, val3, val4, val5],
                [val1, val2, val3, val4, val5],
                        //   ^[1] goto
                [val1, val2, val3, val4, val5],
                [val1, val2, val3, val4, val5],
            ];
            false
        }
    "#,
        InitFileOpt::default(),
        None,
        None,
        "",
    )
    .await;
}

#[tokio::test]
async fn multiline_def_works() {
    init_with_file(
        r#"
            fn rec(arg: int<8>) -> int<8> {
        //  ^[2] goto-target
                4
            }
        //  ^[3] goto-target-end

            fn rec_call() -> int<8> {
                rec( 3 & rec( 3 % rec( 1 / rec( 2 ^rec(5 & rec(1 ^ rec(1*1*1*1*rec(rec(rec(1 + 2 * 1 - 1))))))))))
                                                                                  //   ^[1] goto
            }
    "#,
        InitFileOpt::default(),
        None,
        None,
        "",
    )
    .await;
}

#[tokio::test]
async fn struct_def_from_struct_member() {
    init_with_file(
        r#"
            struct S1 {
        //  ^[2] goto-target
            }
        //  ^[3] goto-target-end

            struct S2 {
                s1: S1,
                //   ^[1] goto
            }
    "#,
        InitFileOpt::default(),
        None,
        None,
        "",
    )
    .await;
}

#[tokio::test]
async fn enum_def_from_struct_member() {
    init_with_file(
        r#"
            enum E1 {
        //  ^[2] goto-target
            }
        //  ^[3] goto-target-end

            struct S2 {
                s1: E1,
                //   ^[1] goto
            }
    "#,
        InitFileOpt::default(),
        None,
        None,
        "",
    )
    .await;
}

#[tokio::test]
async fn struct_def_from_enum_variant() {
    init_with_file(
        r#"
            struct S1 {
        //  ^[2] goto-target
            }
        //  ^[3] goto-target-end

            enum E1 {
                S1 { s1: S1 },
                     //   ^[1] goto
            }
    "#,
        InitFileOpt::default(),
        None,
        None,
        "",
    )
    .await;
}

#[tokio::test]
async fn enum_def_from_enum_variant() {
    init_with_file(
        r#"
            enum E1 {
        //  ^[2] goto-target
            }
        //  ^[3] goto-target-end

            enum E2 {
                E1 { e1: E1 },
                     //   ^[1] goto
            }
    "#,
        InitFileOpt::default(),
        None,
        None,
        "",
    )
    .await;
}
