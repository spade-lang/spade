use tower_lsp::lsp_types::{
    HoverContents, HoverParams, MarkedString, MarkupContent, TextDocumentIdentifier,
    TextDocumentPositionParams,
};
use tower_lsp::LanguageServer;

use crate::tests::{init_with_file, InitFileOpt, TestContext};

macro_rules! test_hover {
    ($name:ident, $code:expr$(,)?) => {
        test_hover!($name, $code, expect_none: false);
    };
    ($name:ident, $code:expr, expect_none$(,)?) => {
        test_hover!($name, $code, expect_none: true);
    };
    ($name:ident, $code:expr, expect_none: $expect_none:expr$(,)?) => {
        #[tokio::test]
        async fn $name() {
            let TestContext {
                root_dir: _,
                client: _,
                server,
                markers,
                file_uri,
            } = init_with_file(
                $code,
                InitFileOpt::default(),
                None,
                "",
            )
            .await;

            // Check hover
            let hover = markers.values().find(|m| m.hover);
            if let Some(hover) = hover {
                let response = server
                    .hover(HoverParams {
                        text_document_position_params: TextDocumentPositionParams {
                            text_document: TextDocumentIdentifier {
                                uri: file_uri.clone(),
                            },
                            position: hover.range.start,
                        },
                        work_done_progress_params: Default::default(),
                    })
                    .await
                    .unwrap();

                if $expect_none {
                    if response.is_some() {
                        panic!("Got hover response when none was expected")
                    }
                } else {
                    let expected = indoc::indoc!($code);
                    let response = response.expect(&format!("Did not find any hover information in {}", expected));

                    if let HoverContents::Scalar(MarkedString::String(s))
                    | HoverContents::Markup(MarkupContent { kind: _, value: s }) = response.contents
                    {
                        insta::assert_snapshot!(expected.to_string() + "\n---code ⬆️ hover ⬇️ ---\n" + &s)
                    } else {
                        panic!("Unexpected hover info {response:?}")
                    }
                }
            }
        }
    };
}

test_hover! {
    hover_binding,
    "
        struct NameOfStruct {
            field_a: bool,
            field_b: int<4>,
        }
        fn foo() -> bool {
            let s = NameOfStruct(false, 2);

            let cow = s;
                  //  ^[1] hover
            false
        }
    ",
}

test_hover! {
    hover_function,
    r#"
    struct NameOfStruct {
        field_a: bool,
        field_b: int<4>,
    }
    fn foo() -> bool {
        let s = NameOfStruct(false, 2);

        let cow = s;
        false
    }

    fn bar() -> bool {
        foo()
     //  ^[1] hover
    }
    "#,
}

test_hover! {
    hover_function_in_arguments,
    r#"
    struct NameOfStruct {
        field_a: bool,
        field_b: int<4>,
    }
    fn foo() -> bool {
        let s = NameOfStruct(false, 2);

        let cow = s;
        false
    }

    fn bar() -> bool {
        foo()
     //     ^[1] hover
    }
    "#,
    expect_none
}

test_hover! {
    hover_on_struct_name,
    r#"
    struct NameOfStruct {
        field_a: bool,
        field_b: int<4>,
    }
    fn foo() {
        let s = NameOfStruct(false, 2);
             //     ^[1] hover
    }
    "#,
}

test_hover! {
    hover_unit_with_docs,
    r#"
    /// This is a doc string
    fn foo() -> bool {true}

    fn bar() -> bool {
        foo()
     //  ^[1] hover
    }
    "#
}

test_hover! {
    hover_on_method,
    r#"
        struct S {}

        impl S {
            /// Docs
            fn meth(self, a: bool) -> bool {
                true
            }
        }

        fn bar() -> bool {
            S().meth(true)
        //       ^[1] hover
        }
    "#
}

test_hover! {
    hover_on_chained_method,
    r#"
        struct S {}

        impl S {
            /// Docs
            fn meth(self, a: bool) -> bool {
                true
            }
        }

        impl bool {
            fn meth2(self) -> uint<8> {0}
        }

        fn bar() -> uint<8> {
            S()
                .meth(true)
                .meth2()
        //       ^[1] hover
        }
    "#
}

test_hover! {
    hover_on_first_chained_method,
    r#"
        struct S {}

        impl S {
            /// Docs
            fn meth(self, a: bool) -> bool {
                true
            }
        }

        impl bool {
            fn meth2(self) -> uint<8> {0}
        }

        fn bar() -> uint<8> {
            S()

                .meth(true)
        //       ^[1] hover
                .meth2()
        }
    "#
}

test_hover! {
    hover_on_generic_impl,
    r#"
        struct S<T> {x: T}

        impl<T> S<T> {
            /// Docs
            fn meth(self, x: T) -> T {
                x
            }
        }

        fn bar() -> uint<8> {
            S(8u8)
                .meth(0)
        //       ^[1] hover
        }
    "#
}

test_hover! {
    hover_on_field,
    r#"
        struct NameOfStruct {
            field_a: bool,
            field_b: int<4>,
        }
        fn foo() -> bool {
            let s = NameOfStruct(false, 2);
            s.field_a
            //  ^[1] hover
        }
    "#,
}

test_hover! {
    hover_on_single_elem_enum_variant,
    r#"
        enum A {
            Field,
            Field2{val1: bool, val2: int<8>}
        }
        fn foo() {
            let s = A::Field;
                    //  ^[1] hover
        }
    "#,
}

test_hover! {
    hover_on_multi_elem_enum_variant,
    r#"
        enum A {
            Field,
            Field2{val1: bool, val2: int<8>}
        }
        fn foo() {
            let s = A::Field2(false, 0);
                    //  ^[1] hover
        }
    "#,
}

test_hover! {
    hover_on_method_chain_with_unrelated_type_error_in_module_gives_correct_results,
    r#"
        struct S {}
        impl S {
            fn meth(self) -> bool {true}
        }

        fn test() {
            let a = 0 + true;

            S().meth();
            //  ^[1] hover

            true
        }
    "#,
}
