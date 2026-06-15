use tower_lsp::lsp_types::{
    CompletionParams, CompletionResponse, TextDocumentIdentifier, TextDocumentPositionParams,
};
use tower_lsp::LanguageServer;

use crate::tests::{init_with_file, InitFileOpt, TestContext};

async fn check_completion(test_name: &str, code: &str, expect_none: bool) {
    let TestContext {
        root_dir: _,
        client: _,
        server,
        markers,
        file_uri,
    } = init_with_file(code, InitFileOpt::default(), false).await;

    let completions = markers.values().find(|m| m.completion);
    if let Some(completions) = completions {
        let position = TextDocumentPositionParams {
            text_document: TextDocumentIdentifier {
                uri: file_uri.clone(),
            },
            position: completions.range.start,
        };

        let response = server
            .completion(CompletionParams {
                text_document_position: position,
                context: None,
                partial_result_params: Default::default(),
                work_done_progress_params: Default::default(),
            })
            .await
            .unwrap();

        server
            .backend
            .get_position_details(&completions.range.start, &file_uri.clone())
            .map(|details| {
                let qq = server.backend.query_cache.lock().unwrap();
                let things_around = qq.things_around(&details.loc);

                println!("The things around are :\n{:?}", things_around);
            })
            .expect("The completion marker did not resolve to a loc...");

        if expect_none {
            if response.is_some() {
                panic!("Got completions response when none was expected")
            }
        } else {
            let expected = indoc::formatdoc!("{}", code);
            let response = response.expect(&format!("Did not find any completions information"));

            if let CompletionResponse::Array(items) = response {
                let mut result = String::new();

                for item in items {
                    if !item
                        .label_details
                        .as_ref()
                        .and_then(|details| {
                            details.description.as_ref().map(|d| d.contains("core"))
                        })
                        .unwrap_or(false)
                    {
                        result += &format!(
                            "{}\t{}\n",
                            &item.label,
                            item.insert_text.unwrap_or("-".to_string())
                        );
                    }
                }

                insta::assert_snapshot!(
                    test_name,
                    expected.to_string() + "\n---code ⬆️ completion ⬇️ ---\n" + &result
                )
            } else {
                panic!("Unexpected completion info {response:?}")
            }
        }
    } else {
        panic!("Did not find any completion markers in this test")
    }
}

macro_rules! test_completion {
    ($name:ident, $code:expr$(,)?) => {
        test_completion!($name, $code, expect_none: false);
    };
    ($name:ident, $code:expr, expect_none$(,)?) => {
        test_completion!($name, $code, expect_none: true);
    };
    ($name:ident, $code:expr, expect_none: $expect_none:expr$(,)?) => {
        #[tokio::test]
        async fn $name() {
            check_completion(stringify!($name), $code, $expect_none).await
        }
    };
}

test_completion! {
    bare_completion,
    "
        struct NameOfStruct {
            field_a: bool,
            field_b: int<4>,
        }
        impl NameOfStruct {
            fn method(self) {}
        }

        fn foo() -> bool {
            let s = NameOfStruct(false, 2);

            
      //    ^[1] completion
            false
        }
    ",
}

test_completion! {
    completion_on_in_progress_field,
    "
        struct NameOfStruct {}
        impl NameOfStruct {
            fn method(self) {}
        }

        fn foo() -> bool {
            let s = NameOfStruct();

            let _ = s.aaa
                   // ^[1] completion

            let another = false;

            false
        }
    ",
}

test_completion! {
    completion_on_blank_dot,
    "
        struct NameOfStruct {}
        impl NameOfStruct {
            fn method(self) {}
        }

        fn foo() -> bool {
            let s = NameOfStruct();

            let _ = s.
                   // ^[1] completion

            let another = false;

            false
        }
    ",
}

test_completion! {
    completion_on_blank_dot_not_in_target,
    "
        struct NameOfStruct {}
        impl NameOfStruct {
            fn method(self) {}
        }

        fn foo() -> bool {
            let s = NameOfStruct();

            let _ = s.
                 // ^[1] completion

            let another = false;

            false
        }
    ",
}

test_completion! {
    completion_on_field_not_in_target,
    "
        struct NameOfStruct {}
        impl NameOfStruct {
            fn method(self) {}
        }

        fn foo() -> bool {
            let s = NameOfStruct();

            let _ = s.
                 // ^[1] completion

            let another = false;

            false
        }
    ",
}

test_completion! {
    completion_adds_inst_correctly,
    "
        struct NameOfStruct {}
        impl NameOfStruct {
            fn func(self) {}
            entity ent(self) {}
            pipeline(5) pl1(self, clk: clock) {}
            pipeline({5 + 1}) pl2(self, clk: clock) {}
        }

        fn foo() {
            NameOfStruct().
                        // ^[1] completion

        }
    ",
}

test_completion! {
    field_completion_works,
    "
        struct NameOfStruct {
            f1: bool,
            field2: bool,
        }
        impl NameOfStruct {
            fn func(self) {}
        }

        fn foo() {
            NameOfStruct(false, false).
                                    // ^[1] completion
        }
    "
}

test_completion! {
    method_completion_does_not_run_in_next_token,
    "
        struct NameOfStruct {}

        impl NameOfStruct {
            fn func(self) {}
        }

        fn foo() {
            NameOfStruct(). if
                        //  ^[1] completion
        }
    "
}

test_completion! {
    dot_completion_runs_on_next_line,
    "
        struct NameOfStruct {
            f1: bool,
            field2: bool,
        }
        impl NameOfStruct {
            fn func(self) {}
        }

        fn foo() {
            NameOfStruct(false, false).
            
             // ^[1] completion
        }
    "
}

test_completion! {
    dot_completion_does_not_double_fill_inst,
    "
        struct NameOfStruct {}
        impl NameOfStruct {
            entity func(self) {}
            pipeline(1) funct(self, clk: clock) {reg;}
        }

        fn foo() {
            NameOfStruct().inst 
            
            // ^[1] completion
        }
    "
}

test_completion! {
    dot_completion_does_not_double_fill_pipeline_inst,
    "
        struct NameOfStruct {}
        impl NameOfStruct {
            entity func(self) {}
            pipeline(1) funct(self, clk: clock) {reg;}
        }

        entity foo() {
            NameOfStruct().inst(_)
            
            // ^[1] completion
        }
    "
}

test_completion! {
    locals_complete_correctly,
    "
        entity test(clk: clock, argument: bool) {
            let before_let = false;
            reg(clk) before_reg = false;
            decl before_decl;

            {
                let inner_but_hidden = false;
            };

            {
                let inner_let = false;

                // ^[1] completion
            };

            let before_decl = false;
            let after_let = false;
            reg(clk) after_reg = false;
        }
    "
}

test_completion! {
    path_completion_works,
    "
        mod abc {
            mod def {
                struct A {
                    
                }
            }
        }

        fn main() {
            abc::def
              // ^[1] completion
        }
    "
}

test_completion! {
    path_completion_works_on_partial_paths,
    "
        mod abc {
            mod def {
                struct A {
                    
                }
            }
        }

        fn main() {
            abc::
              // ^[1] completion
        }
    "
}

test_completion! {
    non_imported_enum_variants_are_not_naked_completed,
    "
        enum A {
            B,
            C{x: bool},
        }

        fn main() {
            
        // ^[1] completion
        }
    "
}

test_completion! {
    enum_variants_are_path_completed,
    "
        enum A {
            B,
            C{x: bool},
        }

        fn main() {
            A::
            // ^[1] completion
        }
    "
}

