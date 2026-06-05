use tower_lsp::lsp_types::{
    CompletionParams, CompletionResponse, TextDocumentIdentifier, TextDocumentPositionParams,
};
use tower_lsp::LanguageServer;

use crate::tests::{init_with_file, InitFileOpt, TestContext};

async fn check_completion(test_name: &str, code: &str, expect_none: bool) {
    let TestContext {
        root_dir: root_dir, // Has to be given a name to not go out of scope // TODO: Probably wrong
        client: _,
        server,
        markers,
        file_uri,
    } = init_with_file(code, InitFileOpt::default(), false).await;

    root_dir.into_persistent();

    // Check hover
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
                        result += &format!("{}\n", &item.label);
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
    completion_after_dot,
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
