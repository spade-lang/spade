use tower_lsp::lsp_types::{
    CompletionParams, CompletionResponse, TextDocumentIdentifier, TextDocumentPositionParams,
};
use tower_lsp::LanguageServer;

use crate::tests::{init_with_file, InitFileOpt, TestContext};

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
                false,
            )
            .await;

            // Check hover
            let hover = markers.values().find(|m| m.completion);
            if let Some(hover) = hover {
                let response = server
                    .completion(CompletionParams {
                        text_document_position: TextDocumentPositionParams {
                            text_document: TextDocumentIdentifier {
                                uri: file_uri.clone(),
                            },
                            position: hover.range.start,
                        },
                        context: None,
                        partial_result_params: Default::default(),
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

                    if let CompletionResponse::Array(items) = response
                    {
                        let mut result = String::new();

                        for item in items {
                            if !item.label_details.as_ref().and_then(|details| details.description.as_ref().map(|d| d.contains("core"))).unwrap_or(false) {
                                result += &format!("{}\n", &item.label);
                            }
                        }

                        insta::assert_snapshot!(expected.to_string() + "\n---code ⬆️ completion ⬇️ ---\n" + &result)
                    } else {
                        panic!("Unexpected completion info {response:?}")
                    }
                }
            } else {
                panic!("Did not find any completion markers in this test")
            }
        }
    };
}

test_completion! {
    completion_after_dot,
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

            ;
      //    ^[1] completion
            false
        }
    ",
}
