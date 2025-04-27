use std::collections::HashMap;
use std::fmt::Display;
use std::iter::repeat;
use std::sync::atomic::{AtomicI32, Ordering};
use std::sync::Arc;

use assert_fs::TempDir;
use smart_default::SmartDefault;
use spade_codespan_reporting::files::SimpleFile;
use tokio::sync::Mutex;
use tower_lsp::lsp_types::{
    CompletionContext, CompletionItem, CompletionParams, CompletionResponse, CompletionTriggerKind,
    Diagnostic, DidOpenTextDocumentParams, GotoDefinitionParams, GotoDefinitionResponse,
    HoverContents, HoverParams, InitializeParams, InitializedParams, MarkedString, MessageType,
    Range, TextDocumentIdentifier, TextDocumentItem, TextDocumentPositionParams, Url,
};
use tower_lsp::LanguageServer;

use crate::language_server::ServerFrontend;
use crate::tests::markers::{find_markers, Marker};
use crate::Client;

mod completions;
mod diagnostics;
mod goto_definition;
mod hover;
mod markers;
mod utils;

// Used to fill various `version` fields. Should always be `fetch_add(1)`-ed.
pub(crate) static VERSION: AtomicI32 = AtomicI32::new(0);

#[derive(Clone)]
struct TestClient {
    logs: Arc<Mutex<Vec<String>>>,
    diagnostics: Arc<Mutex<HashMap<Url, Vec<Diagnostic>>>>,
}

impl TestClient {
    fn new() -> TestClient {
        Self {
            logs: Arc::new(Mutex::new(Vec::new())),
            diagnostics: Arc::new(Mutex::new(HashMap::new())),
        }
    }
}

impl Client for TestClient {
    async fn log_message(&self, _ty: MessageType, message: impl Display + Send) {
        self.logs.lock().await.push(message.to_string());
    }

    async fn publish_diagnostics(&self, uri: Url, diags: Vec<Diagnostic>, _version: Option<i32>) {
        self.diagnostics
            .lock()
            .await
            .entry(uri)
            .or_default()
            .extend(diags);
    }
}

#[allow(unused)]
struct TestContext {
    root_dir: TempDir,
    client: TestClient,
    server: ServerFrontend<TestClient>,
    markers: HashMap<i32, Marker>,
    file_uri: Url,
}

impl TestContext {
    async fn _diagnostics(&self) -> Vec<(Url, Diagnostic)> {
        self.client
            .diagnostics
            .lock()
            .await
            .iter()
            .flat_map(|(uri, diagnostics)| repeat(uri.clone()).zip(diagnostics.iter().cloned()))
            .collect()
    }
}

#[derive(SmartDefault)]
struct InitFileOpt {
    /// Send `did_open` on the file after loading.
    #[default(true)]
    open_immediately: bool,
}

/// Initialize the LSP with one file.
async fn init_with_file(
    code: &str,
    opt: InitFileOpt,
    test_comps: Option<&Vec<&str>>,
    test_hover: Option<&str>,
    completion_char: &str,
) -> TestContext {
    let InitFileOpt { open_immediately } = opt;
    let root_dir = TempDir::new().unwrap();
    let root_uri = Url::from_directory_path(&root_dir).unwrap();
    let file = SimpleFile::new("main.spade", code);
    let path = root_dir.join(file.name());
    let file_uri = Url::from_file_path(path.clone()).unwrap();
    let markers = find_markers(&file);

    tokio::fs::write(&path, code).await.unwrap();
    let client = TestClient::new();
    let server = ServerFrontend::new(client.clone());
    server
        .initialize(InitializeParams {
            root_uri: Some(root_uri),
            ..Default::default()
        })
        .await
        .unwrap();
    server.initialized(InitializedParams {}).await;

    let goto = markers.values().find(|m| m.goto);
    let goto_target = markers.values().find(|m| m.goto_target);
    let goto_target_end = markers.values().find(|m| m.goto_target_end);

    let has_goto = match (goto, goto_target) {
        (Some(_), Some(_)) => true,
        (None, None) => false,
        (Some(_), None) | (None, Some(_)) => panic!("need both goto and goto-target marker"),
    };

    if !open_immediately && markers.iter().any(|m| m.1.diagnostic.is_some()) {
        panic!("need to open to check diagnostics");
    }

    if !open_immediately && has_goto {
        panic!("need to open to check goto");
    }

    if open_immediately {
        server
            .did_open(DidOpenTextDocumentParams {
                text_document: TextDocumentItem {
                    uri: file_uri.clone(),
                    language_id: "spade".to_string(),
                    version: VERSION.fetch_add(1, Ordering::AcqRel),
                    text: file.source().to_string(),
                },
            })
            .await;

        // FIXME: probably race condition here. wait for server to mark "done compiling files" or something

        // Check that every diagnostic marker is present in the client diagnostics
        let markers_with_diagnostics: Vec<_> = markers
            .values()
            .filter_map(|m| m.diagnostic.as_ref().map(|d| (m, d)))
            .collect();
        if !markers_with_diagnostics.is_empty() {
            for (marker, expected_diagnostic) in &markers_with_diagnostics {
                // FIXME: print pretty error instead of whatever this becomes
                assert!(client
                    .diagnostics
                    .lock()
                    .await
                    .iter()
                    .flat_map(|(_, diags)| diags)
                    .any(
                        |diag| &diag.message == *expected_diagnostic && diag.range == marker.range
                    ));
            }
            assert_eq!(
                markers_with_diagnostics.len(),
                client.diagnostics.lock().await.len()
            );
        }

        // Check goto
        if has_goto {
            let response = server
                .goto_definition(GotoDefinitionParams {
                    text_document_position_params: TextDocumentPositionParams {
                        text_document: TextDocumentIdentifier {
                            uri: file_uri.clone(),
                        },
                        position: goto.unwrap().range.start,
                    },
                    work_done_progress_params: Default::default(),
                    partial_result_params: Default::default(),
                })
                .await
                .unwrap()
                .unwrap();

            let range = if let Some(goto_target_end) = goto_target_end {
                Range::new(goto_target.unwrap().range.start, goto_target_end.range.end)
            } else {
                goto_target.unwrap().range
            };
            match response {
                GotoDefinitionResponse::Scalar(loc) => {
                    assert_eq!(loc.range, range)
                }
                GotoDefinitionResponse::Array(_) => {
                    panic!("expected only GotoDefinitionResponse::Scalar")
                }
                GotoDefinitionResponse::Link(_) => {
                    panic!("expected only GotoDefinitionResponse::Scalar")
                }
            }
        }
    }

    // Check completions
    let comps = markers.values().find(|m| m.comps);
    if let Some(comps) = comps {
        let response = server
            .completion(CompletionParams {
                text_document_position: TextDocumentPositionParams {
                    text_document: TextDocumentIdentifier {
                        uri: file_uri.clone(),
                    },
                    position: comps.range.start,
                },
                work_done_progress_params: Default::default(),
                partial_result_params: Default::default(),
                context: Some(CompletionContext {
                    trigger_kind: CompletionTriggerKind::INVOKED,
                    trigger_character: Some(completion_char.to_string()),
                }),
            })
            .await
            .unwrap()
            .unwrap();

        if let CompletionResponse::Array(lsp_completions) = response {
            for c1 in test_comps.unwrap() {
                assert!(lsp_completions
                    .iter()
                    .find(|c2| comps_are_same(c1, c2))
                    .is_some());
            }
        }
    }
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
            .unwrap()
            .unwrap();

        if let HoverContents::Scalar(MarkedString::String(s)) = response.contents {
            assert!(s == test_hover.unwrap());
        }
    }

    TestContext {
        root_dir,
        client,
        server,
        markers,
        file_uri,
    }
}

fn comps_are_same(c1: &str, c2: &CompletionItem) -> bool {
    c1 == c2.label
}

#[tokio::test]
async fn server_starts() {
    init_with_file(
        r#"
            fn top() -> bool {
              true
            }
        "#,
        InitFileOpt::default(),
        None,
        None,
        "",
    )
    .await;
}
