use camino::Utf8Path;
use camino::Utf8PathBuf;
use std::sync::{Arc, Mutex};
use tokio::select;
use tokio::sync::mpsc;
use tokio::sync::oneshot;
use tokio::sync::watch;
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::CompletionParams;
use tower_lsp::lsp_types::CompletionResponse;
use tower_lsp::lsp_types::DidChangeTextDocumentParams;
use tower_lsp::lsp_types::{
    CompletionOptions, DidOpenTextDocumentParams, DidSaveTextDocumentParams, GotoDefinitionParams,
    GotoDefinitionResponse, Hover, HoverParams, HoverProviderCapability, InitializeParams,
    InitializeResult, InitializedParams, MessageType, OneOf, ServerCapabilities, SymbolInformation,
    TextDocumentPositionParams, TextDocumentSyncCapability, TextDocumentSyncKind,
    WorkDoneProgressOptions, WorkspaceSymbolParams,
};
use tower_lsp::LanguageServer;

use crate::backend::ServerBackend;
use crate::goto_definition::GotoDefinition;
use crate::hover::HoverInfo;
use crate::Client;

pub struct ServerFrontend<C> {
    pub(crate) backend: ServerBackend,
    symbols: Arc<Mutex<Vec<SymbolInformation>>>,
    client: Arc<C>,

    last_compile_fuse: Arc<Mutex<Option<oneshot::Sender<()>>>>,
    is_compiling_rx: watch::Receiver<bool>,
    is_compiling_tx: watch::Sender<bool>,
}

impl<C: Client> ServerFrontend<C> {
    pub fn new(client: C) -> Self {
        let (sender, receiver) = mpsc::channel::<(MessageType, String)>(1);
        let arc_client = Arc::new(client);
        let _log_handler = tokio::spawn(Self::print_logs(Arc::clone(&arc_client), receiver));

        let (is_compiling_tx, is_compiling_rx) = watch::channel(false);

        ServerFrontend {
            backend: ServerBackend::new(sender),
            client: Arc::clone(&arc_client),
            symbols: Arc::new(Mutex::new(Vec::new())),
            last_compile_fuse: Arc::new(Mutex::new(None)),
            is_compiling_rx,
            is_compiling_tx,
        }
    }

    async fn print_logs(client: Arc<C>, mut receiver: mpsc::Receiver<(MessageType, String)>) {
        while let Some((msg_type, log)) = receiver.recv().await {
            client.log_message(msg_type, log).await;
        }
    }

    async fn compile(
        &self,
        path: &Utf8Path,
        modified_file: Option<(&Utf8Path, &str)>,
        version: Option<i32>,
    ) {
        let diagnostics_per_file = self.backend.try_compile(path, modified_file, version).await;

        for (uri, diagnostics) in diagnostics_per_file {
            self.client
                .publish_diagnostics(uri, diagnostics, version)
                .await;
        }

        if let Ok(symbols) = self.backend.get_lsp_symbols().await {
            *self.symbols.lock().unwrap() = symbols;
        }
    }
}

#[tower_lsp::async_trait]
impl<C: Client> LanguageServer for ServerFrontend<C> {
    async fn initialize(&self, params: InitializeParams) -> Result<InitializeResult> {
        self.client
            .log_message(MessageType::LOG, "initialize")
            .await;
        self.client
            .log_message(MessageType::LOG, format!("root_uri: {:?}", params.root_uri))
            .await;

        let root_dir = params
            .root_uri
            .map(|uri| Utf8PathBuf::from(uri.path().to_string()));
        *self.backend.root_dir.lock().unwrap() = root_dir;

        let server_capabilities = ServerCapabilities {
            text_document_sync: Some(TextDocumentSyncCapability::Kind(TextDocumentSyncKind::FULL)),

            workspace_symbol_provider: Some(OneOf::Left(true)),

            definition_provider: Some(OneOf::Left(true)),

            completion_provider: Some(CompletionOptions {
                completion_item: Default::default(),
                resolve_provider: Some(false),
                trigger_characters: Some(vec![".".to_string(), "::".to_string()]),
                all_commit_characters: None,
                work_done_progress_options: WorkDoneProgressOptions {
                    work_done_progress: None,
                },
            }),

            hover_provider: Some(HoverProviderCapability::Simple(true)),

            ..ServerCapabilities::default()
        };

        Ok(InitializeResult {
            capabilities: server_capabilities,
            server_info: None,
        })
    }

    async fn initialized(&self, _: InitializedParams) {
        self.client
            .log_message(MessageType::INFO, "Started the Spade Language Server")
            .await;
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        let path = Utf8PathBuf::from(params.text_document.uri.path().to_string())
            .canonicalize_utf8()
            .unwrap();

        self.client
            .log_message(MessageType::LOG, format!("did_open: {}", path))
            .await;

        self.compile(&path, None, Some(params.text_document.version))
            .await;
    }

    async fn did_save(&self, params: DidSaveTextDocumentParams) {
        let path = Utf8PathBuf::from(params.text_document.uri.path().to_string())
            .canonicalize_utf8()
            .unwrap();

        self.compile(&path, None, None).await;
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        let _ = self.is_compiling_tx.send(true);

        let path = Utf8PathBuf::from(params.text_document.uri.path().to_string())
            .canonicalize_utf8()
            .unwrap();

        // If the user types fast, we end up with a long queue of compilation tasks that are operating
        // on old code. To fix this, we'll fuse these compilation process, and kill the previous in-progress
        // compilation if a new one is starting
        if let Some(fuse) = self.last_compile_fuse.lock().unwrap().take() {
            let _ = fuse.send(());
        }

        let (sender, receiver) = oneshot::channel();
        *self.last_compile_fuse.lock().unwrap() = Some(sender);

        async {
            select! {
                _ = self.compile(
                    &path,
                    params
                        .content_changes
                        .last()
                        .map(|change| (path.as_path(), change.text.as_str())),
                    None,
                ) => {
                    let _ = self.is_compiling_tx.send(false);

                }
                // A select on 2 tasks cancels the one that doesn't finish, so if we receive
                // something from the fuse before compilation is done, we kill the compilation
                // here
                _ = receiver => {}
            }
        }
        .await
    }

    async fn symbol(
        &self,
        params: WorkspaceSymbolParams,
    ) -> Result<Option<Vec<SymbolInformation>>> {
        self.client
            .log_message(
                MessageType::LOG,
                format!("workspace/symbol params: {:?}", params),
            )
            .await;
        let _query = params.query;

        let symbols = self.symbols.lock().unwrap();
        Ok(Some(symbols.clone()))
    }

    async fn goto_definition(
        &self,
        params: GotoDefinitionParams,
    ) -> Result<Option<GotoDefinitionResponse>> {
        let TextDocumentPositionParams {
            text_document: doc,
            position: pos,
        } = params.text_document_position_params;

        match self.backend.find_definition(&pos, &doc.uri) {
            Some(location) => Ok(Some(GotoDefinitionResponse::Scalar(location))),
            None => Ok(None),
        }
    }

    async fn hover(&self, params: HoverParams) -> Result<Option<Hover>> {
        let TextDocumentPositionParams {
            text_document: doc,
            position: pos,
        } = params.text_document_position_params;

        Ok(self.backend.find_hover(&pos, &doc.uri).await)
    }

    async fn completion(&self, params: CompletionParams) -> Result<Option<CompletionResponse>> {
        let mut is_compiling = self.is_compiling_rx.clone();

        let _ = is_compiling.wait_for(|val| *val == false).await;

        let TextDocumentPositionParams {
            text_document: doc,
            position: pos,
        } = params.text_document_position;

        Ok(self.backend.get_completions(&pos, &doc.uri).await)
    }

    async fn shutdown(&self) -> Result<()> {
        Ok(())
    }
}
