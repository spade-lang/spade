use crate::backend_capabilities::completion::Completion;
use crate::backend_capabilities::goto_definition::GotoDefinition;
use crate::backend_capabilities::hover::HoverInfo;
use camino::Utf8Path;
use camino::Utf8PathBuf;
use std::sync::{Arc, Mutex};
use tokio::sync::mpsc;
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::{
    CompletionOptions, CompletionParams, CompletionResponse, DidChangeTextDocumentParams,
    DidOpenTextDocumentParams, DidSaveTextDocumentParams, GotoDefinitionParams,
    GotoDefinitionResponse, Hover, HoverParams, HoverProviderCapability, InitializeParams,
    InitializeResult, InitializedParams, MessageType, OneOf, ServerCapabilities, SymbolInformation,
    TextDocumentPositionParams, TextDocumentSyncCapability, TextDocumentSyncKind,
    WorkDoneProgressOptions, WorkspaceSymbolParams,
};
use tower_lsp::LanguageServer;

use crate::backend::ServerBackend;
use crate::Client;

pub struct ServerFrontend<C> {
    backend: ServerBackend,
    symbols: Arc<Mutex<Vec<SymbolInformation>>>,
    client: Arc<C>,
}

impl<C: Client> ServerFrontend<C> {
    pub fn new(client: C) -> Self {
        let (sender, receiver) = mpsc::channel::<(MessageType, String)>(1);
        let arc_client = Arc::new(client);
        let _log_handler = tokio::spawn(Self::print_logs(Arc::clone(&arc_client), receiver));

        ServerFrontend {
            backend: ServerBackend::new(sender),
            client: Arc::clone(&arc_client),
            symbols: Arc::new(Mutex::new(Vec::new())),
        }
    }

    async fn print_logs(client: Arc<C>, mut receiver: mpsc::Receiver<(MessageType, String)>) {
        while let Some((msg_type, log)) = receiver.recv().await {
            client.log_message(msg_type, log).await;
        }
    }

    async fn compile(&self, path: &Utf8Path, version: Option<i32>) {
        let diagnostics_per_file = self.backend.try_compile(path, version).await;

        for (uri, diagnostics) in diagnostics_per_file {
            self.client
                .log_message(MessageType::LOG, format!("{uri}: {diagnostics:?}"))
                .await;
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

        let dot = ".".to_string();
        let server_capabilities = ServerCapabilities {
            text_document_sync: Some(TextDocumentSyncCapability::Kind(TextDocumentSyncKind::FULL)),

            workspace_symbol_provider: Some(OneOf::Left(true)),

            definition_provider: Some(OneOf::Left(true)),

            completion_provider: Some(CompletionOptions {
                resolve_provider: Some(false),
                trigger_characters: Some(vec![dot]),
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

        self.compile(&path, Some(params.text_document.version))
            .await;
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        let path = Utf8PathBuf::from(params.text_document.uri.path().to_string())
            .canonicalize_utf8()
            .unwrap();

        *self
            .backend
            .changed_files
            .write()
            .unwrap()
            .entry(path.clone())
            // NOTE: We get only one change containing the entire file since we specified
            // TextDocumentSyncKind::FULL in our ServerCapabilities. Therefore we can
            // overwrite the old String with the new one.
            .or_insert_with(String::new) = params.content_changes[0].text.clone();

        self.client
            .log_message(MessageType::LOG, format!("did_change: {}", path))
            .await;

        self.compile(&path, Some(params.text_document.version))
            .await;
    }

    async fn did_save(&self, params: DidSaveTextDocumentParams) {
        let path = Utf8PathBuf::from(params.text_document.uri.path().to_string())
            .canonicalize_utf8()
            .unwrap();

        let _ = self.backend.changed_files.write().unwrap().remove(&path);
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

    async fn completion(&self, params: CompletionParams) -> Result<Option<CompletionResponse>> {
        let TextDocumentPositionParams {
            text_document: doc,
            position: pos,
        } = params.text_document_position;

        let completions = self
            .backend
            .get_completions(&pos, &doc.uri, params.context)
            .await;

        Ok(Some(CompletionResponse::Array(completions)))
    }

    async fn hover(&self, params: HoverParams) -> Result<Option<Hover>> {
        let TextDocumentPositionParams {
            text_document: doc,
            position: pos,
        } = params.text_document_position_params;

        Ok(self.backend.find_hover(&pos, &doc.uri).await)
    }

    async fn shutdown(&self) -> Result<()> {
        Ok(())
    }
}
