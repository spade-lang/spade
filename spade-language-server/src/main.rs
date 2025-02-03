mod backend;
mod backend_capabilities;
mod compile;
mod keywords;
mod language_server;
#[cfg(test)]
mod tests;

use crate::language_server::ServerFrontend;

use std::fmt::Display;
use std::future::Future;

use tower_lsp::lsp_types::{Diagnostic, MessageType, Url};
use tower_lsp::{Client as LspClient, LspService, Server};

pub trait Client: Send + Sync + 'static {
    fn log_message(
        &self,
        typ: MessageType,
        message: impl Display + Send,
    ) -> impl Future<Output = ()> + Send;
    fn publish_diagnostics(
        &self,
        uri: Url,
        diags: Vec<Diagnostic>,
        version: Option<i32>,
    ) -> impl Future<Output = ()> + Send;
}

impl Client for LspClient {
    #[inline(always)]
    async fn log_message(&self, typ: MessageType, message: impl Display) {
        self.log_message(typ, message).await;
    }

    #[inline(always)]
    async fn publish_diagnostics(&self, uri: Url, diags: Vec<Diagnostic>, version: Option<i32>) {
        self.publish_diagnostics(uri, diags, version).await;
    }
}

#[tokio::main]
async fn main() {
    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();
    let (service, socket) = LspService::new(|client| ServerFrontend::new(client));
    Server::new(stdin, stdout, socket).serve(service).await;
}
