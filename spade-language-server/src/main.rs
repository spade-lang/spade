mod backend;
mod backend_capabilities;
mod compile;
mod language_server;
// Disabling lsp tests on macos for now since they break in CI and I don't have
// ready access to a mac to debug them on
#[cfg(all(test, not(target_os = "macos")))]
mod tests;

use crate::language_server::ServerFrontend;

use std::fmt::Display;
use std::future::Future;

use tower_lsp::lsp_types::{Diagnostic, MessageType, Url};
use tower_lsp::{Client as LspClient, LspService, Server};

pub trait Client: Send + Sync + 'static {
    fn log_message(
        &self,
        ty: MessageType,
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
    async fn log_message(&self, ty: MessageType, message: impl Display) {
        self.log_message(ty, message).await;
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
