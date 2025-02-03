use crate::backend_capabilities::spade_symbol::{SMemberKind, SUnitKind, SpadeSymbol};
use tower_lsp::lsp_types::{Hover, HoverContents, MarkedString, Position, Url};

use crate::backend::ServerBackend;

pub trait HoverInfo {
    async fn find_hover(&self, pos: &Position, uri: &Url) -> Option<Hover>;
}

impl HoverInfo for ServerBackend {
    async fn find_hover(&self, pos: &Position, uri: &Url) -> Option<Hover> {
        if let Some(symbol) = self.find_symbol(pos, uri) {
            let hover_information = match symbol {
                SpadeSymbol::Variable { name, var_type } => {
                    format!(
                        "(variable) {}: {}",
                        name.to_string().split("::").last().unwrap(),
                        var_type.to_string().split("::").last().unwrap(),
                    )
                }
                SpadeSymbol::Unit {
                    kind,
                    name,
                    out_type,
                } => {
                    let kind = match kind {
                        SUnitKind::Entity => "entity",
                        SUnitKind::Function => "fn",
                        SUnitKind::Pipeline => "pipeline",
                    };
                    format!(
                        "({}) {} -> {}",
                        kind,
                        name.to_string().split("::").last().unwrap(),
                        out_type.to_string().split("::").last().unwrap(),
                    )
                }
                SpadeSymbol::Member {
                    kind,
                    parent_type,
                    name,
                    member_type,
                } => {
                    let kind = match kind {
                        SMemberKind::Field => "field",
                        SMemberKind::Method => "method",
                    };
                    format!(
                        "({}) {}.{}: {}",
                        kind,
                        parent_type.to_string().split("::").last().unwrap(),
                        name.to_string().split("::").last().unwrap(),
                        member_type.to_string().split("::").last().unwrap(),
                    )
                }
                SpadeSymbol::Type(id) => {
                    format!("(type) {}", id.to_string().split("::").last().unwrap(),)
                }
                SpadeSymbol::NotInferred(_id) => String::new(),
            };

            if !hover_information.is_empty() {
                return Some(Hover {
                    contents: HoverContents::Scalar(MarkedString::String(hover_information)),
                    range: None,
                });
            }
        }
        None
    }
}
