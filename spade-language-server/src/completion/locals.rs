use spade_hir::{Block, ExprKind};
use spade_typeinference::HasType;
use tower_lsp::lsp_types::{CompletionItem, CompletionItemKind, Position, Url};

use crate::{backend::ServerBackend, util::PositionDetails};

impl ServerBackend {
    pub async fn get_local_completion(
        &self,
        pos: &Position,
        uri: &Url,
    ) -> Option<Vec<CompletionItem>> {
        let PositionDetails {
            loc,
            name: _,
            unit_type_state,
            current_unit,
        } = self.get_position_details(pos, uri)?;

        let qq = self.query_cache.lock().unwrap();
        let things_around = qq.things_around(&loc);

        let from_head = current_unit
            .map(|u| u.inputs.iter().map(|i| i.name.clone()).collect::<Vec<_>>())
            .unwrap_or_default();

        let from_expr = things_around
            .iter()
            .map(|thing| {
                let spade_hir::query::Thing::Expr(e) = &thing.inner else {
                    return vec![];
                };
                let ExprKind::Block(block) = &e.kind else {
                    return vec![];
                };
                let Block {
                    statements,
                    result: _,
                } = &**block;

                statements
                    .iter()
                    .filter(|statement| statement.span.start() < loc.span.start())
                    .flat_map(|s| match &s.inner {
                        spade_hir::Statement::Error => vec![],
                        spade_hir::Statement::Binding(binding) => binding.pattern.get_names(),
                        spade_hir::Statement::Expression(_) => vec![],
                        spade_hir::Statement::Register(register) => register.pattern.get_names(),
                        spade_hir::Statement::Declaration(names) => names.clone(),
                        spade_hir::Statement::PipelineRegMarker(_) => vec![],
                        spade_hir::Statement::Label(_) => vec![],
                        spade_hir::Statement::Assert(_) => vec![],
                        spade_hir::Statement::Set { .. } => vec![],
                    })
                    .collect()
            })
            .flatten();

        Some(
            from_head
                .into_iter()
                .chain(from_expr)
                .filter_map(|name_id| {
                    name_id.1.tail().to_named_str().map(|name| CompletionItem {
                        label: name.to_string(),
                        label_details: None,
                        kind: Some(CompletionItemKind::VARIABLE),
                        detail: unit_type_state
                            .as_ref()
                            .and_then(|ts| name_id.try_get_type(&ts).map(|ty| ty.display(&ts))),
                        documentation: None,
                        deprecated: None,
                        preselect: None,
                        sort_text: None,
                        filter_text: None,
                        insert_text: None,
                        insert_text_format: None,
                        insert_text_mode: None,
                        text_edit: None,
                        additional_text_edits: None,
                        command: None,
                        commit_characters: None,
                        data: None,
                        tags: None,
                    })
                })
                .collect(),
        )
    }
}
