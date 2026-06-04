use itertools::Itertools;
use spade_common::{location_info::WithLocation, name::Path};
use tower_lsp::lsp_types::{
    CompletionItem, CompletionItemKind, CompletionItemLabelDetails, CompletionResponse, Position,
    Url,
};

use crate::backend::ServerBackend;

pub trait CompletionInfo {
    async fn get_completions(&self, pos: &Position, uri: &Url) -> Option<CompletionResponse>;
}

impl CompletionInfo for ServerBackend {
    async fn get_completions(&self, pos: &Position, uri: &Url) -> Option<CompletionResponse> {
        let position_details = self.get_position_details(pos, uri)?;

        // FIXME: For completion outside units, we should work out which namespace a loc is in
        let mut parent_paths = vec![];
        if let Some(unit_name) = &position_details.name {
            let mut path = unit_name.1.clone();
            while !path.0.is_empty() {
                parent_paths.push(path.clone());
                path = path.pop();
            }
        }

        // let names = if let Some(unit) = position_details.name {
        let symtab = self.symtab.lock().unwrap();

        let names = if let Some(symtab) = &*symtab {
            symtab
                .symtab()
                .things
                .iter()
                .filter_map(|(thing_name, thing)| {
                    if thing_name.1 .0.len() == 0 {
                        return None;
                    }

                    let local_name = thing_name.1.tail();
                    if !local_name.is_named() {
                        return None;
                    }

                    let is_unnameable = thing_name.1 .0.iter().any(|path| !path.is_named());

                    let is_local = match thing {
                        spade_hir::symbol_table::Thing::Variable(_) => true,

                        spade_hir::symbol_table::Thing::Struct(_)
                        | spade_hir::symbol_table::Thing::EnumVariant(_)
                        | spade_hir::symbol_table::Thing::Unit(_)
                        | spade_hir::symbol_table::Thing::Alias { .. }
                        | spade_hir::symbol_table::Thing::ArrayLabel(_)
                        | spade_hir::symbol_table::Thing::Module(_, _)
                        | spade_hir::symbol_table::Thing::Macro(_, _)
                        | spade_hir::symbol_table::Thing::Trait(_)
                        | spade_hir::symbol_table::Thing::Dummy => false,
                    };

                    if is_unnameable && !is_local {
                        return None;
                    }

                    // Locals should only be completed in the unit we are working on
                    if is_local {
                        if let Some(this_unit) = &position_details.name {
                            if !thing_name.1.starts_with(&this_unit.1) {
                                return None;
                            }
                        } else {
                            return None;
                        }
                    }

                    let kind = Some(match thing {
                        spade_hir::symbol_table::Thing::Struct(_) => CompletionItemKind::STRUCT,
                        spade_hir::symbol_table::Thing::EnumVariant(_) => CompletionItemKind::ENUM,
                        spade_hir::symbol_table::Thing::Unit(_) => CompletionItemKind::FUNCTION,
                        spade_hir::symbol_table::Thing::Variable(_) => CompletionItemKind::VALUE,
                        spade_hir::symbol_table::Thing::Alias { .. } => {
                            CompletionItemKind::REFERENCE
                        }
                        spade_hir::symbol_table::Thing::ArrayLabel(_) => {
                            CompletionItemKind::PROPERTY
                        }
                        spade_hir::symbol_table::Thing::Module(_, _) => CompletionItemKind::MODULE,
                        spade_hir::symbol_table::Thing::Macro(_, _) => CompletionItemKind::FUNCTION,
                        spade_hir::symbol_table::Thing::Trait(_) => CompletionItemKind::INTERFACE,
                        spade_hir::symbol_table::Thing::Dummy => CompletionItemKind::MODULE,
                    });

                    // Everything remaining should be completed, but how we complete it depends
                    // on the path relative to the current unit. If the thing shares a common ancestor
                    // with the unit, complete it as a bare thing, otherwise, complete it
                    // with a fully qualified path in the description
                    let is_imported = parent_paths.iter().any(|path| {
                        thing_name.1.starts_with(path) && thing_name.1 .0.len() == path.0.len() + 1
                    });

                    let local_name = local_name.to_named_str().unwrap_or("<hidden>").to_string();
                    let full_path = thing_name
                        .1
                        .to_named_strs()
                        .into_iter()
                        .filter_map(|x| x)
                        .join("::");
                    let (label, filter_text) = if is_imported {
                        (local_name, None)
                    } else {
                        (format!("{} ({})", local_name, full_path.clone()), Some(local_name))
                    };

                    Some(CompletionItem {
                        label: label,
                        label_details: Some(CompletionItemLabelDetails {
                            detail: None,
                            description: if !is_local { Some(full_path) } else { None },
                        }),
                        kind: kind,
                        detail: None,
                        documentation: None,
                        deprecated: None,
                        preselect: None,
                        sort_text: None,
                        filter_text: filter_text.clone(),
                        insert_text: filter_text,
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
                .collect::<Vec<_>>()
        } else {
            vec![]
        };

        Some(CompletionResponse::Array(names))
    }
}
