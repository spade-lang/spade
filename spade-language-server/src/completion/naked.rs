use itertools::Itertools;
use spade_common::name::NameID;
use spade_hir::{symbol_table::SymbolTable, ParameterList, UnitKind};
use tower_lsp::lsp_types::{
    CompletionItem, CompletionItemKind, CompletionItemLabelDetails, CompletionResponse,
    InsertTextFormat, Position, Url,
};

use crate::{
    backend::ServerBackend,
    completion::{ParamListExt, SnippetBuilder, UnitKindExt},
};

impl ServerBackend {
    pub async fn get_naked_completions(
        &self,
        pos: &Position,
        uri: &Url,
    ) -> Option<CompletionResponse> {
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

        let local_names = self.get_local_completion(pos, uri).await;

        // let names = if let Some(unit) = position_details.name {
        let symtab = self.symtab.lock().unwrap();

        let global_names = if let Some(symtab) = &*symtab {
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

                    // Locals are completed separately
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

                    // We don't want to complete enum variants unless they are explicitly imported
                    // with an alias
                    if let spade_hir::symbol_table::Thing::EnumVariant(_) = thing {
                        return None;
                    }

                    if is_unnameable || is_local {
                        return None;
                    }


                    let resolved_thing = follow_aliases(symtab.symtab(), thing);

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

                    let CompletionData {
                        kind,
                        label,
                        snippet,
                    } = completion_data(&local_name, thing);

                    let (final_label, filter_text) = if is_imported {
                        (label, None)
                    } else {
                        (
                            format!("{} [{}]", label, full_path.clone()),
                            Some(local_name),
                        )
                    };

                    let description = resolved_thing
                        .map(|name| {
                            name.0
                                 .1
                                .to_named_strs()
                                .into_iter()
                                .filter_map(|x| x)
                                .join("::")
                        })
                        .unwrap_or(full_path);

                    Some(CompletionItem {
                        label: final_label,
                        label_details: Some(CompletionItemLabelDetails {
                            detail: None,
                            description: Some(description),
                        }),
                        kind: Some(kind),
                        detail: None,
                        documentation: None,
                        deprecated: None,
                        preselect: None,
                        sort_text: None,
                        filter_text: filter_text.clone(),
                        insert_text: Some(snippet),
                        insert_text_format: Some(InsertTextFormat::SNIPPET),
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

        let names = global_names
            .into_iter()
            .chain(local_names.unwrap_or_default())
            .collect();

        Some(CompletionResponse::Array(names))
    }
}

pub(crate) fn follow_aliases<'a>(
    symtab: &'a SymbolTable,
    thing: &spade_hir::symbol_table::Thing,
) -> Option<(NameID, &'a spade_hir::symbol_table::Thing)> {
    match thing {
        spade_hir::symbol_table::Thing::Alias {
            loc: _,
            path,
            in_namespace: _,
        } => symtab
            .lookup_thing(path, true)
            .ok()
            .and_then(
                |original @ (_, thing)| match follow_aliases(symtab, thing) {
                    None => Some(original),
                    new => new,
                },
            ),
        spade_hir::symbol_table::Thing::Struct(_)
        | spade_hir::symbol_table::Thing::EnumVariant(_)
        | spade_hir::symbol_table::Thing::Unit(_)
        | spade_hir::symbol_table::Thing::Variable(_)
        | spade_hir::symbol_table::Thing::ArrayLabel(_)
        | spade_hir::symbol_table::Thing::Module(_, _)
        | spade_hir::symbol_table::Thing::Macro(_, _)
        | spade_hir::symbol_table::Thing::Trait(_)
        | spade_hir::symbol_table::Thing::Dummy => None,
    }
}

pub(crate) struct CompletionData {
    pub kind: CompletionItemKind,
    pub label: String,
    pub snippet: String,
}

pub(crate) fn completion_data(
    name: &str,
    thing: &spade_hir::symbol_table::Thing,
) -> CompletionData {
    let kind = match thing {
        spade_hir::symbol_table::Thing::Struct(_) => CompletionItemKind::STRUCT,
        spade_hir::symbol_table::Thing::EnumVariant(_) => CompletionItemKind::ENUM,
        spade_hir::symbol_table::Thing::Unit(_) => CompletionItemKind::FUNCTION,
        spade_hir::symbol_table::Thing::Variable(_) => CompletionItemKind::VALUE,
        spade_hir::symbol_table::Thing::Alias { .. } => CompletionItemKind::REFERENCE,
        spade_hir::symbol_table::Thing::ArrayLabel(_) => CompletionItemKind::PROPERTY,
        spade_hir::symbol_table::Thing::Module(_, _) => CompletionItemKind::MODULE,
        spade_hir::symbol_table::Thing::Macro(_, _) => CompletionItemKind::FUNCTION,
        spade_hir::symbol_table::Thing::Trait(_) => CompletionItemKind::INTERFACE,
        spade_hir::symbol_table::Thing::Dummy => CompletionItemKind::MODULE,
    };

    let is_enum_variant = matches!(thing, spade_hir::symbol_table::Thing::EnumVariant(_));

    let mut sb = SnippetBuilder::new();
    let mut unit_like = |params: &ParameterList, kind: &UnitKind| {
        // FIXME Use `inst` data here
        let (inst_label, inst_snippet) = kind.label_snippet(false, false, &mut sb);
        let (arg_label, arg_snippet) = params.label_snippet(&mut sb, is_enum_variant, false);

        (
            format!("{inst_label}{name}{arg_label}"),
            format!("{inst_snippet}{name}{arg_snippet}"),
        )
    };

    let (label, snippet) = match thing {
        spade_hir::symbol_table::Thing::Struct(t) => unit_like(
            &t.params,
            &UnitKind::Function(spade_hir::FunctionKind::Struct),
        ),
        spade_hir::symbol_table::Thing::EnumVariant(t) => unit_like(
            &t.params,
            &UnitKind::Function(spade_hir::FunctionKind::Enum),
        ),
        spade_hir::symbol_table::Thing::Unit(t) => unit_like(&t.inputs, &t.unit_kind.inner),
        spade_hir::symbol_table::Thing::Macro(_, _) => (format!("{name}"), format!("{name}!")),

        spade_hir::symbol_table::Thing::Variable(_)
        | spade_hir::symbol_table::Thing::Alias { .. }
        | spade_hir::symbol_table::Thing::ArrayLabel(_)
        | spade_hir::symbol_table::Thing::Module(_, _)
        | spade_hir::symbol_table::Thing::Trait(_)
        | spade_hir::symbol_table::Thing::Dummy => (format!("{name}"), format!("{name}")),
    };

    CompletionData {
        kind: kind,
        label,
        snippet: snippet,
    }
}
