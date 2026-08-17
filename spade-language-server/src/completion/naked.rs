use itertools::Itertools;
use spade_common::name::NameID;
use spade_hir::{
    symbol_table::{SymbolTable, Thing, ThingOrType, TypeDeclKind, TypeSymbol},
    ParameterList, UnitKind,
};
use tower_lsp::lsp_types::{
    CompletionItem, CompletionItemKind, CompletionItemLabelDetails, CompletionResponse,
    InsertTextFormat, Position, Url,
};

use crate::{
    backend::ServerBackend,
    completion::{ParamListExt, SnippetBuilder},
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
                .things_and_types()
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
                        ThingOrType::Thing(thing) => match thing {
                            Thing::Variable(_) => true,

                            Thing::Struct(_)
                            | Thing::EnumVariant(_)
                            | Thing::Unit(_)
                            | Thing::Alias { .. }
                            | Thing::ArrayLabel(_)
                            | Thing::Module(_, _)
                            | Thing::Macro(_, _)
                            | Thing::Trait(_)
                            | Thing::Dummy => false,
                        },
                        ThingOrType::Type(
                            TypeSymbol::GenericArg { .. } | TypeSymbol::GenericMeta(_),
                        ) => true,
                        ThingOrType::Type(_) => false,
                    };

                    // We don't want to complete enum variants unless they are explicitly imported
                    // with an alias
                    if let ThingOrType::Thing(Thing::EnumVariant(_)) = thing {
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

                    // Massive hack to get rid of a bunch of false positive Self parameters
                    if local_name == "Self" {
                        return None
                    }
                    
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
    thing: &ThingOrType,
) -> Option<(NameID, spade_hir::symbol_table::ThingOrType<'a>)> {
    match thing {
        ThingOrType::Thing(thing) => match thing {
            Thing::Alias {
                loc: _,
                path,
                in_namespace: _,
            } => symtab
                .lookup_thing(path, true)
                .ok()
                .and_then(|(name, thing)| {
                    match follow_aliases(symtab, &ThingOrType::Thing(thing)) {
                        None => Some((name, ThingOrType::Thing(thing))),
                        Some((name, t)) => Some((name, t)),
                    }
                })
                .or_else(|| {
                    symtab
                        .lookup_type_symbol(path, true)
                        .ok()
                        .map(|(name, ty)| (name, ThingOrType::Type(ty)))
                }),
            Thing::Struct(_)
            | Thing::EnumVariant(_)
            | Thing::Unit(_)
            | Thing::Variable(_)
            | Thing::ArrayLabel(_)
            | Thing::Module(_, _)
            | Thing::Macro(_, _)
            | Thing::Trait(_)
            | Thing::Dummy => None,
        },
        ThingOrType::Type(_) => None,
    }
}

pub(crate) struct CompletionData {
    pub kind: CompletionItemKind,
    pub label: String,
    pub snippet: String,
}

pub(crate) fn completion_data(name: &str, thing: &ThingOrType) -> CompletionData {
    let kind = match thing {
        ThingOrType::Thing(thing) => match thing {
            Thing::Struct(_) => CompletionItemKind::STRUCT,
            Thing::EnumVariant(_) => CompletionItemKind::ENUM,
            Thing::Unit(_) => CompletionItemKind::FUNCTION,
            Thing::Variable(_) => CompletionItemKind::VALUE,
            Thing::Alias { .. } => CompletionItemKind::REFERENCE,
            Thing::ArrayLabel(_) => CompletionItemKind::PROPERTY,
            Thing::Module(_, _) => CompletionItemKind::MODULE,
            Thing::Macro(_, _) => CompletionItemKind::FUNCTION,
            Thing::Trait(_) => CompletionItemKind::INTERFACE,
            Thing::Dummy => CompletionItemKind::MODULE,
        },
        ThingOrType::Type(ty) => match ty {
            TypeSymbol::Declared(_, _, TypeDeclKind::Struct) => CompletionItemKind::STRUCT,
            TypeSymbol::Declared(_, _, TypeDeclKind::Enum) => CompletionItemKind::ENUM,
            TypeSymbol::Declared(_, _, TypeDeclKind::Primitive { .. }) => {
                CompletionItemKind::STRUCT
            }
            TypeSymbol::Declared(_, _, TypeDeclKind::Alias) => CompletionItemKind::STRUCT,
            TypeSymbol::GenericArg { .. } => CompletionItemKind::TYPE_PARAMETER,
            TypeSymbol::GenericMeta { .. } => CompletionItemKind::TYPE_PARAMETER,
        },
    };

    let is_enum_variant = matches!(thing, ThingOrType::Thing(Thing::EnumVariant(_)));

    let mut sb = SnippetBuilder::new();
    let mut unit_like = |params: &ParameterList, _kind: &UnitKind| {
        // Ideally we'd insert `inst` here if it is required for the target unit. However,
        // we have to be careful doing so as we risk inserting double inst if the user
        // already did so manually, or we may insert `inst` into a path. For now, we'll err
        // on the side of reducing false positives in completion and just never insert inst
        // let (_inst_label, _inst_snippet) = kind.label_snippet(false, false, &mut sb);
        //
        let (arg_label, arg_snippet) = params.label_snippet(&mut sb, is_enum_variant, false);

        (format!("{name}{arg_label}"), format!("{name}{arg_snippet}"))
    };

    let (label, snippet) = match thing {
        ThingOrType::Thing(thing) => match thing {
            Thing::Struct(t) => unit_like(
                &t.params,
                &UnitKind::Function(spade_hir::FunctionKind::Struct),
            ),
            Thing::EnumVariant(t) => unit_like(
                &t.params,
                &UnitKind::Function(spade_hir::FunctionKind::Enum),
            ),
            Thing::Unit(t) => unit_like(&t.inputs, &t.unit_kind.inner),
            Thing::Macro(_, _) => (format!("{name}"), format!("{name}!")),

            Thing::Variable(_)
            | Thing::Alias { .. }
            | Thing::ArrayLabel(_)
            | Thing::Module(_, _)
            | Thing::Trait(_)
            | Thing::Dummy => (format!("{name}"), format!("{name}")),
        },
        ThingOrType::Type(_) => (format!("{name}"), format!("{name}")),
    };

    CompletionData {
        kind: kind,
        label,
        snippet: snippet,
    }
}
