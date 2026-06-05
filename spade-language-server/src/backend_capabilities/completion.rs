use itertools::Itertools;
use spade_common::name::NameID;
use spade_hir::{query::Thing, symbol_table::SymbolTable, ParameterList, UnitKind};
use spade_typeinference::{
    equation::TypeVarID, method_resolution::methods_for_type, traits::TraitImplList, HasType,
    TypeState,
};
use tower_lsp::lsp_types::{
    CompletionItem, CompletionItemKind, CompletionItemLabelDetails, CompletionResponse,
    InsertTextFormat, Position, Url,
};

use crate::{backend::ServerBackend, backend_capabilities::util::PositionDetails};

pub trait CompletionInfo {
    async fn get_completions(&self, pos: &Position, uri: &Url) -> Option<CompletionResponse>;

    async fn get_naked_completions(&self, pos: &Position, uri: &Url) -> Option<CompletionResponse>;

    async fn get_type_completions(&self, pos: &PositionDetails) -> Option<CompletionResponse>;
}

impl CompletionInfo for ServerBackend {
    async fn get_completions(&self, pos: &Position, uri: &Url) -> Option<CompletionResponse> {
        let pos_details = self.get_position_details(pos, uri)?;

        if let Some(from_type) = self.get_type_completions(&pos_details).await {
            Some(from_type)
        } else {
            self.get_naked_completions(pos, uri).await
        }
    }

    async fn get_type_completions(
        &self,
        PositionDetails {
            loc,
            name: _,
            unit_type_state,
        }: &PositionDetails,
    ) -> Option<CompletionResponse> {
        let Some(ts) = unit_type_state else {
            return None;
        };
        let Some(symtab) = &*self.symtab.lock().unwrap() else {
            return None;
        };

        let qq = self.query_cache.lock().unwrap();
        let things_around = qq.things_around(loc);

        things_around
            .iter()
            .filter_map(|thing| {
                match &thing.inner {
                    // FIXME: We can probably complete fields here
                    Thing::Pattern(_) => None,

                    Thing::Expr(expression) => {
                        match &expression.kind {
                            spade_hir::ExprKind::Error => None,

                            spade_hir::ExprKind::IncompleteDot { base: target }
                            | spade_hir::ExprKind::MethodCall { target, .. }
                            | spade_hir::ExprKind::FieldAccess(target, _) => {
                                if !target.contains_start(loc) {
                                    let ty = target.get_type(ts);

                                    type_field_completions(
                                        &ty,
                                        &self.trait_impls.lock().unwrap(),
                                        ts,
                                        symtab.symtab(),
                                    )
                                } else {
                                    None
                                }
                            }

                            // For identifiers we can just use naked completion
                            spade_hir::ExprKind::Identifier(_)
                            | spade_hir::ExprKind::IntLiteral(_, _)
                            | spade_hir::ExprKind::BoolLiteral(_)
                            | spade_hir::ExprKind::TriLiteral(_)
                            | spade_hir::ExprKind::TypeLevelBool(_)
                            | spade_hir::ExprKind::TypeLevelInteger(_)
                            | spade_hir::ExprKind::TupleLiteral(_)
                            | spade_hir::ExprKind::ArrayLiteral(_)
                            | spade_hir::ExprKind::ArrayShorthandLiteral(_, _)
                            | spade_hir::ExprKind::Index(_, _)
                            | spade_hir::ExprKind::RangeIndex { .. }
                            | spade_hir::ExprKind::TupleIndex(_, _)
                            | spade_hir::ExprKind::TypeCast(_, _)
                            | spade_hir::ExprKind::Call { .. }
                            | spade_hir::ExprKind::BinaryOperator(_, _, _)
                            | spade_hir::ExprKind::UnaryOperator(_, _)
                            | spade_hir::ExprKind::Match(_, _)
                            | spade_hir::ExprKind::Block(_)
                            | spade_hir::ExprKind::If { .. }
                            | spade_hir::ExprKind::TypeLevelIf { .. }
                            | spade_hir::ExprKind::PipelineRef { .. }
                            | spade_hir::ExprKind::LambdaDef { .. }
                            | spade_hir::ExprKind::StageValid
                            | spade_hir::ExprKind::StageReady
                            | spade_hir::ExprKind::StaticUnreachable(_)
                            | spade_hir::ExprKind::Null => None,
                        }
                    }
                    // Naked is fine for now
                    Thing::Statement(_) => None,
                    // Naked is fine for now
                    Thing::Executable(_) => None,
                }
            })
            .last()
    }

    async fn get_naked_completions(&self, pos: &Position, uri: &Url) -> Option<CompletionResponse> {
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
                            if !thing_name.1.starts_with(&this_unit.1.prelude()) {
                                return None;
                            }
                        } else {
                            return None;
                        }
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

                    let CompletionData { kind, label, snippet } = completion_data(&local_name, thing);
                    
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
                        insert_text: snippet,
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

struct CompletionData {
    kind: CompletionItemKind,
    label: String,
    snippet: Option<String>,
}

fn completion_data(name: &str, thing: &spade_hir::symbol_table::Thing) -> CompletionData {
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

    let mut sb = SnippetBuilder::new();
    let mut unit_like = |params: &ParameterList, kind: &UnitKind| {
        let (inst_label, inst_snippet) = kind.label_snippet(&mut sb);
        let (arg_label, arg_snippet) = params.label_snippet(&mut sb);

        (format!("{inst_label}{name}{arg_label}"), Some(format!("{inst_snippet}{name}{arg_snippet}")))
    };

    let (label, snippet) = match thing {
        spade_hir::symbol_table::Thing::Struct(t) => unit_like(
            &t.params,
            &UnitKind::Function(spade_hir::FunctionKind::Struct),
        ),
        spade_hir::symbol_table::Thing::EnumVariant(t) => {
            unit_like(&t.params, &UnitKind::Function(spade_hir::FunctionKind::Enum))
        }
        spade_hir::symbol_table::Thing::Unit(t) => unit_like(&t.inputs, &t.unit_kind.inner),
        spade_hir::symbol_table::Thing::Macro(_, _) => {
            (format!("{name}"), None)
        }

        spade_hir::symbol_table::Thing::Variable(_)
        | spade_hir::symbol_table::Thing::Alias {
            ..
        }
        | spade_hir::symbol_table::Thing::ArrayLabel(_)
        | spade_hir::symbol_table::Thing::Module(_, _)
        | spade_hir::symbol_table::Thing::Trait(_)
        | spade_hir::symbol_table::Thing::Dummy => (format!("{name}"), None)
    };

    CompletionData { kind: kind, label, snippet: snippet }
}

fn follow_aliases<'a>(
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

struct SnippetBuilder {
    placeholder_idx: u64,
}

impl SnippetBuilder {
    fn new() -> Self {
        Self { placeholder_idx: 1 }
    }
    fn next(&mut self) -> u64 {
        let result = self.placeholder_idx;
        self.placeholder_idx += 1;
        result
    }
}

trait UnitKindExt {
    fn label_snippet(&self, snippet_builder: &mut SnippetBuilder) -> (String, String);
}
impl UnitKindExt for UnitKind {
    fn label_snippet(&self, snippet_builder: &mut SnippetBuilder) -> (String, String) {
        match self {
            spade_hir::UnitKind::Function(_) => ("".to_string(), "".to_string()),
            spade_hir::UnitKind::Entity => ("".to_string(), "inst ".to_string()),
            spade_hir::UnitKind::Pipeline {
                depth,
                depth_typeexpr_id: _,
            } => {
                let depth = match &depth.inner {
                    spade_hir::TypeExpression::Integer(val) => format!("{val}"),
                    spade_hir::TypeExpression::Bool(_)
                    | spade_hir::TypeExpression::String(_)
                    | spade_hir::TypeExpression::TypeSpec(_)
                    | spade_hir::TypeExpression::ConstGeneric(_) => {
                        format!("${{{}}}", snippet_builder.next())
                    }
                };
                ("".to_string(), format!("inst({depth}) "))
            }
        }
    }
}

trait ParamListExt {
    fn label_snippet(&self, snippet_builder: &mut SnippetBuilder) -> (String, String);
}
impl ParamListExt for ParameterList {
    fn label_snippet(&self, snippet_builder: &mut SnippetBuilder) -> (String, String) {
        if self.0.len() == 1 {
            (format!("()"), format!("()$0"))
        } else {
            (
                format!("(…)"),
                format!("(${{{}}})$0", snippet_builder.next()),
            )
        }
    }
}

fn type_field_completions(
    ty: &TypeVarID,
    trait_impls: &TraitImplList,
    type_state: &TypeState,
    symtab: &SymbolTable,
) -> Option<CompletionResponse> {
    let methods = methods_for_type(&trait_impls, &ty, type_state)
        .into_iter()
        .map(|(method, fn_info)| {
            let actual_fn = symtab.unit_by_id(&fn_info.name);

            let mut snippet_builder = SnippetBuilder::new();
            let (inst_label, inst_snippet) =
                actual_fn.unit_kind.label_snippet(&mut snippet_builder);
            let (arg_label, arg_snippet) = actual_fn.inputs.label_snippet(&mut snippet_builder);

            let label = format!("{inst_label}{method}{arg_label}");
            let inserted = Some(format!("{inst_snippet}{method}{arg_snippet}"));

            CompletionItem {
                label: label,
                label_details: None,
                kind: Some(CompletionItemKind::FUNCTION),
                detail: None,
                documentation: Some(tower_lsp::lsp_types::Documentation::MarkupContent(
                    tower_lsp::lsp_types::MarkupContent {
                        kind: tower_lsp::lsp_types::MarkupKind::Markdown,
                        value: actual_fn.documentation.clone(),
                    },
                )),
                deprecated: Some(actual_fn.deprecation_note.is_some()),
                preselect: None,
                sort_text: None,
                filter_text: None,
                insert_text: inserted,
                insert_text_format: Some(InsertTextFormat::SNIPPET),
                insert_text_mode: None,
                text_edit: None,
                additional_text_edits: None,
                command: None,
                commit_characters: None,
                data: None,
                tags: None,
            }
        });

    let field_like = match ty.resolve(type_state) {
        spade_typeinference::equation::TypeVar::Known(_, known_type, params) => match known_type {
            // TODO
            spade_types::KnownType::Named(_) => vec![],
            spade_types::KnownType::Array => vec![],
            spade_types::KnownType::Inverted => vec![],
            spade_types::KnownType::CopyView => vec![],
            spade_types::KnownType::Error => vec![],

            spade_types::KnownType::Tuple => params
                .iter()
                .enumerate()
                .map(|(i, param)| {
                    CompletionItem::new_simple(
                        format!("{i}"),
                        param.debug_resolve(type_state).to_string(),
                    )
                })
                .collect(),

            spade_types::KnownType::Integer(_) => vec![],
            spade_types::KnownType::Bool(_) => vec![],
            spade_types::KnownType::String(_) => vec![],
        },
        // TODO: Here we can complete methods
        spade_typeinference::equation::TypeVar::Unknown(_, _, _trait_list, _) => vec![],
    };

    Some(CompletionResponse::Array(
        methods.into_iter().chain(field_like).collect(),
    ))
}
