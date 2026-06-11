use spade_hir::{
    expression::IncompleteExpression, query::Thing, symbol_table::SymbolTable, ParameterList,
    UnitKind,
};
use spade_typeinference::{
    equation::TypeVarID, method_resolution::methods_for_type, traits::TraitImplList, HasType,
    TypeState,
};
use tower_lsp::lsp_types::{
    CompletionItem, CompletionItemKind, CompletionResponse, InsertTextFormat, Position, Url,
};

use crate::{backend::ServerBackend, util::PositionDetails};

mod locals;
mod naked;

impl ServerBackend {
    pub async fn get_completions(&self, pos: &Position, uri: &Url) -> Option<CompletionResponse> {
        let pos_details = self.get_position_details(pos, uri)?;

        let mut results = if let Some(from_type) = self.get_type_completions(&pos_details).await {
            Some(from_type)
        } else {
            self.get_naked_completions(pos, uri).await
        };

        // Not at all required for functionality, but it makes tests more predictable
        match &mut results {
            Some(CompletionResponse::Array(inner)) => inner.sort_by(|l, r| l.label.cmp(&r.label)),
            _ => {}
        }
        results
    }

    async fn get_type_completions(
        &self,
        PositionDetails {
            loc,
            name: _,
            unit_type_state,
            current_unit: _,
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
                let info = match &thing.inner {
                    // FIXME: We can probably complete fields here
                    Thing::Pattern(_) => None,

                    Thing::Expr(expression) => {
                        match &expression.kind {
                            spade_hir::ExprKind::Error => None,

                            spade_hir::ExprKind::Incomplete(
                                _,
                                IncompleteExpression::IncompleteDot {
                                    base: target,
                                    has_depth,
                                    has_inst,
                                },
                            ) => Some((target, *has_inst, *has_depth)),
                            spade_hir::ExprKind::MethodCall {
                                target, call_kind, ..
                            } => Some(match call_kind {
                                spade_hir::expression::CallKind::Function => (target, false, false),
                                spade_hir::expression::CallKind::Entity(_) => (target, true, false),
                                spade_hir::expression::CallKind::Pipeline { .. } => {
                                    (target, true, true)
                                }
                            }),
                            spade_hir::ExprKind::FieldAccess(target, _) => {
                                Some((target, false, false))
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
                };

                info.and_then(|(target, has_inst, has_depth)| {
                    if !target.contains_start(loc) {
                        let ty = target.get_type(ts);

                        type_field_completions(
                            &ty,
                            &self.trait_impls.lock().unwrap(),
                            ts,
                            symtab.symtab(),
                            has_inst,
                            has_depth,
                        )
                    } else {
                        None
                    }
                })
            })
            .last()
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
    fn label_snippet(
        &self,
        has_inst: bool,
        has_depth: bool,
        snippet_builder: &mut SnippetBuilder,
    ) -> (String, String);
}
impl UnitKindExt for UnitKind {
    fn label_snippet(
        &self,
        has_inst: bool,
        has_depth: bool,
        snippet_builder: &mut SnippetBuilder,
    ) -> (String, String) {
        match self {
            spade_hir::UnitKind::Function(_) => ("".to_string(), "".to_string()),
            spade_hir::UnitKind::Entity => (
                "".to_string(),
                if !has_inst {
                    "inst ".to_string()
                } else {
                    "".to_string()
                },
            ),
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
                match (has_inst, has_depth) {
                    (false, false) => ("".to_string(), format!("inst({depth}) ")),
                    (true, false) => ("".to_string(), format!("({depth}) ")),
                    (true, true) => ("".to_string(), format!("")),

                    // NOTE: This should not occur in practice, we'll just return something that sort of works
                    (false, true) => ("".to_string(), "".to_string()),
                }
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
    has_inst: bool,
    has_depth: bool,
) -> Option<CompletionResponse> {
    let methods = methods_for_type(&trait_impls, &ty, type_state)
        .into_iter()
        .filter_map(|(method, fn_info)| {
            let actual_fn = symtab.unit_by_id(&fn_info.name);

            let mut snippet_builder = SnippetBuilder::new();
            let (inst_label, inst_snippet) =
                actual_fn
                    .unit_kind
                    .label_snippet(has_inst, has_depth, &mut snippet_builder);
            let (arg_label, arg_snippet) = actual_fn.inputs.label_snippet(&mut snippet_builder);

            let label = format!("{inst_label}{method}{arg_label}");
            let inserted = Some(format!("{inst_snippet}{method}{arg_snippet}"));

            Some(CompletionItem {
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
            })
        });

    let field_like = match ty.resolve(type_state) {
        spade_typeinference::equation::TypeVar::Known(_, known_type, params) => match known_type {
            spade_types::KnownType::Named(name) => match symtab.thing_by_id(&name) {
                Some(spade_hir::symbol_table::Thing::Struct(s)) => s
                    .params
                    .0
                    .iter()
                    .map(|param| {
                        let mut result = CompletionItem::new_simple(
                            format!("{}", param.name),
                            format!("{}", param.name),
                        );

                        result.kind = Some(CompletionItemKind::FIELD);

                        result
                    })
                    .collect(),
                _ => vec![],
            },
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
        spade_typeinference::equation::TypeVar::Unknown(_, _, _trait_list, _) => vec![],
    };

    Some(CompletionResponse::Array(
        methods.into_iter().chain(field_like).collect(),
    ))
}
