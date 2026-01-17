use indoc::formatdoc;
use itertools::Itertools;
use spade_common::location_info::Loc;
use spade_hir::{
    pretty_print::PrettyPrint,
    symbol_table::{self, StructCallable, TypeDeclKind},
    ExprKind,
};
use spade_typeinference::HasType;
use tower_lsp::lsp_types::{Hover, HoverContents, Position, Url};

use crate::backend::ServerBackend;

use super::util::{FieldInfo, PositionDetails};

impl ServerBackend {
    fn symtab_thing_info(
        &self,
        PositionDetails {
            loc: _,
            name,
            unit_type_state,
        }: &PositionDetails,
    ) -> Option<String> {
        let Some(name) = name else { return None };
        let symtab = self.symtab.lock().unwrap();
        let Some(symtab) = symtab.as_ref() else {
            return None;
        };
        symtab
            .symtab()
            .thing_by_id(&name.inner)
            .map(|thing| match thing {
                symbol_table::Thing::Struct(s) => {
                    let StructCallable {
                        name,
                        self_type: _,
                        params,
                        type_params,
                        deprecation_note: _,
                    } = &s.inner;
                    formatdoc!(
                        r#"
                        struct {}{}{{
                            {}
                        }}"#,
                        name,
                        if type_params.is_empty() {
                            "".to_string()
                        } else {
                            format!(
                                "<{}>",
                                type_params.iter().map(|tp| tp.pretty_print()).join(", ")
                            )
                        },
                        params
                            .0
                            .iter()
                            .map(PrettyPrint::pretty_print)
                            .join("\n    ")
                    )
                }
                symbol_table::Thing::EnumVariant(variant) => formatdoc!(
                    r#"enum variant
                    ```spade
                    {}
                    ```{}"#,
                    if variant.params.0.is_empty() {
                        name.to_string()
                    } else {
                        formatdoc!(
                            r#"{}{{
                                {}
                            }}"#,
                            name,
                            variant.params.pretty_print()
                        )
                    },
                    if variant.documentation != "" {
                        format!("\n---\n{}", variant.documentation)
                    } else {
                        "".to_string()
                    }
                ),
                symbol_table::Thing::Unit(u) => {
                    formatdoc!(
                        r#"
                            ```spade
                            {}
                            ```{}"#,
                        u.pretty_print(),
                        if !u.documentation.is_empty() {
                            format!("\n---\n{}", u.documentation.trim())
                        } else {
                            "".to_string()
                        }
                    )
                }
                symbol_table::Thing::Variable(var) => {
                    let ty = unit_type_state
                        .as_ref()
                        .and_then(|ts| name.try_get_type(ts).map(|ty| ty.resolve(&ts).display(ts)))
                        .map(|ty| format!(": {ty}"))
                        .unwrap_or_else(|| ": ?".to_string());

                    formatdoc!(
                        r#"
                        ```spade
                        let {var}{ty}
                        ```"#
                    )
                }
                symbol_table::Thing::Alias {
                    loc: _,
                    path,
                    in_namespace: _,
                } => {
                    format!("alias for {path}")
                }
                symbol_table::Thing::ArrayLabel(value) => {
                    format!("Array label: {value}")
                }
                symbol_table::Thing::Module(_, _) => {
                    format!("(module)")
                }
                symbol_table::Thing::Trait(_) => {
                    format!("(trait)")
                }
                symbol_table::Thing::Dummy => {
                    format!("(dummy)")
                }
            })
    }

    fn symtab_type_info(
        &self,
        PositionDetails {
            loc: _,
            name,
            unit_type_state: _,
        }: &PositionDetails,
    ) -> Option<String> {
        let Some(name) = name else { return None };
        let symtab = self.symtab.lock().unwrap();
        let Some(symtab) = symtab.as_ref() else {
            return None;
        };
        symtab
            .symtab()
            .try_type_symbol_by_id(&name.inner)
            .map(|ts| match &ts.inner {
                symbol_table::TypeSymbol::Declared(generics, _, type_decl_kind) => {
                    let base = match type_decl_kind {
                        TypeDeclKind::Struct { is_port: true } => "struct port",
                        TypeDeclKind::Struct { is_port: false } => "struct",
                        TypeDeclKind::Enum => "enum",
                        TypeDeclKind::Primitive { .. } => "primitive type",
                        TypeDeclKind::Alias { .. } => "type alias",
                    };

                    let generics = match generics.as_slice() {
                        [] => format!(""),
                        gen => gen.iter().map(|g| g.pretty_print()).join("{}"),
                    };

                    formatdoc!(
                        r#"
                        ```spade
                        {base} {name}{generics}
                        ````"#
                    )
                }
                symbol_table::TypeSymbol::GenericArg { traits } => {
                    let trait_info = if traits.is_empty() {
                        "".to_string()
                    } else {
                        format!(
                            " with traits {}",
                            traits.iter().map(PrettyPrint::pretty_print).join(" + ")
                        )
                    };
                    formatdoc!(r#" Generic argument`{trait_info}` "#)
                }
                symbol_table::TypeSymbol::GenericMeta(meta) => {
                    format!("{meta}")
                }
            })
    }

    fn hover_from_surrounding_thing(
        &self,
        pos @ PositionDetails {
            loc,
            name: _,
            unit_type_state,
        }: &PositionDetails,
    ) -> Option<String> {
        let Some(ts) = unit_type_state else {
            return None;
        };
        let info = self.contextual_expression_info(pos);

        let type_info = info
            .expression
            .iter()
            .filter(|(expr, _ty)| expr.kind.is_hover_target(loc))
            .find_map(|(_expr, ty)| {
                Some(format!(
                    "**Expression type**:\n```spade\n{}\n```",
                    ty.resolve(&ts).display(ts)
                ))
            });

        let struct_field_info = info.field.map(|fi| match fi {
            FieldInfo::Field {
                name,
                st: _,
                field_ty: ty,
            } => format!("{}: {}", name, ty.pretty_print()),
            FieldInfo::Method {
                target_unit,
                target_ty,
            } => formatdoc!(
                r#"
                    ```spade
                    impl{} {}
                    {}
                    ```{}"#,
                if !target_unit.scope_type_params.is_empty() {
                    formatdoc!(
                        "<{}>",
                        target_unit
                            .scope_type_params
                            .iter()
                            .map(PrettyPrint::pretty_print)
                            .join(", ")
                    )
                } else {
                    "".to_string()
                },
                target_ty.display(ts),
                target_unit.pretty_print(),
                if !target_unit.documentation.is_empty() {
                    format!("\n---\n{}", target_unit.documentation)
                } else {
                    "".to_string()
                }
            ),
        });

        let s = [type_info, struct_field_info]
            .into_iter()
            .flatten()
            .join("\n---\n");
        if s.is_empty() {
            None
        } else {
            Some(s)
        }
    }
}

pub trait HoverInfo {
    async fn find_hover(&self, pos: &Position, uri: &Url) -> Option<Hover>;
}

impl HoverInfo for ServerBackend {
    async fn find_hover(&self, pos: &Position, uri: &Url) -> Option<Hover> {
        let hover_details = self.get_position_details(pos, uri)?;

        let from_symtab = self
            .symtab_thing_info(&hover_details)
            .or_else(|| self.symtab_type_info(&hover_details));

        let from_surrounding_thing = self.hover_from_surrounding_thing(&hover_details);

        let s = [from_symtab, from_surrounding_thing]
            .into_iter()
            .flatten()
            .join("\n---\n");

        if s.is_empty() {
            None
        } else {
            Some(Hover {
                contents: HoverContents::Markup(tower_lsp::lsp_types::MarkupContent {
                    kind: tower_lsp::lsp_types::MarkupKind::Markdown,
                    value: s,
                }),
                range: None,
            })
        }
    }
}

trait ExprKindExt {
    fn is_hover_target(&self, loc: &Loc<()>) -> bool;
}

impl ExprKindExt for ExprKind {
    fn is_hover_target(&self, loc: &Loc<()>) -> bool {
        match &self {
            ExprKind::IntLiteral(_, _) => true,
            ExprKind::TypeLevelInteger(_) => true,
            ExprKind::CreatePorts => true,
            ExprKind::MethodCall {
                target: _,
                name,
                args: _,
                call_kind: _,
                turbofish: _,
                safety: _,
            } => name.contains_start(loc),
            ExprKind::Call {
                kind: _,
                callee,
                args: _,
                turbofish: _,
                safety: _,
                verilog_attr_groups: _,
            } => callee.contains_start(loc),
            ExprKind::BinaryOperator(_, op, _) => op.contains_start(loc),

            ExprKind::Error => false,

            ExprKind::Identifier(_)
            | ExprKind::Match(_, _)
            | ExprKind::If(_, _, _)
            | ExprKind::TypeLevelIf(_, _, _)
            | ExprKind::BoolLiteral(_)
            | ExprKind::TypeLevelBool(_)
            | ExprKind::TriLiteral(_)
            | ExprKind::TupleLiteral(_)
            | ExprKind::ArrayLiteral(_)
            | ExprKind::ArrayShorthandLiteral(_, _)
            | ExprKind::Index(_, _)
            | ExprKind::RangeIndex { .. }
            | ExprKind::TupleIndex(_, _)
            | ExprKind::FieldAccess(_, _)
            | ExprKind::UnaryOperator(_, _)
            | ExprKind::Block(_)
            | ExprKind::PipelineRef { .. }
            | ExprKind::LambdaDef { .. }
            | ExprKind::StageValid
            | ExprKind::StageReady
            | ExprKind::StaticUnreachable(_)
            | ExprKind::Null => false,
        }
    }
}
