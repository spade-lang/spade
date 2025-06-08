use indoc::formatdoc;
use itertools::Itertools;
use spade_common::{location_info::Loc, name::NameID};
use spade_hir::{
    pretty_print::PrettyPrint,
    query::Thing,
    symbol_table::{self, StructCallable, TypeDeclKind},
    ExecutableItem, ExprKind,
};
use spade_typeinference::{
    equation::TypeVar, method_resolution::select_method, HasType, TypeState,
};
use tower_lsp::lsp_types::{Hover, HoverContents, Position, Url};

use crate::backend::ServerBackend;

struct HoverDetails {
    loc: Loc<()>,
    name: Option<Loc<NameID>>,
    unit_type_state: Option<TypeState>,
}

impl ServerBackend {
    fn prepare_hover(&self, pos: &Position, uri: &Url) -> Option<HoverDetails> {
        let Some(loc) = self.pos_uri_to_loc(pos, uri).ok() else {
            return None;
        };

        let name = self
            .query_cache
            .lock()
            .unwrap()
            .names_around(&loc)
            .last()
            .map(|loc| loc.map(|inner| inner.clone()));

        let current_unit = self
            .query_cache
            .lock()
            .unwrap()
            .things_around(&loc)
            .iter()
            .find_map(|thing| match thing.inner {
                Thing::Executable(ExecutableItem::Unit(u)) => Some(u),
                _ => None,
            })
            .cloned();

        let unit_type_state = current_unit.as_ref().and_then(|u| {
            self.type_states
                .lock()
                .unwrap()
                .get(u.name.name_id())
                .cloned()
        });

        Some(HoverDetails {
            loc,
            name,
            unit_type_state,
        })
    }

    fn symtab_thing_info(
        &self,
        HoverDetails {
            loc: _,
            name,
            unit_type_state,
        }: &HoverDetails,
    ) -> Option<String> {
        let Some(name) = name else { return None };
        let symtab = self.symtab.lock().unwrap();
        let Some(symtab) = symtab.as_ref() else {
            return None;
        };
        symtab.thing_by_id(&name.inner).map(|thing| match thing {
            symbol_table::Thing::Struct(s) => {
                let StructCallable {
                    name,
                    self_type: _,
                    params,
                    type_params,
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
                path,
                in_namespace: _,
            } => {
                format!("alias for {path}")
            }
            symbol_table::Thing::PipelineStage(_) => {
                format!("(pipeline stage)")
            }
            symbol_table::Thing::Module(_) => {
                format!("(module)")
            }
            symbol_table::Thing::Trait(_) => {
                format!("(trait)")
            }
        })
    }

    fn symtab_type_info(
        &self,
        HoverDetails {
            loc: _,
            name,
            unit_type_state: _,
        }: &HoverDetails,
    ) -> Option<String> {
        let Some(name) = name else { return None };
        let symtab = self.symtab.lock().unwrap();
        let Some(symtab) = symtab.as_ref() else {
            return None;
        };
        symtab
            .try_type_symbol_by_id(&name.inner)
            .map(|ts| match &ts.inner {
                symbol_table::TypeSymbol::Declared(generics, type_decl_kind) => {
                    let base = match type_decl_kind {
                        TypeDeclKind::Struct { is_port: true } => "struct port",
                        TypeDeclKind::Struct { is_port: false } => "struct",
                        TypeDeclKind::Enum => "enum",
                        TypeDeclKind::Primitive { is_port: _ } => "primitive type",
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
                symbol_table::TypeSymbol::Alias(aliased) => {
                    formatdoc!(r#"type {name} = {}"#, aliased.pretty_print())
                }
            })
    }

    fn hover_from_surrounding_thing(
        &self,
        HoverDetails {
            loc,
            name: _,
            unit_type_state,
        }: &HoverDetails,
    ) -> Option<String> {
        let qq = self.query_cache.lock().unwrap();
        let things_around = qq.things_around(loc);

        let type_info = things_around
            .iter()
            .filter_map(|thing| match &thing.inner {
                Thing::Expr(expr) => Some(expr),
                Thing::Pattern(_) | Thing::Statement(_) | Thing::Executable(_) => None,
            })
            // Filter out any expressions which are uninteresting to show the type for,
            // have the type info available in another hover info (such as the name)
            // or restrict the info to only parts of some expressions to avoid spurious
            // info
            .filter(|expr| expr.kind.is_hover_target(loc))
            .find_map(|expr| {
                unit_type_state.as_ref().and_then(|ts| {
                    let Some(self_ty) = expr.try_get_type(ts) else {
                        return None;
                    };

                    Some(format!(
                        "**Expression type**:\n```spade\n{}\n```",
                        self_ty.resolve(&ts).display(ts)
                    ))
                })
            });

        let struct_field_info = things_around
            .iter()
            .filter_map(|thing| match &thing.inner {
                Thing::Expr(expression) => Some((thing, expression)),
                Thing::Pattern(_) | Thing::Statement(_) | Thing::Executable(_) => None,
            })
            .find_map(|(thing, expr)| match &expr.kind {
                ExprKind::FieldAccess(base, field) => {
                    if field.contains_start(loc) {
                        unit_type_state.as_ref().and_then(|ts| {
                            let symtab = self.symtab.lock().unwrap();
                            let Some(symtab) = symtab.as_ref() else {
                                return None;
                            };

                            let Some(target_ty) = base.try_get_type(ts) else {
                                return None;
                            };

                            let TypeVar::Known(_, spade_types::KnownType::Named(name), _) =
                                target_ty.resolve(ts)
                            else {
                                return None;
                            };

                            let s = symtab.struct_by_id(name);

                            let Some(param) = s.params.0.iter().find(|p| &p.name == field) else {
                                return None;
                            };

                            Some(format!("{}: {}", param.name, param.ty.pretty_print()))
                        })
                    } else {
                        None
                    }
                }
                ExprKind::MethodCall {
                    target,
                    name,
                    args: _,
                    call_kind: _,
                    turbofish: _,
                } => {
                    if name.contains_start(loc) {
                        unit_type_state.as_ref().and_then(|ts| {
                            let Some(target_ty) = target.try_get_type(ts) else {
                                return None;
                            };

                            select_method(
                                thing.loc(),
                                &target_ty,
                                name,
                                &self.trait_impls.lock().unwrap(),
                                ts,
                            )
                            .ok()
                            .flatten()
                            .and_then(|callee| {
                                let symtab = self.symtab.lock().unwrap();
                                let Some(symtab) = symtab.as_ref() else {
                                    return None;
                                };
                                let target_unit = symtab.unit_by_id(&callee.inner);
                                let result = formatdoc!(
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
                                );
                                Some(result)
                            })
                        })
                    } else {
                        None
                    }
                }
                _ => None,
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
        let hover_details = self.prepare_hover(pos, uri)?;

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
            } => name.contains_start(loc),
            ExprKind::Call {
                kind: _,
                callee,
                args: _,
                turbofish: _,
            } => callee.contains_start(loc),
            ExprKind::BinaryOperator(_, op, _) => op.contains_start(loc),

            ExprKind::Identifier(_)
            | ExprKind::Match(_, _)
            | ExprKind::If(_, _, _)
            | ExprKind::TypeLevelIf(_, _, _)
            | ExprKind::BoolLiteral(_)
            | ExprKind::BitLiteral(_)
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
