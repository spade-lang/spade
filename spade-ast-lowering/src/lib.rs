mod attributes;
pub mod builtins;
pub mod error;
pub mod global_symbols;
mod impls;
mod lambda;
pub mod pipelines;
pub mod testutil;
mod type_alias;
mod type_level_if;
pub mod types;

use std::sync::{Arc, Mutex};

use attributes::LocAttributeExt;
use global_symbols::visit_meta_type;
use impls::visit_impl;
use itertools::Itertools;
use lambda::visit_lambda;
use num::{BigInt, FromPrimitive, Zero};
use pipelines::PipelineContext;
use recursive::recursive;
use spade_diagnostics::codespan::Span;
use spade_diagnostics::diag_list::{DiagList, ResultExt};
use spade_diagnostics::diagnostic::SuggestionParts;
use spade_diagnostics::{diag_anyhow, diag_bail, Diagnostic};
use spade_hir::expression::Safety;
use spade_types::meta_types::MetaType;
use tracing::{event, Level};
use type_level_if::expand_type_level_if;

use crate::attributes::AttributeListExt;
pub use crate::impls::ensure_unique_anonymous_traits;
use crate::pipelines::maybe_perform_pipelining_tasks;
use crate::types::{IsInOut, IsPort, IsSelf};
use ast::{Binding, CallKind, ParameterList};
use hir::expression::{BinaryOperator, IntLiteralKind};
use hir::param_util::ArgumentError;
use hir::symbol_table::DeclarationState;
use hir::symbol_table::{LookupError, SymbolTable, Thing, TypeSymbol};
use hir::{ConstGeneric, ExecutableItem, PatternKind, TraitName, WalTrace};
use rustc_hash::FxHashSet as HashSet;
use spade_ast::{self as ast, Attribute, Expression, TypeParam, WhereClause};
pub use spade_common::id_tracker;
use spade_common::id_tracker::{ExprIdTracker, GenericID, GenericIdTracker, ImplIdTracker};
use spade_common::location_info::{FullSpan, Loc, WithLocation};
use spade_common::name::{Identifier, Path, PathSegment, Visibility};
use spade_hir::{
    self as hir, ExprKind, Generic, ItemList, Module, TraitSpec, TypeExpression, TypeSpec,
};

use error::Result;

#[derive(Debug)]
pub struct Context {
    pub symtab: SymbolTable,
    pub item_list: ItemList,
    pub idtracker: Arc<ExprIdTracker>,
    pub impl_idtracker: ImplIdTracker,
    pub generic_idtracker: GenericIdTracker,
    pub pipeline_ctx: Option<PipelineContext>,
    pub self_ctx: SelfContext,
    pub current_unit: Option<hir::UnitHead>,
    pub diags: Arc<Mutex<DiagList>>,
    pub safety: Safety,
}

impl Context {
    fn in_fresh_unit<T>(&mut self, transform: impl FnOnce(&mut Context) -> T) -> T {
        let mut tmp_pipeline_ctx = None;
        let mut tmp_self_ctx = SelfContext::FreeStanding;
        let mut tmp_current_unit = None;
        {
            let Context {
                symtab: _,
                item_list: _,
                idtracker: _,
                impl_idtracker: _,
                generic_idtracker: _,
                pipeline_ctx,
                self_ctx,
                current_unit,
                diags: _,
                safety: _,
            } = self;
            std::mem::swap(pipeline_ctx, &mut tmp_pipeline_ctx);
            std::mem::swap(self_ctx, &mut tmp_self_ctx);
            std::mem::swap(current_unit, &mut tmp_current_unit);
        }
        let result = transform(self);
        {
            let Context {
                symtab: _,
                item_list: _,
                idtracker: _,
                impl_idtracker: _,
                generic_idtracker: _,
                pipeline_ctx,
                self_ctx,
                current_unit,
                diags: _,
                safety: _,
            } = self;
            std::mem::swap(pipeline_ctx, &mut tmp_pipeline_ctx);
            std::mem::swap(self_ctx, &mut tmp_self_ctx);
            std::mem::swap(current_unit, &mut tmp_current_unit);
        }
        result
    }

    pub fn in_named_namespace<T>(
        &mut self,
        new_ident: Loc<Identifier>,
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        self.symtab.push_namespace(PathSegment::Named(new_ident));
        let result = f(self);
        self.symtab.pop_namespace();
        result
    }

    pub fn in_new_scope<T>(&mut self, f: impl Fn(&mut Self) -> T) -> T {
        self.symtab.new_scope();
        let result = f(self);
        self.symtab.close_scope();
        result
    }
}

trait LocExt<T> {
    fn try_visit<V, U>(&self, visitor: V, context: &mut Context) -> Result<Loc<U>>
    where
        V: Fn(&T, &mut Context) -> Result<U>;

    fn visit<V, U>(&self, visitor: V, context: &mut Context) -> Loc<U>
    where
        V: Fn(&T, &mut Context) -> U;
}

impl<T> LocExt<T> for Loc<T> {
    fn try_visit<V, U>(&self, visitor: V, context: &mut Context) -> Result<Loc<U>>
    where
        V: Fn(&T, &mut Context) -> Result<U>,
    {
        self.map_ref(|t| visitor(t, context)).map_err(|e, _| e)
    }

    fn visit<V, U>(&self, visitor: V, context: &mut Context) -> Loc<U>
    where
        V: Fn(&T, &mut Context) -> U,
    {
        self.map_ref(|t| visitor(t, context))
    }
}

/// Visit an AST type parameter, converting it to a HIR type parameter and adding it
/// to the symbol table
#[tracing::instrument(skip_all, fields(name=%param.name()))]
pub fn visit_type_param(param: &ast::TypeParam, ctx: &mut Context) -> Result<hir::TypeParam> {
    match &param {
        ast::TypeParam::TypeName {
            name: ident,
            traits,
            default,
        } => {
            let trait_bounds: Vec<Loc<TraitSpec>> = traits
                .iter()
                .map(|t| visit_trait_spec(t, &TypeSpecKind::TraitBound, ctx))
                .collect::<Result<_>>()?;

            let name_id = ctx.symtab.add_type(
                ident.clone(),
                TypeSymbol::GenericArg {
                    traits: trait_bounds.clone(),
                }
                .at_loc(ident),
                Visibility::Implicit.nowhere(),
                None,
            );

            let default = visit_default_type_expression(default, ctx)?;

            Ok(hir::TypeParam {
                name: Generic::Named(name_id.at_loc(ident)),
                trait_bounds,
                meta: MetaType::Type,
                default: default.map(Box::new),
            })
        }
        ast::TypeParam::TypeWithMeta {
            meta,
            name,
            default,
        } => {
            let meta = visit_meta_type(meta)?;
            let name_id = ctx.symtab.add_type(
                name.clone(),
                TypeSymbol::GenericMeta(meta.clone()).at_loc(name),
                Visibility::Implicit.nowhere(),
                None,
            );

            let default = visit_default_type_expression(default, ctx)?;

            Ok(hir::TypeParam {
                name: Generic::Named(name_id.at_loc(name)),
                trait_bounds: vec![],
                meta,
                default: default.map(Box::new),
            })
        }
    }
}

/// Visit an AST type parameter, converting it to a HIR type parameter. The name is not
/// added to the symbol table as this function is re-used for both global symbol collection
/// and normal HIR lowering.
#[tracing::instrument(skip_all, fields(name=%param.name()))]
pub fn re_visit_type_param(param: &ast::TypeParam, ctx: &mut Context) -> Result<hir::TypeParam> {
    match &param {
        ast::TypeParam::TypeName {
            name: ident,
            traits: _,
            default,
        } => {
            let path = Path::ident(ident.clone()).at_loc(ident);
            let (name_id, tsym) = ctx.symtab.lookup_type_symbol(&path, true)?;

            let trait_bounds = match &tsym.inner {
                TypeSymbol::GenericArg { traits } => traits.clone(),
                _ => return Err(Diagnostic::bug(
                    ident,
                    format!(
                        "Trait bound on {ident} on non-generic argument, which should've been caught by the first pass"
                    ),
                ))
            };

            let default = visit_default_type_expression(default, ctx)?;

            Ok(hir::TypeParam {
                name: Generic::Named(name_id.at_loc(&ident)),
                trait_bounds,
                meta: MetaType::Type,
                default: default.map(Box::new),
            })
        }
        ast::TypeParam::TypeWithMeta {
            meta,
            name,
            default,
        } => {
            let path = Path::ident(name.clone()).at_loc(name);
            let name_id = ctx.symtab.lookup_type_symbol(&path, false)?.0;
            let default = visit_default_type_expression(default, ctx)?;

            Ok(hir::TypeParam {
                name: Generic::Named(name_id.at_loc(&name)),
                trait_bounds: vec![],
                meta: visit_meta_type(meta)?,
                default: default.map(Box::new),
            })
        }
    }
}

/// The context in which a type expression occurs. This controls what hir::TypeExpressions an
/// ast::TypeExpression can be lowered to
pub enum TypeSpecKind {
    Argument,
    OutputType,
    EnumMember,
    StructMember,
    ImplTrait,
    ImplTarget,
    BindingType,
    Turbofish,
    PipelineHeadDepth,
    PipelineRegCount,
    PipelineInstDepth,
    TraitBound,
    TypeLevelIf,
}

fn visit_default_type_expression(
    default: &Option<Loc<ast::TypeExpression>>,
    ctx: &mut Context,
) -> Result<Option<Loc<hir::TypeExpression>>> {
    default
        .as_ref()
        .map(|d| Ok(visit_type_expression(d, &TypeSpecKind::TraitBound, ctx)?.at_loc(d)))
        .transpose()
}

#[recursive]
pub fn visit_type_expression(
    expr: &ast::TypeExpression,
    kind: &TypeSpecKind,
    ctx: &mut Context,
) -> Result<hir::TypeExpression> {
    match expr {
        ast::TypeExpression::TypeSpec(spec) => {
            let inner = visit_type_spec(spec, kind, ctx)?;
            // Look up the type. For now, we'll panic if we don't find a concrete type
            Ok(hir::TypeExpression::TypeSpec(inner.inner))
        }
        ast::TypeExpression::Integer(val) => Ok(hir::TypeExpression::Integer(val.clone())),
        ast::TypeExpression::String(val) => Ok(hir::TypeExpression::String(val.clone())),
        ast::TypeExpression::ConstGeneric(expr) => {
            let default_error = |message, primary| {
                Err(Diagnostic::error(
                    expr.as_ref(),
                    format!("{message} cannot have const generics in their type"),
                )
                .primary_label(format!("Const generic in {primary}")))
            };
            match kind {
                TypeSpecKind::ImplTrait => default_error("Implemented traits", "implemented trait"),
                TypeSpecKind::ImplTarget => default_error("Impl targets", "impl target"),
                TypeSpecKind::EnumMember => default_error("Enum members", "enum member"),
                TypeSpecKind::StructMember => default_error("Struct members", "struct member"),
                TypeSpecKind::TraitBound => {
                    default_error("Traits used in trait bounds", "trait bound")
                }
                TypeSpecKind::Argument
                | TypeSpecKind::OutputType
                | TypeSpecKind::Turbofish
                | TypeSpecKind::TypeLevelIf
                | TypeSpecKind::BindingType
                | TypeSpecKind::PipelineInstDepth
                | TypeSpecKind::PipelineRegCount
                | TypeSpecKind::PipelineHeadDepth => {
                    visit_const_generic(expr.as_ref(), ctx).map(hir::TypeExpression::ConstGeneric)
                }
            }
        }
    }
}

pub fn visit_type_spec(
    t: &Loc<ast::TypeSpec>,
    kind: &TypeSpecKind,
    ctx: &mut Context,
) -> Result<Loc<hir::TypeSpec>> {
    let trait_loc = if let SelfContext::TraitDefinition(TraitName::Named(name)) = &ctx.self_ctx {
        name.loc()
    } else {
        ().nowhere()
    };

    if matches!(ctx.self_ctx, SelfContext::TraitDefinition(_)) && t.is_self()? {
        return Ok(hir::TypeSpec::TraitSelf(().at_loc(&trait_loc)).at_loc(t));
    };

    let result = match &t.inner {
        ast::TypeSpec::Named(path, params) => {
            // Lookup the referenced type
            let (base_id, base_t) = ctx.symtab.lookup_type_symbol(path, true)?;

            // Check if the type is a declared type or a generic argument.
            match &base_t.inner {
                TypeSymbol::Declared(generic_args, min_required_params, _) => {
                    // We'll defer checking the validity of generic args to the type checker,
                    // but we still have to visit them now
                    let visited_params = params
                        // We can't flatten "through" Option<Loc<Vec<...>>>, so map it away.
                        .as_ref()
                        .map(|o| &o.inner)
                        .into_iter()
                        .flatten()
                        .map(|p| p.try_map_ref(|p| visit_type_expression(p, kind, ctx)))
                        .collect::<Result<Vec<_>>>()?;

                    if visited_params.len() >= *min_required_params
                        && visited_params.len() <= generic_args.len()
                    {
                        Ok(hir::TypeSpec::Declared(
                            base_id.at_loc(path),
                            visited_params,
                        ))
                    } else {
                        let mut diag = Diagnostic::error(
                            params
                                .as_ref()
                                .map(|p| ().at_loc(p))
                                .unwrap_or(().at_loc(t)),
                            "Wrong number of generic type parameters",
                        )
                        .secondary_label(
                            if !generic_args.is_empty() {
                                ().between_locs(
                                    &generic_args[0],
                                    &generic_args[generic_args.len() - 1],
                                )
                            } else {
                                ().at_loc(&base_t)
                            },
                            format!(
                                "Because this has {} type parameter{}",
                                generic_args.len(),
                                if generic_args.len() != 1 { "s" } else { "" }
                            ),
                        );
                        if *min_required_params == generic_args.len() {
                            diag = diag.primary_label(format!(
                                "Expected {} type parameter{}",
                                generic_args.len(),
                                if generic_args.len() != 1 { "s" } else { "" }
                            ))
                        } else {
                            diag = diag.primary_label(format!(
                                "Expected between {} and {} type parameter{}",
                                min_required_params,
                                generic_args.len(),
                                if generic_args.len() != 1 { "s" } else { "" }
                            ))
                        }
                        Err(diag)
                    }
                }
                TypeSymbol::GenericArg { traits: _ } | TypeSymbol::GenericMeta(_) => {
                    // If this typename refers to a generic argument we need to make
                    // sure that no generic arguments are passed, as generic names
                    // can't have generic parameters

                    if let Some(params) = params {
                        Err(
                            Diagnostic::error(params, "Generic arguments given for a generic type")
                                .primary_label("Generic arguments not allowed here")
                                .secondary_label(base_t, format!("{path} is a generic type")),
                        )
                    } else {
                        Ok(hir::TypeSpec::Generic(Generic::Named(base_id.at_loc(path))))
                    }
                }
                TypeSymbol::Alias(expr) => Ok(expr.inner.clone()),
            }
        }
        ast::TypeSpec::Array { inner, size } => {
            let inner = match visit_type_expression(inner, kind, ctx)? {
                hir::TypeExpression::TypeSpec(t) => Box::new(t.at_loc(inner)),
                _ => {
                    return Err(Diagnostic::error(
                        inner.as_ref(),
                        "Arrays elements must be types, not type level integers",
                    )
                    .primary_label("Non-type array element"))
                }
            };
            let size = Box::new(visit_type_expression(size, kind, ctx)?.at_loc(size));

            Ok(hir::TypeSpec::Array { inner, size })
        }
        ast::TypeSpec::Tuple(inner) => {
            let inner = inner
                .iter()
                .map(|p| match visit_type_expression(p, kind, ctx)? {
                    hir::TypeExpression::TypeSpec(t) => match &t {
                        TypeSpec::Generic(Generic::Hidden(_))
                        | TypeSpec::Tuple(_)
                        | TypeSpec::Array { inner: _, size: _ }
                        | TypeSpec::Inverted(_)
                        | TypeSpec::Wire(_)
                        | TypeSpec::TraitSelf(_)
                        | TypeSpec::Wildcard(_)
                        | TypeSpec::Declared(_, _) => Ok(t.at_loc(p)),
                        TypeSpec::Generic(Generic::Named(name)) => {
                            let inner = ctx.symtab.type_symbol_by_id(name);
                            match &inner.inner {
                                TypeSymbol::Declared(_, _, _)
                                | TypeSymbol::GenericArg { traits: _ }
                                | TypeSymbol::GenericMeta(MetaType::Type) => Ok(t.at_loc(p)),
                                | TypeSymbol::GenericMeta(other_meta) => {
                                    return Err(Diagnostic::error(name, format!("Tuple members can only be types, found {other_meta}"))
                                    .primary_label(format!("Expected type, found {other_meta}"))
                                    .secondary_label(&inner, format!("{name} is defined as {other_meta} here")))
                                }
                                TypeSymbol::Alias(_) => {
                                    return Err(Diagnostic::bug(p, "Aliases in tuple types are currently unsupported"));
                                },
                            }
                        }
                    },
                    _ => {
                        return Err(Diagnostic::error(
                            p,
                            "Tuple elements must be types, not type level integers",
                        )
                        .primary_label("Tuples cannot contain non-types"))
                    }
                })
                .collect::<Result<Vec<_>>>()?;

            // Check if this tuple is a port by checking if any of the contained types
            // are ports. If they are, retain the first one to use as a witness for this fact
            // for error reporting
            let transitive_port_witness = inner
                .iter()
                .map(|p| {
                    if p.is_port(ctx)? {
                        Ok(Some(p))
                    } else {
                        Ok(None)
                    }
                })
                .collect::<Result<Vec<_>>>()?
                .into_iter()
                .find_map(|x| x);

            if let Some(witness) = transitive_port_witness {
                // Since this type has 1 port, all members must be ports
                for ty in &inner {
                    if !ty.is_port(ctx)? {
                        return Err(Diagnostic::error(
                            ty,
                            "Cannot mix ports and non-ports in a tuple",
                        )
                        .primary_label("This is not a port")
                        .secondary_label(witness, "This is a port")
                        .note("A tuple must either contain only ports or no ports"));
                    }
                }
            }

            Ok(hir::TypeSpec::Tuple(inner))
        }
        ast::TypeSpec::Wire(inner) => {
            let inner = match visit_type_expression(inner, kind, ctx)? {
                hir::TypeExpression::TypeSpec(t) => t.at_loc(inner),
                _ => {
                    return Err(Diagnostic::error(
                        inner.as_ref(),
                        "Wire inner types must be types, not type level integers",
                    )
                    .primary_label("Wires cannot contain non-types"))
                }
            };

            if inner.is_port(&ctx)? {
                return Err(Diagnostic::from(error::WireOfPort {
                    full_type: t.loc(),
                    inner_type: inner.loc(),
                }));
            }

            if inner.is_inout(&ctx)? {
                return Err(Diagnostic::from(error::WireOfInOut {
                    full_type: t.loc(),
                    inner_type: inner.loc(),
                }));
            }

            Ok(hir::TypeSpec::Wire(Box::new(inner)))
        }
        ast::TypeSpec::Inverted(inner) => {
            let inner = match visit_type_expression(inner, kind, ctx)? {
                hir::TypeExpression::TypeSpec(t) => t.at_loc(inner),
                _ => {
                    return Err(Diagnostic::error(
                        inner.as_ref(),
                        "Inverted inner types must be types, not type level integers",
                    )
                    .primary_label("Non-type cannot be inverted"))
                }
            };

            if !inner.is_port(ctx)? {
                Err(Diagnostic::error(t, "A non-port type can not be inverted")
                    .primary_label("Inverting non-port")
                    .secondary_label(inner, "This is not a port"))
            } else {
                Ok(hir::TypeSpec::Inverted(Box::new(inner)))
            }
        }
        ast::TypeSpec::Impl(specs) => {
            let specs = specs
                .iter()
                .map(|t| visit_trait_spec(t, &TypeSpecKind::TraitBound, ctx))
                .collect::<Result<Vec<_>>>()?;

            let new_id = ctx.generic_idtracker.next();
            ctx.item_list.hidden_constraints.push(specs.at_loc(&t));
            Ok(hir::TypeSpec::Generic(Generic::Hidden(new_id.at_loc(&t))))
        }
        ast::TypeSpec::Wildcard => {
            let default_error = |message, primary| {
                Err(
                    Diagnostic::error(t, format!("{message} cannot have wildcards in their type"))
                        .primary_label(format!("Wildcard in {primary}")),
                )
            };
            match kind {
                TypeSpecKind::Argument => default_error("Argument types", "argument type"),
                TypeSpecKind::OutputType => default_error("Return types", "return type"),
                TypeSpecKind::ImplTrait => default_error("Implemented traits", "implemented trait"),
                TypeSpecKind::ImplTarget => default_error("Impl targets", "impl target"),
                TypeSpecKind::EnumMember => default_error("Enum members", "enum member"),
                TypeSpecKind::StructMember => default_error("Struct members", "struct member"),
                TypeSpecKind::PipelineHeadDepth => {
                    default_error("Pipeline depths", "pipeline depth")
                }
                TypeSpecKind::PipelineRegCount => {
                    default_error("Register counts", "register count")
                }
                TypeSpecKind::TraitBound => {
                    default_error("Traits used in trait bound", "trait bound")
                }
                TypeSpecKind::PipelineInstDepth
                | TypeSpecKind::TypeLevelIf
                | TypeSpecKind::Turbofish
                | TypeSpecKind::BindingType => Ok(hir::TypeSpec::Wildcard(t.loc())),
            }
        }
    };

    Ok(result?.at_loc(t))
}

#[derive(Debug, Clone, PartialEq)]
pub enum SelfContext {
    /// `self` currently does not refer to anything
    FreeStanding,
    /// `self` refers to `TypeSpec` in an impl block for that type
    ImplBlock(Loc<hir::TypeSpec>),
    /// `self` refers to a trait implementor
    TraitDefinition(TraitName),
}

fn visit_parameter_list(
    l: &Loc<ParameterList>,
    ctx: &mut Context,
    no_mangle_all: Option<Loc<()>>,
) -> Result<Loc<hir::ParameterList>> {
    let mut arg_names: HashSet<Loc<Identifier>> = HashSet::default();
    let mut result = vec![];

    if let SelfContext::ImplBlock(_) = ctx.self_ctx {
        if l.self_.is_none() {
            // Suggest insertion after the first paren
            let mut diag = Diagnostic::error(l, "Method must take 'self' as the first parameter")
                .primary_label("Missing self");

            let suggest_msg = "Consider adding self";
            diag = if l.args.is_empty() {
                diag.span_suggest_replace(suggest_msg, l, "(self)")
            } else {
                diag.span_suggest_insert_before(suggest_msg, &l.args[0].1, "self, ")
            };
            return Err(diag);
        }
    }

    if let Some(ref self_) = l.self_ {
        let mut attrs = self_.inner.clone();
        let no_mangle = attrs
            .consume_no_mangle()
            .map(|ident| ident.loc())
            .or(no_mangle_all);
        attrs.report_unused("`self` parameter")?;

        match &ctx.self_ctx {
            SelfContext::FreeStanding => {
                return Err(Diagnostic::error(
                    self_,
                    "'self' cannot be used in free standing units",
                )
                .primary_label("not allowed here"))
            }
            SelfContext::ImplBlock(spec) => result.push(hir::Parameter {
                no_mangle,
                name: Identifier::intern("self").at_loc(self_),
                ty: spec.clone(),
                field_translator: None,
            }),
            // When visiting trait definitions, we don't need to add self to the
            // symtab at all since we won't be visiting unit bodies here.
            // NOTE: This will be incorrect if we add default impls for traits
            SelfContext::TraitDefinition(_) => result.push(hir::Parameter {
                no_mangle,
                name: Identifier::intern("self").at_loc(self_),
                ty: hir::TypeSpec::TraitSelf(self_.loc()).at_loc(self_),
                field_translator: None,
            }),
        }
    }

    for (attrs, name, input_type) in &l.args {
        if let Some(prev) = arg_names.get(name) {
            return Err(
                Diagnostic::error(name, "Multiple arguments with the same name")
                    .primary_label(format!("{name} later declared here"))
                    .secondary_label(prev, format!("{name} previously declared here")),
            );
        }
        arg_names.insert(name.clone());
        let t = visit_type_spec(input_type, &TypeSpecKind::Argument, ctx)?;

        let mut attrs = attrs.clone();
        let no_mangle = attrs
            .consume_no_mangle()
            .map(|ident| ident.loc())
            .or(no_mangle_all);
        let field_translator = attrs.consume_translator();
        attrs.report_unused("a parameter")?;

        result.push(hir::Parameter {
            name: name.clone(),
            ty: t,
            no_mangle,
            field_translator,
        });
    }

    Ok(hir::ParameterList(result).at_loc(l))
}

/// Builds a diagnostic for a `#[no_mangle(all)]`-marked unit with a non-unit output type.
fn build_no_mangle_all_output_diagnostic(
    head: &ast::UnitHead,
    output_type: &Loc<TypeSpec>,
    body_for_diagnostics: Option<&Loc<Expression>>,
) -> Diagnostic {
    let suffix_length = head
        .inputs
        .args
        .iter()
        .filter_map(|(_, name, _)| {
            if name.inner.as_str().contains("out") {
                Some(name.inner.as_str().len())
            } else {
                None
            }
        })
        .max()
        .unwrap_or(2)
        - 2;
    let suggested_name = format!("out{}", "_".repeat(suffix_length));
    let output_is_wire = output_type.to_string().starts_with("&");
    let suggested_type = format!(
        "inv {}{}",
        if output_is_wire {
            // ports shouldn't have duplicate & (thanks Astrid)
            ""
        } else {
            "&"
        },
        output_type
    );

    let mut diagnostic = Diagnostic::error(output_type, "Cannot apply `#[no_mangle(all)]`")
        .primary_label("Output types are always mangled");

    let output_arrow_span = &head.output_type.as_ref().unwrap().0.span;
    let output_type_full_span: FullSpan = output_type.into();
    let mut first_suggestion = SuggestionParts::new().part(
        (
            Span::new(output_arrow_span.start(), output_type_full_span.0.end()),
            output_type_full_span.1,
        ),
        "",
    );
    if head.inputs.args.is_empty() {
        let (span, file) = (head.inputs.span, head.inputs.file_id);
        first_suggestion = first_suggestion.part(
            (span, file),
            format!("({}: {})", suggested_name, suggested_type),
        );
    } else {
        let last_parameter = &head.inputs.args.last().unwrap().2;
        let (span, file) = (last_parameter.span, last_parameter.file_id);
        first_suggestion.push_part(
            (Span::new(span.end(), span.end()), file),
            format!(", {}: {}", suggested_name, suggested_type),
        );
    }

    diagnostic.push_span_suggest_multipart(
        "Consider replacing the output with an inverted input",
        first_suggestion,
    );

    // add the set suggestion for non-externs
    if let Some(block) = body_for_diagnostics {
        let block = block.assume_block();
        if let Some(result) = block.result.as_ref() {
            if output_is_wire {
                diagnostic = diagnostic.span_suggest_remove("Remember to `set` the inverted input instead of ending the block with an output", result);
            } else {
                let (span, file) = (result.span, result.file_id);
                diagnostic.push_span_suggest_multipart(
                    "...and `set` the inverted input to the return value",
                    SuggestionParts::new()
                        .part(
                            (Span::new(span.start(), span.start()), file),
                            format!("set {} = &", suggested_name),
                        )
                        .part((Span::new(span.end(), span.end()), file), ";"),
                );
            }
        }
    }

    diagnostic
}

pub fn visit_unit_kind(kind: &ast::UnitKind, ctx: &mut Context) -> Result<hir::UnitKind> {
    let inner = match kind {
        ast::UnitKind::Function => hir::UnitKind::Function(hir::FunctionKind::Fn),
        ast::UnitKind::Entity => hir::UnitKind::Entity,
        ast::UnitKind::Pipeline(depth) => hir::UnitKind::Pipeline {
            depth: depth
                .try_map_ref(|t| visit_type_expression(t, &TypeSpecKind::PipelineHeadDepth, ctx))?,
            depth_typeexpr_id: ctx.idtracker.next(),
        },
    };
    Ok(inner)
}

fn validate_default_param_position(
    type_params: &Option<Loc<Vec<Loc<ast::TypeParam>>>>,
) -> Result<()> {
    let misplaced_default = type_params
        .iter()
        .map(Loc::strip_ref)
        .flatten()
        .rev()
        .skip_while(|d| d.default().is_some())
        .find(|d| d.default().is_some());

    if let Some(param) = misplaced_default {
        return Err(Diagnostic::error(
            type_params.as_ref().unwrap(),
            "Generic parameters with a default must be trailing",
        )
        .secondary_label(param, "This parameter has a default and is not trailing"));
    };

    Ok(())
}

pub fn visit_type_params(
    type_params: &Option<Loc<Vec<Loc<ast::TypeParam>>>>,
    ctx: &mut Context,
) -> Result<Vec<Loc<hir::TypeParam>>> {
    validate_default_param_position(type_params)?;

    type_params
        .as_ref()
        .map(Loc::strip_ref)
        .into_iter()
        .flatten()
        .map(|loc| loc.try_map_ref(|p| visit_type_param(p, ctx)))
        .collect::<Result<Vec<_>>>()
}

/// Visit the head of an entity to generate an entity head
#[tracing::instrument(skip_all, fields(name=%head.name))]
pub fn unit_head(
    head: &ast::UnitHead,
    scope_type_params: &Option<Loc<Vec<Loc<TypeParam>>>>,
    scope_where_clauses: &[Loc<hir::WhereClause>],
    ctx: &mut Context,
    body_for_diagnostics: Option<&Loc<Expression>>,
) -> Result<hir::UnitHead> {
    ctx.symtab.new_scope();

    let scope_type_params = scope_type_params
        .as_ref()
        .map(Loc::strip_ref)
        .into_iter()
        .flatten()
        .map(|loc| loc.try_map_ref(|p| re_visit_type_param(p, ctx)))
        .collect::<Result<Vec<Loc<hir::TypeParam>>>>()?;

    let unit_type_params = visit_type_params(&head.type_params, ctx)?;

    let unit_where_clauses = visit_where_clauses(&head.where_clauses, ctx);

    let output_type = if let Some(output_type) = &head.output_type {
        Some(visit_type_spec(
            &output_type.1,
            &TypeSpecKind::OutputType,
            ctx,
        )?)
    } else {
        None
    };

    let no_mangle_all = head
        .attributes
        .0
        .iter()
        .find(|attribute| matches!(attribute.inner, Attribute::NoMangle { all: true }))
        .map(|attribute| ().at_loc(attribute));

    let deprecation_note = head
        .attributes
        .0
        .iter()
        .flat_map(|attribute| match &attribute.inner {
            Attribute::Deprecated { note, .. } => Some(note.clone()),
            _ => None,
        })
        .last();

    // we only care if we're trying to no_mangle_all a type with a non-unit output type
    if no_mangle_all.is_some()
        && output_type
            .as_ref()
            .map(|output_type| {
                !(matches!(&**output_type, TypeSpec::Tuple(inner) if inner.is_empty()))
            })
            .unwrap_or(false)
    {
        return Err(build_no_mangle_all_output_diagnostic(
            head,
            output_type.as_ref().unwrap(),
            body_for_diagnostics,
        ));
    }

    let first_hidden_id = ctx.generic_idtracker.peek();
    let inputs = visit_parameter_list(&head.inputs, ctx, no_mangle_all)?;
    let last_hidden_id = ctx.generic_idtracker.peek();

    // Check for ports in functions
    // We need to have the scope open to check this, but we also need to close
    // the scope if we fail here, so we'll store port_error in a variable

    let unit_kind: Result<_> = head.unit_kind.try_map_ref(|k| visit_unit_kind(k, ctx));

    ctx.symtab.close_scope();
    let where_clauses = unit_where_clauses?
        .iter()
        .chain(scope_where_clauses.iter())
        .cloned()
        .collect();

    let hidden_type_params = (first_hidden_id..last_hidden_id)
        .map(|id| {
            let (trait_bounds, loc) = ctx.item_list.hidden_constraints[id as usize]
                .clone()
                .split_loc();

            hir::TypeParam {
                name: Generic::Hidden(GenericID(id).at_loc(&loc)),
                trait_bounds,
                meta: MetaType::Type,
                default: None,
            }
            .at_loc(&loc)
        })
        .collect();

    Ok(hir::UnitHead {
        name: head.name.clone(),
        is_nonstatic_method: head.inputs.self_.is_some(),
        inputs,
        output_type,
        unit_type_params,
        hidden_type_params,
        scope_type_params,
        unit_kind: unit_kind?,
        where_clauses,
        unsafe_marker: head.unsafe_token,
        documentation: head.attributes.merge_docs(),
        deprecation_note,
    })
}

pub fn visit_const_generic(
    t: &Loc<ast::Expression>,
    ctx: &mut Context,
) -> Result<Loc<ConstGeneric>> {
    let kind = match &t.inner {
        ast::Expression::Identifier(name) => {
            let (name, sym) = ctx.symtab.lookup_type_symbol(name, true)?;
            match &sym.inner {
                TypeSymbol::Declared(_, _, _) => {
                    return Err(Diagnostic::error(t, format!(
                            "{name} is not a type level integer but is used in a const generic expression."
                        ),
                    )
                        .primary_label(format!("Expected type level integer"))
                    .secondary_label(&sym, format!("{name} is defined here")))
                }
                TypeSymbol::GenericArg { traits: _ }=> {
                    return Err(Diagnostic::error(
                        t,
                        format!(
                            "{name} is not a type level integer but is used in a const generic expression."
                        ))
                        .primary_label("Expected type level integer")
                        .secondary_label(&sym, format!("{name} is defined here"))
                        .span_suggest_insert_before(
                            "Try making the generic an integer",
                        &sym,
                        "#int ",
                    )
                    .span_suggest_insert_before(
                        "or an unsigned integer",
                            &sym,
                            "#uint ",
                        ))
                }
                TypeSymbol::GenericMeta(_) => {
                    ConstGeneric::Name(name.at_loc(t))
                },
                TypeSymbol::Alias(a) => {
                    return Err(Diagnostic::error(t, "Type aliases are not supported in const generics").primary_label("Type alias in const generic")
                    .secondary_label(a, "Alias defined here"))
                }
            }
        }
        ast::Expression::IntLiteral(val) => ConstGeneric::Int(val.inner.clone().as_signed()),
        ast::Expression::StrLiteral(val) => ConstGeneric::Str(val.inner.clone()),
        ast::Expression::BinaryOperator(lhs, op, rhs) => {
            let lhs = visit_const_generic(lhs, ctx)?;
            let rhs = visit_const_generic(rhs, ctx)?;

            match &op.inner {
                ast::BinaryOperator::Add => ConstGeneric::Add(Box::new(lhs), Box::new(rhs)),
                ast::BinaryOperator::Sub => ConstGeneric::Sub(Box::new(lhs), Box::new(rhs)),
                ast::BinaryOperator::Mul => ConstGeneric::Mul(Box::new(lhs), Box::new(rhs)),
                ast::BinaryOperator::Eq => ConstGeneric::Eq(Box::new(lhs), Box::new(rhs)),
                ast::BinaryOperator::Neq => ConstGeneric::NotEq(Box::new(lhs), Box::new(rhs)),
                ast::BinaryOperator::Div => ConstGeneric::Div(Box::new(lhs), Box::new(rhs)),
                ast::BinaryOperator::Mod => ConstGeneric::Mod(Box::new(lhs), Box::new(rhs)),
                other => {
                    return Err(Diagnostic::error(
                        op,
                        format!("Operator `{other}` is not supported in a type expression"),
                    )
                    .primary_label("Not supported in a type expression"))
                }
            }
        }
        ast::Expression::UnaryOperator(op, operand) => {
            let operand = visit_const_generic(operand, ctx)?;

            match &op.inner {
                ast::UnaryOperator::Sub => ConstGeneric::Sub(
                    Box::new(ConstGeneric::Int(BigInt::zero()).at_loc(&operand)),
                    Box::new(operand),
                ),
                other => {
                    return Err(Diagnostic::error(
                        t,
                        format!("Operator `{other}` is not supported in a type expression"),
                    )
                    .primary_label("Not supported in a type expression"))
                }
            }
        }
        ast::Expression::Call {
            kind: CallKind::Function,
            callee,
            args,
            turbofish: None,
        } => match callee.to_named_strs().as_slice() {
            [Some("uint_bits_to_fit")] => match &args.inner {
                ast::ArgumentList::Positional(a) => {
                    if a.len() != 1 {
                        return Err(Diagnostic::error(
                            args,
                            format!("This function takes one argument, {} provided", a.len()),
                        )
                        .primary_label("Expected 1 argument"));
                    } else {
                        let arg = visit_const_generic(&a[0], ctx)?;

                        ConstGeneric::UintBitsToFit(Box::new(arg))
                    }
                }
                ast::ArgumentList::Named(_) => {
                    return Err(Diagnostic::error(
                        t,
                        "Passing arguments by name is unsupported in type expressions",
                    )
                    .primary_label("Arguments passed by name in type expression"))
                }
            },
            _ => {
                return Err(Diagnostic::error(
                    callee,
                    format!("{callee} cannot be evaluated in a type expression"),
                )
                .primary_label("Not supported in a type expression"))
            }
        },
        ast::Expression::Parenthesized(inner) => visit_const_generic(inner, ctx)?.inner,
        _ => {
            return Err(Diagnostic::error(
                t,
                format!("This expression is not supported in a type expression"),
            )
            .primary_label("Not supported in a type expression"))
        }
    };

    Ok(kind.at_loc(t))
}

pub fn visit_where_clauses(
    where_clauses: &[WhereClause],
    ctx: &mut Context,
) -> Result<Vec<Loc<hir::WhereClause>>> {
    let mut visited_where_clauses: Vec<Loc<hir::WhereClause>> = vec![];
    for where_clause in where_clauses {
        match where_clause {
            WhereClause::GenericInt {
                target,
                kind,
                expression,
                if_unsatisfied,
            } => {
                let make_diag = |primary| {
                    Diagnostic::error(
                        target,
                        format!("Expected `{}` to be a type level integer", target),
                    )
                    .primary_label(primary)
                    .secondary_label(expression, "This is an integer constraint")
                };
                let (name_id, sym) = match ctx.symtab.lookup_type_symbol(target, true) {
                    Ok(res) => res,
                    Err(LookupError::NotATypeSymbol(_, thing)) => {
                        return Err(make_diag(format!("`{target}` is not a type level integer"))
                            .secondary_label(
                                thing.loc(),
                                format!("`{}` is a {} declared here", target, thing.kind_string()),
                            ))
                    }
                    Err(e) => return Err(e.into()),
                };
                match &sym.inner {
                    TypeSymbol::GenericMeta(_) => {
                        let clause = hir::WhereClause::Int {
                            target: Generic::Named(name_id.at_loc(&target.loc())),
                            kind: match kind {
                                ast::Inequality::Eq => hir::WhereClauseKind::Eq,
                                ast::Inequality::Neq => hir::WhereClauseKind::Neq,
                                ast::Inequality::Lt => hir::WhereClauseKind::Lt,
                                ast::Inequality::Leq => hir::WhereClauseKind::Leq,
                                ast::Inequality::Gt => hir::WhereClauseKind::Gt,
                                ast::Inequality::Geq => hir::WhereClauseKind::Geq,
                            },
                            constraint: visit_const_generic(expression, ctx)?,
                            if_unsatisfied: if_unsatisfied.clone()
                        }
                        .between_locs(target, expression);

                        visited_where_clauses.push(clause);
                    }
                    TypeSymbol::GenericArg { .. } => {
                        return Err(
                            make_diag("Generic type in generic integer constraint".into())
                                .secondary_label(
                                    sym.clone(),
                                    format!("`{target}` is a generic type"),
                                )
                                .span_suggest_insert_before(
                                    "Try making the generic an integer",
                                    &sym,
                                    "#int ",
                                )
                                .span_suggest_insert_before(
                                    "or an unsigned integer",
                                    &sym,
                                    "#uint ",
                                ),
                        );
                    }
                    TypeSymbol::Declared { .. } => {
                        return Err(make_diag(
                            "Declared type in generic integer constraint".into(),
                        )
                        .secondary_label(sym, format!("`{target}` is a type declared here")));
                    }
                    TypeSymbol::Alias(a) => {
                        return Err(Diagnostic::error(
                                &sym, "Type aliases are not supported in where clauses"
                            )
                            .primary_label("Type alias in where clause")
                            .secondary_label(a, "Alias defined here")
                            .note(
                                "This is a soft limitation in the compiler. If you need this feature, open an issue at https://gitlab.com/spade-lang/spade/"
                            )
                        )
                    }
                }
            }
            WhereClause::TraitBounds { target, traits } => {
                let make_diag = |primary| {
                    Diagnostic::error(
                        target,
                        format!("Expected `{}` to be a generic type", target),
                    )
                    .primary_label(primary)
                };
                let (name_id, sym) = match ctx
                    .symtab
                    .lookup_type_symbol(where_clause.target(), true)
                {
                    Ok(res) => res,
                    Err(LookupError::NotATypeSymbol(path, thing)) => {
                        return Err(make_diag(format!("`{target}` is not a type symbol"))
                            .secondary_label(
                                path,
                                format!("`{}` is {} declared here", target, thing.kind_string()),
                            ));
                    }
                    Err(e) => return Err(e.into()),
                };
                match &sym.inner {
                    TypeSymbol::GenericArg { .. } | TypeSymbol::GenericMeta(MetaType::Type) => {
                        let traits = traits
                            .iter()
                            .map(|t| visit_trait_spec(t, &TypeSpecKind::TraitBound, ctx))
                            .collect::<Result<Vec<_>>>()?;

                        ctx.symtab.add_traits_to_generic(&name_id, traits.clone())?;

                        visited_where_clauses.push(
                            hir::WhereClause::Type {
                                target: Generic::Named(name_id.at_loc(&target.loc())),
                                traits,
                            }
                            .at_loc(target),
                        );
                    }
                    TypeSymbol::GenericMeta(_) => {
                        return Err(make_diag("Generic int in trait bound".into())
                            .secondary_label(sym, format!("{target} is a generic int")));
                    }
                    TypeSymbol::Declared { .. } => {
                        return Err(make_diag("Declared type in trait bound".into())
                            .secondary_label(sym, format!("{target} is a type declared here")));
                    }
                    TypeSymbol::Alias(a) => {
                        return Err(Diagnostic::error(
                                &sym, "Type aliases are not supported in where clauses"
                            )
                            .primary_label("Type alias in where clause")
                            .secondary_label(a, "Alias defined here")
                            .note(
                                "This is a soft limitation in the compiler. If you need this feature, open an issue at https://gitlab.com/spade-lang/spade/"
                            )
                        )
                    }
                };
            }
        }
    }
    Ok(visited_where_clauses)
}

/// The `extra_path` parameter allows specifying an extra path prepended to
/// the name of the entity. This is used by impl blocks to append a unique namespace
#[tracing::instrument(skip_all, fields(%unit.head.name, %unit.head.unit_kind))]
pub fn visit_unit(
    extra_path: Option<Path>,
    unit: &Loc<ast::Unit>,
    scope_type_params: &Option<Loc<Vec<Loc<ast::TypeParam>>>>,
    ctx: &mut Context,
) -> Result<hir::Item> {
    let ast::Unit {
        head:
            ast::UnitHead {
                visibility: _,
                unsafe_token: _,
                extern_token: _,
                name,
                attributes,
                inputs: _,
                output_type: _,
                unit_kind: _,
                type_params,
                where_clauses: _,
            },
        body,
    } = &unit.inner;

    ctx.symtab.new_scope();

    let path = extra_path
        .unwrap_or(Path(vec![]))
        .join(Path::ident(name.clone()))
        .at_loc(&name.loc());

    let (id, head) = ctx.symtab.lookup_unit_ignore_metadata(&path).map_err(|_| {
        diag_anyhow!(
            path,
            "Attempting to lower an entity that has not been added to the symtab previously"
        )
    })?;

    ctx.current_unit = Some(head.inner.clone());

    let all_type_params = head.get_type_params();

    let mut unit_name = if all_type_params.is_empty() {
        hir::UnitName::FullPath(id.clone().at_loc(name))
    } else {
        hir::UnitName::WithID(id.clone().at_loc(name))
    };

    let mut wal_suffix = None;

    let attributes = attributes.lower(&mut |attr: &Loc<ast::Attribute>| match &attr.inner {
        ast::Attribute::Optimize { passes } => Ok(Some(hir::Attribute::Optimize {
            passes: passes.clone(),
        })),
        ast::Attribute::NoMangle { .. } => {
            if let Some(generic_list) = type_params {
                // if it's a verilog extern (so `body.is_none()`), then we allow generics insofar
                // as they are numbers or strings (checked later on)
                if body.is_some() {
                    Err(
                        Diagnostic::error(attr, "no_mangle is not allowed on generic units")
                            .primary_label("no_mangle not allowed here")
                            .secondary_label(generic_list, "Because this unit is generic"),
                    )
                } else {
                    // yucky code duplication
                    unit_name = hir::UnitName::Unmangled(
                        name.inner.as_str().to_owned(),
                        id.clone().at_loc(name),
                    );
                    Ok(None)
                }
            } else if let Some(generic_list) = scope_type_params {
                Err(Diagnostic::error(
                    attr,
                    "no_mangle is not allowed on units inside generic impls",
                )
                .primary_label("no_mangle not allowed here")
                .secondary_label(generic_list, "Because this impl is generic"))
            } else {
                unit_name = hir::UnitName::Unmangled(
                    name.inner.as_str().to_owned(),
                    id.clone().at_loc(name),
                );
                Ok(None)
            }
        }
        ast::Attribute::WalSuffix { suffix } => {
            if body.is_none() {
                return Err(
                    Diagnostic::error(attr, "wal_suffix is not allowed on `extern` units")
                        .primary_label("Not allowed on `extern` units")
                        .secondary_label(unit.head.extern_token.unwrap(), "This unit is `extern`"),
                );
            }

            wal_suffix = Some(suffix.clone());
            Ok(None)
        }
        ast::Attribute::VerilogAttrs { entries } => Ok(Some(hir::Attribute::VerilogAttrs {
            entries: entries.clone(),
        })),
        ast::Attribute::Deprecated { .. } => Ok(None),
        ast::Attribute::Documentation { .. } => Ok(None),
        _ => Err(attr.report_unused("a unit")),
    })?;

    // If this is a extern entity
    if body.is_none() {
        ctx.symtab.close_scope();
        return Ok(hir::Item::ExternUnit(unit_name, head));
    }

    // Add the inputs to the symtab
    let inputs = head
        .inputs
        .0
        .iter()
        .map(
            |hir::Parameter {
                 name: ident,
                 ty,
                 no_mangle: _,
                 field_translator: _,
             }| {
                (
                    ctx.symtab.add_local_variable(ident.clone()).at_loc(ident),
                    ty.clone(),
                )
            },
        )
        .collect::<Vec<_>>();

    // Add the type params to the symtab to make them visible in the body
    for param in all_type_params {
        if let hir::TypeParam {
            name: hir::Generic::Named(ref name_id),
            trait_bounds: _,
            meta: _,
            default: _,
        } = param.inner
        {
            let ident = param.ident().unwrap();
            ctx.symtab.re_add_type(ident.clone(), name_id.inner.clone())
        }
    }

    ctx.pipeline_ctx = maybe_perform_pipelining_tasks(unit, &head, ctx)?;

    let mut body = body
        .as_ref()
        .unwrap()
        .map_ref(|body| visit_expression(&body, ctx));

    // Add wal_suffixes for the signals if requested. This creates new statements
    // which we'll add to the end of the body
    if let Some(suffix) = wal_suffix {
        match &mut body.kind {
            hir::ExprKind::Block(block) => {
                block.statements.append(
                    &mut inputs
                        .iter()
                        .map(|(name, _)| {
                            hir::Statement::WalSuffixed {
                                suffix: suffix.inner.clone(),
                                target: name.clone(),
                            }
                            .at_loc(&suffix)
                        })
                        .collect(),
                );
            }
            _ => diag_bail!(body, "Unit body was not block"),
        }
    }

    ctx.symtab.close_scope();
    ctx.current_unit = None;

    Ok(hir::Item::Unit(expand_type_level_if(
        hir::Unit {
            name: unit_name,
            head: head.clone().inner,
            attributes,
            inputs,
            body,
        }
        .at_loc(unit),
        ctx,
    )?))
}

#[tracing::instrument(skip_all, fields(name=?trait_spec.path))]
pub fn visit_trait_spec(
    trait_spec: &Loc<ast::TraitSpec>,
    type_spec_kind: &TypeSpecKind,
    ctx: &mut Context,
) -> Result<Loc<hir::TraitSpec>> {
    let (name_id, loc) = match ctx.symtab.lookup_trait(&trait_spec.inner.path) {
        Ok(res) => res,
        Err(LookupError::IsAType(path, loc)) => {
            return Err(Diagnostic::error(
                path.clone(),
                format!("Unexpected type {}, expected a trait", path.inner),
            )
            .primary_label("Unexpected type")
            .secondary_label(loc, format!("Type {} defined here", path.inner)));
        }
        Err(err) => return Err(err.into()),
    };
    // This must always succeed because `lookup_trait` succeeded right before
    let Some(Thing::Trait(marker)) = ctx.symtab.thing_by_id(&name_id) else {
        unreachable!();
    };
    if trait_spec.paren_syntax && !marker.paren_sugar {
        // Paren syntax enforces at least two type parameters to be present
        let Some(type_params) = trait_spec.type_params.as_ref() else {
            unreachable!();
        };

        return Err(
            Diagnostic::error(trait_spec, "Trait does not support function-like notation")
                .primary_label("Trait does not support function-like notation")
                .span_suggest_replace(
                    "replace it with a regular type parameter list",
                    type_params,
                    format!(
                        "<{}>",
                        type_params.inner.iter().map(|tp| tp.to_string()).join(", ")
                    ),
                ),
        );
    } else if !trait_spec.paren_syntax && marker.paren_sugar {
        let mut diag = Diagnostic::warning(trait_spec, "Trait supports function-like notation")
            .primary_label("Trait supports function-like notation");

        let whole_loc = trait_spec.type_params.as_ref().map(Loc::loc);
        let type_params = trait_spec
            .type_params
            .as_ref()
            .map_or(&[][..], |tp| &tp.inner[..]);

        let (rest_tys, param_ty, return_ty) = match type_params {
            [] => (&[][..], None, None),
            [ref arg] => (&[][..], Some(&arg.inner), None),
            [ref rest @ .., ref arg, ref ret] => (rest, Some(&arg.inner), Some(&ret.inner)),
        };

        let rest_str = match rest_tys {
            [] => String::new(),
            tys => format!("<{}>", tys.iter().map(|tp| tp.to_string()).join(", ")),
        };

        let param_str = match param_ty {
            None => String::from("()"),
            Some(ty @ ast::TypeExpression::TypeSpec(ts)) if ts.is_tuple() => ty.to_string(),
            Some(ty) => format!("({})", ty.to_string()),
        };

        let return_str = match return_ty {
            None => String::new(),
            Some(ast::TypeExpression::TypeSpec(ts)) if ts.is_empty_tuple() => String::new(),
            Some(ty) => format!(" -> {ty}"),
        };

        let message = "consider using function-like syntax";
        let suggestion = format!("{rest_str}{param_str}{return_str}");

        if let Some(loc) = whole_loc {
            diag = diag.span_suggest_replace(message, loc, suggestion);
        } else {
            diag = diag.span_suggest_insert_after(message, &trait_spec.path, suggestion);
        }
        ctx.diags.lock().unwrap().errors.push(diag);
    }
    let name = TraitName::Named(name_id.at_loc(&loc));
    let type_params = match &trait_spec.inner.type_params {
        Some(params) => Some(params.try_map_ref(|params| {
            params
                .iter()
                .map(|param| param.try_map_ref(|te| visit_type_expression(te, type_spec_kind, ctx)))
                .collect::<Result<_>>()
        })?),
        None => None,
    };
    Ok(hir::TraitSpec {
        name,
        type_params,
        paren_syntax: trait_spec.paren_syntax,
    }
    .at_loc(trait_spec))
}

#[tracing::instrument(skip_all, fields(name=?item.name()))]
pub fn visit_item(item: &ast::Item, ctx: &mut Context) -> Result<Vec<hir::Item>> {
    match item {
        ast::Item::Unit(u) => Ok(vec![visit_unit(None, u, &None, ctx)?]),
        ast::Item::TraitDef(_) => {
            // Global symbol lowering already visits traits
            event!(Level::INFO, "Trait definition");
            Ok(vec![])
        }
        ast::Item::Type(_) => {
            // Global symbol lowering already visits type declarations
            event!(Level::INFO, "Type definition");
            Ok(vec![])
        }
        ast::Item::ImplBlock(block) => visit_impl(block, ctx),
        ast::Item::ExternalMod(_) => Ok(vec![]),
        ast::Item::Module(m) => visit_module(m, ctx).map(|_| vec![]),
        ast::Item::Use(_, ss) => {
            for s in &ss.inner {
                ctx.symtab
                    .lookup_id(&s.path, true)
                    .map_err(Diagnostic::from)?;
            }

            Ok(vec![])
        }
    }
}

#[tracing::instrument(skip_all, fields(module.name = %module.name.inner))]
pub fn visit_module(module: &ast::Module, ctx: &mut Context) -> Result<()> {
    let path = &ctx
        .symtab
        .current_namespace()
        .clone()
        .at_loc(&module.name.loc());

    let (id, thing) = ctx
        .symtab
        .lookup_thing(path)
        .map_err(|_| diag_anyhow!(module.name, "Failed to find {path} in symtab"))?;

    if !matches!(thing, Thing::Module(_, _)) {
        diag_bail!(
            module.name,
            "Found {} to be a {}",
            module.name,
            thing.kind_string()
        );
    }

    let documentation = module.body.documentation.join("\n");

    ctx.item_list.modules.insert(
        id.clone(),
        Module {
            name: id.at_loc(&module.name),
            documentation,
        },
    );

    ctx.in_named_namespace(module.name, |ctx| visit_module_body(&module.body, ctx))
}

#[tracing::instrument(skip_all)]
pub fn visit_module_body(body: &ast::ModuleBody, ctx: &mut Context) -> Result<()> {
    for i in &body.members {
        for item in visit_item(i, ctx)? {
            match item {
                hir::Item::Unit(u) => ctx
                    .item_list
                    .add_executable(u.name.name_id().clone(), ExecutableItem::Unit(u))?,

                hir::Item::ExternUnit(name, head) => ctx.item_list.add_executable(
                    name.name_id().clone(),
                    ExecutableItem::ExternUnit(name, head),
                )?,
            }
        }
    }

    Ok(())
}

fn try_lookup_enum_variant(path: &Loc<Path>, ctx: &mut Context) -> Result<hir::PatternKind> {
    let (name_id, variant) = ctx.symtab.lookup_enum_variant(path)?;
    if variant.inner.params.argument_num() == 0 {
        Ok(hir::PatternKind::Type(name_id.at_loc(path), vec![]))
    } else {
        let expected = variant.inner.params.argument_num();
        Err(Diagnostic::from(error::PatternListLengthMismatch {
            expected,
            got: 0,
            at: path.loc(),
            for_what: Some("enum variant".to_string()),
        })
        // FIXME: actual names of variant arguments?
        .span_suggest_insert_after(
            "help: Add arguments here",
            path.loc(),
            format!(
                "({})",
                std::iter::repeat("_")
                    .take(expected)
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        ))
    }
}

pub fn visit_pattern(p: &ast::Pattern, ctx: &mut Context) -> Result<hir::Pattern> {
    let kind = match &p {
        ast::Pattern::Integer(val) => hir::PatternKind::Integer(val.clone().as_signed()),
        ast::Pattern::Bool(val) => hir::PatternKind::Bool(*val),
        ast::Pattern::Path(path) => {
            match (try_lookup_enum_variant(path, ctx), path.inner.0.as_slice()) {
                (Ok(kind), _) => kind,
                (_, [segment]) => {
                    let ident = segment.unwrap_named();
                    // Check if this is declaring a variable
                    let (name_id, pre_declared) =
                        if let Some(state) = ctx.symtab.get_declaration(ident) {
                            match state.inner {
                                DeclarationState::Undefined(id) => {
                                    ctx.symtab
                                        .mark_declaration_defined(ident.clone(), ident.loc());
                                    (id, true)
                                }
                                DeclarationState::Undecleared(id) => {
                                    ctx.symtab.add_thing_with_name_id(
                                        id.clone(),
                                        Thing::Variable(ident.clone()),
                                        None,
                                        None,
                                    );
                                    ctx.symtab
                                        .mark_declaration_defined(ident.clone(), ident.loc());
                                    (id, true)
                                }
                                DeclarationState::Defined(previous) => {
                                    return Err(Diagnostic::error(
                                        ident,
                                        format!("{ident} was already defined"),
                                    )
                                    .secondary_label(previous, "First defined here")
                                    .primary_label("Later defined here")
                                    .secondary_label(state.loc(), format!("{ident} declared here"))
                                    .note("Declared variables can only be defined once"));
                                }
                            }
                        } else {
                            (
                                ctx.symtab.add_thing(
                                    Path::ident(ident.clone()),
                                    Thing::Variable(ident.clone()),
                                    None,
                                    None,
                                ),
                                false,
                            )
                        };

                    hir::PatternKind::Name {
                        name: name_id.at_loc(ident),
                        pre_declared,
                    }
                }
                (_, []) => unreachable!(),
                (Err(e), _) => return Err(e),
            }
        }
        ast::Pattern::Tuple(pattern) => {
            let inner = pattern
                .iter()
                .map(|p| p.try_map_ref(|p| visit_pattern(p, ctx)))
                .collect::<Result<_>>()?;
            hir::PatternKind::Tuple(inner)
        }
        ast::Pattern::Array(patterns) => {
            let inner = patterns
                .iter()
                .map(|p| p.try_map_ref(|p| visit_pattern(p, ctx)))
                .collect::<Result<_>>()?;
            hir::PatternKind::Array(inner)
        }
        ast::Pattern::Type(path, args) => {
            // Look up the name to see if it's an enum variant.
            let (name_id, p) = ctx.symtab.lookup_patternable_type(path)?;
            match &args.inner {
                ast::ArgumentPattern::Named(patterns) => {
                    let mut bound = HashSet::<Loc<Identifier>>::default();
                    let mut unbound = p
                        .params
                        .0
                        .iter()
                        .map(
                            |hir::Parameter {
                                 name: ident,
                                 ty: _,
                                 no_mangle: _,
                                 field_translator: _,
                             }| ident.inner.clone(),
                        )
                        .collect::<HashSet<_>>();

                    let mut patterns = patterns
                        .iter()
                        .map(|(target, pattern)| {
                            let ast_pattern = pattern.as_ref().cloned().unwrap_or_else(|| {
                                ast::Pattern::Path(Path::ident_with_loc(target.clone()))
                                    .at_loc(target)
                            });
                            let new_pattern = visit_pattern(&ast_pattern, ctx)?;
                            // Check if this is a new binding
                            if let Some(prev) = bound.get(target) {
                                return Err(Diagnostic::from(
                                    ArgumentError::DuplicateNamedBindings {
                                        new: target.clone(),
                                        prev_loc: prev.loc(),
                                    },
                                ));
                            }
                            bound.insert(target.clone());
                            if unbound.take(target).is_none() {
                                return Err(Diagnostic::from(ArgumentError::NoSuchArgument {
                                    name: target.clone(),
                                }));
                            }

                            let kind = match pattern {
                                Some(_) => hir::ArgumentKind::Named,
                                None => hir::ArgumentKind::ShortNamed,
                            };

                            Ok(hir::PatternArgument {
                                target: target.clone(),
                                value: new_pattern.at_loc(&ast_pattern),
                                kind,
                            })
                        })
                        .collect::<Result<Vec<_>>>()?;

                    if !unbound.is_empty() {
                        return Err(Diagnostic::from(ArgumentError::MissingArguments {
                            missing: unbound.into_iter().collect(),
                            at: args.loc(),
                        }));
                    }

                    patterns.sort_by_cached_key(|arg| p.params.arg_index(&arg.target).unwrap());

                    hir::PatternKind::Type(name_id.at_loc(path), patterns)
                }
                ast::ArgumentPattern::Positional(patterns) => {
                    // Ensure we have the correct amount of arguments
                    if p.params.argument_num() != patterns.len() {
                        return Err(Diagnostic::from(error::PatternListLengthMismatch {
                            expected: p.params.argument_num(),
                            got: patterns.len(),
                            at: args.loc(),
                            for_what: None,
                        }));
                    }

                    let patterns = patterns
                        .iter()
                        .zip(p.params.0.iter())
                        .map(|(p, arg)| {
                            let pat = p.try_map_ref(|p| visit_pattern(p, ctx))?;
                            Ok(hir::PatternArgument {
                                target: arg.name.clone(),
                                value: pat,
                                kind: hir::ArgumentKind::Positional,
                            })
                        })
                        .collect::<Result<Vec<_>>>()?;

                    hir::PatternKind::Type(name_id.at_loc(path), patterns)
                }
            }
        }
    };
    Ok(kind.with_id(ctx.idtracker.next()))
}

fn try_visit_statement(
    s: &Loc<ast::Statement>,
    ctx: &mut Context,
) -> Result<Vec<Loc<hir::Statement>>> {
    match &s.inner {
        ast::Statement::Declaration(names) => {
            let names = names
                .iter()
                .map(|name| {
                    ctx.symtab
                        .add_declaration(name.clone())
                        .map(|decl| decl.at_loc(name))
                })
                .filter_map(|name| name.handle_in(&mut ctx.diags.lock().unwrap()))
                .collect::<Vec<_>>();

            Ok(vec![hir::Statement::Declaration(names).at_loc(s)])
        }
        ast::Statement::Binding(Binding {
            pattern,
            ty,
            value,
            attrs,
        }) => {
            let mut stmts = vec![];

            let hir_type = if let Some(t) = ty {
                Some(visit_type_spec(t, &TypeSpecKind::BindingType, ctx)?)
            } else {
                None
            };

            let mut value = value.visit(visit_expression, ctx);

            let pattern = pattern.try_visit(visit_pattern, ctx)?;

            let mut wal_trace = None;
            attrs.lower(&mut |attr| match &attr.inner {
                ast::Attribute::WalTrace { clk, rst } => {
                    wal_trace = Some(
                        WalTrace {
                            clk: clk.as_ref().map(|x| x.visit(visit_expression, ctx)),
                            rst: rst.as_ref().map(|x| x.visit(visit_expression, ctx)),
                        }
                        .at_loc(attr),
                    );
                    Ok(None)
                }
                ast::Attribute::WalSuffix { suffix } => {
                    // All names in the pattern should have the suffix applied to them
                    for name in pattern.get_names() {
                        stmts.push(
                            hir::Statement::WalSuffixed {
                                suffix: suffix.inner.clone(),
                                target: name.clone(),
                            }
                            .at_loc(suffix),
                        );
                    }
                    Ok(None)
                }
                ast::Attribute::VerilogAttrs { entries }
                    if inject_verilog_attrs(&mut value, entries) =>
                {
                    Ok(None)
                }
                ast::Attribute::VerilogAttrs { .. }
                | ast::Attribute::NoMangle { .. }
                | ast::Attribute::Fsm { .. }
                | ast::Attribute::Optimize { .. }
                | ast::Attribute::Deprecated { .. }
                | ast::Attribute::Documentation { .. }
                | ast::Attribute::SurferTranslator(_)
                | ast::Attribute::SpadecParenSugar
                | ast::Attribute::WalTraceable { .. } => Err(attr.report_unused("let binding")),
            })?;

            stmts.push(
                hir::Statement::Binding(hir::Binding {
                    pattern,
                    ty: hir_type,
                    value,
                    wal_trace,
                })
                .at_loc(s),
            );
            Ok(stmts)
        }
        ast::Statement::Expression(expr, attrs) => {
            let mut value = expr.visit(visit_expression, ctx);
            attrs.lower(&mut |attr| match &attr.inner {
                ast::Attribute::VerilogAttrs { entries }
                    if inject_verilog_attrs(&mut value, entries) =>
                {
                    Ok(None)
                }
                ast::Attribute::VerilogAttrs { .. }
                | ast::Attribute::WalTrace { .. }
                | ast::Attribute::WalSuffix { .. }
                | ast::Attribute::NoMangle { .. }
                | ast::Attribute::Fsm { .. }
                | ast::Attribute::Optimize { .. }
                | ast::Attribute::Deprecated { .. }
                | ast::Attribute::Documentation { .. }
                | ast::Attribute::SurferTranslator(_)
                | ast::Attribute::SpadecParenSugar
                | ast::Attribute::WalTraceable { .. } => {
                    Err(attr.report_unused("expression statement"))
                }
            })?;
            Ok(vec![hir::Statement::Expression(value).at_loc(expr)])
        }
        ast::Statement::Register(inner) => visit_register(inner, ctx),
        ast::Statement::PipelineRegMarker(count, cond) => {
            let cond = match cond {
                Some(cond) => Some(cond.visit(visit_expression, ctx)),
                None => None,
            };

            let extra = match (count, cond) {
                (None, None) => None,
                (Some(count), None) => Some(hir::PipelineRegMarkerExtra::Count {
                    count: count.try_map_ref(|c| {
                        visit_type_expression(c, &TypeSpecKind::PipelineRegCount, ctx)
                    })?,
                    count_typeexpr_id: ctx.idtracker.next(),
                }),
                (None, Some(cond)) => Some(hir::PipelineRegMarkerExtra::Condition(cond)),
                (Some(count), Some(cond)) => {
                    return Err(Diagnostic::error(
                        count,
                        "Multiple registers with conditions can not be defined",
                    )
                    .primary_label("Multiple registers not allowed")
                    .secondary_label(cond, "Condition specified here")
                    .help("Consider splitting into two reg statements"));
                }
            };

            Ok(vec![hir::Statement::PipelineRegMarker(extra).at_loc(s)])
        }
        ast::Statement::Label(name) => {
            // NOTE: pipeline labels are lowered in visit_pipeline
            let (name, sym) = ctx
                .symtab
                .lookup_type_symbol(&Path::ident(name.clone()).at_loc(name), false)?;
            Ok(vec![hir::Statement::Label(name.at_loc(&sym)).at_loc(s)])
        }
        ast::Statement::Assert(expr) => {
            let expr = expr.visit(visit_expression, ctx);

            Ok(vec![hir::Statement::Assert(expr).at_loc(s)])
        }
        ast::Statement::Set { target, value } => {
            let target = target.visit(visit_expression, ctx);
            let value = value.visit(visit_expression, ctx);

            Ok(vec![hir::Statement::Set { target, value }.at_loc(s)])
        }
    }
}

fn visit_statement(s: &Loc<ast::Statement>, ctx: &mut Context) -> Vec<Loc<hir::Statement>> {
    match try_visit_statement(s, ctx) {
        Ok(result) => result,
        Err(e) => {
            ctx.diags.lock().unwrap().errors.push(e);
            vec![hir::Statement::Error.at_loc(s)]
        }
    }
}

#[tracing::instrument(skip_all)]
fn visit_argument_list(
    arguments: &ast::ArgumentList,
    ctx: &mut Context,
) -> Result<hir::ArgumentList<hir::Expression>> {
    match arguments {
        ast::ArgumentList::Positional(args) => {
            let inner = args
                .iter()
                .map(|arg| arg.visit(visit_expression, ctx))
                .collect::<_>();

            Ok(hir::ArgumentList::Positional(inner))
        }
        ast::ArgumentList::Named(args) => {
            let inner = args
                .iter()
                .map(|arg| match arg {
                    ast::NamedArgument::Full(name, expr) => {
                        Ok(hir::expression::NamedArgument::Full(
                            name.clone(),
                            expr.visit(visit_expression, ctx),
                        ))
                    }
                    ast::NamedArgument::Short(name) => {
                        let expr = ast::Expression::Identifier(Path::ident_with_loc(name.clone()))
                            .at_loc(name);

                        Ok(hir::expression::NamedArgument::Short(
                            name.clone(),
                            expr.visit(visit_expression, ctx),
                        ))
                    }
                })
                .collect::<Result<_>>()?;

            Ok(hir::ArgumentList::Named(inner))
        }
    }
}

pub fn visit_call_kind(
    kind: &ast::CallKind,
    ctx: &mut Context,
) -> Result<hir::expression::CallKind> {
    Ok(match kind {
        ast::CallKind::Function => hir::expression::CallKind::Function,
        ast::CallKind::Entity(loc) => hir::expression::CallKind::Entity(*loc),
        ast::CallKind::Pipeline(loc, depth) => {
            let depth = depth
                .try_map_ref(|e| visit_type_expression(e, &TypeSpecKind::PipelineInstDepth, ctx))?;
            hir::expression::CallKind::Pipeline {
                inst_loc: *loc,
                depth,
                depth_typeexpr_id: ctx.idtracker.next(),
            }
        }
    })
}

pub fn visit_turbofish(
    t: &Loc<ast::TurbofishInner>,
    ctx: &mut Context,
) -> Result<Loc<hir::ArgumentList<TypeExpression>>> {
    t.try_map_ref(|args| match args {
        ast::TurbofishInner::Named(fishes) => fishes
            .iter()
            .map(|fish| match &fish.inner {
                ast::NamedTurbofish::Short(name) => {
                    let arg = ast::TypeExpression::TypeSpec(Box::new(
                        ast::TypeSpec::Named(Path::ident_with_loc(name.clone()), None).at_loc(name),
                    ));

                    let arg =
                        visit_type_expression(&arg, &TypeSpecKind::Turbofish, ctx)?.at_loc(name);
                    Ok(hir::expression::NamedArgument::Short(name.clone(), arg))
                }
                ast::NamedTurbofish::Full(name, arg) => {
                    let arg =
                        visit_type_expression(arg, &TypeSpecKind::Turbofish, ctx)?.at_loc(arg);
                    Ok(hir::expression::NamedArgument::Full(name.clone(), arg))
                }
            })
            .collect::<Result<Vec<_>>>()
            .map(|params| hir::ArgumentList::Named(params)),
        ast::TurbofishInner::Positional(args) => args
            .iter()
            .map(|arg| {
                arg.try_map_ref(|arg| visit_type_expression(arg, &TypeSpecKind::Turbofish, ctx))
            })
            .collect::<Result<_>>()
            .map(hir::ArgumentList::Positional),
    })
}

fn visit_expression_result(e: &ast::Expression, ctx: &mut Context) -> Result<hir::ExprKind> {
    match e {
        ast::Expression::IntLiteral(val) => {
            let kind = match &val.inner {
                ast::IntLiteral::Unsized(_) => IntLiteralKind::Unsized,
                ast::IntLiteral::Signed { val: _, size } => IntLiteralKind::Signed(size.clone()),
                ast::IntLiteral::Unsigned { val: _, size } => {
                    IntLiteralKind::Unsigned(size.clone())
                }
            };
            Ok(hir::ExprKind::IntLiteral(
                val.inner.clone().as_signed(),
                kind,
            ))
        }
        ast::Expression::BoolLiteral(val) => Ok(hir::ExprKind::BoolLiteral(val.inner)),
        ast::Expression::StrLiteral(val) => Err(Diagnostic::error(
            val,
            "Unicode strings are not supported inside expressions",
        )
        .primary_label("Unicode strings are not supported in expressions")
        .span_suggest_insert_before("Consider using an ASCII string", val, "b")),
        ast::Expression::TriLiteral(lit) => {
            let result = match lit.inner {
                ast::BitLiteral::Low => hir::expression::TriLiteral::Low,
                ast::BitLiteral::High => hir::expression::TriLiteral::High,
                ast::BitLiteral::HighImp => hir::expression::TriLiteral::HighImp,
            };
            Ok(hir::ExprKind::TriLiteral(result))
        }
        ast::Expression::CreatePorts => Ok(hir::ExprKind::CreatePorts),
        ast::Expression::BinaryOperator(lhs, tok, rhs) => {
            let lhs = lhs.visit(visit_expression, ctx);
            let rhs = rhs.visit(visit_expression, ctx);

            let operator = |op: BinaryOperator| {
                hir::ExprKind::BinaryOperator(Box::new(lhs), op.at_loc(tok), Box::new(rhs))
            };

            match tok.inner {
                ast::BinaryOperator::Add => Ok(operator(BinaryOperator::Add)),
                ast::BinaryOperator::Sub => Ok(operator(BinaryOperator::Sub)),
                ast::BinaryOperator::Mul => Ok(operator(BinaryOperator::Mul)),
                ast::BinaryOperator::Div => Ok(operator(BinaryOperator::Div)),
                ast::BinaryOperator::Mod => Ok(operator(BinaryOperator::Mod)),
                ast::BinaryOperator::Eq => Ok(operator(BinaryOperator::Eq)),
                ast::BinaryOperator::Neq => Ok(operator(BinaryOperator::NotEq)),
                ast::BinaryOperator::Gt => Ok(operator(BinaryOperator::Gt)),
                ast::BinaryOperator::Lt => Ok(operator(BinaryOperator::Lt)),
                ast::BinaryOperator::Ge => Ok(operator(BinaryOperator::Ge)),
                ast::BinaryOperator::Le => Ok(operator(BinaryOperator::Le)),
                ast::BinaryOperator::LeftShift => Ok(operator(BinaryOperator::LeftShift)),
                ast::BinaryOperator::RightShift => Ok(operator(BinaryOperator::RightShift)),
                ast::BinaryOperator::ArithmeticRightShift => {
                    Ok(operator(BinaryOperator::ArithmeticRightShift))
                }
                ast::BinaryOperator::LogicalAnd => Ok(operator(BinaryOperator::LogicalAnd)),
                ast::BinaryOperator::LogicalOr => Ok(operator(BinaryOperator::LogicalOr)),
                ast::BinaryOperator::LogicalXor => Ok(operator(BinaryOperator::LogicalXor)),
                ast::BinaryOperator::BitwiseOr => Ok(operator(BinaryOperator::BitwiseOr)),
                ast::BinaryOperator::BitwiseAnd => Ok(operator(BinaryOperator::BitwiseAnd)),
                ast::BinaryOperator::BitwiseXor => Ok(operator(BinaryOperator::BitwiseXor)),
            }
        }
        ast::Expression::UnaryOperator(operator, operand) => {
            let operand = operand.visit(visit_expression, ctx);

            let unop = |op: hir::expression::UnaryOperator| {
                hir::ExprKind::UnaryOperator(op.at_loc(operator), Box::new(operand))
            };
            match operator.inner {
                ast::UnaryOperator::Sub => Ok(unop(hir::expression::UnaryOperator::Sub)),
                ast::UnaryOperator::Not => Ok(unop(hir::expression::UnaryOperator::Not)),
                ast::UnaryOperator::BitwiseNot => {
                    Ok(unop(hir::expression::UnaryOperator::BitwiseNot))
                }
                ast::UnaryOperator::Dereference => {
                    Ok(unop(hir::expression::UnaryOperator::Dereference))
                }
                ast::UnaryOperator::Reference => {
                    Ok(unop(hir::expression::UnaryOperator::Reference))
                }
            }
        }
        ast::Expression::Parenthesized(expr) => visit_expression_result(expr, ctx),
        ast::Expression::TupleLiteral(exprs) => {
            let exprs = exprs
                .iter()
                .map(|e| e.visit(visit_expression, ctx))
                .collect::<Vec<_>>();
            Ok(hir::ExprKind::TupleLiteral(exprs))
        }
        ast::Expression::ArrayLiteral(exprs) => {
            ctx.in_new_scope(|ctx| {
                // First, resolve any labels we find
                for (i, (label, _expr)) in exprs.iter().enumerate() {
                    if let Some(label) = label {
                        ctx.symtab.add_thing(
                            Path::ident(label.clone()),
                            Thing::ArrayLabel(i.at_loc(label)),
                            None,
                            None,
                        );
                    }
                }

                // Then generate the result
                let exprs = exprs
                    .iter()
                    .map(|(_label, e)| e.visit(visit_expression, ctx))
                    .collect::<Vec<_>>();

                Ok(hir::ExprKind::ArrayLiteral(exprs))
            })
        }
        ast::Expression::ArrayShorthandLiteral(expr, amount) => {
            Ok(hir::ExprKind::ArrayShorthandLiteral(
                Box::new(visit_expression(expr, ctx).at_loc(expr)),
                visit_const_generic(amount, ctx)?.map(|c| c.with_id(ctx.idtracker.next())),
            ))
        }
        ast::Expression::Index(target, index) => {
            let target = target.visit(visit_expression, ctx);
            let index = index.visit(visit_expression, ctx);
            Ok(hir::ExprKind::Index(Box::new(target), Box::new(index)))
        }
        ast::Expression::RangeIndex { target, start, end } => {
            let target = target.visit(visit_expression, ctx);
            Ok(hir::ExprKind::RangeIndex {
                target: Box::new(target),
                start: visit_const_generic(start, ctx)?.map(|c| c.with_id(ctx.idtracker.next())),
                end: visit_const_generic(end, ctx)?.map(|c| c.with_id(ctx.idtracker.next())),
            })
        }
        ast::Expression::TupleIndex {
            target,
            index,
            deprecated_syntax,
        } => {
            if *deprecated_syntax {
                let loc = ().between_locs(&target, &index);
                ctx.diags.lock().unwrap().errors.push(
                    Diagnostic::warning(loc, "Deprecated tuple syntax indexing")
                        .primary_label("`#` syntax for tuple indexing is deprecated")
                        .note("replace `#` with `.`"),
                );
            }

            Ok(hir::ExprKind::TupleIndex(
                Box::new(target.visit(visit_expression, ctx)),
                *index,
            ))
        }
        ast::Expression::FieldAccess(target, field) => Ok(hir::ExprKind::FieldAccess(
            Box::new(target.visit(visit_expression, ctx)),
            field.clone(),
        )),
        ast::Expression::MethodCall {
            kind,
            target,
            name,
            args,
            turbofish,
        } => {
            let target = target.visit(visit_expression, ctx);
            Ok(hir::ExprKind::MethodCall {
                target: Box::new(target),
                name: name.clone(),
                args: args.try_map_ref(|args| visit_argument_list(args, ctx))?,
                call_kind: visit_call_kind(kind, ctx)?,
                turbofish: turbofish
                    .as_ref()
                    .map(|t| visit_turbofish(t, ctx))
                    .transpose()?,
                safety: ctx.safety,
            })
        }
        ast::Expression::If(cond, ontrue, onfalse) => {
            let cond = cond.visit(visit_expression, ctx);
            let ontrue = ontrue.visit(visit_expression, ctx);
            let onfalse = onfalse.visit(visit_expression, ctx);

            Ok(hir::ExprKind::If(
                Box::new(cond),
                Box::new(ontrue),
                Box::new(onfalse),
            ))
        }
        ast::Expression::TypeLevelIf(cond, ontrue, onfalse) => {
            let cond = visit_const_generic(cond, ctx)?;
            let ontrue = ontrue.visit(visit_expression, ctx);
            let onfalse = onfalse.visit(visit_expression, ctx);

            Ok(hir::ExprKind::TypeLevelIf(
                cond.map(|cond| cond.with_id(ctx.idtracker.next())),
                Box::new(ontrue),
                Box::new(onfalse),
            ))
        }
        ast::Expression::Match(expression, branches) => {
            let e = expression.visit(visit_expression, ctx);

            if branches.is_empty() {
                return Err(Diagnostic::error(branches, "Match body has no arms")
                    .primary_label("This match body has no arms"));
            }

            let b = branches
                .iter()
                .map(|(pattern, if_condition, result)| {
                    ctx.symtab.new_scope();
                    let p = pattern.try_visit(visit_pattern, ctx)?;
                    let c = if_condition
                        .as_ref()
                        .map(|c| c.visit(visit_expression, ctx));
                    let r = result.visit(visit_expression, ctx);
                    ctx.symtab.close_scope();
                    Ok((p, c, r))
                })
                .collect::<Result<Vec<_>>>()?;

            Ok(hir::ExprKind::Match(Box::new(e), b))
        }
        ast::Expression::Block(block) => {
            Ok(hir::ExprKind::Block(Box::new(visit_block(block, ctx)?)))
        }
        ast::Expression::Unsafe(block) => {
            let outside = ::core::mem::replace(&mut ctx.safety, Safety::Unsafe);
            if outside == Safety::Unsafe {
                ctx.diags.lock().unwrap().errors.push(
                    Diagnostic::warning(block.loc(), "Unnecessary unsafe block")
                        .note("This block is already in unsafe context"),
                );
            }
            let res = visit_block(block, ctx);
            ctx.safety = outside;
            Ok(hir::ExprKind::Block(Box::new(res?)))
        }
        ast::Expression::Lambda { .. } => {
            let outside = ::core::mem::replace(&mut ctx.safety, Safety::Default);
            let res = visit_lambda(e, ctx);
            ctx.safety = outside;
            res
        }
        ast::Expression::Call {
            kind,
            callee,
            args,
            turbofish,
        } => {
            let (name_id, _) = ctx.symtab.lookup_unit(callee)?;
            let args = visit_argument_list(args, ctx)?.at_loc(args);

            let kind = visit_call_kind(kind, ctx)?;

            let turbofish = turbofish
                .as_ref()
                .map(|t| visit_turbofish(t, ctx))
                .transpose()?;

            Ok(hir::ExprKind::Call {
                kind,
                callee: name_id.at_loc(callee),
                args,
                turbofish,
                safety: ctx.safety,
                verilog_attr_groups: vec![],
            })
        }
        ast::Expression::Identifier(path) => {
            // If the identifier isn't a valid variable, report as "expected value".
            match ctx.symtab.lookup_variable(path) {
                Ok(id) => Ok(hir::ExprKind::Identifier(id)),
                Err(LookupError::IsAType(_, _)) => {
                    let ty = ctx.symtab.lookup_type_symbol(path, false)?;
                    let (name, ty) = &ty;
                    match ty.inner {
                        TypeSymbol::GenericMeta(
                            MetaType::Int | MetaType::Uint | MetaType::Number | MetaType::Str,
                        ) => Ok(hir::ExprKind::TypeLevelInteger(name.clone())),
                        TypeSymbol::GenericMeta(_) | TypeSymbol::GenericArg { traits: _ } => {
                            Err(Diagnostic::error(
                                path,
                                format!("Generic type {name} is a type but it is used as a value"),
                            )
                            .primary_label(format!("{name} is a type"))
                            .secondary_label(ty, format!("{name} is declared here"))
                            .span_suggest_insert_before(
                                format!("Consider making `{name}` a type level integer"),
                                ty,
                                "#int ",
                            )
                            .span_suggest_insert_before(
                                format!("or a type level uint"),
                                ty,
                                "#uint ",
                            ))
                        }
                        TypeSymbol::Declared(_, _, _) | TypeSymbol::Alias(_) => Err(
                            Diagnostic::error(path, format!("Type {name} is used as a value"))
                                .primary_label(format!("{name} is a type")),
                        ),
                    }
                }
                Err(LookupError::NotAVariable(path, ref was @ Thing::EnumVariant(_)))
                | Err(LookupError::NotAVariable(
                    path,
                    ref was @ Thing::Alias {
                        loc: _,
                        path: _,
                        in_namespace: _,
                    },
                )) => {
                    let (name_id, variant) = match ctx.symtab.lookup_enum_variant(&path) {
                        Ok(res) => res,
                        Err(_) => return Err(LookupError::NotAValue(path, was.clone()).into()),
                    };
                    if variant.params.0.is_empty() {
                        // NOTE: This loc is a little bit approximate because it is unlikely
                        // that any error will reference the empty argument list.
                        let callee = name_id.at_loc(&path);
                        let args = hir::ArgumentList::Positional(vec![]).at_loc(&path);
                        Ok(hir::ExprKind::Call {
                            kind: hir::expression::CallKind::Function,
                            callee,
                            args,
                            turbofish: None,
                            safety: ctx.safety,
                            verilog_attr_groups: vec![],
                        })
                    } else {
                        Err(LookupError::NotAValue(path, was.clone()).into())
                    }
                }
                Err(LookupError::NotAVariable(path, was)) => {
                    Err(LookupError::NotAValue(path, was).into())
                }
                Err(err) => Err(err.into()),
            }
        }
        ast::Expression::PipelineReference {
            stage_kw_and_reference_loc,
            stage,
            name,
        } => {
            let stage = match stage {
                ast::PipelineStageReference::Relative(offset) => {
                    hir::expression::PipelineRefKind::Relative(offset.try_map_ref(|t| {
                        visit_type_expression(t, &TypeSpecKind::PipelineInstDepth, ctx)
                    })?)
                }
                ast::PipelineStageReference::Absolute(name) => {
                    hir::expression::PipelineRefKind::Absolute(
                        ctx.symtab
                            .lookup_type_symbol(&Path::ident(name.clone()).at_loc(name), false)?
                            .0
                            .at_loc(name),
                    )
                }
            }
            .at_loc(stage_kw_and_reference_loc);

            let pipeline_ctx = ctx
                .pipeline_ctx
                .as_ref()
                .expect("Expected to have a pipeline context");

            let path = Path::ident_with_loc(name.clone());
            let (name_id, declares_name) = match ctx.symtab.try_lookup_variable(&path)? {
                Some(id) => (id.at_loc(name), false),
                None => {
                    let pipeline_offset = ctx.symtab.current_scope() - pipeline_ctx.scope;
                    let undecleared_lookup = ctx.symtab.declarations[pipeline_ctx.scope].get(name);

                    if let Some(DeclarationState::Undecleared(name_id)) = undecleared_lookup {
                        (name_id.clone().at_loc(name), false)
                    } else {
                        let name_id = ctx
                            .symtab
                            .add_undecleared_at_offset(pipeline_offset, name.clone());
                        (name_id.at_loc(name), true)
                    }
                }
            };

            Ok(hir::ExprKind::PipelineRef {
                stage,
                name: name_id,
                declares_name,
                depth_typeexpr_id: ctx.idtracker.next(),
            })
        }
        ast::Expression::LabelAccess { label, field } => {
            let (_, label_target) = ctx.symtab.lookup_thing(label)?;

            match label_target {
                Thing::ArrayLabel(val) => match field.inner.as_str() {
                    "index" => Ok(hir::ExprKind::IntLiteral(
                        BigInt::from_usize(val.inner).unwrap(),
                        IntLiteralKind::Unsized,
                    )),
                    _ => Err(Diagnostic::error(field, "Array labels only support .index")
                        .primary_label("Unknown field on array label")
                        .secondary_label(val, "Array label defined here")),
                },
                other => Err(Diagnostic::error(
                    label,
                    format!("Expected a label, found {}", other.kind_string()),
                )
                .primary_label("Expected label")
                .secondary_label(other.name_loc(), format!("{} is defined here", label))),
            }
        }
        ast::Expression::StageReady => Ok(hir::ExprKind::StageReady),
        ast::Expression::StageValid => Ok(hir::ExprKind::StageValid),
        ast::Expression::StaticUnreachable(message) => {
            Ok(hir::ExprKind::StaticUnreachable(message.clone()))
        }
    }
}

fn check_for_undefined(ctx: &mut Context) {
    for problem in &ctx.symtab.get_undefined_declarations() {
        match problem {
            (undefined, DeclarationState::Undefined(_)) => {
                Err(
                    Diagnostic::error(undefined, "Declared variable is not defined")
                        .primary_label("This variable is declared but not defined")
                        // FIXME: Suggest removing the declaration (with a diagnostic suggestion) only if the variable is unused.
                        .help(format!("Define {undefined} with a let or reg binding"))
                        .help("Or, remove the declaration if the variable is unused"),
                )
            }
            (undecleared, DeclarationState::Undecleared(_)) => Err(Diagnostic::error(
                undecleared,
                "Could not find referenced variable",
            )
            .primary_label("This variable could not be found")),
            (_, _) => Ok(()),
        }
        .handle_in(&mut ctx.diags.lock().unwrap());
    }
}

#[recursive]
#[tracing::instrument(skip_all, fields(kind=e.variant_str()))]
pub fn visit_expression(e: &ast::Expression, ctx: &mut Context) -> hir::Expression {
    let new_id = ctx.idtracker.next();

    let kind = match visit_expression_result(e, ctx) {
        Ok(kind) => kind,
        Err(e) => {
            ctx.diags.lock().unwrap().errors.push(e);
            ExprKind::Error
        }
    };

    kind.with_id(new_id)
}

fn visit_block(b: &ast::Block, ctx: &mut Context) -> Result<hir::Block> {
    ctx.symtab.new_scope();
    let statements = b
        .statements
        .iter()
        .map(|statement| visit_statement(statement, ctx))
        .collect::<Vec<_>>()
        .into_iter()
        .flatten()
        .collect::<Vec<_>>();

    let result = b.result.as_ref().map(|o| o.visit(visit_expression, ctx));

    check_for_undefined(ctx);

    ctx.symtab.close_scope();

    Ok(hir::Block { statements, result })
}

fn visit_register(reg: &Loc<ast::Register>, ctx: &mut Context) -> Result<Vec<Loc<hir::Statement>>> {
    let (reg, loc) = reg.split_loc_ref();

    let pattern = reg.pattern.try_visit(visit_pattern, ctx)?;

    let clock = reg.clock.visit(visit_expression, ctx);

    let reset = if let Some((trig, value)) = &reg.reset {
        Some((
            trig.visit(visit_expression, ctx),
            value.visit(visit_expression, ctx),
        ))
    } else {
        None
    };

    let initial = reg.initial.as_ref().map(|i| i.visit(visit_expression, ctx));

    let value = reg.value.visit(visit_expression, ctx);

    let value_type = if let Some(value_type) = &reg.value_type {
        Some(visit_type_spec(
            value_type,
            &TypeSpecKind::BindingType,
            ctx,
        )?)
    } else {
        None
    };

    let mut stmts = vec![];

    let attributes = reg
        .attributes
        .lower(&mut |attr| match &attr.inner {
            ast::Attribute::Fsm { state } => {
                let name_id = if let Some(state) = state {
                    ctx.symtab
                        .lookup_variable(&Path::ident_with_loc(state.clone()))?
                } else if let PatternKind::Name { name, .. } = &pattern.inner.kind {
                    name.inner.clone()
                } else {
                    return Err(Diagnostic::error(
                        attr,
                        "#[fsm] without explicit name on non-name pattern",
                    )
                    .secondary_label(&pattern, "This is a pattern")
                    .span_suggest(
                        "Consider specifying the name of the s ignal containing the state",
                        attr,
                        "#[fsm(<name>)]",
                    ));
                };

                Ok(Some(hir::Attribute::Fsm { state: name_id }))
            }
            ast::Attribute::WalSuffix { suffix } => {
                // All names in the pattern should have the suffix applied to them
                for name in pattern.get_names() {
                    stmts.push(
                        hir::Statement::WalSuffixed {
                            suffix: suffix.inner.clone(),
                            target: name.clone(),
                        }
                        .at_loc(suffix),
                    );
                }
                Ok(None)
            }
            _ => Err(attr.report_unused("a register")),
        })
        .handle_in(&mut ctx.diags.lock().unwrap())
        .unwrap_or_else(|| hir::AttributeList::empty());

    stmts.push(
        hir::Statement::Register(hir::Register {
            pattern,
            clock,
            reset,
            initial,
            value,
            value_type,
            attributes,
        })
        .at_loc(&loc),
    );

    Ok(stmts)
}

fn inject_verilog_attrs(
    expr: &mut Loc<hir::Expression>,
    verilog_attrs: &Vec<(Loc<Identifier>, Option<Loc<String>>)>,
) -> bool {
    match &mut expr.inner.kind {
        ExprKind::Call {
            verilog_attr_groups,
            ..
        } => {
            verilog_attr_groups.push(verilog_attrs.clone());
            true
        }
        ExprKind::Error
        | ExprKind::Identifier(_)
        | ExprKind::IntLiteral(_, _)
        | ExprKind::BoolLiteral(_)
        | ExprKind::TriLiteral(_)
        | ExprKind::TypeLevelInteger(_)
        | ExprKind::CreatePorts
        | ExprKind::TupleLiteral(_)
        | ExprKind::ArrayLiteral(_)
        | ExprKind::ArrayShorthandLiteral(_, _)
        | ExprKind::Index(_, _)
        | ExprKind::RangeIndex { .. }
        | ExprKind::TupleIndex(_, _)
        | ExprKind::FieldAccess(_, _)
        | ExprKind::MethodCall { .. }
        | ExprKind::BinaryOperator(_, _, _)
        | ExprKind::UnaryOperator(_, _)
        | ExprKind::Match(_, _)
        | ExprKind::Block(_)
        | ExprKind::If(_, _, _)
        | ExprKind::TypeLevelIf(_, _, _)
        | ExprKind::PipelineRef { .. }
        | ExprKind::LambdaDef { .. }
        | ExprKind::StageValid
        | ExprKind::StageReady
        | ExprKind::StaticUnreachable(_)
        | ExprKind::Null => false,
    }
}
