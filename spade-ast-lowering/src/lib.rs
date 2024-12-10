mod attributes;
pub mod builtins;
mod comptime;
pub mod error;
pub mod global_symbols;
mod impls;
pub mod pipelines;
pub mod testutil;
pub mod types;

use attributes::LocAttributeExt;
use global_symbols::visit_meta_type;
use impls::visit_impl;
use itertools::{EitherOrBoth, Itertools};
use num::{BigInt, Zero};
use pipelines::PipelineContext;
use spade_diagnostics::{diag_bail, Diagnostic};
use spade_types::meta_types::MetaType;
use tracing::{event, info, Level};

use crate::attributes::AttributeListExt;
pub use crate::impls::ensure_unique_anonymous_traits;
use crate::pipelines::maybe_perform_pipelining_tasks;
use crate::types::{IsPort, IsSelf};
use ast::{Binding, CallKind, ParameterList, UnitKind};
use comptime::ComptimeCondExt;
use hir::expression::{BinaryOperator, IntLiteralKind};
use hir::param_util::ArgumentError;
use hir::symbol_table::DeclarationState;
use hir::symbol_table::{LookupError, SymbolTable, Thing, TypeSymbol};
use hir::{ConstGeneric, ExecutableItem, PatternKind, TraitName, WalTrace};
use spade_ast::{self as ast, ImplBlock, TypeParam, Unit, WhereClause};
pub use spade_common::id_tracker;
use spade_common::id_tracker::{ExprIdTracker, ImplIdTracker};
use spade_common::location_info::{Loc, WithLocation};
use spade_common::name::{Identifier, NameID, Path};
use spade_hir::{
    self as hir, ItemList, Module, TraitDef, TraitSpec, TypeExpression, TypeSpec, UnitHead,
};
use std::collections::{HashMap, HashSet};

use error::Result;

pub struct Context {
    pub symtab: SymbolTable,
    pub item_list: ItemList,
    pub idtracker: ExprIdTracker,
    pub impl_idtracker: ImplIdTracker,
    pub pipeline_ctx: Option<PipelineContext>,
    pub self_ctx: SelfContext,
}

trait LocExt<T> {
    fn try_visit<V, U>(&self, visitor: V, context: &mut Context) -> Result<Loc<U>>
    where
        V: Fn(&T, &mut Context) -> Result<U>;
}

impl<T> LocExt<T> for Loc<T> {
    fn try_visit<V, U>(&self, visitor: V, context: &mut Context) -> Result<Loc<U>>
    where
        V: Fn(&T, &mut Context) -> Result<U>,
    {
        self.map_ref(|t| visitor(t, context)).map_err(|e, _| e)
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
        } => {
            let trait_bounds: Vec<Loc<TraitSpec>> = traits
                .iter()
                .map(|t| visit_trait_spec(t, &TypeSpecKind::TraitBound, ctx))
                .collect::<Result<_>>()?;

            let name_id = ctx.symtab.add_type(
                Path::ident(ident.clone()),
                TypeSymbol::GenericArg {
                    traits: trait_bounds.clone(),
                }
                .at_loc(ident),
            );

            Ok(hir::TypeParam {
                ident: ident.clone(),
                name_id,
                trait_bounds,
                meta: MetaType::Type,
            })
        }
        ast::TypeParam::TypeWithMeta { meta, name } => {
            let meta = visit_meta_type(meta)?;
            let name_id = ctx.symtab.add_type(
                Path::ident(name.clone()),
                TypeSymbol::GenericMeta(meta.clone()).at_loc(name),
            );

            Ok(hir::TypeParam {
                ident: name.clone(),
                name_id,
                trait_bounds: vec![],
                meta,
            })
        }
    }
}

/// Visit an AST type parameter, converting it to a HIR type parameter. The name is not
/// added to the symbol table as this function is re-used for both global symbol collection
/// and normal HIR lowering.
#[tracing::instrument(skip_all, fields(name=%param.name()))]
pub fn re_visit_type_param(param: &ast::TypeParam, ctx: &Context) -> Result<hir::TypeParam> {
    match &param {
        ast::TypeParam::TypeName {
            name: ident,
            traits: _,
        } => {
            let path = Path::ident(ident.clone()).at_loc(ident);
            let (name_id, tsym) = ctx.symtab.lookup_type_symbol(&path)?;

            let trait_bounds = match &tsym.inner {
                TypeSymbol::GenericArg { traits } => traits.clone(),
                _ => return Err(Diagnostic::bug(
                    ident,
                    format!(
                        "Trait bound on {ident} on non-generic argument, which should've been caught by the first pass"
                    ),
                ))
            };

            Ok(hir::TypeParam {
                ident: ident.clone(),
                name_id,
                trait_bounds,
                meta: MetaType::Type,
            })
        }
        ast::TypeParam::TypeWithMeta { meta, name } => {
            let path = Path::ident(name.clone()).at_loc(name);
            let name_id = ctx.symtab.lookup_type_symbol(&path)?.0;
            Ok(hir::TypeParam {
                ident: name.clone(),
                name_id,
                trait_bounds: vec![],
                meta: visit_meta_type(meta)?,
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
    PipelineDepth,
    TraitBound,
}

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
        ast::TypeExpression::ConstGeneric(expr) => {
            let default_error = |message, primary| {
                Err(Diagnostic::error(
                    expr.as_ref(),
                    format!("{message} cannot have const generics in their type"),
                )
                .primary_label(format!("Const generic in {primary}")))
            };
            match kind {
                TypeSpecKind::Argument => default_error("Argument types", "argument type"),
                TypeSpecKind::OutputType => default_error("Return types", "return type"),
                TypeSpecKind::ImplTrait => default_error("Implemented traits", "implemented trait"),
                TypeSpecKind::ImplTarget => default_error("Impl targets", "impl target"),
                TypeSpecKind::EnumMember => default_error("Enum members", "enum member"),
                TypeSpecKind::StructMember => default_error("Struct members", "struct member"),
                TypeSpecKind::TraitBound => {
                    default_error("Traits used in trait bounds", "trait bound")
                }
                TypeSpecKind::Turbofish
                | TypeSpecKind::BindingType
                | TypeSpecKind::PipelineDepth => {
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
            let (base_id, base_t) = ctx.symtab.lookup_type_symbol(path)?;

            // Check if the type is a declared type or a generic argument.
            match &base_t.inner {
                TypeSymbol::Declared(generic_args, _) => {
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

                    if generic_args.len() != visited_params.len() {
                        Err(Diagnostic::error(
                            params
                                .as_ref()
                                .map(|p| ().at_loc(p))
                                .unwrap_or(().at_loc(t)),
                            "Wrong number of generic type parameters",
                        )
                        .primary_label(format!(
                            "Expected {} type parameter{}",
                            generic_args.len(),
                            if generic_args.len() != 1 { "s" } else { "" }
                        ))
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
                        ))
                    } else {
                        Ok(hir::TypeSpec::Declared(
                            base_id.at_loc(path),
                            visited_params,
                        ))
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
                        Ok(hir::TypeSpec::Generic(base_id.at_loc(path)))
                    }
                }
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
            // Check if this tuple is a port by checking if any of the contained types
            // are ports. If they are, retain the first one to use as a witness for this fact
            // for error reporting
            let transitive_port_witness = inner
                .iter()
                .map(|p| {
                    if p.is_port(&ctx.symtab)? {
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
                for ty in inner {
                    if !ty.is_port(&ctx.symtab)? {
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

            let inner = inner
                .iter()
                .map(|p| match visit_type_expression(p, kind, ctx)? {
                    hir::TypeExpression::TypeSpec(t) => Ok(t.at_loc(p)),
                    _ => {
                        return Err(Diagnostic::error(
                            p,
                            "Tuple elements must be types, not type level integers",
                        )
                        .primary_label("Tuples cannot contain non-types"))
                    }
                })
                .collect::<Result<Vec<_>>>()?;

            Ok(hir::TypeSpec::Tuple(inner))
        }
        ast::TypeSpec::Unit(w) => Ok(hir::TypeSpec::Unit(*w)),
        ast::TypeSpec::Wire(inner) => {
            if inner.is_port(&ctx.symtab)? {
                return Err(Diagnostic::from(error::WireOfPort {
                    full_type: t.loc(),
                    inner_type: inner.loc(),
                }));
            }

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

            Ok(hir::TypeSpec::Wire(Box::new(inner)))
        }
        ast::TypeSpec::Inverted(inner) => {
            if !inner.is_port(&ctx.symtab)? {
                return Err(Diagnostic::error(t, "A non-port type can not be inverted")
                    .primary_label("Inverting non-port")
                    .secondary_label(inner.as_ref(), "This is not a port"));
            } else {
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

                Ok(hir::TypeSpec::Inverted(Box::new(inner)))
            }
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
                TypeSpecKind::PipelineDepth => default_error("Pipeline depth", "pipeline depth"),
                TypeSpecKind::TraitBound => {
                    default_error("Traits used in trait bound", "trait bound")
                }
                TypeSpecKind::Turbofish | TypeSpecKind::BindingType => Ok(hir::TypeSpec::Wildcard),
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
) -> Result<Loc<hir::ParameterList>> {
    let mut arg_names: HashSet<Loc<Identifier>> = HashSet::new();
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

    if let Some(self_loc) = l.self_ {
        match &ctx.self_ctx {
            SelfContext::FreeStanding => {
                return Err(Diagnostic::error(
                    self_loc,
                    "'self' cannot be used in free standing units",
                )
                .primary_label("not allowed here"))
            }
            SelfContext::ImplBlock(spec) => result.push(hir::Parameter {
                no_mangle: None,
                name: Identifier(String::from("self")).at_loc(&self_loc),
                ty: spec.clone(),
            }),
            // When visiting trait definitions, we don't need to add self to the
            // symtab at all since we won't be visiting unit bodies here.
            // NOTE: This will be incorrect if we add default impls for traits
            SelfContext::TraitDefinition(_) => result.push(hir::Parameter {
                no_mangle: None,
                name: Identifier(String::from("self")).at_loc(&self_loc),
                ty: hir::TypeSpec::TraitSelf(self_loc).at_loc(&self_loc),
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
        let no_mangle = attrs.consume_no_mangle().map(|ident| ident.loc());
        attrs.report_unused("a parameter")?;

        result.push(hir::Parameter {
            name: name.clone(),
            ty: t,
            no_mangle,
        });
    }
    Ok(hir::ParameterList(result).at_loc(l))
}

/// Visit the head of an entity to generate an entity head
#[tracing::instrument(skip_all, fields(name=%head.name))]
pub fn unit_head(
    head: &ast::UnitHead,
    scope_type_params: &Option<Loc<Vec<Loc<TypeParam>>>>,
    scope_where_clauses: &[Loc<hir::WhereClause>],
    ctx: &mut Context,
) -> Result<hir::UnitHead> {
    ctx.symtab.new_scope();

    let scope_type_params = scope_type_params
        .as_ref()
        .map(Loc::strip_ref)
        .into_iter()
        .flatten()
        .map(|loc| loc.try_map_ref(|p| re_visit_type_param(p, ctx)))
        .collect::<Result<Vec<Loc<hir::TypeParam>>>>()?;

    let unit_type_params = head
        .type_params
        .as_ref()
        .map(Loc::strip_ref)
        .into_iter()
        .flatten()
        .map(|loc| loc.try_map_ref(|p| visit_type_param(p, ctx)))
        .collect::<Result<Vec<Loc<hir::TypeParam>>>>()?;

    let unit_where_clauses = visit_where_clauses(&head.where_clauses, ctx);

    let output_type = if let Some(output_type) = &head.output_type {
        Some(visit_type_spec(
            output_type,
            &TypeSpecKind::OutputType,
            ctx,
        )?)
    } else {
        None
    };

    let inputs = visit_parameter_list(&head.inputs, ctx)?;

    // Check for ports in functions
    // We need to have the scope open to check this, but we also need to close
    // the scope if we fail here, so we'll store port_error in a variable
    let mut port_error = Ok(());

    if let ast::UnitKind::Function = head.unit_kind.inner {
        for (_, _, ty) in &head.inputs.args {
            if matches!(ctx.self_ctx, SelfContext::TraitDefinition(_)) && ty.is_self()? {
                continue;
            };

            if ty.is_port(&ctx.symtab)? {
                port_error = Err(Diagnostic::error(ty, "Port argument in function")
                    .primary_label("This is a port")
                    .note("Only entities and pipelines can take ports as arguments")
                    .span_suggest_replace(
                        "Consider making this an entity",
                        &head.unit_kind,
                        "entity",
                    ))
            }
        }
    }

    let unit_kind: Result<_> = head.unit_kind.try_map_ref(|k| {
        let inner = match k {
            ast::UnitKind::Function => hir::UnitKind::Function(hir::FunctionKind::Fn),
            ast::UnitKind::Entity => hir::UnitKind::Entity,
            ast::UnitKind::Pipeline(depth) => hir::UnitKind::Pipeline {
                depth: depth
                    .inner
                    .maybe_unpack(&ctx.symtab)?
                    .ok_or_else(|| {
                        Diagnostic::error(depth, "Missing pipeline depth")
                            .primary_label("Missing pipeline depth")
                            .note("The current comptime branch does not specify a depth")
                    })?
                    .try_map_ref(|t| visit_type_expression(t, &TypeSpecKind::PipelineDepth, ctx))?,
                depth_typeexpr_id: ctx.idtracker.next(),
            },
        };
        Ok(inner)
    });

    ctx.symtab.close_scope();
    port_error?;
    let where_clauses = unit_where_clauses?
        .iter()
        .chain(scope_where_clauses.iter())
        .cloned()
        .collect();

    Ok(hir::UnitHead {
        name: head.name.clone(),
        inputs,
        output_type,
        unit_type_params,
        scope_type_params,
        unit_kind: unit_kind?,
        where_clauses,
    })
}

pub fn visit_const_generic(
    t: &Loc<ast::Expression>,
    ctx: &mut Context,
) -> Result<Loc<ConstGeneric>> {
    let kind = match &t.inner {
        ast::Expression::Identifier(name) => {
            let (name, sym) = ctx.symtab.lookup_type_symbol(name)?;
            match &sym.inner {
                TypeSymbol::Declared(_, _) => {
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
            }
        }
        ast::Expression::IntLiteral(val) => ConstGeneric::Const(val.clone().as_signed()),
        ast::Expression::BinaryOperator(lhs, op, rhs) => {
            let lhs = visit_const_generic(lhs, ctx)?;
            let rhs = visit_const_generic(rhs, ctx)?;

            match &op.inner {
                ast::BinaryOperator::Add => ConstGeneric::Add(Box::new(lhs), Box::new(rhs)),
                ast::BinaryOperator::Sub => ConstGeneric::Sub(Box::new(lhs), Box::new(rhs)),
                ast::BinaryOperator::Mul => ConstGeneric::Mul(Box::new(lhs), Box::new(rhs)),
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
                    Box::new(ConstGeneric::Const(BigInt::zero()).at_loc(&operand)),
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
        } => match callee.as_strs().as_slice() {
            ["uint_bits_to_fit"] => match &args.inner {
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
            WhereClause::GenericInt { target, expression } => {
                let make_diag = |primary| {
                    Diagnostic::error(
                        target,
                        format!("Expected `{}` to be a type level integer", target),
                    )
                    .primary_label(primary)
                    .secondary_label(expression, "This is an integer constraint")
                };
                let (name_id, sym) = match ctx.symtab.lookup_type_symbol(target) {
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
                            target: name_id.at_loc(target),
                            constraint: visit_const_generic(expression, ctx)?,
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
                let (name_id, sym) = match ctx.symtab.lookup_type_symbol(where_clause.target()) {
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
                                target: name_id.at_loc(target),
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
        .join(Path(vec![name.clone()]))
        .at_loc(&name.loc());

    let (id, head) = ctx
        .symtab
        .lookup_unit(&path)
        .map_err(|_| {
            ctx.symtab.print_symbols();
            println!("Failed to find {path:?} in symtab")
        })
        .expect("Attempting to lower an entity that has not been added to the symtab previously");

    let mut unit_name = if type_params.is_some() || scope_type_params.is_some() {
        hir::UnitName::WithID(id.clone().at_loc(name))
    } else {
        hir::UnitName::FullPath(id.clone().at_loc(name))
    };

    let mut wal_suffix = None;

    let attributes = attributes.lower(&mut |attr: &Loc<ast::Attribute>| match &attr.inner {
        ast::Attribute::Optimize { passes } => Ok(Some(hir::Attribute::Optimize {
            passes: passes.clone(),
        })),
        ast::Attribute::NoMangle => {
            if let Some(generic_list) = type_params {
                // if it's a verilog extern (so `body.is_none()`), then we allow generics insofar
                // as they are numbers (checked later on)
                if body.is_some() {
                    Err(
                        Diagnostic::error(attr, "no_mangle is not allowed on generic units")
                            .primary_label("no_mangle not allowed here")
                            .secondary_label(generic_list, "Because this unit is generic"),
                    )
                } else {
                    // yucky code duplication
                    unit_name = hir::UnitName::Unmangled(name.0.clone(), id.clone().at_loc(name));
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
                unit_name = hir::UnitName::Unmangled(name.0.clone(), id.clone().at_loc(name));
                Ok(None)
            }
        }
        ast::Attribute::WalSuffix { suffix } => {
            if body.is_none() {
                return Err(Diagnostic::error(
                    attr,
                    "wal_suffix is not allowed on __builtin__ units",
                )
                .primary_label("Not allowed on __builtin__ units"));
            }

            wal_suffix = Some(suffix.clone());
            Ok(None)
        }
        _ => Err(attr.report_unused("a unit")),
    })?;

    // If this is a builtin entity
    if body.is_none() {
        return Ok(hir::Item::Builtin(unit_name, head));
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
             }| {
                (
                    ctx.symtab.add_local_variable(ident.clone()).at_loc(ident),
                    ty.clone(),
                )
            },
        )
        .collect::<Vec<_>>();

    // Add the type params to the symtab to make them visible in the body
    for param in head.get_type_params() {
        let hir::TypeParam {
            ident,
            name_id,
            trait_bounds: _,
            meta: _,
        } = param.inner;
        ctx.symtab.re_add_type(ident, name_id)
    }

    ctx.pipeline_ctx = maybe_perform_pipelining_tasks(unit, &head, ctx)?;

    let mut body = body.as_ref().unwrap().try_visit(visit_expression, ctx)?;

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

    check_for_undefined(ctx)?;

    ctx.symtab.close_scope();

    info!("Checked all function arguments");

    Ok(hir::Item::Unit(
        hir::Unit {
            name: unit_name,
            head: head.clone().inner,
            attributes,
            inputs,
            body,
        }
        .at_loc(unit),
    ))
}

#[tracing::instrument(skip_all, fields(name=?trait_spec.path))]
pub fn visit_trait_spec(
    trait_spec: &Loc<ast::TraitSpec>,
    type_spec_kind: &TypeSpecKind,
    ctx: &mut Context,
) -> Result<Loc<hir::TraitSpec>> {
    let (name_id, loc) = match ctx.symtab.lookup_trait(&trait_spec.inner.path) {
        Ok(res) => res,
        Err(LookupError::IsAType(path)) => {
            let (_, loc) = ctx.symtab.lookup_type_symbol(&path)?;
            return Err(Diagnostic::error(
                path.clone(),
                format!("Unexpected type {}, expected a trait", path.inner),
            )
            .primary_label("Unexpected type")
            .secondary_label(loc, format!("Type {} defined here", path.inner)));
        }
        Err(err) => return Err(err.into()),
    };
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
    Ok(hir::TraitSpec { name, type_params }.at_loc(trait_spec))
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
        ast::Item::Module(m) => {
            ctx.symtab.push_namespace(m.name.clone());
            let result = visit_module(m, ctx);
            ctx.symtab.pop_namespace();
            result.map(|_| vec![])
        }
        ast::Item::Use(s) => match ctx.symtab.lookup_id(&s.path) {
            Ok(_) => Ok(vec![]),
            Err(lookup_error) => Err(lookup_error.into()),
        },
        ast::Item::Config(_) => Ok(vec![]),
    }
}

#[tracing::instrument(skip_all, fields(module.name = %module.name.inner))]
pub fn visit_module(module: &ast::Module, ctx: &mut Context) -> Result<()> {
    let path = &ctx
        .symtab
        .current_namespace()
        .clone()
        .at_loc(&module.name.loc());
    let id = ctx
        .symtab
        .lookup_id(path)
        .map_err(|_| {
            ctx.symtab.print_symbols();
            println!("Failed to find {path:?} in symtab")
        })
        .expect("Attempting to lower a module that has not been added to the symtab previously");

    ctx.item_list.modules.insert(
        id.clone(),
        Module {
            name: id.at_loc(&module.name),
        },
    );

    visit_module_body(&module.body, ctx)
}

#[tracing::instrument(skip_all)]
pub fn visit_module_body(body: &ast::ModuleBody, ctx: &mut Context) -> Result<()> {
    for i in &body.members {
        for item in visit_item(i, ctx)? {
            match item {
                hir::Item::Unit(u) => ctx
                    .item_list
                    .add_executable(u.name.name_id().clone(), ExecutableItem::Unit(u))?,

                hir::Item::Builtin(name, head) => ctx.item_list.add_executable(
                    name.name_id().clone(),
                    ExecutableItem::BuiltinUnit(name, head),
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
                (_, [ident]) => {
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
                    let mut bound = HashSet::<Loc<Identifier>>::new();
                    let mut unbound = p
                        .params
                        .0
                        .iter()
                        .map(
                            |hir::Parameter {
                                 name: ident,
                                 ty: _,
                                 no_mangle: _,
                             }| ident.inner.clone(),
                        )
                        .collect::<HashSet<_>>();

                    let mut patterns = patterns
                        .iter()
                        .map(|(target, pattern)| {
                            let ast_pattern = pattern.as_ref().cloned().unwrap_or_else(|| {
                                ast::Pattern::Path(Path(vec![target.clone()]).at_loc(target))
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

fn visit_statement(s: &Loc<ast::Statement>, ctx: &mut Context) -> Result<Vec<Loc<hir::Statement>>> {
    match &s.inner {
        ast::Statement::Declaration(names) => {
            let names = names
                .iter()
                .map(|name| {
                    ctx.symtab
                        .add_declaration(name.clone())
                        .map(|decl| decl.at_loc(name))
                })
                .collect::<Result<Vec<_>>>()?;

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

            let value = value.try_visit(visit_expression, ctx)?;

            let pattern = pattern.try_visit(visit_pattern, ctx)?;

            let mut wal_trace = None;
            attrs.lower(&mut |attr| match &attr.inner {
                ast::Attribute::WalTrace { clk, rst } => {
                    wal_trace = Some(
                        WalTrace {
                            clk: clk
                                .as_ref()
                                .map(|x| x.try_map_ref(|x| visit_expression(x, ctx)))
                                .transpose()?,
                            rst: rst
                                .as_ref()
                                .map(|x| x.try_map_ref(|x| visit_expression(x, ctx)))
                                .transpose()?,
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
                ast::Attribute::NoMangle
                | ast::Attribute::Fsm { .. }
                | ast::Attribute::Optimize { .. }
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
        ast::Statement::Register(inner) => visit_register(inner, ctx),
        ast::Statement::PipelineRegMarker(count, cond) => {
            let cond = match cond {
                Some(cond) => Some(cond.try_map_ref(|c| visit_expression(c, ctx))?),
                None => None,
            };

            let extra = match (count, cond) {
                (None, None) => None,
                (Some(count), None) => Some(hir::PipelineRegMarkerExtra::Count {
                    count: count.try_map_ref(|c| {
                        visit_type_expression(c, &TypeSpecKind::PipelineDepth, ctx)
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
                .lookup_type_symbol(&Path::ident(name.clone()).at_loc(name))?;
            Ok(vec![hir::Statement::Label(name.at_loc(&sym)).at_loc(s)])
        }
        ast::Statement::Assert(expr) => {
            let expr = expr.try_visit(visit_expression, ctx)?;

            Ok(vec![hir::Statement::Assert(expr).at_loc(s)])
        }
        ast::Statement::Comptime(condition) => {
            if let Some(ast_statements) = condition.maybe_unpack(&ctx.symtab)? {
                Ok(ast_statements
                    .iter()
                    .map(|s| visit_statement(s, ctx))
                    .collect::<Result<Vec<_>>>()?
                    .into_iter()
                    .flatten()
                    .collect())
            } else {
                Ok(vec![])
            }
        }
        ast::Statement::Set { target, value } => {
            let target = target.try_visit(visit_expression, ctx)?;
            let value = value.try_visit(visit_expression, ctx)?;

            Ok(vec![hir::Statement::Set { target, value }.at_loc(s)])
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
                .map(|arg| arg.try_visit(visit_expression, ctx))
                .collect::<Result<_>>()?;

            Ok(hir::ArgumentList::Positional(inner))
        }
        ast::ArgumentList::Named(args) => {
            let inner = args
                .iter()
                .map(|arg| match arg {
                    ast::NamedArgument::Full(name, expr) => {
                        Ok(hir::expression::NamedArgument::Full(
                            name.clone(),
                            expr.try_visit(visit_expression, ctx)?,
                        ))
                    }
                    ast::NamedArgument::Short(name) => {
                        let expr =
                            ast::Expression::Identifier(Path(vec![name.clone()]).at_loc(name))
                                .at_loc(name);

                        Ok(hir::expression::NamedArgument::Short(
                            name.clone(),
                            expr.try_visit(visit_expression, ctx)?,
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
                .clone()
                .maybe_unpack(&ctx.symtab)?
                .ok_or_else(|| {
                    Diagnostic::error(depth, "Expected pipeline depth")
                        .help("The current comptime branch did not specify a depth")
                })?
                .try_map_ref(|e| visit_type_expression(e, &TypeSpecKind::PipelineDepth, ctx))?;
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
                        ast::TypeSpec::Named(Path(vec![name.clone()]).at_loc(name), None)
                            .at_loc(name),
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

#[tracing::instrument(skip_all, fields(kind=e.variant_str()))]
pub fn visit_expression(e: &ast::Expression, ctx: &mut Context) -> Result<hir::Expression> {
    let new_id = ctx.idtracker.next();

    match e {
        ast::Expression::IntLiteral(val) => {
            let kind = match val {
                ast::IntLiteral::Unsized(_) => IntLiteralKind::Unsized,
                ast::IntLiteral::Signed { val: _, size } => IntLiteralKind::Signed(size.clone()),
                ast::IntLiteral::Unsigned { val: _, size } => {
                    IntLiteralKind::Unsigned(size.clone())
                }
            };
            Ok(hir::ExprKind::IntLiteral(val.clone().as_signed(), kind))
        }
        ast::Expression::BoolLiteral(val) => Ok(hir::ExprKind::BoolLiteral(*val)),
        ast::Expression::BitLiteral(lit) => {
            let result = match lit {
                ast::BitLiteral::Low => hir::expression::BitLiteral::Low,
                ast::BitLiteral::High => hir::expression::BitLiteral::High,
                ast::BitLiteral::HighImp => hir::expression::BitLiteral::HighImp,
            };
            Ok(hir::ExprKind::BitLiteral(result))
        }
        ast::Expression::CreatePorts => Ok(hir::ExprKind::CreatePorts),
        ast::Expression::BinaryOperator(lhs, tok, rhs) => {
            let lhs = lhs.try_visit(visit_expression, ctx)?;
            let rhs = rhs.try_visit(visit_expression, ctx)?;

            let operator = |op: BinaryOperator| {
                hir::ExprKind::BinaryOperator(Box::new(lhs), op.at_loc(tok), Box::new(rhs))
            };

            match tok.inner {
                ast::BinaryOperator::Add => Ok(operator(BinaryOperator::Add)),
                ast::BinaryOperator::Sub => Ok(operator(BinaryOperator::Sub)),
                ast::BinaryOperator::Mul => Ok(operator(BinaryOperator::Mul)),
                ast::BinaryOperator::Div => Ok(operator(BinaryOperator::Div)),
                ast::BinaryOperator::Mod => Ok(operator(BinaryOperator::Mod)),
                ast::BinaryOperator::Equals => Ok(operator(BinaryOperator::Eq)),
                ast::BinaryOperator::NotEquals => Ok(operator(BinaryOperator::NotEq)),
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
            let operand = operand.try_visit(visit_expression, ctx)?;

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
        ast::Expression::TupleLiteral(exprs) => {
            let exprs = exprs
                .iter()
                .map(|e| e.try_map_ref(|e| visit_expression(e, ctx)))
                .collect::<Result<Vec<_>>>()?;
            Ok(hir::ExprKind::TupleLiteral(exprs))
        }
        ast::Expression::ArrayLiteral(exprs) => {
            let exprs = exprs
                .iter()
                .map(|e| e.try_map_ref(|e| visit_expression(e, ctx)))
                .collect::<Result<Vec<_>>>()?;
            Ok(hir::ExprKind::ArrayLiteral(exprs))
        }
        ast::Expression::ArrayShorthandLiteral(expr, amount) => {
            Ok(hir::ExprKind::ArrayShorthandLiteral(
                Box::new(visit_expression(expr, ctx)?.at_loc(expr)),
                visit_const_generic(amount, ctx)?.map(|c| c.with_id(ctx.idtracker.next())),
            ))
        }
        ast::Expression::Index(target, index) => {
            let target = target.try_visit(visit_expression, ctx)?;
            let index = index.try_visit(visit_expression, ctx)?;
            Ok(hir::ExprKind::Index(Box::new(target), Box::new(index)))
        }
        ast::Expression::RangeIndex { target, start, end } => {
            let target = target.try_visit(visit_expression, ctx)?;
            Ok(hir::ExprKind::RangeIndex {
                target: Box::new(target),
                start: visit_const_generic(start, ctx)?.map(|c| c.with_id(ctx.idtracker.next())),
                end: visit_const_generic(end, ctx)?.map(|c| c.with_id(ctx.idtracker.next())),
            })
        }
        ast::Expression::TupleIndex(tuple, index) => Ok(hir::ExprKind::TupleIndex(
            Box::new(tuple.try_visit(visit_expression, ctx)?),
            *index,
        )),
        ast::Expression::FieldAccess(target, field) => Ok(hir::ExprKind::FieldAccess(
            Box::new(target.try_visit(visit_expression, ctx)?),
            field.clone(),
        )),
        ast::Expression::MethodCall {
            kind,
            target,
            name,
            args,
            turbofish,
        } => {
            let target = target.try_visit(visit_expression, ctx)?;
            Ok(hir::ExprKind::MethodCall {
                target: Box::new(target),
                name: name.clone(),
                args: args.try_map_ref(|args| visit_argument_list(args, ctx))?,
                call_kind: visit_call_kind(kind, ctx)?,
                turbofish: turbofish
                    .as_ref()
                    .map(|t| visit_turbofish(t, ctx))
                    .transpose()?,
            })
        }
        ast::Expression::If(cond, ontrue, onfalse) => {
            let cond = cond.try_visit(visit_expression, ctx)?;
            let ontrue = ontrue.try_visit(visit_expression, ctx)?;
            let onfalse = onfalse.try_visit(visit_expression, ctx)?;

            Ok(hir::ExprKind::If(
                Box::new(cond),
                Box::new(ontrue),
                Box::new(onfalse),
            ))
        }
        ast::Expression::Match(expression, branches) => {
            let e = expression.try_visit(visit_expression, ctx)?;

            if branches.is_empty() {
                return Err(Diagnostic::error(branches, "Match body has no arms")
                    .primary_label("This match body has no arms"));
            }

            let b = branches
                .iter()
                .map(|(pattern, result)| {
                    ctx.symtab.new_scope();
                    let p = pattern.try_visit(visit_pattern, ctx)?;
                    let r = result.try_visit(visit_expression, ctx)?;
                    ctx.symtab.close_scope();
                    Ok((p, r))
                })
                .collect::<Result<Vec<_>>>()?;

            Ok(hir::ExprKind::Match(Box::new(e), b))
        }
        ast::Expression::Block(block) => {
            Ok(hir::ExprKind::Block(Box::new(visit_block(block, ctx)?)))
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
            })
        }
        ast::Expression::Identifier(path) => {
            // If the identifier isn't a valid variable, report as "expected value".
            match ctx.symtab.lookup_variable(path) {
                Ok(id) => Ok(hir::ExprKind::Identifier(id)),
                Err(LookupError::IsAType(_)) => {
                    let ty = ctx.symtab.lookup_type_symbol(path)?;
                    let (name, ty) = &ty;
                    match ty.inner {
                        TypeSymbol::GenericMeta(
                            MetaType::Int | MetaType::Uint | MetaType::Number,
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
                        TypeSymbol::Declared(_, _) => Err(Diagnostic::error(
                            path,
                            format!("Type {name} is used as a value"),
                        )
                        .primary_label(format!("{name} is a type"))),
                    }
                }
                Err(LookupError::NotAVariable(path, ref was @ Thing::EnumVariant(_)))
                | Err(LookupError::NotAVariable(
                    path,
                    ref was @ Thing::Alias {
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
                        visit_type_expression(t, &TypeSpecKind::PipelineDepth, ctx)
                    })?)
                }
                ast::PipelineStageReference::Absolute(name) => {
                    hir::expression::PipelineRefKind::Absolute(
                        ctx.symtab
                            .lookup_type_symbol(&Path::ident(name.clone()).at_loc(name))?
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

            let path = Path(vec![name.clone()]).at_loc(name);
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
        ast::Expression::Comptime(inner) => {
            let inner = inner.maybe_unpack(&ctx.symtab)?.ok_or_else(|| {
                Diagnostic::error(inner.as_ref(), "Missing expression")
                    .help("The current comptime branch has no expression")
            })?;
            Ok(visit_expression(&inner, ctx)?.kind)
        }
        ast::Expression::StageReady => Ok(hir::ExprKind::StageReady),
        ast::Expression::StageValid => Ok(hir::ExprKind::StageValid),
    }
    .map(|kind| kind.with_id(new_id))
}

fn check_for_undefined(ctx: &Context) -> Result<()> {
    match ctx.symtab.get_undefined_declarations().first() {
        Some((undefined, DeclarationState::Undefined(_))) => {
            Err(
                Diagnostic::error(undefined, "Declared variable is not defined")
                    .primary_label("This variable is declared but not defined")
                    // FIXME: Suggest removing the declaration (with a diagnostic suggestion) only if the variable is unused.
                    .help(format!("Define {undefined} with a let or reg binding"))
                    .help("Or, remove the declaration if the variable is unused"),
            )
        }
        Some((undecleared, DeclarationState::Undecleared(_))) => Err(Diagnostic::error(
            undecleared,
            "Could not find referenced variable",
        )
        .primary_label("This variable could not be found")),
        _ => Ok(()),
    }
}

fn visit_block(b: &ast::Block, ctx: &mut Context) -> Result<hir::Block> {
    ctx.symtab.new_scope();
    let statements = b
        .statements
        .iter()
        .map(|statement| visit_statement(statement, ctx))
        .collect::<Result<Vec<_>>>()?
        .into_iter()
        .flatten()
        .collect::<Vec<_>>();

    let result = b
        .result
        .as_ref()
        .map(|o| o.try_visit(visit_expression, ctx))
        .transpose()?;

    check_for_undefined(ctx)?;

    ctx.symtab.close_scope();

    Ok(hir::Block { statements, result })
}

fn visit_register(reg: &Loc<ast::Register>, ctx: &mut Context) -> Result<Vec<Loc<hir::Statement>>> {
    let (reg, loc) = reg.split_loc_ref();

    let pattern = reg.pattern.try_visit(visit_pattern, ctx)?;

    let clock = reg.clock.try_visit(visit_expression, ctx)?;

    let reset = if let Some((trig, value)) = &reg.reset {
        Some((
            trig.try_visit(visit_expression, ctx)?,
            value.try_visit(visit_expression, ctx)?,
        ))
    } else {
        None
    };

    let initial = reg
        .initial
        .as_ref()
        .map(|i| i.try_visit(visit_expression, ctx))
        .transpose()?;

    let value = reg.value.try_visit(visit_expression, ctx)?;

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

    let attributes = reg.attributes.lower(&mut |attr| match &attr.inner {
        ast::Attribute::Fsm { state } => {
            let name_id = if let Some(state) = state {
                ctx.symtab
                    .lookup_variable(&Path(vec![state.clone()]).at_loc(state))?
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
    })?;

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

#[cfg(test)]
mod entity_visiting {
    use super::*;

    use hir::{hparams, UnitName};
    use spade_ast::testutil::{ast_ident, ast_path};
    use spade_common::name::testutil::name_id;
    use spade_common::{location_info::WithLocation, name::Identifier};

    use crate::testutil::test_context;
    use pretty_assertions::assert_eq;

    #[test]
    fn entity_visits_work() {
        let input = ast::Unit {
            head: ast::UnitHead {
                name: Identifier("test".to_string()).nowhere(),
                inputs: ParameterList::without_self(vec![(
                    ast_ident("a"),
                    ast::TypeSpec::Unit(().nowhere()).nowhere(),
                )])
                .nowhere(),
                output_type: None,
                type_params: None,
                attributes: ast::AttributeList(vec![]),
                unit_kind: ast::UnitKind::Entity.nowhere(),
                where_clauses: vec![],
            },
            body: Some(
                ast::Expression::Block(Box::new(ast::Block {
                    statements: vec![ast::Statement::binding(
                        ast::Pattern::name("var"),
                        Some(ast::TypeSpec::Unit(().nowhere()).nowhere()),
                        ast::Expression::int_literal_signed(0).nowhere(),
                    )
                    .nowhere()],
                    result: Some(ast::Expression::int_literal_signed(0).nowhere()),
                }))
                .nowhere(),
            ),
        }
        .nowhere();

        let expected = hir::Unit {
            name: UnitName::FullPath(name_id(0, "test")),
            head: hir::UnitHead {
                name: Identifier("test".to_string()).nowhere(),
                inputs: hparams!(("a", hir::TypeSpec::unit().nowhere())).nowhere(),
                output_type: None,
                unit_type_params: vec![],
                scope_type_params: vec![],
                unit_kind: hir::UnitKind::Entity.nowhere(),
                where_clauses: vec![],
            },
            attributes: hir::AttributeList::empty(),
            inputs: vec![((name_id(1, "a"), hir::TypeSpec::unit().nowhere()))],
            body: hir::ExprKind::Block(Box::new(hir::Block {
                statements: vec![hir::Statement::binding(
                    hir::PatternKind::name(name_id(2, "var")).idless().nowhere(),
                    Some(hir::TypeSpec::unit().nowhere()),
                    hir::ExprKind::int_literal(0).idless().nowhere(),
                )
                .nowhere()],
                result: Some(hir::ExprKind::int_literal(0).idless().nowhere()),
            }))
            .idless()
            .nowhere(),
        }
        .nowhere();

        let mut ctx = test_context();

        global_symbols::visit_unit(&None, &input, &None, &vec![], &mut ctx)
            .expect("Failed to collect global symbols");

        let result = visit_unit(None, &input, &None, &mut ctx);

        assert_eq!(result, Ok(hir::Item::Unit(expected)));

        // But the local variables should not
        assert!(!ctx.symtab.has_symbol(ast_path("a").inner));
        assert!(!ctx.symtab.has_symbol(ast_path("var").inner));
    }

    #[ignore]
    #[test]
    fn entity_with_generics_works() {
        unimplemented![]
        // let input = ast::Entity {
        //     name: Identifier("test".to_string()).nowhere(),
        //     inputs: vec![(ast_ident("a"), ast::Type::UnitType.nowhere())],
        //     output_type: ast::Type::UnitType.nowhere(),
        //     body: ast::Expression::Block(Box::new(ast::Block {
        //         statements: vec![ast::Statement::binding(
        //             ast_ident("var"),
        //             Some(ast::Type::UnitType.nowhere()),
        //             ast::Expression::IntLiteral(0).nowhere(),
        //         )
        //         .nowhere()],
        //         result: ast::Expression::IntLiteral(0).nowhere(),
        //     }))
        //     .nowhere(),
        //     type_params: vec![
        //         ast::TypeParam::TypeName(ast_ident("a").inner).nowhere(),
        //         ast::TypeParam::Integer(ast_ident("b")).nowhere(),
        //     ],
        // };

        // let expected = hir::Entity {
        //     head: hir::EntityHead {
        //         inputs: vec![
        //             ((
        //                 NameID(0, Path::from_strs(&["a"])),
        //                 hir::Type::Unit.nowhere(),
        //             )),
        //         ],
        //         output_type: hir::Type::Unit.nowhere(),
        //         type_params: vec![
        //             hir::TypeParam::TypeName(hir_ident("a").inner).nowhere(),
        //             hir::TypeParam::Integer(hir_ident("b")).nowhere(),
        //         ],
        //     },
        //     body: hir::ExprKind::Block(Box::new(hir::Block {
        //         statements: vec![hir::Statement::binding(
        //             hir_ident("var"),
        //             Some(hir::Type::Unit.nowhere()),
        //             hir::ExprKind::IntLiteral(0).idless().nowhere(),
        //         )
        //         .nowhere()],
        //         result: hir::ExprKind::IntLiteral(0).idless().nowhere(),
        //     }))
        //     .idless()
        //     .nowhere(),
        // };

        // let mut symtab = SymbolTable::new();
        // let mut idtracker = ExprIdTracker::new();

        // let result = visit_entity(&input, &mut symtab, &mut idtracker);

        // assert_eq!(result, Ok(expected));

        // // But the local variables should not
        // assert!(!symtab.has_symbol(&hir_ident("a").inner));
        // assert!(!symtab.has_symbol(&hir_ident("var").inner));
    }
}

#[cfg(test)]
mod statement_visiting {
    use super::*;

    use crate::testutil::test_context;
    use pretty_assertions::assert_eq;
    use spade_ast::testutil::{ast_ident, ast_path};
    use spade_common::location_info::WithLocation;
    use spade_common::name::testutil::name_id;

    #[test]
    fn bindings_convert_correctly() {
        let mut ctx = test_context();

        let input = ast::Statement::binding(
            ast::Pattern::name("a"),
            Some(ast::TypeSpec::Unit(().nowhere()).nowhere()),
            ast::Expression::int_literal_signed(0).nowhere(),
        )
        .nowhere();

        let expected = hir::Statement::binding(
            hir::PatternKind::name(name_id(0, "a")).idless().nowhere(),
            Some(hir::TypeSpec::unit().nowhere()),
            hir::ExprKind::int_literal(0).idless().nowhere(),
        )
        .nowhere();

        assert_eq!(visit_statement(&input, &mut ctx), Ok(vec![expected]));
        assert_eq!(ctx.symtab.has_symbol(ast_path("a").inner), true);
    }

    #[test]
    fn registers_are_statements() {
        let input = ast::Statement::Register(
            ast::Register {
                pattern: ast::Pattern::name("regname"),
                clock: ast::Expression::Identifier(ast_path("clk")).nowhere(),
                reset: None,
                initial: None,
                value: ast::Expression::int_literal_signed(0).nowhere(),
                value_type: None,
                attributes: ast::AttributeList::empty(),
            }
            .nowhere(),
        )
        .nowhere();

        let expected = hir::Statement::Register(hir::Register {
            pattern: hir::PatternKind::name(name_id(1, "regname"))
                .idless()
                .nowhere(),
            clock: hir::ExprKind::Identifier(name_id(0, "clk").inner)
                .with_id(0)
                .nowhere(),
            reset: None,
            initial: None,
            value: hir::ExprKind::int_literal(0).idless().nowhere(),
            value_type: None,
            attributes: hir::AttributeList::empty(),
        })
        .nowhere();

        let mut ctx = test_context();
        let clk_id = ctx.symtab.add_local_variable(ast_ident("clk"));
        assert_eq!(clk_id.0, 0);
        assert_eq!(visit_statement(&input, &mut ctx), Ok(vec![expected]));
        assert_eq!(ctx.symtab.has_symbol(ast_path("regname").inner), true);
    }

    #[test]
    fn declarations_declare_variables() {
        let input = ast::Statement::Declaration(vec![ast_ident("x"), ast_ident("y")]).nowhere();
        let ctx = &mut test_context();
        assert_eq!(
            visit_statement(&input, ctx),
            Ok(vec![hir::Statement::Declaration(vec![
                name_id(0, "x"),
                name_id(1, "y")
            ])
            .nowhere()])
        );
        assert_eq!(ctx.symtab.has_symbol(ast_path("x").inner), true);
        assert_eq!(ctx.symtab.has_symbol(ast_path("y").inner), true);
    }
}

#[cfg(test)]
mod expression_visiting {
    use super::*;

    use crate::testutil::test_context;
    use hir::hparams;
    use hir::symbol_table::EnumVariant;
    use spade_ast::testutil::{ast_ident, ast_path};
    use spade_common::location_info::WithLocation;
    use spade_common::name::testutil::name_id;

    #[test]
    fn int_literals_work() {
        let input = ast::Expression::int_literal_signed(123);
        let expected = hir::ExprKind::int_literal(123).idless();

        assert_eq!(visit_expression(&input, &mut test_context()), Ok(expected));
    }

    macro_rules! binop_test {
        ($test_name:ident, $token:ident, $op:ident) => {
            #[test]
            fn $test_name() {
                let input = ast::Expression::BinaryOperator(
                    Box::new(ast::Expression::int_literal_signed(123).nowhere()),
                    spade_ast::BinaryOperator::$token.nowhere(),
                    Box::new(ast::Expression::int_literal_signed(456).nowhere()),
                );
                let expected = hir::ExprKind::BinaryOperator(
                    Box::new(hir::ExprKind::int_literal(123).idless().nowhere()),
                    BinaryOperator::$op.nowhere(),
                    Box::new(hir::ExprKind::int_literal(456).idless().nowhere()),
                )
                .idless();

                assert_eq!(visit_expression(&input, &mut test_context()), Ok(expected));
            }
        };
    }

    macro_rules! unop_test {
        ($test_name:ident, $token:ident, $op:ident) => {
            #[test]
            fn $test_name() {
                let input = ast::Expression::UnaryOperator(
                    spade_ast::UnaryOperator::$token.nowhere(),
                    Box::new(ast::Expression::int_literal_signed(456).nowhere()),
                );
                let expected = hir::ExprKind::UnaryOperator(
                    hir::expression::UnaryOperator::$op.nowhere(),
                    Box::new(hir::ExprKind::int_literal(456).idless().nowhere()),
                )
                .idless();

                assert_eq!(visit_expression(&input, &mut test_context()), Ok(expected));
            }
        };
    }

    binop_test!(additions, Add, Add);
    binop_test!(subtractions, Sub, Sub);
    binop_test!(equals, Equals, Eq);
    binop_test!(bitwise_or, BitwiseOr, BitwiseOr);
    binop_test!(bitwise_and, BitwiseAnd, BitwiseAnd);
    unop_test!(usub, Sub, Sub);
    unop_test!(not, Not, Not);

    #[test]
    fn indexing_works() {
        let input = ast::Expression::Index(
            Box::new(ast::Expression::int_literal_signed(0).nowhere()),
            Box::new(ast::Expression::int_literal_signed(1).nowhere()),
        );

        let expected = hir::ExprKind::Index(
            Box::new(hir::ExprKind::int_literal(0).idless().nowhere()),
            Box::new(hir::ExprKind::int_literal(1).idless().nowhere()),
        )
        .idless();

        assert_eq!(visit_expression(&input, &mut test_context()), Ok(expected));
    }

    #[test]
    fn field_access_works() {
        let input = ast::Expression::FieldAccess(
            Box::new(ast::Expression::int_literal_signed(0).nowhere()),
            ast_ident("a"),
        );

        let expected = hir::ExprKind::FieldAccess(
            Box::new(hir::ExprKind::int_literal(0).idless().nowhere()),
            ast_ident("a"),
        )
        .idless();

        assert_eq!(visit_expression(&input, &mut test_context(),), Ok(expected));
    }

    #[test]
    fn blocks_work() {
        let input = ast::Expression::Block(Box::new(ast::Block {
            statements: vec![ast::Statement::binding(
                ast::Pattern::name("a"),
                None,
                ast::Expression::int_literal_signed(0).nowhere(),
            )
            .nowhere()],
            result: Some(ast::Expression::int_literal_signed(0).nowhere()),
        }));
        let expected = hir::ExprKind::Block(Box::new(hir::Block {
            statements: vec![hir::Statement::binding(
                hir::PatternKind::name(name_id(0, "a")).idless().nowhere(),
                None,
                hir::ExprKind::int_literal(0).idless().nowhere(),
            )
            .nowhere()],
            result: Some(hir::ExprKind::int_literal(0).idless().nowhere()),
        }))
        .idless();

        let mut ctx = test_context();
        assert_eq!(visit_expression(&input, &mut ctx), Ok(expected));
        assert!(!ctx.symtab.has_symbol(ast_path("a").inner));
    }

    #[test]
    fn if_expressions_work() {
        let input = ast::Expression::If(
            Box::new(ast::Expression::int_literal_signed(0).nowhere()),
            Box::new(
                ast::Expression::Block(Box::new(ast::Block {
                    statements: vec![],
                    result: Some(ast::Expression::int_literal_signed(1).nowhere()),
                }))
                .nowhere(),
            ),
            Box::new(
                ast::Expression::Block(Box::new(ast::Block {
                    statements: vec![],
                    result: Some(ast::Expression::int_literal_signed(2).nowhere()),
                }))
                .nowhere(),
            ),
        );
        let expected = hir::ExprKind::If(
            Box::new(hir::ExprKind::int_literal(0).idless().nowhere()),
            Box::new(
                hir::ExprKind::Block(Box::new(hir::Block {
                    statements: vec![],
                    result: Some(hir::ExprKind::int_literal(1).idless().nowhere()),
                }))
                .idless()
                .nowhere(),
            ),
            Box::new(
                hir::ExprKind::Block(Box::new(hir::Block {
                    statements: vec![],
                    result: Some(hir::ExprKind::int_literal(2).idless().nowhere()),
                }))
                .idless()
                .nowhere(),
            ),
        )
        .idless();

        assert_eq!(visit_expression(&input, &mut test_context(),), Ok(expected));
    }

    #[test]
    fn match_expressions_work() {
        let input = ast::Expression::Match(
            Box::new(ast::Expression::int_literal_signed(1).nowhere()),
            vec![(
                ast::Pattern::name("x"),
                ast::Expression::int_literal_signed(2).nowhere(),
            )]
            .nowhere(),
        );

        let expected = hir::ExprKind::Match(
            Box::new(hir::ExprKind::int_literal(1).idless().nowhere()),
            vec![(
                hir::PatternKind::name(name_id(0, "x")).idless().nowhere(),
                hir::ExprKind::int_literal(2).idless().nowhere(),
            )],
        )
        .idless();

        assert_eq!(visit_expression(&input, &mut test_context(),), Ok(expected))
    }

    #[test]
    fn match_expressions_with_enum_members_works() {
        let input = ast::Expression::Match(
            Box::new(ast::Expression::int_literal_signed(1).nowhere()),
            vec![(
                ast::Pattern::Type(
                    ast_path("x"),
                    ast::ArgumentPattern::Positional(vec![
                        ast::Pattern::Path(ast_path("y")).nowhere()
                    ])
                    .nowhere(),
                )
                .nowhere(),
                ast::Expression::Identifier(ast_path("y")).nowhere(),
            )]
            .nowhere(),
        );

        let expected = hir::ExprKind::Match(
            Box::new(hir::ExprKind::int_literal(1).idless().nowhere()),
            vec![(
                hir::PatternKind::Type(
                    name_id(100, "x"),
                    vec![hir::PatternArgument {
                        target: ast_ident("x"),
                        value: hir::PatternKind::name(name_id(0, "y")).idless().nowhere(),
                        kind: hir::ArgumentKind::Positional,
                    }],
                )
                .idless()
                .nowhere(),
                hir::ExprKind::Identifier(name_id(0, "y").inner)
                    .idless()
                    .nowhere(),
            )],
        )
        .idless();

        let mut symtab = SymbolTable::new();

        let enum_variant = EnumVariant {
            name: Identifier("".to_string()).nowhere(),
            output_type: hir::TypeSpec::Unit(().nowhere()).nowhere(),
            option: 0,
            params: hparams![("x", hir::TypeSpec::Unit(().nowhere()).nowhere())].nowhere(),
            type_params: vec![],
        }
        .nowhere();

        symtab.add_thing_with_id(100, ast_path("x").inner, Thing::EnumVariant(enum_variant));
        assert_eq!(
            visit_expression(
                &input,
                &mut Context {
                    symtab,
                    ..test_context()
                }
            ),
            Ok(expected)
        )
    }

    #[test]
    fn match_expressions_with_0_argument_enum_works() {
        let input = ast::Expression::Match(
            Box::new(ast::Expression::int_literal_signed(1).nowhere()),
            vec![(
                ast::Pattern::Type(
                    ast_path("x"),
                    ast::ArgumentPattern::Positional(vec![
                        ast::Pattern::Path(ast_path("y")).nowhere()
                    ])
                    .nowhere(),
                )
                .nowhere(),
                ast::Expression::Identifier(ast_path("y")).nowhere(),
            )]
            .nowhere(),
        );

        let expected = hir::ExprKind::Match(
            Box::new(hir::ExprKind::int_literal(1).idless().nowhere()),
            vec![(
                hir::PatternKind::Type(
                    name_id(100, "x"),
                    vec![hir::PatternArgument {
                        target: ast_ident("x"),
                        value: hir::PatternKind::name(name_id(0, "y")).idless().nowhere(),
                        kind: hir::ArgumentKind::Positional,
                    }],
                )
                .idless()
                .nowhere(),
                hir::ExprKind::Identifier(name_id(0, "y").inner)
                    .idless()
                    .nowhere(),
            )],
        )
        .idless();

        let mut symtab = SymbolTable::new();

        let enum_variant = EnumVariant {
            name: Identifier("".to_string()).nowhere(),
            output_type: hir::TypeSpec::Unit(().nowhere()).nowhere(),
            option: 0,
            params: hparams![("x", hir::TypeSpec::Unit(().nowhere()).nowhere())].nowhere(),
            type_params: vec![],
        }
        .nowhere();

        symtab.add_thing_with_id(100, ast_path("x").inner, Thing::EnumVariant(enum_variant));

        assert_eq!(
            visit_expression(
                &input,
                &mut Context {
                    symtab,
                    ..test_context()
                }
            ),
            Ok(expected)
        )
    }

    #[test]
    fn entity_instantiation_works() {
        let input = ast::Expression::Call {
            kind: ast::CallKind::Entity(().nowhere()),
            callee: ast_path("test"),
            args: ast::ArgumentList::Positional(vec![
                ast::Expression::int_literal_signed(1).nowhere(),
                ast::Expression::int_literal_signed(2).nowhere(),
            ])
            .nowhere(),
            turbofish: None,
        }
        .nowhere();

        let expected = hir::ExprKind::Call {
            kind: hir::expression::CallKind::Entity(().nowhere()),
            callee: name_id(0, "test"),
            args: hir::ArgumentList::Positional(vec![
                hir::ExprKind::int_literal(1).idless().nowhere(),
                hir::ExprKind::int_literal(2).idless().nowhere(),
            ])
            .nowhere(),
            turbofish: None,
        }
        .idless();

        let mut symtab = SymbolTable::new();

        symtab.add_thing(
            ast_path("test").inner,
            Thing::Unit(
                hir::UnitHead {
                    name: Identifier("".to_string()).nowhere(),
                    inputs: hparams![
                        ("a", hir::TypeSpec::unit().nowhere()),
                        ("b", hir::TypeSpec::unit().nowhere()),
                    ]
                    .nowhere(),
                    output_type: None,
                    unit_type_params: vec![],
                    scope_type_params: vec![],
                    unit_kind: hir::UnitKind::Entity.nowhere(),
                    where_clauses: vec![],
                }
                .nowhere(),
            ),
        );

        assert_eq!(
            visit_expression(
                &input,
                &mut Context {
                    symtab,
                    ..test_context()
                }
            ),
            Ok(expected)
        );
    }

    #[test]
    fn entity_instantiation_with_named_args_works() {
        let input = ast::Expression::Call {
            kind: ast::CallKind::Entity(().nowhere()),
            callee: ast_path("test"),
            args: ast::ArgumentList::Named(vec![
                ast::NamedArgument::Full(
                    ast_ident("b"),
                    ast::Expression::int_literal_signed(2).nowhere(),
                ),
                ast::NamedArgument::Full(
                    ast_ident("a"),
                    ast::Expression::int_literal_signed(1).nowhere(),
                ),
            ])
            .nowhere(),
            turbofish: None,
        }
        .nowhere();

        let expected = hir::ExprKind::Call {
            kind: hir::expression::CallKind::Entity(().nowhere()),
            callee: name_id(0, "test"),
            args: hir::ArgumentList::Named(vec![
                hir::expression::NamedArgument::Full(
                    ast_ident("b"),
                    hir::ExprKind::int_literal(2).idless().nowhere(),
                ),
                hir::expression::NamedArgument::Full(
                    ast_ident("a"),
                    hir::ExprKind::int_literal(1).idless().nowhere(),
                ),
            ])
            .nowhere(),
            turbofish: None,
        }
        .idless();

        let mut symtab = SymbolTable::new();

        symtab.add_thing(
            ast_path("test").inner,
            Thing::Unit(
                hir::UnitHead {
                    name: Identifier("".to_string()).nowhere(),
                    inputs: hparams![
                        ("a", hir::TypeSpec::unit().nowhere()),
                        ("b", hir::TypeSpec::unit().nowhere()),
                    ]
                    .nowhere(),
                    output_type: None,
                    unit_type_params: vec![],
                    scope_type_params: vec![],
                    unit_kind: hir::UnitKind::Entity.nowhere(),
                    where_clauses: vec![],
                }
                .nowhere(),
            ),
        );

        assert_eq!(
            visit_expression(
                &input,
                &mut Context {
                    symtab,
                    ..test_context()
                }
            ),
            Ok(expected)
        );
    }

    #[test]
    fn function_instantiation_works() {
        let input = ast::Expression::Call {
            kind: ast::CallKind::Function,
            callee: ast_path("test"),
            args: ast::ArgumentList::Positional(vec![
                ast::Expression::int_literal_signed(1).nowhere(),
                ast::Expression::int_literal_signed(2).nowhere(),
            ])
            .nowhere(),
            turbofish: None,
        }
        .nowhere();

        let expected = hir::ExprKind::Call {
            kind: hir::expression::CallKind::Function,
            callee: name_id(0, "test"),
            args: hir::ArgumentList::Positional(vec![
                hir::ExprKind::int_literal(1).idless().nowhere(),
                hir::ExprKind::int_literal(2).idless().nowhere(),
            ])
            .nowhere(),
            turbofish: None,
        }
        .idless();

        let mut symtab = SymbolTable::new();

        symtab.add_thing(
            ast_path("test").inner,
            Thing::Unit(
                hir::UnitHead {
                    name: Identifier("".to_string()).nowhere(),
                    inputs: hparams![
                        ("a", hir::TypeSpec::unit().nowhere()),
                        ("b", hir::TypeSpec::unit().nowhere()),
                    ]
                    .nowhere(),
                    output_type: None,
                    unit_type_params: vec![],
                    scope_type_params: vec![],
                    unit_kind: hir::UnitKind::Function(hir::FunctionKind::Fn).nowhere(),
                    where_clauses: vec![],
                }
                .nowhere(),
            ),
        );

        assert_eq!(
            visit_expression(
                &input,
                &mut Context {
                    symtab,
                    ..test_context()
                }
            ),
            Ok(expected)
        );
    }
}

#[cfg(test)]
mod pattern_visiting {
    use crate::testutil::test_context;
    use ast::{
        testutil::{ast_ident, ast_path},
        ArgumentPattern,
    };
    use hir::{
        hparams,
        symbol_table::{StructCallable, TypeDeclKind},
        PatternKind,
    };
    use spade_common::name::testutil::name_id;

    use super::*;

    #[test]
    fn bool_patterns_work() {
        let input = ast::Pattern::Bool(true);

        let result = visit_pattern(&input, &mut test_context());

        assert_eq!(result, Ok(PatternKind::Bool(true).idless()));
    }

    #[test]
    fn int_patterns_work() {
        let input = ast::Pattern::integer(5);

        let result = visit_pattern(&input, &mut test_context());

        assert_eq!(result, Ok(PatternKind::integer(5).idless()));
    }

    #[test]
    fn named_struct_patterns_work() {
        let input = ast::Pattern::Type(
            ast_path("a"),
            ArgumentPattern::Named(vec![
                (ast_ident("x"), None),
                (ast_ident("y"), Some(ast::Pattern::integer(0).nowhere())),
            ])
            .nowhere(),
        );

        let mut symtab = SymbolTable::new();

        let type_name = symtab.add_type(
            ast_path("a").inner,
            TypeSymbol::Declared(vec![], TypeDeclKind::normal_struct()).nowhere(),
        );

        symtab.add_thing_with_name_id(
            type_name.clone(),
            Thing::Struct(
                StructCallable {
                    name: Identifier("".to_string()).nowhere(),
                    self_type: hir::TypeSpec::Declared(type_name.clone().nowhere(), vec![])
                        .nowhere(),
                    params: hparams![
                        ("x", hir::TypeSpec::unit().nowhere()),
                        ("y", hir::TypeSpec::unit().nowhere()),
                    ]
                    .nowhere(),
                    type_params: vec![],
                }
                .nowhere(),
            ),
        );

        let result = visit_pattern(
            &input,
            &mut Context {
                symtab,
                ..test_context()
            },
        );

        let expected = PatternKind::Type(
            type_name.nowhere(),
            vec![
                hir::PatternArgument {
                    target: ast_ident("x"),
                    value: hir::PatternKind::name(name_id(1, "x")).idless().nowhere(),
                    kind: hir::ArgumentKind::ShortNamed,
                },
                hir::PatternArgument {
                    target: ast_ident("y"),
                    value: hir::PatternKind::integer(0).idless().nowhere(),
                    kind: hir::ArgumentKind::Named,
                },
            ],
        )
        .idless();

        assert_eq!(result, Ok(expected))
    }
}

#[cfg(test)]
mod register_visiting {
    use super::*;

    use crate::testutil::test_context;
    use spade_ast::testutil::{ast_ident, ast_path};
    use spade_common::location_info::WithLocation;
    use spade_common::name::testutil::name_id;

    #[test]
    fn register_visiting_works() {
        let input = ast::Register {
            pattern: ast::Pattern::name("test"),
            clock: ast::Expression::Identifier(ast_path("clk")).nowhere(),
            reset: Some((
                ast::Expression::Identifier(ast_path("rst")).nowhere(),
                ast::Expression::int_literal_signed(0).nowhere(),
            )),
            initial: Some(ast::Expression::int_literal_signed(0).nowhere()),
            value: ast::Expression::int_literal_signed(1).nowhere(),
            value_type: Some(ast::TypeSpec::Unit(().nowhere()).nowhere()),
            attributes: ast::AttributeList::empty(),
        }
        .nowhere();

        let expected = hir::Register {
            pattern: hir::PatternKind::name(name_id(2, "test"))
                .idless()
                .nowhere(),
            clock: hir::ExprKind::Identifier(name_id(0, "clk").inner)
                .with_id(0)
                .nowhere(),
            reset: Some((
                hir::ExprKind::Identifier(name_id(1, "rst").inner)
                    .idless()
                    .nowhere(),
                hir::ExprKind::int_literal(0).idless().nowhere(),
            )),
            initial: Some(hir::ExprKind::int_literal(0).idless().nowhere()),
            value: hir::ExprKind::int_literal(1).idless().nowhere(),
            value_type: Some(hir::TypeSpec::unit().nowhere()),
            attributes: hir::AttributeList::empty(),
        };

        let mut symtab = SymbolTable::new();
        let clk_id = symtab.add_local_variable(ast_ident("clk"));
        assert_eq!(clk_id.0, 0);
        let rst_id = symtab.add_local_variable(ast_ident("rst"));
        assert_eq!(rst_id.0, 1);
        assert_eq!(
            visit_register(
                &input,
                &mut Context {
                    symtab,
                    ..test_context()
                }
            ),
            Ok(vec![hir::Statement::Register(expected).nowhere()])
        );
    }
}

#[cfg(test)]
mod item_visiting {
    use super::*;

    use ast::aparams;
    use spade_ast::testutil::ast_ident;
    use spade_common::location_info::WithLocation;
    use spade_common::name::testutil::name_id;

    use crate::testutil::test_context;
    use pretty_assertions::assert_eq;

    #[test]
    pub fn item_entity_visiting_works() {
        let input = ast::Item::Unit(
            ast::Unit {
                head: ast::UnitHead {
                    name: ast_ident("test"),
                    output_type: None,
                    inputs: aparams![],
                    type_params: None,
                    attributes: ast::AttributeList(vec![]),
                    unit_kind: ast::UnitKind::Entity.nowhere(),
                    where_clauses: vec![],
                },
                body: Some(
                    ast::Expression::Block(Box::new(ast::Block {
                        statements: vec![],
                        result: Some(ast::Expression::int_literal_signed(0).nowhere()),
                    }))
                    .nowhere(),
                ),
            }
            .nowhere(),
        );

        let expected = hir::Item::Unit(
            hir::Unit {
                name: hir::UnitName::FullPath(name_id(0, "test")),
                head: hir::UnitHead {
                    name: Identifier("test".to_string()).nowhere(),
                    output_type: None,
                    inputs: hir::ParameterList(vec![]).nowhere(),
                    unit_type_params: vec![],
                    scope_type_params: vec![],
                    unit_kind: hir::UnitKind::Entity.nowhere(),
                    where_clauses: vec![],
                },
                attributes: hir::AttributeList::empty(),
                inputs: vec![],
                body: hir::ExprKind::Block(Box::new(hir::Block {
                    statements: vec![],
                    result: Some(hir::ExprKind::int_literal(0).idless().nowhere()),
                }))
                .idless()
                .nowhere(),
            }
            .nowhere(),
        );

        let mut ctx = test_context();

        global_symbols::visit_item(&input, &mut ctx).unwrap();
        assert_eq!(visit_item(&input, &mut ctx), Ok(vec![expected]));
    }
}

#[cfg(test)]
mod module_visiting {
    use std::collections::HashMap;

    use super::*;

    use hir::hparams;
    use spade_ast::testutil::ast_ident;
    use spade_common::location_info::WithLocation;
    use spade_common::name::testutil::name_id;

    use crate::testutil::test_context;
    use pretty_assertions::assert_eq;
    use spade_common::namespace::ModuleNamespace;

    #[test]
    fn visiting_module_with_one_entity_works() {
        let input = ast::ModuleBody {
            members: vec![ast::Item::Unit(
                ast::Unit {
                    head: ast::UnitHead {
                        name: ast_ident("test"),
                        output_type: None,
                        inputs: ParameterList::without_self(vec![]).nowhere(),
                        type_params: None,
                        attributes: ast::AttributeList(vec![]),
                        unit_kind: ast::UnitKind::Entity.nowhere(),
                        where_clauses: vec![],
                    },
                    body: Some(
                        ast::Expression::Block(Box::new(ast::Block {
                            statements: vec![],
                            result: Some(ast::Expression::int_literal_signed(0).nowhere()),
                        }))
                        .nowhere(),
                    ),
                }
                .nowhere(),
            )],
        };

        let expected = hir::ItemList {
            executables: vec![(
                name_id(0, "test").inner,
                hir::ExecutableItem::Unit(
                    hir::Unit {
                        name: hir::UnitName::FullPath(name_id(0, "test")),
                        head: hir::UnitHead {
                            name: Identifier("test".to_string()).nowhere(),
                            output_type: None,
                            inputs: hparams!().nowhere(),
                            unit_type_params: vec![],
                            scope_type_params: vec![],
                            unit_kind: hir::UnitKind::Entity.nowhere(),
                            where_clauses: vec![],
                        },
                        inputs: vec![],
                        attributes: hir::AttributeList::empty(),
                        body: hir::ExprKind::Block(Box::new(hir::Block {
                            statements: vec![],
                            result: Some(hir::ExprKind::int_literal(0).idless().nowhere()),
                        }))
                        .idless()
                        .nowhere(),
                    }
                    .nowhere(),
                ),
            )]
            .into_iter()
            .collect(),
            types: vec![].into_iter().collect(),
            modules: vec![].into_iter().collect(),
            traits: HashMap::new(),
            impls: HashMap::new(),
        };

        let mut ctx = test_context();
        global_symbols::gather_symbols(&input, &mut ctx).expect("failed to collect global symbols");
        assert_eq!(visit_module_body(&input, &mut ctx), Ok(()));
        assert_eq!(ctx.item_list, expected);
    }

    #[test]
    fn visiting_submodules_works() {
        let input = ast::ModuleBody {
            members: vec![ast::Item::Module(
                ast::Module {
                    name: ast_ident("outer"),
                    body: ast::ModuleBody {
                        members: vec![ast::Item::Module(
                            ast::Module {
                                name: ast_ident("inner"),
                                body: ast::ModuleBody { members: vec![] }.nowhere(),
                            }
                            .nowhere(),
                        )],
                    }
                    .nowhere(),
                }
                .nowhere(),
            )],
        };

        let expected = hir::ItemList {
            executables: vec![].into_iter().collect(),
            types: vec![].into_iter().collect(),
            modules: vec![
                (
                    name_id(1, "outer").inner,
                    hir::Module {
                        name: name_id(1, "outer"),
                    },
                ),
                (
                    name_id(2, "outer::inner").inner,
                    hir::Module {
                        name: name_id(2, "outer::inner"),
                    },
                ),
            ]
            .into_iter()
            .collect(),
            traits: HashMap::new(),
            impls: HashMap::new(),
        };

        let mut ctx = test_context();

        let namespace = ModuleNamespace {
            namespace: Path::from_strs(&[""]),
            base_namespace: Path::from_strs(&[""]),
        };
        ctx.symtab.add_thing(
            namespace.namespace.clone(),
            Thing::Module(namespace.namespace.0[0].clone()),
        );
        global_symbols::gather_types(&input, &mut ctx).expect("failed to collect types");

        assert_eq!(visit_module_body(&input, &mut ctx), Ok(()));
        assert_eq!(ctx.item_list, expected);
    }
}
