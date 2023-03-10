mod attributes;
pub mod builtins;
mod comptime;
pub mod error;
pub mod global_symbols;
pub mod pipelines;
pub mod types;

use attributes::{report_unused_attributes, unit_name};
use num::{BigInt, ToPrimitive, Zero};
use pipelines::{int_literal_to_pipeline_stages, PipelineContext};
use spade_diagnostics::Diagnostic;
use tracing::{event, info, Level};

use std::collections::{HashMap, HashSet};

use comptime::ComptimeCondExt;
use hir::param_util::ArgumentError;
use hir::symbol_table::DeclarationState;
use hir::{ExecutableItem, TraitName};
use spade_ast as ast;
use spade_common::id_tracker::{ExprIdTracker, ImplIdTracker};
use spade_common::location_info::{Loc, WithLocation};
use spade_common::name::{Identifier, Path};
use spade_hir as hir;

use crate::pipelines::maybe_perform_pipelining_tasks;
use crate::types::IsPort;
use ast::{ParameterList, UnitKind};
use hir::expression::BinaryOperator;
use hir::symbol_table::{LookupError, SymbolTable, Thing, TypeSymbol};
use hir::UnitHead;
pub use spade_common::id_tracker;

use error::Result;

pub struct Context {
    pub symtab: SymbolTable,
    pub idtracker: ExprIdTracker,
    pub impl_idtracker: ImplIdTracker,
    pub pipeline_ctx: Option<PipelineContext>,
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
        self.map_ref(|t| visitor(&t, context)).map_err(|e, _| e)
    }
}

/// Visit an AST type parameter, converting it to a HIR type parameter. The name is not
/// added to the symbol table as this function is re-used for both global symbol collection
/// and normal HIR lowering.
#[tracing::instrument(skip_all, fields(name=%param.name()))]
pub fn visit_type_param(
    param: &ast::TypeParam,
    symtab: &mut SymbolTable,
) -> Result<hir::TypeParam> {
    match &param {
        ast::TypeParam::TypeName(ident) => {
            let name_id = symtab.add_type(
                Path::ident(ident.clone()),
                TypeSymbol::GenericArg.at_loc(&ident),
            );

            Ok(hir::TypeParam::TypeName(ident.inner.clone(), name_id))
        }
        ast::TypeParam::Integer(ident) => {
            let name_id = symtab.add_type(
                Path::ident(ident.clone()),
                TypeSymbol::GenericArg.at_loc(&ident),
            );

            Ok(hir::TypeParam::Integer(ident.inner.clone(), name_id))
        }
    }
}

pub fn visit_type_expression(
    expr: &ast::TypeExpression,
    symtab: &mut SymbolTable,
) -> Result<hir::TypeExpression> {
    // todo!("Implement visiting type expressions")
    match expr {
        ast::TypeExpression::TypeSpec(spec) => {
            let inner = visit_type_spec(spec, symtab)?;
            // Look up the type. For now, we'll panic if we don't find a concrete type
            Ok(hir::TypeExpression::TypeSpec(inner.inner))
        }
        ast::TypeExpression::Integer(val) => Ok(hir::TypeExpression::Integer(val.clone())),
    }
}

pub fn visit_type_spec(
    t: &Loc<ast::TypeSpec>,
    symtab: &mut SymbolTable,
) -> Result<Loc<hir::TypeSpec>> {
    let result = match &t.inner {
        ast::TypeSpec::Named(path, params) => {
            // Lookup the referenced type
            let (base_id, base_t) = symtab.lookup_type_symbol(path)?;

            // Check if the type is a declared type or a generic argument.
            match &base_t.inner {
                TypeSymbol::Declared(_, _) => {
                    // We'll defer checking the validity of generic args to the type checker,
                    // but we still have to visit them now
                    let params = params
                        // We can't flatten "through" Option<Loc<Vec<...>>>, so map it away.
                        .as_ref()
                        .map(|o| &o.inner)
                        .into_iter()
                        .flatten()
                        .map(|p| p.try_map_ref(|p| visit_type_expression(p, symtab)))
                        .collect::<Result<Vec<_>>>()?;

                    Ok(hir::TypeSpec::Declared(base_id.at_loc(path), params))
                }
                TypeSymbol::GenericArg | TypeSymbol::GenericInt => {
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
            let inner = Box::new(visit_type_spec(inner, symtab)?);
            let size = Box::new(visit_type_expression(size, symtab)?.at_loc(size));

            Ok(hir::TypeSpec::Array { inner, size })
        }
        ast::TypeSpec::Tuple(inner) => {
            // Check if this tuple is a port by checking if any of the contained types
            // are ports. If they are, retain the first one to use as a witness for this fact
            // for error reporting
            let transitive_port_witness = inner
                .iter()
                .map(|p| {
                    if p.is_port(symtab)? {
                        Ok(Some(p))
                    } else {
                        Ok(None)
                    }
                })
                .collect::<Result<Vec<_>>>()?
                .into_iter()
                .find_map(|x| x);

            if let Some(witness) = transitive_port_witness {
                let witness = witness;
                // Since this type has 1 port, all members must be ports
                for ty in inner {
                    if !ty.is_port(symtab)? {
                        return Err(Diagnostic::error(
                            ty,
                            "Can't mix ports and non-ports in a tuple",
                        )
                        .primary_label("This is not a port")
                        .secondary_label(witness, "This is a port")
                        .note("A tuple must either contain only ports or no ports")
                        .into());
                    }
                }
            }

            let inner = inner
                .iter()
                .map(|p| visit_type_spec(p, symtab))
                .collect::<Result<Vec<_>>>()?;

            Ok(hir::TypeSpec::Tuple(inner))
        }
        ast::TypeSpec::Unit(w) => Ok(hir::TypeSpec::Unit(*w)),
        ast::TypeSpec::Backward(inner) => {
            if inner.is_port(symtab)? {
                return Err(Diagnostic::from(error::WireOfPort {
                    full_type: t.loc(),
                    inner_type: inner.loc(),
                })
                .into());
            }
            Ok(hir::TypeSpec::Backward(Box::new(visit_type_spec(
                inner, symtab,
            )?)))
        }
        ast::TypeSpec::Wire(inner) => {
            if inner.is_port(symtab)? {
                return Err(Diagnostic::from(error::WireOfPort {
                    full_type: t.loc(),
                    inner_type: inner.loc(),
                })
                .into());
            }
            Ok(hir::TypeSpec::Wire(Box::new(visit_type_spec(
                inner, symtab,
            )?)))
        }
    };

    Ok(result?.at_loc(&t))
}

pub enum SelfContext {
    /// `self` currently does not refer to anything
    FreeStanding,
    /// `self` refers to `TypeSpec` in an impl block for that type
    ImplBlock(Loc<hir::TypeSpec>),
}

fn visit_parameter_list(
    l: &Loc<ParameterList>,
    symtab: &mut SymbolTable,
    self_context: &SelfContext,
) -> Result<hir::ParameterList> {
    let mut arg_names: HashSet<Loc<Identifier>> = HashSet::new();
    let mut result = vec![];

    if let SelfContext::ImplBlock(_) = self_context {
        if l.self_.is_none() {
            // Suggest insertion after the first paren
            let mut diag = Diagnostic::error(l, "Method must take 'self' as the first parameter")
                .primary_label("Missing self");

            let suggest_msg = "Consider adding self";
            diag = if l.args.is_empty() {
                diag.span_suggest_replace(suggest_msg, l, "(self)")
            } else {
                diag.span_suggest_insert_before(suggest_msg, &l.args[0].0, "self, ")
            };
            return Err(diag.into());
        }
    }

    if let Some(self_loc) = l.self_ {
        match self_context {
            SelfContext::FreeStanding => {
                return Err(Diagnostic::error(
                    self_loc,
                    "'self' can not be used in free standing units",
                )
                .primary_label("not allowed here")
                .into())
            }
            SelfContext::ImplBlock(spec) => result.push((
                Identifier(String::from("self")).at_loc(&self_loc),
                spec.clone(),
            )),
        }
    }

    for (name, input_type) in &l.args {
        if let Some(prev) = arg_names.get(name) {
            return Err(
                Diagnostic::error(name, "Multiple arguments with the same name")
                    .primary_label(format!("{name} later declared here"))
                    .secondary_label(prev, format!("{name} previously declared here"))
                    .into(),
            );
        }
        arg_names.insert(name.clone());
        let t = visit_type_spec(input_type, symtab)?;

        result.push((name.clone(), t));
    }
    Ok(hir::ParameterList(result))
}

/// Visit the head of an entity to generate an entity head
#[tracing::instrument(skip_all, fields(name=%item.name))]
pub fn entity_head(
    item: &ast::Unit,
    symtab: &mut SymbolTable,
    self_context: &SelfContext,
) -> Result<UnitHead> {
    symtab.new_scope();

    let type_params = item
        .type_params
        .iter()
        .map(|p| p.try_map_ref(|p| visit_type_param(p, symtab)))
        .collect::<Result<_>>()?;

    let output_type = if let Some(output_type) = &item.output_type {
        Some(visit_type_spec(output_type, symtab)?)
    } else {
        None
    };
    let inputs = visit_parameter_list(&item.inputs, symtab, self_context)?;

    // Check for ports in functions
    // We need to have the scope open to check this, but we also need to close
    // the scope if we fail here, so we'll store port_error in a variable
    let mut port_error = Ok(());
    if let ast::UnitKind::Function = item.unit_kind.inner {
        for (_, ty) in &item.inputs.args {
            if ty.is_port(symtab)? {
                port_error = Err(Diagnostic::error(ty, "Port argument in function")
                    .primary_label("This is a port")
                    .note("Only entities and pipelines can take ports as arguments")
                    .span_suggest_replace(
                        "Consider making this an entity",
                        &item.unit_kind,
                        "entity",
                    ))
            }
        }
    }

    symtab.close_scope();
    port_error?;

    let unit_kind = item.unit_kind.try_map_ref(|k| -> Result<_> {
        match k {
            ast::UnitKind::Function => Ok(hir::UnitKind::Function(hir::FunctionKind::Fn)),
            ast::UnitKind::Entity => Ok(hir::UnitKind::Entity),
            ast::UnitKind::Pipeline(d) => {
                let depth = int_literal_to_pipeline_stages(
                    &d.inner.maybe_unpack(symtab)?.ok_or_else(|| {
                        Diagnostic::error(d, "Missing pipeline depth")
                            .note("The current comptime branch does not specify a depth")
                    })?,
                )?;
                Ok(hir::UnitKind::Pipeline(depth))
            }
        }
    })?;

    Ok(UnitHead {
        name: item.name.clone(),
        inputs,
        output_type,
        type_params,
        unit_kind,
    })
}

/// The `extra_path` parameter allows specifying an extra path prepended to
/// the name of the entity. This is used by impl blocks to append a unique namespace
#[tracing::instrument(skip_all, fields(%unit.name, %unit.unit_kind))]
pub fn visit_unit(
    extra_path: Option<Path>,
    unit: &Loc<ast::Unit>,
    ctx: &mut Context,
) -> Result<hir::Item> {
    let ast::Unit {
        body,
        name,
        attributes,
        inputs: _,
        output_type: _,
        type_params,
        unit_kind: _,
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
    let head = head.clone(); // An offering to the borrow checker. May ferris have mercy on us all

    let mut attributes = attributes.clone();
    let unit_name = unit_name(&mut attributes, &id.at_loc(name), name, type_params)?;

    // If this is a builtin entity
    if body.is_none() {
        report_unused_attributes(&attributes)?;
        return Ok(hir::Item::Builtin(unit_name, head));
    }

    // Add the inputs to the symtab
    let inputs = head
        .inputs
        .0
        .iter()
        .map(|(ident, ty)| {
            (
                ctx.symtab.add_local_variable(ident.clone()).at_loc(ident),
                ty.clone(),
            )
        })
        .collect();

    ctx.pipeline_ctx = maybe_perform_pipelining_tasks(&unit, &head, ctx)?;

    let body = body.as_ref().unwrap().try_visit(visit_expression, ctx)?;

    ctx.symtab.close_scope();

    // Any remaining attributes are unused and will have an error reported
    report_unused_attributes(&attributes)?;

    info!("Checked all function arguments");

    Ok(hir::Item::Unit(
        hir::Unit {
            name: unit_name,
            head: head.clone().inner,
            inputs,
            body,
        }
        .at_loc(unit),
    ))
}

#[tracing::instrument(skip(items, ctx))]
pub fn visit_impl(
    block: &Loc<ast::ImplBlock>,
    items: &mut hir::ItemList,
    ctx: &mut Context,
) -> Result<Vec<hir::Item>> {
    let mut result = vec![];

    let impl_block_id = ctx.impl_idtracker.next();
    let (is_anonymous, trait_name) = if block.r#trait.is_some() {
        todo!("Support impl of non-anonymous traits");
    } else {
        // Create an anonymous trait which we will impl
        let trait_name = TraitName::Anonymous(impl_block_id);
        (true, trait_name)
    };

    // FIXME: Support impls for generic items
    let target_name = ctx.symtab.lookup_type_symbol(&block.target)?;
    let ast_type_spec = ast::TypeSpec::Named(block.target.clone(), None).at_loc(&block.target);
    let target_type_spec = visit_type_spec(&ast_type_spec, &mut ctx.symtab)?;

    let mut trait_members = vec![];
    let mut trait_impl = HashMap::new();
    let self_context = SelfContext::ImplBlock(target_type_spec);
    for entity in &block.units {
        if matches!(entity.unit_kind.inner, UnitKind::Function)
            && ast_type_spec.is_port(&ctx.symtab)?
        {
            return Err(Diagnostic::error(
                &entity.unit_kind,
                "Functions are not allowed on port types",
            )
            .primary_label("Function on port type")
            .secondary_label(ast_type_spec, "This is a port type")
            .span_suggest_replace(
                "Consider making this an entity",
                &entity.unit_kind,
                "entity",
            )
            .into());
        }

        let path_suffix = Some(Path(vec![
            Identifier(format!("impl_{}", impl_block_id)).nowhere()
        ]));
        global_symbols::visit_unit(&path_suffix, entity, &mut ctx.symtab, &self_context)?;
        let item = visit_unit(path_suffix, entity, ctx)?;

        match &item {
            hir::Item::Unit(e) => {
                trait_members.push((entity.name.inner.clone(), e.head.clone()));

                trait_impl.insert(
                    entity.name.inner.clone(),
                    (e.name.name_id().inner.clone(), e.loc()),
                );
            }
            hir::Item::Builtin(_, head) => {
                return Err(Diagnostic::error(head, "Methods can not be __builtin__")
                    .help("Consider defining a free-standing function")
                    .into())
            }
        }

        result.push(item);
    }

    if is_anonymous {
        // Add the trait to the trait list
        items.traits.insert(trait_name.clone(), trait_members);
        items
            .impls
            .entry(target_name.0)
            .or_insert(HashMap::new())
            .insert(trait_name, hir::ImplBlock { fns: trait_impl });
    }

    Ok(result)
}

#[tracing::instrument(skip_all, fields(name=?item.name()))]
pub fn visit_item(
    item: &ast::Item,
    ctx: &mut Context,
    item_list: &mut hir::ItemList,
) -> Result<(Vec<hir::Item>, Option<hir::ItemList>)> {
    match item {
        ast::Item::Unit(u) => Ok((vec![visit_unit(None, u, ctx)?], None)),
        ast::Item::TraitDef(_) => {
            todo!("Visit trait definitions")
        }
        ast::Item::Type(_) => {
            // Global symbol lowering already visits type declarations
            event!(Level::INFO, "Type definition");
            Ok((vec![], None))
        }
        ast::Item::ImplBlock(block) => Ok((visit_impl(block, item_list, ctx)?, None)),
        ast::Item::Module(m) => {
            ctx.symtab.push_namespace(m.name.clone());
            let mut new_item_list = hir::ItemList::new();
            let result = match visit_module(&mut new_item_list, m, ctx) {
                Ok(()) => Ok((vec![], Some(new_item_list))),
                Err(e) => Err(e),
            };
            ctx.symtab.pop_namespace();
            result
        }
        ast::Item::Use(_) => Ok((vec![], None)),
        ast::Item::Config(_) => Ok((vec![], None)),
    }
}

#[tracing::instrument(skip_all, fields(module.name = %module.name.inner))]
pub fn visit_module(
    item_list: &mut hir::ItemList,
    module: &ast::Module,
    ctx: &mut Context,
) -> Result<()> {
    visit_module_body(item_list, &module.body, ctx)
}

#[tracing::instrument(skip_all)]
pub fn visit_module_body(
    item_list: &mut hir::ItemList,
    body: &ast::ModuleBody,
    ctx: &mut Context,
) -> Result<()> {
    let all_items = body
        .members
        .iter()
        .map(|i| visit_item(i, ctx, item_list))
        .collect::<Result<Vec<_>>>()?
        .into_iter();

    for (items, new_item_list) in all_items {
        // Insertion in hash maps return a value if duplicates are present (or not if try_insert is
        // used) We need to get rid of that for the type of the match block here to work, and a macro
        // hides those details
        macro_rules! add_item {
            ($map:expr, $name:expr, $item:expr) => {{
                if let Some(_) = $map.insert($name, $item) {
                    panic!("Internal error: Multiple things named {}", $name)
                }
            }};
        }

        use hir::Item::*;
        for item in items {
            match &item {
                Unit(u) => add_item!(
                    item_list.executables,
                    u.name.name_id().inner.clone(),
                    ExecutableItem::Unit(u.clone())
                ),
                Builtin(name, head) => add_item!(
                    item_list.executables,
                    name.name_id().inner.clone(),
                    ExecutableItem::BuiltinUnit(name.clone(), head.clone())
                ),
            }
        }

        match new_item_list {
            Some(list) => {
                for (name, executable) in list.executables {
                    add_item!(item_list.executables, name.clone(), executable)
                }
            }
            None => {}
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
                                DeclarationState::Defined(previous) => {
                                    return Err(Diagnostic::error(
                                        ident,
                                        format!("{ident} was already defined"),
                                    )
                                    .secondary_label(previous, "First defined here")
                                    .primary_label("Later defined here")
                                    .secondary_label(state.loc(), format!("{ident} declared here"))
                                    .note("Declared variables can only be defined once")
                                    .into());
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
                        name: name_id.at_loc(&ident),
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
                        .map(|(ident, _)| ident.inner.clone())
                        .collect::<HashSet<_>>();

                    let mut patterns = patterns
                        .iter()
                        .map(|(target, pattern)| {
                            let ast_pattern =
                                pattern.as_ref().map(|i| i.clone()).unwrap_or_else(|| {
                                    ast::Pattern::Path(Path(vec![target.clone()]).at_loc(&target))
                                        .at_loc(&target)
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
                            if let None = unbound.take(target) {
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
                                target: arg.0.clone(),
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

            Ok(vec![hir::Statement::Declaration(names).at_loc(&s)])
        }
        ast::Statement::Binding(pattern, t, expr) => {
            let hir_type = if let Some(t) = t {
                Some(visit_type_spec(t, &mut ctx.symtab)?)
            } else {
                None
            };

            let expr = expr.try_visit(visit_expression, ctx)?;

            let pat = pattern.try_visit(visit_pattern, ctx)?;

            Ok(vec![hir::Statement::Binding(pat, hir_type, expr).at_loc(s)])
        }
        ast::Statement::Register(inner) => {
            let (result, span) = visit_register(&inner, ctx)?.separate_loc();
            Ok(vec![hir::Statement::Register(result).at_loc(&span)])
        }
        ast::Statement::PipelineRegMarker(count) => {
            let result = (0..*count)
                .map(|_| {
                    ctx.pipeline_ctx
                        .as_mut()
                        .expect("Expected to have a pipeline context")
                        .current_stage += 1;
                    hir::Statement::PipelineRegMarker.at_loc(s)
                })
                .collect();

            Ok(result)
        }
        ast::Statement::Label(name) => {
            // NOTE: pipeline labels are lowered in visit_pipeline
            Ok(vec![hir::Statement::Label(name.clone()).at_loc(s)])
        }
        ast::Statement::Assert(expr) => {
            let expr = expr.try_visit(visit_expression, ctx)?;

            Ok(vec![hir::Statement::Assert(expr).at_loc(s)])
        }
        ast::Statement::Comptime(condition) => {
            if let Some(ast_statements) = condition.maybe_unpack(&ctx.symtab)? {
                Ok(ast_statements
                    .iter()
                    .map(|s| visit_statement(&s, ctx))
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
) -> Result<hir::ArgumentList> {
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
        ast::CallKind::Entity(loc) => hir::expression::CallKind::Entity(loc.clone()),
        ast::CallKind::Pipeline(loc, depth) => {
            let depth = depth.clone().maybe_unpack(&ctx.symtab)?.ok_or_else(|| {
                Diagnostic::error(depth, "Expected pipeline depth")
                    .help("The current comptime branch did not specify a depth")
            })?;
            hir::expression::CallKind::Pipeline(
                loc.clone(),
                int_literal_to_pipeline_stages(&depth)?,
            )
        }
    })
}

#[tracing::instrument(skip_all, fields(kind=e.variant_str()))]
pub fn visit_expression(e: &ast::Expression, ctx: &mut Context) -> Result<hir::Expression> {
    let new_id = ctx.idtracker.next();

    match e {
        ast::Expression::IntLiteral(val) => {
            let result = match val {
                ast::IntLiteral::Signed(val) => hir::expression::IntLiteral::Signed(val.clone()),
                ast::IntLiteral::Unsigned(val) => hir::expression::IntLiteral::Unsigned(val.clone()),
            };
            Ok(hir::ExprKind::IntLiteral(result.clone()))
        },
        ast::Expression::BoolLiteral(val) => Ok(hir::ExprKind::BoolLiteral(*val)),
        ast::Expression::BinaryOperator(lhs, tok, rhs) => {
            let lhs = lhs.try_visit(visit_expression, ctx)?;
            let rhs = rhs.try_visit(visit_expression, ctx)?;

            let operator = |op| hir::ExprKind::BinaryOperator(Box::new(lhs), op, Box::new(rhs));

            match tok {
                ast::BinaryOperator::Add => Ok(operator(BinaryOperator::Add)),
                ast::BinaryOperator::Sub => Ok(operator(BinaryOperator::Sub)),
                ast::BinaryOperator::Mul => Ok(operator(BinaryOperator::Mul)),
                ast::BinaryOperator::Equals => Ok(operator(BinaryOperator::Eq)),
                ast::BinaryOperator::Gt => Ok(operator(BinaryOperator::Gt)),
                ast::BinaryOperator::Lt => Ok(operator(BinaryOperator::Lt)),
                ast::BinaryOperator::Ge => Ok(operator(BinaryOperator::Ge)),
                ast::BinaryOperator::Le => Ok(operator(BinaryOperator::Le)),
                ast::BinaryOperator::LeftShift => Ok(operator(BinaryOperator::LeftShift)),
                ast::BinaryOperator::RightShift => Ok(operator(BinaryOperator::RightShift)),
                ast::BinaryOperator::ArithmeticRightShift => Ok(operator(BinaryOperator::ArithmeticRightShift)),
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

            let unop = |op| hir::ExprKind::UnaryOperator(op, Box::new(operand));
            match operator {
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
                .into_iter()
                .map(|e| e.try_map_ref(|e| visit_expression(e, ctx)))
                .collect::<Result<Vec<_>>>()?;
            Ok(hir::ExprKind::TupleLiteral(exprs))
        }
        ast::Expression::ArrayLiteral(exprs) => {
            let exprs = exprs
                .into_iter()
                .map(|e| e.try_map_ref(|e| visit_expression(e, ctx)))
                .collect::<Result<Vec<_>>>()?;
            Ok(hir::ExprKind::ArrayLiteral(exprs))
        }
        ast::Expression::Index(target, index) => {
            let target = target.try_visit(visit_expression, ctx)?;
            let index = index.try_visit(visit_expression, ctx)?;
            Ok(hir::ExprKind::Index(Box::new(target), Box::new(index)))
        }
        ast::Expression::TupleIndex(tuple, index) => Ok(hir::ExprKind::TupleIndex(
            Box::new(tuple.try_visit(visit_expression, ctx)?),
            index.clone(),
        )),
        ast::Expression::FieldAccess(target, field) => Ok(hir::ExprKind::FieldAccess(
            Box::new(target.try_visit(visit_expression, ctx)?),
            field.clone(),
        )),
        ast::Expression::MethodCall{kind, target, name, args} => Ok(hir::ExprKind::MethodCall{
            target: Box::new(target.try_visit(visit_expression, ctx)?),
            name: name.clone(),
            args: args.try_map_ref(|args| visit_argument_list(args, ctx))?,
            call_kind: visit_call_kind(kind, ctx)?,
        }),
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
                return Err(Diagnostic::error(branches, "Match body has no arms").primary_label("This match body has no arms").into());
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
        ast::Expression::Call{kind, callee, args} => {
            let (name_id, _) = ctx.symtab.lookup_unit(callee)?;
            let args = visit_argument_list(args, ctx)?.at_loc(args);

            let kind = visit_call_kind(kind, ctx)?;

            Ok(hir::ExprKind::Call{kind, callee: name_id.at_loc(callee), args})
        }
        ast::Expression::Identifier(path) => {
            // If the identifier isn't a valid variable, report as "expected value".
            let id = ctx.symtab.lookup_variable(path).map_err(|err| match err {
                LookupError::NotAVariable(path, was) => LookupError::NotAValue(path, was),
                err => err,
            })?;

            Ok(hir::ExprKind::Identifier(id))
        }
        ast::Expression::PipelineReference { stage_kw_and_reference_loc, stage, name } => {
            let pipeline_ctx = ctx
                .pipeline_ctx
                .as_ref()
                .expect("Expected to have a pipeline context");

            let (stage_index, loc) = match stage {
                ast::PipelineStageReference::Relative(offset) => {
                    let current = pipeline_ctx.current_stage;
                    let absolute = current as i64 + &offset.inner;

                    if absolute < BigInt::zero() {
                        return Err(Diagnostic::error(
                            stage_kw_and_reference_loc,
                            "Reference to negative pipeline stage",
                        )
                        .primary_label("This references a negative pipeline stage")
                        .note(format!(
                            "Since this is at stage {current}, stage({offset}) references stage {absolute}"
                        ))
                        .note("Pipeline stages start at 0")
                        .into());
                    }
                    let absolute = absolute.to_usize().ok_or_else(|| {
                        Diagnostic::error(offset, "Pipeline offset overflow")
                            .primary_label(format!("Pipeline stages must fit in 0..{}", usize::MAX))
                    })?;
                    let pipeline_depth = pipeline_ctx.stages.len();
                    if absolute >= pipeline_depth {
                        return Err(Diagnostic::error(stage_kw_and_reference_loc, "Reference to pipeline stage beyond pipeline depth")
                            .primary_label("This references a pipeline stage beyond the pipeline depth")
                            .note(format!("Since this is at stage {current}, stage(+{offset}) references stage {absolute}"))
                            .note(format!("The pipeline has depth {}", pipeline_depth - 1))
                            .into()

                        )
                    }

                    (absolute, offset.loc())
                }
                ast::PipelineStageReference::Absolute(name) => (
                    pipeline_ctx
                        .get_stage(name)
                        .ok_or_else(|| Diagnostic::error(name, "Undefined pipeline stage")
                            .primary_label(format!("Can't find pipeline stage '{name}"))
                        )?,
                    name.loc(),
                ),
            };

            let path = Path(vec![name.clone()]).at_loc(name);
            let (name_id, declares_name) = match ctx.symtab.try_lookup_variable(&path)? {
                Some(id) => (id.at_loc(name), false),
                None => (ctx.symtab.add_declaration(name.clone())?.at_loc(name), true),
            };

            Ok(hir::ExprKind::PipelineRef {
                stage: stage_index.at_loc(&loc),
                name: name_id,
                declares_name,
            })
        }
        ast::Expression::Comptime(inner) => {
            let inner = inner
                .maybe_unpack(&ctx.symtab)?
                .ok_or_else(|| {
                Diagnostic::error(inner.as_ref(), "Missing expression")
                    .help("The current comptime branch has no expression")
                })?;
            Ok(visit_expression(&inner, ctx)?.kind)
        }
    }
    .map(|kind| kind.with_id(new_id))
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
        .into_iter()
        .collect::<Vec<_>>();

    let result = b.result.try_visit(visit_expression, ctx)?;

    if let Some(undefined) = ctx.symtab.get_undefined_declarations().first() {
        return Err(
            Diagnostic::error(undefined, "Declared variable is not defined")
                .primary_label("This variable is declared but not defined")
                // FIXME: Suggest removing the declaration (with a diagnostic suggestion) only if the variable is unused.
                .help(format!("Define {undefined} with a let or reg binding"))
                .help("Or, remove the declaration if the variable is unused")
                .into(),
        );
    }

    ctx.symtab.close_scope();

    Ok(hir::Block { statements, result })
}

fn visit_register(reg: &Loc<ast::Register>, ctx: &mut Context) -> Result<Loc<hir::Register>> {
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

    let value = reg.value.try_visit(visit_expression, ctx)?;

    let value_type = if let Some(value_type) = &reg.value_type {
        Some(visit_type_spec(value_type, &mut ctx.symtab)?)
    } else {
        None
    };

    Ok(hir::Register {
        pattern,
        clock,
        reset,
        value,
        value_type,
    }
    .at_loc(&loc))
}

/// Ensures that there are no functions in anonymous trait impls that have conflicting
/// names
#[tracing::instrument(skip(item_list))]
pub fn ensure_unique_anonymous_traits(item_list: &hir::ItemList) -> Vec<Diagnostic> {
    item_list
        .impls
        .iter()
        .map(|(type_name, impls)| {
            let mut fns = impls
                .iter()
                .filter(|(trait_name, _)| trait_name.is_anonymous())
                .flat_map(|(_, impl_block)| impl_block.fns.iter())
                .collect::<Vec<_>>();

            // For deterministic error messages, the order at which functions are seen must be
            // deterministic. This is not the case as the impls come out of the hash map, so we'll
            // sort them depending on the loc span of the impl. The exact ordering is
            // completely irrelevant, as long as it is ordered the same way every time a test
            // is run
            fns.sort_by_key(|f| f.1 .1.span);

            let mut set: HashMap<&Identifier, Loc<()>> = HashMap::new();

            let mut duplicate_errs = vec![];
            for (f, f_loc) in fns {
                if let Some(prev) = set.get(f) {
                    duplicate_errs.push(
                        Diagnostic::error(
                            f_loc.1,
                            format!("{type_name} already has a method named {f}"),
                        )
                        .primary_label("Duplicate method")
                        .secondary_label(prev, "Previous definition here")
                        .into(),
                    );
                } else {
                    set.insert(f, f_loc.1.clone());
                }
            }

            duplicate_errs
        })
        .flatten()
        .collect::<Vec<_>>()
}

#[cfg(test)]
mod entity_visiting {
    use super::*;

    use hir::UnitName;
    use spade_ast::testutil::{ast_ident, ast_path};
    use spade_common::name::testutil::name_id;
    use spade_common::{location_info::WithLocation, name::Identifier};

    use pretty_assertions::assert_eq;

    #[test]
    fn entity_visits_work() {
        let input = ast::Unit {
            name: Identifier("test".to_string()).nowhere(),
            inputs: ParameterList::without_self(vec![(
                ast_ident("a"),
                ast::TypeSpec::Unit(().nowhere()).nowhere(),
            )])
            .nowhere(),
            output_type: None,
            body: Some(
                ast::Expression::Block(Box::new(ast::Block {
                    statements: vec![ast::Statement::Binding(
                        ast::Pattern::name("var"),
                        Some(ast::TypeSpec::Unit(().nowhere()).nowhere()),
                        ast::Expression::int_literal(0).nowhere(),
                    )
                    .nowhere()],
                    result: ast::Expression::int_literal(0).nowhere(),
                }))
                .nowhere(),
            ),
            type_params: vec![],
            attributes: ast::AttributeList(vec![]),
            unit_kind: ast::UnitKind::Entity.nowhere(),
        }
        .nowhere();

        let expected = hir::Unit {
            name: UnitName::FullPath(name_id(0, "test")),
            head: hir::UnitHead {
                name: Identifier("test".to_string()).nowhere(),
                inputs: hir::ParameterList(vec![(ast_ident("a"), hir::TypeSpec::unit().nowhere())]),
                output_type: None,
                type_params: vec![],
                unit_kind: hir::UnitKind::Entity.nowhere(),
            },
            inputs: vec![((name_id(1, "a"), hir::TypeSpec::unit().nowhere()))],
            body: hir::ExprKind::Block(Box::new(hir::Block {
                statements: vec![hir::Statement::Binding(
                    hir::PatternKind::name(name_id(2, "var")).idless().nowhere(),
                    Some(hir::TypeSpec::unit().nowhere()),
                    hir::ExprKind::int_literal(0).idless().nowhere(),
                )
                .nowhere()],
                result: hir::ExprKind::int_literal(0).idless().nowhere(),
            }))
            .idless()
            .nowhere(),
        }
        .nowhere();

        let symtab = SymbolTable::new();
        let idtracker = ExprIdTracker::new();
        let mut ctx = Context {
            symtab,
            idtracker,
            impl_idtracker: ImplIdTracker::new(),
            pipeline_ctx: None,
        };
        global_symbols::visit_unit(&None, &input, &mut ctx.symtab, &SelfContext::FreeStanding)
            .expect("Failed to collect global symbols");

        let result = visit_unit(None, &input, &mut ctx);

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
        //         statements: vec![ast::Statement::Binding(
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
        //         statements: vec![hir::Statement::Binding(
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

    use pretty_assertions::assert_eq;
    use spade_ast::testutil::{ast_ident, ast_path};
    use spade_common::location_info::WithLocation;
    use spade_common::name::testutil::name_id;

    #[test]
    fn bindings_convert_correctly() {
        let symtab = SymbolTable::new();
        let idtracker = ExprIdTracker::new();
        let mut ctx = &mut Context {
            symtab,
            idtracker,
            impl_idtracker: ImplIdTracker::new(),
            pipeline_ctx: None,
        };

        let input = ast::Statement::Binding(
            ast::Pattern::name("a"),
            Some(ast::TypeSpec::Unit(().nowhere()).nowhere()),
            ast::Expression::int_literal(0).nowhere(),
        )
        .nowhere();

        let expected = hir::Statement::Binding(
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
                value: ast::Expression::int_literal(0).nowhere(),
                value_type: None,
            }
            .nowhere(),
        )
        .nowhere();

        let expected = hir::Statement::Register(
            hir::Register {
                pattern: hir::PatternKind::name(name_id(1, "regname"))
                    .idless()
                    .nowhere(),
                clock: hir::ExprKind::Identifier(name_id(0, "clk").inner)
                    .with_id(0)
                    .nowhere(),
                reset: None,
                value: hir::ExprKind::int_literal(0).idless().nowhere(),
                value_type: None,
            }
            .nowhere(),
        )
        .nowhere();

        let symtab = SymbolTable::new();
        let idtracker = ExprIdTracker::new();
        let mut ctx = Context {
            symtab,
            idtracker,
            impl_idtracker: ImplIdTracker::new(),
            pipeline_ctx: None,
        };
        let clk_id = ctx.symtab.add_local_variable(ast_ident("clk"));
        assert_eq!(clk_id.0, 0);
        assert_eq!(visit_statement(&input, &mut ctx), Ok(vec![expected]));
        assert_eq!(ctx.symtab.has_symbol(ast_path("regname").inner), true);
    }

    #[test]
    fn declarations_declare_variables() {
        let input = ast::Statement::Declaration(vec![ast_ident("x"), ast_ident("y")]).nowhere();

        let symtab = SymbolTable::new();
        let idtracker = ExprIdTracker::new();
        let mut ctx = Context {
            symtab,
            idtracker,
            impl_idtracker: ImplIdTracker::new(),
            pipeline_ctx: None,
        };
        assert_eq!(
            visit_statement(&input, &mut ctx),
            Ok(vec![hir::Statement::Declaration(vec![
                name_id(0, "x"),
                name_id(1, "y")
            ])
            .nowhere()])
        );
        assert_eq!(ctx.symtab.has_symbol(ast_path("x").inner), true);
        assert_eq!(ctx.symtab.has_symbol(ast_path("y").inner), true);
    }

    #[test]
    fn multi_reg_statements_lower_correctly() {
        let input = ast::Statement::PipelineRegMarker(3).nowhere();

        let symtab = SymbolTable::new();
        let idtracker = ExprIdTracker::new();
        let mut ctx = Context {
            symtab,
            idtracker,
            impl_idtracker: ImplIdTracker::new(),
            pipeline_ctx: Some(PipelineContext {
                stages: vec![],
                current_stage: 0,
            }),
        };
        assert_eq!(
            visit_statement(&input, &mut ctx),
            Ok(vec![
                hir::Statement::PipelineRegMarker.nowhere(),
                hir::Statement::PipelineRegMarker.nowhere(),
                hir::Statement::PipelineRegMarker.nowhere(),
            ])
        );

        assert_eq!(ctx.pipeline_ctx.as_ref().unwrap().current_stage, 3);
    }
}

#[cfg(test)]
mod expression_visiting {
    use super::*;

    use ast::comptime::MaybeComptime;
    use hir::symbol_table::EnumVariant;
    use spade_ast::testutil::{ast_ident, ast_path};
    use spade_common::location_info::WithLocation;
    use spade_common::name::testutil::name_id;
    use spade_common::num_ext::InfallibleToBigInt;

    #[test]
    fn int_literals_work() {
        let symtab = SymbolTable::new();
        let idtracker = ExprIdTracker::new();
        let input = ast::Expression::int_literal(123);
        let expected = hir::ExprKind::int_literal(123).idless();

        assert_eq!(
            visit_expression(
                &input,
                &mut Context {
                    symtab,
                    idtracker,
                    impl_idtracker: ImplIdTracker::new(),
                    pipeline_ctx: None
                }
            ),
            Ok(expected)
        );
    }

    macro_rules! binop_test {
        ($test_name:ident, $token:ident, $op:ident) => {
            #[test]
            fn $test_name() {
                let symtab = SymbolTable::new();
                let idtracker = ExprIdTracker::new();
                let input = ast::Expression::BinaryOperator(
                    Box::new(ast::Expression::int_literal(123).nowhere()),
                    spade_ast::BinaryOperator::$token,
                    Box::new(ast::Expression::int_literal(456).nowhere()),
                );
                let expected = hir::ExprKind::BinaryOperator(
                    Box::new(hir::ExprKind::int_literal(123).idless().nowhere()),
                    BinaryOperator::$op,
                    Box::new(hir::ExprKind::int_literal(456).idless().nowhere()),
                )
                .idless();

                assert_eq!(
                    visit_expression(
                        &input,
                        &mut Context {
                            symtab,
                            idtracker,
                            impl_idtracker: ImplIdTracker::new(),
                            pipeline_ctx: None
                        }
                    ),
                    Ok(expected)
                );
            }
        };
    }

    macro_rules! unop_test {
        ($test_name:ident, $token:ident, $op:ident) => {
            #[test]
            fn $test_name() {
                let symtab = SymbolTable::new();
                let idtracker = ExprIdTracker::new();
                let input = ast::Expression::UnaryOperator(
                    spade_ast::UnaryOperator::$token,
                    Box::new(ast::Expression::int_literal(456).nowhere()),
                );
                let expected = hir::ExprKind::UnaryOperator(
                    hir::expression::UnaryOperator::$op,
                    Box::new(hir::ExprKind::int_literal(456).idless().nowhere()),
                )
                .idless();

                assert_eq!(
                    visit_expression(
                        &input,
                        &mut Context {
                            symtab,
                            idtracker,
                            impl_idtracker: ImplIdTracker::new(),
                            pipeline_ctx: None
                        }
                    ),
                    Ok(expected)
                );
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
        let symtab = SymbolTable::new();
        let idtracker = ExprIdTracker::new();
        let input = ast::Expression::Index(
            Box::new(ast::Expression::int_literal(0).nowhere()),
            Box::new(ast::Expression::int_literal(1).nowhere()),
        );

        let expected = hir::ExprKind::Index(
            Box::new(hir::ExprKind::int_literal(0).idless().nowhere()),
            Box::new(hir::ExprKind::int_literal(1).idless().nowhere()),
        )
        .idless();

        assert_eq!(
            visit_expression(
                &input,
                &mut Context {
                    symtab,
                    idtracker,
                    impl_idtracker: ImplIdTracker::new(),
                    pipeline_ctx: None
                }
            ),
            Ok(expected)
        );
    }

    #[test]
    fn field_access_works() {
        let symtab = SymbolTable::new();
        let idtracker = ExprIdTracker::new();
        let input = ast::Expression::FieldAccess(
            Box::new(ast::Expression::int_literal(0).nowhere()),
            ast_ident("a"),
        );

        let expected = hir::ExprKind::FieldAccess(
            Box::new(hir::ExprKind::int_literal(0).idless().nowhere()),
            ast_ident("a"),
        )
        .idless();

        assert_eq!(
            visit_expression(
                &input,
                &mut Context {
                    symtab,
                    idtracker,
                    impl_idtracker: ImplIdTracker::new(),
                    pipeline_ctx: None
                }
            ),
            Ok(expected)
        );
    }

    #[test]
    fn blocks_work() {
        let input = ast::Expression::Block(Box::new(ast::Block {
            statements: vec![ast::Statement::Binding(
                ast::Pattern::name("a"),
                None,
                ast::Expression::int_literal(0).nowhere(),
            )
            .nowhere()],
            result: ast::Expression::int_literal(0).nowhere(),
        }));
        let expected = hir::ExprKind::Block(Box::new(hir::Block {
            statements: vec![hir::Statement::Binding(
                hir::PatternKind::name(name_id(0, "a")).idless().nowhere(),
                None,
                hir::ExprKind::int_literal(0).idless().nowhere(),
            )
            .nowhere()],
            result: hir::ExprKind::int_literal(0).idless().nowhere(),
        }))
        .idless();

        let symtab = SymbolTable::new();
        let idtracker = ExprIdTracker::new();
        let mut ctx = Context {
            symtab,
            idtracker,
            impl_idtracker: ImplIdTracker::new(),
            pipeline_ctx: None,
        };
        assert_eq!(visit_expression(&input, &mut ctx), Ok(expected));
        assert!(!ctx.symtab.has_symbol(ast_path("a").inner));
    }

    #[test]
    fn if_expressions_work() {
        let input = ast::Expression::If(
            Box::new(ast::Expression::int_literal(0).nowhere()),
            Box::new(
                ast::Expression::Block(Box::new(ast::Block {
                    statements: vec![],
                    result: ast::Expression::int_literal(1).nowhere(),
                }))
                .nowhere(),
            ),
            Box::new(
                ast::Expression::Block(Box::new(ast::Block {
                    statements: vec![],
                    result: ast::Expression::int_literal(2).nowhere(),
                }))
                .nowhere(),
            ),
        );
        let expected = hir::ExprKind::If(
            Box::new(hir::ExprKind::int_literal(0).idless().nowhere()),
            Box::new(
                hir::ExprKind::Block(Box::new(hir::Block {
                    statements: vec![],
                    result: hir::ExprKind::int_literal(1).idless().nowhere(),
                }))
                .idless()
                .nowhere(),
            ),
            Box::new(
                hir::ExprKind::Block(Box::new(hir::Block {
                    statements: vec![],
                    result: hir::ExprKind::int_literal(2).idless().nowhere(),
                }))
                .idless()
                .nowhere(),
            ),
        )
        .idless();

        let symtab = SymbolTable::new();
        let idtracker = ExprIdTracker::new();
        assert_eq!(
            visit_expression(
                &input,
                &mut Context {
                    symtab,
                    idtracker,
                    impl_idtracker: ImplIdTracker::new(),
                    pipeline_ctx: None
                }
            ),
            Ok(expected)
        );
    }

    #[test]
    fn match_expressions_work() {
        let input = ast::Expression::Match(
            Box::new(ast::Expression::int_literal(1).nowhere()),
            vec![(
                ast::Pattern::name("x"),
                ast::Expression::int_literal(2).nowhere(),
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

        let symtab = SymbolTable::new();
        let idtracker = ExprIdTracker::new();
        assert_eq!(
            visit_expression(
                &input,
                &mut Context {
                    symtab,
                    idtracker,
                    impl_idtracker: ImplIdTracker::new(),
                    pipeline_ctx: None
                }
            ),
            Ok(expected)
        )
    }

    #[test]
    fn match_expressions_with_enum_members_works() {
        let input = ast::Expression::Match(
            Box::new(ast::Expression::int_literal(1).nowhere()),
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
            params: hir::ParameterList(vec![(
                ast_ident("x"),
                hir::TypeSpec::Unit(().nowhere()).nowhere(),
            )]),
            type_params: vec![],
        }
        .nowhere();

        symtab.add_thing_with_id(100, ast_path("x").inner, Thing::EnumVariant(enum_variant));
        let idtracker = ExprIdTracker::new();
        assert_eq!(
            visit_expression(
                &input,
                &mut Context {
                    symtab,
                    idtracker,
                    impl_idtracker: ImplIdTracker::new(),
                    pipeline_ctx: None
                }
            ),
            Ok(expected)
        )
    }

    #[test]
    fn match_expressions_with_0_argument_enum_works() {
        let input = ast::Expression::Match(
            Box::new(ast::Expression::int_literal(1).nowhere()),
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
            params: hir::ParameterList(vec![(
                ast_ident("x"),
                hir::TypeSpec::Unit(().nowhere()).nowhere(),
            )]),
            type_params: vec![],
        }
        .nowhere();

        symtab.add_thing_with_id(100, ast_path("x").inner, Thing::EnumVariant(enum_variant));
        let idtracker = ExprIdTracker::new();
        assert_eq!(
            visit_expression(
                &input,
                &mut Context {
                    symtab,
                    idtracker,
                    impl_idtracker: ImplIdTracker::new(),
                    pipeline_ctx: None
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
                ast::Expression::int_literal(1).nowhere(),
                ast::Expression::int_literal(2).nowhere(),
            ])
            .nowhere(),
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
        }
        .idless();

        let mut symtab = SymbolTable::new();
        let idtracker = ExprIdTracker::new();

        symtab.add_thing(
            ast_path("test").inner,
            Thing::Unit(
                UnitHead {
                    name: Identifier("".to_string()).nowhere(),
                    inputs: hir::ParameterList(vec![
                        (ast_ident("a"), hir::TypeSpec::unit().nowhere()),
                        (ast_ident("b"), hir::TypeSpec::unit().nowhere()),
                    ]),
                    output_type: None,
                    type_params: vec![],
                    unit_kind: hir::UnitKind::Entity.nowhere(),
                }
                .nowhere(),
            ),
        );

        assert_eq!(
            visit_expression(
                &input,
                &mut Context {
                    symtab,
                    idtracker,
                    impl_idtracker: ImplIdTracker::new(),
                    pipeline_ctx: None
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
                ast::NamedArgument::Full(ast_ident("b"), ast::Expression::int_literal(2).nowhere()),
                ast::NamedArgument::Full(ast_ident("a"), ast::Expression::int_literal(1).nowhere()),
            ])
            .nowhere(),
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
        }
        .idless();

        let mut symtab = SymbolTable::new();
        let idtracker = ExprIdTracker::new();

        symtab.add_thing(
            ast_path("test").inner,
            Thing::Unit(
                UnitHead {
                    name: Identifier("".to_string()).nowhere(),
                    inputs: hir::ParameterList(vec![
                        (ast_ident("a"), hir::TypeSpec::unit().nowhere()),
                        (ast_ident("b"), hir::TypeSpec::unit().nowhere()),
                    ]),
                    output_type: None,
                    type_params: vec![],
                    unit_kind: hir::UnitKind::Entity.nowhere(),
                }
                .nowhere(),
            ),
        );

        assert_eq!(
            visit_expression(
                &input,
                &mut Context {
                    symtab,
                    idtracker,
                    impl_idtracker: ImplIdTracker::new(),
                    pipeline_ctx: None
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
                ast::Expression::int_literal(1).nowhere(),
                ast::Expression::int_literal(2).nowhere(),
            ])
            .nowhere(),
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
        }
        .idless();

        let mut symtab = SymbolTable::new();
        let idtracker = ExprIdTracker::new();

        symtab.add_thing(
            ast_path("test").inner,
            Thing::Unit(
                UnitHead {
                    name: Identifier("".to_string()).nowhere(),
                    inputs: hir::ParameterList(vec![
                        (ast_ident("a"), hir::TypeSpec::unit().nowhere()),
                        (ast_ident("b"), hir::TypeSpec::unit().nowhere()),
                    ]),
                    output_type: None,
                    type_params: vec![],
                    unit_kind: hir::UnitKind::Function(hir::FunctionKind::Fn).nowhere(),
                }
                .nowhere(),
            ),
        );

        assert_eq!(
            visit_expression(
                &input,
                &mut Context {
                    symtab,
                    idtracker,
                    impl_idtracker: ImplIdTracker::new(),
                    pipeline_ctx: None
                }
            ),
            Ok(expected)
        );
    }

    #[test]
    fn pipeline_instantiation_works() {
        let input = ast::Expression::Call {
            kind: ast::CallKind::Pipeline(
                ().nowhere(),
                MaybeComptime::Raw(ast::IntLiteral::Signed(2.to_bigint()).nowhere()).nowhere(),
            ),
            callee: ast_path("test"),
            args: ast::ArgumentList::Positional(vec![
                ast::Expression::int_literal(1).nowhere(),
                ast::Expression::int_literal(2).nowhere(),
            ])
            .nowhere(),
        }
        .nowhere();

        let expected = hir::ExprKind::Call {
            kind: hir::expression::CallKind::Pipeline(().nowhere(), 2.nowhere()),
            callee: name_id(0, "test"),
            args: hir::ArgumentList::Positional(vec![
                hir::ExprKind::int_literal(1).idless().nowhere(),
                hir::ExprKind::int_literal(2).idless().nowhere(),
            ])
            .nowhere(),
        }
        .idless();

        let mut symtab = SymbolTable::new();
        let idtracker = ExprIdTracker::new();

        symtab.add_thing(
            ast_path("test").inner,
            Thing::Unit(
                UnitHead {
                    name: Identifier("".to_string()).nowhere(),
                    unit_kind: hir::UnitKind::Pipeline(2.nowhere()).nowhere(),
                    inputs: hir::ParameterList(vec![
                        (ast_ident("a"), hir::TypeSpec::unit().nowhere()),
                        (ast_ident("b"), hir::TypeSpec::unit().nowhere()),
                    ]),
                    output_type: None,
                    type_params: vec![],
                }
                .nowhere(),
            ),
        );

        assert_eq!(
            visit_expression(
                &input,
                &mut Context {
                    symtab,
                    idtracker,
                    impl_idtracker: ImplIdTracker::new(),
                    pipeline_ctx: None
                }
            ),
            Ok(expected)
        );
    }
}

#[cfg(test)]
mod pattern_visiting {
    use ast::{
        testutil::{ast_ident, ast_path},
        ArgumentPattern,
    };
    use hir::{
        symbol_table::{StructCallable, TypeDeclKind},
        PatternKind,
    };
    use spade_common::{id_tracker::ImplIdTracker, name::testutil::name_id};

    use super::*;

    #[test]
    fn bool_patterns_work() {
        let input = ast::Pattern::Bool(true);

        let symtab = SymbolTable::new();
        let idtracker = ExprIdTracker::new();

        let result = visit_pattern(
            &input,
            &mut Context {
                symtab,
                idtracker,
                impl_idtracker: ImplIdTracker::new(),
                pipeline_ctx: None,
            },
        );

        assert_eq!(result, Ok(PatternKind::Bool(true).idless()));
    }

    #[test]
    fn int_patterns_work() {
        let input = ast::Pattern::integer(5);

        let symtab = SymbolTable::new();
        let idtracker = ExprIdTracker::new();

        let result = visit_pattern(
            &input,
            &mut Context {
                symtab,
                idtracker,
                impl_idtracker: ImplIdTracker::new(),
                pipeline_ctx: None,
            },
        );

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
        let idtracker = ExprIdTracker::new();

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
                    params: hir::ParameterList(vec![
                        (ast_ident("x"), hir::TypeSpec::unit().nowhere()),
                        (ast_ident("y"), hir::TypeSpec::unit().nowhere()),
                    ]),
                    type_params: vec![],
                }
                .nowhere(),
            ),
        );

        let result = visit_pattern(
            &input,
            &mut Context {
                symtab,
                idtracker,
                impl_idtracker: ImplIdTracker::new(),
                pipeline_ctx: None,
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
                ast::Expression::int_literal(0).nowhere(),
            )),
            value: ast::Expression::int_literal(1).nowhere(),
            value_type: Some(ast::TypeSpec::Unit(().nowhere()).nowhere()),
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
            value: hir::ExprKind::int_literal(1).idless().nowhere(),
            value_type: Some(hir::TypeSpec::unit().nowhere()),
        }
        .nowhere();

        let mut symtab = SymbolTable::new();
        let idtracker = ExprIdTracker::new();
        let clk_id = symtab.add_local_variable(ast_ident("clk"));
        assert_eq!(clk_id.0, 0);
        let rst_id = symtab.add_local_variable(ast_ident("rst"));
        assert_eq!(rst_id.0, 1);
        assert_eq!(
            visit_register(
                &input,
                &mut Context {
                    symtab,
                    idtracker,
                    impl_idtracker: ImplIdTracker::new(),
                    pipeline_ctx: None
                }
            ),
            Ok(expected)
        );
    }
}

#[cfg(test)]
mod item_visiting {
    use super::*;

    use ast::aparams;
    use hir::ItemList;
    use spade_ast::testutil::ast_ident;
    use spade_common::location_info::WithLocation;
    use spade_common::name::testutil::name_id;

    use pretty_assertions::assert_eq;

    #[test]
    pub fn item_entity_visiting_works() {
        let input = ast::Item::Unit(
            ast::Unit {
                name: ast_ident("test"),
                output_type: None,
                inputs: aparams![],
                body: Some(
                    ast::Expression::Block(Box::new(ast::Block {
                        statements: vec![],
                        result: ast::Expression::int_literal(0).nowhere(),
                    }))
                    .nowhere(),
                ),
                type_params: vec![],
                attributes: ast::AttributeList(vec![]),
                unit_kind: ast::UnitKind::Entity.nowhere(),
            }
            .nowhere(),
        );

        let expected = hir::Item::Unit(
            hir::Unit {
                name: hir::UnitName::FullPath(name_id(0, "test")),
                head: UnitHead {
                    name: Identifier("test".to_string()).nowhere(),
                    output_type: None,
                    inputs: hir::ParameterList(vec![]),
                    type_params: vec![],
                    unit_kind: hir::UnitKind::Entity.nowhere(),
                },
                inputs: vec![],
                body: hir::ExprKind::Block(Box::new(hir::Block {
                    statements: vec![],
                    result: hir::ExprKind::int_literal(0).idless().nowhere(),
                }))
                .idless()
                .nowhere(),
            }
            .nowhere(),
        );

        let mut symtab = SymbolTable::new();
        let idtracker = ExprIdTracker::new();
        crate::global_symbols::visit_item(&input, &mut symtab, &mut ItemList::new()).unwrap();
        assert_eq!(
            visit_item(
                &input,
                &mut Context {
                    symtab,
                    idtracker,
                    impl_idtracker: ImplIdTracker::new(),
                    pipeline_ctx: None,
                },
                &mut ItemList::new()
            ),
            Ok((vec![expected], None))
        );
    }
}

#[cfg(test)]
mod impl_blocks {
    use ast::{
        testutil::{ast_ident, ast_path},
        ImplBlock,
    };
    use hir::{symbol_table::TypeDeclKind, ItemList};
    use spade_common::name::testutil::name_id;

    use pretty_assertions::assert_eq;

    use super::*;

    #[test]
    fn anonymous_impl_blocks_work() {
        let ast_block = ImplBlock {
            r#trait: None,
            target: ast_path("a"),
            units: vec![ast::Unit {
                attributes: ast::AttributeList::empty(),
                name: ast_ident("x"),
                inputs: ParameterList::with_self(().nowhere(), vec![]).nowhere(),
                output_type: None,
                body: Some(
                    ast::Expression::Block(Box::new(ast::Block {
                        statements: vec![],
                        result: ast::Expression::int_literal(0).nowhere(),
                    }))
                    .nowhere(),
                ),
                type_params: vec![],
                unit_kind: ast::UnitKind::Function.nowhere(),
            }
            .nowhere()],
        }
        .nowhere();

        let mut items = ItemList::new();
        let mut ctx = Context {
            symtab: SymbolTable::new(),
            idtracker: ExprIdTracker::new(),
            impl_idtracker: ImplIdTracker::new(),
            pipeline_ctx: None,
        };

        // Add the type we are going to impl for. NOTE: Adding this as a j
        let target_type_name = ctx.symtab.add_type(
            ast_path("a").inner,
            TypeSymbol::Declared(vec![], TypeDeclKind::Struct { is_port: false }).nowhere(),
        );

        let new_items = visit_impl(&ast_block, &mut items, &mut ctx).unwrap();

        assert_eq!(new_items.len(), 1);

        // We'll have to cheat a bit here. Since we don't know what name will be given
        // to the entity in the impl block, we'll peek at that and use it in the expected item
        let entity_name = match new_items.first().unwrap() {
            hir::Item::Unit(e) => e.name.clone(),
            _ => panic!("Expected unit"),
        };

        let param_type_spec =
            hir::TypeSpec::Declared(target_type_name.clone().nowhere(), vec![]).nowhere();
        let hir_param_list = hir::ParameterList(vec![(ast_ident("self"), param_type_spec.clone())]);
        let expected_item = hir::Item::Unit(
            hir::Unit {
                name: entity_name.clone(),
                head: hir::UnitHead {
                    name: ast_ident("x"),
                    inputs: hir_param_list.clone(),
                    output_type: None,
                    type_params: vec![],
                    unit_kind: hir::UnitKind::Function(hir::FunctionKind::Fn).nowhere(),
                },
                inputs: vec![(name_id(2, "self"), param_type_spec)],
                body: hir::ExprKind::Block(Box::new(hir::Block {
                    statements: vec![],
                    result: hir::ExprKind::int_literal(0).with_id(1).nowhere(),
                }))
                .with_id(0)
                .nowhere(),
            }
            .nowhere(),
        );

        // Ensure that the entity is generated
        assert_eq!(&expected_item, new_items.first().unwrap());

        // Ensure that the trait is added to the item list
        assert_eq!(items.traits.len(), 1);
        let t = items.traits.iter().next().unwrap().clone();
        let trait_head = hir::UnitHead {
            name: ast_ident("x"),
            inputs: hir_param_list,
            output_type: None,
            type_params: vec![],
            unit_kind: hir::UnitKind::Function(hir::FunctionKind::Fn).nowhere(),
        };
        assert_eq!(t.1, &vec![(ast_ident("x").inner, trait_head)]);

        let trait_name = t.0;

        // Ensure that there is an impl of the trait
        let impl_note = items
            .impls
            .get(&target_type_name)
            .expect("Expected an impl list")
            .get(&trait_name)
            .expect("Expected an impl of trait");

        assert_eq!(
            impl_note,
            &hir::ImplBlock {
                fns: vec![(
                    ast_ident("x").inner,
                    (entity_name.name_id().inner.clone(), ().nowhere())
                )]
                .into_iter()
                .collect()
            }
        )
    }
}

#[cfg(test)]
mod module_visiting {
    use std::collections::HashMap;

    use super::*;

    use hir::ItemList;
    use spade_ast::testutil::ast_ident;
    use spade_common::location_info::WithLocation;
    use spade_common::name::testutil::name_id;

    use pretty_assertions::assert_eq;

    #[test]
    fn visiting_module_with_one_entity_works() {
        let input = ast::ModuleBody {
            members: vec![ast::Item::Unit(
                ast::Unit {
                    name: ast_ident("test"),
                    output_type: None,
                    inputs: ParameterList::without_self(vec![]).nowhere(),
                    body: Some(
                        ast::Expression::Block(Box::new(ast::Block {
                            statements: vec![],
                            result: ast::Expression::int_literal(0).nowhere(),
                        }))
                        .nowhere(),
                    ),
                    type_params: vec![],
                    attributes: ast::AttributeList(vec![]),
                    unit_kind: ast::UnitKind::Entity.nowhere(),
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
                        head: UnitHead {
                            name: Identifier("test".to_string()).nowhere(),
                            output_type: None,
                            inputs: hir::ParameterList(vec![]),
                            type_params: vec![],
                            unit_kind: hir::UnitKind::Entity.nowhere(),
                        },
                        inputs: vec![],
                        body: hir::ExprKind::Block(Box::new(hir::Block {
                            statements: vec![],
                            result: hir::ExprKind::int_literal(0).idless().nowhere(),
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
            traits: HashMap::new(),
            impls: HashMap::new(),
        };

        let mut symtab = SymbolTable::new();
        let idtracker = ExprIdTracker::new();
        global_symbols::gather_symbols(&input, &mut symtab, &mut ItemList::new())
            .expect("failed to collect global symbols");
        let mut item_list = ItemList::new();
        assert_eq!(
            visit_module_body(
                &mut item_list,
                &input,
                &mut Context {
                    symtab,
                    idtracker,
                    impl_idtracker: ImplIdTracker::new(),
                    pipeline_ctx: None
                }
            ),
            Ok(())
        );

        assert_eq!(item_list, expected);
    }
}
