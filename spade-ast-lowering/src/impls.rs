use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};

use itertools::{EitherOrBoth, Itertools};
use spade_ast as ast;
use spade_common::id_tracker::ImplID;
use spade_common::location_info::{Loc, WithLocation};
use spade_common::name::{Identifier, NameID, Path, PathSegment, Visibility};
use spade_diagnostics::diagnostic::Subdiagnostic;
use spade_diagnostics::{diag_bail, Diagnostic};
use spade_hir::impl_tab::type_specs_overlap;
use spade_hir::pretty_debug::PrettyDebug;
use spade_hir::symbol_table::{Thing, TypeDeclKind, TypeSymbol};
use spade_hir::{self as hir, TraitName, TypeExpression};
use spade_types::meta_types::MetaType;

use crate::error::Result;
use crate::global_symbols::{self, visit_meta_type};
use crate::{
    unit_head, visit_default_type_expression, visit_trait_spec, visit_trait_specs,
    visit_type_expression, visit_type_params, visit_type_spec, visit_unit, visit_where_clauses,
    Context, SelfContext, TypeSpecKind,
};

pub fn visit_impl(block: &Loc<ast::ImplBlock>, ctx: &mut Context) -> Result<Vec<hir::Item>> {
    ctx.symtab.new_scope();
    let result = visit_impl_inner(block, ctx);
    ctx.symtab.close_scope();
    ctx.self_ctx = SelfContext::FreeStanding;
    result
}

#[tracing::instrument(skip(ctx))]
pub fn visit_impl_inner(block: &Loc<ast::ImplBlock>, ctx: &mut Context) -> Result<Vec<hir::Item>> {
    let mut result = vec![];

    let impl_type_params = visit_type_params(&block.type_params, ctx)?;
    let target_type = visit_type_spec(&block.target, &TypeSpecKind::ImplTarget, ctx)?;
    let self_name = Identifier::intern("Self").nowhere();

    let alias_id = ctx.symtab.add_type(
        self_name,
        TypeSymbol::Declared(vec![], 0, TypeDeclKind::Alias).at_loc(&target_type),
        Visibility::Implicit.nowhere(),
        None,
    );

    ctx.item_list.types.insert(
        alias_id.clone(),
        hir::TypeDeclaration {
            name: alias_id.clone().nowhere(),
            kind: hir::TypeDeclKind::Alias(
                hir::TypeAlias {
                    type_spec: target_type.clone(),
                    wal_traceable: None,
                    documentation: String::new(),
                }
                .nowhere(),
            ),
            generic_args: vec![],
        }
        .nowhere(),
    );

    if let ast::TypeSpec::Named(path, _) = &block.target.inner {
        ctx.symtab.add_thing_with_name_id(
            alias_id.clone(),
            Thing::Alias {
                loc: block.target.loc(),
                path: path.clone(),
                in_namespace: ctx.symtab.current_namespace().clone(),
            },
            None,
            None,
        );
    }

    let (target, target_args) = get_impl_target(block, ctx)?;

    let visited_where_clauses = visit_where_clauses(&block.where_clauses, ctx)?;

    let impl_block_id = ctx.impl_idtracker.next();
    let (trait_name, trait_spec) = get_or_create_trait(block, impl_block_id, ctx)?;

    let trait_def = ctx
        .item_list
        .get_trait(&trait_name)
        .ok_or_else(|| {
            Diagnostic::bug(
                block,
                format!("Failed to find trait {} in the item list", &trait_name),
            )
        })?
        .clone();

    check_generic_params_match_trait_def(&trait_def, &trait_spec)?;

    let trait_methods = &trait_def.fns;

    let mut trait_members = vec![];
    let mut trait_impl = HashMap::default();

    ctx.self_ctx = SelfContext::ImplBlock(target_type.clone());

    let mut missing_methods = trait_methods.keys().collect::<HashSet<_>>();

    for unit in &block.units {
        let trait_method = if let Some(method) = trait_methods.get(&unit.head.name.inner) {
            method
        } else {
            return Err(Diagnostic::error(
                &unit.head.name,
                format!(
                    "`{}` is not a member of the trait `{trait_name}`",
                    unit.head.name
                ),
            )
            .primary_label(format!("Not a member of `{trait_name}`"))
            // NOTE: Safe unwrap, if we got here, we're not in an anonymous trait
            .secondary_label(
                block.r#trait.as_ref().unwrap(),
                format!("This is an impl for the trait `{trait_name}`"),
            ));
        };

        let path_segment = PathSegment::Impl(impl_block_id.0);
        let path_suffix = Some(Path(vec![path_segment.clone()]));
        ctx.symtab.add_dummy(path_segment);

        global_symbols::visit_unit(
            &path_suffix,
            unit,
            &block.type_params,
            &visited_where_clauses,
            ctx,
        )?;
        let item = visit_unit(path_suffix, unit, &block.type_params, ctx)?;

        match &item {
            hir::Item::Unit(u) => {
                let name = &unit.head.name;
                trait_members.push((name.inner.clone(), u.head.clone()));

                if let Some((_, prev)) = trait_impl.get(&name.inner) {
                    return Err(
                        Diagnostic::error(name, format!("Multiple definitions of {name}"))
                            .primary_label(format!("{name} is defined multiple times"))
                            .secondary_label(prev, "Previous definition here"),
                    );
                }

                trait_impl.insert(
                    name.inner.clone(),
                    (u.name.name_id().inner.clone(), u.loc()),
                );
            }
            hir::Item::ExternUnit(_, head) => {
                return Err(Diagnostic::error(head, "Methods cannot be `extern`")
                    .help("Consider defining a free-standing function"))
            }
        }

        let impl_method = &item.assume_unit().head;

        check_safeness_for_impl_method_and_trait_method_match(impl_method, trait_method)?;

        check_type_params_for_impl_method_and_trait_method_match(impl_method, trait_method)?;

        let trait_method_mono =
            map_trait_method_parameters(trait_method, impl_method, &trait_def, &trait_spec, ctx)?;

        check_output_type_for_impl_method_and_trait_method_matches(
            impl_method,
            &trait_method_mono,
            &target_type.inner,
            &alias_id,
        )?;

        check_params_for_impl_method_and_trait_method_match(
            impl_method,
            &trait_method_mono,
            &target_type.inner,
            &alias_id,
        )?;

        missing_methods.remove(&unit.head.name.inner);

        result.push(item);
    }

    check_no_missing_methods(block, missing_methods)?;

    let insert_result = ctx.item_list.impls.insert(
        target,
        trait_spec.inner,
        target_args,
        hir::ImplBlock {
            fns: trait_impl,
            type_params: impl_type_params,
            target: target_type,
            id: impl_block_id,
        }
        .at_loc(block),
    );

    match insert_result {
        Ok(()) => Ok(result),
        Err(diag) => Err(diag),
    }
}

pub fn get_or_create_trait(
    block: &Loc<ast::ImplBlock>,
    impl_block_id: ImplID,
    ctx: &mut Context,
) -> Result<(TraitName, Loc<hir::TraitSpec>)> {
    if let Some(trait_spec) = &block.r#trait {
        let (name, loc) = ctx.symtab.lookup_trait(&trait_spec.inner.path, false)?;
        Ok((
            TraitName::Named(trait_spec.inner.path.clone(), name.at_loc(&loc)),
            visit_trait_spec(trait_spec, &TypeSpecKind::ImplTrait, ctx)?,
        ))
    } else {
        // Create an anonymous trait which we will impl
        let trait_name = TraitName::Anonymous(impl_block_id);

        create_trait_from_unit_heads(
            trait_name.clone(),
            &block.type_params,
            &vec![],
            &block.where_clauses,
            &block
                .units
                .iter()
                .map(|u| u.head.clone().at_loc(u))
                .collect::<Vec<_>>(),
            false,
            String::new(),
            ctx,
        )?;

        let type_params = match &block.type_params {
            Some(params) => {
                let mut type_expressions = vec![];
                for param in &params.inner {
                    let (name, _) = ctx.symtab.lookup_type_symbol(
                        &param.map_ref(|_| Path::ident(param.inner.name().clone())),
                        false,
                    )?;
                    let spec = hir::TypeSpec::Generic(hir::Generic::Named(name.at_loc(param)));
                    type_expressions.push(hir::TypeExpression::TypeSpec(spec).at_loc(param));
                }
                Some(type_expressions.at_loc(params))
            }
            None => None,
        };

        let spec = hir::TraitSpec {
            name: trait_name.clone(),
            type_params,
            paren_syntax: false,
        }
        .nowhere();

        Ok((trait_name, spec))
    }
}

pub fn get_impl_target(
    block: &Loc<ast::ImplBlock>,
    ctx: &mut Context,
) -> Result<(hir::ImplTarget, Vec<hir::TypeExpression>)> {
    match &block.target.inner {
        spade_ast::TypeSpec::Array { inner, size } => Ok((
            hir::ImplTarget::Array,
            vec![
                visit_type_expression(inner, &TypeSpecKind::ImplTarget, ctx)?,
                visit_type_expression(size, &TypeSpecKind::ImplTarget, ctx)?,
            ],
        )),
        spade_ast::TypeSpec::Named(name, args) => {
            let (target_name, sym) = ctx.symtab.lookup_type_symbol(&name, true)?;

            if let TypeSymbol::GenericArg { traits: _ } | TypeSymbol::GenericMeta { .. } =
                &sym.inner
            {
                return Err(
                    Diagnostic::error(name, "Impl target must be a concrete type")
                        .primary_label("Impl on generic type")
                        .secondary_label(sym, format!("{name} defined here")),
                );
            }

            Ok((
                hir::ImplTarget::Named(target_name),
                args.as_ref()
                    .map(|t| t.inner.clone())
                    .unwrap_or_default()
                    .iter()
                    .map(|expr| visit_type_expression(expr, &TypeSpecKind::ImplTarget, ctx))
                    .collect::<Result<_>>()?,
            ))
        }
        spade_ast::TypeSpec::Inverted(inner) => Ok((
            hir::ImplTarget::Inverted,
            vec![visit_type_expression(
                inner,
                &TypeSpecKind::ImplTarget,
                ctx,
            )?],
        )),
        spade_ast::TypeSpec::Wire(inner) => Ok((
            hir::ImplTarget::Wire,
            vec![visit_type_expression(
                inner,
                &TypeSpecKind::ImplTarget,
                ctx,
            )?],
        )),
        ast::TypeSpec::Impl(_) => {
            return Err(
                Diagnostic::error(&block.target, "Impls target cannot be impl type")
                    .primary_label("Impl target cannot be impl type"),
            );
        }
        spade_ast::TypeSpec::Wildcard => {
            return Err(
                Diagnostic::error(&block.target, "Impl target cannot be wildcard")
                    .primary_label("Impl target cannot be wildcard"),
            );
        }
        ast::TypeSpec::Tuple(_) => {
            return Err(Diagnostic::error(
                &block.target,
                "Impls on tuples is currently unsupported",
            )
            .primary_label("Impl target cannot be a tuple"));
        }
    }
}

pub fn create_trait_from_unit_heads(
    name: TraitName,
    type_params: &Option<Loc<Vec<Loc<ast::TypeParam>>>>,
    subtraits: &Vec<Loc<ast::TraitSpec>>,
    where_clauses: &[ast::WhereClause],
    heads: &[Loc<ast::UnitHead>],
    paren_sugar: bool,
    documentation: String,
    ctx: &mut Context,
) -> Result<()> {
    ctx.symtab.new_scope();

    ctx.self_ctx = SelfContext::TraitDefinition(name.clone());

    let visited_type_params = if let Some(params) = type_params {
        Some(params.try_map_ref(|params| {
            params
                .iter()
                .map(|param| {
                    param.try_map_ref(|tp| {
                        let ident = tp.name();
                        let type_symbol = match tp {
                            ast::TypeParam::TypeName {
                                name,
                                traits,
                                default: _,
                            } => TypeSymbol::GenericArg {
                                traits: visit_trait_specs(&traits, &TypeSpecKind::TraitBound, ctx)?,
                            }
                            .at_loc(name),
                            ast::TypeParam::TypeWithMeta {
                                meta,
                                name,
                                default: _,
                            } => TypeSymbol::GenericMeta(visit_meta_type(meta)?).at_loc(name),
                        };
                        let name_id = ctx.symtab.add_type(
                            ident.clone(),
                            type_symbol,
                            Visibility::Implicit.nowhere(),
                            None,
                        );
                        Ok(match tp {
                            ast::TypeParam::TypeName {
                                name: _,
                                traits,
                                default,
                            } => hir::TypeParam {
                                name: hir::Generic::Named(name_id.at_loc(&ident)),
                                trait_bounds: visit_trait_specs(
                                    traits,
                                    &TypeSpecKind::TraitBound,
                                    ctx,
                                )?,
                                meta: MetaType::Type,
                                default: visit_default_type_expression(default, ctx)?.map(Box::new),
                            },
                            ast::TypeParam::TypeWithMeta {
                                meta,
                                name: _,
                                default,
                            } => hir::TypeParam {
                                name: hir::Generic::Named(name_id.at_loc(&ident)),
                                trait_bounds: vec![],
                                meta: visit_meta_type(meta)?,
                                default: visit_default_type_expression(default, ctx)?.map(Box::new),
                            },
                        })
                    })
                })
                .collect::<Result<Vec<_>>>()
        })?)
    } else {
        None
    };

    let subtraits = visit_trait_specs(subtraits, &TypeSpecKind::ImplTarget, ctx)?;
    let visited_where_clauses = visit_where_clauses(where_clauses, ctx)?;

    let trait_members = heads
        .iter()
        .map(|head| {
            Ok((
                head.name.inner.clone(),
                unit_head(head, type_params, &visited_where_clauses, ctx, None)?.at_loc(head),
            ))
        })
        .collect::<Result<Vec<_>>>()?;

    let mut pending_names = subtraits
        .iter()
        .map(|s| s.name.clone())
        .collect::<HashSet<_>>();

    let mut visited_edges = subtraits
        .iter()
        .map(|s| (s.name.clone(), name.clone().at_loc(s)))
        .collect::<HashMap<_, _>>();

    while let Some(pending_name) = pending_names.extract_if(|_| true).next() {
        if pending_name == name {
            let mut diag = Diagnostic::error(
                name.name_loc().unwrap(),
                format!("Cycle caused by supertrait of `{name}`"),
            );

            let mut current_name = visited_edges.get(&name).unwrap();

            while current_name.inner != name {
                diag.push_subdiagnostic(Subdiagnostic::span_note(
                    current_name,
                    format!("... which is a supertrait of `{current_name}`"),
                ));
                current_name = visited_edges.get(&current_name).unwrap();
            }

            diag.push_subdiagnostic(Subdiagnostic::span_note(
                current_name,
                format!("... which is a supertrait of `{name}`, completing the cycle"),
            ));

            return Err(diag);
        }

        let Some(subtrait_def) = ctx.item_list.get_trait(&pending_name) else {
            continue;
        };

        for subsubtrait in &subtrait_def.subtraits {
            if !visited_edges.contains_key(&subsubtrait.name) {
                pending_names.insert(subsubtrait.name.clone());
                visited_edges.insert(
                    subsubtrait.name.clone(),
                    pending_name.clone().at_loc(subsubtrait),
                );
            }
        }
    }

    // Add the trait to the trait list
    ctx.item_list.add_trait(
        name,
        visited_type_params,
        subtraits,
        trait_members,
        paren_sugar,
        documentation,
    )?;

    ctx.symtab.close_scope();
    Ok(())
}

fn check_generic_params_match_trait_def(
    trait_def: &hir::TraitDef,
    trait_spec: &Loc<hir::TraitSpec>,
) -> Result<()> {
    if let Some(generic_params) = &trait_def.type_params {
        let min_required_params = generic_params
            .inner
            .iter()
            .take_while(|p| p.default.is_none())
            .count();

        if let hir::TraitSpec {
            type_params: Some(generic_spec),
            ..
        } = &trait_spec.inner
        {
            if generic_spec.len() >= min_required_params
                && generic_spec.len() <= generic_params.len()
            {
                Ok(())
            } else {
                let mut diag =
                    Diagnostic::error(generic_spec, "Wrong number of generic type parameters")
                        .secondary_label(
                            ().between_locs(
                                &generic_params[0],
                                &generic_params[generic_params.len() - 1],
                            ),
                            format!(
                                "Because this has {} type parameter{}",
                                generic_params.len(),
                                if generic_params.len() != 1 { "s" } else { "" }
                            ),
                        );
                if min_required_params == generic_params.len() {
                    diag = diag.primary_label(format!(
                        "Expected {} type parameter{}",
                        generic_params.len(),
                        if generic_params.len() != 1 { "s" } else { "" }
                    ));
                } else {
                    diag = diag.primary_label(format!(
                        "Expected between {} and {} type parameter{}",
                        min_required_params,
                        generic_params.len(),
                        if generic_params.len() != 1 { "s" } else { "" }
                    ));
                }
                Err(diag)
            }
        } else {
            if min_required_params == 0 {
                Ok(())
            } else {
                match &trait_spec.name {
                    TraitName::Named(path, name) => Err(Diagnostic::error(
                        trait_spec,
                        format!("Raw use of generic trait {path}"),
                    )
                    .primary_label(format!(
                        "Trait {path} used without specifying type parameters"
                    ))
                    .secondary_label(name, format!("Trait {path} defined here"))),
                    TraitName::Anonymous(_) => Err(Diagnostic::bug(
                        ().nowhere(),
                        "Generic anonymous trait found, which should not be possible here",
                    )),
                }
            }
        }
    } else if let hir::TraitSpec {
        name,
        type_params: Some(generic_spec),
        paren_syntax: _,
    } = &trait_spec.inner
    {
        match name {
            TraitName::Named(path, name) => {
                Err(Diagnostic::error(
                    generic_spec,
                    "Generic type parameters specified for non-generic trait",
                )
                .primary_label(
                    "Generic type parameters specified here",
                )
                .secondary_label(
                    name,
                    format!("Trait {} is not generic", path),
                ))
            },
            TraitName::Anonymous(_) => Err(Diagnostic::bug(
                generic_spec,
                "Generic type parameters specified for anonymous trait, which should not be possible",
            ))
        }
    } else {
        Ok(())
    }
}

fn check_no_missing_methods(
    block: &Loc<ast::ImplBlock>,
    missing_methods: HashSet<&Identifier>,
) -> Result<()> {
    if !missing_methods.is_empty() {
        // Sort for deterministic errors
        let mut missing_list = missing_methods.into_iter().collect::<Vec<_>>();
        missing_list.sort_by_key(|ident| ident.as_str());

        let as_str = match missing_list.as_slice() {
            [] => unreachable!(),
            [single] => format!("{single}"),
            other => {
                if other.len() <= 3 {
                    format!(
                        "{} and {}",
                        other[0..other.len() - 1]
                            .iter()
                            .map(|id| id.as_str())
                            .join(", "),
                        other[other.len() - 1].as_str()
                    )
                } else {
                    format!(
                        "{} and {} more",
                        other[0..3].iter().map(|id| id.as_str()).join(", "),
                        other.len() - 3
                    )
                }
            }
        };

        Err(
            Diagnostic::error(block, format!("Missing methods {as_str}"))
                .primary_label(format!("Missing definition of {as_str} in this impl block")),
        )
    } else {
        Ok(())
    }
}

fn check_safeness_for_impl_method_and_trait_method_match(
    impl_method: &hir::UnitHead,
    trait_method: &hir::UnitHead,
) -> Result<()> {
    let diag = || {
        Diagnostic::error(
            &impl_method.name,
            "Safeness of impl method does not match that of trait definition",
        )
    };

    match (impl_method.unsafe_marker, trait_method.unsafe_marker) {
        (Some(_), Some(_)) | (None, None) => Ok(()),
        (None, Some(def)) => Err(diag()
            .primary_label("This impl isn't marked as unsafe")
            .secondary_label(def, "But the trait definition is")
            .span_suggest_insert_before("Add unsafe here", &impl_method.unit_kind, "unsafe ")),
        (Some(loc), None) => Err(diag()
            .primary_label("This impl is marked as unsafe")
            .secondary_label(&trait_method.name, "But the trait definition isn't")
            .span_suggest_remove("Remove unsafe here", loc)),
    }
}

fn check_type_params_for_impl_method_and_trait_method_match(
    impl_method: &hir::UnitHead,
    trait_method: &hir::UnitHead,
) -> Result<()> {
    if impl_method.unit_type_params.len() != trait_method.unit_type_params.len() {
        if impl_method.unit_type_params.is_empty() {
            Err(Diagnostic::error(
                &impl_method.name,
                format!(
                    "Missing type parameter{} on impl of generic method",
                    if trait_method.unit_type_params.len() != 1 {
                        "s"
                    } else {
                        ""
                    },
                ),
            )
            .primary_label(format!(
                "Expected {} type parameter{}",
                trait_method.unit_type_params.len(),
                if trait_method.unit_type_params.len() != 1 {
                    "s"
                } else {
                    ""
                },
            ))
            .secondary_label(
                ().between_locs(
                    trait_method.unit_type_params.first().unwrap(),
                    trait_method.unit_type_params.last().unwrap(),
                ),
                format!(
                    "Because this has {} type parameter{}",
                    trait_method.unit_type_params.len(),
                    if trait_method.unit_type_params.len() != 1 {
                        "s"
                    } else {
                        ""
                    },
                ),
            ))
        } else if trait_method.unit_type_params.is_empty() {
            Err(Diagnostic::error(
                ().between_locs(
                    impl_method.unit_type_params.first().unwrap(),
                    impl_method.unit_type_params.last().unwrap(),
                ),
                format!(
                    "Unexpected type parameter{} on impl of non-generic method",
                    if impl_method.unit_type_params.len() != 1 {
                        "s"
                    } else {
                        ""
                    },
                ),
            )
            .primary_label(format!(
                "Type parameter{} specified here",
                if impl_method.unit_type_params.len() != 1 {
                    "s"
                } else {
                    ""
                },
            ))
            .secondary_label(&trait_method.name, "But this is not generic"))
        } else {
            Err(Diagnostic::error(
                ().between_locs(
                    impl_method.unit_type_params.first().unwrap(),
                    impl_method.unit_type_params.last().unwrap(),
                ),
                "Wrong number of generic type parameters",
            )
            .primary_label(format!(
                "Expected {} type parameter{}",
                trait_method.unit_type_params.len(),
                if trait_method.unit_type_params.len() != 1 {
                    "s"
                } else {
                    ""
                },
            ))
            .secondary_label(
                ().between_locs(
                    trait_method.unit_type_params.first().unwrap(),
                    trait_method.unit_type_params.last().unwrap(),
                ),
                format!(
                    "Because this has {} type parameter{}",
                    trait_method.unit_type_params.len(),
                    if trait_method.unit_type_params.len() != 1 {
                        "s"
                    } else {
                        ""
                    },
                ),
            ))
        }
    } else {
        Ok(())
    }
}

fn resolve_trait_self(
    trait_ty: hir::TypeSpec,
    impl_target_type: hir::TypeSpec,
    self_id: &NameID,
) -> hir::TypeSpec {
    let resolve_in_expr =
        |e: Loc<TypeExpression>| {
            let (e, loc) = e.split_loc();
            match e {
                hir::TypeExpression::TypeSpec(ts) => hir::TypeExpression::TypeSpec(
                    resolve_trait_self(ts, impl_target_type.clone(), self_id),
                )
                .at_loc(&loc),
                hir::TypeExpression::Bool(_) => e.at_loc(&loc),
                hir::TypeExpression::Integer(_) => e.at_loc(&loc),
                hir::TypeExpression::String(_) => e.at_loc(&loc),
                // There is no way for `Self` to be used inside a const generic block
                hir::TypeExpression::ConstGeneric(_) => e.at_loc(&loc),
            }
        };
    match trait_ty {
        hir::TypeSpec::Tuple(inner) => hir::TypeSpec::Tuple(
            inner
                .iter()
                .map(|inner| {
                    resolve_trait_self(inner.inner.clone(), impl_target_type.clone(), self_id)
                        .at_loc(&inner)
                })
                .collect(),
        ),
        hir::TypeSpec::Array { inner, size } => {
            let (inner, loc) = inner.split_loc();

            hir::TypeSpec::Array {
                inner: Box::new(
                    resolve_trait_self(inner, impl_target_type.clone(), self_id).at_loc(&loc),
                ),
                size: Box::new(resolve_in_expr(*size)),
            }
        }
        hir::TypeSpec::Inverted(inner) => {
            let loc = inner.loc();
            let new_inner = resolve_trait_self(inner.inner, impl_target_type, self_id).at_loc(&loc);
            hir::TypeSpec::Inverted(Box::new(new_inner))
        }
        hir::TypeSpec::Wire(inner) => {
            let loc = inner.loc();
            let new_inner = resolve_trait_self(inner.inner, impl_target_type, self_id).at_loc(&loc);
            hir::TypeSpec::Wire(Box::new(new_inner))
        }
        hir::TypeSpec::TraitSelf(_) => impl_target_type,
        hir::TypeSpec::Declared(name_id, _) if &name_id.inner == self_id => impl_target_type,
        hir::TypeSpec::Declared(name, exprs) => {
            hir::TypeSpec::Declared(name, exprs.into_iter().map(resolve_in_expr).collect())
        }
        hir::TypeSpec::Generic(_) | hir::TypeSpec::Wildcard(_) => trait_ty,
    }
}

fn check_output_type_for_impl_method_and_trait_method_matches(
    impl_method: &hir::UnitHead,
    trait_method: &hir::UnitHead,
    target_type: &hir::TypeSpec,
    self_id: &NameID,
) -> Result<()> {
    let impl_output = impl_method.output_type().inner;
    let impl_output = resolve_trait_self(impl_output.clone(), target_type.clone(), self_id);

    let trait_output = trait_method.output_type().inner;
    let trait_output = resolve_trait_self(trait_output.clone(), target_type.clone(), self_id);

    if impl_output != trait_output {
        return Err(Diagnostic::error(
            impl_method.output_type(),
            "Return type does not match trait",
        )
        .primary_label(format!("Expected {}", trait_method.output_type()))
        .secondary_label(trait_method.output_type(), "To match the trait"));
    }
    Ok(())
}

fn check_params_for_impl_method_and_trait_method_match(
    impl_method: &hir::UnitHead,
    trait_method: &hir::UnitHead,
    impl_target_type: &hir::TypeSpec,
    self_id: &NameID,
) -> Result<()> {
    for (i, pair) in impl_method
        .inputs
        .0
        .iter()
        .zip_longest(trait_method.inputs.0.iter())
        .enumerate()
    {
        match pair {
            EitherOrBoth::Both(
                hir::Parameter {
                    name: i_name,
                    ty: i_spec,
                    no_mangle: _,
                    field_translator: _,
                },
                hir::Parameter {
                    name: t_name,
                    ty: t_spec,
                    no_mangle: _,
                    field_translator: _,
                },
            ) => {
                if i_name != t_name {
                    return Err(Diagnostic::error(i_name, "Argument name mismatch")
                        .primary_label(format!("Expected `{t_name}`"))
                        .secondary_label(
                            t_name,
                            format!("Because argument {i} is named `{t_name}` in the trait"),
                        ));
                }

                let trait_type =
                    resolve_trait_self(t_spec.inner.clone(), impl_target_type.clone(), self_id);
                let impl_type =
                    resolve_trait_self(i_spec.inner.clone(), impl_target_type.clone(), self_id);
                if trait_type != impl_type {
                    return Err(Diagnostic::error(i_spec, "Argument type mismatch")
                        .primary_label(format!("Expected {t_spec}"))
                        .secondary_label(
                            t_spec,
                            format!("Because of the type of {t_name} in the trait"),
                        ));
                }
            }
            EitherOrBoth::Left(hir::Parameter {
                name,
                ty: _,
                no_mangle: _,
                field_translator: _,
            }) => {
                return Err(
                    Diagnostic::error(name, "Trait method does not have this argument")
                        .primary_label("Extra argument")
                        .secondary_label(&trait_method.name, "Method defined here"),
                )
            }
            EitherOrBoth::Right(hir::Parameter {
                name,
                ty: _,
                no_mangle: _,
                field_translator: _,
            }) => {
                return Err(Diagnostic::error(
                    &impl_method.inputs,
                    format!("Missing argument {}", name),
                )
                .primary_label(format!("Missing argument {}", name))
                .secondary_label(name, "The trait method has this argument"));
            }
        }
    }
    Ok(())
}

/// Replaces the generic type parameters in a trait method with the corresponding generic type parameters of the impl block.
/// This is used to check if the method signature of the impl block matches the method signature of the trait.
/// e.g. `fn foo<T>(self, a: T) -> T` in the trait would be replaced with `fn foo<U>(self, a: U) -> U` in the impl block.
fn map_trait_method_parameters(
    trait_method: &hir::UnitHead,
    impl_method: &hir::UnitHead,
    trait_def: &hir::TraitDef,
    trait_spec: &hir::TraitSpec,
    ctx: &mut Context,
) -> Result<hir::UnitHead> {
    let trait_type_params = trait_def
        .type_params
        .as_ref()
        .map_or(vec![], |params| params.inner.clone());

    let trait_method_type_params = &trait_method
        .unit_type_params
        .iter()
        .chain(&trait_method.hidden_type_params)
        .cloned()
        .collect_vec();

    let impl_type_params = trait_spec
        .type_params
        .as_ref()
        .map_or(vec![], |params| params.inner.clone());

    let impl_or_default_type_params = impl_type_params
        .into_iter()
        .zip_longest(&trait_type_params)
        .map(|elem| match elem {
            EitherOrBoth::Both(expr, _) => Ok(expr),
            EitherOrBoth::Right(param) => Ok(*param.default.clone().unwrap()),
            EitherOrBoth::Left(expr) => {
                diag_bail!(
                    expr,
                    "Excess type parameter slipped through trait parameter checks"
                )
            }
        })
        .collect::<Result<Vec<_>>>()?;

    let impl_method_type_params = &impl_method
        .unit_type_params
        .iter()
        .chain(&impl_method.hidden_type_params)
        .map(|param| {
            let spec = hir::TypeSpec::Generic(param.name.clone());
            hir::TypeExpression::TypeSpec(spec).at_loc(param)
        })
        .collect_vec();

    let inputs = trait_method.inputs.try_map_ref(|param_list| {
        param_list
            .0
            .iter()
            .map(|param| {
                map_type_spec_to_trait(
                    &param.ty,
                    trait_type_params.as_slice(),
                    trait_method_type_params.as_slice(),
                    impl_or_default_type_params.as_slice(),
                    impl_method_type_params.as_slice(),
                    ctx,
                )
                .map(|ty| hir::Parameter {
                    name: param.name.clone(),
                    ty,
                    no_mangle: param.no_mangle,
                    field_translator: None,
                })
            })
            .collect::<Result<_>>()
            .map(|params| hir::ParameterList(params))
    })?;

    let output_type = if let Some(ty) = trait_method.output_type.as_ref() {
        Some(map_type_spec_to_trait(
            &ty,
            trait_type_params.as_slice(),
            trait_method_type_params.as_slice(),
            impl_or_default_type_params.as_slice(),
            impl_method_type_params.as_slice(),
            ctx,
        )?)
    } else {
        None
    };

    Ok(hir::UnitHead {
        inputs,
        output_type,
        ..trait_method.clone()
    })
}

fn map_const_generic_to_trait(
    cg: &Loc<hir::ConstGeneric>,
    trait_type_params: &[Loc<hir::TypeParam>],
    trait_method_type_params: &[Loc<hir::TypeParam>],
    impl_type_params: &[Loc<hir::TypeExpression>],
    impl_method_type_params: &[Loc<hir::TypeExpression>],
    ctx: &mut Context,
) -> Result<Loc<hir::ConstGeneric>> {
    let mut map_boilerplate = |cg| {
        Result::Ok(Box::new(map_const_generic_to_trait(
            cg,
            trait_type_params,
            trait_method_type_params,
            impl_type_params,
            impl_method_type_params,
            ctx,
        )?))
    };

    match &cg.inner {
        hir::ConstGeneric::Name(name) => {
            let param_idx = trait_type_params
                .iter()
                .find_position(|tp| tp.name_id() == Some(name))
                .map(|(idx, _)| idx);

            if let Some(param_idx) = param_idx {
                impl_type_params[param_idx].try_map_ref(|te| match &te {
                    hir::TypeExpression::TypeSpec(hir::TypeSpec::Generic(g)) => match g {
                        hir::Generic::Named(name) => Ok(hir::ConstGeneric::Name(name.clone())),
                        hir::Generic::Hidden(_) => Err(Diagnostic::bug(
                            cg,
                            "Cannot substitute hidden type generic into const generic",
                        )),
                    },
                    hir::TypeExpression::TypeSpec(_) => Err(Diagnostic::bug(
                        cg,
                        "Cannot substitute type spec into const generic",
                    )),
                    hir::TypeExpression::Bool(b) => Ok(hir::ConstGeneric::Bool(*b)),
                    hir::TypeExpression::Integer(i) => Ok(hir::ConstGeneric::Int(i.clone())),
                    hir::TypeExpression::String(s) => Ok(hir::ConstGeneric::Str(s.clone())),
                    hir::TypeExpression::ConstGeneric(cg) => Ok(cg.inner.clone()),
                })
            } else {
                let param_idx = trait_method_type_params
                    .iter()
                    .find_position(|tp| tp.name_id() == Some(name))
                    .map(|(idx, _)| idx);

                if let Some(param_idx) = param_idx {
                    impl_method_type_params[param_idx].try_map_ref(|te| match &te {
                        hir::TypeExpression::TypeSpec(hir::TypeSpec::Generic(g)) => match g {
                            hir::Generic::Named(name) => Ok(hir::ConstGeneric::Name(name.clone())),
                            hir::Generic::Hidden(_) => Err(Diagnostic::bug(
                                cg,
                                "Cannot substitute hidden type generic into const generic",
                            )),
                        },
                        hir::TypeExpression::TypeSpec(_) => Err(Diagnostic::bug(
                            cg,
                            "Cannot substitute type spec into const generic",
                        )),
                        hir::TypeExpression::Bool(b) => Ok(hir::ConstGeneric::Bool(*b)),
                        hir::TypeExpression::Integer(i) => Ok(hir::ConstGeneric::Int(i.clone())),
                        hir::TypeExpression::String(s) => Ok(hir::ConstGeneric::Str(s.clone())),
                        hir::TypeExpression::ConstGeneric(cg) => Ok(cg.inner.clone()),
                    })
                } else {
                    Err(Diagnostic::bug(
                        name,
                        format!(
                            "Could not find type parameter {} in trait or trait method.",
                            name.inner
                        ),
                    ))
                }
            }
        }

        hir::ConstGeneric::Add(lhs, rhs) => {
            Ok(hir::ConstGeneric::Add(map_boilerplate(lhs)?, map_boilerplate(rhs)?).at_loc(&cg))
        }
        hir::ConstGeneric::Sub(lhs, rhs) => {
            Ok(hir::ConstGeneric::Sub(map_boilerplate(lhs)?, map_boilerplate(rhs)?).at_loc(&cg))
        }
        hir::ConstGeneric::Mul(lhs, rhs) => {
            Ok(hir::ConstGeneric::Mul(map_boilerplate(lhs)?, map_boilerplate(rhs)?).at_loc(&cg))
        }
        hir::ConstGeneric::Div(lhs, rhs) => {
            Ok(hir::ConstGeneric::Div(map_boilerplate(lhs)?, map_boilerplate(rhs)?).at_loc(&cg))
        }
        hir::ConstGeneric::Mod(lhs, rhs) => {
            Ok(hir::ConstGeneric::Mod(map_boilerplate(lhs)?, map_boilerplate(rhs)?).at_loc(&cg))
        }
        hir::ConstGeneric::UintBitsToFit(inner) => {
            Ok(hir::ConstGeneric::UintBitsToFit(map_boilerplate(inner)?).at_loc(&cg))
        }
        hir::ConstGeneric::Eq(lhs, rhs) => {
            Ok(hir::ConstGeneric::Eq(map_boilerplate(lhs)?, map_boilerplate(rhs)?).at_loc(&cg))
        }
        hir::ConstGeneric::NotEq(lhs, rhs) => {
            Ok(hir::ConstGeneric::NotEq(map_boilerplate(lhs)?, map_boilerplate(rhs)?).at_loc(&cg))
        }
        hir::ConstGeneric::LogicalNot(inner) => {
            Ok(hir::ConstGeneric::LogicalNot(map_boilerplate(inner)?).at_loc(&cg))
        }
        hir::ConstGeneric::LogicalAnd(lhs, rhs) => Ok(hir::ConstGeneric::LogicalAnd(
            map_boilerplate(lhs)?,
            map_boilerplate(rhs)?,
        )
        .at_loc(&cg)),
        hir::ConstGeneric::LogicalOr(lhs, rhs) => Ok(hir::ConstGeneric::LogicalOr(
            map_boilerplate(lhs)?,
            map_boilerplate(rhs)?,
        )
        .at_loc(&cg)),
        hir::ConstGeneric::LogicalXor(lhs, rhs) => Ok(hir::ConstGeneric::LogicalXor(
            map_boilerplate(lhs)?,
            map_boilerplate(rhs)?,
        )
        .at_loc(&cg)),
        hir::ConstGeneric::Bool(_) => Ok(cg.clone()),
        hir::ConstGeneric::Int(_) => Ok(cg.clone()),
        hir::ConstGeneric::Str(_) => Ok(cg.clone()),
    }
}

fn map_type_expr_to_trait(
    te: &Loc<hir::TypeExpression>,
    trait_type_params: &[Loc<hir::TypeParam>],
    trait_method_type_params: &[Loc<hir::TypeParam>],
    impl_type_params: &[Loc<hir::TypeExpression>],
    impl_method_type_params: &[Loc<hir::TypeExpression>],
    ctx: &mut Context,
) -> Result<Loc<hir::TypeExpression>> {
    match &te.inner {
        hir::TypeExpression::Bool(_) => Ok(te.clone()),
        hir::TypeExpression::Integer(_) => Ok(te.clone()),
        hir::TypeExpression::String(_) => Ok(te.clone()),
        hir::TypeExpression::TypeSpec(s) => {
            let (inner, loc) = map_type_spec_to_trait(
                &s.clone().at_loc(te),
                trait_type_params,
                trait_method_type_params,
                impl_type_params,
                impl_method_type_params,
                ctx,
            )?
            .split_loc();
            Ok(hir::TypeExpression::TypeSpec(inner).at_loc(&loc))
        }
        hir::TypeExpression::ConstGeneric(cg) => Ok(hir::TypeExpression::ConstGeneric(
            map_const_generic_to_trait(
                cg,
                trait_type_params,
                trait_method_type_params,
                impl_type_params,
                impl_method_type_params,
                ctx,
            )?,
        )
        .at_loc(&te)),
    }
}

fn map_type_spec_to_trait(
    ty: &Loc<hir::TypeSpec>,
    trait_type_params: &[Loc<hir::TypeParam>],
    trait_method_type_params: &[Loc<hir::TypeParam>],
    impl_type_params: &[Loc<hir::TypeExpression>],
    impl_method_type_params: &[Loc<hir::TypeExpression>],
    ctx: &mut Context,
) -> Result<Loc<hir::TypeSpec>> {
    match &ty.inner {
        hir::TypeSpec::Declared(name, te) => {
            let mono_tes = te
                .iter()
                .map(|te| {
                    map_type_expr_to_trait(
                        te,
                        trait_type_params,
                        trait_method_type_params,
                        impl_type_params,
                        impl_method_type_params,
                        ctx,
                    )
                })
                .collect::<Result<_>>()?;

            Ok(hir::TypeSpec::Declared(name.clone(), mono_tes).at_loc(ty))
        }
        hir::TypeSpec::Generic(name) => {
            let param_idx = trait_type_params
                .iter()
                .find_position(|tp| &tp.name == name)
                .map(|(idx, _)| idx);

            if let Some(param_idx) = param_idx {
                impl_type_params[param_idx].try_map_ref(|te| match &te {
                    hir::TypeExpression::TypeSpec(spec) => Ok(spec.clone()),
                    hir::TypeExpression::Bool(_) => Err(Diagnostic::bug(
                        &impl_type_params[param_idx],
                        "Expected a TypeExpression::TypeSpec, found TypeExpression::Bool",
                    )),
                    hir::TypeExpression::Integer(_) => Err(Diagnostic::bug(
                        &impl_type_params[param_idx],
                        "Expected a TypeExpression::TypeSpec, found TypeExpression::Integer",
                    )),
                    hir::TypeExpression::String(_) => Err(Diagnostic::bug(
                        &impl_type_params[param_idx],
                        "Expected a TypeExpression::TypeSpec, found TypeExpression::String",
                    )),
                    hir::TypeExpression::ConstGeneric(_) => {
                        diag_bail!(ty, "Const generic in impl head")
                    }
                })
            } else {
                let param_idx = trait_method_type_params
                    .iter()
                    .find_position(|tp| &tp.name == name)
                    .map(|(idx, _)| idx);

                if let Some(param_idx) = param_idx {
                    impl_method_type_params[param_idx].try_map_ref(|te| match &te {
                        hir::TypeExpression::TypeSpec(spec) => Ok(spec.clone()),
                        hir::TypeExpression::Bool(_) => Err(Diagnostic::bug(
                            &impl_type_params[param_idx],
                            "Expected a TypeExpression::TypeSpec, found TypeExpression::Bool",
                        )),
                        hir::TypeExpression::Integer(_) => Err(Diagnostic::bug(
                            &impl_method_type_params[param_idx],
                            "Expected a TypeExpression::TypeSpec, found TypeExpression::Integer",
                        )),
                        hir::TypeExpression::String(_) => Err(Diagnostic::bug(
                            &impl_method_type_params[param_idx],
                            "Expected a TypeExpression::TypeSpec, found TypeExpression::String",
                        )),
                        hir::TypeExpression::ConstGeneric(_) => {
                            diag_bail!(ty, "Const generic in impl head")
                        }
                    })
                } else {
                    Err(Diagnostic::bug(
                        name.loc(),
                        format!(
                            "Could not find type parameter {} in trait or trait method.",
                            name.pretty_debug()
                        ),
                    ))
                }
            }
        }
        hir::TypeSpec::Tuple(specs) => {
            let mono_elems = specs
                .iter()
                .map(|spec| {
                    map_type_spec_to_trait(
                        spec,
                        trait_type_params,
                        trait_method_type_params,
                        impl_type_params,
                        impl_method_type_params,
                        ctx,
                    )
                })
                .collect::<Result<_>>()?;

            Ok(hir::TypeSpec::Tuple(mono_elems).at_loc(ty))
        }
        hir::TypeSpec::Array { inner, size } => {
            let mono_inner = map_type_spec_to_trait(
                inner,
                trait_type_params,
                trait_method_type_params,
                impl_type_params,
                impl_method_type_params,
                ctx,
            )?;
            let mono_size = map_type_expr_to_trait(
                size,
                trait_type_params,
                trait_method_type_params,
                impl_type_params,
                impl_method_type_params,
                ctx,
            )?;

            Ok(hir::TypeSpec::Array {
                inner: Box::from(mono_inner),
                size: Box::from(mono_size),
            }
            .at_loc(ty))
        }
        hir::TypeSpec::Inverted(inner) => {
            let mono_inner = map_type_spec_to_trait(
                inner,
                trait_type_params,
                trait_method_type_params,
                impl_type_params,
                impl_method_type_params,
                ctx,
            )?;
            Ok(hir::TypeSpec::Inverted(Box::from(mono_inner)).at_loc(ty))
        }
        hir::TypeSpec::Wire(inner) => {
            let mono_inner = map_type_spec_to_trait(
                inner,
                trait_type_params,
                trait_method_type_params,
                impl_type_params,
                impl_method_type_params,
                ctx,
            )?;
            Ok(hir::TypeSpec::Wire(Box::from(mono_inner)).at_loc(ty))
        }
        _ => Ok(ty.clone()),
    }
}

/// Ensures that there are no functions in anonymous trait impls that have conflicting
/// names
#[tracing::instrument(skip(item_list))]
pub fn ensure_unique_anonymous_traits(item_list: &mut hir::ItemList) -> Vec<Diagnostic> {
    let mut diags = vec![];
    for (_impl_target, impls) in item_list.impls.inner.iter_mut() {
        let mut set: HashMap<Identifier, Vec<(Loc<()>, hir::TypeSpec)>> = HashMap::default();

        for block in impls
            .iter_mut()
            .filter(|(trait_name, _)| trait_name.is_anonymous())
            .flat_map(|(_, impls)| impls.values_mut())
            .flat_map(|impls| impls.iter_mut())
            .map(|(_, block)| block)
            .sorted_by_key(|block| block.span)
        {
            let target = block.target.clone();
            block.fns.retain(|f, (_f_nameid, f_loc)| {
                let specs = set.entry(f.clone()).or_default();
                if let Some((prev, _)) = specs
                    .iter()
                    .find(|(_, spec)| type_specs_overlap(&target.inner, spec))
                {
                    diags.push(
                        Diagnostic::error(
                            *f_loc,
                            format!("{} already has a method named {f}", target),
                        )
                        .primary_label("Duplicate method")
                        .secondary_label(prev.loc(), "Previous definition here"),
                    );
                    false
                } else {
                    specs.push((f_loc.loc(), target.inner.clone()));
                    true
                }
            });
        }
    }
    diags
}
