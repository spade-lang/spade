use std::collections::{HashMap, HashSet};

use itertools::{EitherOrBoth, Itertools};
use spade_ast as ast;
use spade_common::id_tracker::ImplID;
use spade_common::location_info::{Loc, WithLocation};
use spade_common::name::{Identifier, Path};
use spade_diagnostics::{diag_bail, Diagnostic};
use spade_hir::impl_tab::type_specs_overlap;
use spade_hir::symbol_table::TypeSymbol;
use spade_hir::{self as hir, TraitName};
use spade_types::meta_types::MetaType;

use crate::error::Result;
use crate::global_symbols::{self, visit_meta_type};
use crate::{
    types::IsPort, unit_head, visit_trait_spec, visit_type_expression, visit_type_param,
    visit_type_spec, visit_unit, visit_where_clauses, Context, SelfContext, TypeSpecKind,
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

    let mut impl_type_params = vec![];

    if let Some(type_params) = &block.type_params {
        for param in type_params.inner.iter() {
            let param = param.try_map_ref(|p| visit_type_param(p, ctx))?;
            impl_type_params.push(param);
        }
    }

    let target_type = visit_type_spec(&block.target, &TypeSpecKind::ImplTarget, ctx)?;

    let self_path = Path::from_strs(&["Self"]);
    ctx.symtab.add_type(
        self_path,
        TypeSymbol::Alias(
            hir::TypeExpression::TypeSpec(target_type.inner.clone()).at_loc(&block.target),
        )
        .at_loc(&block.target),
    );

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
    let mut trait_impl = HashMap::new();

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

        check_is_no_function_on_port_type(unit, &target_type, ctx)?;

        let path_suffix = Some(Path(vec![
            Identifier(format!("impl_{}", impl_block_id.0)).nowhere()
        ]));

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

        check_type_params_for_impl_method_and_trait_method_match(impl_method, trait_method)?;

        let trait_method_mono =
            map_trait_method_parameters(trait_method, impl_method, &trait_def, &trait_spec, ctx)?;

        check_output_type_for_impl_method_and_trait_method_matches(
            impl_method,
            &trait_method_mono,
            &target_type.inner,
        )?;

        check_params_for_impl_method_and_trait_method_match(
            impl_method,
            &trait_method_mono,
            &target_type.inner,
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
        let (name, loc) = ctx.symtab.lookup_trait(&trait_spec.inner.path)?;
        Ok((
            TraitName::Named(name.at_loc(&loc)),
            visit_trait_spec(trait_spec, &TypeSpecKind::ImplTrait, ctx)?,
        ))
    } else {
        // Create an anonymous trait which we will impl
        let trait_name = TraitName::Anonymous(impl_block_id);

        create_trait_from_unit_heads(
            trait_name.clone(),
            &block.type_params,
            &block.where_clauses,
            &block
                .units
                .iter()
                .map(|u| u.head.clone().at_loc(u))
                .collect::<Vec<_>>(),
            ctx,
        )?;

        let type_params = match &block.type_params {
            Some(params) => {
                let mut type_expressions = vec![];
                for param in &params.inner {
                    let (name, _) = ctx.symtab.lookup_type_symbol(
                        &param.map_ref(|_| Path::ident(param.inner.name().clone())),
                    )?;
                    let spec = hir::TypeSpec::Generic(name.at_loc(param));
                    type_expressions.push(hir::TypeExpression::TypeSpec(spec).at_loc(param));
                }
                Some(type_expressions.at_loc(params))
            }
            None => None,
        };

        let spec = hir::TraitSpec {
            name: trait_name.clone(),
            type_params,
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
            let (target_name, sym) = ctx.symtab.lookup_type_symbol(&name)?;

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
    where_clauses: &[ast::WhereClause],
    heads: &[Loc<ast::UnitHead>],
    ctx: &mut Context,
) -> Result<()> {
    ctx.symtab.new_scope();

    let visited_type_params = if let Some(params) = type_params {
        Some(params.try_map_ref(|params| {
            params
                .iter()
                .map(|param| {
                    param.try_map_ref(|tp| {
                        let ident = tp.name();
                        let type_symbol = match tp {
                            ast::TypeParam::TypeName { name, traits } => {
                                let traits = traits
                                    .iter()
                                    .map(|t| visit_trait_spec(t, &TypeSpecKind::TraitBound, ctx))
                                    .collect::<Result<Vec<_>>>()?;

                                TypeSymbol::GenericArg { traits }.at_loc(name)
                            }
                            ast::TypeParam::TypeWithMeta { meta, name } => {
                                TypeSymbol::GenericMeta(visit_meta_type(meta)?).at_loc(name)
                            }
                        };
                        let name_id = ctx.symtab.add_type(Path::ident(ident.clone()), type_symbol);
                        Ok(match tp {
                            ast::TypeParam::TypeName { name: _, traits } => {
                                let trait_bounds = traits
                                    .iter()
                                    .map(|t| visit_trait_spec(t, &TypeSpecKind::TraitBound, ctx))
                                    .collect::<Result<_>>()?;

                                hir::TypeParam {
                                    ident: ident.clone(),
                                    name_id,
                                    trait_bounds,
                                    meta: MetaType::Type,
                                }
                            }
                            ast::TypeParam::TypeWithMeta { meta, name: _ } => hir::TypeParam {
                                ident: ident.clone(),
                                name_id,
                                trait_bounds: vec![],
                                meta: visit_meta_type(meta)?,
                            },
                        })
                    })
                })
                .collect::<Result<Vec<_>>>()
        })?)
    } else {
        None
    };

    let visited_where_clauses = visit_where_clauses(where_clauses, ctx)?;

    ctx.self_ctx = SelfContext::TraitDefinition(name.clone());
    let trait_members = heads
        .iter()
        .map(|head| {
            Ok((
                head.name.inner.clone(),
                unit_head(head, type_params, &visited_where_clauses, ctx, None)?.at_loc(head),
            ))
        })
        .collect::<Result<Vec<_>>>()?;

    // Add the trait to the trait list
    ctx.item_list
        .add_trait(name, visited_type_params, trait_members)?;

    ctx.symtab.close_scope();
    Ok(())
}

fn check_generic_params_match_trait_def(
    trait_def: &hir::TraitDef,
    trait_spec: &Loc<hir::TraitSpec>,
) -> Result<()> {
    if let Some(generic_params) = &trait_def.type_params {
        if let hir::TraitSpec {
            type_params: Some(generic_spec),
            ..
        } = &trait_spec.inner
        {
            if generic_params.len() != generic_spec.len() {
                Err(
                    Diagnostic::error(generic_spec, "Wrong number of generic type parameters")
                        .primary_label(format!(
                            "Expected {} type parameter{}",
                            generic_params.len(),
                            if generic_params.len() != 1 { "s" } else { "" }
                        ))
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
                        ),
                )
            } else {
                Ok(())
            }
        } else {
            match &trait_spec.name {
                TraitName::Named(name) => Err(Diagnostic::error(
                    trait_spec,
                    format!("Raw use of generic trait {name}"),
                )
                .primary_label(format!(
                    "Trait {name} used without specifying type parameters"
                ))
                .secondary_label(name, format!("Trait {name} defined here"))),
                TraitName::Anonymous(_) => Err(Diagnostic::bug(
                    ().nowhere(),
                    "Generic anonymous trait found, which should not be possible here",
                )),
            }
        }
    } else if let hir::TraitSpec {
        name,
        type_params: Some(generic_spec),
    } = &trait_spec.inner
    {
        match name {
            TraitName::Named(name) => {
                Err(Diagnostic::error(
                    generic_spec,
                    "Generic type parameters specified for non-generic trait",
                )
                .primary_label(
                    "Generic type parameters specified here",
                )
                .secondary_label(
                    name,
                    format!("Trait {} is not generic", name.inner.1),
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

fn check_is_no_function_on_port_type(
    unit: &Loc<ast::Unit>,
    target_type: &Loc<hir::TypeSpec>,
    ctx: &mut Context,
) -> Result<()> {
    if matches!(unit.head.unit_kind.inner, ast::UnitKind::Function) && target_type.is_port(ctx)? {
        Err(Diagnostic::error(
            &unit.head.unit_kind,
            "Functions are not allowed on port types",
        )
        .primary_label("Function on port type")
        .secondary_label(target_type.clone(), "This is a port type")
        .span_suggest_replace(
            "Consider making this an entity",
            &unit.head.unit_kind,
            "entity",
        ))
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
        missing_list.sort_by_key(|ident| &ident.0);

        let as_str = match missing_list.as_slice() {
            [] => unreachable!(),
            [single] => format!("{single}"),
            other => {
                if other.len() <= 3 {
                    format!(
                        "{} and {}",
                        other[0..other.len() - 1].iter().map(|id| &id.0).join(", "),
                        other[other.len() - 1].0
                    )
                } else {
                    format!(
                        "{} and {} more",
                        other[0..3].iter().map(|id| &id.0).join(", "),
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

fn resolve_trait_self<'a>(
    trait_ty: &'a hir::TypeSpec,
    impl_target_type: &'a hir::TypeSpec,
) -> &'a hir::TypeSpec {
    if matches!(trait_ty, hir::TypeSpec::TraitSelf(_)) {
        &impl_target_type
    } else {
        &trait_ty
    }
}

fn check_output_type_for_impl_method_and_trait_method_matches(
    impl_method: &hir::UnitHead,
    trait_method: &hir::UnitHead,
    target_type: &hir::TypeSpec,
) -> Result<()> {
    let trait_output = trait_method.output_type().inner;
    let trait_output = resolve_trait_self(&trait_output, &target_type);

    if &impl_method.output_type().inner != trait_output {
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

                let trait_type = resolve_trait_self(&t_spec.inner, impl_target_type);
                if trait_type != &i_spec.inner {
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

    let trait_method_type_params = &trait_method.unit_type_params;

    let impl_type_params = trait_spec
        .type_params
        .as_ref()
        .map_or(vec![], |params| params.inner.clone());

    let impl_method_type_params = &impl_method
        .unit_type_params
        .iter()
        .map(|param| {
            let spec = hir::TypeSpec::Generic(param.map_ref(hir::TypeParam::name_id));
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
                    impl_type_params.as_slice(),
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
            impl_type_params.as_slice(),
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

fn map_type_expr_to_trait(
    te: &Loc<hir::TypeExpression>,
    trait_type_params: &[Loc<hir::TypeParam>],
    trait_method_type_params: &[Loc<hir::TypeParam>],
    impl_type_params: &[Loc<hir::TypeExpression>],
    impl_method_type_params: &[Loc<hir::TypeExpression>],
    ctx: &mut Context,
) -> Result<Loc<hir::TypeExpression>> {
    match &te.inner {
        hir::TypeExpression::Integer(_) => Ok(te.clone()),
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
        hir::TypeExpression::ConstGeneric(_) => diag_bail!(te, "Const generic in impl head"),
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
                .find_position(|tp| tp.name_id() == name.inner)
                .map(|(idx, _)| idx);

            if let Some(param_idx) = param_idx {
                impl_type_params[param_idx].try_map_ref(|te| match &te {
                    hir::TypeExpression::TypeSpec(spec) => Ok(spec.clone()),
                    hir::TypeExpression::Integer(_) => Err(Diagnostic::bug(
                        &impl_type_params[param_idx],
                        "Expected a TypeExpression::TypeSpec, found TypeExpression::Integer",
                    )),
                    hir::TypeExpression::ConstGeneric(_) => {
                        diag_bail!(ty, "Const generic in impl head")
                    }
                })
            } else {
                let param_idx = trait_method_type_params
                    .iter()
                    .find_position(|tp| tp.name_id() == name.inner)
                    .map(|(idx, _)| idx);

                if let Some(param_idx) = param_idx {
                    impl_method_type_params[param_idx].try_map_ref(|te| match &te {
                        hir::TypeExpression::TypeSpec(spec) => Ok(spec.clone()),
                        hir::TypeExpression::Integer(_) => Err(Diagnostic::bug(
                            &impl_method_type_params[param_idx],
                            "Expected a TypeExpression::TypeSpec, found TypeExpression::Integer",
                        )),
                        hir::TypeExpression::ConstGeneric(_) => {
                            diag_bail!(ty, "Const generic in impl head")
                        }
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
        let mut set: HashMap<Identifier, Vec<(Loc<()>, hir::TypeSpec)>> = HashMap::new();

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
