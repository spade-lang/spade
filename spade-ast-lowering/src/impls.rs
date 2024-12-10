use std::collections::{HashMap, HashSet};

use itertools::{EitherOrBoth, Itertools};
use spade_ast as ast;
use spade_common::location_info::{Loc, WithLocation};
use spade_common::name::{Identifier, Path};
use spade_diagnostics::{diag_bail, Diagnostic};
use spade_hir::symbol_table::TypeSymbol;
use spade_hir::{self as hir, TraitName};
use spade_types::meta_types::MetaType;

use crate::error::Result;
use crate::global_symbols::{self, visit_meta_type};
use crate::{
    types::IsPort, unit_head, visit_trait_spec, visit_type_expression, visit_type_param,
    visit_type_spec, visit_unit, visit_where_clauses, Context, SelfContext, TypeSpecKind,
};

#[tracing::instrument(skip(ctx))]
pub fn visit_impl(block: &Loc<ast::ImplBlock>, ctx: &mut Context) -> Result<Vec<hir::Item>> {
    let mut result = vec![];

    ctx.symtab.new_scope();

    let self_path = Loc::new(Path::from_strs(&["Self"]), block.span, block.file_id);

    let target_path = if let ast::TypeSpec::Named(path, _) = &block.target.inner {
        ctx.symtab.add_alias(self_path, path.clone())?;
        path
    } else {
        return Err(
            Diagnostic::error(&block.target, "Impl target is not a named type")
                .primary_label("Not a named type"),
        );
    };

    let mut impl_type_params = vec![];

    if let Some(type_params) = &block.type_params {
        for param in type_params.inner.iter() {
            let param = param.try_map_ref(|p| visit_type_param(p, ctx))?;
            impl_type_params.push(param);
        }
    }

    let (target, target_args) = get_impl_target(block, ctx)?;

    let visited_where_clauses = visit_where_clauses(&block.where_clauses, ctx)?;

    let impl_block_id = ctx.impl_idtracker.next();
    let (trait_name, trait_spec) = if let Some(trait_spec) = &block.r#trait {
        let (name, loc) = ctx.symtab.lookup_trait(&trait_spec.inner.path)?;
        (
            TraitName::Named(name.at_loc(&loc)),
            visit_trait_spec(trait_spec, &TypeSpecKind::ImplTrait, ctx)?,
        )
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

        (trait_name, spec)
    };

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

    let target_type_spec = visit_type_spec(&block.target, &TypeSpecKind::ImplTarget, ctx)?;

    let mut trait_members = vec![];
    let mut trait_impl = HashMap::new();

    ctx.self_ctx = SelfContext::ImplBlock(target_type_spec);

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

        check_is_no_function_on_port_type(unit, block, ctx)?;

        let path_suffix = Some(Path(vec![
            Identifier(format!("impl_{}", impl_block_id)).nowhere()
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
            hir::Item::Builtin(_, head) => {
                return Err(Diagnostic::error(head, "Methods cannot be __builtin__")
                    .help("Consider defining a free-standing function"))
            }
        }

        let impl_method = &item.assume_unit().head;

        check_type_params_for_impl_method_and_trait_method_match(impl_method, trait_method)?;

        let trait_method_mono =
            monomorphise_trait_method(trait_method, impl_method, &trait_def, &trait_spec, ctx)?;

        check_output_type_for_impl_method_and_trait_method_matches(
            impl_method,
            &trait_method_mono,
            &target,
        )?;

        check_params_for_impl_method_and_trait_method_match(
            impl_method,
            &trait_method_mono,
            target_path,
            ctx,
        )?;

        missing_methods.remove(&unit.head.name.inner);

        result.push(item);
    }

    check_no_missing_methods(block, missing_methods)?;

    let target_type = visit_type_spec(&block.target, &TypeSpecKind::ImplTarget, ctx)?;

    let trait_type_params = if let Some(trait_type_params) = &trait_spec.type_params {
        trait_type_params
            .inner
            .iter()
            .map(Loc::strip_ref)
            .cloned()
            .collect()
    } else {
        vec![]
    };

    let impl_only_differing_by_trait_type_params = ctx
        .item_list
        .impls
        .get(&target)
        .map(|impls| {
            impls
                .iter()
                .find_position(|((name, _), _)| name == &trait_name)
                .map(|(idx, _)| idx)
        })
        .flatten();

    let duplicate = ctx
        .item_list
        .impls
        .entry(target.clone())
        .or_default()
        .insert(
            (trait_name.clone(), trait_type_params),
            hir::ImplBlock {
                fns: trait_impl,
                type_params: impl_type_params,
                target: target_type,
                id: impl_block_id,
            }
            .at_loc(block),
        );

    if let Some(duplicate) = duplicate {
        let name = match &trait_name {
            TraitName::Named(n) => n,
            TraitName::Anonymous(_) => {
                diag_bail!(block, "Found multiple impls of anonymous trait")
            }
        };
        return Err(Diagnostic::error(
            block,
            format!(
                "Multiple implementations of {} for {}",
                name,
                &target.display(&target_args)
            ),
        )
        .secondary_label(duplicate, "Previous impl here"));
    }

    if let Some(_) = impl_only_differing_by_trait_type_params {
        return Err(Diagnostic::error(
            block,
            format!("An impl of trait {trait_name} for {} already exists", target.display(&target_args)),
        )
            .primary_label(format!("An impl of trait {trait_name} for {} already exists", target.display(&target_args)))
            .note("The impls only differ by type parameters of the trait, which is currently not supported"));
    }

    ctx.self_ctx = SelfContext::FreeStanding;
    ctx.symtab.close_scope();

    Ok(result)
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
        spade_ast::TypeSpec::Unit(_) => {
            return Err(
                Diagnostic::error(&block.target, "Impls on void is currently unsupported")
                    .primary_label("Impl target cannot be void"),
            );
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
                unit_head(head, type_params, &visited_where_clauses, ctx)?,
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
    block: &Loc<ast::ImplBlock>,
    ctx: &mut Context,
) -> Result<()> {
    if matches!(unit.head.unit_kind.inner, ast::UnitKind::Function)
        && block.target.is_port(&ctx.symtab)?
    {
        Err(Diagnostic::error(
            &unit.head.unit_kind,
            "Functions are not allowed on port types",
        )
        .primary_label("Function on port type")
        .secondary_label(block.target.clone(), "This is a port type")
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

fn check_output_type_for_impl_method_and_trait_method_matches(
    impl_method: &hir::UnitHead,
    trait_method: &hir::UnitHead,
    target_name: &hir::ImplTarget,
) -> Result<()> {
    if impl_method.output_type() != trait_method.output_type() {
        let returns_trait_self = matches!(
            trait_method.output_type().inner,
            hir::TypeSpec::TraitSelf(_)
        );
        let impl_output_type = match impl_method.output_type().inner {
            hir::TypeSpec::Declared(name, _) => Some(name),
            hir::TypeSpec::Generic(name) => Some(name),
            _ => None,
        };

        // TODO: This'll need a good bit of testing
        if !(returns_trait_self
            && impl_output_type.is_some_and(|it| &hir::ImplTarget::Named(it.inner) == target_name))
        {
            return Err(Diagnostic::error(
                impl_method.output_type(),
                "Return type does not match trait",
            )
            .primary_label(format!("Expected {}", trait_method.output_type()))
            .secondary_label(trait_method.output_type(), "To match the trait"));
        }
    }
    Ok(())
}

fn check_params_for_impl_method_and_trait_method_match(
    impl_method: &hir::UnitHead,
    trait_method: &hir::UnitHead,
    target_path: &Loc<Path>,
    ctx: &Context,
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
                },
                hir::Parameter {
                    name: t_name,
                    ty: t_spec,
                    no_mangle: _,
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

                let i_spec_name = match &i_spec.inner {
                    hir::TypeSpec::Declared(name, _) => Some(&name.inner),
                    _ => None,
                };

                let (target_name, _) = ctx.symtab.lookup_type_symbol(target_path)?;

                if !(matches!(&t_spec.inner, hir::TypeSpec::TraitSelf(_))
                    && i_spec_name.is_some_and(|path| path == &target_name))
                    && t_spec != i_spec
                {
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
fn monomorphise_trait_method(
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
                monomorphise_type_spec(
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
                })
            })
            .collect::<Result<_>>()
            .map(|params| hir::ParameterList(params))
    })?;

    let output_type = if let Some(ty) = trait_method.output_type.as_ref() {
        Some(monomorphise_type_spec(
            ty,
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

fn monomorphise_type_expr(
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
            let (inner, loc) = monomorphise_type_spec(
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

fn monomorphise_type_spec(
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
                    monomorphise_type_expr(
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
                    monomorphise_type_spec(
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
            let mono_inner = monomorphise_type_spec(
                inner,
                trait_type_params,
                trait_method_type_params,
                impl_type_params,
                impl_method_type_params,
                ctx,
            )?;
            let mono_size = monomorphise_type_expr(
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
            let mono_inner = monomorphise_type_spec(
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
            let mono_inner = monomorphise_type_spec(
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
pub fn ensure_unique_anonymous_traits(item_list: &hir::ItemList) -> Vec<Diagnostic> {
    item_list
        .impls
        .iter()
        .flat_map(|(impl_target, impls)| {
            let mut fns = impls
                .iter()
                .filter(|(t, _)| t.0.is_anonymous())
                .flat_map(|(_, impl_block)| impl_block.fns.iter().map(|f| (f, &impl_block.target)))
                .collect::<Vec<_>>();

            // For deterministic error messages, the order at which functions are seen must be
            // deterministic. This is not the case as the impls come out of the hash map, so we'll
            // sort them depending on the loc span of the impl. The exact ordering is
            // completely irrelevant, as long as it is ordered the same way every time a test
            // is run
            fns.sort_by_key(|(f, _target)| f.1 .1.span);

            let mut set: HashMap<&Identifier, (Loc<()>, Vec<&hir::TypeSpec>)> = HashMap::new();
            // TODO: Report the overlapee

            let mut duplicate_errs = vec![];
            for ((f, f_loc), target) in fns {
                if let Some((prev, specs)) = set.get_mut(f) {
                    if specs.iter().any(|spec| type_specs_overlap(target, spec)) {
                        duplicate_errs.push(
                            Diagnostic::error(
                                f_loc.1,
                                format!("{} already has a method named {f}", target),
                            )
                            .primary_label("Duplicate method")
                            .secondary_label(prev.loc(), "Previous definition here"),
                        );
                    } else {
                        specs.push(target)
                    }
                } else {
                    set.insert(f, (f_loc.1, vec![&target.inner]));
                }
            }

            duplicate_errs
        })
        .collect::<Vec<_>>()
}

fn type_specs_overlap(l: &hir::TypeSpec, r: &hir::TypeSpec) -> bool {
    match (l, r) {
        // Generic types overlap with all types
        (hir::TypeSpec::Generic(_), _) => true,
        (_, hir::TypeSpec::Generic(_)) => true,
        // Declared types overlap if their base is the same and their generics overlap
        (hir::TypeSpec::Declared(lbase, lparams), hir::TypeSpec::Declared(rbase, rparams)) => {
            lbase == rbase
                && lparams
                    .iter()
                    .zip(rparams)
                    .all(|(le, re)| type_exprs_overlap(le, re))
        }
        (hir::TypeSpec::Declared(_, _), _) => false,
        (hir::TypeSpec::Tuple(linner), hir::TypeSpec::Tuple(rinner)) => linner
            .iter()
            .zip(rinner)
            .all(|(l, r)| type_specs_overlap(l, r)),
        (hir::TypeSpec::Tuple(_), _) => false,
        (
            hir::TypeSpec::Array {
                inner: linner,
                size: lsize,
            },
            hir::TypeSpec::Array {
                inner: rinner,
                size: rsize,
            },
        ) => type_specs_overlap(linner, rinner) && type_exprs_overlap(lsize, rsize),
        (hir::TypeSpec::Array { .. }, _) => false,
        (hir::TypeSpec::Unit(_), hir::TypeSpec::Unit(_)) => true,
        (hir::TypeSpec::Unit(_), _) => false,
        (hir::TypeSpec::Inverted(linner), hir::TypeSpec::Inverted(rinner)) => {
            type_specs_overlap(&linner.inner, &rinner.inner)
        }
        (hir::TypeSpec::Inverted(_), _) => todo!(),
        (hir::TypeSpec::Wire(linner), hir::TypeSpec::Wire(rinner)) => {
            type_specs_overlap(linner, rinner)
        }
        (hir::TypeSpec::Wire(_), _) => false,
        (hir::TypeSpec::TraitSelf(_), _) => unreachable!("Self type cannot be checked for overlap"),
        (hir::TypeSpec::Wildcard, _) => unreachable!("Wildcard type cannot be checked for overlap"),
    }
}

fn type_exprs_overlap(l: &hir::TypeExpression, r: &hir::TypeExpression) -> bool {
    match (l, r) {
        (hir::TypeExpression::Integer(rval), hir::TypeExpression::Integer(lval)) => rval == lval,
        // The only way an integer overlaps with a type is if it is a generic, so both
        // of these branches overlap
        (hir::TypeExpression::Integer(_), hir::TypeExpression::TypeSpec(_)) => true,
        (hir::TypeExpression::TypeSpec(_), hir::TypeExpression::Integer(_)) => true,
        (hir::TypeExpression::TypeSpec(lspec), hir::TypeExpression::TypeSpec(rspec)) => {
            type_specs_overlap(lspec, rspec)
        }
        (hir::TypeExpression::ConstGeneric(_), _) | (_, hir::TypeExpression::ConstGeneric(_)) => {
            unreachable!("Const generic during type_exprs_overlap")
        }
    }
}
