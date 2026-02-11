use rustc_hash::FxHashMap as HashMap;
use spade_common::{
    location_info::{Loc, WithLocation},
    name::{Identifier, Path, Visibility},
};
use spade_diagnostics::Diagnostic;
use spade_hir::{
    self as hir,
    symbol_table::{EnumVariant, StructCallable, Thing, TypeSymbol},
};

use crate::{error::Result, Context};

pub fn add_type_alias(
    alias_name: Loc<Identifier>,
    alias_params: &Vec<Loc<hir::TypeParam>>,
    target_type: &Loc<hir::TypeSpec>,
    visibility: Loc<Visibility>,
    deprecation_note: Option<Option<Loc<String>>>,
    ctx: &mut Context,
) -> Result<()> {
    let alias_id = ctx.symtab.add_type(
        alias_name.clone(),
        TypeSymbol::Alias(target_type.clone()).at_loc(&target_type),
        visibility.clone(),
        deprecation_note.clone(),
    );

    // When aliasing a struct or enum, their `Callables` must also be added to the symbol table
    match &target_type.inner {
        hir::TypeSpec::Declared(name_id, generic_params) => {
            match ctx.item_list.types.get(&name_id).map(|td| &td.inner) {
                Some(hir::TypeDeclaration {
                    name: _,
                    kind: hir::TypeDeclKind::Struct(s),
                    generic_args,
                }) => {
                    let replacements = generic_args
                        .iter()
                        .map(|tp| tp.inner.name.clone())
                        .zip(generic_params.iter().cloned())
                        .collect::<HashMap<_, _>>();

                    let new_members = hir::ParameterList(
                        s.members
                            .inner
                            .0
                            .iter()
                            .map(|param| {
                                let new_ty =
                                    apply_replacements_to_type_spec(&param.ty, &replacements)?;

                                Ok(hir::Parameter {
                                    no_mangle: param.no_mangle.clone(),
                                    name: param.name.clone(),
                                    ty: new_ty,
                                    field_translator: param.field_translator.clone(),
                                })
                            })
                            .collect::<Result<_>>()?,
                    );

                    ctx.symtab.add_thing_with_name_id(
                        alias_id.clone(),
                        Thing::Struct(
                            StructCallable {
                                name: alias_name.clone(),
                                self_type: target_type.clone(),
                                params: new_members.at_loc(&s.members),
                                type_params: alias_params.clone(),
                                deprecation_note: deprecation_note.clone(),
                            }
                            .at_loc(&target_type),
                        ),
                        Some(visibility),
                        deprecation_note.clone(),
                    );

                    ctx.item_list
                        .executables
                        .insert(alias_id.clone(), hir::ExecutableItem::StructInstance);
                }
                Some(hir::TypeDeclaration {
                    name: _,
                    kind: hir::TypeDeclKind::Enum(e),
                    generic_args,
                }) => {
                    for (pos, (variant_path_id, members)) in e.options.iter().enumerate() {
                        let variant_name = variant_path_id.1.tail().unwrap_named().clone();

                        let replacements = generic_args
                            .iter()
                            .map(|tp| tp.inner.name.clone())
                            .zip(generic_params.iter().cloned())
                            .collect::<HashMap<_, _>>();

                        let new_members = hir::ParameterList(
                            members
                                .inner
                                .0
                                .iter()
                                .map(|param| {
                                    let new_ty =
                                        apply_replacements_to_type_spec(&param.ty, &replacements)?;

                                    Ok(hir::Parameter {
                                        no_mangle: param.no_mangle.clone(),
                                        name: param.name.clone(),
                                        ty: new_ty,
                                        field_translator: param.field_translator.clone(),
                                    })
                                })
                                .collect::<Result<_>>()?,
                        );

                        let variant_deprecation_note =
                            ctx.symtab.deprecation_notes.get(&variant_path_id).cloned();

                        let new_variant_id = ctx.symtab.add_thing(
                            Path::from_idents(&[&alias_name, &variant_name]),
                            Thing::EnumVariant(
                                EnumVariant {
                                    name: variant_name,
                                    output_type: target_type.clone(),
                                    option: pos,
                                    params: new_members.at_loc(&members),
                                    type_params: alias_params.clone(),
                                    documentation: e.documentation.clone(),
                                    deprecation_note: variant_deprecation_note.clone(),
                                }
                                .at_loc(&variant_path_id),
                            ),
                            Some(Visibility::AtSuper.nowhere()),
                            variant_deprecation_note,
                        );

                        ctx.item_list.executables.insert(
                            new_variant_id.clone(),
                            hir::ExecutableItem::EnumInstance {
                                base_enum: alias_id.clone(),
                                variant: pos,
                            },
                        );
                    }
                }
                _ => {}
            }
        }
        hir::TypeSpec::Generic(_)
        | hir::TypeSpec::Tuple(_)
        | hir::TypeSpec::Array { .. }
        | hir::TypeSpec::Inverted(_)
        | hir::TypeSpec::Wire(_)
        | hir::TypeSpec::TraitSelf(_)
        | hir::TypeSpec::Wildcard(_) => {}
    }

    Ok(())
}

fn apply_replacements_to_type_spec(
    ty: &Loc<hir::TypeSpec>,
    replacements: &HashMap<hir::Generic, Loc<hir::TypeExpression>>,
) -> Result<Loc<hir::TypeSpec>> {
    match &ty.inner {
        hir::TypeSpec::Declared(name_id, generic_args) => Ok(hir::TypeSpec::Declared(
            name_id.clone(),
            generic_args
                .iter()
                .map(|arg| apply_replacements_to_type_expr(&arg, replacements))
                .collect::<Result<_>>()?,
        )
        .at_loc(&ty)),
        hir::TypeSpec::Generic(g) => match replacements.get(g) {
            Some(t) => {
                let ts = match &t.inner {
                    hir::TypeExpression::TypeSpec(ts) => ts,
                    hir::TypeExpression::Bool(_) => {
                        return Err(Diagnostic::bug(t, "Cannot replace generic with bool"))
                    }
                    hir::TypeExpression::Integer(_) => {
                        return Err(Diagnostic::bug(t, "Cannot replace generic with integer"))
                    }
                    hir::TypeExpression::String(_) => {
                        return Err(Diagnostic::bug(t, "Cannot replace generic with string"))
                    }
                    hir::TypeExpression::ConstGeneric(_) => {
                        return Err(Diagnostic::bug(
                            t,
                            "Cannot replace generic with const generic",
                        ))
                    }
                };
                Ok(ts.clone().at_loc(&t))
            }
            None => Ok(ty.clone()),
        },
        hir::TypeSpec::Tuple(members) => Ok(hir::TypeSpec::Tuple(
            members
                .iter()
                .map(|member| apply_replacements_to_type_spec(member, replacements))
                .collect::<Result<_>>()?,
        )
        .at_loc(&ty)),
        hir::TypeSpec::Array { inner, size } => Ok(hir::TypeSpec::Array {
            inner: Box::new(apply_replacements_to_type_spec(&inner, replacements)?),
            size: Box::new(apply_replacements_to_type_expr(&size, replacements)?),
        }
        .at_loc(&ty)),
        hir::TypeSpec::Inverted(ts) => Ok(hir::TypeSpec::Inverted(Box::new(
            apply_replacements_to_type_spec(&ts, replacements)?,
        ))
        .at_loc(&ty)),
        hir::TypeSpec::Wire(ts) => Ok(hir::TypeSpec::Inverted(Box::new(
            apply_replacements_to_type_spec(&ts, replacements)?,
        ))
        .at_loc(&ty)),

        hir::TypeSpec::TraitSelf(_) | hir::TypeSpec::Wildcard(_) => Ok(ty.clone()),
    }
}

fn apply_replacements_to_type_expr(
    ty: &Loc<hir::TypeExpression>,
    replacements: &HashMap<hir::Generic, Loc<hir::TypeExpression>>,
) -> Result<Loc<hir::TypeExpression>> {
    match &ty.inner {
        hir::TypeExpression::Bool(_) => Ok(ty.clone()),
        hir::TypeExpression::Integer(_) => Ok(ty.clone()),
        hir::TypeExpression::String(_) => Ok(ty.clone()),
        hir::TypeExpression::TypeSpec(ts) => {
            if let hir::TypeSpec::Generic(name) = ts {
                match replacements.get(name) {
                    Some(replacement) => Ok(replacement.clone()),
                    None => Ok(ty.clone()),
                }
            } else {
                Ok(hir::TypeExpression::TypeSpec(
                    apply_replacements_to_type_spec(&ts.clone().at_loc(&ty), replacements)?.inner,
                )
                .at_loc(&ty))
            }
        }
        hir::TypeExpression::ConstGeneric(cg) => Ok(hir::TypeExpression::ConstGeneric(
            apply_replacements_to_const_generic(cg, replacements)?,
        )
        .at_loc(&ty)),
    }
}

fn apply_replacements_to_const_generic(
    ty: &Loc<hir::ConstGeneric>,
    replacements: &HashMap<hir::Generic, Loc<hir::TypeExpression>>,
) -> Result<Loc<hir::ConstGeneric>> {
    match &ty.inner {
        hir::ConstGeneric::Name(name) => match replacements.get(&hir::Generic::Named(name.clone()))
        {
            Some(t) => match &t.inner {
                hir::TypeExpression::TypeSpec(_) => {
                    return Err(Diagnostic::bug(
                        t,
                        "Cannot replace const generic name with type spec",
                    ))
                }
                hir::TypeExpression::Bool(b) => Ok(hir::ConstGeneric::Bool(*b).at_loc(&t)),
                hir::TypeExpression::Integer(i) => Ok(hir::ConstGeneric::Int(i.clone()).at_loc(&t)),
                hir::TypeExpression::String(s) => Ok(hir::ConstGeneric::Str(s.clone()).at_loc(&t)),
                hir::TypeExpression::ConstGeneric(cg) => Ok(cg.clone()),
            },
            None => Ok(ty.clone()),
        },
        hir::ConstGeneric::Add(lhs, rhs) => Ok(hir::ConstGeneric::Add(
            Box::new(apply_replacements_to_const_generic(lhs, replacements)?),
            Box::new(apply_replacements_to_const_generic(rhs, replacements)?),
        )
        .at_loc(ty)),
        hir::ConstGeneric::Sub(lhs, rhs) => Ok(hir::ConstGeneric::Sub(
            Box::new(apply_replacements_to_const_generic(lhs, replacements)?),
            Box::new(apply_replacements_to_const_generic(rhs, replacements)?),
        )
        .at_loc(ty)),
        hir::ConstGeneric::Mul(lhs, rhs) => Ok(hir::ConstGeneric::Mul(
            Box::new(apply_replacements_to_const_generic(lhs, replacements)?),
            Box::new(apply_replacements_to_const_generic(rhs, replacements)?),
        )
        .at_loc(ty)),
        hir::ConstGeneric::Div(lhs, rhs) => Ok(hir::ConstGeneric::Div(
            Box::new(apply_replacements_to_const_generic(lhs, replacements)?),
            Box::new(apply_replacements_to_const_generic(rhs, replacements)?),
        )
        .at_loc(ty)),
        hir::ConstGeneric::Mod(lhs, rhs) => Ok(hir::ConstGeneric::Mod(
            Box::new(apply_replacements_to_const_generic(lhs, replacements)?),
            Box::new(apply_replacements_to_const_generic(rhs, replacements)?),
        )
        .at_loc(ty)),
        hir::ConstGeneric::UintBitsToFit(inner) => Ok(hir::ConstGeneric::UintBitsToFit(Box::new(
            apply_replacements_to_const_generic(inner, replacements)?,
        ))
        .at_loc(ty)),
        hir::ConstGeneric::Eq(lhs, rhs) => Ok(hir::ConstGeneric::Eq(
            Box::new(apply_replacements_to_const_generic(lhs, replacements)?),
            Box::new(apply_replacements_to_const_generic(rhs, replacements)?),
        )
        .at_loc(ty)),
        hir::ConstGeneric::NotEq(lhs, rhs) => Ok(hir::ConstGeneric::NotEq(
            Box::new(apply_replacements_to_const_generic(lhs, replacements)?),
            Box::new(apply_replacements_to_const_generic(rhs, replacements)?),
        )
        .at_loc(ty)),
        hir::ConstGeneric::LogicalNot(inner) => Ok(hir::ConstGeneric::LogicalNot(Box::new(
            apply_replacements_to_const_generic(inner, replacements)?,
        ))
        .at_loc(ty)),
        hir::ConstGeneric::LogicalAnd(lhs, rhs) => Ok(hir::ConstGeneric::LogicalAnd(
            Box::new(apply_replacements_to_const_generic(lhs, replacements)?),
            Box::new(apply_replacements_to_const_generic(rhs, replacements)?),
        )
        .at_loc(ty)),
        hir::ConstGeneric::LogicalOr(lhs, rhs) => Ok(hir::ConstGeneric::LogicalOr(
            Box::new(apply_replacements_to_const_generic(lhs, replacements)?),
            Box::new(apply_replacements_to_const_generic(rhs, replacements)?),
        )
        .at_loc(ty)),
        hir::ConstGeneric::LogicalXor(lhs, rhs) => Ok(hir::ConstGeneric::LogicalXor(
            Box::new(apply_replacements_to_const_generic(lhs, replacements)?),
            Box::new(apply_replacements_to_const_generic(rhs, replacements)?),
        )
        .at_loc(ty)),
        hir::ConstGeneric::Bool(_) => Ok(ty.clone()),
        hir::ConstGeneric::Int(_) => Ok(ty.clone()),
        hir::ConstGeneric::Str(_) => Ok(ty.clone()),
    }
}
