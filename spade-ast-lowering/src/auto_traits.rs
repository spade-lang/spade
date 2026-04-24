use crate::Result;
use rustc_hash::FxHashMap as HashMap;
use spade_common::{
    doc_links::WIRE_DOCS,
    location_info::{Loc, WithLocation},
};
use spade_diagnostics::{Diagnostic, diag_bail};
use spade_hir::{
    ImplBlock, Parameter, Struct, TraitName, TraitSpec, TypeAlias, TypeDeclaration, TypeExpression,
    TypeSpec,
    auto_traits::{CopyWitness, DataWitness},
    symbol_table::{LangItem, TypeSymbol},
};
use spade_types::meta_types::MetaType;

use crate::Context;

trait TyExt {
    fn get_copy_witness(&self, ctx: &Context) -> Option<CopyWitness>;
    fn get_data_witness(&self, ctx: &Context) -> Option<DataWitness>;
}

impl TyExt for Loc<TypeExpression> {
    fn get_copy_witness(&self, ctx: &Context) -> Option<CopyWitness> {
        match &self.inner {
            TypeExpression::TypeSpec(spec) => spec
                .clone()
                .at_loc(self)
                .get_copy_witness(ctx)
                .map(|w| w.recurse(&self.loc())),
            // A generic non-type being one value or another cannot impact the copy-ness
            // of a value
            TypeExpression::Bool(_) => None,
            TypeExpression::Integer(_) => None,
            TypeExpression::String(_) => None,
            TypeExpression::ConstGeneric(_) => None,
        }
    }

    fn get_data_witness(&self, ctx: &Context) -> Option<DataWitness> {
        match &self.inner {
            TypeExpression::TypeSpec(spec) => spec
                .clone()
                .at_loc(self)
                .get_data_witness(ctx)
                .map(|w| w.recurse(&self.loc())),
            // A generic non-type being one value or another cannot impact the data-ness
            // of a value
            TypeExpression::Bool(_) => None,
            TypeExpression::Integer(_) => None,
            TypeExpression::String(_) => None,
            TypeExpression::ConstGeneric(_) => None,
        }
    }
}

impl TyExt for Loc<TypeSpec> {
    fn get_copy_witness(&self, ctx: &Context) -> Option<CopyWitness> {
        match &self.inner {
            TypeSpec::Tuple(inner) => inner
                .iter()
                .find_map(|ty| ty.get_copy_witness(ctx).map(|w| w.recurse(&ty.loc()))),
            TypeSpec::Array { inner, size: _ } => {
                inner.get_copy_witness(ctx).map(|w| w.recurse(&self.loc()))
            }
            TypeSpec::Declared(base, params) => {
                let Some(ty) = ctx.item_list.types.get(base).cloned() else {
                    unreachable!()
                };

                ty.get_copy_witness(ctx).or_else(|| {
                    params
                        .iter()
                        .find_map(|ty| ty.get_copy_witness(ctx).map(|w| w.recurse(&ty.loc())))
                })
            }
            TypeSpec::Generic(_) => {
                // Generics are not handled here, they get added as constraints to
                // the impl blocks we generate.
                None
            }
            // As soon as we see an `inv`, we know for sure we're not dealing with Copy
            TypeSpec::Inverted(_) => Some(CopyWitness::Here(self.loc())),
            // As soon as we see an `&`, we know for sure we're dealing with Copy
            TypeSpec::CopyView(_) => None,
            TypeSpec::TraitSelf(_) => {
                unreachable!()
            }
            TypeSpec::Wildcard(_) => {
                unreachable!(
                    "A wildcard cannot appear in a type spec which is being investigated for data"
                )
            }
        }
    }

    fn get_data_witness(&self, ctx: &Context) -> Option<DataWitness> {
        match &self.inner {
            TypeSpec::Tuple(inner) => inner
                .iter()
                .find_map(|ty| ty.get_data_witness(ctx).map(|w| w.recurse(&ty.loc()))),
            TypeSpec::Array { inner, size: _ } => {
                inner.get_data_witness(ctx).map(|w| w.recurse(&self.loc()))
            }
            TypeSpec::Declared(base, params) => {
                let Some(ty) = ctx.item_list.types.get(base).cloned() else {
                    unreachable!()
                };

                ty.get_data_witness(ctx).or_else(|| {
                    params
                        .iter()
                        .find_map(|ty| ty.get_data_witness(ctx).map(|w| w.recurse(&ty.loc())))
                })
            }
            TypeSpec::Generic(_) => {
                // Generics are not handled here, they get added as constraints to
                // the impl blocks we generate.
                None
            }
            // As soon as we see an `inv`, we know for sure we're not dealing with Data
            TypeSpec::Inverted(_) => Some(DataWitness::Here(self.loc())),
            // As soon as we see an `&`, we know for sure we're dealing with Data
            TypeSpec::CopyView(_) => None,
            TypeSpec::TraitSelf(_) => {
                unreachable!()
            }
            TypeSpec::Wildcard(_) => {
                unreachable!(
                    "A wildcard cannot appear in a type spec which is being investigated for data"
                )
            }
        }
    }
}

impl TyExt for Loc<TypeDeclaration> {
    fn get_copy_witness(&self, ctx: &Context) -> Option<CopyWitness> {
        match &self.kind {
            // Enums never impl !Copy because their members must impl data.
            spade_hir::TypeDeclKind::Enum(_) => None,
            spade_hir::TypeDeclKind::Primitive(inner) => match inner {
                spade_types::PrimitiveType::Int => None,
                spade_types::PrimitiveType::Uint => None,
                spade_types::PrimitiveType::Bool => None,
                spade_types::PrimitiveType::Clock => None,
                spade_types::PrimitiveType::Tri => None,

                spade_types::PrimitiveType::Memory | spade_types::PrimitiveType::InOut => {
                    Some(CopyWitness::Here(self.loc()))
                }
            },
            spade_hir::TypeDeclKind::Struct(s) => {
                let Struct {
                    members,
                    attributes: _,
                    wal_traceable: _,
                    documentation: _,
                } = &s.inner;

                members.inner.0.iter().find_map(
                    |Parameter {
                         no_mangle: _,
                         name: _,
                         ty,
                         wire: _,
                         field_translator: _,
                     }| {
                        ty.get_copy_witness(ctx).map(|w| w.recurse(&ty.loc()))
                    },
                )
            }
            spade_hir::TypeDeclKind::Alias(alias) => {
                let TypeAlias {
                    type_spec,
                    wal_traceable: _,
                    documentation: _,
                } = &alias.inner;

                type_spec.get_copy_witness(ctx)
            }
        }
    }

    fn get_data_witness(&self, ctx: &Context) -> Option<DataWitness> {
        match &self.kind {
            // Enums never impl !Data because their members must impl data.
            spade_hir::TypeDeclKind::Enum(_) => None,
            spade_hir::TypeDeclKind::Primitive(inner) => match inner {
                spade_types::PrimitiveType::Int => None,
                spade_types::PrimitiveType::Uint => None,
                spade_types::PrimitiveType::Bool => None,

                spade_types::PrimitiveType::Clock
                | spade_types::PrimitiveType::Tri
                | spade_types::PrimitiveType::Memory
                | spade_types::PrimitiveType::InOut => Some(DataWitness::Here(self.loc())),
            },
            spade_hir::TypeDeclKind::Struct(s) => {
                let Struct {
                    members,
                    attributes: _,
                    wal_traceable: _,
                    documentation: _,
                } = &s.inner;

                members.inner.0.iter().find_map(
                    |Parameter {
                         no_mangle: _,
                         name: _,
                         ty,
                         wire: _,
                         field_translator: _,
                     }| {
                        ty.get_data_witness(ctx).map(|w| w.recurse(&ty.loc()))
                    },
                )
            }
            spade_hir::TypeDeclKind::Alias(alias) => {
                let TypeAlias {
                    type_spec,
                    wal_traceable: _,
                    documentation: _,
                } = &alias.inner;

                type_spec.get_data_witness(ctx)
            }
        }
    }
}

pub fn enforce_enum_data(ctx: &mut Context) {
    for (_, ty) in &ctx.item_list.types {
        match &ty.kind {
            spade_hir::TypeDeclKind::Enum(e) => {
                for (_, parameters) in &e.options {
                    for param in &parameters.0 {
                        if let Some(witness) = param.ty.get_data_witness(ctx) {
                            Diagnostic::error(&param.ty, "Enum members must be Data")
                                .primary_label("Non-data enum member")
                                .secondary_label(witness.loc(), "This type is not Data")
                                .help("Typically, a type not being Data means it has an `inv` part")
                                .help(format!(
                                    "You can learn more about `Data` here: {}",
                                    WIRE_DOCS
                                ))
                                .handle_in(&mut ctx.diags.lock().unwrap());
                        }
                    }
                }
            }
            spade_hir::TypeDeclKind::Primitive(_)
            | spade_hir::TypeDeclKind::Struct(_)
            | spade_hir::TypeDeclKind::Alias(_) => {}
        }
    }
}

fn impl_auto_trait(
    lang_item: LangItem,
    ctx: &mut Context,
    pred: impl Fn(&Loc<TypeDeclaration>, &Context) -> bool,
) -> Result<()> {
    let name_id = ctx.symtab.lang_item(lang_item).clone().nowhere();

    let trait_name = TraitName::Named(None, name_id);

    for (name, ty) in &ctx.item_list.types {
        if pred(ty, ctx) {
            let (type_params, target_args): (Vec<_>, Vec<_>) = ty
                .inner
                .generic_args
                .iter()
                .map(|param| {
                    let Some(name) = param.name_id() else {
                        diag_bail!(param, "Found an impl Trait in a type definition")
                    };
                    let name = ctx.symtab.add_type(
                        name.1.clone().at_loc(&name),
                        TypeSymbol::GenericArg {
                            traits: vec![
                                TraitSpec {
                                    name: trait_name.clone(),
                                    type_params: None,
                                    paren_syntax: false,
                                }
                                .nowhere(),
                            ],
                        }
                        .nowhere(),
                        None,
                        None,
                    );

                    let mut param = param.clone();

                    param.name = spade_hir::Generic::Named(name.clone().at_loc(&param));

                    if param.meta == MetaType::Type {
                        param.trait_bounds.push(
                            TraitSpec {
                                name: trait_name.clone(),
                                type_params: None,
                                paren_syntax: false,
                            }
                            .nowhere(),
                        );
                    }

                    Ok((
                        param,
                        TypeExpression::TypeSpec(TypeSpec::Generic(spade_hir::Generic::Named(
                            name.nowhere(),
                        ))),
                    ))
                })
                .collect::<Result<Vec<_>>>()?
                .into_iter()
                .unzip();

            ctx.item_list.impls.insert(
                spade_hir::ImplTarget::Named(name.clone()),
                spade_hir::TraitSpec {
                    name: trait_name.clone(),
                    type_params: None,
                    paren_syntax: false,
                },
                target_args.clone(),
                ImplBlock {
                    fns: HashMap::default(),
                    type_params: type_params,
                    target: TypeSpec::Declared(
                        name.clone().nowhere(),
                        target_args.clone().into_iter().map(Loc::nowhere).collect(),
                    )
                    .nowhere(),
                    id: ctx.impl_idtracker.next(),
                }
                .nowhere(),
            )?;
        }
    }

    Ok(())
}

/// This performs blanket implementations of the `Data` trait for all types which do not
pub fn impl_auto_traits(ctx: &mut Context) -> Result<()> {
    // We'll add a few things to the symtab here, let's do that in a scope
    ctx.in_new_scope(|ctx| {
        impl_auto_trait(LangItem::CopyTrait, ctx, |ty, ctx| {
            ty.get_copy_witness(ctx).is_none()
        })?;

        impl_auto_trait(LangItem::DataTrait, ctx, |ty, ctx| {
            ty.get_data_witness(ctx).is_none()
        })?;

        enforce_enum_data(ctx);
        Ok(())
    })
}
