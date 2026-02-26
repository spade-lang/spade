use crate::Result;
use rustc_hash::FxHashMap as HashMap;
use spade_common::{
    location_info::{Loc, WithLocation},
    name::Visibility,
};
use spade_diagnostics::diag_bail;
use spade_hir::{
    ImplBlock, Parameter, Struct, TraitName, TraitSpec, TypeAlias, TypeDeclaration, TypeExpression, TypeSpec, auto_traits::DataWitness, symbol_table::TypeSymbol
};
use spade_types::meta_types::MetaType;

use crate::Context;

trait TyExt {
    fn get_data_witness(&self, ctx: &Context) -> Option<DataWitness>;
}

impl TyExt for Loc<TypeExpression> {
    fn get_data_witness(&self, ctx: &Context) -> Option<DataWitness> {
        match &self.inner {
            // TODO: This clone is awful
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
                    unreachable!() // TODO: Decide if this is fine
                };

                ty.get_data_witness(ctx).or_else(|| {
                    params
                        .iter()
                        .find_map(|ty| ty.get_data_witness(ctx).map(|w| w.recurse(&ty.loc())))
                })
            }
            TypeSpec::Generic(_) => {
                // Generics are nto handled here, they get added as constraints to
                // the impl blocks we generate.
                None
            }
            // As soon as we see an `inv`, we know for sure we're not dealing with Data
            TypeSpec::Inverted(_) => Some(DataWitness::Here(self.loc())),
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
    fn get_data_witness(&self, ctx: &Context) -> Option<DataWitness> {
        match &self.kind {
            // Enums never impl !Data because their members must impl data. This
            // mustbe checked later
            // TODO
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

/// This performs blanket implementations of the `Data` trait for all types which do not
pub fn impl_auto_traits(ctx: &mut Context) -> Result<()> {
    // We'll add a few things to the symtab here, let's do that in a scope
    ctx.in_new_scope(|ctx| {
        let data = ctx
            .symtab
            .lang_item(spade_hir::symbol_table::LangItem::DataTrait)
            .clone()
            .nowhere();
        let data_trait_name = TraitName::Named(None, data);
        for (name, ty) in &ctx.item_list.types {
            if let Some(witness) = ty.get_data_witness(ctx) {
                ctx.symtab.data_witnesses.insert(name.clone(), witness);
            } else {
                let (type_params, target_args): (Vec<_>, Vec<_>) = ty
                    .inner
                    .generic_args
                    .iter()
                    .map(|param| {
                        let Some(name) = param.name_id() else {
                            diag_bail!(param, "Found an impl Trait in a type definition")
                        };
                        let name = ctx.symtab.add_type(
                            name.1.tail().unwrap_named().clone(),
                            TypeSymbol::GenericArg {
                                traits: vec![TraitSpec {
                                    name: data_trait_name.clone(),
                                    type_params: None,
                                    paren_syntax: false,
                                }
                                .nowhere()],
                            }
                            .nowhere(),
                            Visibility::Public.nowhere(),
                            None,
                        );

                        let mut param = param.clone();

                        param.name = spade_hir::Generic::Named(name.clone().at_loc(&param));

                        if param.meta == MetaType::Type {
                            param.trait_bounds.push(
                                TraitSpec {
                                    name: data_trait_name.clone(),
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
                        name: data_trait_name.clone(),
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
    })
}
