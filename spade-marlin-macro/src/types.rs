use std::collections::HashMap;

use proc_macro_error::{abort, emit_error};
use proc_macro2::{Ident, TokenStream};
use quote::{format_ident, quote};
use spade::compiler_state::CompilerState;
use spade_common::{
    location_info::WithLocation,
    name::{Identifier, NameID, Path},
};
use spade_hir::{
    Parameter, TypeDeclaration, TypeExpression, TypeParam, TypeSpec,
};

type PrimitiveMap = HashMap<NameID, TokenStream>;


/// NameIDs always contain their fully qualified paths, but for some things, we want the
/// non-FQP, for example, for generic arguments. Hence the special mirror functions
trait NameIDExt {
    /// Translalte the fully qualified path into the corresponding Spade path
    /// (relative to the module where things will be inserted)
    fn mirror_global(
        &self,
        primitives: &PrimitiveMap,
    ) -> TokenStream;
    fn mirror_local(&self) -> TokenStream;
}

impl NameIDExt for NameID {
    fn mirror_global(
        &self,
        primitives: &PrimitiveMap,
    ) -> TokenStream {
        primitives.get(self).cloned().unwrap_or_else(|| {
            let full = format_ident!("spade_types");
            let here = self.1.0.iter().map(|segment| {
                let s = format_ident!("{}", &segment.0);
                quote!(#s)
            });
            quote!(crate :: #full :: #(#here)::*)
        })
    }

    fn mirror_local(&self) -> TokenStream {
        let name = format_ident!(
            "{}",
            &self
                .1
                .0
                .last()
                .expect("Found a NameID with 0 path segments")
                .0
        );
        quote!(#name)
    }
}

trait IdentExt {
    fn mirror(&self) -> TokenStream;
}
impl IdentExt for Identifier {
    fn mirror(&self) -> TokenStream {
        let name = format_ident!("{}", self.0);
        quote!(#name)
    }
}

trait Mirror {
    fn mirror(
        &self,
        primitive_map: &PrimitiveMap,
    ) -> TokenStream;
}

impl Mirror for TypeExpression {
    fn mirror(
        &self,
        primitive_map: &PrimitiveMap,
    ) -> TokenStream {
        match self {
            TypeExpression::TypeSpec(type_spec) => {
                type_spec.mirror(primitive_map)
            }
            TypeExpression::Integer(val) => {
                // let val = val.to_str_radix(10);
                let (sign, val) = val.to_u64_digits();
                if val.len() > 1 {
                    panic!("Type level integers > 64 bits are currently unsupported");
                }
                let val = if matches!(sign, num::bigint::Sign::Minus) {
                    panic!("Negative type level integers are not currently supported")
                } else {
                    val[0]
                };
                quote!({ #val })
            }
            TypeExpression::String(_) => {
                panic!("Strings are not supported")
            }
            TypeExpression::ConstGeneric(_) => {
                panic!("Const generics are not supported")
            }
        }
    }
}

pub trait TypeSpecExt {
    fn mirror(
        &self,
        primitive_map: &PrimitiveMap,
    ) -> TokenStream;
    fn mirror_with_turbofish(
        &self,
        primitive_map: &PrimitiveMap,
    ) -> TokenStream;
    fn mirror_impl(
        &self,
        primitive_map: &PrimitiveMap,
        turbofish: bool,
    ) -> TokenStream;
}

impl TypeSpecExt for TypeSpec {
    fn mirror(
        &self,
        primitive_map: &PrimitiveMap,
    ) -> TokenStream {
        self.mirror_impl(primitive_map, false)
    }
    fn mirror_with_turbofish(
        &self,
        primitive_map: &PrimitiveMap,
    ) -> TokenStream {
        self.mirror_impl(primitive_map, true)
    }
    fn mirror_impl(
        &self,
        primitive_map: &PrimitiveMap,
        turbofish: bool,
    ) -> TokenStream {
        match self {
            TypeSpec::Declared(name, generic_params) => {
                if generic_params.is_empty() {
                    name.mirror_global(primitive_map)
                } else {
                    let name = name.mirror_global(primitive_map);
                    let params = generic_params
                        .iter()
                        .map(|param| param.mirror(primitive_map));
                    let turbofish = if turbofish {
                        quote!(::)
                    } else {
                        quote!()
                    };
                    quote!(#name #turbofish < #(#params),* >)
                }
            }
            TypeSpec::Generic(name) => {
                let name = name.mirror_local();
                quote!(#name)
            }
            TypeSpec::Tuple(inner) => {
                let members = inner.iter().map(|t| t.mirror(primitive_map));
                quote!(( #(#members),* ) )
            }
            TypeSpec::Array { inner, size } => {
                let inner = inner.mirror(primitive_map);
                let size = size.mirror(primitive_map);
                quote!([#inner; #size])
            }
            TypeSpec::Inverted(inner) => {
                // TODO: This is just flat out wrong, but needed for the prototype to compile
                inner.mirror_impl(primitive_map, turbofish)
            }
            // Wires are irrelevant to the testing system, we can just treat them as their non-wire
            // counterpart
            TypeSpec::Wire(w) => w.mirror_impl(primitive_map, turbofish),

            TypeSpec::TraitSelf(_) => {
                quote!()
            }
            TypeSpec::Wildcard(_) => {
                quote!()
            }
        }
    }
}

trait TypeDeclarationExt {
    fn mirror(
        &self,
        name: &NameID,
        primitive_map: &PrimitiveMap,
    ) -> Option<TokenStream>;
}

impl TypeDeclarationExt for TypeDeclaration {
    fn mirror(
        &self,
        name: &NameID,
        primitive_map: &PrimitiveMap,
    ) -> Option<TokenStream> {
        let generics = match self.generic_args.as_slice() {
            [] => quote! {},
            params => {
                let params = params.iter().map(|param| {
                    param.mirror(Some(quote!(
                        spade_marlin::type_translation::SpadeType
                    )))
                });
                quote! {< #(#params),* >}
            }
        };
        let raw_generics = self
            .generic_args
            .iter()
            .map(|param| param.name_id.mirror_local())
            .collect::<Vec<_>>();

        let impl_generics = match self.generic_args.as_slice() {
            [] => quote! {},
            _ => {
                quote! {< #(#raw_generics),* >}
            }
        };

        let def = match &self.kind {
            spade_hir::TypeDeclKind::Enum(_) => {
                let name = name.mirror_local();
                Some(quote! {
                    enum #name #generics {
                        A(std::marker::PhantomData<( #(#raw_generics),* )>)
                    }

                    impl #generics Default for #name<#(#raw_generics),*> {
                        fn default() -> Self {
                            #name::A(Default::default())
                        }
                    }
                })
            }
            spade_hir::TypeDeclKind::Primitive(_) => None,
            spade_hir::TypeDeclKind::Struct(s) => {
                let name = &self.name.mirror_local();

                let fields = s.members.0.iter().map(
                    |Parameter {
                         no_mangle: _,
                         name,
                         ty,
                         field_translator: _,
                     }| {
                        let name = format_ident!("{}", &name.0);
                        let ty = ty.mirror(primitive_map);

                        quote! {#name : #ty}
                    },
                );

                let sizes =
                    s.members.0.iter().map(|Parameter { ty, .. }| {
                        let ty = ty.mirror_with_turbofish(primitive_map);
                        quote!(#ty::size())
                    });
                let backward_sizes =
                    s.members.0.iter().map(|Parameter { ty, .. }| {
                        let ty = ty.mirror_with_turbofish(primitive_map);
                        quote!(#ty::backward_size())
                    });

                let field_updaters = s.members.0.iter().map(|param| {
                    let name = &param.name.mirror();
                    let ty = param.ty.mirror_with_turbofish(primitive_map);
                    quote! {
                        self.#name.from_verilator_value(bit_offset + local_offset, bits);
                        local_offset += #ty :: size();
                    }
                });

                let def = quote! {
                    #[derive(Default)]
                    pub struct #name #generics {
                        #(#fields),*
                    }

                    impl #generics spade_marlin::type_translation::SpadeType for #name #impl_generics {
                        fn size() -> usize {
                            #(#sizes)+*
                        }

                        fn backward_size() -> usize {
                            #(#backward_sizes)+*
                        }

                        fn from_verilator_value(&mut self, bit_offset: usize, bits: &[u32]) {
                            let mut local_offset = 0;
                            #(#field_updaters);*
                        }

                        fn to_verilator_value(&self, bit_offset: usize, target: &mut [u32]) {
                            unimplemented!("to_verilator_value is not implemented for structs yet")
                        }
                    }
                };
                Some(def)
            }
        };

        def
    }
}

trait TypeParamExt {
    fn mirror(&self, with_traits: Option<TokenStream>) -> TokenStream;
}
impl TypeParamExt for TypeParam {
    fn mirror(&self, with_traits: Option<TokenStream>) -> TokenStream {
        let name = self.name_id.mirror_local();
        match self.meta {
            spade_types::meta_types::MetaType::Type => {
                let with_traits = with_traits.map(|t| quote!(: #t));
                quote! {#name #with_traits}
            }
            spade_types::meta_types::MetaType::Int => {
                quote!(const #name: i64)
            }
            spade_types::meta_types::MetaType::Uint => {
                quote!(const #name: u64)
            }
            spade_types::meta_types::MetaType::Bool => {
                quote!(const #name: bool)
            }

            spade_types::meta_types::MetaType::Str => {
                panic!("Strings in type parameters are unsupported")
            }
            spade_types::meta_types::MetaType::Any => {
                panic!("Found an any meta-type in a type defintion")
            }
            spade_types::meta_types::MetaType::Number => {
                panic!("Found a number meta-type in a type defintion")
            }
        }
    }
}

enum ModEntry<'a> {
    Submod(&'a str, HashMap<&'a str, ModEntry<'a>>),
    Def(TokenStream),
}

impl<'a> ModEntry<'a> {
    fn emit(self) -> TokenStream {
        match self {
            ModEntry::Submod(name, inner) => {
                let members =
                    inner.into_iter().map(|(_, module)| module.emit());
                let name = format_ident!("{}", name);
                quote! {pub mod #name { #(#members)* }}
            }
            ModEntry::Def(def) => def,
        }
    }
}

pub fn primitive_map(compiler_state: &CompilerState) -> PrimitiveMap {
    let symtab = compiler_state.symtab.symtab();

    // TODO: More
    // TODO: Rewrite to use the type list not the symtab

    let primitives = [
        (
            ["uint"].as_slice(),
            quote! {spade_marlin::type_translation::SpadeUint},
        ),
        (["bool"].as_slice(), quote! {bool}),
        (
            ["std", "option", "Option"].as_slice(),
            quote! {std::option::Option},
        ),
    ]
    .into_iter()
    .map(|(name, value)| {
        (
            symtab
                .lookup_type_symbol(&Path::from_strs(name).nowhere())
                .expect(&format!(
                    "The `{name:?}` type was not defined in Spade"
                ))
                .0,
            value,
        )
    })
    .collect();

    primitives
}

pub fn mirror_types(compiler_state: &CompilerState) -> TokenStream {
    let primitives = primitive_map(compiler_state);

    let all_defs =
        compiler_state
            .item_list
            .types
            .iter()
            .filter_map(|(name, ty)| {
                ty.mirror(name, &primitives).map(|def| (name, def))
            });

    // We can't generate multiple modules, so we have to collect everything
    let mut modules = HashMap::new();

    for (name, def) in all_defs {
        let mut module = &mut modules;
        for segment in &name.1.0[0..(name.1.0.len() - 1)] {
            let ModEntry::Submod(_, next) =
                module.entry(segment.0.as_str()).or_insert(ModEntry::Submod(
                    segment.0.as_str(),
                    HashMap::new(),
                ))
            else {
                panic!(
                    "Found {segment} in {name} to be both a type and a module"
                )
            };
            module = next
        }

        module.insert(
            &name.1.0.last().expect("Found an empty path").0,
            ModEntry::Def(def),
        );
    }

    let result = ModEntry::Submod("spade_types", modules).emit();
    result 
}

