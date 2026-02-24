use std::collections::HashMap;

use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use spade::compiler_state::CompilerState;
use spade_common::{
    location_info::WithLocation,
    name::{Identifier, NameID, Path},
};
use spade_hir::{Parameter, TypeDeclaration, TypeExpression, TypeParam, TypeSpec};

type PrimitiveMap = HashMap<NameID, TokenStream>;

/// NameIDs always contain their fully qualified paths, but for some things, we want the
/// non-FQP, for example, for generic arguments. Hence the special mirror functions
trait NameIDExt {
    /// Translalte the fully qualified path into the corresponding Spade path
    /// (relative to the module where things will be inserted)
    fn mirror_global(&self, primitives: &PrimitiveMap) -> TokenStream;
    fn mirror_local(&self) -> TokenStream;
}

impl NameIDExt for NameID {
    fn mirror_global(&self, primitives: &PrimitiveMap) -> TokenStream {
        primitives.get(self).cloned().unwrap_or_else(|| {
            let full = format_ident!("spade_types");
            let here = self.1 .0.iter().map(|segment| {
                let s = format_ident!("{}", &segment.unwrap_named().as_str());
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
                .unwrap_named()
                .as_str()
        );
        quote!(#name)
    }
}

trait IdentExt {
    fn mirror(&self) -> TokenStream;
}
impl IdentExt for Identifier {
    fn mirror(&self) -> TokenStream {
        let name = format_ident!("{}", self.as_str());
        quote!(#name)
    }
}

trait Mirror {
    fn mirror(&self, primitive_map: &PrimitiveMap) -> TokenStream;
}

impl Mirror for TypeExpression {
    fn mirror(&self, primitive_map: &PrimitiveMap) -> TokenStream {
        match self {
            TypeExpression::TypeSpec(type_spec) => type_spec.mirror(primitive_map),
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
                panic!("String type parameters are not supported")
            }
            TypeExpression::Bool(_) => {
                panic!("Bool type parameters not supported")
            }
            TypeExpression::ConstGeneric(_) => {
                panic!("Const generics are not supported")
            }
        }
    }
}

pub trait TypeSpecExt {
    fn mirror(&self, primitive_map: &PrimitiveMap) -> TokenStream;
    fn mirror_with_turbofish(&self, primitive_map: &PrimitiveMap) -> TokenStream;
    fn mirror_impl(&self, primitive_map: &PrimitiveMap, turbofish: bool) -> TokenStream;
}

impl TypeSpecExt for TypeSpec {
    fn mirror(&self, primitive_map: &PrimitiveMap) -> TokenStream {
        self.mirror_impl(primitive_map, false)
    }
    fn mirror_with_turbofish(&self, primitive_map: &PrimitiveMap) -> TokenStream {
        self.mirror_impl(primitive_map, true)
    }
    fn mirror_impl(&self, primitive_map: &PrimitiveMap, turbofish: bool) -> TokenStream {
        match self {
            TypeSpec::Declared(name, generic_params) => {
                if generic_params.is_empty() {
                    name.mirror_global(primitive_map)
                } else {
                    let name = name.mirror_global(primitive_map);
                    let params = generic_params
                        .iter()
                        .map(|param| param.mirror(primitive_map));
                    let turbofish = if turbofish { quote!(::) } else { quote!() };
                    quote!(#name #turbofish < #(#params),* >)
                }
            }
            TypeSpec::Generic(name) => {
                let name = name
                    .name_id()
                    .expect("Found a hidden generic in a type signature")
                    .mirror_local();
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
    fn mirror(&self, name: &NameID, primitive_map: &PrimitiveMap) -> Option<TokenStream>;
}

impl TypeDeclarationExt for TypeDeclaration {
    fn mirror(&self, name: &NameID, primitive_map: &PrimitiveMap) -> Option<TokenStream> {
        let generics = match self.generic_args.as_slice() {
            [] => quote! {},
            params => {
                let params = params.iter().map(|param| {
                    param.mirror(Some(quote!(spade_marlin::type_translation::SpadeType)))
                });
                quote! {< #(#params),* >}
            }
        };
        let raw_generics = self
            .generic_args
            .iter()
            .map(|param| {
                param
                    .name_id()
                    .expect("Found a hidden generic")
                    .mirror_local()
            })
            .collect::<Vec<_>>();

        let impl_generics = match self.generic_args.as_slice() {
            [] => quote! {},
            _ => {
                quote! {< #(#raw_generics),* >}
            }
        };

        let def = match &self.kind {
            spade_hir::TypeDeclKind::Enum(e) => {
                let name = name.mirror_local();
                let options = e
                    .options
                    .iter()
                    .map(|(name, members)| {
                        let name = name.mirror_local();
                        let members = members
                            .0
                            .iter()
                            .map(|member| {
                                let name = member.name.mirror();
                                let ty = member.ty.mirror(primitive_map);
                                quote!(#name: #ty)
                            })
                            .collect::<Vec<_>>();
                        quote!(#name { #(#members),* })
                    })
                    .collect::<Vec<_>>();

                let default_impl = e.options.first().map(|(variant_name, params)| {
                    let variant_name = variant_name.mirror_local();
                    let params = params.0.iter().map(|param| {
                        let name = param.name.mirror();
                        quote!(#name: Default::default())
                    });

                    quote! {
                        impl #generics Default for #name <#(#raw_generics,)*> {
                            fn default() -> Self {
                                #name::#variant_name{#(#params),*}
                            }
                        }
                    }
                });

                let variant_sizes = e.options.iter().map(|(_, members)| {
                    if members.0.len() == 0 {
                        quote! {0}
                    } else {
                        let members = members.0.iter().map(|m| {
                            let ty = m.ty.mirror_with_turbofish(primitive_map);
                            quote!(#ty :: size())
                        });

                        quote! {#(#members)+*}
                    }
                })
                .collect::<Vec<_>>();
                let payload_size =
                    quote!([#(#variant_sizes),*].into_iter().max().unwrap_or_default());
                let tag_size = (e.options.len() as f32).log2().floor() as usize;

                let size = quote!(#tag_size + #payload_size);

                let variant_updaters =
                    e.options
                        .iter()
                        .enumerate()
                        .map(|(i, (variant_name, variant))| {
                            // Enums are packed msb first, so the indexing is "reversed"
                            // |tag| v1 | padding |
                            // |tag| v1 | v2      |
                            let variant_name = variant_name.mirror_local();

                            let prelude = quote! {
                                local_offset = #payload_size;
                            };

                            let field_updaters = variant.0.iter().map(|param| {
                                let name = &param.name.mirror();
                                let ty = param.ty.mirror_with_turbofish(primitive_map);
                                quote! {
                                    let mut #name = #ty::default();
                                    local_offset -= #ty :: size();
                                    #name.from_verilator_value(bit_offset + local_offset, bits);
                                }
                            });
                            let field_names = variant.0.iter().map(|param| param.name.mirror());
                            let construction = quote! {Self::#variant_name{#(#field_names),*}};

                            let i = i as u64;
                            let result = quote! {
                                #i => {
                                    #prelude
                                    #(#field_updaters;)*
                                    #construction
                                }
                            };
                            result
                        });

                let tag_size = tag_size as u64;
                let result = quote! {
                    #[derive(Debug, PartialEq)]
                    pub enum #name #generics {
                        #(#options),*
                    }

                    #default_impl

                    impl #generics spade_marlin::type_translation::SpadeType for #name #impl_generics {
                        fn size() -> usize {
                            #size
                        }

                        fn backward_size() -> usize {
                            0
                        }

                        fn from_verilator_value(&mut self, bit_offset: usize, bits: &[u32]) {
                            let mut local_offset = 0;
                            let mut tag = spade_marlin::type_translation::SpadeUint::<#tag_size>::default();
                            tag.from_verilator_value(bit_offset + #payload_size, bits);
                            *self = match *tag {
                                #(#variant_updaters,)*
                                _ => {Default::default()} // TODO: What the hell do we do here
                            };
                        }

                        fn to_verilator_value(&self, bit_offset: usize, target: &mut [u32]) {
                            unimplemented!("to_verilator_value is not implemented for enums yet")
                        }
                    }
                };
                Some(result)
            }
            spade_hir::TypeDeclKind::Primitive(_) => None,
            spade_hir::TypeDeclKind::Struct(s) => {
                let name = &self.name.mirror_local();

                // FIXME: Figure out which parameters need phantom data instead of blanket
                // phantom data'ing them
                let phantom_args = self
                    .generic_args
                    .iter()
                    .filter_map(|arg| {
                        match arg.meta {
                            spade_types::meta_types::MetaType::Type => {
                                Some(arg.name
                                    .name_id()
                                    .expect("Found hidden generic in type")
                                    .mirror_local())
                            },
                            spade_types::meta_types::MetaType::Any |
                            spade_types::meta_types::MetaType::Number |
                            spade_types::meta_types::MetaType::Int |
                            spade_types::meta_types::MetaType::Uint |
                            spade_types::meta_types::MetaType::Bool |
                            spade_types::meta_types::MetaType::Str => {
                                None
                            }
                        }
                    })
                    .collect::<Vec<_>>();

                let fields = s
                    .members
                    .0
                    .iter()
                    .map(
                        |Parameter {
                             no_mangle: _,
                             name,
                             ty,
                             field_translator: _,
                         }| {
                            let name = format_ident!("{}", &name.as_str());
                            let ty = ty.mirror(primitive_map);

                            quote! {#name : #ty}
                        },
                    )
                    .chain([quote!(phantom: std::marker::PhantomData<(#(#phantom_args),*)>)]);

                let sizes = s.members.0.iter().map(|Parameter { ty, .. }| {
                    let ty = ty.mirror_with_turbofish(primitive_map);
                    quote!(#ty::size())
                });
                let backward_sizes = s.members.0.iter().map(|Parameter { ty, .. }| {
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

                let size = if sizes.len() != 0 {
                    quote!(#(#sizes)+*)
                } else {
                    quote!(0)
                };
                let backward_size = if backward_sizes.len() != 0 {
                    quote!(#(#backward_sizes)+*)
                } else {
                    quote!(0)
                };

                let def = quote! {
                    #[derive(Default)]
                    pub struct #name #generics {
                        #(#fields),*
                    }

                    impl #generics spade_marlin::type_translation::SpadeType for #name #impl_generics {
                        fn size() -> usize {
                            #size
                        }

                        fn backward_size() -> usize {
                            #backward_size
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
            // FIXME: For now, we won't mirror type aliases
            spade_hir::TypeDeclKind::Alias(_) => None,
        };

        def
    }
}

trait TypeParamExt {
    fn mirror(&self, with_traits: Option<TokenStream>) -> TokenStream;
}
impl TypeParamExt for TypeParam {
    fn mirror(&self, with_traits: Option<TokenStream>) -> TokenStream {
        let name = self
            .name_id()
            .expect("Attempted to mirror a type with no generics")
            .mirror_local();
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
                let members = inner.into_iter().map(|(_, module)| module.emit());
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
        (
            ["int"].as_slice(),
            quote! {spade_marlin::type_translation::SpadeInt},
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
                .lookup_type_symbol(&Path::from_strs(name).nowhere(), false)
                .expect(&format!("The `{name:?}` type was not defined in Spade"))
                .0,
            value,
        )
    })
    .collect();

    primitives
}

pub fn mirror_types(compiler_state: &CompilerState) -> TokenStream {
    let primitives = primitive_map(compiler_state);

    let all_defs = compiler_state
        .item_list
        .types
        .iter()
        .filter_map(|(name, ty)| ty.mirror(name, &primitives).map(|def| (name, def)));

    // We can't generate multiple modules, so we have to collect everything
    let mut modules = HashMap::new();

    for (name, def) in all_defs {
        let mut module = &mut modules;
        for segment in &name.1 .0[0..(name.1 .0.len() - 1)] {
            let ModEntry::Submod(_, next) = module
                .entry(segment.unwrap_named().as_str())
                .or_insert(ModEntry::Submod(
                    segment.unwrap_named().as_str(),
                    HashMap::new(),
                ))
            else {
                panic!("Found {segment} in {name} to be both a type and a module")
            };
            module = next
        }

        module.insert(&name.1.tail().unwrap_named().as_str(), ModEntry::Def(def));
    }

    let result = ModEntry::Submod("spade_types", modules).emit();
    result
}
