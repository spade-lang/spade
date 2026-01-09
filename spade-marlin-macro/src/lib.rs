// Copyright (C) 2024 Ethan Uppal.
//
// This Source Code Form is subject to the terms of the Mozilla Public License,
// v. 2.0. If a copy of the MPL was not distributed with this file, You can
// obtain one at https://mozilla.org/MPL/2.0/.

mod types;

use std::env;

use camino::Utf8PathBuf;
use marlin_verilator::{PortDirection, mangle};
use marlin_verilog_macro_builder::{
     build_verilated_struct,
};
use num::ToPrimitive;
use proc_macro::TokenStream;
use quote::{format_ident, quote};

use proc_macro_error::{abort_call_site, proc_macro_error};
use spade as spade_compiler;
use spade_compiler::compiler_state::CompilerState;
use spade_hir_lowering::{MirLowerable, UnitNameExt};
use types::mirror_types;

use crate::types::{TypeSpecExt, primitive_map};

// TODO: Move into a more general place
struct MacroArgs {
    pub top: syn::LitStr,
}

impl syn::parse::Parse for MacroArgs {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        syn::custom_keyword!(top);

        input.parse::<top>()?;
        input.parse::<syn::Token![=]>()?;
        let top = input.parse::<syn::LitStr>()?;

        Ok(Self { top })
    }
}

fn search_for_swim_toml(mut start: Utf8PathBuf) -> Option<Utf8PathBuf> {
    while start.parent().is_some() {
        if start.join("swim.toml").is_file() {
            return Some(start.join("swim.toml"));
        }
        start.pop();
    }
    None
}

struct SpadeInfo {
    compiler_state: CompilerState,
    source_path: Utf8PathBuf,
}

fn get_compiler_state() -> Result<SpadeInfo, syn::Error> {
    let manifest_directory = Utf8PathBuf::from(
        env::var("CARGO_MANIFEST_DIR").expect("Please use CARGO"),
    );
    let Some(swim_toml) = search_for_swim_toml(manifest_directory) else {
        abort_call_site!("Could not find swim.toml")
    };
    let mut source_path = swim_toml.clone();
    source_path.pop();

    let state_file_path = source_path.join("build/state.bincode");
    let state_file_content = match std::fs::read(&state_file_path) {
        Ok(state_file) => state_file,
        Err(e) => {
            abort_call_site!(format!("Failed to read {state_file_path}. {e}"))
        }
    };

    let (compiler_state, _) =
        match bincode::serde::decode_from_slice::<CompilerState, _>(
            &state_file_content,
            bincode::config::standard(),
        ) {
            Ok(state) => state,
            Err(e) => {
                abort_call_site!(format!("Failed to decode build/state.bincode. {e}"))
            }
        };

    Ok(SpadeInfo {
        compiler_state,
        source_path,
    })
}

#[proc_macro]
#[proc_macro_error]
pub fn spade_types(_args: TokenStream) -> TokenStream {
    let SpadeInfo {
        compiler_state,
        source_path: _,
    } = match get_compiler_state() {
        Ok(state) => state,
        Err(e) => return e.into_compile_error().into(),
    };

    let type_definitions = mirror_types(&compiler_state);

    type_definitions.into()
}

#[proc_macro_error]
#[proc_macro_attribute]
// TODO: This name is forced by the macro assuming that crate_name == macro name
pub fn spade_marlin(args: TokenStream, item: TokenStream) -> TokenStream {
    let args = syn::parse_macro_input!(args as MacroArgs);

    let SpadeInfo {
        compiler_state,
        source_path,
    } = match get_compiler_state() {
        Ok(state) => state,
        Err(e) => return e.into_compile_error().into(),
    };

    let Some(top_unit) =
        compiler_state
            .item_list
            .executables
            .iter()
            .find_map(|(exec, item)| {
                if exec.1.as_strs()
                    == args.top.value().split("::").collect::<Vec<_>>()
                {
                    Some(item)
                } else {
                    None
                }
            })
    else {
        return syn::Error::new_spanned(
            &args.top,
            format!(
                "Spade project did not contain {}.\nRemember to include the project name from `swim.toml` in the path",
                args.top.value()
            ),
        ).into_compile_error().into();
    };

    let top_unit = match top_unit {
        spade_hir::ExecutableItem::Unit(unit) => unit,
        spade_hir::ExecutableItem::ExternUnit(_, _) => {
            return syn::Error::new_spanned(
                args.top,
                format!("Top unit is an extern unit, which cannot be tested"),
            )
            .into_compile_error()
            .into();
        }
        spade_hir::ExecutableItem::EnumInstance { .. } => {
            return syn::Error::new_spanned(
                args.top,
                format!("Top unit is an enum variant, which cannot be tested"),
            )
            .into_compile_error()
            .into();
        }
        spade_hir::ExecutableItem::StructInstance => {
            return syn::Error::new_spanned(
                args.top,
                format!("Top unit is a struct, which cannot be tested"),
            )
            .into_compile_error()
            .into();
        }
    };

    if !(top_unit.head.unit_type_params.is_empty()
        && top_unit.head.scope_type_params.is_empty())
    {
        return syn::Error::new_spanned(
            args.top,
            format!("The module under test cannot be generic. Consider creating a non-generic test harness.")
        ).into_compile_error().into();
    }
    let type_state = compiler_state
        .mir_context
        .get(top_unit.name.name_id())
        .expect("Expected to find a mir_context for the top module")
        .type_state
        .clone();

    let primitive_map = primitive_map(&compiler_state);

    let verilog_source_path = {
        syn::LitStr::new(
            source_path.join("build/spade.sv").as_str(),
            args.top.span(),
        )
    };

    let mut ports = vec![];
    let mut input_fields = vec![];
    let mut extra_init = vec![];
    let mut pre_hooks = vec![];
    let mut post_hooks = vec![];
    for ((name, hir_type), param) in
        top_unit.inputs.iter().zip(top_unit.head.inputs.0.clone())
    {
        let ty = type_state
            .concrete_type_of_name(
                &name,
                compiler_state.symtab.symtab(),
                &compiler_state.item_list.types,
            )
            .expect("Expected a concrete type for {name}");

        let verilog_name = if param.no_mangle.is_some() {
            param.name.0.to_string()
        } else {
            format!("{}_i", param.name.0)
        };

        let mir_ty = ty.to_mir_type();

        let size = mir_ty
            .size()
            .to_usize()
            .expect("Types with more than 2^64 bits are unsupported");
        if size != 0 {
            ports.push(
                (
                    verilog_name.clone(), // Inclusive, like Verilog
                    size - 1,
                    0,
                    PortDirection::Input,
                ),
            );
        }

        let back_size = mir_ty
            .backward_size()
            .to_usize()
            .expect("Types with more than 2^64 bits are unsupported");
        let back_name = param.name.0.clone() + "_o";
        if back_size != 0 {
            // TODO: Verify that this mangling scheme is correct
            ports.push(
                (
                    back_name.clone(),
                    back_size - 1, // Inclusive, like Verilog
                    0,
                    PortDirection::Output,
                )
            );
        }

        let field_name = format_ident!("{}", param.name.inner.0);
        let field_ty = hir_type.mirror(&primitive_map);
        input_fields.push(quote! {
            pub #field_name: #field_ty
        });
        extra_init.push(quote! {
            #field_name: Default::default()
        });

        if size != 0 {
            let verilog_name = format_ident!("{verilog_name}");
            let num_u32_chunks = size / 32 + 1;
            pre_hooks.push(quote!{
                let mut buffer = [0; #num_u32_chunks];
                crate::spade::type_translation::SpadeType::to_verilator_value(&mut self.i.#field_name, 0, &mut buffer);
                spade_marlin::type_ext::IntoU32s::update_from_u32(&mut self.verilator.#verilog_name, &buffer);
            });
        }

        if back_size != 0 {
            let verilog_name = format_ident!("{back_name}");
            let num_u32_chunks = back_size / 32 + 1;
            post_hooks.push(quote!{
                let mut buffer = [0; #num_u32_chunks];
                spade_marlin::type_ext::IntoU32s::populate_u32(&self.verilator.#verilog_name, &mut buffer);
                crate::spade::type_translation::SpadeType::from_verilator_value(&mut self.i.#field_name, 0, &mut buffer)
            });
        }
    }

    let top_name = top_unit.name.as_mir();
    let top_name = top_name.without_escapes();
    let verilator = build_verilated_struct(
        "spade",
        syn::LitStr::new(
            &mangle(&top_name).unwrap(),
            args.top.span(),
        ),
        verilog_source_path,
        ports,
        None,
        None,
        item.clone().into(),
    );

    let item = match syn::parse::<syn::ItemStruct>(item.into()) {
        Ok(item) => item,
        Err(error) => {
            return error.into_compile_error().into();
        }
    };
    
    let struct_name = item.ident;
    let mod_name = format_ident!("{}_impl", struct_name);

    let spade_wrapper = quote! {
        struct Inputs {
            #(#input_fields),*
        }
        struct #struct_name<'a> {
            // NOTE: This name relies on Marlin internals for now
            // The underlying Verilog struct, to which we set inputs and outputs,
            // and run eval. Since our hooks overwrite the values set on inputs,
            // we cannot grant mutable access to it externally
            verilator: #mod_name :: #struct_name<'a>,
            pub i: Inputs,
        }

        impl<'a> #struct_name<'a> {
            pub fn new_simple(runtime: &'a SpadeRuntime) -> Result<Self, snafu::Whatever> {
                let model = runtime.create_model_simple()?;
                Ok(Self {
                    verilator: model,
                    i: Inputs {
                        #(#extra_init),*
                    }
                })
            }

            pub fn eval(&mut self) {
                #(#pre_hooks);*
                self.verilator.eval();
                #(#post_hooks);*
            }

            pub fn verilator(&self) -> &#mod_name :: #struct_name {
                &self.verilator
            }
        }
    };

    quote::quote! {
        #[allow(non_snake_case)]
        #[doc(hidden)]
        mod #mod_name {
            use super::*;
            pub(super) #verilator
        }

        #spade_wrapper
    }
    .into()
}
