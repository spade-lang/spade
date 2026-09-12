// Copyright (C) 2024 Ethan Uppal.
//
// This Source Code Form is subject to the terms of the Mozilla Public License,
// v. 2.0. If a copy of the MPL was not distributed with this file, You can
// obtain one at https://mozilla.org/MPL/2.0/.

mod types;

use std::env;

use camino::Utf8PathBuf;
use marlin_verilator::{mangle_verilator_name, PortDirection};
use marlin_verilog_macro_builder::build_verilated_struct;
use num::ToPrimitive;
use proc_macro::TokenStream;
use quote::{format_ident, quote};

use proc_macro_error::{abort_call_site, proc_macro_error};
use spade::{self as spade_compiler, compiler_state::StoredCompilerState};
use spade_compiler::compiler_state::CompilerState;
use spade_hir::Input;
use spade_hir_lowering::{MirLowerable, UnitNameExt};
use syn::LitStr;
use types::mirror_types;

use crate::types::{primitive_map, TypeSpecExt};

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
    project_dir: Utf8PathBuf,
}

fn get_compiler_state() -> Result<SpadeInfo, syn::Error> {
    let manifest_directory =
        Utf8PathBuf::from(env::var("CARGO_MANIFEST_DIR").expect("Please use CARGO"));
    let Some(swim_toml) = search_for_swim_toml(manifest_directory) else {
        abort_call_site!("Could not find swim.toml")
    };
    let mut project_dir = swim_toml.clone();
    project_dir.pop();

    let state_file_path = project_dir.join("build/state.bincode");
    let state_file_content = match std::fs::read(&state_file_path) {
        Ok(state_file) => state_file,
        Err(e) => {
            abort_call_site!(format!("Failed to read {state_file_path}. {e}"))
        }
    };

    let compiler_state = match postcard::from_bytes::<StoredCompilerState>(&state_file_content) {
        Ok(state) => state.into_compiler_state(),
        Err(e) => {
            abort_call_site!(format!("Failed to decode build/state.bincode. {e}"))
        }
    };

    Ok(SpadeInfo {
        compiler_state,
        project_dir,
    })
}

#[proc_macro]
#[proc_macro_error]
pub fn spade_types(_args: TokenStream) -> TokenStream {
    let SpadeInfo {
        compiler_state,
        project_dir: _,
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
        project_dir,
    } = match get_compiler_state() {
        Ok(state) => state,
        Err(e) => return e.into_compile_error().into(),
    };

    let Some(top_unit) = compiler_state
        .item_list
        .executables
        .iter()
        .find_map(|(exec, item)| {
            if exec.1.to_strings() == args.top.value().split("::").collect::<Vec<_>>() {
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

    if !(top_unit.head.unit_type_params.is_empty() && top_unit.head.scope_type_params.is_empty()) {
        return syn::Error::new_spanned(
            args.top,
            format!("The module under test cannot be generic. Consider creating a non-generic test harness.")
        ).into_compile_error().into();
    }
    let type_state = compiler_state
        .mir_context
        .as_ref()
        .expect("This was made an Option I guess")
        .get(top_unit.name.name_id())
        .expect("Expected to find a mir_context for the top module")
        .type_state
        .clone();

    let primitive_map = primitive_map(&compiler_state);

    let verilog_source_path =
        { syn::LitStr::new(project_dir.join("build/spade.sv").as_str(), args.top.span()) };

    let mut ports = vec![];
    let mut input_fields = vec![];
    let mut extra_init = vec![];
    let mut pre_hooks = vec![];
    let mut post_hooks = vec![];
    for (Input{name, ty: hir_type, wire: _}, param) in top_unit.inputs.iter().zip(top_unit.head.inputs.0.clone()) {
        let ty = type_state
            .concrete_type_of_name(
                &name,
                compiler_state.symtab.symtab(),
                &compiler_state.item_list.types,
            )
            .expect("Expected a concrete type for {name}");

        let verilog_name = if param.no_mangle.is_some() {
            param.name.as_str().to_string()
        } else {
            format!("{}_i", param.name.as_str())
        };

        let mir_ty = ty.to_mir_type();

        let size = mir_ty
            .size()
            .to_usize()
            .expect("Types with more than 2^64 bits are unsupported");
        if size != 0 {
            ports.push((
                verilog_name.clone(), // Inclusive, like Verilog
                size - 1,
                0,
                PortDirection::Input,
            ));
        }

        let back_size = mir_ty
            .backward_size()
            .to_usize()
            .expect("Types with more than 2^64 bits are unsupported");
        let back_name = param.name.as_str().to_string() + "_o";
        if back_size != 0 {
            // TODO: Verify that this mangling scheme is correct
            ports.push((
                back_name.clone(),
                back_size - 1, // Inclusive, like Verilog
                0,
                PortDirection::Output,
            ));
        }

        let field_name = format_ident!("{}", param.name.as_str());
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
        syn::LitStr::new(&mangle_verilator_name(&top_name).unwrap(), args.top.span()),
        verilog_source_path,
        ports,
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

    let top = args.top;

    let project_dir_lit = LitStr::new(&project_dir.to_string(), top.span());

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

            project_dir: String,
        }

        impl<'a> #struct_name<'a> {
            pub fn new_simple(runtime: &'a SpadeRuntime) -> Result<Self, snafu::Whatever> {
                let model = runtime.create_model_simple()?;
                Ok(Self {
                    verilator: model,
                    i: Inputs {
                        #(#extra_init),*
                    },
                    project_dir: #project_dir_lit.to_string()
                })
            }

            pub fn new(runtime: &'a SpadeRuntime, config: crate::spade::SpadeModelConfig) -> Result<Self, snafu::Whatever> {
                let model = runtime.create_model(config)?;
                Ok(Self {
                    verilator: model,
                    i: Inputs {
                        #(#extra_init),*
                    },
                    project_dir: #project_dir_lit.to_string()
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

            pub fn open_vcd(&mut self, path: impl AsRef<std::path::Path>) -> spade_marlin::prelude::marlin::verilator::vcd::Vcd<'a> {
                let vcd_path = format!(
                    "{}/{}",
                    std::env::current_dir().expect("Failed to get current working directory").to_string_lossy(),
                    path.as_ref().to_string_lossy()
                );
                let surfer_ron_content = format!(
                    r#"(state_file:"{}/build/state.bincode",top_names:{{"{vcd_path}": "{}"}})"#,
                    self.project_dir,
                    #top,
                );
                let surfer_ron_path = format!("{}/build/surfer.ron", self.project_dir);

                // TODO: This will clash if there are multiple tests.
                std::fs::write(&surfer_ron_path, surfer_ron_content).expect(&format!("Failed to write surfer ron file to {surfer_ron_path}"));

                println!("Opening VCD file {vcd_path}");

                self.verilator.open_vcd(path)
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
