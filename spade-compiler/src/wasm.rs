use codespan_reporting::term::termcolor::Buffer;
use color_eyre::{
    eyre::{anyhow, bail, Context},
    Result,
};
use logos::Logos;
use spade_common::name::Path;
use spade_diagnostics::{emitter::CodespanEmitter, DiagHandler};
use spade_parser::{lexer, Parser};
use wasm_bindgen::prelude::wasm_bindgen;

use crate::{namespaced_file::namespaced_file, ModuleNamespace, Opt};

#[wasm_bindgen]
pub struct File {
    /// Namespace where this file belongs
    pub(crate) namespace: String,
    pub(crate) base_namespace: String,
    pub(crate) filename: String,
    pub(crate) file_content: String,
}

#[wasm_bindgen]
impl File {
    #[wasm_bindgen(constructor)]
    pub fn new(
        namespace: String,
        base_namespace: String,
        filename: String,
        file_content: String,
    ) -> Self {
        Self {
            namespace,
            base_namespace,
            filename,
            file_content,
        }
    }
}

pub fn parse_path(path: &str) -> Result<Path> {
    let mut root_parser = Parser::new(lexer::TokenKind::lexer(path), 0);
    Ok(root_parser
        .path()
        .with_context(|| format!("Failed to parse path"))?
        .inner)
}

pub fn compile_inner(sources: Vec<File>) -> Result<String> {
    let sources: Vec<(ModuleNamespace, String, String)> = sources
        .iter()
        .map(|s| {
            let ns = ModuleNamespace {
                namespace: parse_path(&s.namespace)?,
                base_namespace: parse_path(&s.base_namespace)?,
            };

            Ok((ns, s.filename.to_string(), s.file_content.to_string()))
        })
        .collect::<Result<Vec<_>>>()?;

    let mut buffer = Buffer::no_color();
    let diag_handler = DiagHandler::new(Box::new(CodespanEmitter));

    let opts = Opt {
        outfile: None,
        mir_output: None,
        verilator_wrapper_output: None,
        state_dump_file: None,
        item_list_file: None,
        print_type_traceback: false,
        print_parse_traceback: false,
        wl_infer_method: None,
    };

    crate::compile_inner(sources, true, &opts, &mut buffer, diag_handler)
        .map(|artefacts| artefacts.codegen_artefacts.module_code.join("\n\n"))
        .map_err(|_| anyhow!("{}", String::from_utf8_lossy(&buffer.into_inner())))
}

/// Compile a list of files into a `spade.sv` that is returned as a string. The files
/// use the same format as [namespaced_file::namespaced_file]
#[wasm_bindgen]
pub fn compile(sources: Vec<File>) -> std::result::Result<String, String> {
    compile_inner(sources).map_err(|e| format!("{e:#?}"))
}
