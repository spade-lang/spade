use std::fs::File;
use std::io::{prelude::*, stderr, IsTerminal};
use std::path::PathBuf;

use clap::Parser;
use color_eyre::eyre::{anyhow, bail, Context, Result};
use serde::Deserialize;
use spade_codespan_reporting::term::termcolor::Buffer;
use spade_diagnostics::emitter::CodespanEmitter;
use spade_diagnostics::DiagHandler;
use tracing_subscriber::filter::{EnvFilter, LevelFilter};
use tracing_subscriber::prelude::*;
use tracing_tree::HierarchicalLayer;

use spade::{
    namespaced_file::{dummy_file, namespaced_file, NamespacedFile},
    ModuleNamespace,
};

#[derive(Deserialize, Parser)]
#[structopt(name = "spade", about = "Compiler for the spade language")]
pub struct Opt {
    #[serde(skip, default = "dummy_file")]
    #[arg(name = "INPUT_FILE", value_parser(namespaced_file))]
    pub infile: NamespacedFile,
    #[serde(skip, default)]
    #[arg(name = "EXTRA_FILES", value_parser(namespaced_file))]
    pub extra_files: Vec<NamespacedFile>,
    #[structopt(short = 'o')]
    pub outfile: PathBuf,
    /// File to output the MIR for the generated modules. Primarily for debug purposes
    #[structopt(long)]
    pub mir_output: Option<PathBuf>,
    #[structopt(long)]
    pub verilator_wrapper_output: Option<PathBuf>,

    /// Do not include the standard library nor the prelude before compilation
    #[structopt(long)]
    pub omit_stdlib_and_prelude: bool,

    /// Do not include color in the error report
    #[structopt(long = "no-color")]
    pub no_color: bool,

    /// Write the compiler state required to continue adding modules to the project
    /// formatted in ron https://github.com/ron-rs/ron
    #[structopt(long)]
    pub state_dump: Option<PathBuf>,

    /// Write a list of all named items along with their corresponding verilog names
    /// to the specified file. See crate::name_dump for format
    #[structopt(long)]
    pub item_list: Option<PathBuf>,

    /// Print a traceback of the type inference process if type inference or hir lowering fails
    #[structopt(long = "print-type-traceback")]
    pub print_type_traceback: bool,
    /// Print a traceback of the parser if parsing fails
    #[structopt(long = "print-parse-traceback")]
    pub print_parse_traceback: bool,

    /// Read the arguments from the specified `.json` file instead of parsing the
    /// command line arguments
    #[structopt(long)]
    command_file: Option<PathBuf>,

    // List of optimization passes to apply globally
    #[structopt(long = "optimize")]
    opt_passes: Vec<String>,

    /// When command_file is used, use this field to specify a list of strings that will
    /// be decoded to NamespacedFile instead of using `infile` and `extra_files`
    #[structopt(skip)]
    files: Vec<String>,
}

fn main() -> Result<()> {
    let env_filter = EnvFilter::builder()
        .with_default_directive(LevelFilter::OFF.into())
        .with_env_var("SPADE_LOG")
        .from_env_lossy();
    let layer = HierarchicalLayer::new(2)
        .with_targets(true)
        .with_filter(env_filter);

    tracing_subscriber::registry().with(layer).init();

    let mut opts = Opt::parse();

    if let Some(command_file) = opts.command_file {
        let content = std::fs::read_to_string(&command_file)
            .with_context(|| format!("Failed to read commands from {command_file:?}"))?;
        opts = serde_json::from_str(&content)
            .with_context(|| format!("Failed to decode {command_file:?}"))?;

        let files = opts
            .files
            .iter()
            .map(|s| namespaced_file(s).map_err(|e| anyhow!("{e}")))
            .collect::<Result<Vec<_>>>()
            .with_context(|| format!("Failed to decode file list in {command_file:?}"))?;

        if files.is_empty() {
            bail!("File list in {command_file:?} contains no files")
        }

        opts.infile = files[0].clone();
        opts.extra_files = files[1..].to_vec();
    }

    let mut infiles = vec![opts.infile.clone()];
    infiles.append(&mut opts.extra_files);

    let sources: Result<Vec<(ModuleNamespace, String, String)>> = infiles
        .into_iter()
        .map(
            |NamespacedFile {
                 file: infile,
                 namespace,
                 base_namespace,
             }| {
                let mut file = File::open(&infile)
                    .with_context(|| format!("Failed to open {}", &infile.to_string_lossy()))?;
                let mut file_content = String::new();
                file.read_to_string(&mut file_content)?;
                Ok((
                    ModuleNamespace {
                        namespace,
                        base_namespace,
                        file: infile.to_string_lossy().to_string(),
                    },
                    infile.to_string_lossy().to_string(),
                    file_content,
                ))
            },
        )
        .collect();

    let mut buffer = if opts.no_color || !stderr().is_terminal() {
        Buffer::no_color()
    } else {
        Buffer::ansi() // FIXME: Use `Buffer::console()` on windows?
    };

    let spade_opts = spade::Opt {
        error_buffer: &mut buffer,
        outfile: Some(opts.outfile),
        mir_output: opts.mir_output,
        verilator_wrapper_output: opts.verilator_wrapper_output,
        state_dump_file: opts.state_dump,
        item_list_file: opts.item_list,
        print_type_traceback: opts.print_type_traceback,
        print_parse_traceback: opts.print_parse_traceback,
        opt_passes: opts.opt_passes,
    };

    let diag_handler = DiagHandler::new(Box::new(CodespanEmitter));
    match spade::compile(
        sources?,
        !opts.omit_stdlib_and_prelude,
        spade_opts,
        diag_handler,
    ) {
        Ok(_) => Ok(()),
        Err(_) => {
            std::io::stderr().write_all(buffer.as_slice())?;
            Err(anyhow!("aborting due to previous error"))
        }
    }
}
