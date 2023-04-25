use std::fs::File;
use std::io::prelude::*;
use std::path::PathBuf;

use clap::Parser;
use codespan_reporting::term::termcolor::Buffer;
use color_eyre::eyre::{anyhow, Context, Result};
use spade_diagnostics::emitter::CodespanEmitter;
use spade_diagnostics::DiagHandler;
use tracing_subscriber::filter::{EnvFilter, LevelFilter};
use tracing_subscriber::prelude::*;
use tracing_tree::HierarchicalLayer;

use spade::{
    namespaced_file::{namespaced_file, NamespacedFile},
    ModuleNamespace,
};

#[derive(Parser)]
#[structopt(name = "spade", about = "Compiler for the spade language")]
pub struct Opt {
    #[structopt(name = "INPUT_FILE", parse(try_from_str = namespaced_file))]
    pub infile: NamespacedFile,
    #[structopt(name = "EXTRA_FILES", parse(try_from_str = namespaced_file))]
    pub extra_files: Vec<NamespacedFile>,
    #[structopt(short = 'o')]
    pub outfile: PathBuf,
    /// File to output the MIR for the generated modules. Primarily for debug purposes
    #[structopt(long)]
    pub mir_output: Option<PathBuf>,
    /// Do not include color in the error report
    #[structopt(long = "no-color")]
    pub no_color: bool,

    /// Use (currently experimental) affine arithmetic to check integer bounds stricter than
    /// previously possible.
    #[structopt(long)]
    pub use_aa: bool,

    /// Write a mapping between expression ids/names and the types of the values
    /// formatted in ron https://github.com/ron-rs/ron
    #[structopt(long)]
    pub type_dump: Option<PathBuf>,

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
                    },
                    infile.to_string_lossy().to_string(),
                    file_content,
                ))
            },
        )
        .collect();

    let mut buffer = if opts.no_color || atty::isnt(atty::Stream::Stderr) {
        Buffer::no_color()
    } else {
        Buffer::ansi() // FIXME: Use `Buffer::console()` on windows?
    };

    let spade_opts = spade::Opt {
        error_buffer: &mut buffer,
        outfile: Some(opts.outfile),
        mir_output: opts.mir_output,
        type_dump_file: opts.type_dump,
        state_dump_file: opts.state_dump,
        item_list_file: opts.item_list,
        print_type_traceback: opts.print_type_traceback,
        print_parse_traceback: opts.print_parse_traceback,
        use_aa: opts.use_aa,
    };

    let diag_handler = DiagHandler::new(Box::new(CodespanEmitter));
    match spade::compile(sources?, true, spade_opts, diag_handler) {
        Ok(_) => Ok(()),
        Err(_) => {
            std::io::stderr().write_all(buffer.as_slice())?;
            Err(anyhow!("aborting due to previous error"))
        }
    }
}
