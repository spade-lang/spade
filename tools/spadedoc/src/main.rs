use std::str::FromStr;

use argh::FromArgs;
use camino::Utf8PathBuf;
use color_eyre::eyre::bail;
use spade::namespaced_file::namespaced_file;
use spade::namespaced_file::NamespacedFile;
use tracing::metadata::LevelFilter;
use tracing_subscriber::prelude::*;
use tracing_subscriber::EnvFilter;
use tracing_tree::HierarchicalLayer;

struct NamespacedFileLocal(NamespacedFile);

impl FromStr for NamespacedFileLocal {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Self(namespaced_file(s)?))
    }
}

/// Generates HTML documentation for Spade code
#[derive(FromArgs)]
struct Spadedoc {
    /// documentation output directory; default "doc"
    #[argh(option, default = "Utf8PathBuf::from(\"doc\")")]
    output: Utf8PathBuf,

    /// the library to document (think --crate in rustdoc)
    #[argh(option)]
    lib: String,

    /// files to document
    #[argh(positional)]
    files: Vec<NamespacedFileLocal>,
}

fn main() -> color_eyre::Result<()> {
    color_eyre::install()?;

    let opts: Spadedoc = argh::from_env();

    let env_filter = EnvFilter::builder()
        .with_default_directive(LevelFilter::OFF.into())
        .with_env_var("SPADEDOC_LOG")
        .from_env_lossy();
    let layer = HierarchicalLayer::new(2)
        .with_targets(true)
        .with_filter(env_filter);

    tracing_subscriber::registry().with(layer).init();

    let files = opts
        .files
        .into_iter()
        .map(|file| file.0)
        .collect::<Vec<_>>();

    match spadedoc::doc(files, &opts.lib) {
        Ok(doc) => {
            spadedoc::renderer::Renderer::new(opts.output, &doc).render()?;
        }
        Err(buffer) => {
            eprintln!("{}", String::from_utf8_lossy(buffer.as_slice()));
            bail!("spade file failed to compile");
        }
    }

    Ok(())
}
