use std::io::Write;

use spade_codespan_reporting::term::termcolor::Buffer;

use spade::Artefacts;
use spade_diagnostics::emitter::CodespanEmitter;
use spade_diagnostics::{CodeBundle, CompilationError, DiagHandler};

#[cfg(test)]
mod ast_lowering;
#[cfg(test)]
mod compiler_state;
#[cfg(test)]
mod const_generics;
#[cfg(test)]
mod hir_lowering;
#[cfg(test)]
mod integration;
#[cfg(test)]
mod linear_check;
#[cfg(test)]
mod mod_namespacing;
#[cfg(test)]
mod parser;
#[cfg(test)]
mod ports_integration;
#[cfg(test)]
mod suggestions;
#[cfg(test)]
mod typeinference;
#[cfg(test)]
mod usefulness;
#[cfg(test)]
mod verilator_wrapper;
#[cfg(test)]
mod wal_tracing;

// NOTE: word length inference tests no longer work after adding `int` and `uint`
// #[cfg(test)]
// mod wordlength_inference;

pub trait ResultExt<T> {
    fn report_failure(self, code: &str) -> T;
}
impl<T> ResultExt<T> for spade_hir_lowering::error::Result<T> {
    fn report_failure(self, code: &str) -> T {
        match self {
            Ok(t) => t,
            Err(e) => {
                let code_bundle = CodeBundle::new(code.to_string());
                let mut buffer = Buffer::no_color();
                let mut diag_handler = DiagHandler::new(Box::new(CodespanEmitter));
                e.report(&mut buffer, &code_bundle, &mut diag_handler);
                std::io::stderr().write_all(buffer.as_slice()).unwrap();
                panic!("Compilation error")
            }
        }
    }
}

#[macro_export]
#[cfg(test)]
macro_rules! build_entity {
    ($code:expr) => {{
        match build_items($code).as_slice() {
            [] => panic!("Found no entities"),
            [e] => e.clone(),
            _ => panic!("Found more than one entity"),
        }
    }};
}

#[macro_export]
macro_rules! snapshot_error {
    ($fn:ident, $src:literal) => {
        snapshot_error!($fn, $src, true);
    };
    ($fn:ident, {$({
        $namespace:expr,
        $base_namespace:expr,
        $src_file:literal,
        $src_content:literal$(,)*
    }),*$(,)?}, $include_stdlib:expr) => {
        #[test]
        fn $fn() {
            use tracing_subscriber::filter::{EnvFilter, LevelFilter};
            use tracing_subscriber::prelude::*;
            use tracing_tree::HierarchicalLayer;
            let env_filter = EnvFilter::builder()
                .with_default_directive(LevelFilter::OFF.into())
                .with_env_var("SPADE_LOG")
                .from_env_lossy();
            let layer = HierarchicalLayer::new(2)
                .with_targets(true)
                .with_writer(tracing_subscriber::fmt::TestWriter::new())
                .with_filter(env_filter);

            tracing_subscriber::registry().with(layer).try_init().ok();

            let mut buffer = spade_codespan_reporting::term::termcolor::Buffer::no_color();
            let opts = spade::Opt {
                error_buffer: &mut buffer,
                outfile: None,
                mir_output: None,
                verilator_wrapper_output: None,
                state_dump_file: None,
                item_list_file: None,
                print_type_traceback: std::env::var("SPADE_TRACE_TYPEINFERENCE").is_ok(),
                print_parse_traceback: std::env::var("SPADE_TRACE_PARSER").is_ok(),
                opt_passes: vec![]
            };

            let files = vec![
                $((
                    spade::ModuleNamespace {
                        namespace: $namespace,
                        base_namespace: $base_namespace,
                        file: $src_file.to_string(),
                    },
                    $src_file.to_string(),
                    unindent::unindent($src_content),
                )),*
            ];

            let _ = spade::compile(
                files,
                $include_stdlib,
                opts,
                spade_diagnostics::DiagHandler::new(Box::new(
                    spade_diagnostics::emitter::CodespanEmitter,
                )),
            );

            insta::with_settings!({
                // FIXME: Why can't we set 'description => source' here?
                omit_expression => true,
            }, {
                let all_code = vec![
                    $(unindent::unindent($src_content)),*
                ].join("\n");
                insta::assert_snapshot!(format!(
                    "{}\n\n{}",
                    all_code,
                    std::str::from_utf8(buffer.as_slice()).expect("error contains invalid utf-8")
                ));
            });
        }
    };
    ($fn:ident, $src:literal, $include_stdlib:expr) => {
        snapshot_error!(
            $fn, {
                {
                    spade_common::name::Path(vec![]),
                    spade_common::name::Path(vec![]),
                    "testinput",
                    $src,
                }
            }, $include_stdlib);
    };
}

#[macro_export]
macro_rules! code_compiles {
    ($fn:ident, $src:literal) => {
        #[test]
        fn $fn() {
            let code = $src;
            build_items(code);
        }
    };
}

#[macro_export]
macro_rules! snapshot_mir {
    ($fn:ident, $src:literal) => {
        #[test]
        fn $fn() {
            let code = $src;
            let items = build_items(code);
            insta::assert_snapshot!(format!("{}", items[0]))
        }
    };
}

#[macro_export]
macro_rules! snapshot_inference_error {
    ($fn:ident, $kind:literal, $src:literal) => {
        #[test]
        fn $fn() {
            use tracing_subscriber::filter::{EnvFilter, LevelFilter};
            use tracing_subscriber::prelude::*;
            use tracing_tree::HierarchicalLayer;
            let env_filter = EnvFilter::builder()
                .with_default_directive(LevelFilter::OFF.into())
                .with_env_var("SPADE_LOG")
                .from_env_lossy();
            let layer = HierarchicalLayer::new(2)
                .with_targets(true)
                .with_writer(tracing_subscriber::fmt::TestWriter::new())
                .with_filter(env_filter);

            tracing_subscriber::registry().with(layer).try_init().ok();

            let source = unindent::unindent($src);
            let mut buffer = codespan_reporting::term::termcolor::Buffer::no_color();
            let opts = spade::Opt {
                error_buffer: &mut buffer,
                outfile: None,
                mir_output: None,
                verilator_wrapper_output: None,
                state_dump_file: None,
                item_list_file: None,
                print_type_traceback: false,
                print_parse_traceback: false,
                wl_infer_method: match $kind {
                    "AA" => Some(InferMethod::AA),
                    "IA" => Some(InferMethod::IA),
                    "AAIA" => Some(InferMethod::AAIA),
                    "ONE" => None,
                    _ => panic!("Not a valid inference kind: {:?}", $kind),
                },
            };

            let files = vec![(
                    spade::ModuleNamespace {
                        namespace: spade_common::name::Path(vec![]),
                        base_namespace: spade_common::name::Path(vec![]),
                    },
                    "testinput".to_string(),
                    source.to_string(),
                )];

            let _ = spade::compile(
                files,
                true,
                opts,
                spade_diagnostics::DiagHandler::new(Box::new(
                    spade_diagnostics::emitter::CodespanEmitter,
                )),
            );

            insta::with_settings!({
                // FIXME: Why can't we set 'description => source' here?
                omit_expression => true,
            }, {
                insta::assert_snapshot!(format!(
                    "{}\n\n{}",
                    source,
                    std::str::from_utf8(buffer.as_slice()).expect("error contains invalid utf-8")
                ));
            });
        }
    };
}

#[cfg(test)]
fn build_items(code: &str) -> Vec<spade_mir::Entity> {
    build_items_inner(code, false)
}

#[cfg(test)]
fn build_items_with_stdlib(code: &str) -> Vec<spade_mir::Entity> {
    build_items_inner(code, true)
        .into_iter()
        .filter(|f| match &f.name.kind {
            spade_mir::unit_name::UnitNameKind::Unescaped(_) => true,
            spade_mir::unit_name::UnitNameKind::Escaped { name: _, path } => {
                !path.starts_with(&["std".to_string()])
            }
        })
        .collect()
}

/// Builds multiple items and types from a source string.
/// Panics if the compilation fails
/// Returns all MIR entities in unflattened format
#[cfg(test)]
fn build_items_inner(code: &str, with_stdlib: bool) -> Vec<spade_mir::Entity> {
    build_artifacts(code, with_stdlib).bumpy_mir_entities
}

pub fn build_artifacts(code: &str, with_stdlib: bool) -> Artefacts {
    let source = unindent::unindent(code);
    let mut buffer = spade_codespan_reporting::term::termcolor::BufferWriter::stdout(
        spade_codespan_reporting::term::termcolor::ColorChoice::Never,
    )
    .buffer();
    let opts = spade::Opt {
        error_buffer: &mut buffer,
        outfile: None,
        mir_output: None,
        verilator_wrapper_output: None,
        state_dump_file: None,
        item_list_file: None,
        print_type_traceback: std::env::var("SPADE_TRACE_TYPEINFERENCE").is_ok(),
        print_parse_traceback: false,
        opt_passes: vec![],
    };

    let files = vec![(
        spade::ModuleNamespace {
            namespace: spade_common::name::Path(vec![]),
            base_namespace: spade_common::name::Path(vec![]),
            file: "testinput".to_string(),
        },
        "testinput".to_string(),
        source,
    )];

    match spade::compile(
        files,
        with_stdlib,
        opts,
        spade_diagnostics::DiagHandler::new(Box::new(spade_diagnostics::emitter::CodespanEmitter)),
    ) {
        Ok(artefacts) => artefacts,
        Err(_) => {
            // I'm not 100% sure why this is needed. The bufferwriter should output
            // to stdout and buffer.flush() should be enough. Unfortunately, that does
            // not seem to be the case
            if !buffer.is_empty() {
                println!("{}", String::from_utf8_lossy(&buffer.into_inner()));
            }
            panic!("Compilation error")
        }
    }
}

/// Builds multiple entities and types from a source string, then compares the resulting
/// entities. $expected should be a vector of mir entities. If any pipelines or other
/// non-entities or types are included in $code, this panics
/// Sorts the entities by name to make deterministic
#[macro_export]
macro_rules! build_and_compare_entities {
    ($code:expr, $expected:expr, no_stdlib) => {
        build_and_compare_entities!($code, $expected, build_items)
    };
    ($code:expr, $expected:expr) => {
        build_and_compare_entities!($code, $expected, build_items_with_stdlib)
    };
    ($code:expr, $expected:expr, $build_function:ident) => {
        let mut result = $build_function($code);

        assert_eq!(
            $expected.len(),
            result.len(),
            "Expected {} entities, found {}",
            $expected.len(),
            result.len()
        );

        let mut expected = $expected.clone();
        expected.sort_by_key(|e| e.name.clone());
        result.sort_by_key(|e| e.name.clone());

        println!(
            "comparing {:?} with {:?}",
            expected.iter().map(|e| &e.name).collect::<Vec<_>>(),
            result.iter().map(|e| &e.name).collect::<Vec<_>>()
        );
        for (exp, res) in expected.into_iter().zip(result.into_iter()) {
            assert_same_mir!(&res, &exp);
        }
    };
}
