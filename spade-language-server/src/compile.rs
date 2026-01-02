use std::sync::{Arc, Mutex};

use camino::Utf8Path;
use color_eyre::eyre::{bail, Context};
use rustc_hash::FxHashMap as HashMap;
use spade::{
    stdlib_and_prelude, Artefacts, CompilationResult, ModuleNamespace, UnfinishedArtefacts,
};
use spade_codespan_reporting::term::termcolor::Buffer;
use spade_common::location_info::{Loc, WithLocation};
use spade_common::name::{Identifier, PathSegment};
use spade_diagnostics::diagnostic::DiagnosticLevel as SpadeDiagnosticLevel;
use spade_diagnostics::Diagnostic as SpadeDiagnostic;
use spade_diagnostics::{CodeBundle, DiagHandler, Emitter};
use spade_hir::query::QueryCache;
use spade_hir::ItemList;
use spade_typeinference::traits::TraitImplList;
use swim::libraries::RestoreAction;
use swim::lockfile::LockFile;
use swim::spade::{Namespace, SpadeFile};
use swim::{libs_dir, lock_file, src_dir};
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::{
    Diagnostic, DiagnosticSeverity, Location, MessageType, SymbolInformation, SymbolKind, Url,
};

use crate::backend::ServerBackend;
use crate::backend_capabilities::util::loc_to_location;

struct LspDiagnosticsEmitter {
    /// All diagnostics and which file they are located in.
    diagnostics: Arc<Mutex<Vec<(Url, Diagnostic)>>>,
}

impl LspDiagnosticsEmitter {
    fn try_emit_diagnostic(
        &mut self,
        diag: &SpadeDiagnostic,
        code: &CodeBundle,
    ) -> color_eyre::Result<()> {
        let (span, file_id) = diag.labels.span;
        let Location { uri, range } = loc_to_location(Loc::new((), span, file_id), code)
            .with_context(|| format!("diagnostic was {diag:?}"))?;
        self.diagnostics.lock().unwrap().push((
            uri,
            Diagnostic {
                range,
                severity: Some(match diag.level {
                    SpadeDiagnosticLevel::Bug => DiagnosticSeverity::ERROR,
                    SpadeDiagnosticLevel::Error => DiagnosticSeverity::ERROR,
                    SpadeDiagnosticLevel::Warning => DiagnosticSeverity::WARNING,
                }),
                code: None,
                code_description: None,
                source: Some("Spade Language Server".to_string()),
                message: diag.labels.message.as_str().to_string(),
                related_information: None, // FIXME subdiagnostics here
                tags: None,
                data: None,
            },
        ));
        Ok(())
    }
}

impl Emitter for LspDiagnosticsEmitter {
    fn emit_diagnostic(&mut self, diag: &SpadeDiagnostic, _buffer: &mut Buffer, code: &CodeBundle) {
        match self.try_emit_diagnostic(diag, code) {
            Ok(()) => (),
            Err(_e) => {
                /*
                let client = Arc::clone(&self.client);
                Handle::current().spawn(async move {
                    client
                        .log_message(
                            MessageType::ERROR,
                            format!("Error emitting diagnostic: {e:?}"),
                        )
                        .await;
                });
                */
            }
        }
    }
}

fn spade_path(s: &str) -> spade_common::name::Path {
    if s.is_empty() {
        return spade_common::name::Path(vec![]);
    }
    let parts = s
        .split("::")
        .map(|ident| PathSegment::Named(Identifier::intern(ident).nowhere()))
        .collect();
    spade_common::name::Path(parts)
}

macro_rules! try_or_warn {
    ($expr:expr, $prefix:expr $(,)?) => {
        if let Err(e) = $expr {
            println!("{}{:#}", $prefix, e);
            return HashMap::default();
        } else {
            $expr.unwrap()
        }
    };
}

impl ServerBackend {
    pub async fn try_compile(
        &self,
        file: &Utf8Path,
        version: Option<i32>,
    ) -> HashMap<Url, Vec<Diagnostic>> {
        let maybe_root_dir = self.root_dir.lock().unwrap().as_ref().map(Clone::clone);
        // FIXME look upwards for swim.toml?
        let has_swim_toml = maybe_root_dir
            .as_ref()
            .map(|root_dir| root_dir.join("swim.toml").exists())
            .unwrap_or(false);

        match (maybe_root_dir, has_swim_toml) {
            (Some(root_dir), true) => {
                try_or_warn!(
                    self.try_compile_swim(&root_dir, version).await,
                    "When compiling swim project: ",
                )
            }
            (_, false) => {
                // Try to compile the "current" file.
                try_or_warn!(
                    self.try_compile_file(file, version).await,
                    format!("When compiling {file}: ")
                )
            }
            (None, true) => unreachable!("Can't have swim.toml without a root_dir to start from"),
        }
    }

    async fn try_compile_swim(
        &self,
        root_dir: &Utf8Path,
        version: Option<i32>,
    ) -> color_eyre::Result<HashMap<Url, Vec<Diagnostic>>> {
        let swim_toml = root_dir.join("swim.toml");
        if !swim_toml.exists() {
            bail!("swim.toml doesn't exist");
        }
        if !swim_toml.is_file() {
            bail!("swim.toml isn't a file");
        }
        /*
        self.client
            .log_message(MessageType::LOG, format!("Reading {swim_toml:?}"))
            .await;
        */
        let config = swim::config::Config::read(root_dir, &None)?;

        // Get Spade repository, which clones the compiler repository if needed. This ensures
        // we have the standard library on disk.
        swim::spade::get_spade_repository(root_dir, &config, RestoreAction::Deny)?;

        let mut lock_file = LockFile::open_or_default(lock_file(root_dir));
        let library_dirs = swim::libraries::collect_libraries(
            &libs_dir(root_dir),
            &config,
            &mut lock_file,
            RestoreAction::Deny,
        )?;
        let library_files: Vec<_> = library_dirs
            .iter()
            .map(|(name, dir)| swim::spade::spade_files_in_dir(Namespace::new_lib(&name), dir))
            .collect::<color_eyre::Result<Vec<_>>>()?
            .into_iter()
            .flatten()
            .collect();
        // NOTE: We deliberately do not filter the lock file at this stage, since we only want
        // user-run commands (like `swim build`) to change it.

        let self_files = swim::spade::spade_files_in_dir(
            Namespace::new_lib(&config.package.name),
            src_dir(root_dir),
        )?;

        let spade_files: Vec<_> = self_files.into_iter().chain(library_files).collect();

        self.try_compile_files(&spade_files, version).await
    }

    async fn try_compile_files(
        &self,
        files: &[SpadeFile],
        _version: Option<i32>,
    ) -> color_eyre::Result<HashMap<Url, Vec<Diagnostic>>> {
        let file_names: Vec<String> = files.iter().map(|f| f.path.to_string()).collect();
        let _ = self
            .client_log_chan
            .send((
                MessageType::LOG,
                format!("compiling {}", file_names.join(", ")),
            ))
            .await;

        let mut buffer = Buffer::no_color();
        let sources = files
            .iter()
            .map(|SpadeFile { namespace, path }| {
                let file_contents = std::fs::read_to_string(path)?;
                Ok((
                    ModuleNamespace {
                        namespace: spade_path(&namespace.namespace),
                        base_namespace: spade_path(&namespace.base_namespace),
                        file: path.to_string(),
                    },
                    path.to_string(),
                    file_contents,
                ))
            })
            .collect::<color_eyre::Result<Vec<_>>>()?
            .into_iter()
            .chain(stdlib_and_prelude())
            .collect::<Vec<_>>();
        let opts = spade::Opt {
            error_buffer: &mut buffer,
            outfile: None,
            mir_output: None,
            state_dump_file: None,
            item_list_file: None,
            print_type_traceback: false,
            print_parse_traceback: false,
            verilator_wrapper_output: None,
            opt_passes: vec![],
        };
        let diagnostics = Arc::new(Mutex::new(Vec::new()));
        let diag_handler = DiagHandler::new(Box::new(LspDiagnosticsEmitter {
            diagnostics: Arc::clone(&diagnostics),
        }));
        let compile_result = spade::compile(sources, false, opts, diag_handler);
        let diagnostics = std::mem::take(&mut *diagnostics.lock().unwrap());

        let mut diagnostics_per_file: HashMap<Url, Vec<Diagnostic>> = files
            .iter()
            .map(|spade_file| {
                (
                    Url::from_file_path(spade_file.path.to_path_buf().canonicalize_utf8().unwrap())
                        .unwrap(),
                    Vec::new(),
                )
            })
            .collect();
        for (file, diagnostic) in diagnostics {
            diagnostics_per_file
                .get_mut(&file)
                .unwrap()
                .push(diagnostic);
        }

        if !buffer.is_empty() {
            let _ = self
                .client_log_chan
                .send((
                    MessageType::LOG,
                    format!(
                        "Got a codespan-style error: {}",
                        String::from_utf8_lossy(buffer.as_slice())
                    ),
                ))
                .await;
        }

        match compile_result {
            Ok(artefacts) | Err(CompilationResult::LateFailure(artefacts)) => {
                let Artefacts {
                    code,
                    item_list,
                    type_states,
                    state,
                    impl_list,
                    ..
                } = artefacts;
                *self.code.lock().unwrap() = code;
                *self.query_cache.lock().unwrap() = QueryCache::from_item_list(&item_list);
                *self.item_list.lock().unwrap() = item_list;
                *self.type_states.lock().unwrap() = type_states;
                *self.symtab.lock().unwrap() = Some(state.symtab.unfreeze());
                *self.trait_impls.lock().unwrap() = impl_list;
            }
            Err(CompilationResult::EarlyFailure(UnfinishedArtefacts {
                code,
                item_list,
                type_states,
                symtab,
            })) => {
                *self.code.lock().unwrap() = code;
                *self.query_cache.lock().unwrap() = item_list
                    .as_ref()
                    .map(|item_list| QueryCache::from_item_list(&item_list))
                    .unwrap_or_else(|| QueryCache::empty());
                *self.item_list.lock().unwrap() = item_list.unwrap_or_else(|| ItemList::new());
                *self.type_states.lock().unwrap() = type_states.unwrap_or_default();
                *self.symtab.lock().unwrap() = symtab;
                *self.trait_impls.lock().unwrap() = Arc::new(TraitImplList::new());
            }
        }

        Ok(diagnostics_per_file)
    }

    async fn try_compile_file(
        &self,
        file: &Utf8Path,
        version: Option<i32>,
    ) -> color_eyre::Result<HashMap<Url, Vec<Diagnostic>>> {
        self.try_compile_files(
            &[SpadeFile {
                namespace: Namespace {
                    namespace: "proj".to_string(),
                    base_namespace: "proj".to_string(),
                },
                path: file.to_path_buf(),
            }],
            version,
        )
        .await
    }
    // Field 'deprecated' in SymbolInformation is deprecated (the irony!)
    // but we still have to specify it.
    #[allow(deprecated)]
    pub async fn get_lsp_symbols(&self) -> Result<Vec<SymbolInformation>> {
        let item_list = self.item_list.lock().unwrap();
        let code = &self.code.lock().unwrap();
        Ok(item_list
            .executables
            .iter()
            .filter_map(|(_id, executable)| match executable {
                spade_hir::ExecutableItem::EnumInstance {
                    base_enum: _,
                    variant: _,
                } => None,
                spade_hir::ExecutableItem::StructInstance => None,
                spade_hir::ExecutableItem::Unit(unit) => {
                    Some((unit.name.to_string(), unit.loc(), SymbolKind::FUNCTION))
                }
                spade_hir::ExecutableItem::ExternUnit(_, unit_head) => Some((
                    unit_head.name.to_string(),
                    unit_head.loc(),
                    SymbolKind::FUNCTION,
                )),
            })
            .filter_map(|(name, loc, kind)| {
                loc_to_location(loc, code)
                    // FIXME: Report error here (can't currently since it requires an async context).
                    .ok()
                    .map(|location| (name, location, kind))
            })
            .map(|(name, location, kind)| SymbolInformation {
                name,
                location,
                kind,
                tags: None,
                deprecated: None,
                // rust-analyzer uses crates for container_name
                container_name: None,
            })
            .collect())
    }
}
