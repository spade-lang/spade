pub mod compiler_state;
pub mod error_handling;
mod name_dump;
pub mod namespaced_file;

use compiler_state::{CompilerState, MirContext};
use error_handling::{ErrorHandler, Reportable};
use itertools::Itertools;
use rayon::prelude::*;
use rustc_hash::FxHashMap as HashMap;
use spade_ast_lowering::id_tracker::ExprIdTracker;
use spade_codespan_reporting::term::termcolor::Buffer;
use spade_common::location_info::{Loc, WithLocation};
pub use spade_common::namespace::ModuleNamespace;
use spade_diagnostics::diag_list::{DiagList, ResultExt};
use spade_hir::expression::Safety;
use spade_hir_lowering::inline::do_inlining;
use spade_mir::codegen::{Codegenable, cocotb_code, prepare_codegen};
use spade_mir::passes::MirPass;
use spade_mir::passes::deduplicate_mut_wires::DeduplicateMutWires;
use spade_mir::unit_name::InstanceMap;
use spade_mir::verilator_wrapper::verilator_wrappers;
use spade_typeinference::traits::TraitImplList;
use std::collections::BTreeMap;
use std::io::Write;
use std::path::PathBuf;
use std::sync::{Arc, Mutex, RwLock};
use tracing::Level;
use typeinference::TypeState;

use spade_ast::{FloatingNodes, MacroRules, ModuleBody};
use spade_ast_lowering::{
    Context as AstLoweringCtx, SelfContext, auto_traits, ensure_unique_anonymous_traits,
    global_symbols, visit_module_body,
};
use spade_common::id_tracker::{GenericIdTracker, ImplIdTracker};
use spade_common::name::{NameID, Path as SpadePath, Visibility};
use spade_diagnostics::{CodeBundle, DiagHandler, Diagnostic};
use spade_hir::symbol_table::{FrozenSymtab, SymbolTable};
use spade_hir::{ExecutableItem, ItemList};
use spade_hir_lowering::{NameSourceMap, monomorphisation::MirOutput};
use spade_parser::Parser;
use spade_typeinference::{self as typeinference, SharedTypeState};

pub struct Opt<'b> {
    pub error_buffer: &'b mut Buffer,
    pub outfile: Option<PathBuf>,
    pub mir_output: Option<PathBuf>,
    pub verilator_wrapper_output: Option<PathBuf>,
    pub state_dump_file: Option<PathBuf>,
    pub item_list_file: Option<PathBuf>,
    /// Print the parsing traceback for any files which contain the specified
    /// string
    pub print_parse_traceback: Option<String>,
    pub opt_passes: Vec<String>,
}

/// Compiler output.
pub struct Artefacts {
    pub code: CodeBundle,
    // MIR entities before aliases have been flattened
    pub bumpy_mir_entities: Option<Vec<spade_mir::Entity>>,
    pub item_list: ItemList,
    pub state: CompilerState,
    pub impl_list: TraitImplList,
    pub type_states: BTreeMap<NameID, TypeState>,
    pub floating_nodes: FloatingNodes,
}

/// Like [Artefacts], but if the compiler didn't finish due to errors.
pub struct UnfinishedArtefacts {
    pub code: Arc<RwLock<CodeBundle>>,
    pub symtab: Option<SymbolTable>,
    pub item_list: Option<ItemList>,
    pub floating_nodes: Option<FloatingNodes>,
    pub type_states: Option<BTreeMap<NameID, TypeState>>,
}

pub enum CompilationResult {
    EarlyFailure(UnfinishedArtefacts),
    LateFailure(Artefacts),
}

struct CodegenArtefacts {
    flat_mir_entities: Vec<Codegenable>,
    bumpy_mir_entities: Vec<spade_mir::Entity>,
    module_code: Vec<String>,
    mir_code: Vec<String>,
    instance_map: InstanceMap,
    mir_context: HashMap<NameID, MirContext>,
}

/// The state of the compiler after having `run_global_compilation_tasks`. Using this
/// the bodies of units can be built independently.
pub struct GlobalCompilationState {
    item_list: ItemList,
    impl_type_state: TypeState,
    frozen_symtab: FrozenSymtab,
    idtracker: Arc<ExprIdTracker>,
    mapped_trait_impls: TraitImplList,
    shared_type_state: Arc<SharedTypeState>,
    impl_idtracker: ImplIdTracker,
    generic_idtracker: GenericIdTracker,
    floating_nodes: FloatingNodes,
    macros: HashMap<NameID, MacroRules>,
}

pub enum GlobalCompilationError {
    EarlyFailure,
}

/// Run enough of the compilation process on all files included in the project in order
/// to independently be able to re-run compilation on the bodies of entities.
pub fn run_global_compilation_tasks(
    sources: Vec<(ModuleNamespace, String, String)>,
    code: Arc<RwLock<CodeBundle>>,
    errors: &mut ErrorHandler,
    unfinished_artefacts: &mut UnfinishedArtefacts,
    print_parse_traceback: Option<String>,
) -> Result<GlobalCompilationState, GlobalCompilationError> {
    let diags = Arc::new(Mutex::new(DiagList::new()));
    let mut symtab = SymbolTable::new(diags.clone());
    let mut item_list = ItemList::new();

    spade_ast_lowering::builtins::populate_symtab(&mut symtab, &mut item_list);

    let (module_asts, floating_nodes) = parse(sources, Arc::clone(&code), print_parse_traceback, errors);
    errors.errors_are_recoverable();

    unfinished_artefacts.floating_nodes = Some(floating_nodes.clone());

    let mut ctx = AstLoweringCtx {
        symtab,
        item_list,
        macros: HashMap::default(),
        code,
        idtracker: Arc::new(ExprIdTracker::new()),
        impl_idtracker: ImplIdTracker::new(),
        generic_idtracker: GenericIdTracker::new(),
        pipeline_ctx: None,
        self_ctx: SelfContext::FreeStanding,
        current_unit: None,
        diags: diags.clone(),
        safety: Safety::Default,
    };

    // Add all "root" project main.spade modules
    for root in module_asts
        .iter()
        .filter(|(ns, _ast)| ns.base_namespace == ns.namespace)
    {
        let namespace = &root.0;
        if !namespace.namespace.0.is_empty() {
            let name_id = ctx.symtab.add_thing(
                namespace.namespace.clone(),
                spade_hir::symbol_table::Thing::Module(
                    ().nowhere(),
                    namespace.namespace.0.last().unwrap().unwrap_named().clone(),
                ),
                Some(Visibility::Implicit.nowhere()),
                None,
            );
            ctx.item_list.modules.insert(
                name_id.clone(),
                spade_hir::Module {
                    name: name_id.at_loc(&root.1),
                    documentation: "".to_string(),
                },
            );
        }
    }

    for (namespace, module_ast) in &module_asts {
        do_in_namespace(namespace, &mut ctx, &mut |ctx| {
            global_symbols::gather_macro_rules(module_ast, ctx).or_report(errors);
        })
    }

    let mut missing_namespace_set = module_asts
        .iter()
        .map(|(ns, _ast)| (ns.namespace.clone(), ns.file.clone()))
        .collect::<HashMap<_, _>>();

    for (namespace, module_ast) in &module_asts {
        do_in_namespace(namespace, &mut ctx, &mut |ctx| {
            global_symbols::handle_external_modules(
                &namespace.file,
                None,
                module_ast,
                &mut missing_namespace_set,
                ctx,
            )
            .or_report(errors);
        })
    }

    if errors.failed_now() {
        unfinished_artefacts.symtab = Some(ctx.symtab);
        return Err(GlobalCompilationError::EarlyFailure);
    }

    for err in global_symbols::report_missing_mod_declarations(&module_asts, &missing_namespace_set)
    {
        errors.report(&err);
    }

    errors.errors_are_recoverable();

    for (namespace, module_ast) in &module_asts {
        do_in_namespace(namespace, &mut ctx, &mut |ctx| {
            global_symbols::gather_traits_and_modules(module_ast, ctx).or_report(errors);
        })
    }
    for (namespace, module_ast) in &module_asts {
        do_in_namespace(namespace, &mut ctx, &mut |ctx| {
            global_symbols::gather_types(module_ast, ctx).or_report(errors);
        })
    }

    errors.drain_diag_list(&mut ctx.diags.lock().unwrap());
    if errors.failed_now() {
        unfinished_artefacts.symtab = Some(ctx.symtab);
        return Err(GlobalCompilationError::EarlyFailure);
    }

    for (namespace, module_ast) in &module_asts {
        do_in_namespace(namespace, &mut ctx, &mut |ctx| {
            global_symbols::gather_symbols(module_ast, ctx).or_report(errors);
        })
    }

    unfinished_artefacts.item_list = Some(ctx.item_list.clone());
    errors.drain_diag_list(&mut ctx.diags.lock().unwrap());

    if errors.failed_now() {
        unfinished_artefacts.symtab = Some(ctx.symtab);
        return Err(GlobalCompilationError::EarlyFailure);
    }

    lower_ast(&module_asts, &mut ctx, errors);

    auto_traits::impl_auto_traits(&mut ctx).handle_in(&mut diags.lock().unwrap());

    errors.drain_diag_list(&mut ctx.diags.lock().unwrap());
    if errors.failed_now() {
        unfinished_artefacts.symtab = Some(ctx.symtab);
        return Err(GlobalCompilationError::EarlyFailure);
    }

    let AstLoweringCtx {
        symtab,
        mut item_list,
        macros,
        code: _,
        idtracker,
        impl_idtracker,
        generic_idtracker,
        pipeline_ctx: _,
        self_ctx: _,
        current_unit: _,
        diags,
        safety: _,
    } = ctx;

    errors.drain_diag_list(&mut diags.lock().unwrap());

    for e in ensure_unique_anonymous_traits(&mut item_list) {
        errors.report(&e)
    }

    let frozen_symtab = symtab.freeze();

    let shared_type_state = Arc::new(SharedTypeState::new());
    let mut impl_type_state = TypeState::fresh(Arc::clone(&shared_type_state));

    let mut type_inference_ctx = typeinference::Context {
        symtab: frozen_symtab.symtab(),
        items: &item_list,
        trait_impls: &TraitImplList::new(),
    };

    // NOTE: feels hacky but does the job
    let (mapped_trait_impls, obligations) = impl_type_state
        .visit_impl_blocks(&item_list, &type_inference_ctx)
        .split();
    type_inference_ctx.trait_impls = &mapped_trait_impls;

    obligations
        .resolve_obligations(&mut impl_type_state, &type_inference_ctx)
        .handle_in(&mut impl_type_state.owned.diags);

    errors.drain_diag_list(&mut impl_type_state.owned.diags);

    Ok(GlobalCompilationState {
        item_list,
        impl_type_state,
        frozen_symtab,
        idtracker,
        mapped_trait_impls,
        shared_type_state,
        impl_idtracker,
        generic_idtracker,
        macros,
        floating_nodes,
    })
}

pub struct LocalCompilationResult {
    type_states: BTreeMap<NameID, TypeState>,
    mir_entities: Vec<Result<MirOutput, Diagnostic>>,
    name_source_map: Arc<RwLock<NameSourceMap>>,
}

pub fn run_local_compilation_steps(
    only_in_file: Option<usize>,
    global_state: &GlobalCompilationState,
    errors: &mut ErrorHandler,
    opt_passes: &Vec<&(dyn MirPass + Send + Sync)>,
) -> Result<LocalCompilationResult, CompilationResult> {
    let mut type_states = BTreeMap::new();

    let type_inference_ctx = typeinference::Context {
        symtab: global_state.frozen_symtab.symtab(),
        items: &global_state.item_list,
        trait_impls: &global_state.mapped_trait_impls,
    };

    let executables_and_types = global_state
        .item_list
        .executables
        .iter()
        .filter_map(|(name, item)| match item {
            ExecutableItem::Unit(u) => {
                if only_in_file.map(|file| file == u.file_id).unwrap_or(true) {
                    let mut type_state = global_state.impl_type_state.create_child();

                    let result = type_state.visit_unit(u, &type_inference_ctx).report(errors);

                    let failures = type_state.owned.diags.errors.len() != 0;
                    errors.drain_diag_list(&mut type_state.owned.diags);

                    // Later stages will fail if we don't have a a complete type state,
                    // so we'll need to filter out modules that failed. However, for the LSP
                    // we still want to retain the incomplete type state
                    type_states.insert(name.clone(), type_state.clone());

                    if let Ok(()) = result {
                        type_state.emit_trace_if_enabled(|| {}, &u.name);
                        if !failures {
                            Some((name, (item, type_state)))
                        } else {
                            None
                        }
                    } else {
                        type_state.emit_trace_if_enabled(|| {}, &u.name);
                        None
                    }
                } else {
                    None
                }
            }
            ExecutableItem::EnumInstance { .. } => None,
            ExecutableItem::StructInstance => None,
            ExecutableItem::ExternUnit(_, _) => None,
        })
        .collect::<BTreeMap<_, _>>();

    let name_source_map = Arc::new(RwLock::new(NameSourceMap::new()));
    let mir_entities = spade_hir_lowering::monomorphisation::compile_items(
        &executables_and_types,
        &global_state.frozen_symtab,
        &global_state.idtracker,
        &name_source_map,
        &global_state.item_list,
        &opt_passes,
        &global_state.impl_type_state,
        &global_state.mapped_trait_impls,
    );

    Ok(LocalCompilationResult {
        type_states,
        mir_entities,
        name_source_map,
    })
}

pub enum CompilationGoal {
    /// Run codegen, and actually emit resulting files.
    Codegen,
    /// Same as `codegen`, but no files are emitted. Used for LSP on file save events etc.
    Full,
    /// Only build enough of the project to re-build the units that are defined in the specified file. In practice, this
    /// means parsing, global visiting and impl collection for the whole project, but no ast lowering of any
    /// units outside `SpadePath`
    ///
    /// This is used by the LSP for interactive editing of a single file.
    LocalBuild(String),
}

impl CompilationGoal {
    fn should_codegen(&self) -> bool {
        match self {
            CompilationGoal::Codegen => true,
            CompilationGoal::Full => false,
            CompilationGoal::LocalBuild(_) => false,
        }
    }
}

#[tracing::instrument(skip_all)]
pub fn compile(
    mut sources: Vec<(ModuleNamespace, String, String)>,
    compilation_goal: CompilationGoal,
    include_stdlib: bool,
    opts: Opt,
    diag_handler: DiagHandler,
) -> Result<Artefacts, CompilationResult> {
    let mut sources = if include_stdlib {
        // We want to build stdlib and prelude before building user code,
        // to give `previously defined <here>` pointing into user code, instead
        // of stdlib code
        let mut all_sources = stdlib_files();
        all_sources.append(&mut sources);
        all_sources
    } else {
        sources
    };
    sources.append(&mut core_files());

    let code = Arc::new(RwLock::new(CodeBundle::new("".to_string())));
    let mut errors = ErrorHandler::new(opts.error_buffer, diag_handler, Arc::clone(&code));

    let mut unfinished_artefacts = UnfinishedArtefacts {
        code: Arc::clone(&code),
        symtab: None,
        item_list: None,
        type_states: None,
        floating_nodes: None,
    };

    let pass_impls = spade_mir::passes::mir_passes();
    let opt_passes = opts
        .opt_passes
        .iter()
        .map(|pass| {
            if let Some(pass) = pass_impls.get(pass.as_str()) {
                Ok(pass.as_ref())
            } else {
                let err = format!("{pass} is not a known optimization pass.");
                Err(err)
            }
        })
        .collect::<Result<Vec<_>, _>>();

    let mut opt_passes = match opt_passes {
        Ok(p) => p,
        Err(e) => {
            errors.error_buffer.write_all(e.as_bytes()).unwrap();
            return Err(CompilationResult::EarlyFailure(unfinished_artefacts));
        }
    };
    // This is a non-optional pass that prevents codegen bugs
    let deduplicate_mut_wires = DeduplicateMutWires {};
    opt_passes.push(&deduplicate_mut_wires);

    let global_compilation_state = run_global_compilation_tasks(
        sources,
        Arc::clone(&code),
        &mut errors,
        &mut unfinished_artefacts,
        opts.print_parse_traceback,
    )
    .map_err(|e| match e {
        GlobalCompilationError::EarlyFailure => {
            CompilationResult::EarlyFailure(unfinished_artefacts)
        }
    })?;

    let file_filter = match &compilation_goal {
        CompilationGoal::Codegen => None,
        CompilationGoal::Full => None,
        CompilationGoal::LocalBuild(file) => Some(code.read().unwrap().file_id(file)),
    };

    let LocalCompilationResult {
        type_states,
        mir_entities,
        name_source_map,
    } = run_local_compilation_steps(
        file_filter,
        &global_compilation_state,
        &mut errors,
        &opt_passes,
    )?;

    let mir_entities: Vec<_> = mir_entities
        .into_iter()
        .filter_map(|result_mir| result_mir.or_report(&mut errors))
        .collect();

    let GlobalCompilationState {
        item_list,
        impl_type_state: _,
        frozen_symtab,
        idtracker,
        mapped_trait_impls,
        shared_type_state,
        impl_idtracker,
        generic_idtracker,
        macros,
        floating_nodes
    } = global_compilation_state;

    let mut state = CompilerState {
        code: code
            .read()
            .unwrap()
            .dump_files()
            .into_iter()
            .map(|(n, s)| (n.to_string(), s.to_string()))
            .collect(),
        symtab: frozen_symtab,
        idtracker,
        impl_idtracker,
        generic_idtracker,
        item_list: item_list.clone(),
        macros: macros.clone(),
        name_source_map,
        instance_map: None,
        mir_context: None,
        shared_type_state,
        floating_nodes: floating_nodes.clone(),
        trait_impl_list: mapped_trait_impls.clone(),
    };

    let mut final_bumpy_mir_entities = None;
    if compilation_goal.should_codegen() {
        let CodegenArtefacts {
            bumpy_mir_entities,
            flat_mir_entities,
            module_code,
            mir_code,
            instance_map,
            mir_context,
        } = codegen(
            mir_entities,
            Arc::clone(&code),
            &mut errors,
            &state.idtracker,
            &state.symtab.symtab().id_tracker,
        );
        final_bumpy_mir_entities = Some(bumpy_mir_entities);
        state.mir_context = Some(mir_context);
        state.instance_map = Some(instance_map);
        if !errors.failed() {
            if let Some(outfile) = opts.outfile {
                std::fs::write(outfile, module_code.join("\n\n")).or_report(&mut errors);
            }
            if let Some(cpp_file) = opts.verilator_wrapper_output {
                let cpp_code =
                    verilator_wrappers(&flat_mir_entities.iter().map(|e| &e.0).collect::<Vec<_>>());
                std::fs::write(cpp_file, cpp_code).or_report(&mut errors);
            }
            if let Some(mir_output) = opts.mir_output {
                std::fs::write(mir_output, mir_code.join("\n\n")).or_report(&mut errors);
            }
            if let Some(item_list_file) = opts.item_list_file {
                let list = name_dump::list_names(&item_list);

                match ron::to_string(&list) {
                    Ok(encoded) => {
                        std::fs::write(item_list_file, encoded).or_report(&mut errors);
                    }
                    Err(e) => {
                        errors.set_failed();
                        println!("Failed to encode item list as RON {e:?}")
                    }
                }
            }
        }
    }

    let stored_state = state.into_stored();

    if compilation_goal.should_codegen() {
        if let Some(state_dump_file) = opts.state_dump_file {
            if std::env::var("SPADE_REPORT_SERIALIZED_SIZE").is_ok() {
                spade_common::sizes::SerializedSize::report_size(&stored_state);
            }

            match postcard::to_stdvec(&stored_state) {
                Ok(encoded) => {
                    std::fs::write(state_dump_file, encoded).or_report(&mut errors);
                }
                Err(e) => {
                    errors.set_failed();
                    println!("Failed to encode compiler state info as bincode {:?}", e)
                }
            }
        }
    }

    let artefacts = Artefacts {
        bumpy_mir_entities: final_bumpy_mir_entities,
        code: code.read().unwrap().clone(),
        item_list,
        impl_list: mapped_trait_impls,
        state: stored_state.into_compiler_state(),
        type_states,
        floating_nodes
    };

    if !errors.failed() {
        Ok(artefacts)
    } else {
        Err(CompilationResult::LateFailure(artefacts))
    }
}

pub fn do_in_namespace(
    namespace: &ModuleNamespace,
    ctx: &mut AstLoweringCtx,
    to_do: &mut dyn FnMut(&mut AstLoweringCtx),
) {
    for segment in &namespace.namespace.0 {
        // NOTE: These identifiers do not have the correct file_id. However,
        // as far as I know, they will never be part of an error, so we *should*
        // be safe.
        ctx.symtab.push_namespace(segment.clone());
    }
    ctx.symtab
        .set_base_namespace(namespace.base_namespace.clone());
    to_do(ctx);
    ctx.symtab.set_base_namespace(SpadePath(vec![]));
    for _ in &namespace.namespace.0 {
        ctx.symtab.pop_namespace();
    }
}

#[tracing::instrument(skip_all)]
pub fn parse(
    sources: Vec<(ModuleNamespace, String, String)>,
    code: Arc<RwLock<CodeBundle>>,
    print_parse_traceback: Option<String>,
    errors: &mut ErrorHandler,
) -> (Vec<(ModuleNamespace, Loc<ModuleBody>)>, FloatingNodes) {
    let mut module_asts = vec![];
    let mut floating_nodes = FloatingNodes::default();
    // Read and parse input files
    for (namespace, name, content) in sources {
        let _span = tracing::span!(Level::TRACE, "source", ?name).entered();
        let file_id = code
            .write()
            .unwrap()
            .add_file(name.clone(), content.clone());

        let mut parser = Parser::new(&content, file_id, namespace.working_dir.clone());

        parser.floating_nodes.namespaces.push(namespace.clone().at(parser.file_id(), &(0..content.len())));

        let result = parser
            .top_level_module_body()
            .map_err(|e| e)
            .or_report(errors);
        if print_parse_traceback
            .as_ref()
            .map(|file| name.contains(file))
            .unwrap_or(false)
        {
            println!("Parse traceback for {name}");
            println!("{}", spade_parser::format_parse_stack(&parser.parse_stack));
        };

        errors.drain_diag_list(&mut parser.diags);

        if let Some(ast) = result {
            module_asts.push((namespace, ast))
        }

        floating_nodes.merge(parser.floating_nodes);
    }

    (module_asts, floating_nodes)
}

#[tracing::instrument(skip_all)]
fn lower_ast(
    module_asts: &[(ModuleNamespace, Loc<ModuleBody>)],
    ctx: &mut AstLoweringCtx,
    errors: &mut ErrorHandler,
) {
    for (namespace, module_ast) in module_asts {
        // Cannot be done by do_in_namespace because the symtab has been moved
        // into `ctx`
        for segment in &namespace.namespace.0 {
            // NOTE: These identifiers do not have the correct file_id. However,
            // as far as I know, they will never be part of an error, so we *should*
            // be safe.
            ctx.symtab.push_namespace(segment.clone());
        }
        ctx.symtab
            .set_base_namespace(namespace.base_namespace.clone());
        visit_module_body(module_ast, ctx).or_report(errors);
        ctx.symtab.set_base_namespace(SpadePath(vec![]));
        for _ in &namespace.namespace.0 {
            ctx.symtab.pop_namespace();
        }
    }
}

struct CodegenArtefact {
    bumpy_mir_entity: spade_mir::Entity,
    flat_mir_entity: Codegenable,
    local_module_code: String,
    local_mir_code: String,
    local_instance_map: InstanceMap,
    local_mir_context: (NameID, MirContext),
}

#[tracing::instrument(skip_all)]
fn codegen(
    mir_entities: Vec<MirOutput>,
    code: Arc<RwLock<CodeBundle>>,
    error_handler: &mut ErrorHandler,
    idtracker: &Arc<ExprIdTracker>,
    nameidtracker: &spade_common::id_tracker::NameIdTracker,
) -> CodegenArtefacts {
    let mir_entities = do_inlining(mir_entities, idtracker, nameidtracker)
        .or_report(error_handler)
        .unwrap_or_default();

    let codegen_results = mir_entities
        .into_par_iter()
        .enumerate()
        .filter_map(
            |(
                i,
                MirOutput {
                    mir,
                    type_state,
                    reg_name_map,
                },
            )| {
                // Codegen breaks if not all statements are valid, and since we don't need
                // codegen if there are errors, we can safely bail from codegen of units with errors
                if mir
                    .statements
                    .iter()
                    .any(|stmt| matches!(stmt, spade_mir::Statement::Error))
                {
                    return None;
                }
                let bumpy_mir_entity = mir.clone();

                let codegenable = prepare_codegen(mir);

                let mut local_instance_map = InstanceMap::new();
                let code = spade_mir::codegen::entity_code(
                    &codegenable,
                    &mut local_instance_map,
                    &Some(code.read().unwrap().clone()),
                );

                let flat_mir_entity = codegenable.clone();

                let (code, name_map) = code;

                let mir_context = (
                    codegenable.0.name.source.clone(),
                    MirContext {
                        reg_name_map: reg_name_map.clone(),
                        type_state,
                        verilog_name_map: name_map,
                    },
                );
                Some((
                    i,
                    CodegenArtefact {
                        bumpy_mir_entity,
                        flat_mir_entity,
                        local_module_code: code.to_string(),
                        local_mir_code: codegenable.0.to_string(),
                        local_instance_map,
                        local_mir_context: mir_context,
                    },
                ))
            },
        )
        .collect::<Vec<_>>();

    let mut bumpy_mir_entities = Vec::with_capacity(codegen_results.len());
    let mut flat_mir_entities = Vec::with_capacity(codegen_results.len());
    let mut module_code = Vec::with_capacity(codegen_results.len() + 2);
    let mut mir_code = Vec::with_capacity(codegen_results.len());
    let mut instance_map = InstanceMap::new();
    let mut mir_context = HashMap::default();

    module_code.push(cocotb_code().to_string());

    for CodegenArtefact {
        bumpy_mir_entity,
        flat_mir_entity,
        local_module_code,
        local_mir_code,
        local_instance_map,
        local_mir_context,
    } in codegen_results
        .into_iter()
        .sorted_by_key(|(k, _)| *k)
        .map(|(_, v)| v)
    {
        bumpy_mir_entities.push(bumpy_mir_entity);
        flat_mir_entities.push(flat_mir_entity);
        module_code.push(local_module_code);
        mir_code.push(local_mir_code);
        instance_map
            .inner
            .extend(&mut local_instance_map.inner.into_iter());
        mir_context.insert(local_mir_context.0, local_mir_context.1);
    }

    // Acts as a sanity check to catch if we ever attempt to use a wire that isn't
    // defined, for example if a zero-sized wire is used.
    module_code.push("`default_nettype none".into());

    CodegenArtefacts {
        bumpy_mir_entities,
        flat_mir_entities,
        module_code,
        mir_code,
        instance_map,
        mir_context,
    }
}

macro_rules! sources {
    ($(($base_namespace:expr, $namespace:expr, $filename:expr)),*$(,)?) => {
        vec! [
            $(
                (
                    ModuleNamespace {
                        namespace: SpadePath::from_strs(&$namespace),
                        base_namespace: SpadePath::from_strs(&$base_namespace),
                        file: String::from($filename).replace("../", "<compiler dir>/"),
                        working_dir: None
                    },
                    String::from($filename).replace("../", "<compiler dir>/"),
                    String::from(include_str!($filename))
                )
            ),*
        ]
    }
}

pub fn core_files() -> Vec<(ModuleNamespace, String, String)> {
    sources! {
        ([], [], "../core/prelude.spade"),

        (["core"], ["core"], "../core/main.spade"),
        (["core"], ["core", "conv"], "../core/conv.spade"),
        (["core"], ["core", "macros"], "../core/macros.spade"),
        (["core"], ["core", "marker"], "../core/marker.spade"),
        (["core"], ["core", "ops"], "../core/ops.spade"),
        (["core"], ["core", "ports"], "../core/ports.spade"),
        (["core"], ["core", "undef"], "../core/undef.spade")
    }
}

/// The spade source files which are included statically in the binary, rather
/// than being passed on the command line. This includes the stdlib and prelude
pub fn stdlib_files() -> Vec<(ModuleNamespace, String, String)> {
    sources! {
        ([], [], "../stdlib/prelude.spade"),

        (["std"], ["std"], "../stdlib/main.spade"),
        (["std"], ["std", "array"], "../stdlib/array.spade"),
        (["std"], ["std", "cdc"], "../stdlib/cdc.spade"),
        (["std"], ["std", "conv"], "../stdlib/conv.spade"),
        (["std"], ["std", "default"], "../stdlib/default.spade"),
        (["std"], ["std", "io"], "../stdlib/io.spade"),
        (["std"], ["std", "mem"], "../stdlib/mem.spade"),
        (["std"], ["std", "num"], "../stdlib/num.spade"),
        (["std"], ["std", "ops"], "../stdlib/ops.spade"),
        (["std"], ["std", "option"], "../stdlib/option.spade"),
        (["std"], ["std", "ports"], "../stdlib/ports.spade"),
        (["std"], ["std", "undef"], "../stdlib/undef.spade"),
    }
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    /// Having to maintain the stdlib list is error prone, so having a test
    /// here to verify that all files in stdlib/<file>.spade
    #[test]
    fn sanity_check_static_sources_stdlib_included() {
        let included = super::stdlib_files()
            .into_iter()
            .filter_map(|(_, file, _)| {
                Some(
                    PathBuf::from(file)
                        .file_name()
                        .map(|f| f.to_string_lossy().to_string()),
                )
            })
            .collect::<Vec<_>>();

        let missing_files = std::fs::read_dir("stdlib/")
            .expect("Failed to read stdlib")
            .into_iter()
            .map(|f| {
                f.unwrap()
                    .path()
                    .file_name()
                    .map(|f| f.to_string_lossy().to_string())
            })
            .filter(|f| !included.contains(f))
            .collect::<Vec<_>>();

        assert_eq!(missing_files, vec![])
    }
}
