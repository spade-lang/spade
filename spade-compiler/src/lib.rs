pub mod compiler_state;
mod error_handling;
mod name_dump;
pub mod namespaced_file;

use compiler_state::{CompilerState, MirContext};
use error_handling::{ErrorHandler, Reportable};
use logos::Logos;
use spade_ast_lowering::id_tracker::ExprIdTracker;
use spade_codespan_reporting::term::termcolor::Buffer;
use spade_common::location_info::Loc;
pub use spade_common::namespace::ModuleNamespace;
use spade_diagnostics::diag_list::DiagList;
use spade_hir::expression::Safety;
use spade_mir::codegen::{prepare_codegen, Codegenable};
use spade_mir::passes::deduplicate_mut_wires::DeduplicateMutWires;
use spade_mir::unit_name::InstanceMap;
use spade_mir::verilator_wrapper::verilator_wrappers;
use spade_typeinference::traits::TraitImplList;
use std::collections::{BTreeMap, HashMap};
use std::io::Write;
use std::path::PathBuf;
use std::rc::Rc;
use std::sync::RwLock;
use tracing::Level;
use typeinference::TypeState;

use spade_ast::ModuleBody;
use spade_ast_lowering::{
    ensure_unique_anonymous_traits, global_symbols, visit_module_body, Context as AstLoweringCtx,
    SelfContext,
};
use spade_common::id_tracker::ImplIdTracker;
use spade_common::name::{NameID, Path as SpadePath};
use spade_diagnostics::{CodeBundle, DiagHandler, Diagnostic};
use spade_hir::symbol_table::SymbolTable;
use spade_hir::{ExecutableItem, ItemList};
use spade_hir_lowering::monomorphisation::MirOutput;
use spade_hir_lowering::NameSourceMap;
pub use spade_parser::lexer;
use spade_parser::Parser;
use spade_typeinference as typeinference;
use spade_typeinference::trace_stack::format_trace_stack;

pub struct Opt<'b> {
    pub error_buffer: &'b mut Buffer,
    pub outfile: Option<PathBuf>,
    pub mir_output: Option<PathBuf>,
    pub verilator_wrapper_output: Option<PathBuf>,
    pub state_dump_file: Option<PathBuf>,
    pub item_list_file: Option<PathBuf>,
    pub print_type_traceback: bool,
    pub print_parse_traceback: bool,
    pub opt_passes: Vec<String>,
}

/// Compiler output.
pub struct Artefacts {
    pub code: CodeBundle,
    pub item_list: ItemList,
    // MIR entities before aliases have been flattened
    pub bumpy_mir_entities: Vec<spade_mir::Entity>,
    // MIR entities after flattening
    pub flat_mir_entities: Vec<Codegenable>,
    pub state: CompilerState,
    pub impl_list: TraitImplList,
    pub type_states: BTreeMap<NameID, TypeState>,
}

/// Like [Artefacts], but if the compiler didn't finish due to errors.
pub struct UnfinishedArtefacts {
    pub code: CodeBundle,
    pub symtab: Option<SymbolTable>,
    pub item_list: Option<ItemList>,
    pub type_states: Option<BTreeMap<NameID, TypeState>>,
}

pub enum CompilationResult {
    EarlyFailure(UnfinishedArtefacts),
    LateFailure(Artefacts),
}

struct CodegenArtefacts {
    bumpy_mir_entities: Vec<spade_mir::Entity>,
    flat_mir_entities: Vec<Codegenable>,
    module_code: Vec<String>,
    mir_code: Vec<String>,
    instance_map: InstanceMap,
    mir_context: HashMap<NameID, MirContext>,
}

#[tracing::instrument(skip_all)]
pub fn compile(
    mut sources: Vec<(ModuleNamespace, String, String)>,
    include_stdlib_and_prelude: bool,
    opts: Opt,
    diag_handler: DiagHandler,
) -> Result<Artefacts, CompilationResult> {
    let mut symtab = SymbolTable::new();
    let mut item_list = ItemList::new();

    let mut sources = if include_stdlib_and_prelude {
        // We want to build stdlib and prelude before building user code,
        // to give `previously defined <here>` pointing into user code, instead
        // of stdlib code
        let mut all_sources = stdlib_and_prelude();
        all_sources.append(&mut sources);
        all_sources
    } else {
        sources
    };
    sources.append(&mut core_files());

    spade_ast_lowering::builtins::populate_symtab(&mut symtab, &mut item_list);

    let code = Rc::new(RwLock::new(CodeBundle::new("".to_string())));

    let mut errors = ErrorHandler::new(opts.error_buffer, diag_handler, Rc::clone(&code));

    let module_asts = parse(
        sources,
        Rc::clone(&code),
        opts.print_parse_traceback,
        &mut errors,
    );
    errors.errors_are_recoverable();

    let mut unfinished_artefacts = UnfinishedArtefacts {
        code: code.read().unwrap().clone(),
        symtab: None,
        item_list: None,
        type_states: None,
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

    let mut ctx = AstLoweringCtx {
        symtab,
        item_list,
        idtracker: ExprIdTracker::new(),
        impl_idtracker: ImplIdTracker::new(),
        pipeline_ctx: None,
        self_ctx: SelfContext::FreeStanding,
        current_unit: None,
        diags: DiagList::new(),
        safety: Safety::Default,
    };

    // Add all "root" project main.spade modules
    for root in module_asts
        .iter()
        .filter(|(ns, _ast)| ns.base_namespace == ns.namespace)
    {
        let namespace = &root.0;
        if !namespace.namespace.0.is_empty() {
            ctx.symtab.add_thing(
                namespace.namespace.clone(),
                spade_hir::symbol_table::Thing::Module(
                    namespace.namespace.0.last().unwrap().clone(),
                ),
            );
        }
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
            .or_report(&mut errors);
        })
    }

    if errors.failed_now() {
        unfinished_artefacts.symtab = Some(ctx.symtab);
        return Err(CompilationResult::EarlyFailure(unfinished_artefacts));
    }

    for err in global_symbols::report_missing_mod_declarations(&module_asts, &missing_namespace_set)
    {
        errors.report(&err);
    }

    errors.errors_are_recoverable();

    for (namespace, module_ast) in &module_asts {
        do_in_namespace(namespace, &mut ctx, &mut |ctx| {
            global_symbols::gather_types(module_ast, ctx).or_report(&mut errors);
        })
    }

    if errors.failed_now() {
        unfinished_artefacts.symtab = Some(ctx.symtab);
        errors.drain_diag_list(&mut ctx.diags);
        return Err(CompilationResult::EarlyFailure(unfinished_artefacts));
    }

    for (namespace, module_ast) in &module_asts {
        do_in_namespace(namespace, &mut ctx, &mut |ctx| {
            global_symbols::gather_symbols(module_ast, ctx).or_report(&mut errors);
        })
    }

    unfinished_artefacts.item_list = Some(ctx.item_list.clone());

    if errors.failed_now() {
        unfinished_artefacts.symtab = Some(ctx.symtab);
        errors.drain_diag_list(&mut ctx.diags);
        return Err(CompilationResult::EarlyFailure(unfinished_artefacts));
    }
    // Let's prevent using this thing again
    let _unfinished_artefacts = unfinished_artefacts;

    lower_ast(&module_asts, &mut ctx, &mut errors);

    let AstLoweringCtx {
        symtab,
        mut item_list,
        mut idtracker,
        impl_idtracker,
        pipeline_ctx: _,
        self_ctx: _,
        current_unit: _,
        mut diags,
        safety: _,
    } = ctx;

    errors.drain_diag_list(&mut diags);

    for e in ensure_unique_anonymous_traits(&mut item_list) {
        errors.report(&e)
    }

    let mut frozen_symtab = symtab.freeze();

    let mut impl_type_state = TypeState::fresh();
    let mapped_trait_impls = impl_type_state.visit_impl_blocks(&item_list);

    errors.drain_diag_list(&mut impl_type_state.diags);

    let type_inference_ctx = typeinference::Context {
        symtab: frozen_symtab.symtab(),
        items: &item_list,
        trait_impls: &mapped_trait_impls,
    };

    let mut type_states = BTreeMap::new();

    let executables_and_types = item_list
        .executables
        .iter()
        .filter_map(|(name, item)| match item {
            ExecutableItem::Unit(u) => {
                let mut type_state = impl_type_state.create_child();

                let result = type_state
                    .visit_unit(u, &type_inference_ctx)
                    .report(&mut errors);

                let failures = type_state.diags.errors.len() != 0;
                errors.drain_diag_list(&mut type_state.diags);

                // Later stages will fail if we don't have a a complete type state,
                // so we'll need to filter out modules that failed. However, for the LSP
                // we still want to retain the incomplete type state
                type_states.insert(name.clone(), type_state.clone());

                if let Ok(()) = result {
                    if opts.print_type_traceback {
                        type_state.print_equations();
                        println!("{}", format_trace_stack(&type_state));
                    }
                    if !failures {
                        Some((name, (item, type_state)))
                    } else {
                        None
                    }
                } else {
                    if opts.print_type_traceback {
                        type_state.print_equations();
                        println!("{}", format_trace_stack(&type_state))
                    }
                    None
                }
            }
            ExecutableItem::EnumInstance { .. } => None,
            ExecutableItem::StructInstance { .. } => None,
            ExecutableItem::ExternUnit(_, _) => None,
        })
        .collect::<BTreeMap<_, _>>();

    let mut name_source_map = NameSourceMap::new();
    let mir_entities = spade_hir_lowering::monomorphisation::compile_items(
        &executables_and_types,
        &mut frozen_symtab,
        &mut idtracker,
        &mut name_source_map,
        &item_list,
        &mut errors.diag_handler,
        &opt_passes,
        &impl_type_state,
    );

    let CodegenArtefacts {
        bumpy_mir_entities,
        flat_mir_entities,
        module_code,
        mir_code,
        instance_map,
        mir_context,
    } = codegen(mir_entities, Rc::clone(&code), &mut errors, &mut idtracker);

    let state = CompilerState {
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
        item_list: item_list.clone(),
        name_source_map,
        instance_map,
        mir_context,
    };

    let code = code.read().unwrap();

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
        if let Some(state_dump_file) = opts.state_dump_file {
            // let ron = ron::Options::default().without_recursion_limit();
            match bincode::serde::encode_to_vec(&state, bincode::config::standard()) {
                Ok(encoded) => {
                    std::fs::write(state_dump_file, encoded).or_report(&mut errors);
                }
                Err(e) => {
                    errors.set_failed();
                    println!("Failed to encode compiler state info as bincode {:?}", e)
                }
            }
        }
        let artefacts = Artefacts {
            bumpy_mir_entities,
            flat_mir_entities,
            code: code.clone(),
            item_list,
            impl_list: mapped_trait_impls,
            state,
            type_states,
        };

        Ok(artefacts)
    } else {
        let artefacts = Artefacts {
            bumpy_mir_entities,
            flat_mir_entities,
            code: code.clone(),
            item_list,
            impl_list: mapped_trait_impls,
            state,
            type_states,
        };

        Err(CompilationResult::LateFailure(artefacts))
    }
}

fn do_in_namespace(
    namespace: &ModuleNamespace,
    ctx: &mut AstLoweringCtx,
    to_do: &mut dyn FnMut(&mut AstLoweringCtx),
) {
    for ident in &namespace.namespace.0 {
        // NOTE: These identifiers do not have the correct file_id. However,
        // as far as I know, they will never be part of an error, so we *should*
        // be safe.
        ctx.symtab.push_namespace(ident.clone());
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
fn parse(
    sources: Vec<(ModuleNamespace, String, String)>,
    code: Rc<RwLock<CodeBundle>>,
    print_parse_traceback: bool,
    errors: &mut ErrorHandler,
) -> Vec<(ModuleNamespace, Loc<ModuleBody>)> {
    let mut module_asts = vec![];
    // Read and parse input files
    for (namespace, name, content) in sources {
        let _span = tracing::span!(Level::TRACE, "source", ?name).entered();
        let file_id = code.write().unwrap().add_file(name, content.clone());
        let mut parser = Parser::new(lexer::TokenKind::lexer(&content), file_id);

        let result = parser
            .top_level_module_body()
            .map_err(|e| {
                if print_parse_traceback {
                    println!("{}", spade_parser::format_parse_stack(&parser.parse_stack));
                };
                e
            })
            .or_report(errors);

        errors.drain_diag_list(&mut parser.diags);

        if let Some(ast) = result {
            module_asts.push((namespace, ast))
        }
    }

    module_asts
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
        for ident in &namespace.namespace.0 {
            // NOTE: These identifiers do not have the correct file_id. However,
            // as far as I know, they will never be part of an error, so we *should*
            // be safe.
            ctx.symtab.push_namespace(ident.clone());
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

#[tracing::instrument(skip_all)]
fn codegen(
    mir_entities: Vec<Result<MirOutput, Diagnostic>>,
    code: Rc<RwLock<CodeBundle>>,
    errors: &mut ErrorHandler,
    idtracker: &mut ExprIdTracker,
) -> CodegenArtefacts {
    let mut bumpy_mir_entities = vec![];
    let mut flat_mir_entities = vec![];
    let mut module_code = vec![];
    let mut mir_code = vec![];
    let mut instance_map = InstanceMap::new();
    let mut mir_context = HashMap::new();

    for mir in mir_entities {
        if let Some(MirOutput {
            mir,
            type_state,
            reg_name_map,
        }) = mir.or_report(errors)
        {
            bumpy_mir_entities.push(mir.clone());

            let codegenable = prepare_codegen(mir, idtracker);

            let code = spade_mir::codegen::entity_code(
                &codegenable,
                &mut instance_map,
                &Some(code.read().unwrap().clone()),
            );

            mir_code.push(format!("{}", codegenable.0));

            flat_mir_entities.push(codegenable.clone());

            let (code, name_map) = code;
            module_code.push(code.to_string());

            mir_context.insert(
                codegenable.0.name.source,
                MirContext {
                    reg_name_map: reg_name_map.clone(),
                    type_state,
                    verilog_name_map: name_map,
                },
            );
        }
    }

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
                        file: String::from($filename).replace("../", "<compiler dir>/")
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
        ([], [], "../core/core.spade"),
    }
}

/// The spade source files which are included statically in the binary, rather
/// than being passed on the command line. This includes the stdlib and prelude
pub fn stdlib_and_prelude() -> Vec<(ModuleNamespace, String, String)> {
    sources! {
        ([], [], "../prelude/prelude.spade"),

        (["std"], ["std"], "../stdlib/main.spade"),
        (["std"], ["std", "array"], "../stdlib/array.spade"),
        (["std"], ["std", "cdc"], "../stdlib/cdc.spade"),
        (["std"], ["std", "conv"], "../stdlib/conv.spade"),
        (["std"], ["std", "io"], "../stdlib/io.spade"),
        (["std"], ["std", "mem"], "../stdlib/mem.spade"),
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
        let included = super::stdlib_and_prelude()
            .into_iter()
            .filter_map(|(ns, file, _)| {
                if ns.base_namespace.as_strs() == ["std"] {
                    Some(
                        PathBuf::from(file)
                            .file_name()
                            .map(|f| f.to_string_lossy().to_string()),
                    )
                } else {
                    None
                }
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
