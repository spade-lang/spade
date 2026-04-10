#![recursion_limit = "256"]

use std::{
    fs::File,
    io::Read,
    sync::{Arc, Mutex, RwLock},
};

use camino::Utf8PathBuf;
use color_eyre::{Result, eyre::Context};
use rustc_hash::FxHashMap as HashMap;
use spade::{
    ModuleNamespace, core_files, do_in_namespace,
    error_handling::{ErrorHandler, Reportable},
    namespaced_file::NamespacedFile,
    parse, stdlib_files,
};
use spade_ast_lowering::{SelfContext, global_symbols};
use spade_codespan_reporting::term::termcolor::Buffer;
use spade_common::name::Path as SpadePath;
use spade_common::{
    id_tracker::{ExprIdTracker, GenericIdTracker, ImplIdTracker},
    location_info::WithLocation as _,
    name::{Path, PathSegment, Visibility},
};
use spade_diagnostics::{CodeBundle, DiagHandler, diag_list::DiagList, emitter::CodespanEmitter};
use spade_hir::{ItemList, expression::Safety, symbol_table::SymbolTable};

use crate::impls_n_docs::ImplsNDocs;

mod djot;
mod error;
/// Holds all methods to emit most of the describing elements.
mod generate;
mod html;
mod impls_n_docs;
/// Holds all methods to emit code from ast.
mod print;

pub fn doc(infiles: Vec<NamespacedFile>, gen_dir: Utf8PathBuf) -> Result<(), Buffer> {
    let mut buffer = Buffer::ansi();

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
    let mut sources = sources.unwrap();

    let opts = spade::Opt {
        error_buffer: &mut buffer,
        outfile: None,
        mir_output: None,
        state_dump_file: None,
        item_list_file: None,
        print_parse_traceback: false,
        verilator_wrapper_output: None,
        opt_passes: vec![],
    };
    // Codespan emitter so compilation errors are reported as normal.
    let diag_handler = DiagHandler::new(Box::new(CodespanEmitter));

    let diags = Arc::new(Mutex::new(DiagList::new()));

    // The following is a part of spade::compile but only until parsing with parts of ast-lowering
    let mut symtab = SymbolTable::new(diags.clone());
    let mut item_list = ItemList::new();

    let include_stdlib_and_prelude = true;
    let mut sources = if include_stdlib_and_prelude {
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
    sources.push((
        ModuleNamespace {
            namespace: SpadePath::from_strs(&["core"]),
            base_namespace: SpadePath::from_strs(&["core"]),
            file: String::from("<spadedoc dir>/primitives.spade"),
        },
        String::from("<spadedoc dir>/primitives.spade"),
        String::from(include_str!("../primitives.spade")),
    ));

    spade_ast_lowering::builtins::populate_symtab(&mut symtab, &mut item_list);

    let code = Arc::new(RwLock::new(CodeBundle::new("".to_string())));

    let mut errors = ErrorHandler::new(opts.error_buffer, diag_handler, Arc::clone(&code));

    let module_asts = parse(
        sources,
        Arc::clone(&code),
        opts.print_parse_traceback,
        &mut errors,
    );
    errors.errors_are_recoverable();

    let (mut primitives, module_asts): (Vec<_>, Vec<_>) = module_asts
        .into_iter()
        .partition(|(m, _)| m.file == "<spadedoc dir>/primitives.spade");
    let primitives = primitives
        .pop()
        .expect("No primitive docs supplied")
        .1
        .inner;

    let mut ctx = spade_ast_lowering::Context {
        symtab,
        item_list,
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
            let _name_id = ctx.symtab.add_thing(
                namespace.namespace.clone(),
                spade_hir::symbol_table::Thing::Module(
                    ().nowhere(),
                    namespace.namespace.0.last().unwrap().unwrap_named().clone(),
                ),
                Some(Visibility::Implicit.nowhere()),
                None,
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
        return Err(buffer);
    }

    for err in global_symbols::report_missing_mod_declarations(&module_asts, &missing_namespace_set)
    {
        errors.report(&err);
    }

    errors.errors_are_recoverable();

    for (namespace, module_ast) in &module_asts {
        do_in_namespace(namespace, &mut ctx, &mut |ctx| {
            global_symbols::gather_traits_and_modules(module_ast, ctx).or_report(&mut errors);
        })
    }
    for (namespace, module_ast) in &module_asts {
        do_in_namespace(namespace, &mut ctx, &mut |ctx| {
            global_symbols::gather_types(module_ast, ctx).or_report(&mut errors);
        })
    }

    if errors.failed_now() {
        errors.drain_diag_list(&mut ctx.diags.lock().unwrap());
        return Err(buffer);
    }

    for (namespace, module_ast) in &module_asts {
        do_in_namespace(namespace, &mut ctx, &mut |ctx| {
            global_symbols::gather_symbols(module_ast, ctx).or_report(&mut errors);
        })
    }

    if errors.failed_now() {
        errors.drain_diag_list(&mut ctx.diags.lock().unwrap());
        return Err(buffer);
    }

    let mut impls = ImplsNDocs {
        for_type: HashMap::default(),
        docs: HashMap::default(),
    };

    for (namespace, module_ast) in &module_asts {
        do_in_namespace(namespace, &mut ctx, &mut |ctx| {
            impls_n_docs::gather_impls_n_docs(module_ast, &mut impls, ctx).or_report(&mut errors);
        })
    }

    if errors.failed_now() {
        errors.drain_diag_list(&mut ctx.diags.lock().unwrap());
        return Err(buffer);
    }

    let mut generator = generate::Generator {
        symtab: ctx.symtab,
        current_dir: gen_dir.clone(),
        impls,
        diags: ctx.diags,
        is_module: true, // this is irrelevant as it is always set before creating a file
        primitives,
    };

    std::fs::create_dir_all(&gen_dir).or_report(&mut errors);
    for (namespace, module_ast) in &module_asts {
        generator.current_dir = gen_dir.clone();
        for seg in &namespace.namespace.0 {
            let PathSegment::Named(ident) = seg else {
                panic!(
                    "Spadedoc assumes that modules can't be in impls/entites: {}",
                    &namespace.namespace
                );
            };
            generator.current_dir.push(ident.inner.as_str());
            // NOTE: These identifiers do not have the correct file_id. However,
            // as far as I know, they will never be part of an error, so we *should*
            // be safe.
            generator
                .symtab
                .push_namespace(PathSegment::Named(ident.clone()));
        }
        std::fs::create_dir_all(&generator.current_dir).or_report(&mut errors);
        generator
            .symtab
            .set_base_namespace(namespace.base_namespace.clone());
        generator
            .doc_mod(module_ast)
            .expect("Couldn't generate documentations"); // FIXME:
        generator.symtab.set_base_namespace(Path(vec![]));
        for _ in &namespace.namespace.0 {
            generator.symtab.pop_namespace();
        }
    }

    if errors.failed_now() {
        errors.drain_diag_list(&mut generator.diags.lock().unwrap());
        return Err(buffer);
    }

    Ok(())
}
