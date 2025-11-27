#![recursion_limit = "256"]

use std::{
    collections::{BTreeMap, HashMap},
    fs::File,
    io::{Read, Write},
};

use color_eyre::{eyre::Context, Result};
use item::Item;
use spade::{namespaced_file::NamespacedFile, ModuleNamespace};
use spade_codespan_reporting::term::termcolor::Buffer;
use spade_common::{
    location_info::WithLocation,
    name::{Identifier, NameID, Path as SpadePath},
};
use spade_diagnostics::{emitter::CodespanEmitter, DiagHandler};
use spade_hir::{
    symbol_table::FrozenSymtab, ExecutableItem, ImplBlock, ImplTarget, ItemList, Module, TraitName,
};

pub mod html;
pub mod item;
pub mod renderer;

pub struct Documentation {
    /// Map from the namespace over all direct items in it, e.g. `a::b::c` is `[a::b, [c, {..}]]`
    pub documentables: HashMap<SpadePath, HashMap<Identifier, Item>>,
    pub root: (String, Module),
    pub symtab: FrozenSymtab,
    pub flattened_impls: BTreeMap<ImplTarget, Vec<(TraitName, ImplBlock)>>,

    pub dependencies: BTreeMap<String, Documentation>,
}

trait SpadePathExt {
    fn as_lib(&self, library: &str) -> Option<Self>
    where
        Self: Sized;

    fn as_dep_lib(&self) -> Option<String>;
}

impl SpadePathExt for SpadePath {
    fn as_lib(&self, library: &str) -> Option<Self> {
        if !self.0.is_empty() && self.0[0].to_named_str() == Some(library) {
            Some(Self(self.0.iter().skip(1).cloned().collect()))
        } else {
            None
        }
    }

    fn as_dep_lib(&self) -> Option<String> {
        self.0.first().map(|first| first.to_string())
    }
}

pub struct PreprocessedItemList {
    root_item_list: ItemList,
}

fn preprocess_item_list(item_list: ItemList, root_name: &str) -> PreprocessedItemList {
    let mut root_item_list = ItemList::default();
    let mut dependency_item_lists: HashMap<String, ItemList> = HashMap::new();

    for (name, executable) in item_list.executables {
        if let Some(path) = name.1.as_lib(root_name) {
            root_item_list
                .executables
                .insert(NameID(name.0, path), executable);
        } else if let Some(dep_name) = name.1.as_dep_lib() {
            dependency_item_lists
                .entry(dep_name)
                .or_default()
                .executables
                .insert(name, executable);
        }
    }
    for (name, ty) in item_list.types {
        if let Some(path) = name.1.as_lib(root_name) {
            root_item_list.types.insert(NameID(name.0, path), ty);
        } else if let Some(dep_name) = name.1.as_dep_lib() {
            dependency_item_lists
                .entry(dep_name)
                .or_default()
                .types
                .insert(name, ty);
        }
    }

    for (name, def) in item_list.traits {
        let TraitName::Named(name) = name else {
            continue;
        };

        if let Some(path) = name.1.as_lib(root_name) {
            root_item_list.traits.insert(
                TraitName::Named(NameID(name.0, path).at_loc(&name.loc())),
                def,
            );
        } else if let Some(dep_name) = name.1.as_dep_lib() {
            dependency_item_lists
                .entry(dep_name)
                .or_default()
                .traits
                .insert(TraitName::Named(name), def);
        }
    }

    root_item_list.impls = item_list.impls;

    for (name, module) in item_list.modules {
        if let Some(path) = name.1.as_lib(root_name) {
            root_item_list.modules.insert(NameID(name.0, path), module);
        } else if let Some(dep_name) = name.1.as_dep_lib() {
            dependency_item_lists
                .entry(dep_name)
                .or_default()
                .modules
                .insert(name, module);
        }
    }

    PreprocessedItemList { root_item_list }
}

pub fn doc(infiles: Vec<NamespacedFile>, root_name: &str) -> Result<Documentation, Buffer> {
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
    // Codespan emitter so compilation errors are reported as normal.
    let diag_handler = DiagHandler::new(Box::new(CodespanEmitter));
    let artefacts =
        spade::compile(sources.unwrap(), true, opts, diag_handler).map_err(|_| buffer)?;

    let PreprocessedItemList { root_item_list } =
        preprocess_item_list(artefacts.item_list, root_name);

    let mut documentables: HashMap<SpadePath, HashMap<Identifier, Item>> = HashMap::new();

    for (NameID(_, path), executable) in root_item_list.executables {
        let namespace = path.prelude();
        let name = path.tail().unwrap_named().inner.clone();

        let is_extern = matches!(executable, ExecutableItem::ExternUnit(_, _));

        let head = match executable {
            ExecutableItem::Unit(unit) => unit.inner.head,
            ExecutableItem::ExternUnit(_, head) => head.inner,
            ExecutableItem::EnumInstance { .. } | ExecutableItem::StructInstance => {
                continue;
            }
        };
        documentables
            .entry(namespace)
            .or_default()
            .insert(name, Item::Unit(head, is_extern));
    }

    for (NameID(_, path), ty) in root_item_list.types {
        let namespace = path.prelude();
        let name = path.tail().unwrap_named().inner.clone();

        documentables
            .entry(namespace)
            .or_default()
            .insert(name, Item::Type(ty.inner));
    }

    for (name, def) in root_item_list.traits {
        let TraitName::Named(id) = name else {
            continue;
        };

        let namespace = id.1.prelude();
        let name = id.1.tail().unwrap_named().inner.clone();

        documentables
            .entry(namespace)
            .or_default()
            .insert(name, Item::Trait(id.inner, def));
    }

    let mut flattened_impls: BTreeMap<ImplTarget, Vec<(TraitName, ImplBlock)>> = BTreeMap::new();
    for (target, traits) in root_item_list.impls.inner {
        for (trait_name, per_typeexpr) in traits {
            for (_target_typeexprs, impl_blocks) in per_typeexpr {
                for (_, impl_block) in impl_blocks {
                    flattened_impls
                        .entry(target.clone())
                        .or_default()
                        .push((trait_name.clone(), impl_block.inner.clone()));
                }
            }
        }
    }

    let mut root = None;
    for (NameID(_, path), module) in root_item_list.modules {
        if path.0.is_empty() {
            // root namespace
            root = Some((root_name.to_string(), module));
            continue;
        }

        let namespace = path.prelude();
        let name = path.tail().unwrap_named().inner.clone();

        documentables
            .entry(namespace)
            .or_default()
            .insert(name, Item::Module(module));
    }
    if let Some(root) = root {
        Ok(Documentation {
            documentables,
            root,
            symtab: artefacts.state.symtab,
            flattened_impls,
            dependencies: BTreeMap::new(),
        })
    } else {
        // FIXME(ethan): there has to be a better way to return an error
        let mut buffer = Buffer::no_color();
        let _ = writeln!(
            &mut buffer,
            "error: Requested root library {root_name} not found"
        );
        Err(buffer)
    }
}
