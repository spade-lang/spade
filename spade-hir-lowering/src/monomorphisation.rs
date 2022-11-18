use std::collections::{HashMap, VecDeque};

use spade_common::{id_tracker::ExprIdTracker, location_info::WithLocation, name::NameID};
use spade_diagnostics::DiagHandler;
use spade_hir::{symbol_table::FrozenSymtab, ExecutableItem, ItemList, UnitName};
use spade_mir as mir;
use spade_typeinference::equation::TypeVar;
use spade_typeinference::error::UnificationErrorExt;
use spade_typeinference::{GenericListToken, TypeState};

use crate::error::{Error, Result};
use crate::generate_entity;
use crate::passes::lower_methods::LowerMethods;
use crate::passes::pass::Passable;
use crate::{generate_pipeline, name_map::NameSourceMap};

/// An item to be monomorphised
struct MonoItem {
    /// The name of the original item which this is a monomorphised version of
    pub source_name: NameID,
    /// The new name of the new item
    pub new_name: UnitName,
    /// The types to replace the generic types in the item. Positional replacement
    pub params: Vec<TypeVar>,
}

pub struct MonoState {
    /// List of mono items left to compile
    to_compile: VecDeque<MonoItem>,
    /// Mapping between items with types specified and names
    translation: HashMap<(NameID, Vec<TypeVar>), NameID>,
}

impl MonoState {
    pub fn new() -> MonoState {
        MonoState {
            to_compile: VecDeque::new(),
            translation: HashMap::new(),
        }
    }

    /// Request compilation of a unit with the specified type parameters, returning the name of the
    /// unit which will be compiled with these parameters. It is up to the caller of this
    /// function to ensure that the type params are valid for this item.
    pub fn request_compilation(
        &mut self,
        source_name: UnitName,
        params: Vec<TypeVar>,
        symtab: &mut FrozenSymtab,
    ) -> NameID {
        match self
            .translation
            .get(&(source_name.name_id().inner.clone(), params.clone()))
        {
            Some(prev) => prev.clone(),
            None => {
                let new_name = symtab.new_name(source_name.name_id().1.clone());

                // Wrap the new name in a UnitName to match the source. Previous steps
                // ensure that the unit name is general enough to not cause name collisions
                let new_unit_name = match &source_name {
                    UnitName::WithID(_) => UnitName::WithID(new_name.clone().nowhere()),
                    UnitName::FullPath(_) => UnitName::FullPath(new_name.clone().nowhere()),
                    UnitName::Unmangled(source, _) => {
                        UnitName::Unmangled(source.clone(), new_name.clone().nowhere())
                    }
                };

                self.to_compile.push_back(MonoItem {
                    source_name: source_name.name_id().inner.clone(),
                    new_name: new_unit_name,
                    params,
                });
                new_name
            }
        }
    }

    fn next_target(&mut self) -> Option<MonoItem> {
        self.to_compile.pop_front()
    }
}

pub struct MirOutput {
    pub mir: mir::Entity,
    pub type_state: TypeState,
    /// Mapping between new names for registers and their previous value. Used
    /// to add type information for registers generated by pipelines
    pub reg_name_map: HashMap<NameID, NameID>,
}

pub fn compile_items(
    items: &HashMap<&NameID, (&ExecutableItem, TypeState)>,
    symtab: &mut FrozenSymtab,
    idtracker: &mut ExprIdTracker,
    name_source_map: &mut NameSourceMap,
    item_list: &ItemList,
    diag_handler: &mut DiagHandler,
) -> Vec<Result<MirOutput>> {
    // Build a map of items to use for compilation later. Also push all non
    // generic items to the compilation queue

    let mut state = MonoState::new();

    for (_, (item, _)) in items {
        match item {
            ExecutableItem::Entity(e) => {
                if e.head.type_params.is_empty() {
                    state.request_compilation(e.name.clone(), vec![], symtab);
                }
            }
            ExecutableItem::Pipeline(p) => {
                if p.head.type_params.is_empty() {
                    state.request_compilation(p.name.clone(), vec![], symtab);
                }
            }
            ExecutableItem::StructInstance => {}
            ExecutableItem::EnumInstance { .. } => {}
            ExecutableItem::BuiltinEntity(_, _) | ExecutableItem::BuiltinPipeline(_, _) => {}
        }
    }

    let mut result = vec![];
    while let Some(item) = state.next_target() {
        let original_item = items.get(&item.source_name);

        let mut reg_name_map = HashMap::new();
        match original_item {
            Some((ExecutableItem::Entity(e), old_type_state)) => {
                let mut type_state = old_type_state.clone();
                if !e.head.type_params.is_empty() {
                    let generic_list = type_state
                        .get_generic_list(&GenericListToken::Definition(
                            e.name.name_id().inner.clone(),
                        ))
                        .clone();

                    for (source_param, new) in e.head.type_params.iter().zip(item.params.iter()) {
                        let source_var = &generic_list[&source_param.name_id()];

                        match type_state
                            .unify(source_var, new, symtab.symtab())
                            .map_normal_err(|(expected, got)| {
                                spade_typeinference::error::Error::UnspecifiedTypeError {
                                    expected,
                                    got,
                                    loc: e.loc(),
                                }
                            }) {
                            Ok(_) => {}
                            Err(e) => {
                                result.push(Err(Error::UnificationError(e)));
                            }
                        }
                    }
                }

                // Apply passes to the type checked module
                let mut e = e.clone();
                let pass_result = e.apply(&mut LowerMethods {
                    type_state: &type_state,
                    items: item_list,
                });
                if let Err(e) = pass_result {
                    result.push(Err(e));
                    continue;
                }

                let out = generate_entity(
                    &e.inner,
                    item.new_name,
                    symtab,
                    idtracker,
                    &type_state,
                    item_list,
                    &mut state,
                    diag_handler,
                    name_source_map,
                )
                .map(|mir| MirOutput {
                    mir,
                    type_state: type_state.clone(),
                    reg_name_map,
                });
                result.push(out);
            }
            Some((ExecutableItem::Pipeline(p), type_state)) => {
                if !p.head.type_params.is_empty() {
                    todo!("Support generic pipelines")
                }

                // Apply passes to the type checked module
                let mut p = p.clone();
                let pass_result = p.apply(&mut LowerMethods {
                    type_state: &type_state,
                    items: item_list,
                });
                if let Err(e) = pass_result {
                    result.push(Err(e));
                }

                let out = generate_pipeline(
                    &p.inner,
                    type_state,
                    symtab,
                    idtracker,
                    item_list,
                    &mut reg_name_map,
                    &mut state,
                    diag_handler,
                    name_source_map,
                )
                .map(|mir| MirOutput {
                    mir,
                    type_state: type_state.clone(),
                    reg_name_map,
                });
                result.push(out);
            }
            Some((ExecutableItem::StructInstance, _)) => {
                panic!("Requesting compilation of struct instance as module")
            }
            Some((ExecutableItem::EnumInstance { .. }, _)) => {
                panic!("Requesting compilation of enum instance as module")
            }
            Some(
                (ExecutableItem::BuiltinEntity(_, _), _)
                | (ExecutableItem::BuiltinPipeline(_, _), _),
            ) => {
                panic!("Requesting compilation of builtin unit")
            }
            None => {
                panic!(
                    "Requesting compilation of {} but no such item is present",
                    item.source_name
                )
            }
        }
    }
    result
}
