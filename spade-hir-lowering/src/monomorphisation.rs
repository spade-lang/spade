use std::collections::{BTreeMap, HashMap, VecDeque};

use itertools::Itertools;
use mir::passes::MirPass;
use spade_common::location_info::Loc;
use spade_common::{id_tracker::ExprIdTracker, location_info::WithLocation, name::NameID};
use spade_diagnostics::diagnostic::{Message, Subdiagnostic};
use spade_diagnostics::{diag_anyhow, DiagHandler, Diagnostic};
use spade_hir::{symbol_table::FrozenSymtab, ExecutableItem, ItemList, UnitName};
use spade_mir as mir;
use spade_typeinference::equation::KnownTypeVar;
use spade_typeinference::error::UnificationErrorExt;
use spade_typeinference::trace_stack::{format_trace_stack, TraceStackEntry};
use spade_typeinference::{GenericListToken, HasType, TypeState};

use crate::error::Result;
use crate::generate_unit;
use crate::name_map::NameSourceMap;
use crate::passes::disallow_inout_bindings::InOutChecks;
use crate::passes::disallow_zero_size::DisallowZeroSize;
use crate::passes::flatten_regs::FlattenRegs;
use crate::passes::lower_lambda_defs::{LambdaReplacement, LowerLambdaDefs};
use crate::passes::lower_methods::LowerMethods;
use crate::passes::lower_type_level_if::LowerTypeLevelIf;
use crate::passes::pass::{Pass, Passable};

/// An item to be monomorphised
#[derive(Clone, Hash, PartialEq, Eq)]
pub struct MonoItem {
    /// The name of the original item which this is a monomorphised version of
    pub source_name: Loc<NameID>,
    /// The new name of the new item
    pub new_name: UnitName,
    /// The types to replace the generic types in the item. Positional replacement.
    /// These are TypeVars which have to be fully known
    pub params: Vec<KnownTypeVar>,
}

pub struct MonoState {
    /// List of mono items left to compile
    to_compile: VecDeque<MonoItem>,
    /// Mapping between items with types specified and names
    translation: BTreeMap<(NameID, Vec<KnownTypeVar>), NameID>,
    /// Locations in the code where compilation of the Mono item was requested. None
    /// if this is non-generic
    request_points: HashMap<MonoItem, Option<(MonoItem, Loc<()>)>>,
}

impl Default for MonoState {
    fn default() -> Self {
        Self::new()
    }
}

impl MonoState {
    pub fn new() -> MonoState {
        MonoState {
            to_compile: VecDeque::new(),
            translation: BTreeMap::new(),
            request_points: HashMap::new(),
        }
    }

    /// Request compilation of a unit with the specified type parameters, returning the name of the
    /// unit which will be compiled with these parameters. It is up to the caller of this
    /// function to ensure that the type params are valid for this item.
    pub fn request_compilation(
        &mut self,
        source_name: UnitName,
        reuse_nameid: bool,
        params: Vec<KnownTypeVar>,
        symtab: &mut FrozenSymtab,
        request_point: Option<(MonoItem, Loc<()>)>,
    ) -> NameID {
        match self
            .translation
            .get(&(source_name.name_id().inner.clone(), params.clone()))
        {
            Some(prev) => prev.clone(),
            None => {
                let new_name = if reuse_nameid {
                    source_name.name_id().inner.clone()
                } else {
                    symtab.new_name(source_name.name_id().1.clone())
                };

                // Wrap the new name in a UnitName to match the source. Previous steps
                // ensure that the unit name is general enough to not cause name collisions
                let new_unit_name = match &source_name {
                    UnitName::WithID(_) => UnitName::WithID(new_name.clone().nowhere()),
                    UnitName::FullPath(_) => UnitName::FullPath(new_name.clone().nowhere()),
                    UnitName::Unmangled(source, _) => {
                        UnitName::Unmangled(source.clone(), new_name.clone().nowhere())
                    }
                };

                let item = MonoItem {
                    source_name: source_name.name_id().clone(),
                    new_name: new_unit_name,
                    params: params.clone(),
                };
                self.request_points.insert(item.clone(), request_point);

                self.translation.insert(
                    (source_name.name_id().inner.clone(), params.clone()),
                    new_name.clone(),
                );
                self.to_compile.push_back(item);
                new_name
            }
        }
    }

    fn next_target(&mut self) -> Option<MonoItem> {
        self.to_compile.pop_front()
    }

    fn add_mono_traceback(&self, diagnostic: Diagnostic, item: &MonoItem) -> Diagnostic {
        let parent = self.request_points.get(item).and_then(|x| x.clone());
        if let Some((next_parent, loc)) = parent {
            let generic_params = item.params.iter().map(|p| format!("{p}")).join(", ");

            let new = diagnostic.subdiagnostic(Subdiagnostic::TemplateTraceback {
                span: loc.into(),
                message: Message::from(format!("{}<{}>", item.source_name, generic_params)),
            });

            self.add_mono_traceback(new, &next_parent)
        } else {
            diagnostic
        }
    }
}

pub struct MirOutput {
    pub mir: mir::Entity,
    pub type_state: TypeState,
    /// Mapping between new names for registers and their previous value. Used
    /// to add type information for registers generated by pipelines
    pub reg_name_map: BTreeMap<NameID, NameID>,
}

pub fn compile_items(
    items: &BTreeMap<&NameID, (&ExecutableItem, TypeState)>,
    symtab: &mut FrozenSymtab,
    idtracker: &mut ExprIdTracker,
    name_source_map: &mut NameSourceMap,
    item_list: &ItemList,
    diag_handler: &mut DiagHandler,
    opt_passes: &[&dyn MirPass],
    impl_type_state: &TypeState,
) -> Vec<Result<MirOutput>> {
    // Build a map of items to use for compilation later. Also push all non
    // generic items to the compilation queue

    let mut state = MonoState::new();

    for (item, _) in items.values() {
        match item {
            ExecutableItem::Unit(u) => {
                if u.head.get_type_params().is_empty() {
                    state.request_compilation(u.name.clone(), true, vec![], symtab, None);
                }
            }
            ExecutableItem::StructInstance => {}
            ExecutableItem::EnumInstance { .. } => {}
            ExecutableItem::ExternUnit(_, _) => {}
        }
    }

    let mut body_replacements: HashMap<NameID, LambdaReplacement> = HashMap::new();

    let mut result = vec![];
    'item_loop: while let Some(item) = state.next_target() {
        let original_item = items.get(&item.source_name.inner);

        let mut reg_name_map = BTreeMap::new();
        match original_item {
            Some((ExecutableItem::Unit(u), old_type_state)) => {
                let (u, old_type_state) =
                    if let Some(replacement) = body_replacements.get(&u.name.name_id().inner) {
                        let new_unit = match replacement.replace_in(u.clone(), idtracker) {
                            Ok(u) => u,
                            Err(e) => {
                                result.push(Err(state.add_mono_traceback(e, &item)));
                                break 'item_loop;
                            }
                        };

                        (&new_unit.clone(), &{
                            let mut type_state = impl_type_state.create_child();
                            let type_ctx = &spade_typeinference::Context {
                                symtab: symtab.symtab(),
                                items: item_list,
                                trait_impls: &old_type_state.trait_impls,
                            };
                            let unification_result = type_state.visit_unit_with_preprocessing(
                                &new_unit,
                                |type_state, unit, generic_list, ctx| {
                                    let gl = type_state
                                        .get_generic_list(generic_list)
                                        .ok_or_else(|| {
                                            diag_anyhow!(unit, "Did not have a generic list")
                                        })?
                                        .clone();
                                    for (i, (_, ty)) in replacement.arguments.iter().enumerate() {
                                        let old_ty = gl
                                            .get(&unit.head.get_type_params()[i].name_id)
                                            .ok_or_else(|| {
                                                diag_anyhow!(
                                                    unit,
                                                    "Did not have an entry for argument {i}"
                                                )
                                            })?
                                            .clone();

                                        ty.insert(type_state)
                                            .unify_with(&old_ty, type_state)
                                            .commit(type_state, ctx)
                                            .into_default_diagnostic(unit, type_state)?;
                                    }
                                    Ok(())
                                },
                                type_ctx,
                            );
                            if let Err(e) = unification_result {
                                result.push(Err(state.add_mono_traceback(e, &item)));
                                break 'item_loop;
                            }

                            type_state
                        })
                    } else {
                        (u, old_type_state)
                    };

                let type_ctx = &spade_typeinference::Context {
                    symtab: symtab.symtab(),
                    items: item_list,
                    trait_impls: &old_type_state.trait_impls,
                };
                let mut type_state = old_type_state.create_child();
                let generic_list_token = if !u.head.get_type_params().is_empty() {
                    Some(GenericListToken::Definition(u.name.name_id().inner.clone()))
                } else {
                    None
                };

                if let Some(generic_list_token) = &generic_list_token {
                    let generic_list = type_state
                        .get_generic_list(generic_list_token)
                        .expect("Found no generic list  when monomorphizing")
                        .clone();
                    for (source_param, new) in
                        u.head.get_type_params().iter().zip(item.params.iter())
                    {
                        let source_var = &generic_list[&source_param.name_id()];

                        type_state
                            .trace_stack
                            .push(TraceStackEntry::Message(format!(
                                "Performing mono replacement of {source_var} -> {new:?}",
                                source_var = source_var.debug_resolve(&type_state),
                            )));

                        let tvar = new.insert(&mut type_state);
                        match type_state
                            .unify(&tvar, source_var, type_ctx)
                            .into_default_diagnostic(u, &type_state)
                            .and_then(|_| type_state.check_requirements(true, type_ctx))
                        {
                            Ok(_) => {}
                            Err(e) => {
                                result.push(Err(state.add_mono_traceback(e, &item)));
                                continue 'item_loop;
                            }
                        }
                    }

                    if std::env::var("SPADE_TRACE_TYPEINFERENCE").is_ok() {
                        println!(
                            "After mono of {} replacing {} with {}",
                            u.inner.name,
                            u.head
                                .get_type_params()
                                .iter()
                                .map(|p| format!("{p:?}"))
                                .join(", "),
                            item.params.iter().map(|p| format!("{p}")).join(", ")
                        );
                        type_state.print_equations();
                        println!("{}", format_trace_stack(&type_state));
                    }
                }

                // Apply passes to the type checked module
                let mut u = u.clone();
                let passes = [
                    &mut LowerLambdaDefs {
                        type_state: &type_state,
                        replacements: &mut body_replacements,
                    } as &mut dyn Pass,
                    &mut FlattenRegs {
                        type_state: &type_state,
                        items: item_list,
                        symtab,
                    } as &mut dyn Pass,
                    &mut LowerMethods {
                        type_state: &type_state,
                        items: item_list,
                        symtab,
                    } as &mut dyn Pass,
                    &mut LowerTypeLevelIf {
                        type_state: &type_state,
                        items: item_list,
                        symtab,
                        allowed_ids: Default::default(),
                    } as &mut dyn Pass,
                    &mut InOutChecks {
                        type_state: &type_state,
                        items: item_list,
                        symtab,
                    } as &mut dyn Pass,
                    &mut DisallowZeroSize {
                        type_state: &type_state,
                        items: item_list,
                        symtab,
                    } as &mut dyn Pass,
                ];
                for pass in passes {
                    let pass_result = u.apply(pass);
                    if let Err(e) = pass_result {
                        result.push(Err(e));
                        continue 'item_loop;
                    }
                }

                let self_mono_item = Some(item.clone());
                let out = generate_unit(
                    &u.inner,
                    item.new_name.clone(),
                    &mut type_state,
                    symtab,
                    idtracker,
                    item_list,
                    &generic_list_token,
                    &mut reg_name_map,
                    &mut state,
                    diag_handler,
                    name_source_map,
                    self_mono_item,
                    opt_passes,
                )
                .map_err(|e| state.add_mono_traceback(e, &item))
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
            Some((ExecutableItem::ExternUnit(_, _), _)) => {
                panic!("Requesting compilation of extern unit")
            }
            None => {}
        }
    }
    result
}
