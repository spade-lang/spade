use std::collections::{BTreeMap, VecDeque};
use std::sync::{Arc, Condvar, Mutex, RwLock};

use itertools::Itertools;
use mir::passes::MirPass;
use rustc_hash::FxHashMap as HashMap;
use spade_common::location_info::Loc;
use spade_common::{id_tracker::ExprIdTracker, location_info::WithLocation, name::NameID};
use spade_diagnostics::diagnostic::{Message, Subdiagnostic};
use spade_diagnostics::{diag_anyhow, Diagnostic};
use spade_hir::Unit;
use spade_hir::{symbol_table::FrozenSymtab, ExecutableItem, ItemList, UnitName};
use spade_mir as mir;
use spade_typeinference::equation::KnownTypeVar;
use spade_typeinference::error::UnificationErrorExt;
use spade_typeinference::trace_stack::format_trace_stack;
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
use crate::passes::pass::Passable;

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

pub struct MonoStateInner {
    /// List of mono items left to compile
    to_compile: VecDeque<MonoItem>,
    /// Mapping between items with types specified and names
    translation: BTreeMap<(NameID, Vec<KnownTypeVar>), NameID>,
    /// Locations in the code where compilation of the Mono item was requested. None
    /// if this is non-generic
    request_points: HashMap<MonoItem, Option<(MonoItem, Loc<()>)>>,

    /// Number of items which we we have requested compilation of but which have not
    /// been completed yet.
    works_in_progress: u64,
}

pub struct MonoState {
    inner: Mutex<MonoStateInner>,
    cond: Condvar,
}

impl Default for MonoState {
    fn default() -> Self {
        Self::new()
    }
}

impl MonoState {
    pub fn new() -> MonoState {
        let inner = MonoStateInner {
            to_compile: VecDeque::new(),
            translation: BTreeMap::new(),
            request_points: HashMap::default(),
            works_in_progress: 0,
        };

        MonoState {
            inner: Mutex::new(inner),
            cond: Condvar::new(),
        }
    }

    /// Request compilation of a unit with the specified type parameters, returning the name of the
    /// unit which will be compiled with these parameters. It is up to the caller of this
    /// function to ensure that the type params are valid for this item.
    pub fn request_compilation(
        &self,
        source_name: UnitName,
        reuse_nameid: bool,
        params: Vec<KnownTypeVar>,
        symtab: &FrozenSymtab,
        request_point: Option<(MonoItem, Loc<()>)>,
    ) -> NameID {
        let mut inner = self.inner.lock().unwrap();

        match inner
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
                inner.request_points.insert(item.clone(), request_point);

                inner.translation.insert(
                    (source_name.name_id().inner.clone(), params.clone()),
                    new_name.clone(),
                );
                inner.to_compile.push_back(item);

                self.cond.notify_all();

                new_name
            }
        }
    }

    fn report_done(&self) {
        self.inner.lock().unwrap().works_in_progress -= 1;
        self.cond.notify_all();
    }

    fn next_target(&self) -> Option<MonoItem> {
        let mut inner = self.inner.lock().unwrap();

        loop {
            if let Some(result) = inner.to_compile.pop_front() {
                inner.works_in_progress += 1;
                return Some(result);
            }
            if inner.works_in_progress == 0 {
                return None;
            }
            inner = self.cond.wait(inner).unwrap();
        }
    }

    fn add_mono_traceback(&self, diagnostic: Diagnostic, item: &MonoItem) -> Diagnostic {
        let parent = self
            .inner
            .lock()
            .unwrap()
            .request_points
            .get(item)
            .and_then(|x| x.clone());
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

type BodyReplacements = HashMap<(NameID, Vec<KnownTypeVar>), LambdaReplacement>;

pub fn compile_items(
    items: &BTreeMap<&NameID, (&ExecutableItem, TypeState)>,
    symtab: &FrozenSymtab,
    idtracker: &Arc<ExprIdTracker>,
    name_source_map: &Arc<RwLock<NameSourceMap>>,
    item_list: &ItemList,
    opt_passes: &[&(dyn MirPass + Send + Sync)],
    impl_type_state: &TypeState,
) -> Vec<Result<MirOutput>> {
    // Build a map of items to use for compilation later. Also push all non
    // generic items to the compilation queue

    let state = Arc::new(MonoState::new());

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

    let body_replacements: Arc<RwLock<BodyReplacements>> =
        Arc::new(RwLock::new(HashMap::default()));

    let result = Arc::new(RwLock::new(vec![]));
    {
        let result = Arc::clone(&result);
        let state = Arc::clone(&state);
        rayon::scope(move |s| {
            while let Some(item) = state.next_target() {
                let state = Arc::clone(&state);
                let name_source_map = Arc::clone(&name_source_map);
                let result = Arc::clone(&result);
                let idtracker = Arc::clone(&idtracker);
                let body_replacements = Arc::clone(&body_replacements);

                s.spawn(move |_s| {
                    monoprhipze_item(
                        item,
                        items,
                        body_replacements,
                        &idtracker,
                        &state,
                        symtab,
                        item_list,
                        impl_type_state,
                        &name_source_map,
                        opt_passes,
                        &result,
                    );
                    state.report_done();
                });
            }
        });
    }
    let mut result = result.write().unwrap();
    let result = std::mem::replace(&mut *result, vec![]);
    result
}

fn monoprhipze_item(
    item: MonoItem,
    items: &BTreeMap<&NameID, (&ExecutableItem, TypeState)>,
    body_replacements: Arc<RwLock<BodyReplacements>>,
    idtracker: &Arc<ExprIdTracker>,
    state: &Arc<MonoState>,
    symtab: &FrozenSymtab,
    item_list: &ItemList,
    impl_type_state: &TypeState,
    name_source_map: &Arc<RwLock<NameSourceMap>>,
    opt_passes: &[&(dyn MirPass + Send + Sync)],

    result: &RwLock<Vec<Result<MirOutput>>>,
) {
    let original_item = items.get(&item.source_name.inner);

    let mut reg_name_map = BTreeMap::new();
    let unit;
    match original_item {
        Some((ExecutableItem::Unit(u), old_type_state)) => {
            let (u, mut preprocessor) = if let Some(replacement) = body_replacements
                .write()
                .unwrap()
                .remove(&(u.name.name_id().inner.clone(), item.params.clone()))
            {
                let new_unit = match replacement.replace_in(u.clone(), &idtracker) {
                    Ok(u) => {
                        unit = u;
                        &unit
                    }
                    Err(e) => {
                        result
                            .write()
                            .unwrap()
                            .push(Err(state.add_mono_traceback(e, &item)));
                        return;
                    }
                };

                (
                    new_unit,
                    Some(
                        move |type_state: &mut TypeState,
                              unit: &Loc<Unit>,
                              generic_list: &GenericListToken,
                              ctx: &spade_typeinference::Context|
                              -> Result<_> {
                            let gl = type_state
                                .get_generic_list(generic_list)
                                .ok_or_else(|| diag_anyhow!(unit, "Did not have a generic list"))?
                                .clone();
                            for (i, (_, ty)) in replacement.arguments.into_iter().enumerate() {
                                let old_ty = gl
                                    .get(&unit.head.get_type_params()[i].name_id)
                                    .ok_or_else(|| {
                                        diag_anyhow!(unit, "Did not have an entry for argument {i}")
                                    })?
                                    .clone();

                                ty.insert(type_state)
                                    .unify_with(&old_ty, type_state)
                                    .commit(type_state, ctx)
                                    .into_default_diagnostic(unit, type_state)?;
                            }

                            Ok(())
                        },
                    ),
                )
            } else {
                (u, None)
            };

            let type_ctx = &spade_typeinference::Context {
                symtab: symtab.symtab(),
                items: item_list,
                trait_impls: old_type_state.trait_impls.clone(),
            };

            // If the unit is generic, we're going to re-do type inference from scratch
            // with the known types from the outer context
            let (mut type_state, generic_list_token) = if !u.head.get_type_params().is_empty() {
                let mut type_state = impl_type_state.create_child();

                let preprocessor = preprocessor.take();
                let u = &u;
                let item = &item;
                let revisit_result = type_state.visit_unit_with_preprocessing(
                    u,
                    move |type_state, unit, generic_list, ctx| {
                        let gl = type_state
                            .get_generic_list(generic_list)
                            .ok_or_else(|| diag_anyhow!(unit, "Did not have a generic list"))?
                            .clone();

                        let generic_map = u
                            .head
                            .get_type_params()
                            .iter()
                            .zip(item.params.iter())
                            .map(|(param, outer_var)| {
                                (param.name_id().at_loc(param), outer_var.clone())
                            })
                            .collect::<Vec<_>>();

                        for (name, outer_var) in generic_map {
                            let inner_var = gl.get(&name).ok_or_else(|| {
                                diag_anyhow!(name.clone(), "Did not find a generic type for {name}")
                            })?;

                            let outer_var = outer_var.insert(type_state);
                            type_state
                                .unify(&inner_var.clone(), &outer_var, ctx)
                                .into_default_diagnostic(name, type_state)?;
                        }

                        if let Some(preprocessor) = preprocessor {
                            preprocessor(type_state, unit, generic_list, ctx)?;
                        }

                        Ok(())
                    },
                    type_ctx,
                );

                if std::env::var("SPADE_TRACE_TYPEINFERENCE").is_ok() {
                    println!("After mono of {} with {:?}", u.inner.name, item.params);
                    type_state.print_equations();
                    println!("{}", format_trace_stack(&type_state));
                }

                let mut failed = false;
                for diag in type_state.diags.drain() {
                    result
                        .write()
                        .unwrap()
                        .push(Err(state.add_mono_traceback(diag, &item)));
                    failed = true
                }

                match revisit_result {
                    Ok(_) => {}
                    Err(e) => {
                        result
                            .write()
                            .unwrap()
                            .push(Err(state.add_mono_traceback(e, &item)));
                        failed = true
                    }
                }
                if failed {
                    return;
                }

                let tok = Some(GenericListToken::Definition(u.name.name_id().inner.clone()));

                (type_state, tok)
            } else {
                (old_type_state.clone(), None)
            };

            // Apply passes to the type checked module
            let mut u = u.clone();

            macro_rules! run_pass (
            ($pass:expr) => {
                let pass_result = u.apply(&mut $pass);
                if let Err(e) = pass_result {
                    result.write().unwrap().push(Err(e));
                    return;
                }
            };
        );

            run_pass!(LowerLambdaDefs {
                type_state: &mut type_state,
                idtracker: &idtracker,
                replacements: body_replacements,
            });
            run_pass!(FlattenRegs {
                type_state: &type_state,
                items: item_list,
                symtab,
            });
            run_pass!(LowerMethods {
                type_state: &type_state,
                items: item_list,
                symtab,
            });
            run_pass!(LowerTypeLevelIf {
                type_state: &type_state,
                items: item_list,
                symtab,
                allowed_ids: Default::default(),
            });
            run_pass!(InOutChecks {
                type_state: &type_state,
                items: item_list,
                symtab,
            });
            run_pass!(DisallowZeroSize {
                type_state: &type_state,
                items: item_list,
                symtab,
            });

            let self_mono_item = Some(item.clone());
            let out = generate_unit(
                &u.inner,
                item.new_name.clone(),
                &mut type_state,
                symtab,
                &idtracker,
                item_list,
                &generic_list_token,
                &mut reg_name_map,
                &state,
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
            result.write().unwrap().push(out);
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
