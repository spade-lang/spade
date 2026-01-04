use std::{
    collections::BTreeMap,
    sync::{Arc, RwLock},
};

use color_eyre::eyre::anyhow;
use itertools::Itertools;
use rustc_hash::FxHashMap as HashMap;
use serde::{Deserialize, Serialize};
use spade_ast_lowering::id_tracker::{ExprIdTracker, ImplIdTracker};
use spade_common::location_info::WithLocation;
use spade_common::name::NameID;
use spade_hir::{
    query::QueryCache,
    symbol_table::{FrozenSymtab, SymbolTable},
    ItemList,
};
use spade_hir_lowering::{
    name_map::{NameSource, NamedValue},
    NameSourceMap,
};
use spade_mir::{
    renaming::{VerilogNameMap, VerilogNameSource},
    unit_name::InstanceMap,
};
use spade_typeinference::{
    equation::TypedExpression, traits::TraitImplList, HasType, OwnedTypeState, SharedTypeState,
    TypeState,
};
use spade_types::ConcreteType;

use spade_common::sizes::{add_field, SerializedSize};

#[derive(Serialize, Deserialize)]
pub struct StoredMirContext {
    /// Mapping to concrete types for this instantiation of the entity
    pub type_state: OwnedTypeState,
    pub reg_name_map: BTreeMap<NameID, NameID>,
    pub verilog_name_map: VerilogNameMap,
}

impl StoredMirContext {
    fn with_shared(self, shared: Arc<SharedTypeState>) -> MirContext {
        MirContext {
            type_state: TypeState {
                owned: self.type_state,
                shared,
            },
            reg_name_map: self.reg_name_map,
            verilog_name_map: self.verilog_name_map,
        }
    }
}

impl SerializedSize for StoredMirContext {
    fn accumulate_size(
        &self,
        field: &[&'static str],
        into: &mut HashMap<Vec<&'static str>, usize>,
    ) {
        let Self {
            type_state,
            reg_name_map,
            verilog_name_map,
        } = self;

        let mut ts_path = field.to_vec();
        ts_path.push("type_state");
        type_state.accumulate_size(&ts_path, into);

        add_field(field, "type_state", type_state, into);
        add_field(field, "reg_name_map", reg_name_map, into);
        add_field(field, "verilog_name_map", verilog_name_map, into);
    }
}

pub struct MirContext {
    /// Mapping to concrete types for this instantiation of the entity
    pub type_state: TypeState,
    pub reg_name_map: BTreeMap<NameID, NameID>,
    pub verilog_name_map: VerilogNameMap,
}

impl MirContext {
    fn to_stored(self) -> StoredMirContext {
        StoredMirContext {
            type_state: self.type_state.owned,
            reg_name_map: self.reg_name_map,
            verilog_name_map: self.verilog_name_map,
        }
    }
}

/// All the state required in order to add more things to the compilation process
#[derive(Serialize, Deserialize)]
pub struct StoredCompilerState {
    // (filename, file content) of all the compiled files
    pub code: Vec<(String, String)>,
    pub symtab: FrozenSymtab,
    pub idtracker: Arc<ExprIdTracker>,
    pub impl_idtracker: ImplIdTracker,
    pub item_list: ItemList,
    pub name_source_map: Arc<RwLock<NameSourceMap>>,
    pub instance_map: InstanceMap,
    pub mir_context: HashMap<NameID, StoredMirContext>,
    pub shared_type_state: Arc<SharedTypeState>,
    pub trait_impl_list: TraitImplList,
}

impl StoredCompilerState {
    pub fn into_compiler_state(self) -> CompilerState {
        let Self {
            code,
            symtab,
            idtracker,
            impl_idtracker,
            item_list,
            name_source_map,
            instance_map,
            mir_context,
            shared_type_state,
            trait_impl_list,
        } = self;

        CompilerState {
            code,
            symtab,
            idtracker,
            impl_idtracker,
            item_list,
            name_source_map,
            instance_map,
            mir_context: mir_context
                .into_iter()
                .map(|(k, v)| (k, v.with_shared(Arc::clone(&shared_type_state))))
                .collect(),
            shared_type_state,
            trait_impl_list,
        }
    }
}

pub struct CompilerState {
    // (filename, file content) of all the compiled files
    pub code: Vec<(String, String)>,
    pub symtab: FrozenSymtab,
    pub idtracker: Arc<ExprIdTracker>,
    pub impl_idtracker: ImplIdTracker,
    pub item_list: ItemList,
    pub name_source_map: Arc<RwLock<NameSourceMap>>,
    pub instance_map: InstanceMap,
    pub mir_context: HashMap<NameID, MirContext>,
    pub shared_type_state: Arc<SharedTypeState>,
    pub trait_impl_list: TraitImplList,
}

impl CompilerState {
    pub fn into_stored(self) -> StoredCompilerState {
        StoredCompilerState {
            code: self.code,
            symtab: self.symtab,
            idtracker: self.idtracker,
            impl_idtracker: self.impl_idtracker,
            item_list: self.item_list,
            name_source_map: self.name_source_map,
            instance_map: self.instance_map,
            mir_context: self
                .mir_context
                .into_iter()
                .map(|(k, v)| (k, v.to_stored()))
                .collect(),
            shared_type_state: self.shared_type_state,
            trait_impl_list: self.trait_impl_list,
        }
    }

    pub fn build_query_cache<'a>(&'a self) -> QueryCache {
        QueryCache::from_item_list(&self.item_list)
    }

    // Attempts to demangle the specified string to the corresponding snippet of source code
    pub fn demangle_string(&self, mangled: &str) -> Option<String> {
        // We'll need to first mangle the ValueNames into actual strings to search.
        // NOTE: A smart non-lazy person would do this once, not every time we ask
        // for demangling
        let string_map = self
            .name_source_map
            .read()
            .unwrap()
            .inner
            .iter()
            .flat_map(|(k, v)| {
                vec![
                    (k.var_name(), v.clone()),
                    (k.backward_var_name(), v.clone()),
                ]
            })
            .collect::<HashMap<_, _>>();

        string_map.get(mangled).map(|name| match name {
            NamedValue::Primary(source) => self.demangle_name_source(source),
            NamedValue::Secondary(source, description) => {
                format!("{} ({description})", self.demangle_name_source(source))
            }
        })
    }

    pub fn demangle_name_source(&self, source: &NameSource) -> String {
        match source {
            NameSource::Name(n) => format!("{n}"),
            NameSource::Expr(e) => {
                format!(
                    "(id) {}",
                    &self.code[e.file_id].1[e.span.start().to_usize()..e.span.end().to_usize()]
                )
            }
        }
    }

    pub fn name_source_of_hierarchical_value(
        &self,
        top_module: &NameID,
        hierarchy: &[String],
        query_cache: &QueryCache,
    ) -> color_eyre::Result<Option<NameSource>> {
        let (verilog_source, _mir_ctx) = source_of_hierarchical_value(
            top_module,
            hierarchy,
            &self.instance_map,
            &self.mir_context,
        )?;

        match verilog_source {
            VerilogNameSource::ForwardName(n) | VerilogNameSource::BackwardName(n) => {
                Ok(Some(NameSource::Name(n.clone().nowhere())))
            }
            VerilogNameSource::ForwardExpr(id) | VerilogNameSource::BackwardExpr(id) => {
                Ok(query_cache
                    .id_to_expression(*id)
                    .map(|loc_expr| NameSource::Expr(loc_expr.map_ref(|_| *id))))
            }
        }
    }

    pub fn type_of_hierarchical_value(
        &self,
        top_module: &NameID,
        hierarchy: &[String],
    ) -> color_eyre::Result<ConcreteType> {
        type_of_hierarchical_value(
            top_module,
            hierarchy,
            &self.instance_map,
            &self.mir_context,
            self.symtab.symtab(),
            &self.item_list,
        )
    }
}

impl SerializedSize for StoredCompilerState {
    fn accumulate_size(
        &self,
        field: &[&'static str],
        into: &mut HashMap<Vec<&'static str>, usize>,
    ) {
        let Self {
            code,
            symtab,
            idtracker,
            impl_idtracker,
            item_list,
            name_source_map,
            instance_map,
            mir_context,
            shared_type_state,
            trait_impl_list,
        } = self;

        for (_, mc) in mir_context {
            let mut path = field.to_vec();
            path.push("mir_context");
            mc.accumulate_size(&path, into);
        }

        add_field(field, "code", code, into);
        add_field(field, "symtab", symtab, into);
        add_field(field, "idtracker", idtracker, into);
        add_field(field, "impl_idtracker", impl_idtracker, into);
        add_field(field, "item_list", item_list, into);
        add_field(field, "name_source_map", name_source_map, into);
        add_field(field, "instance_map", instance_map, into);
        add_field(field, "mir_context", mir_context, into);
        add_field(field, "shared_type_state", shared_type_state, into);
        add_field(field, "trait_impl_list", trait_impl_list, into);
    }
}

pub fn source_of_hierarchical_value<'a>(
    top_module: &'a NameID,
    hierarchy: &'a [String],
    instance_map: &'a InstanceMap,
    mir_contexts: &'a HashMap<NameID, MirContext>,
) -> color_eyre::Result<(&'a VerilogNameSource, &'a MirContext)> {
    let mut hierarchy = Vec::from(hierarchy);
    let value_name = hierarchy.pop().unwrap();
    hierarchy.reverse();

    // Lookup the name_id of the instance we want to query for the value_name in
    let mut current_unit = top_module;
    let mut path_so_far = vec![format!("{}", top_module)];
    while let Some(next_instance_name) = hierarchy.pop() {
        let local_map = instance_map
            .inner
            .get(&current_unit.clone())
            .ok_or_else(|| {
                let candidates = instance_map
                    .inner
                    .keys()
                    .map(|n| format!("    {n}"))
                    .collect::<Vec<_>>();

                let candidates_msg = if candidates.is_empty() {
                    String::new()
                } else {
                    format!("  candidates\n    {}", candidates.join("    \n"))
                };

                anyhow!(
                    "Did not find a unit named {} in {}\n{candidates_msg}",
                    &next_instance_name,
                    path_so_far.join(".")
                )
            })?;
        let next = local_map.get(&next_instance_name);
        if let Some(next) = next {
            current_unit = next;
        } else {
            let candidates_msg = if local_map.is_empty() {
                String::new()
            } else {
                format!("\n  candidates:\n    {}", local_map.keys().join("    \n"))
            };

            return Err(anyhow!(
                "{} has no spade unit instance named {next_instance_name}{candidates_msg}",
                path_so_far.join(".")
            ));
        };
        path_so_far.push(next_instance_name.to_string());
    }

    // Look up the mir context of the unit we are observing
    let mir_ctx = mir_contexts
        .get(current_unit)
        .ok_or_else(|| anyhow!("Did not find information a unit named {current_unit}"))?;

    let source = mir_ctx
        .verilog_name_map
        .lookup_name(&value_name)
        .ok_or_else(|| {
            anyhow!(
                "Did not find spade variable for verilog identifier '{value_name}' in '{path}'",
                path = path_so_far.join(".")
            )
        })?;

    Ok((source, mir_ctx))
}

pub fn type_of_hierarchical_value(
    top_module: &NameID,
    hierarchy: &[String],
    instance_map: &InstanceMap,
    mir_contexts: &HashMap<NameID, MirContext>,
    symtab: &SymbolTable,
    item_list: &ItemList,
) -> color_eyre::Result<ConcreteType> {
    let (source, mir_ctx) =
        source_of_hierarchical_value(top_module, hierarchy, instance_map, mir_contexts)?;

    let typed_expr = match source {
        VerilogNameSource::ForwardName(n) => TypedExpression::Name(n.clone()),
        VerilogNameSource::ForwardExpr(id) => TypedExpression::Id(*id),
        VerilogNameSource::BackwardName(_) | VerilogNameSource::BackwardExpr(_) => {
            return Err(anyhow!("Translation of backward port types is unsupported"))
        }
    };

    let ty = typed_expr
        .try_get_type(&mir_ctx.type_state)
        .ok_or_else(|| anyhow!("Did not find a type for {}", typed_expr))?;

    let concrete = mir_ctx
        .type_state
        .ungenerify_type(&ty, symtab, &item_list.types)
        .ok_or_else(|| {
            anyhow!(
                "Tried to ungenerify generic type {ty}",
                ty = ty.display(&mir_ctx.type_state)
            )
        })?;

    Ok(concrete)
}
