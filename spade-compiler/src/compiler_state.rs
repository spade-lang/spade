use std::collections::{BTreeMap, HashMap};

use color_eyre::eyre::anyhow;
use itertools::Itertools;
use serde::{Deserialize, Serialize};
use spade_ast_lowering::id_tracker::{ExprIdTracker, ImplIdTracker};
use spade_common::name::NameID;
use spade_hir::{
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
use spade_typeinference::{equation::TypedExpression, TypeState};
use spade_types::ConcreteType;

#[derive(Serialize, Deserialize)]
pub struct MirContext {
    /// Mapping to concrete types for this instantiation of the entity
    pub type_state: TypeState,
    pub reg_name_map: BTreeMap<NameID, NameID>,
    pub verilog_name_map: VerilogNameMap,
}

/// All the state required in order to add more things to the compilation process
#[derive(Serialize, Deserialize)]
pub struct CompilerState {
    // (filename, file content) of all the compiled files
    pub code: Vec<(String, String)>,
    pub symtab: FrozenSymtab,
    pub idtracker: ExprIdTracker,
    pub impl_idtracker: ImplIdTracker,
    pub item_list: ItemList,
    pub name_source_map: NameSourceMap,
    pub instance_map: InstanceMap,
    pub mir_context: HashMap<NameID, MirContext>,
}

impl CompilerState {
    // Attempts to demangle the specified string to the corresponding snippet of source code
    pub fn demangle_string(&self, mangled: &str) -> Option<String> {
        // We'll need to first mangle the ValueNames into actual strings to search.
        // NOTE: A smart non-lazy person would do this once, not every time we ask
        // for demangling
        let string_map = self
            .name_source_map
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

pub fn type_of_hierarchical_value(
    top_module: &NameID,
    hierarchy: &[String],
    instance_map: &InstanceMap,
    mir_contexts: &HashMap<NameID, MirContext>,
    symtab: &SymbolTable,
    item_list: &ItemList,
) -> color_eyre::Result<ConcreteType> {
    // NOTE: Safe unwrap, we already checked that there is at least one item
    // in the hierarchy
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

    let typed_expr = match source {
        VerilogNameSource::ForwardName(n) => TypedExpression::Name(n.clone()),
        VerilogNameSource::ForwardExpr(id) => TypedExpression::Id(*id),
        VerilogNameSource::BackwardName(_) | VerilogNameSource::BackwardExpr(_) => {
            return Err(anyhow!("Translation of backward port types is unsupported"))
        }
    };

    let ty = mir_ctx.type_state.type_of(&typed_expr);

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
