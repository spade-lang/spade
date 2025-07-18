use rustc_hash::FxHashMap as HashMap;
use serde::{Deserialize, Serialize};
use spade_common::{id_tracker::ExprID, name::NameID};

use crate::{Binding, Entity, MirInput, Register, ValueName};

/// Mapping from verilog name back to the corresponding NameID
#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct VerilogNameMap {
    inner: HashMap<String, VerilogNameSource>,
}

impl Default for VerilogNameMap {
    fn default() -> Self {
        Self::new()
    }
}

impl VerilogNameMap {
    pub fn new() -> Self {
        Self {
            inner: HashMap::default(),
        }
    }

    /// Insert the specified string into the name map. If the string contains
    /// verilog escape characters (\\<name> ), those are removed
    pub fn insert(&mut self, from: &str, to: VerilogNameSource) {
        self.inner.insert(
            from.trim_start_matches('\\')
                .trim_end_matches(' ')
                .to_string(),
            to,
        );
    }

    pub fn lookup_name(&self, name: &str) -> Option<&VerilogNameSource> {
        self.inner.get(name)
    }
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub enum VerilogNameSource {
    ForwardName(NameID),
    BackwardName(NameID),
    ForwardExpr(ExprID),
    BackwardExpr(ExprID),
}

#[derive(Clone)]
pub struct NameState {
    /// Mapping between names and the amount of copies of that name we've seen so far
    names: HashMap<String, u64>,
    /// Mapping between ValueName and predictable name
    name_map: HashMap<ValueName, ValueName>,
}

impl Default for NameState {
    fn default() -> Self {
        Self::new()
    }
}

impl NameState {
    pub fn new() -> NameState {
        Self {
            names: HashMap::default(),
            name_map: HashMap::default(),
        }
    }

    pub fn push(&mut self, name: &ValueName) {
        let new_name = match name {
            ValueName::Named(_, name_str, source) => {
                let id = self
                    .names
                    .entry(name_str.clone())
                    .and_modify(|v| *v += 1)
                    .or_insert(0);

                ValueName::Named(*id, name_str.clone(), source.clone())
            }
            v @ ValueName::Expr(_) => v.clone(),
        };

        self.name_map.insert(name.clone(), new_name);
    }

    pub fn get(&mut self, name: &ValueName) -> ValueName {
        self.name_map
            .get(name)
            .cloned()
            .unwrap_or_else(|| name.clone())
    }
}

pub fn make_names_predictable(e: &mut Entity) -> NameState {
    let mut state = NameState::new();

    {
        // Walk through all statements adding defined names to the state
        let Entity {
            name: _, // we should not translate the outer name
            inputs,
            output: _,
            output_type: _,
            statements,
            verilog_attr_groups: _,
        } = e;

        for input in inputs {
            state.push(&input.val_name);
        }

        for stmt in statements {
            match stmt {
                crate::Statement::Binding(Binding {
                    name,
                    operator: _,
                    operands: _,
                    ty: _,
                    loc: _,
                }) => state.push(name),
                crate::Statement::Register(Register {
                    name,
                    ty: _,
                    clock: _,
                    reset: _,
                    initial: _,
                    value: _,
                    loc: _,
                    traced: _,
                }) => state.push(name),
                crate::Statement::Constant(_, _, _) => {}
                crate::Statement::Assert(_) => {}
                crate::Statement::Set {
                    target: _,
                    value: _,
                } => {}
                crate::Statement::WalTrace { .. } => {}
                crate::Statement::Error => {}
            }
        }
    }

    {
        // Walk through the whole structure again, replacing names by their predictable versions
        let Entity {
            name: _, // we should not translate the outer name
            inputs,
            output,
            output_type: _,
            statements,
            verilog_attr_groups: _,
        } = e;

        for MirInput {
            name: _,
            val_name: val,
            ty: _,
            no_mangle: _,
        } in inputs.iter_mut()
        {
            *val = state.get(val)
        }

        *output = state.get(output);

        for stmt in statements.iter_mut() {
            match stmt {
                crate::Statement::Binding(Binding {
                    name,
                    operator: _,
                    operands,
                    ty: _,
                    loc: _,
                }) => {
                    *name = state.get(name);

                    for op in operands {
                        *op = state.get(op)
                    }
                }
                crate::Statement::Register(Register {
                    name,
                    ty: _,
                    clock,
                    reset,
                    initial: _,
                    value,
                    loc: _,
                    traced,
                }) => {
                    *name = state.get(name);
                    *clock = state.get(clock);
                    reset.as_mut().map(|(trig, val)| {
                        *trig = state.get(trig);
                        *val = state.get(val);
                    });
                    *value = state.get(value);
                    traced.as_mut().map(|traced| *traced = state.get(traced));
                }
                crate::Statement::Constant(_, _, _) => {}
                crate::Statement::Assert(val) => val.inner = state.get(val),
                crate::Statement::Set { target, value } => {
                    target.inner = state.get(target);
                    value.inner = state.get(value);
                }
                crate::Statement::WalTrace {
                    name,
                    val,
                    suffix: _,
                    ty: _,
                } => {
                    *name = state.get(name);
                    *val = state.get(val);
                }
                crate::Statement::Error => {}
            }
        }
    }
    state
}
