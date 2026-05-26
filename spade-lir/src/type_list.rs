use std::collections::HashMap;

use spade_common::location_info::Loc;
use spade_diagnostics::diag_anyhow;

use crate::{Entity, LirArg, Result, Statement, Type, ValueName};

#[derive(Debug)]
pub struct LirTypeList {
    inner: HashMap<ValueName, Type>,
}

impl LirTypeList {
    pub fn empty() -> Self {
        Self {
            inner: HashMap::default(),
        }
    }

    pub fn from_entity(e: &Entity) -> Self {
        let mut result = Self::empty();

        for LirArg {
            val_name,
            name: _,
            ty,
            no_mangle: _,
        } in &e.inputs
        {
            result.inner.insert(val_name.inner.clone(), ty.clone());
        }
        result.add_statements(&e.statements);

        result
    }

    pub(crate) fn add_statements(&mut self, stmts: &[Loc<Statement>]) {
        for stmt in stmts {
            match &stmt.inner {
                Statement::Binding(b) => {
                    self.inner.insert(b.name.clone(), b.ty.clone());
                }
                Statement::Register(reg) => {
                    self.inner.insert(reg.name.clone(), reg.ty.clone());
                }
                Statement::Constant(idx, ty, _) => {
                    self.inner.insert(idx.clone(), ty.clone());
                }
                Statement::Assert(_) => {}
                Statement::Set { .. } => {
                    // No new types introduced
                }
                Statement::Error => {}
                Statement::Instance {
                    name: _,
                    params: _,
                    inputs: _,
                    outputs,
                    verilog_attr_groups: _,
                } => {
                    for (_, ty, name) in outputs {
                        self.inner.insert(name.inner.clone(), ty.clone());
                    }
                }
            }
        }
    }

    pub fn lookup(&self, name: &Loc<ValueName>) -> Result<Type> {
        self.inner
            .get(name)
            .ok_or_else(|| {
                diag_anyhow!(
                    name,
                    "Tried looking up LIR type of {name} but it was not in the LIR"
                )
            })
            .cloned()
    }

    /// Allows in place construction of a type list
    #[cfg(test)]
    pub fn with(mut self, v: ValueName, t: Type) -> Self {
        self.inner.insert(v, t);
        self
    }
}
