use std::collections::HashMap;

use spade_common::location_info::Loc;
use spade_diagnostics::{diag_anyhow, diag_bail};

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

    pub fn from_entity(e: &Entity) -> Result<Self> {
        let mut result = Self::empty();

        for LirArg {
            val_name,
            name: _,
            ty,
            no_mangle: _,
        } in &e.inputs
        {
            result.insert(val_name, val_name.inner.clone(), ty.clone())?;
        }
        for LirArg {
            val_name,
            name: _,
            ty,
            no_mangle: _,
        } in &e.outputs
        {
            result.insert(val_name, val_name.inner.clone(), ty.clone())?;
        }
        result.add_statements(&e.statements)?;

        Ok(result)
    }

    pub(crate) fn add_statements(&mut self, stmts: &[Loc<Statement>]) -> Result<()> {
        for stmt in stmts {
            match &stmt.inner {
                Statement::Binding(b) => {
                    self.insert(stmt, b.name.clone(), b.ty.clone())?;
                }
                Statement::Register(reg) => {
                    self.insert(stmt, reg.name.clone(), reg.ty.clone())?;
                }
                Statement::Constant(idx, ty, _) => {
                    self.insert(stmt, idx.clone(), ty.clone())?;
                }
                Statement::Assert(_) => {}
                Statement::Error => {}
                Statement::Set(_, _) => {}
                Statement::Instance {
                    name: _,
                    params: _,
                    inputs: _,
                    outputs,
                    verilog_attr_groups: _,
                } => {
                    for (_, ty, name) in outputs {
                        self.insert(stmt, name.inner.clone(), ty.clone())?;
                    }
                }
            }
        }
        Ok(())
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

    fn insert<T>(&mut self, loc: &Loc<T>, name: ValueName, ty: Type) -> Result<()> {
        // NOTE(Performance) These clones are unfortunate, but make things easier for now
        if let Some(prev) = self.inner.insert(name.clone(), ty.clone()) {
            if prev != ty {
                diag_bail!(
                    loc,
                    "Found multiple statements that define {name} but they give different types ({prev} vs {ty})"
                );
            }
        }
        Ok(())
    }

    /// Allows in place construction of a type list
    #[cfg(test)]
    pub fn with(mut self, v: ValueName, t: Type) -> Self {
        self.inner.insert(v, t);
        self
    }
}
