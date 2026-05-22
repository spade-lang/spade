use crate::{Entity, MirInput, Statement, ValueName, types::Type};
use rustc_hash::FxHashMap as HashMap;
use spade_common::location_info::Loc;

#[derive(Debug)]
pub struct MirTypeList {
    inner: HashMap<ValueName, Type>,
}

impl MirTypeList {
    pub fn empty() -> Self {
        Self {
            inner: HashMap::default(),
        }
    }

    pub fn from_entity(e: &Entity) -> Self {
        let mut result = Self::empty();

        for MirInput {
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
                    self.inner.insert(b.name.inner.clone(), b.ty.clone());
                }
                Statement::Register(reg) => {
                    self.inner.insert(reg.name.inner.clone(), reg.ty.clone());
                }
                Statement::Constant(idx, ty, _) => {
                    self.inner.insert(idx.inner.clone(), ty.clone());
                }
                Statement::Assert(_) => {}
                Statement::Set { .. } => {
                    // No new types introduced
                }
                Statement::Error => {}
            }
        }
    }

    /// Allows in place construction of a type list
    #[cfg(test)]
    pub fn with(mut self, v: ValueName, t: Type) -> Self {
        self.inner.insert(v, t);
        self
    }
}

impl std::ops::Index<&ValueName> for MirTypeList {
    type Output = Type;

    fn index(&self, index: &ValueName) -> &Self::Output {
        self.inner
            .get(index)
            .unwrap_or_else(|| panic!("No type found for {index}"))
    }
}
