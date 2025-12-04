use crate::{types::Type, Entity, MirInput, Statement, ValueName};
use rustc_hash::FxHashMap as HashMap;

pub struct TypeList {
    inner: HashMap<ValueName, Type>,
}

impl TypeList {
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
            result.inner.insert(val_name.clone(), ty.clone());
        }

        result.add_statements(&e.statements);

        result
    }

    fn add_statements(&mut self, stmts: &[Statement]) {
        for stmt in stmts {
            match stmt {
                Statement::Binding(b) => {
                    self.inner.insert(b.name.clone(), b.ty.clone());
                }
                Statement::Register(reg) => {
                    self.inner.insert(reg.name.clone(), reg.ty.clone());
                }
                Statement::Constant(idx, ty, _) => {
                    self.inner.insert(ValueName::Expr(*idx), ty.clone());
                }
                Statement::Assert(_) => {}
                Statement::Set { .. } => {
                    // No new types introduced
                }
                Statement::WalTrace { .. } => {}
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

impl std::ops::Index<&ValueName> for TypeList {
    type Output = Type;

    fn index(&self, index: &ValueName) -> &Self::Output {
        self.inner
            .get(index)
            .unwrap_or_else(|| panic!("No type found for {index}"))
    }
}
