use std::collections::HashMap;

use crate::{types::Type, Entity, Statement, ValueName};

pub struct TypeList {
    inner: HashMap<ValueName, Type>,
}

impl TypeList {
    pub fn empty() -> Self {
        Self {
            inner: HashMap::new(),
        }
    }

    pub fn from_entity(e: &Entity) -> Self {
        let mut result = Self::empty();

        for (_, name, ty) in &e.inputs {
            result.inner.insert(name.clone(), ty.clone());
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
        &self
            .inner
            .get(index)
            .expect(&format!("No type found for {index}"))
    }
}
