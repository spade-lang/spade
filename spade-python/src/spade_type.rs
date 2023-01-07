use pyo3::{pyclass, pymethods};
use spade_types::ConcreteType;

#[pyclass]
#[derive(Clone)]
pub struct SpadeType(pub ConcreteType);

#[pymethods]
impl SpadeType {
    pub fn fields(&self) -> Vec<(String, SpadeType)> {
        match &self.0 {
            ConcreteType::Tuple(sub) => sub
                .iter()
                .enumerate()
                .map(|(i, t)| (format!("{i}"), SpadeType(t.clone())))
                .collect(),
            ConcreteType::Struct { members, .. } => members
                .iter()
                .map(|(ident, t)| (format!("{ident}"), SpadeType(t.clone())))
                .collect(),
            ConcreteType::Array { .. } => vec![],
            ConcreteType::Enum { .. } => vec![],
            ConcreteType::Single { .. } => vec![],
            ConcreteType::Integer(_) => vec![],
            ConcreteType::Backward(_) => vec![],
            ConcreteType::Wire(inner) => SpadeType(*inner.clone()).fields(),
        }
    }
}
