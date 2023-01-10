use std::collections::HashMap;

use pyo3::{pyclass, pymethods};
use spade_types::ConcreteType;

use color_eyre::{eyre::Context, Result};
use vcd_translate::{
    structural::{translate_string, StructuralValue},
    translation::translate_names,
};

use crate::spade_type::SpadeType;

#[pyclass]
pub struct BitTranslator {
    types: HashMap<String, Option<ConcreteType>>,
}

#[pymethods]
impl BitTranslator {
    #[new]
    fn new(type_file: &str) -> Result<Self> {
        let type_file = std::fs::read_to_string(&type_file)
            .with_context(|| format!("Failed to read type file {:?}", type_file))?;

        let types = translate_names(
            ron::from_str(&type_file)
                .with_context(|| format!("failed to decode types in {:?}", type_file))?,
        );

        Ok(Self { types })
    }

    pub fn translate_value(&self, name: &str, val: &str) -> Result<Option<PyStructuralValue>> {
        translate_string(name, val, &self.types).map(|result| result.map(PyStructuralValue))
    }

    pub fn type_of(&self, name: &str) -> Option<SpadeType> {
        self.types
            .get(name)
            .and_then(|t| t.clone())
            .map(|t| SpadeType(t))
    }
}

#[pyclass]
pub struct PyStructuralValue(pub StructuralValue);

impl PyStructuralValue {
    fn value(&self) -> String {
        todo!()
    }

    fn fields(&self) -> Vec<(String, PyStructuralValue)> {
        match self.0 {
            StructuralValue::HighImp => vec![],
            StructuralValue::Undef => vec![],
            StructuralValue::InvalidTag(_) => vec![],
            StructuralValue::Bits(_) => vec![],
            StructuralValue::Tuple(inner) => inner
                .iter()
                .enumerate()
                .map(|(i, sv)| (format!("{i}"), PyStructuralValue(sv)))
                .collect(),
            StructuralValue::Array(inner) => vec![],
            StructuralValue::Struct(members) => {
                inner.iter().map(|(name, val)| {
                    (format!("{name}", val))
                })
            },
            StructuralValue::Enum(_, _) => todo!(),
            StructuralValue::Memory => todo!(),
            StructuralValue::Unsized => todo!(),
        }
    }
}
