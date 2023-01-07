use std::collections::HashMap;

use pyo3::{pyclass, pymethods};
use spade_types::ConcreteType;

use color_eyre::{eyre::Context, Result};
use vcd_translate::translation::{translate_names, translate_string};

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

    pub fn translate_value(&self, name: &str, val: &str) -> Result<Option<String>> {
        translate_string(name, val, &self.types)
    }

    pub fn type_of(&self, name: &str) -> Option<SpadeType> {
        self.types
            .get(name)
            .and_then(|t| t.clone())
            .map(|t| SpadeType(t))
    }
}
