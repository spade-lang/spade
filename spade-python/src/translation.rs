use std::collections::HashMap;

use pyo3::{pyclass, pymethods, types::PyModule, PyObject, Python, ToPyObject};
use spade_types::ConcreteType;

use color_eyre::{eyre::Context, Result};
use vcd_translate::{
    structural::{translate_string, StructuralValue},
    translation::translate_names,
};

use crate::spade_type::SpadeType;

#[pyclass]
pub struct SurferTranslator {
    types: HashMap<String, Option<ConcreteType>>,

    surfer_module: PyObject,
}

#[pymethods]
impl SurferTranslator {
    #[new]
    fn new(type_file: &str) -> Result<Self> {
        let type_file = std::fs::read_to_string(&type_file)
            .with_context(|| format!("Failed to read type file {:?}", type_file))?;

        let types = translate_names(
            ron::from_str(&type_file)
                .with_context(|| format!("failed to decode types in {:?}", type_file))?,
        );

        let surfer_module = Python::with_gil(|py| -> Result<PyObject> {
            // Ok(py.None())
            Ok(PyModule::import(py, "surfer")?.to_object(py))
        })?;

        Ok(Self {
            types,
            surfer_module,
        })
    }

    fn translates(&self) -> bool {
        true
    }

    fn translate(&self, name: &str, value: &str) -> Result<PyObject> {
        let translated = translate_string(name, value, &self.types)?;

        if let Some(t) = translated {
            Python::with_gil(|py| {
                let result_class = self.surfer_module.getattr(py, "TranslationResult")?;

                pythonify_structural_value(py, &t, &result_class)
            })
        } else {
            Python::with_gil(|py| {
                let result_class = self.surfer_module.getattr(py, "TranslationResult")?;

                Ok(result_class.call1(py, (value,))?)
            })
        }
    }

    fn signal_info(&self, name: &str) -> Result<Option<PyObject>> {
        if let Some(t) = self.types.get(name).and_then(|t| t.clone()) {
            Python::with_gil(|py| {
                let result_class = self.surfer_module.getattr(py, "SignalInfo")?;

                Ok(Some(signal_info_from_type(py, &t, &result_class)?))
            })
        } else {
            Ok(None)
        }
    }
}

fn pythonify_structural_value(
    py: Python,
    value: &StructuralValue,
    result_class: &PyObject,
) -> Result<PyObject> {
    let result = match value {
        StructuralValue::HighImp => result_class.call1(py, ("HIGHIMP",))?,
        StructuralValue::Undef => result_class.call1(py, ("UNDEF",))?,
        StructuralValue::InvalidTag(tag) => {
            result_class.call1(py, (format!("Unknown tag ({tag})"),))?
        }
        StructuralValue::Bits(v) => result_class.call1(py, (v,))?,
        StructuralValue::Tuple(inner) => {
            let result = result_class.call1(py, ("tuple",))?;
            for (i, v) in inner.iter().enumerate() {
                result.call_method1(
                    py,
                    "with_field",
                    (
                        format!("{i}"),
                        pythonify_structural_value(py, v, result_class)?,
                    ),
                )?;
            }
            result
        }
        StructuralValue::Array(_) => result_class.call1(py, ("ARRAY",))?,
        StructuralValue::Struct(inner) => {
            let result = result_class.call1(py, ("tuple",))?;
            for (name, v) in inner {
                result.call_method1(
                    py,
                    "with_field",
                    (
                        format!("{}", name),
                        pythonify_structural_value(py, v, result_class)?,
                    ),
                )?;
            }
            result
        }
        StructuralValue::Enum(_, _) => todo!(),
        StructuralValue::Memory => todo!(),
        StructuralValue::Unsized => todo!(),
    };
    Ok(result)
}

fn signal_info_from_type(
    py: Python,
    ty: &ConcreteType,
    result_class: &PyObject,
) -> Result<PyObject> {
    let fields = match &ty {
        ConcreteType::Backward(inner) | ConcreteType::Wire(inner) => {
            return signal_info_from_type(py, inner, result_class)
        }
        ConcreteType::Tuple(sub) => sub
            .iter()
            .enumerate()
            .map(|(i, t)| Ok((format!("{i}"), signal_info_from_type(py, t, result_class)?)))
            .collect::<Result<Vec<_>>>()?,
        ConcreteType::Struct { members, .. } => members
            .iter()
            .map(|(ident, t)| {
                Ok((
                    format!("{ident}"),
                    signal_info_from_type(py, t, result_class)?,
                ))
            })
            .collect::<Result<Vec<_>>>()?,
        ConcreteType::Array { .. } => vec![],
        ConcreteType::Enum { .. } => vec![],
        ConcreteType::Single { .. } => vec![],
        ConcreteType::Integer(_) => vec![],
    };

    let result = result_class.call0(py)?;

    for field in fields {
        result.call_method1(py, "with_field", (field,))?;
    }
    Ok(result)
}
