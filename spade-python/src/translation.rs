use std::collections::HashMap;

use pyo3::{pyclass, pymethods, types::PyModule, PyObject, Python, ToPyObject};
use spade_types::ConcreteType;

use color_eyre::{eyre::Context, Result};
use vcd_translate::{
    structural::{translate_string, StructuralValue},
    translation::translate_names,
};

use crate::spade_type::SpadeType;

// #[pyclass]
// pub struct BitTranslator {
//     types: HashMap<String, Option<ConcreteType>>,
// }
//
// #[pymethods]
// impl BitTranslator {
//     #[new]
//     fn new(type_file: &str) -> Result<Self> {
//         let type_file = std::fs::read_to_string(&type_file)
//             .with_context(|| format!("Failed to read type file {:?}", type_file))?;
//
//         let types = translate_names(
//             ron::from_str(&type_file)
//                 .with_context(|| format!("failed to decode types in {:?}", type_file))?,
//         );
//
//         Ok(Self { types })
//     }
//
//     pub fn translate_value(&self, name: &str, val: &str) -> Result<Option<PyStructuralValue>> {
//         translate_string(name, val, &self.types).map(|result| result.map(PyStructuralValue))
//     }
//
//     pub fn type_of(&self, name: &str) -> Option<SpadeType> {
//         self.types
//             .get(name)
//             .and_then(|t| t.clone())
//             .map(|t| SpadeType(t))
//     }
// }

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

    fn translate(&self, name: &str, value: &str) -> Result<Option<PyObject>> {
        Python::with_gil(|py| {
            let result_class = self.surfer_module.getattr(py, "TranslationResult")?;

            Ok(Some(result_class.call1(py, ("test",))?))
        })
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

// # def fields_from_type(type: SpadeType) -> SignalInfo:
// #     result = SignalInfo()
// #
// #     for (field_name, field_type) in type.fields():
// #         subfields = fields_from_type(field_type)
// #         result.with_field((field_name, subfields))
// #
// #     return result

// #[pyclass]
// pub struct PyStructuralValue(pub StructuralValue);
//
// impl PyStructuralValue {
//     fn value(&self) -> String {
//         todo!()
//     }
//
//     fn fields(&self) -> Vec<(String, PyStructuralValue)> {
//         match self.0 {
//             StructuralValue::HighImp => vec![],
//             StructuralValue::Undef => vec![],
//             StructuralValue::InvalidTag(_) => vec![],
//             StructuralValue::Bits(_) => vec![],
//             StructuralValue::Tuple(inner) => inner
//                 .iter()
//                 .enumerate()
//                 .map(|(i, sv)| (format!("{i}"), PyStructuralValue(sv)))
//                 .collect(),
//             StructuralValue::Array(inner) => vec![],
//             StructuralValue::Struct(members) => {
//                 inner.iter().map(|(name, val)| {
//                     (format!("{name}", val))
//                 })
//             },
//             StructuralValue::Enum(_, _) => todo!(),
//             StructuralValue::Memory => todo!(),
//             StructuralValue::Unsized => todo!(),
//         }
//     }
// }
