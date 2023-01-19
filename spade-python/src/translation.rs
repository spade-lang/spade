use std::{collections::HashMap, time::Instant};

use pyo3::{intern, pyclass, pymethods, types::PyModule, Py, PyAny, PyObject, Python, ToPyObject};
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
        let translation_start = Instant::now();
        let translated = translate_string(name, value, &self.types)?;
        let translation_end = Instant::now();

        let prelude_start = Instant::now();
        if let Some(t) = translated {
            Python::with_gil(|py| {
                let result_class = self.surfer_module.getattr(py, "TranslationResult")?;
                let prelude_end = Instant::now();

                let mut result = pythonify_structural_value(py, &t, &result_class)?;

                result.call_method1(
                    py,
                    "push_duration",
                    (
                        "spade_translate",
                        (translation_end - translation_start).as_secs_f64(),
                    ),
                )?;
                result.call_method1(
                    py,
                    "push_duration",
                    ("spade_prelude", (prelude_end - prelude_start).as_secs_f64()),
                )?;
                Ok(result)
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
    let repr_string = |s: &str| -> Result<_> {
        let res = result_class.call0(py)?;
        res.call_method1(py, "repr_string", (s,))?;
        Ok(res)
    };
    // NOTE: If performance turns out to be an issue, we can try to intern method, but this is
    // easier for now
    let repr_simple = |method: &'static str, fields: Vec<(String, Py<PyAny>)>| -> Result<_> {
        let res = result_class.call0(py)?;
        res.call_method0(py, method)?;
        if !fields.is_empty() {
            res.call_method1(py, "with_fields", (fields,))?;
        }
        Ok(res)
    };

    let start = Instant::now();
    let result = match value {
        StructuralValue::HighImp => repr_string("HIGHIMP")?,
        StructuralValue::Undef => repr_string("UNDEF")?,
        StructuralValue::InvalidTag(tag) => repr_string(&format!("Unknown tag ({tag})"))?,
        StructuralValue::Bits(v) => repr_simple("repr_bits", vec![])?,
        StructuralValue::Tuple(inner) => repr_simple(
            "repr_tuple",
            inner
                .iter()
                .enumerate()
                .map(|(i, v)| {
                    Ok((
                        format!("{i}"),
                        pythonify_structural_value(py, v, result_class)?,
                    ))
                })
                .collect::<Result<Vec<_>>>()?,
        )?,
        StructuralValue::Array(_) => result_class.call1(py, ("ARRAY",))?,
        StructuralValue::Struct(inner) => repr_simple(
            "repr_struct",
            inner
                .iter()
                .map(|(n, v)| {
                    Ok((
                        n.to_string(),
                        pythonify_structural_value(py, v, result_class)?,
                    ))
                })
                .collect::<Result<Vec<_>>>()?,
        )?,
        StructuralValue::Enum(_, _) => repr_string("ENUM")?,
        StructuralValue::Memory => repr_string("MEMORY")?,
        StructuralValue::Unsized => repr_string("()")?,
    };
    let end = Instant::now();
    result.call_method1(
        py,
        "push_duration",
        ("spade_pythonify", (end - start).as_secs_f64()),
    )?;
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
