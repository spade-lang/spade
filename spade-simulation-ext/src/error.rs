use color_eyre::eyre::ErrReport;
#[cfg(feature = "python")]
use pyo3::pyclass;

use crate::maybe_pyclass;

pub type Result<T> = std::result::Result<T, Error>;

maybe_pyclass! {
    #[cfg_attr(feature = "python", pyclass)]
    #[derive(Debug)]
    pub struct SourceCodeError {
        #[pyo3(get)]
        description: String,
        #[pyo3(get)]
        primary_label: String,
        #[pyo3(get)]
        notes: Vec<String>,
    }
}

impl SourceCodeError {
    pub fn new(description: impl AsRef<str>) -> Self {
        SourceCodeError {
            description: description.as_ref().to_string(),
            primary_label: description.as_ref().to_string(),
            notes: vec![],
        }
    }

    pub fn primary_label(mut self, label: impl AsRef<str>) -> Self {
        self.primary_label = label.as_ref().to_string();
        self
    }

    pub fn note(mut self, note: impl AsRef<str>) -> Self {
        self.notes.push(note.as_ref().to_string());
        self
    }

    pub fn maybe_note(mut self, note: Option<impl AsRef<str>>) -> Self {
        if let Some(note) = note {
            self.notes.push(note.as_ref().to_string());
        }
        self
    }
}

impl std::convert::From<SourceCodeError> for Error {
    fn from(value: SourceCodeError) -> Self {
        Self::SourceCodeError { inner: value }
    }
}

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("The top module ({top}) has no input '{name}'")]
    NoSuchInput { name: String, top: String },
    #[error("Type {ty} has no field {field}")]
    NoSuchField {
        ty: String,
        field: String,
        path: Vec<String>,
    },

    #[error("{}", inner.description)]
    SourceCodeError { inner: SourceCodeError },

    #[error("Compilation error {msg}")]
    CompilationError { msg: String },

    #[error(transparent)]
    Anyhow(#[from] ErrReport),
}

#[cfg(feature = "python")]
pub mod pyerr {
    use pyo3::{
        create_exception,
        exceptions::{PyException, PyRuntimeError},
        PyErr,
    };

    use super::Error;

    create_exception!(spade, CompilationError, PyException);
    create_exception!(spade, SourceCodeError, PyException);

    impl std::convert::From<Error> for PyErr {
        fn from(err: Error) -> PyErr {
            match err {
                Error::NoSuchInput { name, top } => {
                    SourceCodeError::new_err(super::SourceCodeError {
                        description: format!("{top} has no input {name}"),
                        primary_label: format!("`{name}` is not an input"),
                        notes: vec![],
                    })
                }
                Error::NoSuchField { ty, field, path } => {
                    SourceCodeError::new_err(super::SourceCodeError {
                        description: format!("Type {ty} has no field {field}"),
                        primary_label: format!("No field `{field}` in {ty}"),
                        notes: vec![format!(
                            "The full path of the field is `{}`",
                            path.join(".")
                        )],
                    })
                }
                Error::SourceCodeError { inner } => SourceCodeError::new_err(inner),
                Error::CompilationError { msg } => CompilationError::new_err(msg),
                Error::Anyhow(e) => PyRuntimeError::new_err(format!("{e:#?}")),
            }
        }
    }
}
