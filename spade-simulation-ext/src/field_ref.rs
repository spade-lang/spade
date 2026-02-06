#[cfg(feature = "python")]
use pyo3::prelude::*;
use spade_typeinference::equation::KnownTypeVar;
use spade_types::KnownType;

use crate::error::{Result, SourceCodeError};
use crate::{maybe_pyclass, UptoRange};
use color_eyre::eyre::anyhow;

#[cfg_attr(feature = "python", pyclass)]
#[derive(Clone, Debug)]
pub enum FieldSource {
    Input {
        mangled_fwd: String,
        mangled_back: String,
    },
    Output {},
}

#[cfg_attr(feature = "python", pymethods)]
impl FieldSource {
    pub fn fwd_mangled(&self) -> &str {
        match self {
            FieldSource::Input {
                mangled_fwd,
                mangled_back: _,
            } => &mangled_fwd,
            FieldSource::Output {} => "input__",
        }
    }

    pub fn back_mangled(&self) -> &str {
        match self {
            FieldSource::Input {
                mangled_fwd: _,
                mangled_back,
            } => &mangled_back,
            FieldSource::Output {} => "output__",
        }
    }
}

maybe_pyclass! {
    /// A reference to a field of an input or output of a module. fwd_range and back_range
    /// is the range of bits which contains this particular field in the full signal that this
    /// field originates from.
    /// fwd and back are in reference to *inputs*, so fwd is the non-inverted ports and back
    /// is the inverted ports.
    #[cfg_attr(feature = "python", pyclass)]
    #[derive(Clone, Debug)]
    pub struct FieldRef {
        #[pyo3(get)]
        pub(crate) fwd_range: Option<UptoRange>,
        #[pyo3(get)]
        pub(crate) back_range: Option<UptoRange>,

        /// True if the field is a field on the output of the DUT rather than the input
        #[pyo3(get)]
        pub source: FieldSource,

        pub ty: KnownTypeVar,
        pub path: Vec<String>,
    }

}

pub enum BackRangeError {
    OnlyForward,
    Mixed,
    Empty,
}

#[cfg_attr(feature = "python", pymethods)]
impl FieldRef {
    pub fn fwd_range(&self) -> Option<UptoRange> {
        match self.source {
            FieldSource::Input { .. } => self.fwd_range,
            FieldSource::Output {} => self.back_range,
        }
    }

    pub fn back_range(&self) -> Option<UptoRange> {
        match self.source {
            FieldSource::Input { .. } => self.back_range,
            FieldSource::Output {} => self.fwd_range,
        }
    }

    pub fn write_dir_range(&self) -> Result<UptoRange> {
        let (fwd_range, back_range) = if matches!(self.source, FieldSource::Output {}) {
            (self.back_range, self.fwd_range)
        } else {
            (self.fwd_range, self.back_range)
        };
        match (fwd_range, back_range) {
            (Some(fwd), None) => Ok(fwd),
            (None, Some(_)) => match &self.source {
                FieldSource::Input { .. } => Err(SourceCodeError::new(format!(
                    "Cannot set the value of {} because it is an input with type {}",
                    self.path.join("."),
                    self.ty
                ))
                .primary_label(format!("{} cannot be set", self.path.join(".")))
                .note(format!("The field has type {}", self.ty))
                .note("Since this is an input, only signals with non-inv type can be set")
                .into()),
                FieldSource::Output {} => Err(SourceCodeError::new(format!(
                    "Cannot set the value of {} because it is an output with type {}",
                    self.path.join("."),
                    self.ty
                ))
                .primary_label(format!("{} cannot be set", self.path.join(".")))
                .note(format!("The field has type {}", self.ty))
                .note("Since this is an output, only signals with inv values can be set")
                .into()),
            },
            (Some(_), Some(_)) => Err(SourceCodeError::new(format!(
                "{} with type {} has both forward and backward values",
                self.path.join("."),
                self.ty
            ))
            .primary_label(format!("{} has both forward and backward values", self.ty))
            .note("Try reading or setting individual fields")
            .into()),
            (None, None) => Err(SourceCodeError::new(format!(
                "{} with type {} is a zero sized type",
                self.path.join("."),
                self.ty
            ))
            .primary_label(format!("{} is a zero sized type", self.ty))
            .into()),
        }
    }

    pub fn read_dir_range(&self) -> Result<UptoRange> {
        let (fwd_range, back_range) = if matches!(self.source, FieldSource::Output {}) {
            (self.back_range, self.fwd_range)
        } else {
            (self.fwd_range, self.back_range)
        };
        match (fwd_range, back_range) {
            (None, Some(back)) => Ok(back),
            (Some(_), None) => match &self.source {
                FieldSource::Input { .. } => Err(SourceCodeError::new(format!(
                    "Cannot read the value of {} because it is an input with type {}",
                    self.path.join("."),
                    self.ty
                ))
                .primary_label(format!("Cannot read the value of {}", self.path.join(".")))
                .note(format!("The field has type {}", self.ty))
                .note("Since this is an input, only signals with inv type can be read")
                .into()),
                FieldSource::Output {} => Err(SourceCodeError::new(format!(
                    "Cannot read the value of {} because it is an output with type {}",
                    self.path.join("."),
                    self.ty
                ))
                .primary_label(format!("Cannot read from {}", self.path.join(".")))
                .note(format!("The field has type {}", self.ty))
                .note("Since this is an output, only signals with non-inv type can be read")
                .into()),
            },
            (Some(_), Some(_)) => Err(SourceCodeError::new(format!(
                "{} with type {} has both forward and backward values",
                self.path.join("."),
                self.ty
            ))
            .primary_label(format!("{} has both forward and backward values", self.ty))
            .note("Try reading or setting individual fields")
            .into()),
            (None, None) => Err(SourceCodeError::new(format!(
                "{} with type {} is a zero sized type",
                self.path.join("."),
                self.ty
            ))
            .primary_label(format!("{} is a zero sized type", self.ty))
            .into()),
        }
    }
}

impl FieldRef {
    pub fn write_range_and_type(&self) -> Result<(UptoRange, KnownTypeVar)> {
        let range = self.write_dir_range()?;

        if matches!(self.source, FieldSource::Output {}) {
            let KnownTypeVar(_, KnownType::Inverted, inner) = &self.ty else {
                return Err(anyhow!("Internal error: Backward type had non-inv field").into());
            };
            Ok((range, inner[0].clone()))
        } else {
            Ok((range, self.ty.clone()))
        }
    }

    pub fn read_range_and_type(&self) -> Result<(UptoRange, KnownTypeVar)> {
        let range = self.read_dir_range()?;

        if matches!(self.source, FieldSource::Output {}) {
            Ok((range, self.ty.clone()))
        } else {
            let KnownTypeVar(_, KnownType::Inverted, inner) = &self.ty else {
                return Err(anyhow!("Internal error: Backward type had non-inv field").into());
            };
            Ok((range, inner[0].clone()))
        }
    }
}
