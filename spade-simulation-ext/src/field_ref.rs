use std::collections::HashMap;

#[cfg(feature = "python")]
use pyo3::prelude::*;
use spade_typeinference::equation::TypeVar;
use spade_types::KnownType;

use crate::UptoRange;
use color_eyre::eyre::{anyhow, bail};
use color_eyre::Result;

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
            // TODO: Add a test that checks that this is done correctly since it did not
            // trigger the test suite when this was output__
            FieldSource::Output {} => "input__",
        }
    }

    pub fn back_mangled(&self) -> &str {
        match self {
            FieldSource::Input {
                mangled_fwd: _,
                mangled_back,
            } => &mangled_back,
            // TODO: Add a test that checks that this is done correctly since it did not
            // trigger the test suite when this was output__
            FieldSource::Output {} => "output__",
        }
    }
}

/// #[pyo3(get)] does not work unless the struct is #[pyclass]. Since we can build this crate both
/// with and without python support, we therefore need to #[cfg] away the #[pyo3(get)] fields.
/// THis macro removes that boilerplate
macro_rules! maybe_pyclass {
    ($( #[$sattr:meta] )* $svis:vis struct $sname:ident {
        $( $(#[$mattr:meta])* $mvis:vis $mname:ident : $mty:ty),*$(,)?
    }) => {
        $(#[$sattr])*
        $svis struct $sname {
            $(
                #[cfg(feature = "python")]
                $(#[$mattr])*
                $mvis $mname: $mty,
                #[cfg(not(feature = "python"))]
                $mvis $mname: $mty
            ),*
        }
    }
}

maybe_pyclass! {
    /// A reference to a field of an input or output of a module. fwd_range and back_range
    /// is the range of bits which contains this particular field in the full signal that this
    /// field originates from.
    /// fwd and back are in reference to *inputs*, so fwd is the non-inverted ports and back
    /// is the inverted ports.
    // TODO: Verify that this is still correct when merging
    /// The module output is transformed to an input by immediaetly inverting `ty` on creation.
    /// This unifies the handling of the module output with the inputs.
    #[cfg_attr(feature = "python", pyclass)]
    #[derive(Clone)]
    pub struct FieldRef {
        #[pyo3(get)]
        pub(crate) fwd_range: Option<UptoRange>,
        #[pyo3(get)]
        pub(crate) back_range: Option<UptoRange>,

        /// True if the field is a field on the output of the DUT rather than the input
        #[pyo3(get)]
        pub source: FieldSource,

        pub ty: TypeVar,
        pub path: Vec<String>,
        // TODO(performance): A field cache like this is not going to work very well since we clone the structure.
        // Move this into the Spade struct
        pub field_cache: HashMap<String, FieldRef>,
    }

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

    pub fn backward_range(&self) -> Result<UptoRange> {
        match (self.fwd_range, self.back_range) {
            (None, Some(back)) => Ok(back),
            // TODO: This probably needs a better error message
            (Some(_), None) => Err(anyhow!(
                "{} has type {} which only has forward values",
                self.path.join("."),
                self.ty
            )),
            (Some(_), Some(_)) => Err(anyhow!(
                "{} has type {} which has both forward and backward values",
                self.path.join("."),
                self.ty
            )),
            // TODO: Bad error message
            (None, None) => Err(anyhow!("Cannot compare zero-sized fields")),
        }
    }

    pub fn forward_range(&self) -> Result<UptoRange> {
        match (self.fwd_range, self.back_range) {
            (Some(fwd), None) => Ok(fwd),
            // TODO: This probably needs a better error message
            (None, Some(_)) => Err(anyhow!(
                "{} has type {} which only has backward values",
                self.path.join("."),
                self.ty
            )),
            (Some(_), Some(_)) => Err(anyhow!(
                "{} has type {} which has both forward and backward values",
                self.path.join("."),
                self.ty
            )),
            // TODO: Bad error message
            (None, None) => Err(anyhow!("Cannot compare zero-sized fields")),
        }
    }
}

impl FieldRef {
    pub fn backward_range_and_type(&self) -> Result<(UptoRange, TypeVar)> {
        if matches!(self.source, FieldSource::Output {}) {
            let range = self.forward_range()?;

            Ok((range, self.ty.clone()))
        } else {
            let range = self.backward_range()?;

            // TODO: This is probably wrong
            match &self.ty {
                TypeVar::Known(_, KnownType::Inverted, inner) => Ok((range, inner[0].clone())),
                _ => bail!("Internal error: Backward type had non-inv field"),
            }
        }
    }
}
