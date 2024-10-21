use std::collections::HashMap;

#[cfg(feature = "python")]
use pyo3::prelude::*;
use spade_typeinference::equation::TypeVar;

use crate::UptoRange;
use color_eyre::eyre::anyhow;
use color_eyre::Result;

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
    #[cfg(feature = "python")]
    #[pyo3(get)]
    pub(crate) fwd_range: Option<UptoRange>,
    #[cfg(not(feature = "python"))]
    pub(crate) fwd_range: Option<UptoRange>,
    #[cfg(feature = "python")]
    #[pyo3(get)]
    pub(crate) back_range: Option<UptoRange>,
    #[cfg(not(feature = "python"))]
    pub(crate) back_range: Option<UptoRange>,

    /// True if the field is a field on the output of the DUT rather than the input
    pub is_output: bool,

    pub ty: TypeVar,
    // TODO: A field cache like this is not going to work very well since we clone the structure.
    // Move this into the Spade struct
    pub field_cache: HashMap<String, FieldRef>,
}

#[cfg_attr(feature = "python", pymethods)]
impl FieldRef {
    pub fn fwd_range(&self) -> Option<UptoRange> {
        if self.is_output {
            self.back_range
        } else {
            self.fwd_range
        }
    }

    pub fn back_range(&self) -> Option<UptoRange> {
        if self.is_output {
            self.fwd_range
        } else {
            self.back_range
        }
    }

    pub fn backward_range(&self) -> Result<UptoRange> {
        match (self.fwd_range, self.back_range) {
            (None, Some(back)) => Ok(back),
            // TODO: This probably needs a better error message
            (Some(_), None) => Err(anyhow!(
                "This field has type {} which only has forward values",
                self.ty
            )),
            (Some(_), Some(_)) => Err(anyhow!(
                "This field has type {} which has both forward and backward values",
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
                "This field has type {} which only has backward values",
                self.ty
            )),
            (Some(_), Some(_)) => Err(anyhow!(
                "This field has type {} which has both forward and backward values",
                self.ty
            )),
            // TODO: Bad error message
            (None, None) => Err(anyhow!("Cannot compare zero-sized fields")),
        }
    }
}
