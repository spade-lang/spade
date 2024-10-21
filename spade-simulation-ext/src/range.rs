#[cfg(feature = "python")]
use pyo3::prelude::*;

/// Represents a range of bits. These are stored using [x upto y] which is what we use here
/// when indexing strings. However, cocotb indexing uses `x downto y` since we declare all our
/// signals as `N:0`. Use `.as_downto` to perform this translation.
#[cfg_attr(feature = "python", pyclass)]
#[derive(Clone, Copy, Debug)]
pub struct UptoRange {
    pub from: u64,
    pub to: u64,
    /// true if this range is the full range of the field it belongs to or if it is a sub-range.
    /// Used for optimization to not do per-bit assignment unless necessary
    pub is_full: bool,
}

#[cfg_attr(feature = "python", pymethods)]
impl UptoRange {
    pub fn as_downto(&self, size: u64) -> (u64, u64) {
        // NOTE: Since this is used to assign signals, and our bit strings are [x upto y],
        // we the outer index to be (x downto y), but the inner indexing should be (y upto x),
        // hence the unintuitive to,from
        (size - self.to, size - self.from)
    }

    pub fn is_full(&self) -> bool {
        self.is_full
    }
}
