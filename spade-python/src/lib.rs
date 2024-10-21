use pyo3::{pymodule, types::PyModule, Bound, PyResult, Python};
use spade_simulation_ext::{field_ref::FieldRef, BitString, ComparisonResult, SpadeType};

/// A Python module implemented in Rust.
#[pymodule]
fn spade(_py: Python, m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<spade_simulation_ext::Spade>()?;
    m.add_class::<BitString>()?;
    m.add_class::<SpadeType>()?;
    m.add_class::<ComparisonResult>()?;
    m.add_class::<FieldRef>()?;
    Ok(())
}
