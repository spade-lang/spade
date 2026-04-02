use pyo3::{
    Bound, PyResult, Python, pymodule,
    types::PyModule,
    types::{PyModuleMethods, PyType},
};
use spade_simulation_ext::{
    BitString, ComparisonResult, SpadeType,
    error::pyerr::{CompilationError, SourceCodeError},
    field_ref::FieldRef,
};

/// A Python module implemented in Rust.
#[pymodule]
fn spade(py: Python, m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<spade_simulation_ext::Spade>()?;
    m.add_class::<BitString>()?;
    m.add_class::<SpadeType>()?;
    m.add_class::<ComparisonResult>()?;
    m.add_class::<FieldRef>()?;
    m.add("SourceCodeError", PyType::new::<SourceCodeError>(py))?;
    m.add("CompilationError", PyType::new::<CompilationError>(py))?;
    Ok(())
}
