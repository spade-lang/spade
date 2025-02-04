use crate::name::Path;

#[derive(Debug)]
pub struct ModuleNamespace {
    pub namespace: Path,
    pub base_namespace: Path,
    pub file: String,
}
