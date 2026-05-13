use std::{
    io::Result,
    path::{Path as FsPath, PathBuf},
};

use crate::name::Path as SpadePath;

#[derive(Debug)]
pub struct ModuleNamespace {
    pub namespace: SpadePath,
    pub base_namespace: SpadePath,
    pub file: String,
    pub working_dir: Option<PathBuf>,
}

impl ModuleNamespace {
    pub fn new(namespace: SpadePath, base_namespace: SpadePath, file: &FsPath) -> Result<Self> {
        Ok(ModuleNamespace {
            namespace,
            base_namespace,
            file: file.to_string_lossy().to_string(),
            // Safe unwrap, we have a filename, and the parent of a filename is the always present
            working_dir: Some(file.parent().unwrap().to_path_buf()),
        })
    }
}
