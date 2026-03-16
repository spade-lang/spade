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
            // Safe unwrap, canonicalize ensures all partial path components exist as directories
            working_dir: Some(file.canonicalize()?.parent().unwrap().to_path_buf()),
        })
    }
}
