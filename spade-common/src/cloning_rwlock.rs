use std::sync::{LockResult, RwLock, RwLockReadGuard, RwLockWriteGuard};

use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize)]
pub struct CloningRWLock<T>(RwLock<T>);

impl<T> CloningRWLock<T> {
    pub fn new(x: T) -> Self {
        Self(RwLock::new(x))
    }

    #[inline]
    pub fn write(&self) -> LockResult<RwLockWriteGuard<'_, T>> {
        self.0.write()
    }

    pub fn read(&self) -> LockResult<RwLockReadGuard<'_, T>> {
        self.0.read()
    }
}

impl<T: Clone> Clone for CloningRWLock<T> {
    fn clone(&self) -> Self {
        Self(RwLock::new(self.0.read().unwrap().clone()))
    }
}
