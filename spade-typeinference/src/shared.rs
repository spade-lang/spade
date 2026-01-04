use std::sync::{atomic::AtomicU64, RwLock};

use serde::{Deserialize, Serialize};

use crate::{equation::TypeVar, GenericLists, HashMap};

#[derive(Serialize, Deserialize)]
pub struct SharedTypeStateInner {
    // List of the mapping between generic parameters and type vars.
    // The key is the index of the expression for which this generic list is associated. (if this
    // is a generic list for a call whose expression id is x to f<A, B>, then generic_lists[x] will
    // be {A: <type var>, b: <type var>}
    // Managed here because unification must update *all* TypeVars in existence.
    generic_lists: GenericLists,

    /// All types are referred to by their index to allow type vars changing inside
    /// the type state while the types are "out in the wild". The TypeVarID is an index
    /// into this type_vars list which is used to look up the actual type as currently
    /// seen by the type state
    type_vars: Vec<TypeVar>,
}

#[derive(Serialize, Deserialize)]
pub struct SharedTypeState {
    inner: RwLock<SharedTypeStateInner>,

    // NOTE: This is kind of redundant, we could use TypeVarIDs instead of having dedicated
    // numbers for unknown types.
    pub next_typeid: AtomicU64,

    pub next_annon_generic_list: AtomicU64,
}

impl SharedTypeState {
    pub fn new() -> Self {
        Self {
            inner: RwLock::new(SharedTypeStateInner {
                generic_lists: HashMap::new(),
                type_vars: vec![],
            }),
            next_typeid: AtomicU64::new(0),
            next_annon_generic_list: AtomicU64::new(0),
        }
    }

    pub fn modify_type_vars<T, F: FnOnce(&mut Vec<TypeVar>) -> T>(&self, f: F) -> T {
        (f)(&mut self.inner.write().unwrap().type_vars)
    }

    pub fn read_type_vars<T, F: FnOnce(&Vec<TypeVar>) -> T>(&self, f: F) -> T {
        (f)(&self.inner.read().unwrap().type_vars)
    }

    pub fn modify_generic_lists<T, F: FnOnce(&mut GenericLists) -> T>(&self, f: F) -> T {
        (f)(&mut self.inner.write().unwrap().generic_lists)
    }

    pub fn read_generic_lists<T, F: FnOnce(&GenericLists) -> T>(&self, f: F) -> T {
        (f)(&self.inner.read().unwrap().generic_lists)
    }
}
