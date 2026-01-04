use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};
use spade_common::cloning_rwlock::CloningRWLock;

use crate::equation::TypeVarID;

#[derive(Clone, Serialize, Deserialize)]
pub struct Replacements {
    replacements: CloningRWLock<BTreeMap<TypeVarID, TypeVarID>>,
}

impl Replacements {
    fn new() -> Self {
        Replacements {
            replacements: CloningRWLock::new(BTreeMap::new()),
        }
    }
}

#[derive(Clone, Serialize, Deserialize)]
pub struct ReplacementStack {
    inner: Vec<Replacements>,
}

impl ReplacementStack {
    pub fn new() -> Self {
        Self {
            inner: vec![Replacements::new()],
        }
    }

    pub fn push(&mut self) {
        self.inner.push(Replacements::new());
    }

    pub fn discard_top(&mut self) {
        self.inner.pop();
    }

    pub fn insert(&mut self, from: TypeVarID, to: TypeVarID) {
        self.inner
            .last_mut()
            .expect("there was no map in the replacement stack")
            .replacements
            .write()
            .unwrap()
            .insert(from, to);
    }

    pub fn get(&self, mut key: TypeVarID) -> TypeVarID {
        let top = self
            .inner
            .last()
            .expect("Did not have an entry in the replacement stack");

        // store all nodes in the chain we're walking on
        let mut seen = Vec::new();
        while let Some(target) =
            self.inner.iter().rev().find_map(|replacements| {
                replacements.replacements.read().unwrap().get(&key).copied()
            })
        {
            seen.push(key);
            key = target;
        }
        let target = key;
        let mut replacements = top.replacements.write().unwrap();
        // update all of them to the end of the chain
        for key in seen {
            replacements.insert(key, target);
        }
        target
    }

    pub fn all(&self) -> Vec<&CloningRWLock<BTreeMap<TypeVarID, TypeVarID>>> {
        self.inner.iter().map(|var| &var.replacements).collect()
    }
}
