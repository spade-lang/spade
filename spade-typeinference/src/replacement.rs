use std::{cell::RefCell, collections::BTreeMap};

use serde::{Deserialize, Serialize};

use crate::equation::TypeVarID;

#[derive(Clone, Serialize, Deserialize)]
pub struct Replacements {
    replacements: RefCell<BTreeMap<TypeVarID, TypeVarID>>,
}

impl Replacements {
    fn new() -> Self {
        Replacements {
            replacements: RefCell::new(BTreeMap::new()),
        }
    }
}

#[derive(Clone, Serialize, Deserialize)]
pub struct ReplacementStack {
    inner: Vec<Replacements>,

    lookup_steps: RefCell<BTreeMap<usize, usize>>,
}

impl ReplacementStack {
    pub fn new() -> Self {
        Self {
            inner: vec![Replacements::new()],
            lookup_steps: RefCell::new(BTreeMap::new()),
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
            .borrow_mut()
            .insert(from, to);
    }

    pub fn get(&self, mut key: TypeVarID) -> TypeVarID {
        let top = self
            .inner
            .last()
            .expect("Did not have an entry in the replacement stack");

        // store all nodes in the chain we're walking on
        let mut seen = Vec::new();
        let mut replacements = top.replacements.borrow_mut();
        while let Some(target) = replacements.get(&key) {
            seen.push(key);
            key = *target;
        }
        let target = key;
        // update all of them to the end of the chain
        for key in seen {
            replacements.insert(key, target);
        }
        target
    }

    pub fn all(&self) -> Vec<&RefCell<BTreeMap<TypeVarID, TypeVarID>>> {
        self.inner.iter().map(|var| &var.replacements).collect()
    }
}
