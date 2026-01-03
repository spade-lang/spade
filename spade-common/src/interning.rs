use std::{
    ops::DerefMut,
    sync::{LazyLock, Mutex},
};

use bumpalo::Bump;
use rustc_hash::{FxBuildHasher, FxHashSet};

pub static INTERNER: LazyLock<Interner> = LazyLock::new(|| Interner::new());

pub struct Interner {
    inner: Mutex<(FxHashSet<&'static str>, Bump)>,
}

impl Interner {
    pub fn new() -> Self {
        Self {
            inner: Mutex::new((
                FxHashSet::with_capacity_and_hasher(256, FxBuildHasher::default()),
                Bump::new(),
            )),
        }
    }

    pub fn intern(&self, string: &str) -> &'static str {
        let mut guard = self.inner.lock().unwrap();
        let (lookup, arena) = DerefMut::deref_mut(&mut guard);

        if let Some(prev) = lookup.get(string) {
            return prev;
        }

        let ptr = arena.alloc_str(string);
        let ptr = unsafe {
            // SAFETY: the arena lives forever
            ::core::mem::transmute::<&'_ str, &'static str>(ptr)
        };
        lookup.insert(ptr);
        ptr
    }
}
