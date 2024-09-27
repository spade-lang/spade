use std::collections::{BTreeMap, HashMap};

use spade_codespan::{ByteIndex, Span};

use crate::location_info::Loc;

/// A map that allows quick (O(log(n))) lookup of things by source code location.
pub struct LocMap<T> {
    inner: HashMap<usize, BTreeMap<ByteIndex, BTreeMap<ByteIndex, Vec<T>>>>,
}

impl<T> LocMap<T> {
    pub fn new() -> Self {
        Self {
            inner: HashMap::new(),
        }
    }

    pub fn insert(&mut self, thing: Loc<T>) {
        self.inner
            .entry(thing.file_id)
            .or_insert(Default::default())
            .entry(thing.span.start())
            .or_insert(Default::default())
            .entry(thing.span.end())
            .or_insert(Default::default())
            .push(thing.inner)
    }

    pub fn around(&self, loc: &Loc<()>) -> Vec<Loc<&T>> {
        self.inner
            .get(&loc.file_id)
            .map(|starts| {
                let after_start = starts.range(loc.span.start()..);
                after_start
                    .map(|(start, ends)| {
                        ends.range(..loc.span.end())
                            .map(|(end, things)| {
                                let with_locs = things.iter().map(|thing| {
                                    Loc::new(thing, Span::new(*start, *end), loc.file_id)
                                });
                                with_locs
                            })
                            .flatten()
                    })
                    .flatten()
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default()
    }
}
