use std::collections::{BTreeMap, HashMap};

use spade_codespan::{ByteIndex, Span};

use crate::location_info::Loc;

/// A map that allows quick (O(log(n))) lookup of things by source code location.
#[derive(Debug)]
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
                let after_start = starts.range(..=loc.span.start());
                after_start
                    .map(|(start, ends)| {
                        ends.range(loc.span.end()..)
                            .map(|(end, things)| {
                                let with_locs = things.iter().map(|thing| {
                                    Loc::new(thing, Span::new(*start, *end), loc.file_id)
                                });
                                with_locs
                            })
                            .flatten()
                    })
                    .flatten()
                    .rev()
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default()
    }
}

#[test]
fn around_tests() {
    let mut test = LocMap::new();

    test.insert(Loc::new("a", Span::new(100, 105), 1));
    test.insert(Loc::new("b", Span::new(262, 265), 1));
    test.insert(Loc::new("c", Span::new(300, 305), 1));
    test.insert(Loc::new("d", Span::new(400, 405), 1));
    test.insert(Loc::new("e", Span::new(500, 500), 1));

    test.insert(Loc::new("0", Span::new(0, 100), 1));
    test.insert(Loc::new("1", Span::new(30, 70), 1));
    test.insert(Loc::new("2", Span::new(40, 60), 1));
    test.insert(Loc::new("3", Span::new(40, 70), 1));
    test.insert(Loc::new("4", Span::new(45, 50), 1));

    println!("{test:?}");

    assert_eq!(
        test.around(&Loc::new((), Span::new(263, 263), 1))
            .iter()
            .map(|l| *l.inner)
            .collect::<Vec<_>>(),
        vec!["b"]
    );

    assert_eq!(
        test.around(&Loc::new((), Span::new(500, 500), 1))
            .iter()
            .map(|l| *l.inner)
            .collect::<Vec<_>>(),
        vec!["e"]
    );

    assert_eq!(
        test.around(&Loc::new((), Span::new(50, 50), 1))
            .iter()
            .map(|l| *l.inner)
            .collect::<Vec<_>>(),
        vec!["4", "3", "2", "1", "0"],
    )
}
