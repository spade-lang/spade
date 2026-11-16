// Heavily inspired by the rust usefulness implementation documented here
// https://doc.rust-lang.org/nightly/nightly-rustc/rustc_mir_build/thir/pattern/usefulness/index.html
// https://github.com/rust-lang/rust/blob/da895e7938e8d6f8d221fce2876d225bf58df865/compiler/rustc_mir_build/src/thir/pattern/usefulness.rs
// See https://github.com/rust-lang/rust/blob/da895e7938e8d6f8d221fce2876d225bf58df865/COPYRIGHT for the rustc copyright

use itertools::Itertools;
use spade_types::ConcreteType;

use crate::pattern::{Constructor, DeconstructedPattern};

#[derive(Clone, Debug)]
pub(crate) struct PatStack {
    pats: Vec<DeconstructedPattern>,
}

/// A stack of subptaterns representing a part of a pattern which
/// is currently being evaluated.
impl PatStack {
    pub(crate) fn new(inner: Vec<DeconstructedPattern>) -> Self {
        Self { pats: inner }
    }

    fn head(&self) -> &DeconstructedPattern {
        &self.pats[0]
    }

    /// Remove the left-most pattern, re-adding the fields of the pattern to the stack.
    /// For example, a stack containing `[Some((_, _)), None]` popped once would
    /// result in `[(_, _), None]`, and `[_, _, None]` after a second pop
    fn pop_head(&self, ctor: &Constructor) -> PatStack {
        let mut new_fields = self.head().specialize(ctor);
        new_fields.extend_from_slice(&self.pats[1..]);
        PatStack::new(new_fields)
    }

    fn is_empty(&self) -> bool {
        self.pats.is_empty()
    }
}

impl std::fmt::Display for PatStack {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "[{}]",
            self.pats.iter().map(|pat| format!("{}", pat)).join(", ")
        )
    }
}

/// A vector of patterns which generally make up a set of patterns for which to check
/// usefulness against.
/// All patterns in the matrix must be of equal length
pub(crate) struct Matrix {
    pub patterns: Vec<PatStack>,
}

impl Matrix {
    pub(crate) fn new(patterns: &[PatStack]) -> Self {
        Self {
            patterns: patterns.into(),
        }
    }

    fn empty() -> Self {
        Matrix { patterns: vec![] }
    }

    fn rows(&self) -> &[PatStack] {
        &self.patterns
    }

    fn push(&mut self, new: PatStack) {
        self.patterns.push(new)
    }

    /// Specializing a matrix with respect to a constructor `ctor` filters out branches
    /// which are not covered by `ctor` and pops the inner patterns into a new matrix.
    ///
    /// For example, the stack
    /// [ [Some(true), _]
    /// , [Some(_), _]
    /// , [None, _]
    /// ]
    /// specialized against `Some(_)` results in
    /// [ [true, _]
    /// , [_, _]
    /// ]
    fn specialize(&self, ctor: Constructor) -> Matrix {
        let mut result = Matrix::empty();

        for row in &self.patterns {
            if ctor.is_covered_by(&row.head().ctor) {
                result.push(row.pop_head(&ctor))
            }
        }

        result
    }
}

impl std::fmt::Debug for Matrix {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "matrix [{}]",
            self.rows().iter().map(|row| format!("{row}")).join("\n")
        )
    }
}

/// A witness of the usefulness of a pattern. During construction, patterns
/// are pushed from left to right, with constructors containing fields "consuming"
/// fields already on the stack for its parameters
///
/// For example, pushing `_, _, _, (,)` results in the following witness stacks
/// [_, _]
/// [_, _, _]
/// [(_, _), _] // (,) (the 2 tuple constructor) takes 2 fields, and therefore consumes the 2 already
/// on the stack
#[derive(Debug, Clone)]
pub struct Witness(pub Vec<DeconstructedPattern>);

impl Witness {
    fn apply_constructor(mut self, ctor: &Constructor, ty: &ConcreteType) -> Self {
        let pat = {
            let len = self.0.len();
            let arity = ctor.arity(ty);
            let fields = self.0.drain((len - arity)..).rev().collect();
            DeconstructedPattern {
                ctor: ctor.clone(),
                fields,
                ty: ty.clone(),
            }
        };

        self.0.push(pat);

        self
    }
}

impl std::fmt::Display for Witness {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.0.is_empty() {
            write!(f, "*no witnesses*")
        } else if self.0.len() != 1 {
            write!(f, "[{}]", self.0.iter().map(|p| format!("{p}")).join(", "))
        } else {
            write!(f, "{}", self.0[0])
        }
    }
}

/// Struct representing if a pattern is useful nor not. `witnesses` are a list of
/// patterns which are not matched. Not guaranteed to list all patterns, but is guaranteed
/// to list at least one witness if the pattern is useful
pub(crate) struct Usefulness {
    pub witnesses: Vec<Witness>,
}

impl Usefulness {
    fn new_useful() -> Self {
        Self {
            witnesses: vec![Witness(vec![])],
        }
    }

    fn new_useless() -> Self {
        Self { witnesses: vec![] }
    }

    pub(crate) fn is_useful(&self) -> bool {
        !self.witnesses.is_empty()
    }

    fn apply_constructor(self, ctor: &Constructor, ty: &ConcreteType) -> Self {
        if self.witnesses.is_empty() {
            self
        } else {
            let witnesses = self
                .witnesses
                .into_iter()
                .flat_map(|w| match ctor {
                    Constructor::Missing { all_missing } => all_missing
                        .iter()
                        .map(|ctor| w.clone().apply_constructor(ctor, ty))
                        .collect(),
                    other => vec![w.apply_constructor(other, ty)],
                })
                .collect();

            Self { witnesses }
        }
    }

    fn extend(&mut self, other: Self) {
        match (self.witnesses.is_empty(), other.witnesses.is_empty()) {
            (_, true) => {}
            (true, _) => *self = other,
            _ => self.witnesses.extend(other.witnesses),
        }
    }
}

impl std::fmt::Display for Usefulness {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "witnesses: [{}]",
            self.witnesses.iter().map(|w| format!("{w}")).join(", ")
        )
    }
}

/// Checks if `pattern` is useful with respect to `prev_patterns`, that is, if the
/// pattern matches some value which is not matched by any pattern in `prev_patterns`
pub(crate) fn is_useful(pattern: &PatStack, prev_patterns: &Matrix) -> Usefulness {
    if pattern.is_empty() {
        if prev_patterns.rows().is_empty() {
            return Usefulness::new_useful();
        } else {
            return Usefulness::new_useless();
        }
    };

    // If an existing row contains only wildcards, it necessarily covers every
    // remaining value. Therefore this candidate cannot cover any cases that
    // the previous case didn't (is useful), so we can avoid recursing and just
    // indicate that this pattern is useless
    if prev_patterns.rows().iter().any(|row| {
        row.pats
            .iter()
            .all(|pat| matches!(pat.ctor, Constructor::Wildcard))
    }) {
        return Usefulness::new_useless();
    }

    let v_ctor = &pattern.head().ctor;

    let ty = &pattern.head().ty;
    let split_ctors = v_ctor.split(
        ty,
        prev_patterns
            .rows()
            .iter()
            .map(|row| row.head().ctor.clone()),
    );

    let mut ret = Usefulness::new_useless();

    for ctor in split_ctors {
        let pattern = pattern.pop_head(&ctor);
        let specialized = prev_patterns.specialize(ctor.clone());

        let usefulness = is_useful(&pattern, &specialized);

        let usefulness = usefulness.apply_constructor(&ctor, ty);

        ret.extend(usefulness);
    }

    ret
}

#[cfg(test)]
mod test {
    use spade_types::PrimitiveType;

    use super::*;

    #[test]
    fn single_pattern_is_useful_wrt_nothing() {
        let pattern = PatStack::new(vec![DeconstructedPattern {
            ctor: Constructor::Single,
            fields: vec![],
            ty: ConcreteType::Single {
                base: PrimitiveType::Bool,
                params: vec![],
            },
        }]);

        let matrix = Matrix { patterns: vec![] };

        assert!(is_useful(&pattern, &matrix).is_useful())
    }

    #[test]
    fn single_pattern_is_not_useful_wrt_single_pattern() {
        let pattern = PatStack::new(vec![DeconstructedPattern {
            ctor: Constructor::Single,
            fields: vec![],
            ty: ConcreteType::Single {
                base: PrimitiveType::Bool,
                params: vec![],
            },
        }]);

        let matrix = Matrix {
            patterns: vec![pattern.clone()],
        };

        assert!(!is_useful(&pattern, &matrix).is_useful())
    }
}
