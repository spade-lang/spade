// Heavily inspired by the rust compiler
// https://github.com/rust-lang/rust/blob/da895e7938e8d6f8d221fce2876d225bf58df865/compiler/rustc_mir_build/src/thir/pattern/deconstruct_pat.rs
// See https://github.com/rust-lang/rust/blob/da895e7938e8d6f8d221fce2876d225bf58df865/COPYRIGHT for the rustc copyright

use itertools::Itertools;
use num::{BigInt, ToPrimitive};
use spade_common::num_ext::InfallibleToBigInt;
use spade_hir::Pattern;
use spade_types::ConcreteType;

use crate::{Context, MirLowerable};

/// Takes a list of integer range constructors which are possibly overlapping and
/// creates consecutive non-overlapping constructors with edges at each point where
/// any original edge has a range.
///
/// The following input:
/// ```text
///   |-------------------------| // "self"
/// |------|  |----------|   |----|
///    |-------| |-------|
/// ```
/// would be iterated over as follows:
/// ```text
///    |---|--||-|---|---|---|--|
/// ```
fn split_int_range(
    min: BigInt,
    max: BigInt,
    other_ctors: impl Iterator<Item = Constructor> + Clone,
) -> Vec<Constructor> {
    let mut edges = other_ctors
        .flat_map(|other| {
            let (min, max) = other.as_range();
            [min, max]
        })
        .collect::<Vec<_>>();
    edges.sort();
    edges.dedup();

    let mut result = vec![];
    let mut current_low = min.clone();

    for edge in edges.into_iter().filter(|e| e > &min && e < &max) {
        result.push(Constructor::IntRange {
            min: current_low,
            max: &edge - 1u32.to_bigint(),
        });
        current_low = edge;
    }
    result.push(Constructor::IntRange {
        min: current_low,
        max,
    });
    result
}

pub(crate) fn split_wildcard(
    ty: &ConcreteType,
    other_ctors: impl Iterator<Item = Constructor> + Clone,
) -> Vec<Constructor> {
    match ty {
        ConcreteType::Error => vec![Constructor::Single],
        ConcreteType::Tuple(_) => vec![Constructor::Single],
        ConcreteType::Struct { .. } => vec![Constructor::Single],
        // We don't currently support array patterns. We'll return Constructor::Single
        // here since we still want to be able to match on arrays with variables
        ConcreteType::Array { .. } => vec![Constructor::Single],
        ConcreteType::Enum { options } => options
            .iter()
            .enumerate()
            .map(|(i, _)| Constructor::Variant(i))
            .collect(),
        ConcreteType::Single { base, params } => match base {
            spade_types::PrimitiveType::Int => {
                let bits = match &params[0] {
                    ConcreteType::Integer(s) => s
                        .to_u128()
                        // NOTE: Throwing error handling in here right now would be annoying,
                        // so an expect should be fine. This is a very uncommon case anyway
                        .expect("Integer bit sizes above 2^128 bits is unsupported"),
                    _ => unreachable!(),
                };

                if bits == 0 {
                    vec![Constructor::IntRange {
                        min: BigInt::ZERO,
                        max: BigInt::ZERO,
                    }]
                } else {
                    let min = -(1.to_bigint() << (bits - 1));
                    let max = (1.to_bigint() << (bits - 1)) - 1;
                    split_int_range(
                        min,
                        max,
                        // Recursively split wildcards into ranges
                        other_ctors.flat_map(|ctor| ctor.split(ty, vec![].into_iter())),
                    )
                }
            }
            spade_types::PrimitiveType::Uint => {
                let bits = match &params[0] {
                    ConcreteType::Integer(s) => s
                        .to_u128()
                        // NOTE: Throwing error handling in here right now would be annoying,
                        // so an expect should be fine. This is a very uncommon case anyway
                        .expect("Integer bit sizes above 2^128 bits is unsupported"),
                    _ => unreachable!(),
                };

                if bits == 0 {
                    vec![Constructor::IntRange {
                        min: BigInt::ZERO,
                        max: BigInt::ZERO,
                    }]
                } else {
                    let min = 0.to_bigint();
                    let max = (1.to_bigint() << (bits)) - 1;
                    split_int_range(
                        min,
                        max,
                        // Recursively split wildcards into ranges
                        other_ctors.flat_map(|ctor| ctor.split(ty, vec![].into_iter())),
                    )
                }
            }
            spade_types::PrimitiveType::Bool => {
                let all_ctors = vec![Constructor::Bool(false), Constructor::Bool(true)];

                group_missing_constructors(all_ctors, other_ctors)
            }
            // Bit literals can't be matched on because you can't compare against z in hardware
            spade_types::PrimitiveType::Bit => vec![],
            // Special types for which there are no constructors which makes matching
            // on them impossible
            spade_types::PrimitiveType::Clock
            | spade_types::PrimitiveType::Memory
            | spade_types::PrimitiveType::InOut => vec![],
        },
        ConcreteType::Backward(_) => vec![Constructor::Single],
        ConcreteType::Wire(_) => vec![Constructor::Single],
        ConcreteType::Integer(_) => unreachable!("Pattern matching on type level integer"),
        ConcreteType::Bool(_) => unreachable!("Pattern matching on type level bool"),
    }
}

/// Like rustc, we need a way to deal with arrays of mostly wildcard patterns. We
/// steal rustc's solution of grouping all patterns not explicitly stated in one column
/// of a pattern into a group of `missing` patterns. That way those can be checked groups.
/// This function groups all the missing patterns when given a list of constructors
pub fn group_missing_constructors(
    all_ctors: Vec<Constructor>,
    other_ctors: impl Iterator<Item = Constructor> + Clone,
) -> Vec<Constructor> {
    let mut non_wildcard_other = other_ctors
        .filter(|other| !matches!(other, Constructor::Wildcard))
        .collect::<Vec<_>>();

    // This list contains every constructor from the list of possible constructors
    // which is not matched by an explicit constructor in the other_ctors list.
    // We lump these together for future operations, as explained in
    // https://github.com/rust-lang/rust/blob/da895e7938e8d6f8d221fce2876d225bf58df865/compiler/rustc_mir_build/src/thir/pattern/deconstruct_pat.rs#L662
    let missing = all_ctors
        .iter()
        .filter(|ctor| {
            !non_wildcard_other
                .iter()
                .any(|other| ctor.is_covered_by(other))
        })
        .cloned()
        .collect::<Vec<_>>();

    if missing.is_empty() {
        all_ctors
    } else {
        non_wildcard_other.push(Constructor::Missing {
            all_missing: missing,
        });
        non_wildcard_other
    }
}

#[derive(Clone, Debug)]
pub enum Constructor {
    /// Patterns that only have a single constructor, like tuples and struct patterns
    Single,
    /// A boolean pattern. The compiler code might look nicer if we define booleans as
    /// enums in the standard library or some core lib, but for now we'll solve it like
    /// this
    Bool(bool),
    /// Enum variant constructor
    Variant(usize),
    IntRange {
        min: BigInt,
        max: BigInt,
    },
    Missing {
        all_missing: Vec<Constructor>,
    },
    Wildcard,
}

impl Constructor {
    /// Some constructors reprersent, like wildcards and int ranges, represent a set of other
    /// constructors. This function splits them into their constituent constructors. To efficiently
    /// split integer ranges, the set of constructors which we are comparing against must be known
    /// because we can't split it into each constructor individually.
    pub fn split(
        &self,
        ty: &ConcreteType,
        other_ctors: impl Iterator<Item = Constructor> + Clone,
    ) -> Vec<Self> {
        match self {
            Self::Wildcard => split_wildcard(ty, other_ctors),
            Self::IntRange { min, max } => split_int_range(min.clone(), max.clone(), other_ctors),
            _ => vec![self.clone()],
        }
    }

    /// Returns true if self is covered by other
    pub fn is_covered_by(&self, other: &Self) -> bool {
        use Constructor::*;
        match (self, other) {
            // Everything is covered by a wildcard
            (_, Wildcard) => true,
            // The missing ctors are not covered by anything in the matrix except wildcards.
            (Missing { .. }, _) => false,
            (Single, Single) => true,
            (Variant(self_id), Variant(other_id)) => self_id == other_id,
            (
                IntRange {
                    min: smin,
                    max: smax,
                },
                IntRange {
                    min: omin,
                    max: omax,
                },
            ) => smin >= omin && smax <= omax,
            (Bool(b1), Bool(b2)) => b1 == b2,
            // Type inference will make sure that we only have comparable
            // constructors to check here.
            _ => panic!("Checking coverage of incompatible constructors. {self:?}, {other:?}"),
        }
    }

    pub fn fields(&self, ty: &ConcreteType) -> Vec<ConcreteType> {
        match &self {
            Constructor::Single => match ty {
                ConcreteType::Error => vec![],
                ConcreteType::Tuple(i) => i.clone(),
                ConcreteType::Struct {
                    name: _,
                    is_port: _,
                    members,
                } => members.iter().map(|m| m.1.clone()).collect(),
                ConcreteType::Array { inner, size } => (0..size
                    .to_u128()
                    .expect("Arrays with more than 2^128 elements are unsupported"))
                    .map(|_| *inner.clone())
                    .collect(),
                ConcreteType::Enum { .. } => {
                    unreachable!("enum should have Variant constructor")
                }
                ConcreteType::Single { .. } => vec![],
                ConcreteType::Integer(_) => unreachable!("Pattern matching on type level integer"),
                ConcreteType::Bool(_) => unreachable!("Pattern matching on type level bool"),
                ConcreteType::Backward(_) => vec![],
                ConcreteType::Wire(_) => vec![],
            },
            Constructor::Variant(idx) => match ty {
                ConcreteType::Enum { options } => {
                    options[*idx].1.iter().map(|o| o.1.clone()).collect()
                }
                _ => unreachable!(),
            },
            Constructor::Bool(_) => vec![],
            Constructor::IntRange { .. } => vec![],
            // Accessing the fields of a wildcard is (probably) impossible
            Constructor::Missing { .. } => vec![],
            Constructor::Wildcard => unreachable!(),
        }
    }

    /// Returns the number of subpatterns which this constructor matches
    pub fn arity(&self, ty: &ConcreteType) -> usize {
        self.fields(ty).len()
    }

    fn as_range(&self) -> (BigInt, BigInt) {
        match self {
            Constructor::IntRange { min, max } => (min.clone(), max.clone()),
            other => panic!("Interprerting {other:?} constructor as range"),
        }
    }
}

#[derive(Clone, Debug)]
pub struct DeconstructedPattern {
    pub ctor: Constructor,
    pub fields: Vec<DeconstructedPattern>,
    pub ty: ConcreteType,
}

impl DeconstructedPattern {
    pub(crate) fn wildcard(ty: &ConcreteType) -> Self {
        Self {
            ctor: Constructor::Wildcard,
            fields: vec![],
            ty: ty.clone(),
        }
    }

    pub(crate) fn wild_from_ctor(ctor: &Constructor, ty: &ConcreteType) -> Self {
        let fields = ctor.fields(ty).iter().map(Self::wildcard).collect();
        Self {
            ctor: ctor.clone(),
            fields,
            ty: ty.clone(),
        }
    }

    pub(crate) fn from_hir(pat: &Pattern, ctx: &Context) -> Self {
        let (ctor, fields) = match &pat.kind {
            spade_hir::PatternKind::Integer(val) => (
                Constructor::IntRange {
                    min: val.clone(),
                    max: (val + 1),
                },
                vec![],
            ),
            spade_hir::PatternKind::Bool(val) => (Constructor::Bool(*val), vec![]),
            spade_hir::PatternKind::Name { .. } => (Constructor::Wildcard, vec![]),
            spade_hir::PatternKind::Tuple(inner) => (
                Constructor::Single,
                inner.iter().map(|i| Self::from_hir(i, ctx)).collect(),
            ),
            spade_hir::PatternKind::Array(inner) => (
                Constructor::Single,
                inner.iter().map(|i| Self::from_hir(i, ctx)).collect(),
            ),
            spade_hir::PatternKind::Type(path, args) => {
                let patternable = ctx.symtab.symtab().patternable_type_by_id(path);

                let fields = args
                    .iter()
                    .map(|arg| Self::from_hir(&arg.value, ctx))
                    .collect();

                match patternable.kind {
                    spade_hir::symbol_table::PatternableKind::Struct => {
                        (Constructor::Single, fields)
                    }
                    spade_hir::symbol_table::PatternableKind::Enum => {
                        let enum_variant = ctx.symtab.symtab().enum_variant_by_id(path);

                        let self_type = ctx
                            .types
                            .concrete_type_of_infallible(
                                pat.id,
                                ctx.symtab.symtab(),
                                &ctx.item_list.types,
                            )
                            .to_mir_type();

                        let variant = enum_variant.option;

                        match self_type {
                            spade_mir::types::Type::Enum(_) => {
                                (Constructor::Variant(variant), fields)
                            }
                            _ => unreachable!("Wrong type for enum variant pattern"),
                        }
                    }
                }
            }
        };

        let ty = ctx.types.concrete_type_of_infallible(
            pat.id,
            ctx.symtab.symtab(),
            &ctx.item_list.types,
        );

        Self { ctor, fields, ty }
    }

    pub fn specialize(&self, other_ctor: &Constructor) -> Vec<Self> {
        match (&self.ctor, other_ctor) {
            (Constructor::Wildcard, _) => Self::wild_from_ctor(other_ctor, &self.ty).fields,
            _ => self.fields.clone(),
        }
    }
}

impl std::fmt::Display for DeconstructedPattern {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.ctor {
            Constructor::Single => match &self.ty {
                ConcreteType::Tuple(_) => write!(
                    f,
                    "({})",
                    self.fields.iter().map(|f| format!("{f}")).join(", ")
                ),
                ConcreteType::Struct {
                    name,
                    is_port: _,
                    members,
                } => {
                    write!(
                        f,
                        "{name}({})",
                        self.fields
                            .iter()
                            .zip(members.iter())
                            .map(|(f, m)| format!("{}: {f}", m.0))
                            .join(", ")
                    )
                }
                ConcreteType::Array { .. } => {
                    write!(
                        f,
                        "[{}]",
                        self.fields.iter().map(|f| format!("{f}")).join(", ")
                    )
                }
                ConcreteType::Enum { .. } => unreachable!(),
                ConcreteType::Single { .. } => write!(f, "_"),
                ConcreteType::Error { .. } => write!(f, "{{error}}"),
                ConcreteType::Integer(_) => unreachable!("Pattern on type level integer"),
                ConcreteType::Bool(_) => unreachable!("Pattern on type level bool"),
                ConcreteType::Backward(_) => unreachable!("Pattern on backward type"),
                ConcreteType::Wire(_) => unreachable!("Pattern on backward type"),
            },
            Constructor::Variant(idx) => match &self.ty {
                ConcreteType::Enum { options } => {
                    let option = &options[*idx];

                    let fields_str = if !self.fields.is_empty() {
                        format!(
                            "({})",
                            self.fields
                                .iter()
                                .zip(option.1.iter())
                                .map(|(f, m)| format!("{}: {f}", m.0))
                                .join(", ")
                        )
                    } else {
                        String::new()
                    };

                    write!(f, "{}{fields_str}", option.0,)
                }
                _ => unreachable!(),
            },
            Constructor::Bool(val) => write!(f, "{val}"),
            Constructor::IntRange { min, max } => write!(f, "{min}..{max}"),
            Constructor::Missing { .. } => {
                unreachable!("Missing should have been removed by Usefulness::apply_constructor")
            }
            Constructor::Wildcard => write!(f, "_"),
        }
    }
}
