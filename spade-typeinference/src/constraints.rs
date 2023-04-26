use num::{bigint::ToBigInt, BigInt, ToPrimitive};
use spade_common::location_info::{Loc, WithLocation};

use crate::equation::TypeVar;

#[derive(Debug, Clone)]
pub enum ConstraintExpr {
    // [ed]: Denotes the values, and I assume people don't use ints
    // larger than an i64 - which is probably a bad assumption. But I need log2 and it's not that
    Range { lo: i64, hi: i64 },
    Var(TypeVar),
    Add(Box<ConstraintExpr>, Box<ConstraintExpr>),
    Mul(Box<ConstraintExpr>, Box<ConstraintExpr>),
    Neg(Box<ConstraintExpr>),
}

impl WithLocation for ConstraintExpr {}

impl ConstraintExpr {
    pub fn with_context(
        self,
        replaces: &TypeVar,
        inside: &TypeVar,
        source: ConstraintSource,
    ) -> ConstraintRhs {
        ConstraintRhs {
            constraint: self,
            context: ConstraintContext {
                replaces: replaces.clone(),
                inside: inside.clone(),
                source,
            },
        }
    }
}

impl std::ops::Add for ConstraintExpr {
    type Output = ConstraintExpr;

    fn add(self, rhs: Self) -> Self::Output {
        ConstraintExpr::Add(Box::new(self), Box::new(rhs))
    }
}

impl std::ops::Sub for ConstraintExpr {
    type Output = ConstraintExpr;

    fn sub(self, rhs: Self) -> Self::Output {
        ConstraintExpr::Add(Box::new(self), Box::new(-rhs))
    }
}

impl std::ops::Neg for ConstraintExpr {
    type Output = ConstraintExpr;

    fn neg(self) -> Self::Output {
        ConstraintExpr::Neg(Box::new(self))
    }
}

impl std::ops::Mul for ConstraintExpr {
    type Output = ConstraintExpr;

    fn mul(self, rhs: Self) -> Self::Output {
        ConstraintExpr::Mul(Box::new(self), Box::new(rhs))
    }
}

impl std::fmt::Display for ConstraintExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConstraintExpr::Range { lo, hi } => write!(f, "<{lo}, {hi}>"),
            ConstraintExpr::Var(var) => write!(f, "{var}"),
            ConstraintExpr::Add(lhs, rhs) => write!(f, "({lhs} + {rhs})"),
            ConstraintExpr::Neg(val) => write!(f, "(-{val})"),
            ConstraintExpr::Mul(lhs, rhs) => write!(f, "({lhs} * {lhs})"),
        }
    }
}

// Shorthand constructors for constraint_expr
pub fn ce_var(v: TypeVar) -> ConstraintExpr {
    ConstraintExpr::Var(v)
}

pub fn ce_range(lo: i64, hi: i64) -> ConstraintExpr {
    ConstraintExpr::Range { lo, hi }
}

#[derive(Debug, Clone, PartialEq, thiserror::Error)]
pub enum ConstraintSource {
    AdditionOutput, // TOOD: rename to Addition
    MultOutput,     // TOOD: rename to Multiplication
    ArrayIndexing,
    MemoryIndexing,
    Concatenation,
}

impl std::fmt::Display for ConstraintSource {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConstraintSource::AdditionOutput => write!(f, "AdditionOutput"),
            ConstraintSource::MultOutput => write!(f, "MultiplicationOutput"),
            ConstraintSource::ArrayIndexing => write!(f, "ArrayIndexing"),
            ConstraintSource::MemoryIndexing => write!(f, "MemoryIndexing"),
            ConstraintSource::Concatenation => write!(f, "Concatenation"),
        }
    }
}

// TODO: Can't this be removed?
#[derive(Debug, Clone)]
pub struct ConstraintRhs {
    pub constraint: ConstraintExpr,
    pub context: ConstraintContext,
}

impl WithLocation for ConstraintRhs {}

#[derive(Clone)]
pub struct TypeConstraints {
    // All these constraints are of the kind `var <= eq`
    pub inner: Vec<(TypeVar, Loc<ConstraintRhs>)>,
}

impl TypeConstraints {
    pub fn new() -> Self {
        Self { inner: vec![] }
    }

    pub fn add_constraint(&mut self, lhs: TypeVar, rhs: Loc<ConstraintRhs>) {
        self.inner.push((lhs, rhs));
    }

    /*
    /// Calls `evaluate` on all constraints. If any constraints are now `T = Integer(val)`,
    /// those updated values are returned. Such constraints are then removed
    pub fn update_constraints(&mut self) -> Vec<Loc<(TypeVar, ConstraintReplacement)>> {
        let mut new_known = vec![];
        self.inner = self
            .inner
            .iter_mut()
            .filter_map(|(expr, rhs)| {
                let mut rhs = rhs.clone();
                rhs.constraint = rhs.constraint.evaluate();

                match &rhs.constraint {
                    ConstraintExpr::Integer(val) => {
                        // ().at_loc(..).map is a somewhat ugly way to wrap an arbitrary type
                        // in a known Loc. This is done to avoid having to impl WithLocation for
                        // the the unusual tuple used here
                        let replacement = ConstraintReplacement {
                            val: val.clone(),
                            context: rhs.context.clone(),
                        };
                        new_known
                            .push(().at_loc(&rhs).map(|_| (expr.clone(), replacement.clone())));
                        None
                    }
                    ConstraintExpr::Var(_)
                    | ConstraintExpr::Sum(_, _)
                    | ConstraintExpr::BitsToRepresent(_)
                    | ConstraintExpr::Sub(_) => Some((expr.clone(), rhs)),
                }
            })
            .collect();

        new_known
    }
    */
}

#[derive(Clone)]
pub struct ConstraintReplacement {
    /// The actual constraint
    pub val: BigInt,
    pub context: ConstraintContext,
}

#[derive(Clone, Debug)]
pub struct ConstraintContext {
    /// A type var in which this constraint applies. For example, if a constraint
    /// this constraint constrains `t1` inside `int<t1>`, then `from` is `int<t1>`
    pub inside: TypeVar,
    /// The left hand side which this constrains. Used together with `from` to construct
    /// type errors
    pub replaces: TypeVar,
    /// Context in which this constraint was added to give hints to the user
    pub source: ConstraintSource,
}

impl std::fmt::Display for TypeConstraints {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (lhs, rhs) in &self.inner {
            writeln!(f, "{lhs}: {rhs}", rhs = rhs.constraint)?;
        }
        Ok(())
    }
}
