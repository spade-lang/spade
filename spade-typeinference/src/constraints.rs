use num::{bigint::ToBigInt, BigInt, ToPrimitive};
use spade_common::location_info::{Loc, WithLocation};

use crate::equation::TypeVar;

#[derive(Debug, Clone)]
pub enum ConstraintExpr {
    Integer(BigInt),
    Var(TypeVar),
    Sum(Box<ConstraintExpr>, Box<ConstraintExpr>),
    Sub(Box<ConstraintExpr>),
    /// The number of bits required to represent the specified number. In practice
    /// inner.log2().floor()+1
    BitsToRepresent(Box<ConstraintExpr>),
}

impl WithLocation for ConstraintExpr {}

impl ConstraintExpr {
    /// Evaluates the ConstraintExpr returning a new simplified form
    fn evaluate(&self) -> ConstraintExpr {
        match self {
            ConstraintExpr::Integer(_) => self.clone(),
            ConstraintExpr::Var(_) => self.clone(),
            ConstraintExpr::Sum(lhs, rhs) => match (lhs.evaluate(), rhs.evaluate()) {
                (ConstraintExpr::Integer(l), ConstraintExpr::Integer(r)) => {
                    ConstraintExpr::Integer(l + r)
                }
                _ => self.clone(),
            },
            ConstraintExpr::Sub(inner) => match inner.evaluate() {
                ConstraintExpr::Integer(val) => ConstraintExpr::Integer(-val),
                _ => self.clone(),
            },
            ConstraintExpr::BitsToRepresent(inner) => match inner.evaluate() {
                ConstraintExpr::Integer(val) => ConstraintExpr::Integer(
                    // NOTE: This might fail, but it will only do so for massive
                    // constraints. If this turns out to be an issue, we need to
                    // look into doing log2 on BigInt, which as of right now, is
                    // unsupported
                    ((val
                        .to_f64()
                        .expect("Failed to convert constrained integer to f64"))
                    .log2()
                    .floor() as i128
                        + 1)
                    .to_bigint()
                    .unwrap(),
                ),
                _ => self.clone(),
            },
        }
    }

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
        ConstraintExpr::Sum(Box::new(self), Box::new(rhs))
    }
}

impl std::ops::Sub for ConstraintExpr {
    type Output = ConstraintExpr;

    fn sub(self, rhs: Self) -> Self::Output {
        ConstraintExpr::Sum(Box::new(self), Box::new(-rhs))
    }
}

impl std::ops::Neg for ConstraintExpr {
    type Output = ConstraintExpr;

    fn neg(self) -> Self::Output {
        ConstraintExpr::Sub(Box::new(self))
    }
}

impl std::fmt::Display for ConstraintExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConstraintExpr::Integer(val) => write!(f, "{val}"),
            ConstraintExpr::Var(var) => write!(f, "{var}"),
            ConstraintExpr::Sum(rhs, lhs) => write!(f, "({rhs} + {lhs})"),
            ConstraintExpr::Sub(val) => write!(f, "(-{val})"),
            ConstraintExpr::BitsToRepresent(val) => write!(f, "BitsToRepresent({val})"),
        }
    }
}

pub fn bits_to_store(inner: ConstraintExpr) -> ConstraintExpr {
    ConstraintExpr::BitsToRepresent(Box::new(inner))
}

// Shorthand constructors for constraint_expr
pub fn ce_var(v: &TypeVar) -> ConstraintExpr {
    ConstraintExpr::Var(v.clone())
}
pub fn ce_int(v: BigInt) -> ConstraintExpr {
    ConstraintExpr::Integer(v)
}

#[derive(Debug, Clone, PartialEq, thiserror::Error)]
pub enum ConstraintSource {
    AdditionOutput,
    MultOutput,
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

#[derive(Debug, Clone)]
pub struct ConstraintRhs {
    /// The actual constraint
    pub constraint: ConstraintExpr,
    pub context: ConstraintContext,
}

impl WithLocation for ConstraintRhs {}

#[derive(Clone)]
pub struct TypeConstraints {
    pub inner: Vec<(TypeVar, Loc<ConstraintRhs>)>,
}

impl TypeConstraints {
    pub fn new() -> Self {
        Self { inner: vec![] }
    }

    pub fn add_constraint(&mut self, lhs: TypeVar, rhs: Loc<ConstraintRhs>) {
        self.inner.push((lhs, rhs));
    }

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
