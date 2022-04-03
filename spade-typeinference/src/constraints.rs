use spade_common::location_info::{Loc, WithLocation};

use crate::equation::TypeVar;

#[derive(Debug, Clone)]
pub enum ConstraintExpr {
    Integer(i128),
    Var(TypeVar),
    Sum(Box<ConstraintExpr>, Box<ConstraintExpr>),
    Sub(Box<ConstraintExpr>),
}

impl WithLocation for ConstraintExpr {}

impl ConstraintExpr {
    /// Evaluates the ConstraintExpr returning a new simplified form
    fn evaluate(&self) -> ConstraintExpr {
        match self {
            ConstraintExpr::Integer(_) => self.clone(),
            ConstraintExpr::Var(_) => self.clone(),
            ConstraintExpr::Sum(lhs, rhs) => match (lhs.as_ref(), rhs.as_ref()) {
                (ConstraintExpr::Integer(l), ConstraintExpr::Integer(r)) => {
                    ConstraintExpr::Integer(l + r)
                }
                _ => self.clone(),
            },
            ConstraintExpr::Sub(inner) => match **inner {
                ConstraintExpr::Integer(val) => ConstraintExpr::Integer(-val),
                _ => self.clone(),
            },
        }
    }

    pub fn with_context(
        self,
        replaces: &TypeVar,
        from: &TypeVar,
        source: ConstraintSource,
    ) -> ConstraintRhs {
        ConstraintRhs {
            constraint: self,
            from: from.clone(),
            replaces: replaces.clone(),
            source,
        }
    }
}

impl std::ops::Add for ConstraintExpr {
    type Output = ConstraintExpr;

    fn add(self, rhs: Self) -> Self::Output {
        ConstraintExpr::Sum(Box::new(self.clone()), Box::new(rhs.clone()))
    }
}

impl std::ops::Neg for ConstraintExpr {
    type Output = ConstraintExpr;

    fn neg(self) -> Self::Output {
        ConstraintExpr::Sub(Box::new(self.clone()))
    }
}

impl std::fmt::Display for ConstraintExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConstraintExpr::Integer(val) => write!(f, "{val}"),
            ConstraintExpr::Var(var) => write!(f, "{var}"),
            ConstraintExpr::Sum(rhs, lhs) => write!(f, "({rhs} + {lhs})"),
            ConstraintExpr::Sub(val) => write!(f, "(-{val})"),
        }
    }
}

// Shorthand constructors for constraint_expr
pub fn ce_var(v: &TypeVar) -> ConstraintExpr {
    ConstraintExpr::Var(v.clone())
}
pub fn ce_int(v: i128) -> ConstraintExpr {
    ConstraintExpr::Integer(v)
}

#[derive(Debug, Clone, PartialEq, thiserror::Error)]
pub enum ConstraintSource {
    AdditionOutput,
    MultOutput,
}

impl std::fmt::Display for ConstraintSource {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConstraintSource::AdditionOutput => write!(f, "AdditionOutput"),
            ConstraintSource::MultOutput => write!(f, "MultiplicationOutput"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct ConstraintRhs {
    /// The actual constraint
    pub constraint: ConstraintExpr,
    /// A type var in which this constraint applies. For example, if a constraint
    /// this constraint constrains `t1` inside `int<t1>`, then `from` is `int<t1>`
    // TODO: Rename -> inside
    pub from: TypeVar,
    /// The left hand side which this constrains. Used together with `from` to construct
    /// type errors
    pub replaces: TypeVar,
    /// Context in which this constraint was added to give hints to the user
    pub source: ConstraintSource,
}

impl WithLocation for ConstraintRhs {}

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

                match rhs.constraint {
                    ConstraintExpr::Integer(val) => {
                        // ().at_loc(..).map is a somewhat ugly way to wrap an arbitrary type
                        // in a known Loc. This is done to avoid having to impl WithLocation for
                        // the the unusual tuple used here
                        let replacement = ConstraintReplacement {
                            val,
                            from: rhs.from.clone(),
                            source: rhs.source.clone(),
                            replaces: rhs.replaces.clone(),
                        };
                        new_known
                            .push(().at_loc(&rhs).map(|_| (expr.clone(), replacement.clone())));
                        None
                    }
                    ConstraintExpr::Var(_) => Some((expr.clone(), rhs)),
                    ConstraintExpr::Sum(_, _) => Some((expr.clone(), rhs)),
                    ConstraintExpr::Sub(_) => Some((expr.clone(), rhs)),
                }
            })
            .collect();

        new_known
    }
}

#[derive(Clone)]
pub struct ConstraintReplacement {
    /// The actual constraint
    pub val: i128,
    // TODO: Make this context information a separate struct to avoid code duplication
    /// A type var in which this constraint applies. For example, if a constraint
    /// this constraint constrains `t1` inside `int<t1>`, then `from` is `int<t1>`
    pub from: TypeVar,
    /// Context in which this constraint was added to give hints to the user
    pub source: ConstraintSource,
    pub replaces: TypeVar,
}

impl std::fmt::Display for TypeConstraints {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (lhs, rhs) in &self.inner {
            writeln!(f, "{lhs}: {rhs}", rhs = rhs.constraint)?;
        }
        Ok(())
    }
}