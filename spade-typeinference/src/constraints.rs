use num::{BigInt, Signed, Zero};
use serde::{Deserialize, Serialize};
use spade_common::{
    location_info::{Loc, WithLocation},
    num_ext::InfallibleToBigInt,
};
use spade_diagnostics::Diagnostic;
use spade_types::KnownType;

use crate::{
    TypeState,
    equation::{TypeVar, TypeVarID},
};

#[derive(Debug, Clone)]
pub enum ConstraintExpr {
    Bool(bool),
    Integer(BigInt),
    String(String),
    Var(TypeVarID),
    Sum(Box<ConstraintExpr>, Box<ConstraintExpr>),
    Difference(Box<ConstraintExpr>, Box<ConstraintExpr>),
    Product(Box<ConstraintExpr>, Box<ConstraintExpr>),
    Div(Box<ConstraintExpr>, Box<ConstraintExpr>),
    Mod(Box<ConstraintExpr>, Box<ConstraintExpr>),
    Sub(Box<ConstraintExpr>),
    Eq(Box<ConstraintExpr>, Box<ConstraintExpr>),
    NotEq(Box<ConstraintExpr>, Box<ConstraintExpr>),
    Lt(Box<ConstraintExpr>, Box<ConstraintExpr>),
    Gt(Box<ConstraintExpr>, Box<ConstraintExpr>),
    Le(Box<ConstraintExpr>, Box<ConstraintExpr>),
    Ge(Box<ConstraintExpr>, Box<ConstraintExpr>),
    LogicalNot(Box<ConstraintExpr>),
    LogicalAnd(Box<ConstraintExpr>, Box<ConstraintExpr>),
    LogicalOr(Box<ConstraintExpr>, Box<ConstraintExpr>),
    LogicalXor(Box<ConstraintExpr>, Box<ConstraintExpr>),
    /// The number of bits required to represent the specified number. In practice
    /// inner.log2().floor()+1
    IntBitsToRepresent(Box<ConstraintExpr>),
    UintBitsToRepresent(Box<ConstraintExpr>),
}

impl ConstraintExpr {
    pub fn debug_display(&self, type_state: &TypeState) -> String {
        match self {
            ConstraintExpr::Bool(b) => format!("{b}"),
            ConstraintExpr::Integer(v) => format!("{v}"),
            ConstraintExpr::String(v) => format!("{v:?}"),
            ConstraintExpr::Var(type_var_id) => {
                format!("{}", type_var_id.debug_resolve(type_state))
            }
            ConstraintExpr::Sum(lhs, rhs) => {
                format!(
                    "({} + {})",
                    lhs.debug_display(type_state),
                    rhs.debug_display(type_state)
                )
            }
            ConstraintExpr::Difference(lhs, rhs) => {
                format!(
                    "({} - {})",
                    lhs.debug_display(type_state),
                    rhs.debug_display(type_state)
                )
            }
            ConstraintExpr::Product(lhs, rhs) => {
                format!(
                    "({} * {})",
                    lhs.debug_display(type_state),
                    rhs.debug_display(type_state)
                )
            }
            ConstraintExpr::Div(lhs, rhs) => {
                format!(
                    "({} / {})",
                    lhs.debug_display(type_state),
                    rhs.debug_display(type_state)
                )
            }
            ConstraintExpr::Mod(lhs, rhs) => {
                format!(
                    "({} % {})",
                    lhs.debug_display(type_state),
                    rhs.debug_display(type_state)
                )
            }
            ConstraintExpr::Sub(lhs) => {
                format!("(-{})", lhs.debug_display(type_state))
            }
            ConstraintExpr::Eq(lhs, rhs) => {
                format!(
                    "({} == {})",
                    lhs.debug_display(type_state),
                    rhs.debug_display(type_state)
                )
            }
            ConstraintExpr::NotEq(lhs, rhs) => {
                format!(
                    "({} != {})",
                    lhs.debug_display(type_state),
                    rhs.debug_display(type_state)
                )
            }
            ConstraintExpr::Lt(lhs, rhs) => {
                format!(
                    "({} < {})",
                    lhs.debug_display(type_state),
                    rhs.debug_display(type_state)
                )
            }
            ConstraintExpr::Gt(lhs, rhs) => {
                format!(
                    "({} > {})",
                    lhs.debug_display(type_state),
                    rhs.debug_display(type_state)
                )
            }
            ConstraintExpr::Le(lhs, rhs) => {
                format!(
                    "({} <= {})",
                    lhs.debug_display(type_state),
                    rhs.debug_display(type_state)
                )
            }
            ConstraintExpr::Ge(lhs, rhs) => {
                format!(
                    "({} >= {})",
                    lhs.debug_display(type_state),
                    rhs.debug_display(type_state)
                )
            }
            ConstraintExpr::LogicalNot(inner) => {
                format!("(!{})", inner.debug_display(type_state))
            }
            ConstraintExpr::LogicalAnd(lhs, rhs) => {
                format!(
                    "({} && {})",
                    lhs.debug_display(type_state),
                    rhs.debug_display(type_state)
                )
            }
            ConstraintExpr::LogicalOr(lhs, rhs) => {
                format!(
                    "({} || {})",
                    lhs.debug_display(type_state),
                    rhs.debug_display(type_state)
                )
            }
            ConstraintExpr::LogicalXor(lhs, rhs) => {
                format!(
                    "({} ^^ {})",
                    lhs.debug_display(type_state),
                    rhs.debug_display(type_state)
                )
            }
            ConstraintExpr::IntBitsToRepresent(c) => {
                format!("int::bits_for({})", c.debug_display(type_state))
            }
            ConstraintExpr::UintBitsToRepresent(c) => {
                format!("uint::bits_for({})", c.debug_display(type_state))
            }
        }
    }
}

impl ConstraintExpr {
    /// Evaluates the ConstraintExpr returning a new simplified form or a diagnostic if the expression is invalid.
    pub(crate) fn evaluate(
        &self,
        resolve: &dyn Fn(&TypeVarID) -> Option<KnownType>,
        loc: &Loc<()>,
    ) -> Result<ConstraintExpr, Diagnostic> {
        let int_binop =
            |lhs: &ConstraintExpr,
             rhs: &ConstraintExpr,
             op: &dyn Fn(BigInt, BigInt) -> Result<BigInt, Diagnostic>| {
                match (lhs.evaluate(resolve, loc)?, rhs.evaluate(resolve, loc)?) {
                    (ConstraintExpr::Integer(l), ConstraintExpr::Integer(r)) => {
                        Ok(ConstraintExpr::Integer(op(l, r)?))
                    }
                    _ => Ok(self.clone()),
                }
            };
        let bool_binop =
            |lhs: &ConstraintExpr,
             rhs: &ConstraintExpr,
             op: &dyn Fn(bool, bool) -> Result<bool, Diagnostic>| {
                match (lhs.evaluate(resolve, loc)?, rhs.evaluate(resolve, loc)?) {
                    (ConstraintExpr::Bool(l), ConstraintExpr::Bool(r)) => {
                        Ok(ConstraintExpr::Bool(op(l, r)?))
                    }
                    _ => Ok(self.clone()),
                }
            };
        match self {
            ConstraintExpr::Integer(_) => Ok(self.clone()),
            ConstraintExpr::Bool(_) => Ok(self.clone()),
            ConstraintExpr::String(_) => Ok(self.clone()),
            ConstraintExpr::Var(v) => match resolve(v) {
                Some(KnownType::Integer(i)) => Ok(ConstraintExpr::Integer(i)),
                Some(KnownType::Bool(b)) => Ok(ConstraintExpr::Bool(b)),
                Some(KnownType::String(s)) => Ok(ConstraintExpr::String(s)),
                Some(KnownType::Error) => Ok(self.clone()),
                Some(
                    KnownType::Named(_)
                    | KnownType::Tuple
                    | KnownType::Array
                    | KnownType::Inverted
                    | KnownType::CopyView,
                ) => Err(Diagnostic::bug(
                    loc,
                    "Inferred non-integer or bool for constraint variable",
                )),
                None => Ok(self.clone()),
            },
            ConstraintExpr::Sum(lhs, rhs) => int_binop(lhs, rhs, &|l, r| Ok(l + r)),
            ConstraintExpr::Difference(lhs, rhs) => int_binop(lhs, rhs, &|l, r| Ok(l - r)),
            ConstraintExpr::Product(lhs, rhs) => int_binop(lhs, rhs, &|l, r| Ok(l * r)),
            ConstraintExpr::Div(lhs, rhs) => int_binop(lhs, rhs, &|l, r| {
                if r.is_zero() {
                    Err(Diagnostic::error(
                        loc,
                        "Could not perform division during constraint evaluation",
                    )
                    .primary_label("Division by zero"))
                } else {
                    Ok(l / r)
                }
            }),
            ConstraintExpr::Mod(lhs, rhs) => int_binop(lhs, rhs, &|l, r| {
                if r.is_zero() {
                    Err(Diagnostic::error(
                        loc,
                        "Could not perform modulo during constraint evaluation",
                    )
                    .primary_label("Modulo by zero"))
                } else {
                    Ok(l % r)
                }
            }),
            ConstraintExpr::Sub(inner) => match inner.evaluate(resolve, loc)? {
                ConstraintExpr::Integer(val) => Ok(ConstraintExpr::Integer(-val)),
                _ => Ok(self.clone()),
            },
            ConstraintExpr::Eq(lhs, rhs) => {
                match (lhs.evaluate(resolve, loc)?, rhs.evaluate(resolve, loc)?) {
                    (ConstraintExpr::Bool(l), ConstraintExpr::Bool(r)) => {
                        Ok(ConstraintExpr::Bool(l == r))
                    }
                    (ConstraintExpr::Integer(l), ConstraintExpr::Integer(r)) => {
                        Ok(ConstraintExpr::Bool(l == r))
                    }
                    (ConstraintExpr::String(l), ConstraintExpr::String(r)) => {
                        Ok(ConstraintExpr::Bool(l == r))
                    }
                    _ => Ok(self.clone()),
                }
            }
            ConstraintExpr::NotEq(lhs, rhs) => {
                match (lhs.evaluate(resolve, loc)?, rhs.evaluate(resolve, loc)?) {
                    (ConstraintExpr::Bool(l), ConstraintExpr::Bool(r)) => {
                        Ok(ConstraintExpr::Bool(l != r))
                    }
                    (ConstraintExpr::Integer(l), ConstraintExpr::Integer(r)) => {
                        Ok(ConstraintExpr::Bool(l != r))
                    }
                    (ConstraintExpr::String(l), ConstraintExpr::String(r)) => {
                        Ok(ConstraintExpr::Bool(l != r))
                    }
                    _ => Ok(self.clone()),
                }
            }
            ConstraintExpr::Lt(lhs, rhs) => {
                match (lhs.evaluate(resolve, loc)?, rhs.evaluate(resolve, loc)?) {
                    (ConstraintExpr::Integer(l), ConstraintExpr::Integer(r)) => {
                        Ok(ConstraintExpr::Bool(l < r))
                    }
                    _ => Ok(self.clone()),
                }
            }
            ConstraintExpr::Gt(lhs, rhs) => {
                match (lhs.evaluate(resolve, loc)?, rhs.evaluate(resolve, loc)?) {
                    (ConstraintExpr::Integer(l), ConstraintExpr::Integer(r)) => {
                        Ok(ConstraintExpr::Bool(l > r))
                    }
                    _ => Ok(self.clone()),
                }
            }
            ConstraintExpr::Le(lhs, rhs) => {
                match (lhs.evaluate(resolve, loc)?, rhs.evaluate(resolve, loc)?) {
                    (ConstraintExpr::Integer(l), ConstraintExpr::Integer(r)) => {
                        Ok(ConstraintExpr::Bool(l <= r))
                    }
                    _ => Ok(self.clone()),
                }
            }
            ConstraintExpr::Ge(lhs, rhs) => {
                match (lhs.evaluate(resolve, loc)?, rhs.evaluate(resolve, loc)?) {
                    (ConstraintExpr::Integer(l), ConstraintExpr::Integer(r)) => {
                        Ok(ConstraintExpr::Bool(l >= r))
                    }
                    _ => Ok(self.clone()),
                }
            }
            ConstraintExpr::LogicalNot(inner) => match inner.evaluate(resolve, loc)? {
                ConstraintExpr::Bool(b) => Ok(ConstraintExpr::Bool(!b)),
                _ => Ok(self.clone()),
            },
            ConstraintExpr::LogicalAnd(lhs, rhs) => bool_binop(lhs, rhs, &|l, r| Ok(l && r)),
            ConstraintExpr::LogicalOr(lhs, rhs) => bool_binop(lhs, rhs, &|l, r| Ok(l || r)),
            ConstraintExpr::LogicalXor(lhs, rhs) => bool_binop(lhs, rhs, &|l, r| Ok(l != r)),
            ConstraintExpr::IntBitsToRepresent(inner) => match inner.evaluate(resolve, loc)? {
                ConstraintExpr::Integer(val) => {
                    let bits = if val.is_negative() {
                        (-val - BigInt::from(1)).bits().to_bigint()
                    } else {
                        val.bits().to_bigint()
                    };

                    Ok(ConstraintExpr::Integer(bits + BigInt::from(1)))
                }
                _ => Ok(self.clone()),
            },
            ConstraintExpr::UintBitsToRepresent(inner) => match inner.evaluate(resolve, loc)? {
                ConstraintExpr::Integer(val) => Ok(ConstraintExpr::Integer(val.bits().into())),
                _ => Ok(self.clone()),
            },
        }
    }

    /// Evaluate the ConstraintExpr using the provided TypeState to resolve any type variables.
    fn evaluate_in(
        &self,
        type_state: &TypeState,
        loc: &Loc<()>,
    ) -> Result<ConstraintExpr, Diagnostic> {
        self.evaluate(
            &|v| match v.resolve(type_state) {
                TypeVar::Known(_, kt, _) => Some(kt),
                TypeVar::Unknown(..) => None,
            },
            loc,
        )
    }

    pub fn with_context(
        self,
        replaces: &TypeVarID,
        inside: &TypeVarID,
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

pub fn bits_to_store(inner: ConstraintExpr) -> ConstraintExpr {
    ConstraintExpr::UintBitsToRepresent(Box::new(inner))
}

// Shorthand constructors for constraint_expr
pub fn ce_var(v: &TypeVarID) -> ConstraintExpr {
    ConstraintExpr::Var(v.clone())
}
pub fn ce_int(v: BigInt) -> ConstraintExpr {
    ConstraintExpr::Integer(v)
}

#[derive(Debug, Clone, PartialEq)]
pub enum ConstraintSource {
    Const,
    AdditionOutput,
    MultOutput,
    ArrayIndexing,
    MemoryIndexing,
    Concatenation,
    PipelineRegOffset { reg: Loc<()>, total: Loc<()> },
    PipelineRegCount { reg: Loc<()>, total: Loc<()> },
    PipelineAvailDepth,
    RangeIndex,
    RangeIndexOutputSize,
    ArraySize,
    GenExpr,
    Where,
}

impl std::fmt::Display for ConstraintSource {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConstraintSource::Const => write!(f, "Const"),
            ConstraintSource::AdditionOutput => write!(f, "AdditionOutput"),
            ConstraintSource::MultOutput => write!(f, "MultiplicationOutput"),
            ConstraintSource::ArrayIndexing => write!(f, "ArrayIndexing"),
            ConstraintSource::MemoryIndexing => write!(f, "MemoryIndexing"),
            ConstraintSource::Concatenation => write!(f, "Concatenation"),
            ConstraintSource::Where => write!(f, "Where"),
            ConstraintSource::RangeIndex => write!(f, "RangeIndex"),
            ConstraintSource::RangeIndexOutputSize => write!(f, "RangeIndexOutputSize"),
            ConstraintSource::ArraySize => write!(f, "ArraySize"),
            ConstraintSource::PipelineRegOffset { .. } => write!(f, "PipelineRegOffset"),
            ConstraintSource::PipelineRegCount { .. } => write!(f, "PipelineRegOffset"),
            ConstraintSource::PipelineAvailDepth => write!(f, "PipelineAvailDepth"),
            ConstraintSource::GenExpr => write!(f, "GenExpr"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct ConstraintRhs {
    /// The actual constraint
    pub constraint: ConstraintExpr,
    pub context: ConstraintContext,
}

impl ConstraintRhs {
    pub fn debug_display(&self, type_state: &TypeState) -> String {
        self.constraint.debug_display(type_state)
    }
}

#[derive(Clone, Serialize, Deserialize)]
pub struct TypeConstraints {
    #[serde(skip)]
    pub inner: Vec<(TypeVarID, Loc<ConstraintRhs>)>,
}

impl TypeConstraints {
    pub fn new() -> Self {
        Self { inner: vec![] }
    }

    pub fn add_int_constraint(&mut self, lhs: TypeVarID, rhs: Loc<ConstraintRhs>) {
        self.inner.push((lhs, rhs));
    }

    /// Calls `evaluate` on all constraints. If any constraints are now `T = Integer(val)`,
    /// those updated values are returned. Such constraints are then removed
    /// Returns the updated constraints, the new known values, and any diagnostic errors that
    /// occurred during evaluation.
    pub fn update_type_level_value_constraints(
        self,
        type_state: &TypeState,
    ) -> (
        TypeConstraints,
        Vec<Loc<(TypeVarID, ConstraintReplacement)>>,
        Vec<Diagnostic>,
    ) {
        let mut new_known = vec![];
        let mut diagnostics = vec![];
        let remaining = self
            .inner
            .into_iter()
            .filter_map(|(expr, rhs)| {
                let mut rhs = rhs.clone();
                let loc = ().at_loc(&rhs);
                rhs.constraint = match rhs.constraint.evaluate_in(type_state, &loc) {
                    Ok(constraint) => constraint,
                    Err(diag) => {
                        diagnostics.push(diag);
                        return None;
                    }
                };

                match &rhs.constraint {
                    ConstraintExpr::Integer(val) => {
                        // ().at_loc(..).map is a somewhat ugly way to wrap an arbitrary type
                        // in a known Loc. This is done to avoid having to impl WithLocation for
                        // the unusual tuple used here
                        let replacement = ConstraintReplacement {
                            val: KnownType::Integer(val.clone()),
                            context: rhs.context.clone(),
                        };
                        new_known
                            .push(().at_loc(&rhs).map(|_| (expr.clone(), replacement.clone())));

                        None
                    }
                    // NOTE: If we add more branches that look like this, combine it with
                    // Integer
                    ConstraintExpr::Bool(val) => {
                        let replacement = ConstraintReplacement {
                            val: KnownType::Bool(val.clone()),
                            context: rhs.context.clone(),
                        };
                        new_known
                            .push(().at_loc(&rhs).map(|_| (expr.clone(), replacement.clone())));

                        None
                    }
                    // NOTE: If we add more branches that look like this, combine it with
                    // Integer and Bool
                    ConstraintExpr::String(val) => {
                        let replacement = ConstraintReplacement {
                            val: KnownType::String(val.clone()),
                            context: rhs.context.clone(),
                        };
                        new_known
                            .push(().at_loc(&rhs).map(|_| (expr.clone(), replacement.clone())));

                        None
                    }
                    ConstraintExpr::Var(_)
                    | ConstraintExpr::Sum(_, _)
                    | ConstraintExpr::Div(_, _)
                    | ConstraintExpr::Mod(_, _)
                    | ConstraintExpr::Eq(_, _)
                    | ConstraintExpr::NotEq(_, _)
                    | ConstraintExpr::Lt(_, _)
                    | ConstraintExpr::Gt(_, _)
                    | ConstraintExpr::Le(_, _)
                    | ConstraintExpr::Ge(_, _)
                    | ConstraintExpr::LogicalNot(_)
                    | ConstraintExpr::LogicalAnd(_, _)
                    | ConstraintExpr::LogicalOr(_, _)
                    | ConstraintExpr::LogicalXor(_, _)
                    | ConstraintExpr::Difference(_, _)
                    | ConstraintExpr::Product(_, _)
                    | ConstraintExpr::IntBitsToRepresent(_)
                    | ConstraintExpr::UintBitsToRepresent(_)
                    | ConstraintExpr::Sub(_) => Some((expr.clone(), rhs)),
                }
            })
            .collect();

        (TypeConstraints { inner: remaining }, new_known, diagnostics)
    }
}

#[derive(Clone, Debug)]
pub struct ConstraintReplacement {
    /// The actual constraint
    pub val: KnownType,
    pub context: ConstraintContext,
}

#[derive(Clone, Debug)]
pub struct ConstraintContext {
    /// A type var in which this constraint applies. For example, if a constraint
    /// this constraint constrains `t1` inside `int<t1>`, then `from` is `int<t1>`
    pub inside: TypeVarID,
    /// The left hand side which this constrains. Used together with `from` to construct
    /// type errors
    pub replaces: TypeVarID,
    /// Context in which this constraint was added to give hints to the user
    pub source: ConstraintSource,
}
