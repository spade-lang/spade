use num::{bigint::ToBigInt, BigInt, ToPrimitive};
use serde::{Deserialize, Serialize};
use spade_common::location_info::{Loc, WithLocation};
use spade_types::KnownType;

use crate::{
    equation::{TypeVar, TypeVarID},
    TypeState,
};

#[derive(Debug, Clone)]
pub enum ConstraintExpr {
    Bool(bool),
    Integer(BigInt),
    Var(TypeVarID),
    Sum(Box<ConstraintExpr>, Box<ConstraintExpr>),
    Difference(Box<ConstraintExpr>, Box<ConstraintExpr>),
    Product(Box<ConstraintExpr>, Box<ConstraintExpr>),
    Div(Box<ConstraintExpr>, Box<ConstraintExpr>),
    Mod(Box<ConstraintExpr>, Box<ConstraintExpr>),
    Sub(Box<ConstraintExpr>),
    Eq(Box<ConstraintExpr>, Box<ConstraintExpr>),
    NotEq(Box<ConstraintExpr>, Box<ConstraintExpr>),
    /// The number of bits required to represent the specified number. In practice
    /// inner.log2().floor()+1
    UintBitsToRepresent(Box<ConstraintExpr>),
}
impl WithLocation for ConstraintExpr {}

impl ConstraintExpr {
    pub fn debug_display(&self, type_state: &TypeState) -> String {
        match self {
            ConstraintExpr::Bool(b) => format!("{b}"),
            ConstraintExpr::Integer(v) => format!("{v}"),
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
            ConstraintExpr::UintBitsToRepresent(c) => {
                format!("uint_bits_to_fit({})", c.debug_display(type_state))
            }
        }
    }
}

impl ConstraintExpr {
    /// Evaluates the ConstraintExpr returning a new simplified form
    fn evaluate(&self, type_state: &TypeState) -> ConstraintExpr {
        let binop =
            |lhs: &ConstraintExpr, rhs: &ConstraintExpr, op: &dyn Fn(BigInt, BigInt) -> BigInt| {
                match (lhs.evaluate(type_state), rhs.evaluate(type_state)) {
                    (ConstraintExpr::Integer(l), ConstraintExpr::Integer(r)) => {
                        ConstraintExpr::Integer(op(l, r))
                    }
                    _ => self.clone(),
                }
            };
        match self {
            ConstraintExpr::Integer(_) => self.clone(),
            ConstraintExpr::Bool(_) => self.clone(),
            ConstraintExpr::Var(v) => match v.resolve(type_state) {
                TypeVar::Known(_, known_type, _) => match known_type {
                    KnownType::Integer(i) => ConstraintExpr::Integer(i.clone()),
                    KnownType::Bool(b) => ConstraintExpr::Bool(b.clone()),
                    KnownType::Named(_)
                    | KnownType::Tuple
                    | KnownType::Array
                    | KnownType::Wire
                    | KnownType::Inverted => {
                        panic!("Inferred non-integer or bool for constraint variable")
                    }
                },
                TypeVar::Unknown(_, _, _, _) => self.clone(),
            },
            ConstraintExpr::Sum(lhs, rhs) => binop(lhs, rhs, &|l, r| l + r),
            ConstraintExpr::Difference(lhs, rhs) => binop(lhs, rhs, &|l, r| l - r),
            ConstraintExpr::Product(lhs, rhs) => binop(lhs, rhs, &|l, r| l * r),
            ConstraintExpr::Div(lhs, rhs) => binop(lhs, rhs, &|l, r| l / r),
            ConstraintExpr::Mod(lhs, rhs) => binop(lhs, rhs, &|l, r| l % r),
            ConstraintExpr::Sub(inner) => match inner.evaluate(type_state) {
                ConstraintExpr::Integer(val) => ConstraintExpr::Integer(-val),
                _ => self.clone(),
            },
            ConstraintExpr::Eq(lhs, rhs) => {
                match (lhs.evaluate(type_state), rhs.evaluate(type_state)) {
                    (ConstraintExpr::Integer(l), ConstraintExpr::Integer(r)) => {
                        ConstraintExpr::Bool(l == r)
                    }
                    _ => self.clone(),
                }
            }
            ConstraintExpr::NotEq(lhs, rhs) => {
                match (lhs.evaluate(type_state), rhs.evaluate(type_state)) {
                    (ConstraintExpr::Integer(l), ConstraintExpr::Integer(r)) => {
                        ConstraintExpr::Bool(l != r)
                    }
                    _ => self.clone(),
                }
            }
            ConstraintExpr::UintBitsToRepresent(inner) => match inner.evaluate(type_state) {
                ConstraintExpr::Integer(val) => ConstraintExpr::Integer(if val == BigInt::ZERO {
                    BigInt::ZERO
                } else {
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
                    .unwrap()
                }),
                _ => self.clone(),
            },
        }
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
    TypeLevelIf,
    Where,
}

impl std::fmt::Display for ConstraintSource {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
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
            ConstraintSource::TypeLevelIf => write!(f, "TypeLevelIf"),
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

impl WithLocation for ConstraintRhs {}

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
    pub fn update_type_level_value_constraints(
        self,
        type_state: &TypeState,
    ) -> (
        TypeConstraints,
        Vec<Loc<(TypeVarID, ConstraintReplacement)>>,
    ) {
        let mut new_known = vec![];
        let remaining = self
            .inner
            .into_iter()
            .filter_map(|(expr, rhs)| {
                let mut rhs = rhs.clone();
                rhs.constraint = rhs.constraint.evaluate(type_state);

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
                    ConstraintExpr::Var(_)
                    | ConstraintExpr::Sum(_, _)
                    | ConstraintExpr::Div(_, _)
                    | ConstraintExpr::Mod(_, _)
                    | ConstraintExpr::Eq(_, _)
                    | ConstraintExpr::NotEq(_, _)
                    | ConstraintExpr::Difference(_, _)
                    | ConstraintExpr::Product(_, _)
                    | ConstraintExpr::UintBitsToRepresent(_)
                    | ConstraintExpr::Sub(_) => Some((expr.clone(), rhs)),
                }
            })
            .collect();

        (TypeConstraints { inner: remaining }, new_known)
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
