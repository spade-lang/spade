use spade_diagnostics::Diagnostic;
use spade_hir::param_util::ArgumentError;
use thiserror::Error;

use crate::constraints::ConstraintSource;

use super::equation::{TypeVar, TypedExpression};
use spade_common::{
    location_info::{Loc, WithLocation},
    name::{Identifier, NameID},
};

/// A trace of a unification error. The `failing` field indicates which exact type failed to unify,
/// while the `inside` is the "top level" type which failed to unify if it's not the same as
/// failing.
///
/// For example, if unifying `int<7>` with `int<8>`, this would be `failing: 8, inside: int<8>`
/// while if unifying `int<7>` with `bool`, inside would be `None`
#[derive(Debug, PartialEq, Clone)]
pub struct UnificationTrace {
    pub failing: TypeVar,
    pub inside: Option<TypeVar>,
}
impl WithLocation for UnificationTrace {}
impl std::fmt::Display for UnificationTrace {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.outer())
    }
}
impl UnificationTrace {
    pub fn new(failing: TypeVar) -> Self {
        Self {
            failing,
            inside: None,
        }
    }

    pub fn outer(&self) -> &TypeVar {
        self.inside.as_ref().unwrap_or(&self.failing)
    }
}
pub trait UnificationErrorExt<T> {
    fn add_context(self, lhs: TypeVar, rhs: TypeVar) -> std::result::Result<T, UnificationError>;

    fn map_normal_err<F>(self, f: F) -> std::result::Result<T, Error>
    where
        F: Fn((UnificationTrace, UnificationTrace)) -> Error;
}
impl<T> UnificationErrorExt<T> for std::result::Result<T, UnificationError> {
    fn add_context(self, lhs: TypeVar, rhs: TypeVar) -> std::result::Result<T, UnificationError> {
        match self {
            Ok(val) => Ok(val),
            Err(UnificationError::Normal((mut old_lhs, mut old_rhs))) => {
                old_lhs.inside.replace(lhs);
                old_rhs.inside.replace(rhs);
                Err(UnificationError::Normal((old_lhs, old_rhs)))
            }
            Err(UnificationError::FromConstraints { .. }) => {
                panic!("Called add_context on a constraint based unfication error")
            }
            Err(UnificationError::NegativeFromConstraints { .. }) => {
                panic!("Called add_context on a constraint based unfication error")
            }
        }
    }

    fn map_normal_err<F>(self, f: F) -> std::result::Result<T, Error>
    where
        F: Fn((UnificationTrace, UnificationTrace)) -> Error,
    {
        match self {
            Ok(val) => Ok(val),
            Err(UnificationError::Normal(inner)) => Err(f(inner)),
            Err(UnificationError::FromConstraints {
                expected,
                got,
                loc,
                source,
            }) => Err(Error::ConstraintMismatch {
                expected,
                got,
                loc,
                source,
            }),
            Err(UnificationError::NegativeFromConstraints {
                inside,
                offender,
                loc,
            }) => Err(
                Diagnostic::error(loc, "Infered a negative type level integer")
                    .primary_label(format!("Inferred type {inside}"))
                    .note(format!("{offender} in {inside} is negative"))
                    .into(),
            ),
        }
    }
}

#[derive(Debug, Error, PartialEq, Clone)]
pub enum UnificationError {
    #[error("Unification error")]
    Normal((UnificationTrace, UnificationTrace)),
    #[error("Unification error from constraints")]
    FromConstraints {
        expected: UnificationTrace,
        got: UnificationTrace,
        source: ConstraintSource,
        loc: Loc<()>,
    },
    // The specified constraint gave rise to a negative integer
    #[error("Unification error from constraints")]
    NegativeFromConstraints {
        /// The outer type in which we found a negative value
        inside: TypeVar,
        /// The actual type which was negative
        offender: i128,
        loc: Loc<()>,
    },
}

#[derive(Debug, Error, PartialEq, Clone)]
pub enum Error {
    #[error("The specified expression has no type information {}", 0.0)]
    UnknownType(TypedExpression),
    #[error("Type mismatch between {0:?} and {1:?}")]
    TypeMismatch(UnificationTrace, UnificationTrace),

    #[error("Entity output type mismatch")]
    EntityOutputTypeMismatch {
        expected: UnificationTrace,
        got: UnificationTrace,
        // The location of the type specification
        type_spec: Loc<()>,
        // The location of the output expression with the offending type
        output_expr: Loc<()>,
    },
    // An entity output mismatch where the output type was unspecified and defaulted
    // to unit
    #[error("Entity output type mismatch without spec")]
    UnspecedEntityOutputTypeMismatch {
        expected: UnificationTrace,
        got: UnificationTrace,
        // The location of the output expression with the offending type
        output_expr: Loc<()>,
    },
    #[error("Type error: expected {expected}, got: {got}")]
    UnspecifiedTypeError {
        expected: UnificationTrace,
        got: UnificationTrace,
        loc: Loc<()>,
    },
    #[error("Type mismatch due to constraints")]
    ConstraintMismatch {
        expected: UnificationTrace,
        got: UnificationTrace,
        source: ConstraintSource,
        loc: Loc<()>,
    },

    #[error("Int literal not compatible")]
    IntLiteralIncompatible { got: UnificationTrace, loc: Loc<()> },
    #[error("If condition must be boolean")]
    NonBooleanCondition { got: UnificationTrace, loc: Loc<()> },
    #[error("If condition mismatch")]
    IfConditionMismatch {
        expected: UnificationTrace,
        got: UnificationTrace,
        first_branch: Loc<()>,
        incorrect_branch: Loc<()>,
    },
    #[error("Match branch mismatch")]
    MatchBranchMismatch {
        expected: UnificationTrace,
        got: UnificationTrace,
        first_branch: Loc<()>,
        incorrect_branch: Loc<()>,
    },
    #[error("Non clock used as register clock")]
    NonClockClock {
        expected: UnificationTrace,
        got: UnificationTrace,
        loc: Loc<()>,
    },
    #[error("Reset condition must be a bool")]
    NonBoolReset {
        expected: UnificationTrace,
        got: UnificationTrace,
        loc: Loc<()>,
    },
    #[error("Reset value must match register type")]
    RegisterResetMismatch {
        expected: UnificationTrace,
        got: UnificationTrace,
        loc: Loc<()>,
    },

    #[error("Named argument mismatch")]
    NamedArgumentMismatch {
        name: Loc<Identifier>,
        expr: Loc<()>,
        expected: UnificationTrace,
        got: UnificationTrace,
    },
    #[error("Named argument mismatch")]
    ShortNamedArgumentMismatch {
        name: Loc<Identifier>,
        expected: UnificationTrace,
        got: UnificationTrace,
    },
    #[error("Positional argument mismatch")]
    PositionalArgumentMismatch {
        index: usize,
        expr: Loc<()>,
        expected: UnificationTrace,
        got: UnificationTrace,
    },

    #[error("Tuple index of generic argument")]
    TupleIndexOfGeneric { loc: Loc<()> },
    #[error("Tuple index of non-tuple")]
    TupleIndexOfNonTuple { got: TypeVar, loc: Loc<()> },
    #[error("Tuple index out of bounds")]
    TupleIndexOutOfBounds { index: Loc<u128>, actual_size: u128 },

    #[error("Field access on incomplete")]
    FieldAccessOnIncomplete { loc: Loc<()> },
    #[error("Field access on generic")]
    FieldAccessOnGeneric { loc: Loc<()>, name: NameID },
    #[error("Field access on non-struct")]
    FieldAccessOnNonStruct { loc: Loc<()>, got: TypeVar },
    #[error("Field access on integer")]
    FieldAccessOnInteger { loc: Loc<()> },
    #[error("Field access on enum")]
    FieldAccessOnEnum { loc: Loc<()>, actual_type: NameID },
    #[error("Field access on primitive type")]
    FieldAccessOnPrimitive { loc: Loc<()>, actual_type: NameID },
    #[error("No such field")]
    NoSuchField {
        field: Loc<Identifier>,
        _struct: NameID,
    },

    #[error("Array element mismatch")]
    ArrayElementMismatch {
        expected: UnificationTrace,
        got: UnificationTrace,
        loc: Loc<()>,
        first_element: Loc<()>,
    },

    #[error("Index must be an integer")]
    IndexMustBeInteger { got: UnificationTrace, loc: Loc<()> },
    #[error("Indexee must be an array")]
    IndexeeMustBeArray { got: UnificationTrace, loc: Loc<()> },

    #[error("Pattern type mismatch")]
    PatternTypeMismatch {
        pattern: Loc<()>,
        reason: Loc<()>,
        expected: UnificationTrace,
        got: UnificationTrace,
    },

    #[error("The first argument of a pipeline must be a clock")]
    FirstPipelineArgNotClock {
        expected: UnificationTrace,
        spec: Loc<UnificationTrace>,
    },

    #[error("Attempting to instantiate generic type")]
    GenericTypeInstantiation,

    #[error("Argument error")]
    ArgumentError(#[from] ArgumentError),

    #[error("(internal)No entry in generic list")]
    InternalNoEntryInGenericList(Loc<NameID>),

    #[error("Spade diagnostic")]
    SpadeDiagnostic(#[from] spade_diagnostics::Diagnostic),
}
pub type Result<T> = std::result::Result<T, Error>;
