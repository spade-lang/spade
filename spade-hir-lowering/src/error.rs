use spade_common::{location_info::Loc, name::NameID};
use spade_hir::Expression;
use spade_typeinference::equation::TypeVar;
use spade_types::ConcreteType;
use thiserror::Error;

use crate::usefulness::Witness;

#[derive(Error, Debug)]
pub enum Error {
    #[error("(Internal) Argument error")]
    ArgumentError(#[from] spade_hir::param_util::ArgumentError),
    #[error("using generic type")]
    UsingGenericType { expr: Loc<Expression>, t: TypeVar },
    #[error("cast to larger")]
    CastToLarger { from: Loc<u64>, to: Loc<u64> },
    #[error("concat size mismatch")]
    ConcatSizeMismatch {
        lhs: Loc<u64>,
        rhs: Loc<u64>,
        result: Loc<u64>,
        expected: u64,
    },
    #[error("Use of undefined identifier")]
    UndefinedVariable { name: Loc<NameID> },
    #[error("Use of value before it is ready")]
    UseBeforeReady {
        name: Loc<NameID>,
        // The number of stages left until the value is available
        unavailable_for: usize,
        // The absolute stage at which the variable is requested
        referenced_at_stage: usize,
    },
    #[error("Availability mismatch")]
    AvailabilityMismatch { prev: Loc<usize>, new: Loc<usize> },
    #[error("Generic builtin")]
    InstantiatingGenericBuiltin { loc: Loc<()>, head: Loc<()> },
    #[error("Missing patterns")]
    MissingPatterns {
        match_expr: Loc<()>,
        useful_branches: Vec<Witness>,
    },
    #[error("Refutable pattern")]
    RefutablePattern {
        pattern: Loc<()>,
        witnesses: Vec<Witness>,
        // The statement in which this binding occurs. (let, reg etc.)
        binding_kind: &'static str,
    },
    #[error("Port in register")]
    PortInRegister { loc: Loc<()>, ty: ConcreteType },
    #[error("Unification error")]
    UnificationError(#[source] spade_typeinference::result::Error),
    #[error("(Internal) Expression without type")]
    InternalExpressionWithoutType(Loc<()>),
}
pub type Result<T> = std::result::Result<T, Error>;
