use itertools::Itertools;
use thiserror::Error;

use spade_common::{
    location_info::{FullSpan, Loc, WithLocation},
    name::NameID,
};
use spade_diagnostics::Diagnostic;

use crate::constraints::ConstraintSource;

use super::equation::TypeVar;

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
pub trait UnificationErrorExt<T>: Sized {
    fn add_context(
        self,
        got: TypeVar,
        expected: TypeVar,
    ) -> std::result::Result<T, UnificationError>;

    /// Creates a diagnostic with a generic type mismatch error
    fn into_default_diagnostic(
        self,
        unification_point: impl Into<FullSpan> + Clone,
    ) -> std::result::Result<T, Diagnostic> {
        self.into_diagnostic(unification_point, |d, _| d)
    }

    /// Creates a diagnostic with a generic type mismatch error
    fn into_diagnostic_or_default<F>(
        self,
        unification_point: impl Into<FullSpan> + Clone,
        message: Option<F>,
    ) -> std::result::Result<T, Diagnostic>
    where
        F: Fn(Diagnostic, TypeMismatch) -> Diagnostic,
    {
        if let Some(message) = message {
            self.into_diagnostic(unification_point, message)
        } else {
            self.into_diagnostic(unification_point, |d, _| d)
        }
    }

    /// Creates a diagnostic from the unification error that will be emitted at the unification
    /// point, unless the unification error was caused by constraints, at which point
    /// the source of those constraints will be the location of the error.
    /// If trait constraints were not met, a default message will be provided at the unification
    /// point
    fn into_diagnostic<F>(
        self,
        unification_point: impl Into<FullSpan> + Clone,
        message: F,
    ) -> std::result::Result<T, Diagnostic>
    where
        F: Fn(Diagnostic, TypeMismatch) -> Diagnostic,
    {
        self.into_diagnostic_impl(unification_point, false, message)
    }

    fn into_diagnostic_no_expected_source<F>(
        self,
        unification_point: impl Into<FullSpan> + Clone,
        message: F,
    ) -> std::result::Result<T, Diagnostic>
    where
        F: Fn(Diagnostic, TypeMismatch) -> Diagnostic,
    {
        self.into_diagnostic_impl(unification_point, true, message)
    }

    fn into_diagnostic_impl<F>(
        self,
        unification_point: impl Into<FullSpan> + Clone,
        omit_expected_source: bool,
        message: F,
    ) -> std::result::Result<T, Diagnostic>
    where
        F: Fn(Diagnostic, TypeMismatch) -> Diagnostic;
}
impl<T> UnificationErrorExt<T> for std::result::Result<T, UnificationError> {
    fn add_context(
        self,
        got: TypeVar,
        expected: TypeVar,
    ) -> std::result::Result<T, UnificationError> {
        match self {
            Ok(val) => Ok(val),
            Err(UnificationError::Normal(TypeMismatch {
                e: mut old_e,
                g: mut old_g,
            })) => {
                old_e.inside.replace(expected);
                old_g.inside.replace(got);
                Err(UnificationError::Normal(TypeMismatch {
                    e: old_e,
                    g: old_g,
                }))
            }
            e @ Err(UnificationError::UnsatisfiedTraits(_, _)) => e,
            Err(UnificationError::FromConstraints { .. } | UnificationError::Specific { .. }) => {
                panic!("Called add_context on a constraint based unfication error")
            }
        }
    }

    fn into_diagnostic_impl<F>(
        self,
        unification_point: impl Into<FullSpan> + Clone,
        omit_expected_source: bool,
        message: F,
    ) -> std::result::Result<T, Diagnostic>
    where
        F: Fn(Diagnostic, TypeMismatch) -> Diagnostic,
    {
        self.map_err(|e| match e {
            UnificationError::Normal(TypeMismatch { e, g }) => {
                let msg = format!("Expected type {e}, got {g}");
                let diag = Diagnostic::error(unification_point.clone(), msg)
                    .primary_label(format!("Expected {e}"));
                let diag = message(
                    diag,
                    TypeMismatch {
                        e: e.clone(),
                        g: g.clone(),
                    },
                );

                let diag = if !omit_expected_source {
                    add_known_type_context(diag, unification_point.clone(), &e.failing)
                } else {
                    diag
                };

                let diag = add_known_type_context(diag, unification_point, &g.failing);
                diag.type_error(
                    format!("{}", e.failing),
                    e.inside.map(|o| format!("{o}")),
                    format!("{}", g.failing),
                    g.inside.map(|o| format!("{o}")),
                )
            }
            UnificationError::UnsatisfiedTraits(var, impls) => {
                let impls_str = if impls.len() >= 2 {
                    format!(
                        "{} and {}",
                        impls[0..impls.len() - 1]
                            .iter()
                            .map(|i| format!("{i}"))
                            .join(", "),
                        impls[impls.len() - 1]
                    )
                } else {
                    format!("{}", impls[0])
                };
                let short_msg = format!("{var} does not impl {impls_str}");
                Diagnostic::error(
                    unification_point,
                    format!("Unsatisfied trait requirements. {short_msg}"),
                )
                .primary_label(short_msg)
            }
            UnificationError::FromConstraints {
                expected,
                got,
                source,
                loc,
            } => {
                Diagnostic::error(loc, format!("Expected type {}, got {}", expected, got))
                    .primary_label(format!("Expected {}, got {}", expected, got))
                    .note(match source {
                        ConstraintSource::AdditionOutput => {
                            "Addition creates one more output bit than the input to avoid overflow"
                                .to_string()
                        }
                        ConstraintSource::MultOutput => {
                            "The size of a multiplication is the sum of the operand sizes"
                                .to_string()
                        }
                        ConstraintSource::ArrayIndexing => {
                            // NOTE: This error message could probably be improved
                            "because the value is used as an index to an array".to_string()
                        }
                        ConstraintSource::MemoryIndexing => {
                            // NOTE: This error message could probably be improved
                            "because the value is used as an index to a memory".to_string()
                        }
                        ConstraintSource::Concatenation => {
                            "The size of a concatenation is the sum of the operand sizes"
                                .to_string()
                        }
                        ConstraintSource::ForLoopIndex => {
                            "A for-loop index must fit the whole range of iteration".to_string()
                        }
                    })
            }
            UnificationError::Specific(e) => e,
        })
    }
}

fn add_known_type_context(
    diag: Diagnostic,
    unification_point: impl Into<FullSpan> + Clone,
    failing: &TypeVar,
) -> Diagnostic {
    if let TypeVar::Known(k, _, _) = &failing {
        if FullSpan::from(k) != unification_point.clone().into() {
            diag.secondary_label(k, format!("Type {} inferred here", failing))
        } else {
            diag
        }
    } else {
        diag
    }
}

#[derive(Debug, Error, PartialEq, Clone)]
pub struct TypeMismatch {
    /// Expected type
    pub e: UnificationTrace,
    /// Got type
    pub g: UnificationTrace,
}
impl std::fmt::Display for TypeMismatch {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "expected {}, got {}", self.e, self.g)
    }
}

#[derive(Debug, Error, PartialEq, Clone)]
pub enum UnificationError {
    #[error("Unification error")]
    Normal(TypeMismatch),
    #[error("")]
    Specific(#[from] spade_diagnostics::Diagnostic),
    #[error("Unsatisfied traits")]
    UnsatisfiedTraits(TypeVar, Vec<NameID>),
    #[error("Unification error from constraints")]
    FromConstraints {
        expected: UnificationTrace,
        got: UnificationTrace,
        source: ConstraintSource,
        loc: Loc<()>,
    },
}

pub type Result<T> = std::result::Result<T, Diagnostic>;

pub fn error_pattern_type_mismatch(
    reason: Loc<()>,
) -> impl Fn(Diagnostic, TypeMismatch) -> Diagnostic {
    move |diag,
          TypeMismatch {
              e: expected,
              g: got,
          }| {
        diag.message(format!(
            "Pattern type mismatch. Expected {expected} got {got}"
        ))
        .primary_label(format!("expected {expected}, got {got}"))
        .secondary_label(reason, format!("because this has type {expected}"))
    }
}
