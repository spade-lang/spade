use itertools::Itertools;

use spade_common::location_info::{FullSpan, Loc, WithLocation};
use spade_diagnostics::Diagnostic;

use crate::constraints::ConstraintSource;

use super::equation::{TraitReq, TypeVar};

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

    pub fn display_with_meta(&self, meta: bool) -> String {
        self.inside
            .as_ref()
            .unwrap_or(&self.failing)
            .display_with_meta(meta)
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
            Err(UnificationError::MetaMismatch(TypeMismatch {
                e: mut old_e,
                g: mut old_g,
            })) => {
                old_e.inside.replace(expected);
                old_g.inside.replace(got);
                Err(UnificationError::MetaMismatch(TypeMismatch {
                    e: old_e,
                    g: old_g,
                }))
            }
            e @ Err(UnificationError::UnsatisfiedTraits { .. }) => e,
            e @ Err(
                UnificationError::FromConstraints { .. } | UnificationError::Specific { .. },
            ) => e,
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
        self.map_err(|err| {
            let display_meta = match &err {
                UnificationError::Normal { .. } => false,
                UnificationError::MetaMismatch { .. } => true,
                _ => false,
            };
            match err {
                UnificationError::Normal(TypeMismatch { e, g })
                | UnificationError::MetaMismatch(TypeMismatch { e, g }) => {
                    let e_disp = e.display_with_meta(display_meta);
                    let g_disp = g.display_with_meta(display_meta);
                    let msg = format!("Expected type {e_disp}, got {g_disp}");
                    let diag = Diagnostic::error(unification_point.clone(), msg)
                        .primary_label(format!("Expected {e_disp}"));
                    let diag = message(
                        diag,
                        TypeMismatch {
                            e: e.clone(),
                            g: g.clone(),
                        },
                    );

                    let diag = if !omit_expected_source {
                        add_known_type_context(
                            diag,
                            unification_point.clone(),
                            &e.failing,
                            display_meta,
                        )
                    } else {
                        diag
                    };

                    let diag =
                        add_known_type_context(diag, unification_point, &g.failing, display_meta);
                    diag.type_error(
                        format!("{}", e.failing.display_with_meta(display_meta)),
                        e.inside.map(|o| o.display_with_meta(display_meta)),
                        format!("{}", g.failing.display_with_meta(display_meta)),
                        g.inside.map(|o| o.display_with_meta(display_meta)),
                    )
                }
                UnificationError::UnsatisfiedTraits {
                    var,
                    traits,
                    target_loc: _,
                } => {
                    let trait_bound_loc = ().at_loc(&traits[0]);
                    let impls_str = if traits.len() >= 2 {
                        format!(
                            "{} and {}",
                            traits[0..traits.len() - 1]
                                .iter()
                                .map(|i| i.inner.display_with_meta(display_meta))
                                .join(", "),
                            traits[traits.len() - 1]
                        )
                    } else {
                        format!("{}", traits[0].display_with_meta(display_meta))
                    };
                    let short_msg = format!("{var} does not implement {impls_str}");
                    Diagnostic::error(
                        unification_point,
                        format!("Trait bound not satisfied. {short_msg}"),
                    )
                    .primary_label(short_msg)
                    .secondary_label(
                        trait_bound_loc,
                        "Required because of the trait bound specified here",
                    )
                }
                UnificationError::FromConstraints {
                    expected,
                    got,
                    source,
                    loc,
                    is_meta_error,
                } => {
                    let diag = Diagnostic::error(
                        loc,
                        format!(
                            "Expected type {}, got {}",
                            expected.display_with_meta(is_meta_error),
                            got.display_with_meta(is_meta_error)
                        ),
                    )
                    .primary_label(format!(
                        "Expected {}, got {}",
                        expected.display_with_meta(is_meta_error),
                        got.display_with_meta(is_meta_error)
                    ));

                    let diag = diag.type_error(
                        format!("{}", expected.failing.display_with_meta(is_meta_error)),
                        expected
                            .inside
                            .as_ref()
                            .map(|o| o.display_with_meta(is_meta_error)),
                        format!("{}", got.failing.display_with_meta(is_meta_error)),
                        got.inside
                            .as_ref()
                            .map(|o| o.display_with_meta(is_meta_error)),
                    );

                    match source {
                        ConstraintSource::AdditionOutput => diag.note(
                            "Addition creates one more output bit than the input to avoid overflow"
                                .to_string(),
                        ),
                        ConstraintSource::MultOutput => diag.note(
                            "The size of a multiplication is the sum of the operand sizes"
                                .to_string(),
                        ),
                        ConstraintSource::ArrayIndexing => {
                            // NOTE: This error message could probably be improved
                            diag.note(
                                "because the value is used as an index to an array".to_string(),
                            )
                        }
                        ConstraintSource::MemoryIndexing => {
                            // NOTE: This error message could probably be improved
                            diag.note(
                                "because the value is used as an index to a memory".to_string(),
                            )
                        }
                        ConstraintSource::Concatenation => diag.note(
                            "The size of a concatenation is the sum of the operand sizes"
                                .to_string(),
                        ),
                        ConstraintSource::ArraySize => {
                            diag.note("The number of array elements must  match")
                        }
                        ConstraintSource::RangeIndex => diag,
                        ConstraintSource::RangeIndexOutputSize => diag.note(
                            "The output of a range index is an array inferred from the indices",
                        ),
                        ConstraintSource::TypeLevelIf | ConstraintSource::Where => diag,
                        ConstraintSource::PipelineRegOffset { .. } => diag,
                        ConstraintSource::PipelineRegCount { reg, total } => Diagnostic::error(
                            total,
                            format!("Expected {expected} in this pipeline."),
                        )
                        .primary_label(format!("Expected {expected} stages"))
                        .secondary_label(reg, format!("This final register is number {got}")),
                        ConstraintSource::PipelineAvailDepth => diag,
                    }
                }
                UnificationError::Specific(e) => e,
            }
        })
    }
}

fn add_known_type_context(
    diag: Diagnostic,
    unification_point: impl Into<FullSpan> + Clone,
    failing: &TypeVar,
    meta: bool,
) -> Diagnostic {
    match failing {
        TypeVar::Known(k, _, _) => {
            if FullSpan::from(k) != unification_point.clone().into() {
                diag.secondary_label(
                    k,
                    format!("Type {} inferred here", failing.display_with_meta(meta)),
                )
            } else {
                diag
            }
        }
        TypeVar::Unknown(k, _, _, _) => {
            if FullSpan::from(k) != unification_point.clone().into() {
                diag.secondary_label(
                    k,
                    format!("Type {} inferred here", failing.display_with_meta(meta)),
                )
            } else {
                diag
            }
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct TypeMismatch {
    /// Expected type
    pub e: UnificationTrace,
    /// Got type
    pub g: UnificationTrace,
}
impl TypeMismatch {
    pub fn is_meta_error(&self) -> bool {
        matches!(self.e.failing, TypeVar::Unknown(_, _, _, _))
            || matches!(self.g.failing, TypeVar::Unknown(_, _, _, _))
    }

    pub fn display_e_g(&self) -> (String, String) {
        let is_meta = self.is_meta_error();
        (
            self.e.display_with_meta(is_meta),
            self.g.display_with_meta(is_meta),
        )
    }
}
impl std::fmt::Display for TypeMismatch {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "expected {}, got {}", self.e, self.g)
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum UnificationError {
    Normal(TypeMismatch),
    MetaMismatch(TypeMismatch),
    Specific(spade_diagnostics::Diagnostic),
    UnsatisfiedTraits {
        var: TypeVar,
        traits: Vec<Loc<TraitReq>>,
        target_loc: Loc<()>,
    },
    FromConstraints {
        expected: UnificationTrace,
        got: UnificationTrace,
        source: ConstraintSource,
        loc: Loc<()>,
        is_meta_error: bool,
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
