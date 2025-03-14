use itertools::Itertools;

use spade_common::location_info::{FullSpan, Loc, WithLocation};
use spade_diagnostics::Diagnostic;

use crate::{constraints::ConstraintSource, equation::TypeVarID, traits::TraitReq, TypeState};

use super::equation::TypeVar;

/// A trace of a unification error. The `failing` field indicates which exact type failed to unify,
/// while the `inside` is the "top level" type which failed to unify if it's not the same as
/// failing.
///
/// For example, if unifying `int<7>` with `int<8>`, this would be `failing: 8, inside: int<8>`
/// while if unifying `int<7>` with `bool`, inside would be `None`
#[derive(Debug, PartialEq, Clone)]
pub struct UnificationTrace {
    pub failing: TypeVarID,
    pub inside: Option<TypeVarID>,
}
impl WithLocation for UnificationTrace {}

impl UnificationTrace {
    pub fn new(failing: TypeVarID) -> Self {
        Self {
            failing,
            inside: None,
        }
    }

    pub fn outer(&self) -> TypeVarID {
        *self.inside.as_ref().unwrap_or(&self.failing)
    }

    pub fn display_with_meta(&self, meta: bool, type_state: &TypeState) -> String {
        self.inside
            .as_ref()
            .unwrap_or(&self.failing)
            .display_with_meta(meta, type_state)
    }

    pub fn display(&self, type_state: &TypeState) -> String {
        self.outer().display_with_meta(false, type_state)
    }
}

pub trait UnificationErrorExt<T>: Sized {
    fn add_context(
        self,
        got: TypeVarID,
        expected: TypeVarID,
    ) -> std::result::Result<T, UnificationError>;

    /// Creates a diagnostic with a generic type mismatch error
    fn into_default_diagnostic(
        self,
        unification_point: impl Into<FullSpan> + Clone,
        type_state: &TypeState,
    ) -> std::result::Result<T, Diagnostic> {
        self.into_diagnostic(unification_point, |d, _| d, type_state)
    }

    /// Creates a diagnostic with a generic type mismatch error
    fn into_diagnostic_or_default<F>(
        self,
        unification_point: impl Into<FullSpan> + Clone,
        message: Option<F>,
        type_state: &TypeState,
    ) -> std::result::Result<T, Diagnostic>
    where
        F: Fn(Diagnostic, TypeMismatch) -> Diagnostic,
    {
        if let Some(message) = message {
            self.into_diagnostic(unification_point, message, type_state)
        } else {
            self.into_diagnostic(unification_point, |d, _| d, type_state)
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
        type_state: &TypeState,
    ) -> std::result::Result<T, Diagnostic>
    where
        F: Fn(Diagnostic, TypeMismatch) -> Diagnostic,
    {
        self.into_diagnostic_impl(unification_point, false, message, type_state)
    }

    fn into_diagnostic_no_expected_source<F>(
        self,
        unification_point: impl Into<FullSpan> + Clone,
        message: F,
        type_state: &TypeState,
    ) -> std::result::Result<T, Diagnostic>
    where
        F: Fn(Diagnostic, TypeMismatch) -> Diagnostic,
    {
        self.into_diagnostic_impl(unification_point, true, message, type_state)
    }

    fn into_diagnostic_impl<F>(
        self,
        unification_point: impl Into<FullSpan> + Clone,
        omit_expected_source: bool,
        message: F,
        type_state: &TypeState,
    ) -> std::result::Result<T, Diagnostic>
    where
        F: Fn(Diagnostic, TypeMismatch) -> Diagnostic;
}
impl<T> UnificationErrorExt<T> for std::result::Result<T, UnificationError> {
    fn add_context(
        self,
        got: TypeVarID,
        expected: TypeVarID,
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
        type_state: &TypeState,
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
                    let e_disp = e.display_with_meta(display_meta, type_state);
                    let g_disp = g.display_with_meta(display_meta, type_state);
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
                            type_state,
                        )
                    } else {
                        diag
                    };

                    let diag = add_known_type_context(
                        diag,
                        unification_point,
                        &g.failing,
                        display_meta,
                        type_state,
                    );
                    diag.type_error(
                        format!("{}", e.failing.display_with_meta(display_meta, type_state)),
                        e.inside
                            .map(|o| o.display_with_meta(display_meta, type_state)),
                        format!("{}", g.failing.display_with_meta(display_meta, type_state)),
                        g.inside
                            .map(|o| o.display_with_meta(display_meta, type_state)),
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
                                .map(|i| i.inner.display_with_meta(display_meta, type_state))
                                .join(", "),
                            traits[traits.len() - 1].display_with_meta(display_meta, type_state)
                        )
                    } else {
                        format!("{}", traits[0].display_with_meta(display_meta, type_state))
                    };
                    let short_msg = format!(
                        "{var} does not implement {impls_str}",
                        var = var.display_with_meta(display_meta, type_state)
                    );
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
                            expected.display_with_meta(is_meta_error, type_state),
                            got.display_with_meta(is_meta_error, type_state)
                        ),
                    )
                    .primary_label(format!(
                        "Expected {}, got {}",
                        expected.display_with_meta(is_meta_error, type_state),
                        got.display_with_meta(is_meta_error, type_state)
                    ));

                    let diag = diag.type_error(
                        format!(
                            "{}",
                            expected
                                .failing
                                .display_with_meta(is_meta_error, type_state)
                        ),
                        expected
                            .inside
                            .as_ref()
                            .map(|o| o.display_with_meta(is_meta_error, type_state)),
                        format!(
                            "{}",
                            got.failing.display_with_meta(is_meta_error, type_state)
                        ),
                        got.inside
                            .as_ref()
                            .map(|o| o.display_with_meta(is_meta_error, type_state)),
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
                            format!(
                                "Expected {expected} in this pipeline.",
                                expected = expected.display(type_state)
                            ),
                        )
                        .primary_label(format!(
                            "Expected {expected} stages",
                            expected = expected.display(type_state)
                        ))
                        .secondary_label(
                            reg,
                            format!(
                                "This final register is number {expected}",
                                expected = got.display(type_state)
                            ),
                        ),
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
    failing: &TypeVarID,
    meta: bool,
    type_state: &TypeState,
) -> Diagnostic {
    match failing.resolve(type_state) {
        TypeVar::Known(k, _, _) => {
            if FullSpan::from(k) != unification_point.clone().into() {
                diag.secondary_label(
                    k,
                    format!(
                        "Type {} inferred here",
                        failing.display_with_meta(meta, type_state)
                    ),
                )
            } else {
                diag
            }
        }
        TypeVar::Unknown(k, _, _, _) => {
            if FullSpan::from(k) != unification_point.clone().into() {
                diag.secondary_label(
                    k,
                    format!(
                        "Type {} inferred here",
                        failing.display_with_meta(meta, type_state)
                    ),
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
    pub fn is_meta_error(&self, type_state: &TypeState) -> bool {
        matches!(
            self.e.failing.resolve(type_state),
            TypeVar::Unknown(_, _, _, _)
        ) || matches!(
            self.g.failing.resolve(type_state),
            TypeVar::Unknown(_, _, _, _)
        )
    }

    pub fn display_e_g(&self, type_state: &TypeState) -> (String, String) {
        let is_meta = self.is_meta_error(type_state);
        (
            self.e.display_with_meta(is_meta, type_state),
            self.g.display_with_meta(is_meta, type_state),
        )
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum UnificationError {
    Normal(TypeMismatch),
    MetaMismatch(TypeMismatch),
    Specific(spade_diagnostics::Diagnostic),
    UnsatisfiedTraits {
        var: TypeVarID,
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
    type_state: &TypeState,
) -> impl Fn(Diagnostic, TypeMismatch) -> Diagnostic + '_ {
    move |diag, tm| {
        let (expected, got) = tm.display_e_g(type_state);
        diag.message(format!(
            "Pattern type mismatch. Expected {expected} got {got}"
        ))
        .primary_label(format!("expected {expected}, got {got}"))
        .secondary_label(reason, format!("because this has type {expected}"))
    }
}
