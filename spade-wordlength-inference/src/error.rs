use spade_common::location_info::Loc;
use spade_diagnostics::Diagnostic;
use spade_macros::IntoDiagnostic;

use crate::range::Range;

#[derive(IntoDiagnostic)]
#[diagnostic(
    error,
    "Got a type-error while doing wordlength inference - please report this!"
)]
pub struct UnificationError {
    #[diagnostic(primary, "This place is somehow related")]
    pub at: Loc<()>,
}

#[derive(IntoDiagnostic)]
#[diagnostic(error, "Word length mismatch. Got {} bits but expected {} bits", diag.inferred, diag.typechecked)]
pub struct WordlengthMismatch {
    #[diagnostic(primary, "Got {} bits, expected {}", diag.inferred, diag.typechecked)]
    pub inferred_at: Loc<()>,
    pub inferred: Range,
    pub typechecked: Range,
}

pub type Result<T> = std::result::Result<T, Diagnostic>;
