use itertools::Itertools;
use spade_common::{location_info::Loc, name::NameID};
use spade_diagnostics::Diagnostic;

use crate::usefulness::{Usefulness, Witness};

pub type Result<T> = std::result::Result<T, Diagnostic>;

pub(crate) fn undefined_variable(name: &Loc<NameID>) -> Diagnostic {
    Diagnostic::error(name, format!("Use of undeclared name {name}"))
        .primary_label("Undeclared name")
}

pub(crate) fn refutable_pattern_diagnostic(
    loc: Loc<()>,
    refutability: &Usefulness,
    binding_kind: &str,
) -> Diagnostic {
    let witnesses = format_witnesses(&refutability.witnesses);

    Diagnostic::error(loc, format!("Refutable pattern in local binding: {witnesses} not covered"))
        .primary_label(format!("pattern {witnesses} not covered"))
        .note(format!("{binding_kind} requires a pattern which matches all possible options, such as a variable, struct or enum with only 1 option."))
        .help("you might want to use match statement to handle different cases")
}

pub fn format_witnesses(witnesses: &[Witness]) -> String {
    // Print 1 or 2 missing patterns in full, if more print and X more not covered
    let threshold_len = 2;
    if witnesses.len() == 1 {
        format!("pattern {}", witnesses[0])
    } else if witnesses.len() <= threshold_len {
        format!(
            "patterns {}",
            witnesses.iter().map(|w| format!("{w}")).join(", ")
        )
    } else {
        let partial = witnesses[0..threshold_len]
            .iter()
            .map(|w| format!("{w}"))
            .join(", ");
        format!(
            "patterns {partial} and {} more",
            witnesses.len() - threshold_len
        )
    }
}
