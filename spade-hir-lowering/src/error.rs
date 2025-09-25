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

/// Error to emit when instantiating non-function without inst
pub fn expect_function(
    callee: &Loc<NameID>,
    unit_def: Loc<()>,
    found_instead: &spade_hir::UnitKind,
) -> Diagnostic {
    let callee_name = &callee.map_ref(|n| n.1.tail());
    let diag = spade_diagnostics::Diagnostic::error(
        callee_name,
        format!("Expected {callee_name} to be a function"),
    )
    .primary_label("Expected function");

    match found_instead {
        spade_hir::UnitKind::Function(_) => {
            spade_diagnostics::Diagnostic::bug(callee_name, "expected fn and got it")
        }
        spade_hir::UnitKind::Entity => diag
            .span_suggest_insert_before("consider adding inst", callee_name, "inst ")
            .secondary_label(unit_def, format!("{callee_name} is an entity")),
        spade_hir::UnitKind::Pipeline {
            depth,
            depth_typeexpr_id: _,
        } => diag
            .span_suggest_insert_before(
                "consider adding inst",
                callee_name,
                format!("inst({depth}) "),
            )
            .secondary_label(unit_def, format!("{callee_name} is a pipeline")),
    }
}

/// Error to emit when using `inst` to instantiate pipeline or entity
pub fn expect_entity(
    inst: &Loc<()>,
    callee: &Loc<NameID>,
    unit_def: Loc<()>,
    found_instead: &spade_hir::UnitKind,
) -> Diagnostic {
    let unit_name = &callee.map_ref(|n| n.1.tail());
    let diag = spade_diagnostics::Diagnostic::error(
        unit_name,
        format!("Expected {unit_name} to be an entity"),
    )
    .primary_label("Expected entity")
    .secondary_label(
        unit_def,
        format!("{unit_name} is a {}", found_instead.name()),
    )
    .secondary_label(inst, "because of this inst");

    match found_instead {
        spade_hir::UnitKind::Function(_) => {
            diag.span_suggest_remove("Consider removing inst", inst)
        }
        spade_hir::UnitKind::Entity => {
            spade_diagnostics::Diagnostic::bug(unit_name, "expected entity and got it")
        }
        spade_hir::UnitKind::Pipeline {
            depth,
            depth_typeexpr_id: _,
        } => diag.span_suggest_insert_after("Consider adding depth", inst, format!("({depth})")),
    }
}

/// Error to emit when using `inst` to instantiate pipeline or entity
pub fn expect_pipeline(
    inst: &Loc<()>,
    callee: &Loc<NameID>,
    unit_def: Loc<()>,
    found_instead: &spade_hir::UnitKind,
) -> Diagnostic {
    let unit_name = &callee.map_ref(|n| n.1.tail());
    let diag = spade_diagnostics::Diagnostic::error(
        unit_name,
        format!("Expected {unit_name} to be a pipeline"),
    )
    .primary_label("Expected pipeline")
    .secondary_label(inst, "because of this inst");

    match found_instead {
        spade_hir::UnitKind::Function(_) => diag
            .span_suggest_remove("Consider removing inst", inst)
            .secondary_label(unit_def, format!("{unit_name} is a function")),
        spade_hir::UnitKind::Entity => diag
            .span_suggest_replace("Consider removing the depth", inst, "inst")
            .secondary_label(unit_def, format!("{unit_name} is an entity")),
        spade_hir::UnitKind::Pipeline {
            depth: _,
            depth_typeexpr_id: _,
        } => spade_diagnostics::Diagnostic::bug(unit_name, "expected pipeline and got it"),
    }
}
