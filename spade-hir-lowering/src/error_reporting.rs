use crate::usefulness::Witness;
use crate::Error;
use codespan_reporting::diagnostic::Diagnostic;
use codespan_reporting::term::{self, termcolor::Buffer};
use itertools::Itertools;
use spade_common::error_reporting::{codespan_config, AsLabel, CodeBundle, CompilationError};

fn format_witnesses(witnesses: &[Witness]) -> String {
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

impl CompilationError for Error {
    fn report(&self, buffer: &mut Buffer, code: &CodeBundle) {
        // Errors which require special handling
        match self {
            Error::UnificationError(underlying) => {
                underlying.report(buffer, code);
                return;
            }
            Error::ArgumentError(e) => {
                e.report(buffer, code);
                return;
            }
            _ => {}
        }

        let diag = match self {
            Error::ArgumentError(_) => unreachable!(),
            Error::UnificationError(_) => unreachable!(),
            Error::UsingGenericType { expr, t } => Diagnostic::error()
                .with_message(format!("Type of expression is not fully known"))
                .with_labels(vec![expr
                    .primary_label()
                    .with_message(format!("Incomplete type"))])
                .with_notes(vec![format!("Found incomplete type: {}", t)]),
            Error::CastToLarger { from, to } => Diagnostic::error()
                .with_message(format!("Truncating to a larger value"))
                .with_labels(vec![
                    from.primary_label()
                        .with_message(format!("This value is {from} bytes")),
                    to.secondary_label()
                        .with_message(format!("But it is truncated to {to} bytes")),
                ])
                .with_notes(vec![format!("Truncation can only remove bits")]),
            Error::ConcatSizeMismatch {
                lhs,
                rhs,
                result,
                expected,
            } => Diagnostic::error()
                .with_message(format!(
                    "Concatenation produces {result} bits, expected {expected}"
                ))
                .with_labels(vec![
                    result
                        .primary_label()
                        .with_message(format!("Expected {expected} bits")),
                    lhs.secondary_label()
                        .with_message(format!("This has {lhs} bits")),
                    rhs.secondary_label()
                        .with_message(format!("This has {rhs} bits")),
                ]),
            Error::UndefinedVariable { name } => Diagnostic::error()
                .with_message(format!("Use of undeclared name {name}"))
                .with_labels(vec![name.primary_label().with_message("Undeclared name")]),
            Error::UseBeforeReady {
                name,
                unavailable_for,
                referenced_at_stage,
            } => Diagnostic::error()
                .with_message(format!("Use of {name} before it is ready"))
                .with_labels(vec![name.primary_label().with_message(format!(
                    "Is unavailable for another {unavailable_for} stages"
                ))])
                .with_notes(vec![
                    format!("Requesting {name} from stage {referenced_at_stage}"),
                    format!(
                        "But it will not be available until stage {}",
                        referenced_at_stage + unavailable_for
                    ),
                ]),
            Error::AvailabilityMismatch { prev, new } => Diagnostic::error()
                .with_message("All subexpressions need the same pipeline delay")
                .with_labels(vec![
                    new.primary_label()
                        .with_message(format!("This has delay {new}")),
                    prev.secondary_label()
                        .with_message(format!("But this has delay {prev}")),
                ]),
            Error::InstantiatingGenericBuiltin { loc, head } => Diagnostic::error()
                .with_message("Generic builtins can not be instantiated")
                .with_labels(vec![
                    loc.primary_label().with_message("Invalid instance"),
                    head.secondary_label()
                        .with_message("Because this is a generic __builtin__"),
                ]),
            Error::MissingPatterns {
                match_expr,
                useful_branches,
            } => {
                let witnesses = format_witnesses(useful_branches);
                Diagnostic::error()
                    .with_message(format!("Non-exhaustive match: {witnesses} not covered",))
                    .with_labels(vec![match_expr
                        .primary_label()
                        .with_message(format!("{witnesses} not covered"))])
            }
            Error::RefutablePattern {
                binding_kind,
                pattern,
                witnesses,
            } => {
                let witnesses = format_witnesses(witnesses);

                Diagnostic::error()
                    .with_message(format!("Refutable pattern in local binding: {witnesses} not covered"))
                    .with_labels(vec![
                        pattern.primary_label().with_message(format!("pattern {witnesses} not covered"))
                    ])
                    .with_notes(vec![
                        format!("{binding_kind} requires a pattern which matches all possible options, such as a variable, struct or enum with only 1 option."),
                        format!("hint: you might want to use match statement to handle different cases")
                    ])
            }
            Error::PortInRegister { loc, ty } => Diagnostic::error()
                .with_message("Ports can not be put in a register")
                .with_labels(vec![loc.primary_label().with_message("This is a port")])
                .with_notes(vec![format!("{ty} is a port")]),
            Error::PortInGenericType { loc, param, actual } => Diagnostic::error()
                .with_message("Generic types can not be ports")
                .with_labels(vec![loc.primary_label().with_message(format!(
                    "Parameter {param} is {actual} which is a port type"
                ))]),
            Error::InternalExpressionWithoutType(loc) => Diagnostic::error()
                .with_message("(Internal error) expression did not have a type")
                .with_labels(vec![loc
                    .primary_label()
                    .with_message("Expression had no type")]),
        };

        term::emit(buffer, &codespan_config(), &code.files, &diag).unwrap();
    }
}
