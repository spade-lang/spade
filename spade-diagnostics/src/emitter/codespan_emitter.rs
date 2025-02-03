use std::io::Write;

use spade_codespan_reporting as codespan_reporting;
use spade_codespan_reporting::diagnostic::{
    Diagnostic as CodespanDiagnostic, SpannedNote, Subdiagnostic as CodespanSubdiagnostic,
    Suggestion, SuggestionPart,
};
use spade_codespan_reporting::files::Files;
use spade_codespan_reporting::term::termcolor::{Color, ColorChoice, ColorSpec, WriteColor};
use spade_codespan_reporting::term::{self, termcolor::Buffer};

use itertools::Itertools;
use spade_common::location_info::AsLabel;

use crate::diagnostic::{DiagnosticLevel, Subdiagnostic};
use crate::{CodeBundle, Diagnostic, Emitter};

pub fn color_choice(no_color: bool) -> ColorChoice {
    if no_color {
        ColorChoice::Never
    } else {
        ColorChoice::Auto
    }
}

pub fn codespan_config() -> codespan_reporting::term::Config {
    let mut primary_label_error = ColorSpec::new();
    primary_label_error
        .set_fg(Some(Color::Red))
        .set_intense(true);

    let style = codespan_reporting::term::Styles {
        primary_label_error,
        ..Default::default()
    };
    codespan_reporting::term::Config {
        styles: style,
        ..Default::default()
    }
}

pub struct CodespanEmitter;

impl Emitter for CodespanEmitter {
    fn emit_diagnostic(&mut self, diag: &Diagnostic, buffer: &mut Buffer, code: &CodeBundle) {
        let severity = diag.level.severity();
        let is_bug = diag.level == DiagnosticLevel::Bug;
        let message = diag.labels.message.as_str();
        let primary_label = if let Some(primary_label_message) = diag.labels.primary_label.as_ref()
        {
            diag.labels
                .span
                .primary_label()
                .with_message(primary_label_message.as_str())
        } else {
            diag.labels.span.primary_label()
        };
        let mut labels = vec![primary_label];
        labels.extend(
            diag.labels
                .secondary_labels
                .iter()
                .map(|(sp, msg)| sp.secondary_label().with_message(msg.as_str())),
        );
        let mut simple_notes = vec![];
        let mut subdiagnostics = vec![];
        for subdiag in &diag.subdiagnostics {
            match subdiag {
                Subdiagnostic::Note { level, message } => {
                    if message.as_str().contains('\n') {
                        // For text spanning multiple lines, we want to align it.
                        // Example:
                        //
                        // = note: This note contains some text that
                        //         spans multiple lines
                        //
                        // Manual alignment is very hard to do otherwise, since the message
                        // would need to know the length of the level. "= warning:" needs
                        // more alignment than "= note:" does.
                        let level_len = level.as_str().len() + ": ".len();
                        simple_notes.push(format!(
                            "{}: {}",
                            level.as_str(),
                            message
                                .as_str()
                                .lines()
                                .collect::<Vec<_>>()
                                .join(&("\n".to_string() + &str::repeat(" ", level_len)))
                        ));
                    } else {
                        simple_notes.push(format!("{}: {}", level.as_str(), message.as_str()));
                    }
                }
                Subdiagnostic::SpannedNote {
                    level,
                    labels: note_labels,
                } => {
                    let primary_label =
                        if let Some(primary_label_message) = note_labels.primary_label.as_ref() {
                            note_labels
                                .span
                                .primary_label()
                                .with_message(primary_label_message.as_str())
                        } else {
                            note_labels.span.primary_label()
                        };
                    let mut labels = vec![primary_label];
                    labels.extend(
                        note_labels
                            .secondary_labels
                            .iter()
                            .map(|(sp, msg)| sp.secondary_label().with_message(msg.as_str())),
                    );
                    subdiagnostics.push(CodespanSubdiagnostic::SpannedNote(SpannedNote {
                        severity: level.severity(),
                        message: note_labels.message.as_str().to_string(),
                        labels,
                    }));
                }
                Subdiagnostic::Suggestion { parts, message } => {
                    subdiagnostics.push(CodespanSubdiagnostic::Suggestion(Suggestion {
                        file_id: parts[0].0 .1,
                        message: message.as_str().to_string(),
                        parts: parts
                            .iter()
                            .map(|((sp, _), replacement)| SuggestionPart {
                                range: (*sp).into(),
                                replacement: replacement.to_string(),
                            })
                            .collect(),
                    }))
                }
                Subdiagnostic::TemplateTraceback { .. } => {
                    // Handled separately
                }
                Subdiagnostic::TypeMismatch {
                    got,
                    got_outer,
                    expected,
                    expected_outer,
                } => {
                    let mut note = vec![];
                    note.push(format!("note: Expected: {expected}"));
                    if let Some(expected_outer) = expected_outer {
                        note.push(format!("            in: {expected_outer}"));
                    }
                    note.push(format!("           Got: {got}"));
                    if let Some(got_outer) = got_outer {
                        note.push(format!("            in: {got_outer}"));
                    }
                    simple_notes.push(note.join("\n"))
                }
            }
        }

        let type_tracebacks = diag
            .subdiagnostics
            .iter()
            .filter_map(|d| {
                if let Subdiagnostic::TemplateTraceback { span, message } = d {
                    let filename = code.files.name(span.1).unwrap();
                    let line = code
                        .files
                        .location(span.1, span.0.start().0 as usize)
                        .unwrap()
                        .line_number;
                    Some(format!("{filename}:{line} {}", message.as_str()))
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();

        if !type_tracebacks.is_empty() {
            let message = vec!["The error is in a generic unit instantiated at".to_string()]
                .into_iter()
                .chain(type_tracebacks)
                .join("\n╰ ");

            simple_notes.push(message)
        };

        let diag = CodespanDiagnostic::new(severity)
            .with_message(message)
            .with_labels(labels)
            .with_notes(simple_notes)
            .with_subdiagnostics(subdiagnostics);

        if buffer.supports_color() && is_bug {
            // Ignore errors from trying to print the panik.
            let _ = writeln!(buffer, "{}", super::panik::PANIK);
        }

        term::emit(buffer, &codespan_config(), &code.files, &diag).unwrap();
    }
}
