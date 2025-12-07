use spade_codespan_reporting::diagnostic::Diagnostic;
use spade_codespan_reporting::term::{self, termcolor::Buffer};

use spade_common::location_info::{AsLabel, Loc};
use spade_diagnostics::emitter::codespan_config;
use spade_diagnostics::{CodeBundle, CompilationError, DiagHandler};

use crate::ValueName;

pub struct AssertedExpression(pub Loc<ValueName>);

impl CompilationError for AssertedExpression {
    fn report(&self, buffer: &mut Buffer, code: &CodeBundle, _diag_handler: &mut DiagHandler) {
        let diag = Diagnostic::error()
            .with_message("Assertion failed")
            .with_labels(vec![self
                .0
                .primary_label()
                .with_message("This expression is false")]);

        term::emit(buffer, &codespan_config(), &code.files, &diag).unwrap();
    }

    fn severity(&self) -> spade_diagnostics::diagnostic::DiagnosticLevel {
        eprintln!("Called .severity() on an AssertedExpression");
        spade_diagnostics::diagnostic::DiagnosticLevel::Error
    }
}
