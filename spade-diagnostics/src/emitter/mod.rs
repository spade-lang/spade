use spade_codespan_reporting::term::termcolor::Buffer;

use crate::CodeBundle;
use crate::diagnostic::Diagnostic;

pub use codespan_emitter::{CodespanEmitter, codespan_config};

pub mod codespan_emitter;
mod panik;

/// Something that can format and emit diagnostics.
pub trait Emitter {
    /// Emit a diagnostic, e.g. print it.
    fn emit_diagnostic(&mut self, diag: &Diagnostic, buffer: &mut Buffer, code: &CodeBundle);
}
