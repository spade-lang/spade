use std::{rc::Rc, sync::RwLock};

use spade_codespan_reporting::term::termcolor::Buffer;
use spade_diagnostics::{diag_list::DiagList, CodeBundle, CompilationError, DiagHandler};

pub struct ErrorHandler<'a> {
    failed: bool,
    failed_now: bool,
    pub error_buffer: &'a mut Buffer,
    pub diag_handler: DiagHandler,
    /// Using a RW lock here is just a lazy way of managing the ownership of code to
    /// be able to report errors even while modifying CodeBundle
    pub code: Rc<RwLock<CodeBundle>>,
}

impl<'a> ErrorHandler<'a> {
    pub fn new(
        error_buffer: &'a mut Buffer,
        diag_handler: DiagHandler,
        code: Rc<RwLock<CodeBundle>>,
    ) -> Self {
        ErrorHandler {
            failed: false,
            failed_now: false,
            error_buffer,
            diag_handler,
            code: Rc::clone(&code),
        }
    }

    pub fn set_failed(&mut self) {
        self.failed = true;
        self.failed_now = true;
    }

    pub fn errors_are_recoverable(&mut self) {
        self.failed_now = false;
    }

    pub fn failed(&self) -> bool {
        self.failed
    }

    pub fn failed_now(&mut self) -> bool {
        let result = self.failed_now;
        self.failed_now = false;
        result
    }

    pub fn report(&mut self, err: &impl CompilationError) {
        let is_fatal = match err.severity() {
            spade_diagnostics::diagnostic::DiagnosticLevel::Bug => true,
            spade_diagnostics::diagnostic::DiagnosticLevel::Error => true,
            spade_diagnostics::diagnostic::DiagnosticLevel::Warning => false,
        };
        if is_fatal {
            self.failed = true;
            self.failed_now = true;
        }
        err.report(
            self.error_buffer,
            &self.code.read().unwrap(),
            &mut self.diag_handler,
        );
    }

    pub fn drain_diag_list(&mut self, diag_list: &mut DiagList) {
        for diag in diag_list.drain() {
            self.report(&diag)
        }
    }
}

pub trait Reportable<T> {
    /// Report the error, then discard the error, returning Some if it was Ok
    fn or_report(self, errors: &mut ErrorHandler) -> Option<T>;

    // Report the error and continue without modifying the result
    fn report(self, errors: &mut ErrorHandler) -> Self;
}

impl<T, E> Reportable<T> for Result<T, E>
where
    E: CompilationError,
{
    fn report(self, errors: &mut ErrorHandler) -> Self {
        if let Err(e) = &self {
            errors.report(e);
        }
        self
    }

    fn or_report(self, errors: &mut ErrorHandler) -> Option<T> {
        self.report(errors).ok()
    }
}
