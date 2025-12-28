use crate::Diagnostic;

#[derive(Debug, Clone, Default)]
pub struct DiagList {
    pub errors: Vec<Diagnostic>,
}

impl DiagList {
    pub fn new() -> Self {
        Self { errors: vec![] }
    }

    pub fn drain(&mut self) -> Vec<Diagnostic> {
        let mut result = vec![];
        std::mem::swap(&mut self.errors, &mut result);
        result
    }

    pub fn drain_to_new(&mut self) -> Self {
        Self {
            errors: self.drain(),
        }
    }

    pub fn extend(&mut self, other: &mut Self) {
        self.errors.extend(other.drain())
    }
}

impl Drop for DiagList {
    fn drop(&mut self) {
        if !self.errors.is_empty() {
            println!("WARNING: Dropped a DiagList without draining the errors");
            println!(
                "Backtrace:\n{}",
                std::backtrace::Backtrace::capture().to_string()
            )
        }
    }
}

pub trait ResultExt<T> {
    fn handle_in(self, diag: &mut DiagList) -> Option<T>;
}

impl<T> ResultExt<T> for Result<T, Diagnostic> {
    fn handle_in(self, diag: &mut DiagList) -> Option<T> {
        match self {
            Ok(val) => Some(val),
            Err(err) => {
                diag.errors.push(err);
                None
            }
        }
    }
}

impl Diagnostic {
    pub fn handle_in(self, diag: &mut DiagList) {
        diag.errors.push(self);
    }
}
