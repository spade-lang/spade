//! This crate is all about constructing structured [`Diagnostic`]s and emitting
//! them in some specified format.
//!
//! At the time of writing we are in the process of porting old diagnostics to
//! these structured diagnostics, which is [tracked in spade#190 on
//! GitLab](https://gitlab.com/spade-lang/spade/-/issues/190).
//!
//! ## Diagnostics
//!
//! [`Diagnostic`]s are created using builders. The simplest compiler error looks like this:
//!
//! ```
//! # use codespan_reporting::term::termcolor::Buffer;
//! # use spade_diagnostics::{CodeBundle, Diagnostic};
//! # use spade_diagnostics::emitter::{CodespanEmitter, Emitter};
//! # let mut emitter = CodespanEmitter;
//! # let mut buffer = Buffer::no_color();
//! let code = CodeBundle::new("hello ocean!".to_string());
//! // Spans are never created manually like this. They are created by the lexer
//! // and need to be combined with each other to form bigger spans.
//! let span = (codespan::Span::from(6..11), 0);
//! let diag = Diagnostic::error(span, "something's fishy :spadesquint:");
//! emitter.emit_diagnostic(&diag, &mut buffer, &code);
//! # println!("{}", String::from_utf8_lossy(buffer.as_slice()));
//! # // for takin' a peek at the output:
//! # // println!("{}", String::from_utf8_lossy(buffer.as_slice())); panic!();
//! ```
//!
//! ```text
//! error: something's fishy :spadesquint:
//!   ┌─ <str>:1:7
//!   │
//! 1 │ hello ocean!
//!   │       ^^^^^
//! ```
//!
//! As mentioned, spans shouldn't be created manually. They are passed on from
//! earlier stages in the compiler, all the way from the tokenizer, usually as a
//! [`Loc<T>`]. Additional Locs can then be created by combining earlier Locs, for
//! example using [`between_locs`]. The rest of this documentation will assume that
//! Locs and code exist, and instead focus on creating diagnostics. The examples
//! will be inspired by diagnostics currently emitted by spade.
//!
//! [`Loc<T>`]: spade_common::location_info::Loc
//! [`between_locs`]: spade_common::location_info::WithLocation::between_locs
//!
//! ### Secondary labels
//!
//! ```text
//! fn foo() {}
//!    ^^^ ------------- first_foo
//! fn bar() {}
//!
//! fn foo() {}
//!    ^^^ ------------- second_foo
//! ```
//!
//! ```
//! # use codespan_reporting::term::termcolor::Buffer;
//! # use spade_common::location_info::WithLocation;
//! # use spade_diagnostics::{CodeBundle, Diagnostic};
//! # use spade_diagnostics::emitter::{CodespanEmitter, Emitter};
//! # let mut emitter = CodespanEmitter;
//! # let mut buffer = Buffer::no_color();
//! # let code = CodeBundle::new(r#"fn foo() {}
//! #
//! # fn bar() {}
//! #
//! # fn foo() {}
//! # "#.to_string());
//! # let first_foo = ().at(0, &(4..7));
//! # let second_foo = ().at(0, &(30..33));
//! # let diag =
//! Diagnostic::error(second_foo, "Duplicate definition of item")
//!     .primary_label("Second definition here")
//!     .secondary_label(first_foo, "First definition here")
//! # ;
//! # emitter.emit_diagnostic(&diag, &mut buffer, &code);
//! # // println!("{}", String::from_utf8_lossy(buffer.as_slice())); panic!();
//! ```
//!
//! ```text
//! error: Duplicate definition of item
//!   ┌─ <str>:5:4
//!   │
//! 1 │ fn foo() {}
//!   │    --- First definition here
//!   ·
//! 5 │ fn foo() {}
//!   │    ^^^ Second definition here
//! ```
//!
//! Note that labels are sorted by location in the code automatically.
//!
//! ### Notes and spanned notes
//!
//! Notes are additional snippets of text that are shown after the labels. They
//! can be used to give additional information or help notices.
//!
//! ```text
//! fn foo(port: &int<10>) {}
//!              ^^^^^^^^ ------ port_ty
//! ```
//!
//! ```
//! # use codespan_reporting::term::termcolor::Buffer;
//! # use spade_common::location_info::WithLocation;
//! # use spade_diagnostics::{CodeBundle, Diagnostic};
//! # use spade_diagnostics::emitter::{CodespanEmitter, Emitter};
//! # let mut emitter = CodespanEmitter;
//! # let mut buffer = Buffer::no_color();
//! # let code = CodeBundle::new(r#"fn foo(port: &int<10>) {}"#.to_string());
//! # let port_ty = ().at(0, &(13..21));
//! # let diag =
//! Diagnostic::error(port_ty, "Port argument in function")
//!     .primary_label("This is a port")
//!     .note("Only entities and pipelines can take ports as arguments")
//! # ;
//! # emitter.emit_diagnostic(&diag, &mut buffer, &code);
//! # // println!("{}", String::from_utf8_lossy(buffer.as_slice())); panic!();
//! ```
//!
//! ```text
//! error: Port argument in function
//!   ┌─ <str>:1:14
//!   │
//! 1 │ fn foo(port: &int<10>) {}
//!   │              ^^^^^^ This is a port
//!   │
//!   = note: Only entities and pipelines can take ports as arguments
//! ```
//!
//! The spanned versions are rendered like labels, but compared to the secondary
//! labels they are always rendered separately.
//!
//! ### Suggestions
//!
//! Suggestions can be used to format a change suggestion to the user. There are a
//! bunch of convenience functions depending on what kind of suggestion is needed.
//! Try to use them since they show the intent behind the suggestion.
//!
//! ```text
//! struct port S {
//!        ^^^^ --------------- port_kw
//!     field1: &bool,
//!     field2: bool,
//!     ^^^^^^  ^^^^ ---------- field_ty
//!          |----------------- field
//! }
//! ```
//!
//! ```
//! # use codespan_reporting::term::termcolor::Buffer;
//! # use spade_common::location_info::WithLocation;
//! # use spade_diagnostics::{CodeBundle, Diagnostic};
//! # use spade_diagnostics::emitter::{CodespanEmitter, Emitter};
//! # let mut emitter = CodespanEmitter;
//! # let mut buffer = Buffer::no_color();
//! # let code = CodeBundle::new(r#"struct port S {
//! #     field1: &bool,
//! #     field2: bool,
//! # }
//! # "#.to_string());
//! # let port_kw = ().at(0, &(7..11));
//! # let field_ty = ().at(0, &(47..51));
//! # let field = "field2".at(0, &(39..45));
//! # let diag =
//! Diagnostic::error(field_ty, "Non-port in port struct")
//!     .primary_label("This is not a port type")
//!     .secondary_label(port_kw, "This is a port struct")
//!     .note("All members of a port struct must be ports")
//!     .span_suggest_insert_before(
//!         format!("Consider making {field} a wire"),
//!         field_ty,
//!         "&",
//!     )
//! # ;
//! # emitter.emit_diagnostic(&diag, &mut buffer, &code);
//! # // println!("{}", String::from_utf8_lossy(buffer.as_slice())); panic!();
//! ```
//!
//! ```text
//! error: Non-port in port struct
//!   ┌─ <str>:3:13
//!   │
//! 1 │ struct port S {
//!   │        ---- This is a port struct
//! 2 │     field1: &bool,
//! 3 │     field2: bool,
//!   │             ^^^^ This is not a port type
//!   │
//!   = note: All members of a port struct must be ports
//!   = Consider making field2 a wire
//!   │
//! 3 │     field2: &bool,
//!   │             +
//! ```
//!
//! The convenience functions start with `span_suggest` and include
//! [`span_suggest_insert_before`] (above), [`span_suggest_replace`] and
//! [`span_suggest_remove`].
//!
//! [`span_suggest_insert_before`]: Diagnostic::span_suggest_insert_before
//! [`span_suggest_replace`]: Diagnostic::span_suggest_replace
//! [`span_suggest_remove`]: Diagnostic::span_suggest_remove
//!
//! Multipart suggestions are basically multiple single part suggestions. Use them
//! when the suggestion needs to include changes that are separated in the code.
//!
//! ```text
//! enum E {
//!     VariantA(a: bool),
//!             ^       ^ ---- close_paren
//!             |------------- open_paren
//! }
//! ```
//!
//! ```
//! # use codespan_reporting::term::termcolor::Buffer;
//! # use spade_common::location_info::WithLocation;
//! # use spade_diagnostics::{CodeBundle, Diagnostic};
//! # use spade_diagnostics::diagnostic::{SuggestionParts};
//! # use spade_diagnostics::emitter::{CodespanEmitter, Emitter};
//! # let mut emitter = CodespanEmitter;
//! # let mut buffer = Buffer::no_color();
//! # let code = CodeBundle::new(r#"enum E {
//! #     VariantA(a: bool),
//! # }
//! # "#.to_string());
//! # let open_paren = ().at(0, &(21..22));
//! # let close_paren = ().at(0, &(29..30));
//! # let diag =
//! Diagnostic::error(open_paren, "Expected '{', '}' or ','")
//!     .span_suggest_multipart(
//!         "Use '{' if you want to add items to this enum variant",
//!         SuggestionParts::new()
//!             .part(open_paren, "{")
//!             .part(close_paren, "}"),
//!     )
//! # ;
//! # emitter.emit_diagnostic(&diag, &mut buffer, &code);
//! # // println!("{}", String::from_utf8_lossy(buffer.as_slice())); panic!();
//! ```
//!
//! ```text
//! error: Expected '{', '}' or ','
//!   ┌─ <str>:2:13
//!   │
//! 2 │     VariantA(a: bool),
//!   │             ^
//!   │
//!   = Use '{' if you want to add items to this enum variant
//!   │
//! 2 │     VariantA{a: bool},
//!   │             ~       ~
//! ```
//!
//! ## Emitters
//!
//! We also need some way to show these diagnostics to the user. For this we have
//! [`Emitter`]s which abstract away the details of formatting the diagnostic. The
//! default emitter is the [`CodespanEmitter`] which formats the diagnostics using
//! a [forked `codespan-reporting`](https://gitlab.com/spade-lang/codespan).
//!
//! [`CodespanEmitter`]: emitter::CodespanEmitter
//!
//! > If you use the compiler as a library (like we do for the [Spade Language
//! > Server](https://gitlab.com/spade-lang/spade-language-server/)) you can define
//! > your own emitter that formats the diagnostics. The language server, for
//! > example, has [its own
//! > emitter](https://gitlab.com/spade-lang/spade-language-server/-/blob/5eccf6c71724ec1074f69f535132a5b298d583ba/src/main.rs#L75)
//! > that sends LSP-friendly diagnostics to the connected Language Server Client.
//!
//! When writing diagnostics in the compiler you usually don't have to care about
//! the emitter. Almost everywhere, the diagnostics are returned and handled by
//! someone else. (In Spade, that someone else is `spade-compiler`.)

use std::io::Write;

use codespan_reporting::files::{Files, SimpleFiles};
use codespan_reporting::term::termcolor::Buffer;

use spade_common::location_info::{AsLabel, Loc};

pub use codespan;
pub use diagnostic::Diagnostic;
pub use emitter::Emitter;

pub mod diagnostic;
pub mod emitter;

/// A bundle of all the source code included in the current compilation
#[derive(Clone)]
pub struct CodeBundle {
    pub files: SimpleFiles<String, String>,
}

impl CodeBundle {
    // Create a new code bundle adding the passed string as the 0th file
    pub fn new(string: String) -> Self {
        let mut files = SimpleFiles::new();
        files.add("<str>".to_string(), string);
        Self { files }
    }

    pub fn from_files(files: &[(String, String)]) -> Self {
        let mut result = Self {
            files: SimpleFiles::new(),
        };
        for (name, content) in files {
            result.add_file(name.clone(), content.clone());
        }
        result
    }

    pub fn add_file(&mut self, filename: String, content: String) -> usize {
        self.files.add(filename, content)
    }

    pub fn dump_files(&self) -> Vec<(String, String)> {
        let mut all_files = vec![];
        loop {
            match self.files.get(all_files.len()) {
                Ok(file) => all_files.push((file.name().clone(), file.source().clone())),
                Err(codespan_reporting::files::Error::FileMissing) => break,
                Err(e) => {
                    panic!("{e}")
                }
            };
        }
        all_files
    }

    pub fn source_loc<T>(&self, loc: &Loc<T>) -> String {
        let location = self
            .files
            .location(loc.file_id(), loc.span.start().to_usize())
            .expect("Loc was not in code bundle");
        format!(
            "{}:{},{}",
            self.files.get(loc.file_id()).unwrap().name(),
            location.line_number,
            location.column_number
        )
    }
}

pub trait CompilationError {
    fn report(&self, buffer: &mut Buffer, code: &CodeBundle, diag_handler: &mut DiagHandler);
}

impl CompilationError for std::io::Error {
    fn report(&self, buffer: &mut Buffer, _code: &CodeBundle, _diag_handler: &mut DiagHandler) {
        if let Err(e) = buffer.write_all(self.to_string().as_bytes()) {
            eprintln!(
                "io error when writing io error to error buffer\noriginal error: {}\nnew error: {}",
                self, e
            );
        }
    }
}

impl CompilationError for Diagnostic {
    fn report(&self, buffer: &mut Buffer, code: &CodeBundle, diag_handler: &mut DiagHandler) {
        diag_handler.emit(self, buffer, code)
    }
}

pub struct DiagHandler {
    emitter: Box<dyn Emitter + Send>,
    // Here we can add more shared state for diagnostics. For example, rustc can
    // stash diagnostics that can be retrieved in later stages, indexed by (Span, StashKey).
}

impl DiagHandler {
    pub fn new(emitter: Box<dyn Emitter + Send>) -> Self {
        Self { emitter }
    }

    pub fn emit(&mut self, diagnostic: &Diagnostic, buffer: &mut Buffer, code: &CodeBundle) {
        self.emitter.emit_diagnostic(diagnostic, buffer, code);
    }
}

#[cfg(test)]
mod tests {
    use codespan_reporting::term::termcolor::Buffer;

    use crate::emitter::CodespanEmitter;
    use crate::{CodeBundle, Diagnostic, Emitter};

    #[test]
    fn bug_diagnostics_works() {
        let code = CodeBundle::new("hello goodbye".to_string());
        let sp = ((6..13).into(), 0);
        let mut buffer = Buffer::no_color();
        let mut emitter = CodespanEmitter;
        let diagnostic = Diagnostic::bug(sp, "oof");
        emitter.emit_diagnostic(&diagnostic, &mut buffer, &code);
        insta::assert_snapshot!(String::from_utf8(buffer.into_inner()).unwrap());
    }
}
