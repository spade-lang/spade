use std::path::Path;

use codespan_reporting::diagnostic::{Diagnostic, Label};
use codespan_reporting::files::SimpleFiles;
use codespan_reporting::term::{
    self,
    termcolor::{ColorChoice, StandardStream},
};

use crate::parser::Error as ParseError;
use crate::semantic_analysis::Error as SemanticError;
use crate::types::Error as TypeError;

pub fn report_parse_error(filename: &Path, file_content: &str, err: ParseError) {
    let mut files = SimpleFiles::new();
    let file_id = files.add(filename.to_string_lossy(), file_content);
    let diag = match err {
        ParseError::Eof => Diagnostic::error().with_message("Reached end of file when parsing"),
        ParseError::LexerError(location) => Diagnostic::error()
            .with_message("Lexer error, unexpected symbol")
            .with_labels(vec![Label::primary(file_id, location)]),
        ParseError::UnexpectedToken { got, expected } => {
            let expected_list = format!(
                "[{}]",
                expected
                    .iter()
                    .map(|s| s.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            );
            let message = format!(
                "Unexpected token. Got `{}`, expected one of {}",
                got.kind.as_str(),
                expected_list,
            );

            Diagnostic::error()
                .with_message(message)
                .with_labels(vec![Label::primary(file_id, got.span)
                    .with_message(format!("expected one of {}", expected_list))])
        }
        ParseError::UnmatchedPair { friend, expected } => Diagnostic::error()
            .with_message(format!("Expected closing {}", expected.as_str()))
            .with_labels(vec![
                Label::primary(file_id, friend.span).with_message(format!("to close this"))
            ]),
        ParseError::ExpectedExpression { got } => {
            let message = format!(
                "Unexpected token. Got {} expected expression",
                got.kind.as_str(),
            );

            Diagnostic::error()
                .with_message(message)
                .with_labels(vec![Label::primary(file_id, got.span)
                    .with_message(format!("expected expression here"))])
        }
        ParseError::ExpectedBlockForEntity { got, loc } => {
            let message = format!("Expected a block for entity");

            Diagnostic::error().with_message(message).with_labels(vec![
                Label::primary(file_id, got.span).with_message("expected block"),
                Label::secondary(file_id, loc.span).with_message("for this entity"),
            ])
        }
    };

    let writer = StandardStream::stderr(ColorChoice::Always);
    let config = codespan_reporting::term::Config::default();

    term::emit(&mut writer.lock(), &config, &files, &diag).unwrap();
}

pub fn report_semantic_error(filename: &Path, file_content: &str, err: SemanticError) {
    let mut files = SimpleFiles::new();
    let file_id = files.add(filename.to_string_lossy(), file_content);
    let diag = match err {
        SemanticError::UndefinedIdentifier(ident) => {
            let (ident, span) = ident.split();
            Diagnostic::error()
                .with_message(format!("Use of undeclared identifier `{}`", ident.0))
                .with_labels(vec![Label::primary(file_id, span)])
        }
        SemanticError::InvalidType(err, loc) => match err {
            TypeError::UnknownTypeName(name) => {
                let (name, span) = name.split();
                Diagnostic::error()
                    .with_message(format!("Unknown type name `{}`", name))
                    .with_labels(vec![Label::primary(file_id, span)])
            }
            TypeError::BitWidthRequired(name) => Diagnostic::error()
                .with_message(format!("{} requires a bit width", name))
                .with_labels(vec![Label::primary(file_id, loc.span)])
                .with_notes(vec![format!("Try using `{}[<width>]`", name)]),
            TypeError::NamedTypesUnsupported => Diagnostic::error()
                .with_message("Types with arbitrary names are unsupported")
                .with_labels(vec![Label::primary(file_id, loc.span)
                    .with_message("Types with arbitrary names are unsupported")]),
            TypeError::NonLiteralTypeSize(_) => unimplemented!(),
            TypeError::CompoundArrayUnsupported => unimplemented!(),
        },
    };

    let writer = StandardStream::stderr(ColorChoice::Always);
    let config = codespan_reporting::term::Config::default();

    term::emit(&mut writer.lock(), &config, &files, &diag).unwrap();
}