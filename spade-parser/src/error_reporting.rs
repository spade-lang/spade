use crate::lexer::TokenKind;
use crate::{Error, Token};
use codespan_reporting::diagnostic::{Diagnostic, Label, Suggestion};
use codespan_reporting::term::{self, termcolor::Buffer};
use spade_common::error_reporting::{codespan_config, AsLabel, CodeBundle, CompilationError};

fn unexpected_token_list<'a>(expected: impl IntoIterator<Item = &'a str>) -> String {
    let expected = expected
        .into_iter()
        .map(|s| format!("`{}`", s))
        .collect::<Vec<_>>();

    let count = expected.len();
    if count == 1 {
        format!("{}", expected[0])
    } else {
        format!(
            "{}, or {}",
            expected[0..(count - 1)].join(", "),
            expected[count - 1]
        )
    }
}

fn unexpected_token_message<'a>(got: &TokenKind, expected_list: &str) -> String {
    format!("Unexpected `{}`, expected {}", got.as_str(), expected_list,)
}

fn unexpected_token<'a>(
    file_id: usize,
    got: Token,
    expected: impl IntoIterator<Item = &'a str>,
) -> Diagnostic<usize> {
    let expected_list = unexpected_token_list(expected);
    let message = unexpected_token_message(&got.kind, &expected_list);

    Diagnostic::error().with_message(message).with_labels(vec![
        Label::primary(file_id, got.span).with_message(format!("expected {}", expected_list))
    ])
}

impl CompilationError for Error {
    fn report(self, buffer: &mut Buffer, code: &CodeBundle) {
        let diag = match self {
            Error::Eof => Diagnostic::error().with_message("Reached end of file when parsing"),
            Error::LexerError(file_id, location) => Diagnostic::error()
                .with_message("Lexer error, unexpected symbol")
                .with_labels(vec![Label::primary(file_id, location)]),
            Error::UnexpectedToken { got, expected } => {
                unexpected_token(got.file_id, got, expected)
            }
            Error::UnexpectedEndOfArgList { got, expected } => {
                unexpected_token(got.file_id, got, expected.iter().map(|tok| tok.as_str()))
            }
            Error::UnmatchedPair {
                friend,
                expected,
                got,
            } => Diagnostic::error()
                .with_message(format!(
                    "Expected closing `{}`, got `{}`",
                    expected.as_str(),
                    got.kind.as_str()
                ))
                .with_labels(vec![
                    Label::primary(got.file_id, got.span)
                        .with_message(format!("Expected `{}`", expected.as_str())),
                    friend
                        .secondary_label()
                        .with_message(format!("to close this")),
                ]),
            Error::ExpectedExpression { got } => {
                let message = format!("Unexpected `{}`, expected expression", got.kind.as_str(),);

                Diagnostic::error()
                    .with_message(message)
                    .with_labels(vec![Label::primary(got.file_id, got.span)
                        .with_message(format!("expected expression here"))])
            }
            Error::ExpectedIntegerLiteral { got } => {
                let message = format!("Unexpected `{}`, expected integer literal", got.kind.as_str());

                Diagnostic::error()
                    .with_message(message)
                    .with_labels(vec![Label::primary(got.file_id, got.span)
                        .with_message(format!("expected integer literal here"))])
            }
            Error::NonZeroLowerBound { got } => {
                let message = format!("Only non-zero lower bounds are supported, got `{}`", got);

                Diagnostic::error()
                    .with_message(message)
                    .with_labels(vec![Label::primary(got.file_id, got.span)
                        .with_message(format!("this lower bound"))])
                    .with_suggestions(vec![Suggestion {
                        file_id: got.file_id,
                        range: got.span.into(),
                        replacement: format!("0"),
                        message: format!("Consider setting this lower bound to 0"),
                    }])
            }
            Error::EqualLowerUpperBound { lower, upper } => {
                Diagnostic::error()
                    .with_message(format!("Lower and upper bounds are equal to each other"))
                    .with_labels(vec![
                        Label::primary(lower.file_id, lower.span).with_message(format!("this lower bound")),
                        Label::primary(upper.file_id, upper.span).with_message(format!("this upper bound")),
                    ])
                    .with_notes(vec![
                        format!("The type has no valid values")
                    ])
            }
            Error::ExpectedBlock { for_what, got, loc } => {
                let message = format!("Expected a block for {}", for_what);

                Diagnostic::error().with_message(message).with_labels(vec![
                    loc.primary_label().with_message("expected block here"),
                    got.primary_label().with_message("found this instead"),
                    loc.secondary_label()
                        .with_message(format!("for this {}", for_what)),
                ])
            }
            Error::ExpectedItem { got } => Diagnostic::error()
                .with_message(format!("Expected item, found {}", got.kind.as_str()))
                .with_labels(vec![
                    Label::primary(got.file_id, got.span).with_message("Expected item")
                ]),
            Error::MissingTupleIndex { hash_loc } => {
                let message = format!("Expected an index after #");

                Diagnostic::error()
                    .with_message(message)
                    .with_labels(vec![hash_loc
                        .primary_label()
                        .with_message("expected index")])
            }
            Error::ExpectedArgumentList(for_what) => {
                let message = format!("Expected arguments for {}", for_what);

                Diagnostic::error()
                    .with_message(message)
                    .with_labels(vec![for_what
                        .primary_label()
                        .with_message("Expected an argument list")])
            }
            Error::ExpectedPipelineDepth { got } => {
                let message = format!("Expected pipeline depth");

                Diagnostic::error()
                    .with_message(message)
                    .with_labels(vec![got
                        .primary_label()
                        .with_message("Expected pipeline depth")])
                    .with_notes(vec![
                        format!("Found {}", got.kind.as_str()),
                        format!("Pipeline depth can only be fixed integers"),
                    ])
            }
            Error::ExpectedOffset{got} => {
                Diagnostic::error()
                    .with_message(format!("Expected an offset"))
                    .with_labels(vec![got.primary_label()
                        .with_message("Expected offset")
                    ])
            }
            Error::PipelineRefInFunction{ at, fn_keyword } => {
                Diagnostic::error()
                    .with_message(format!("Pipeline stage reference in function"))
                    .with_labels(vec![
                        at.primary_label()
                            .with_message("Stage reference is not allowed here"),
                        fn_keyword.secondary_label().with_message("Because this is a function")
                    ])
            }
            Error::PipelineRefInEntity{ at, entity_keyword } => {
                Diagnostic::error()
                    .with_message(format!("Pipeline stage reference in entity"))
                    .with_labels(vec![
                        at.primary_label()
                            .with_message("Stage reference is not allowed here"),
                        entity_keyword.secondary_label().with_message("Because this is an enity")
                    ])
            }
            Error::ExpectedType(found) => Diagnostic::error()
                .with_message(format!(
                    "Unexpected token. Got `{}`, expected type",
                    found.kind.as_str()
                ))
                .with_labels(vec![found.primary_label().with_message("Expected a type")]),
            Error::ExpectedExpressionOrStage { got } => {
                let message = format!("Expected return expression or pipeline stage");

                Diagnostic::error()
                    .with_message(message)
                    .with_labels(vec![got
                        .primary_label()
                        .with_message("Expected expression or stage")])
                    .with_notes(vec![format!("Found {}", got.kind.as_str())])
            }
            Error::EmptyDeclStatement { at } => Diagnostic::error()
                .with_message("Found empty decl statement")
                .with_labels(vec![at
                    .primary_label()
                    .with_message("decl doesn't declare anything")]),
            Error::InstInFunction {at, fn_keyword} => Diagnostic::error()
                .with_message("Entities or pipelines can not be instanciated in functions")
                .with_labels(vec![
                    at
                        .primary_label()
                        .with_message("inst not allowed here"),
                    fn_keyword
                        .secondary_label()
                        .with_message("Because this is a function")
                ])
                .with_notes(vec![
                    format!("Functions can only contain combinatorial logic"),
                ])
                .with_suggestions(vec![Suggestion {
                    file_id: fn_keyword.file_id,
                    range: fn_keyword.span.into(),
                    replacement: format!("entity"),
                    message: format!("Consider making the function an entity"),
                }]),
            Error::RegInFunction{at, fn_keyword} => Diagnostic::error()
                .with_message("Functions can not contain registers")
                .with_labels(vec![
                    at
                        .primary_label()
                        .with_message("reg not allowed here"),
                    fn_keyword
                        .secondary_label()
                        .with_message("Because this is a function")
                ])
                .with_notes(vec![
                    format!("Functions can only contain combinatorial logic"),
                    format!("If you want to do this, make the function an entity")
                ]),

            // Internal errors
            Error::InternalExpectedItemContext{at} => Diagnostic::error()
                .with_message("(Internal) Attempted to parse something which requires an item context with none existing")
                .with_labels(vec![at.primary_label().with_message("Here")]),
            Error::InternalOverwritingItemContext{at, prev} => Diagnostic::error()
                .with_message("(Internal) Overwriting previously uncleared item_context")
                .with_labels(vec![
                    at.primary_label().with_message("New context set because of this"),
                    prev.secondary_label().with_message("Previous context set here")
                ]),
            Error::ExpectedArraySize{array, inner} => Diagnostic::error()
                .with_message("Expected array size")
                .with_labels(vec![array.primary_label().with_message("This array type")])
                .with_notes(vec![format!("Array types need a specified size")])
                .with_suggestions(vec![Suggestion {
                    file_id: array.file_id,
                    range: inner.span.end().to_usize()..inner.span.end().to_usize(),
                    replacement: format!("; N"),
                    message: format!("Insert a size here")
                }]),
            Error::StageOutsidePipeline(loc) => Diagnostic::error()
                .with_message("Stage outside pipeline")
                .with_labels(vec![loc.primary_label().with_message("stage is not allowed here")])
                .with_notes(vec![format!("Stages are only allowed in the root block of a pipeline")])
        };

        term::emit(buffer, &codespan_config(), &code.files, &diag).unwrap();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unexpected_token_works_for_single_token() {
        let got = crate::lexer::TokenKind::Assignment;
        let expected_list = unexpected_token_list(vec!["=="]);
        let result = unexpected_token_message(&got, &expected_list);
        assert_eq!(result, "Unexpected `=`, expected `==`");
    }

    #[test]
    fn unexpected_token_works_for_multiple_tokens() {
        let got = crate::lexer::TokenKind::Assignment;
        let expected_list = unexpected_token_list(vec!["x", "y", "z"]);
        let result = unexpected_token_message(&got, &expected_list);
        assert_eq!(result, "Unexpected `=`, expected `x`, `y`, or `z`");
    }
}
