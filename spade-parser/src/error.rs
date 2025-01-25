use local_impl::local_impl;
use spade_common::location_info::Loc;
use spade_diagnostics::Diagnostic;
use spade_macros::{IntoDiagnostic, IntoSubdiagnostic};

use crate::{lexer::TokenKind, Token};

pub type Result<T> = std::result::Result<T, Diagnostic>;

#[derive(IntoSubdiagnostic)]
#[diagnostic(suggestion, "Use `{` if you want to add items to this enum variant")]
pub(crate) struct SuggestBraceEnumVariant {
    #[diagnostic(replace, "{")]
    pub open_paren: Loc<()>,
    #[diagnostic(replace, "}")]
    pub close_paren: Loc<()>,
}

#[derive(IntoDiagnostic, Clone)]
#[diagnostic(error, "Expected argument list")]
pub(crate) struct ExpectedArgumentList {
    #[diagnostic(primary, "Expected argument list for this instantiation")]
    pub base_expr: Loc<()>,
    pub next_token: Token,
}

pub fn expected_pipeline_depth(got: &Token) -> Diagnostic {
    let mut diag = Diagnostic::error(
        got.loc(),
        format!("expected pipeline depth, got `{}`", got.kind.as_str()),
    )
    .primary_label("expected pipeline depth here");
    if got.kind != TokenKind::CloseParen {
        diag.add_help("pipeline depth can only be integer constant");
    }
    diag
}

impl ExpectedArgumentList {
    pub fn with_suggestions(self) -> Diagnostic {
        let diag: Diagnostic = self.clone().into();
        // If the next token is any kind of opening paren, we'll try to suggest changing that
        if self.next_token.kind == TokenKind::OpenBrace
            || self.next_token.kind == TokenKind::OpenBracket
        {
            diag.help("Positional argument lists start with`(`.")
                .help("Named argument lists start with `$(`.")
        } else {
            // If not, we'll suggest inserting the argument list after the base expression. We
            // *could* suggest it at the next token, but if the next token is on a new line,
            // that gets confusing
            diag.span_suggest_insert_after(
                "Consider specifying positional arguments",
                self.base_expr,
                "(...)",
            )
            .span_suggest_insert_after("or named arguments", self.base_expr, "$(...)")
        }
    }
}

pub(crate) struct UnexpectedToken {
    pub got: Token,
    pub expected: Vec<&'static str>,
}

impl From<UnexpectedToken> for Diagnostic {
    fn from(e: UnexpectedToken) -> Self {
        // FIXME: derive(IntoDiagnostic) should be able to understand this
        let expected_list = unexpected_token_list(e.expected);
        let message = unexpected_token_message(&e.got.kind, &expected_list);

        Diagnostic::error(e.got.loc(), message).primary_label(format!("expected {expected_list}"))
    }
}

// Error returned by the comma_separated function. Must be explicitly converted
// to the general Error using one of the member methods
#[derive(Debug, Clone)]
pub enum TokenSeparatedError {
    Inner(Diagnostic),
    UnexpectedToken {
        got: Token,
        separator: TokenKind,
        end_tokens: Vec<TokenKind>,
    },
}

pub type CommaSeparatedResult<T> = std::result::Result<T, TokenSeparatedError>;

impl TokenSeparatedError {
    pub fn extra_expected(self, mut extra: Vec<&'static str>) -> Diagnostic {
        match self {
            TokenSeparatedError::Inner(inner) => inner,
            TokenSeparatedError::UnexpectedToken {
                got,
                separator,
                end_tokens,
            } => {
                extra.push(separator.as_str());
                for tok in end_tokens {
                    extra.push(tok.as_str())
                }
                Diagnostic::from(UnexpectedToken {
                    got,
                    expected: extra,
                })
            }
        }
    }

    pub fn no_context(self) -> Diagnostic {
        self.extra_expected(vec![])
    }
}

impl From<Diagnostic> for TokenSeparatedError {
    fn from(value: Diagnostic) -> Self {
        TokenSeparatedError::Inner(value)
    }
}

#[local_impl]
impl<T> CSErrorTransformations for std::result::Result<T, TokenSeparatedError> {
    fn extra_expected(self, extra: Vec<&'static str>) -> Result<T> {
        self.map_err(|e| e.extra_expected(extra))
    }

    fn no_context(self) -> Result<T> {
        self.map_err(|e| e.no_context())
    }
}

pub fn unexpected_token_list<'a>(expected: impl IntoIterator<Item = &'a str>) -> String {
    let expected = expected
        .into_iter()
        .map(|s| format!("`{}`", s))
        .collect::<Vec<_>>();

    let count = expected.len();
    if count == 1 {
        expected[0].to_string()
    } else if count == 2 {
        format!("{} or {}", expected[0], expected[1])
    } else {
        format!(
            "{}, or {}",
            expected[0..(count - 1)].join(", "),
            expected[count - 1]
        )
    }
}

pub fn unexpected_token_message(got: &TokenKind, expected_list: &str) -> String {
    format!("Unexpected `{}`, expected {}", got.as_str(), expected_list,)
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
