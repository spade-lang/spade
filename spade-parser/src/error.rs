use parse_tree_macros::local_impl;
use spade_common::{location_info::Loc, name::Path};
use thiserror::Error;

use crate::{lexer::TokenKind, Token, TypeSpec};

#[derive(Error, Debug, Clone, PartialEq)]
pub enum Error {
    #[error("End of file")]
    Eof,
    #[error("Lexer error at {} in file {}", 1.0, 0)]
    LexerError(usize, codespan::Span),
    #[error("Unexpected token. got {}, expected {expected:?}", got.kind.as_str())]
    UnexpectedToken {
        got: Token,
        expected: Vec<&'static str>,
    },
    #[error("Expected to find a {} to match {friend:?}, got {got:?}", expected.as_str())]
    UnmatchedPair {
        friend: Token,
        expected: TokenKind,
        got: Token,
    },

    #[error("Expected expression, got {got:?}")]
    ExpectedExpression { got: Token },

    #[error("Expected integer literal, got {got:?}")]
    ExpectedIntegerLiteral { got: Token },

    #[error("Only lower bounds equal to 0 are allowed currently, got {got:?}")]
    NonZeroLowerBound { got: Loc<u128> },

    #[error("Integer range has equal lower and upper bound")]
    EqualLowerUpperBound { lower: Loc<u128>, upper: Loc<u128> },

    #[error("Entity missing block for {for_what}")]
    ExpectedBlock {
        for_what: String,
        got: Token,
        loc: Loc<()>,
    },

    #[error("Expected item, got: {got:?}")]
    ExpectedItem { got: Token },

    // Acts mostly like UnexpectedToken but produced by the argument list parser
    // if it encounters the UnexpectedEndOfSCListError, at which point more tokens
    // are added to the returned error. This can not be done to the previous variant
    // as recursive errors of the same kind would then add the token multiple times
    #[error("Unexpected end of argument list")]
    UnexpectedEndOfArgList {
        got: Token,
        expected: Vec<TokenKind>,
    },

    #[error("Expected type, got {0:?}")]
    ExpectedType(Token),

    #[error("Expected argument list for {0}")]
    ExpectedArgumentList(Loc<Path>),

    #[error("Missing tuple index")]
    MissingTupleIndex { hash_loc: Loc<()> },

    #[error("Expected pipeline depth")]
    ExpectedPipelineDepth { got: Token },

    #[error("Expected offset")]
    ExpectedOffset { got: Token },

    #[error("Expected expression or stage")]
    ExpectedExpressionOrStage { got: Token },

    #[error("Empty decl statement")]
    EmptyDeclStatement { at: Loc<()> },

    #[error("Reg in function")]
    RegInFunction { at: Loc<()>, fn_keyword: Loc<()> },
    #[error("Inst in function")]
    InstInFunction { at: Loc<()>, fn_keyword: Loc<()> },
    #[error("Stage references are not allowed in functions")]
    PipelineRefInFunction { at: Loc<()>, fn_keyword: Loc<()> },
    #[error("Stage references are not allowed in entities")]
    PipelineRefInEntity {
        at: Loc<()>,
        entity_keyword: Loc<()>,
    },

    #[error("(Internal) Expected an item context to be set")]
    InternalExpectedItemContext { at: Loc<()> },

    #[error("(Internal) Overwriting item context")]
    InternalOverwritingItemContext { at: Loc<()>, prev: Loc<()> },

    #[error("Expected array size")]
    ExpectedArraySize {
        array: Loc<()>,
        inner: Loc<TypeSpec>,
    },
    #[error("Stages are only allowed in the root of pipelines")]
    StageOutsidePipeline(Loc<()>),
}

impl Error {
    /// If the error is UnexpectedToken, replace it with the type returned by the
    /// provided closure. Otherwise, return the error unaffected
    pub fn specify_unexpected_token(self, f: impl Fn(Token) -> Self) -> Self {
        match self {
            Error::UnexpectedToken { got, .. } => f(got),
            other => other,
        }
    }
}

pub type Result<T> = std::result::Result<T, Error>;

// Error returned by the comma_separated function. Must be explicitly converted
// to the general Error using one of the member methods
#[derive(Error, Debug, Clone)]
pub enum CommaSeparatedError {
    #[error("Inner")]
    Inner(#[from] Error),
    #[error("Unexpected token")]
    UnexpectedToken { got: Token, end_token: TokenKind },
}

pub type CommaSeparatedResult<T> = std::result::Result<T, CommaSeparatedError>;

impl CommaSeparatedError {
    pub fn extra_expected(self, mut extra: Vec<&'static str>) -> Error {
        match self {
            CommaSeparatedError::Inner(inner) => inner,
            CommaSeparatedError::UnexpectedToken { got, end_token } => {
                extra.push(",");
                extra.push(end_token.as_str());
                Error::UnexpectedToken {
                    got,
                    expected: extra,
                }
            }
        }
    }

    pub fn no_context(self) -> Error {
        self.extra_expected(vec![])
    }
}

#[local_impl]
impl<T> CSErrorTransformations for std::result::Result<T, CommaSeparatedError> {
    fn extra_expected(self, extra: Vec<&'static str>) -> Result<T> {
        self.map_err(|e| e.extra_expected(extra))
    }

    fn no_context(self) -> Result<T> {
        self.map_err(|e| e.no_context())
    }
}
