pub mod error;
mod expression;
pub mod item_type;
mod items;
pub mod lexer;
mod statements;

use std::marker::PhantomData;

use colored::*;
use itertools::Itertools;
use local_impl::local_impl;
use logos::Lexer;
use spade_diagnostics::diag_list::{DiagList, ResultExt};
use statements::{AssertParser, BindingParser, DeclParser, LabelParser, RegisterParser, SetParser};
use tracing::{debug, event, Level};

use spade_ast::{
    ArgumentList, ArgumentPattern, Attribute, AttributeList, BitLiteral, Block, CallKind,
    EnumVariant, Expression, Inequality, IntLiteral, Item, ModuleBody, NamedArgument,
    NamedTurbofish, ParameterList, Pattern, PipelineStageReference, Statement, TraitSpec,
    TurbofishInner, TypeExpression, TypeParam, TypeSpec, Unit, UnitHead, UnitKind, WhereClause,
};
use spade_common::location_info::{lspan, AsLabel, FullSpan, HasCodespan, Loc, WithLocation};
use spade_common::name::{Identifier, Path, PathSegment, Visibility};
use spade_common::num_ext::{InfallibleToBigInt, InfallibleToBigUint};
use spade_diagnostics::{diag_bail, Diagnostic};
use spade_macros::trace_parser;

use crate::error::{
    unexpected_token_message, CSErrorTransformations, CommaSeparatedResult, ExpectedArgumentList,
    Result, SuggestBraceEnumVariant, TokenSeparatedError, UnexpectedToken,
};
use crate::item_type::UnitKindLocal;
use crate::lexer::{LiteralKind, TokenKind};

pub use logos;

/// A token with location info
#[derive(Clone, Debug, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: logos::Span,
    pub file_id: usize,
}

impl Token {
    pub fn new(kind: TokenKind, lexer: &Lexer<TokenKind>, file_id: usize) -> Self {
        Self {
            kind,
            span: lexer.span(),
            file_id,
        }
    }

    pub fn loc(&self) -> Loc<()> {
        Loc::new((), self.span.codespan(), self.file_id)
    }
}

impl HasCodespan for Token {
    fn codespan(&self) -> spade_codespan::Span {
        self.span().codespan()
    }
}

impl AsLabel for Token {
    fn file_id(&self) -> usize {
        self.file_id
    }

    fn span(&self) -> std::ops::Range<usize> {
        self.span.clone()
    }
}

impl From<Token> for FullSpan {
    fn from(token: Token) -> FullSpan {
        (token.codespan(), token.file_id)
    }
}

#[derive(Debug, Clone)]
pub enum Comment {
    Line(Token),
    Block(Token, Token),
}

// Clone for when you want to call a parse function but maybe discard the new parser state
// depending on some later condition.
#[derive(Clone)]
pub struct Parser<'a> {
    lex: Lexer<'a, TokenKind>,
    peeked: Option<Token>,
    // The last token that was eaten. Used in eof diagnostics
    last_token: Option<Token>,
    pub parse_stack: Vec<ParseStackEntry>,
    file_id: usize,
    unit_context: Option<Loc<UnitKind>>,
    pub diags: DiagList,
    recovering_tokens: Vec<fn(&TokenKind) -> bool>,
    comments: Vec<Comment>,
}

impl<'a> Parser<'a> {
    pub fn new(lex: Lexer<'a, TokenKind>, file_id: usize) -> Self {
        Self {
            lex,
            peeked: None,
            last_token: None,
            parse_stack: vec![],
            file_id,
            unit_context: None,
            diags: DiagList::new(),
            recovering_tokens: vec![|tok| tok == &TokenKind::Eof],
            comments: vec![],
        }
    }

    pub fn comments(&self) -> &[Comment] {
        &self.comments
    }
}

/// Peek the next token. If it matches the specified token, get that token
/// otherwise return Ok(none)
#[macro_export]
macro_rules! peek_for {
    ($self:expr, $token:expr) => {
        if let Some(t) = $self.peek_and_eat($token)? {
            t
        } else {
            return Ok(None);
        }
    };
}

// Actual parsing functions
impl<'a> Parser<'a> {
    #[trace_parser]
    #[tracing::instrument(level = "trace", skip(self))]
    pub fn identifier(&mut self) -> Result<Loc<Identifier>> {
        let token = self.eat_cond(TokenKind::is_identifier, "Identifier")?;

        if let TokenKind::Identifier(name) = token.kind {
            Ok(name.at(self.file_id, &token.span))
        } else {
            unreachable!("eat_cond should have checked this");
        }
    }

    #[trace_parser]
    pub fn path(&mut self) -> Result<Loc<Path>> {
        let mut result = vec![];
        loop {
            result.push(PathSegment::Named(self.identifier()?));

            if self.peek_and_eat(&TokenKind::PathSeparator)?.is_none() {
                break;
            }
        }
        // NOTE: (safe unwrap) The vec will have at least one element because the first thing
        // in the loop must push an identifier.
        let start = result.first().unwrap().loc();
        let end = result.last().unwrap().loc();
        Ok(Path(result).between_locs(&start, &end))
    }

    #[trace_parser]
    pub fn path_tree_with_as_alias(&mut self) -> Result<Vec<(Loc<Path>, Option<Loc<Identifier>>)>> {
        let mut prefix = Path(vec![]);
        let mut alias = None;

        loop {
            if self.peek_cond(TokenKind::is_identifier, "Identifier")? {
                let ident = self.identifier()?;
                prefix = prefix.push_ident(ident);
            } else if self.peek_and_eat(&TokenKind::OpenBrace)?.is_some() {
                let result = self
                    .comma_separated(Self::path_tree_with_as_alias, &TokenKind::CloseBrace)
                    .no_context()?
                    .into_iter()
                    .flatten()
                    .map(|(p, a)| {
                        let loc = p.loc();
                        let path = prefix.join(p.inner);
                        (path.at_loc(&loc), a)
                    })
                    .collect::<Vec<_>>();
                self.eat(&TokenKind::CloseBrace)?;
                return Ok(result);
            } else {
                let next = self.peek()?;
                return Err(UnexpectedToken {
                    got: next,
                    expected: vec!["identifier", "{", "::"],
                }
                .into());
            }

            if self.peek_and_eat(&TokenKind::As)?.is_some() {
                alias = Some(self.identifier()?);
                break;
            } else if self.peek_and_eat(&TokenKind::PathSeparator)?.is_none() {
                break;
            }
        }

        let start = prefix.0.first().unwrap().loc();
        let end = prefix.0.last().unwrap().loc();
        return Ok(vec![(prefix.between_locs(&start, &end), alias)]);
    }

    pub fn named_turbofish(&mut self) -> Result<Loc<NamedTurbofish>> {
        // This is a named arg
        let name = self.identifier()?;
        if self.peek_and_eat(&TokenKind::Colon)?.is_some() {
            let value = self.type_expression()?;

            let span = name.span.merge(value.span);

            Ok(NamedTurbofish::Full(name, value).at(self.file_id, &span))
        } else {
            Ok(NamedTurbofish::Short(name.clone()).at(self.file_id, &name))
        }
    }

    #[trace_parser]
    pub fn turbofish(&mut self) -> Result<Option<Loc<TurbofishInner>>> {
        let start = peek_for!(self, &TokenKind::PathSeparator);

        if self.peek_kind(&TokenKind::Lt)? {
            // safe unwrap, only None for token kind != Lt
            let params = self.generic_spec_list()?.unwrap();

            Ok(Some(params.map(|p| TurbofishInner::Positional(p))))
        } else if self.peek_kind(&TokenKind::Dollar)? {
            self.eat_unconditional()?;
            let (params, loc) = self.surrounded(
                &TokenKind::Lt,
                |s| {
                    s.comma_separated(Self::named_turbofish, &TokenKind::Gt)
                        .extra_expected(vec!["identifier", "type spec"])
                },
                &TokenKind::Gt,
            )?;

            Ok(Some(TurbofishInner::Named(params).at_loc(&loc)))
        } else {
            let next = self.peek()?;
            return Err(Diagnostic::error(next, "Expected $ or <")
                .primary_label("Expected $ or <")
                .secondary_label(
                    start,
                    ":: after an method is used to specify type parameters",
                ));
        }
    }

    #[trace_parser]
    pub fn path_with_turbofish(
        &mut self,
    ) -> Result<Option<(Loc<Path>, Option<Loc<TurbofishInner>>)>> {
        let mut result = vec![];
        if !self.peek_cond(TokenKind::is_identifier, "Identifier")? {
            return Ok(None);
        }

        loop {
            result.push(PathSegment::Named(self.identifier()?));

            // NOTE: (safe unwrap) The vec will have at least one element because the first thing
            // in the loop must push an identifier.
            let path_start = result.first().unwrap().loc();
            let path_end = result.last().unwrap().loc();

            if self.peek_and_eat(&TokenKind::PathSeparator)?.is_none() {
                break Ok(Some((
                    Path(result).between_locs(&path_start, &path_end),
                    None,
                )));
            } else if self.peek_kind(&TokenKind::Lt)? {
                // safe unwrap, only None for token kind != Lt
                let params = self.generic_spec_list()?.unwrap();

                break Ok(Some((
                    Path(result).between(self.file_id, &path_start, &path_end),
                    Some(params.map(|p| TurbofishInner::Positional(p))),
                )));
            } else if self.peek_kind(&TokenKind::Dollar)? {
                self.eat_unconditional()?;
                let (params, loc) = self.surrounded(
                    &TokenKind::Lt,
                    |s| {
                        s.comma_separated(Self::named_turbofish, &TokenKind::Gt)
                            .extra_expected(vec!["identifier", "type spec"])
                    },
                    &TokenKind::Gt,
                )?;

                break Ok(Some((
                    Path(result).between(self.file_id, &path_start, &path_end),
                    Some(TurbofishInner::Named(params).at_loc(&loc)),
                )));
            }
        }
    }

    #[trace_parser]
    fn array_label(&mut self) -> Result<Option<Loc<Identifier>>> {
        if let ref tok @ Token {
            kind: TokenKind::Label(l),
            ..
        } = self.peek()?
        {
            self.eat_unconditional()?;
            Ok(Some(l.at(self.file_id, tok)))
        } else {
            Ok(None)
        }
    }

    #[trace_parser]
    fn array_literal(&mut self) -> Result<Option<Loc<Expression>>> {
        let start = peek_for!(self, &TokenKind::OpenBracket);

        // empty array
        if let Some(end) = self.peek_and_eat(&TokenKind::CloseBracket)? {
            return Ok(Some(Expression::ArrayLiteral(vec![]).between(
                self.file_id,
                &start,
                &end,
            )));
        }

        // non-empty array => must be an expression
        let first_label = self.array_label()?;
        let first = self.expression()?;

        let expr = if self.peek_and_eat(&TokenKind::Semi).unwrap().is_some() {
            // array shorthand ([<expr>; N])
            Expression::ArrayShorthandLiteral(Box::new(first), Box::new(self.expression()?))
        } else {
            // eat comma, if any
            let _ = self.peek_and_eat(&TokenKind::Comma)?;

            // now we can continue with the rest of the elements
            let mut inner = self
                .comma_separated(
                    |s| Ok((s.array_label()?, s.expression()?)),
                    &TokenKind::CloseBracket,
                )
                .no_context()?;
            inner.insert(0, (first_label, first));
            Expression::ArrayLiteral(inner)
        };

        let end = self.eat(&TokenKind::CloseBracket)?;

        Ok(Some(expr.between(self.file_id, &start, &end)))
    }

    fn map_escape_char(c: Loc<char>, string_delimiter: char) -> Result<char> {
        match c.inner {
            '0' => Ok('\0'),
            't' => Ok('\t'),
            'n' => Ok('\n'),
            'r' => Ok('\r'),
            other if other == string_delimiter => Ok(string_delimiter),
            other => Err(Diagnostic::error(
                c.loc(),
                format!("{} is not a valid byte escape character", other),
            )),
        }
    }

    fn ascii_string_literal(&mut self) -> Result<Option<Loc<Expression>>> {
        let next = self.peek()?;
        let TokenKind::AsciiStringLiteral(val) = &next.kind else {
            return Ok(None);
        };

        self.eat_unconditional()?;

        let mut escape_next = false;
        let array_elements = val
            .char_indices()
            .map(|(i, c)| {
                // +1 because the token starts with b"
                let span = (next.span.start + i + 2)..(next.span.start + i + 2 + c.len_utf8());
                let loc = ().at(self.file_id, &span);
                if !c.is_ascii() {
                    return Err(Diagnostic::error(
                        loc,
                        "ASCII literals can only contain ASCII value, not unicode",
                    )
                    .primary_label("Unicode character in ASCII literal"));
                }

                let result;
                (escape_next, result) = match (escape_next, c) {
                    (false, '\\') => (true, None),
                    (true, esc) => (false, Some(Self::map_escape_char(esc.at_loc(&loc), '"')?)),
                    (_, other) => (false, Some(other)),
                };
                Ok(result.map(|c| c.at_loc(&loc)))
            })
            .collect::<Result<Vec<_>>>()?;

        let elems = array_elements
            .iter()
            .filter_map(|maybe_loc_c| {
                maybe_loc_c.map(|loc_c| {
                    let mut byte = [0; 1];
                    loc_c.inner.encode_utf8(&mut byte);
                    (
                        None,
                        Expression::IntLiteral(
                            IntLiteral::Unsigned {
                                val: byte[0].to_biguint(),
                                size: 8u32.to_biguint(),
                            }
                            .at_loc(&loc_c),
                        )
                        .at_loc(&loc_c),
                    )
                })
            })
            .collect();
        Ok(Some(
            Expression::ArrayLiteral(elems).at(self.file_id, &next),
        ))
    }

    #[trace_parser]
    fn ascii_char_literal(&mut self) -> Result<Option<Loc<IntLiteral>>> {
        let next = self.peek()?;
        if let TokenKind::Utf8CharLiteral = &next.kind {
            return Err(
                Diagnostic::error(&next.loc(), "Unicode char literals are unsupported.")
                    .primary_label("Unicode char literal")
                    .span_suggest_insert_before("Consider making this an ASCII literal", next.loc(), "b")
                    .help("The `b` prefix is used to denote ASCII literals as opposed to full Unicode"),
            );
        }
        let TokenKind::AsciiCharLiteral(val) = &next.kind else {
            return Ok(None);
        };
        self.eat_unconditional()?;

        if !val.is_ascii() {
            return Err(Diagnostic::error(
                next.loc(),
                "ASCII literals can only be ASCII values, not Unicode",
            ));
        }

        let actual_char = if val.len() == 2 && val.starts_with('\\') {
            Self::map_escape_char(
                val.chars().skip(1).next().unwrap().at_loc(&next.loc()),
                '\'',
            )?
        } else if val.len() > 1 {
            return Err(Diagnostic::error(
                next,
                "Only a single character is supported in ASCII char literals.",
            ));
        } else if val.len() == 1 {
            val.chars().next().unwrap()
        } else {
            return Err(Diagnostic::bug(next.loc(), "Found an empty char literal"));
        };

        let mut byte = [0; 1];
        actual_char.encode_utf8(&mut byte);
        Ok(Some(
            IntLiteral::Unsigned {
                val: byte[0].to_biguint(),
                size: 8u32.to_biguint(),
            }
            .at(self.file_id, &next),
        ))
    }

    #[trace_parser]
    fn tuple_literal(&mut self) -> Result<Option<Loc<Expression>>> {
        let start = peek_for!(self, &TokenKind::OpenParen);
        if self.peek_kind(&TokenKind::CloseParen)? {
            return Ok(Some(Expression::TupleLiteral(vec![]).between(
                self.file_id,
                &start,
                &self.eat_unconditional()?,
            )));
        }
        if let Some(_) = self.peek_and_eat(&TokenKind::Comma)? {
            let closer = self.eat(&TokenKind::CloseParen)?;
            return Ok(Some(Expression::TupleLiteral(vec![]).between(
                self.file_id,
                &start,
                &closer,
            )));
        }

        let first = self.expression()?;
        let first_sep = self.eat_unconditional()?;

        match &first_sep.kind {
            TokenKind::CloseParen => {
                let inner = first.inner.between(self.file_id, &start, &first_sep);
                Ok(Some(Expression::Parenthesized(Box::new(inner)).between(
                    self.file_id,
                    &start,
                    &first_sep,
                )))
            }
            TokenKind::Comma => {
                let rest = self
                    .comma_separated(Self::expression, &TokenKind::CloseParen)
                    .no_context()?;

                let end = self.eat(&TokenKind::CloseParen)?;

                Ok(Some(
                    Expression::TupleLiteral(vec![first].into_iter().chain(rest).collect())
                        .between(self.file_id, &start, &end),
                ))
            }
            _ => Err(UnexpectedToken {
                got: first_sep,
                expected: vec!["expression", ",", ")"],
            }
            .into()),
        }
    }

    #[trace_parser]
    #[tracing::instrument(skip(self))]
    fn entity_instance(&mut self) -> Result<Option<Loc<Expression>>> {
        let start = peek_for!(self, &TokenKind::Instance);
        let start_loc = ().at(self.file_id, &start);

        // inst is only allowed in entity/pipeline, so check that we are in one of those
        self.unit_context
            .allows_inst(().at(self.file_id, &start.span()))?;

        // Check if this is a pipeline or not
        let pipeline_depth = if self.peek_kind(&TokenKind::OpenParen)? {
            Some(self.surrounded(
                &TokenKind::OpenParen,
                |s| s.type_expression(),
                &TokenKind::CloseParen,
            )?)
        } else {
            None
        };

        let peeked = self.peek()?;
        let (name, turbofish) = self.path_with_turbofish()?.ok_or_else(|| {
            Diagnostic::from(UnexpectedToken {
                got: peeked,
                expected: vec!["identifier", "pipeline depth"],
            })
        })?;
        let next_token = self.peek()?;

        let args = self.argument_list()?.ok_or_else(|| {
            ExpectedArgumentList {
                next_token,
                base_expr: ().between(self.file_id, &start, &name),
            }
            .with_suggestions()
        })?;

        if let Some((depth, end_paren)) = pipeline_depth {
            Ok(Some(
                Expression::Call {
                    kind: CallKind::Pipeline(
                        ().between(self.file_id, &start_loc, &end_paren),
                        depth,
                    ),
                    callee: name,
                    args: args.clone(),
                    turbofish,
                }
                .between(self.file_id, &start.span, &args),
            ))
        } else {
            Ok(Some(
                Expression::Call {
                    kind: CallKind::Entity(start_loc),
                    callee: name,
                    args: args.clone(),
                    turbofish,
                }
                .between(self.file_id, &start.span, &args),
            ))
        }
    }

    // FIXME: Before changing this, merge it with type_level_if
    #[trace_parser]
    #[tracing::instrument(skip(self))]
    pub fn if_expression(
        &mut self,
        allow_stages: bool,
        allow_let: bool,
    ) -> Result<Option<Loc<Expression>>> {
        let start = peek_for!(self, &TokenKind::If);

        let let_pattern = if allow_let && self.peek_and_eat(&TokenKind::Let)?.is_some() {
            let pat = self.pattern()?;
            self.eat(&TokenKind::Assignment)?;
            Some(pat)
        } else {
            None
        };

        let cond = self.expression()?;

        let on_true = if let Some(block) = self.block(allow_stages)? {
            block.map(Box::new).map(Expression::Block)
        } else {
            let got = self.peek()?;
            return Err(Diagnostic::error(
                got.loc(),
                format!("Unexpected `{}`, expected a block", got.kind.as_str()),
            )
            .primary_label("expected a block here"));
        };

        self.eat(&TokenKind::Else)?;
        let on_false = if let Some(block) = self.block(allow_stages)? {
            block.map(Box::new).map(Expression::Block)
        } else if let Some(expr) = self.if_expression(allow_stages, allow_let)? {
            expr
        } else {
            let got = self.peek()?;
            return Err(Diagnostic::error(
                got.loc(),
                format!(
                    "Unexpected `{}`, expected `if` or a block",
                    got.kind.as_str()
                ),
            )
            .primary_label("expected a block here"));
        };
        let end_span = on_false.span;

        match let_pattern {
            None => Ok(Some(
                Expression::If(Box::new(cond), Box::new(on_true), Box::new(on_false)).between(
                    self.file_id,
                    &start.span,
                    &end_span,
                ),
            )),
            Some(pat) => Ok(Some(
                Expression::Match {
                    expression: Box::new(cond),
                    branches: vec![
                        (pat, None, on_true),
                        (
                            Pattern::Path(Path::from_strs(&["_"]).nowhere()).nowhere(),
                            None,
                            on_false,
                        ),
                    ]
                    .nowhere(),
                    if_let: true,
                }
                .between(self.file_id, &start.span, &end_span),
            )),
        }
    }

    // FIXME: Before changing this, merge it with if_expression
    pub fn type_level_if(&mut self) -> Result<Option<Loc<Expression>>> {
        let start = peek_for!(self, &TokenKind::Gen);

        let Some(inner) = self.if_expression(true, false)? else {
            return Err(
                Diagnostic::error(self.peek()?, "gen must be followed by if")
                    .primary_label("Expected if")
                    .secondary_label(start, "Because of this gen"),
            );
        };
        let end_span = inner.loc();
        let Expression::If(cond, on_true, on_false) = inner.inner else {
            diag_bail!(inner, "if_expression did not return an if")
        };

        let on_false = match &on_false.inner {
            Expression::If(cond, on_true, on_false) => Box::new(
                Expression::TypeLevelIf(cond.clone(), on_true.clone(), on_false.clone())
                    .at_loc(&on_false),
            ),
            _ => on_false,
        };

        Ok(Some(
            Expression::TypeLevelIf(cond, on_true, on_false).between(
                self.file_id,
                &start.span,
                &end_span,
            ),
        ))
    }

    #[trace_parser]
    pub fn match_expression(&mut self) -> Result<Option<Loc<Expression>>> {
        let start = peek_for!(self, &TokenKind::Match);

        let expression = self.expression()?;

        let (patterns, body_loc) = self.surrounded(
            &TokenKind::OpenBrace,
            |s| {
                s.comma_separated(
                    |s| {
                        let pattern = s.pattern()?;
                        let if_condition = if s.peek_kind(&TokenKind::If)? {
                            s.eat_unconditional()?;
                            Some(s.expression()?)
                        } else {
                            None
                        };
                        s.eat(&TokenKind::FatArrow)?;
                        let value = s.expression()?;

                        Ok((pattern, if_condition, value))
                    },
                    &TokenKind::CloseBrace,
                )
                .no_context()
            },
            &TokenKind::CloseBrace,
        )?;
        let patterns = patterns.at_loc(&body_loc);

        Ok(Some(
            Expression::Match {
                expression: Box::new(expression),
                branches: patterns,
                if_let: false,
            }
            .between(self.file_id, &start.span, &body_loc),
        ))
    }

    #[trace_parser]
    pub fn unsafe_block(&mut self) -> Result<Option<Loc<Expression>>> {
        let start = peek_for!(self, &TokenKind::Unsafe);

        let Some(block) = self.block(false)? else {
            let got = self.peek()?;
            return Err(Diagnostic::error(
                got.loc(),
                format!("Unexpected `{}`, expected a block", got.kind.as_str()),
            )
            .primary_label("expected a block here"));
        };

        let block_loc = block.loc();
        Ok(Some(Expression::Unsafe(Box::new(block)).between(
            self.file_id,
            &start.span,
            &block_loc,
        )))
    }

    #[trace_parser]
    #[tracing::instrument(skip(self))]
    pub fn int_literal(&mut self) -> Result<Option<Loc<IntLiteral>>> {
        let plusminus = match &self.peek()?.kind {
            TokenKind::Plus | TokenKind::Minus => Some(self.eat_unconditional()?),
            _ => None,
        };
        if self.peek_cond(TokenKind::is_integer, "integer")? {
            let token = self.eat_unconditional()?;
            match &token.kind {
                TokenKind::Integer(val)
                | TokenKind::HexInteger(val)
                | TokenKind::BinInteger(val) => {
                    let (val_int, val_signed) = val;

                    let signed_val = || {
                        if plusminus.as_ref().map(|tok| &tok.kind) == Some(&TokenKind::Minus) {
                            -val_int.to_bigint()
                        } else {
                            val_int.to_bigint()
                        }
                    };

                    let inner = match val_signed {
                        LiteralKind::Signed(size) => IntLiteral::Signed {
                            val: signed_val(),
                            size: size.clone(),
                        },
                        LiteralKind::Unsized => IntLiteral::Unsized(signed_val()),
                        LiteralKind::Unsigned(size) => IntLiteral::Unsigned {
                            val: val_int.clone(),
                            size: size.clone(),
                        },
                    };
                    let loc = if let Some(pm) = plusminus {
                        ().between(self.file_id, &pm, &token)
                    } else {
                        token.loc()
                    };
                    Ok(Some(inner.at_loc(&loc)))
                }
                _ => unreachable!(),
            }
        } else if let Some(pm) = plusminus {
            Err(Diagnostic::error(
                pm.loc(),
                format!("expected a number after '{}'", pm.kind.as_str()),
            ))
        } else {
            Ok(None)
        }
    }

    #[trace_parser]
    fn bool_literal(&mut self) -> Result<Option<Loc<bool>>> {
        if let Some(tok) = self.peek_and_eat(&TokenKind::True)? {
            Ok(Some(true.at(self.file_id, &tok.span)))
        } else if let Some(tok) = self.peek_and_eat(&TokenKind::False)? {
            Ok(Some(false.at(self.file_id, &tok.span)))
        } else {
            Ok(None)
        }
    }

    #[trace_parser]
    fn str_literal(&mut self) -> Result<Option<Loc<String>>> {
        if self.peek_cond(TokenKind::is_string, "string")? {
            let token = self.eat_unconditional()?;
            match &token.kind {
                TokenKind::String(val) => Ok(Some(val.clone().at_loc(&token.loc()))),
                _ => unreachable!(),
            }
        } else {
            Ok(None)
        }
    }

    #[trace_parser]
    fn tri_literal(&mut self) -> Result<Option<Loc<BitLiteral>>> {
        if let Some(tok) = self.peek_and_eat(&TokenKind::Low)? {
            Ok(Some(BitLiteral::Low.at(self.file_id, &tok.span)))
        } else if let Some(tok) = self.peek_and_eat(&TokenKind::High)? {
            Ok(Some(BitLiteral::High.at(self.file_id, &tok.span)))
        } else if let Some(tok) = self.peek_and_eat(&TokenKind::HighImp)? {
            Ok(Some(BitLiteral::HighImp.at(self.file_id, &tok.span)))
        } else {
            Ok(None)
        }
    }

    #[trace_parser]
    #[tracing::instrument(skip(self))]
    pub fn block(&mut self, is_pipeline: bool) -> Result<Option<Loc<Block>>> {
        let start = peek_for!(self, &TokenKind::OpenBrace);

        let (statements, result) = self.statements(is_pipeline)?;

        let end = self.eat(&TokenKind::CloseBrace)?;

        Ok(Some(Block { statements, result }.between(
            self.file_id,
            &start.span,
            &end.span,
        )))
    }

    pub fn label_access(&mut self) -> Result<Option<Loc<Expression>>> {
        if let ref tok @ Token {
            kind: TokenKind::LabelRef(l),
            ..
        } = self.peek()?
        {
            self.eat_unconditional()?;
            self.eat(&TokenKind::Dot)?;

            let field = self.identifier()?;

            let loc = ().between(self.file_id, tok, &field);
            Ok(Some(
                Expression::LabelAccess {
                    label: Path::ident(l.at(self.file_id, tok)).at(self.file_id, tok),
                    field,
                }
                .at_loc(&loc),
            ))
        } else {
            Ok(None)
        }
    }

    #[trace_parser]
    pub fn pipeline_reference(&mut self) -> Result<Option<Loc<Expression>>> {
        let start = peek_for!(self, &TokenKind::Stage);
        // Peek here because we can't peek in the .ok_or_else below
        let next = self.peek()?;

        let parsed = self.first_successful(vec![
            &|s: &mut Self| s.pipeline_stage_reference(&start),
            &|s: &mut Self| s.pipeline_stage_status(&start),
        ])?;
        match parsed {
            Some(e) => Ok(Some(e)),
            None => Err(Diagnostic::from(UnexpectedToken {
                got: next,
                expected: vec![".", "("],
            })),
        }
    }

    #[trace_parser]
    pub fn pipeline_stage_reference(
        &mut self,
        stage_keyword: &Token,
    ) -> Result<Option<Loc<Expression>>> {
        peek_for!(self, &TokenKind::OpenParen);

        self.unit_context.allows_pipeline_ref(stage_keyword.loc())?;

        let next = self.peek()?;
        let reference = match next.kind {
            TokenKind::Plus => {
                let start = self.eat_unconditional()?;
                let offset = self.expression()?;
                let result = PipelineStageReference::Relative(
                    TypeExpression::ConstGeneric(Box::new(offset.clone())).between(
                        self.file_id,
                        &start,
                        &offset,
                    ),
                );
                result
            }
            TokenKind::Minus => {
                let start = self.eat_unconditional()?;
                let offset = self.expression()?;
                let texpr = TypeExpression::ConstGeneric(Box::new(
                    Expression::UnaryOperator(
                        spade_ast::UnaryOperator::Sub.at(self.file_id, &next.span),
                        Box::new(offset.clone()),
                    )
                    .between(self.file_id, &start, &offset),
                ))
                .between(self.file_id, &start, &offset);
                PipelineStageReference::Relative(texpr)
            }
            TokenKind::Identifier(_) => PipelineStageReference::Absolute(self.identifier()?),
            _ => {
                return Err(Diagnostic::from(UnexpectedToken {
                    got: next,
                    expected: vec!["+", "-", "identifier"],
                }));
            }
        };

        let close_paren = self.eat(&TokenKind::CloseParen)?;

        self.eat(&TokenKind::Dot)?;

        let ident = self.identifier()?;

        Ok(Some(
            Expression::PipelineReference {
                stage_kw_and_reference_loc: ().between(
                    self.file_id,
                    &stage_keyword.span,
                    &close_paren.span,
                ),
                stage: reference,
                name: ident.clone(),
            }
            .between(self.file_id, &stage_keyword.span, &ident),
        ))
    }

    #[trace_parser]
    pub fn pipeline_stage_status(
        &mut self,
        stage_keyword: &Token,
    ) -> Result<Option<Loc<Expression>>> {
        peek_for!(self, &TokenKind::Dot);

        let ident = self.identifier()?;

        match ident.inner.as_str() {
            "valid" => Ok(Some(Expression::StageValid.between(
                self.file_id,
                stage_keyword,
                &ident,
            ))),
            "ready" => Ok(Some(Expression::StageReady.between(
                self.file_id,
                stage_keyword,
                &ident,
            ))),
            other => Err(Diagnostic::error(
                &ident,
                format!("Expected `ready` or `valid`, got `{other}`"),
            )
            .primary_label("Expected `ready` or `valid`")),
        }
    }

    #[trace_parser]
    fn argument_list(&mut self) -> Result<Option<Loc<ArgumentList>>> {
        let is_named = self.peek_and_eat(&TokenKind::Dollar)?.is_some();
        let opener = peek_for!(self, &TokenKind::OpenParen);

        let argument_list = if is_named {
            let args = self
                .comma_separated(Self::named_argument, &TokenKind::CloseParen)
                .extra_expected(vec![":"])
                .map_err(|e| {
                    debug!("check named arguments =");
                    let Ok(tok) = self.peek() else {
                        return e;
                    };
                    debug!("{:?}", tok);
                    if tok.kind == TokenKind::Assignment {
                        e.span_suggest_replace(
                            "named arguments are specified with `:`",
                            // FIXME: expand into whitespace
                            // lifeguard: spade#309
                            tok.loc(),
                            ":",
                        )
                    } else {
                        e
                    }
                })?
                .into_iter()
                .map(Loc::strip)
                .collect();
            ArgumentList::Named(args)
        } else {
            let args = self
                .comma_separated(Self::expression, &TokenKind::CloseParen)
                .no_context()?;

            ArgumentList::Positional(args)
        };
        let end = self.eat(&TokenKind::CloseParen)?;
        let span = lspan(opener.span).merge(lspan(end.span));
        Ok(Some(argument_list.at(self.file_id, &span)))
    }
    #[trace_parser]
    fn named_argument(&mut self) -> Result<Loc<NamedArgument>> {
        // This is a named arg
        let name = self.identifier()?;
        if self.peek_and_eat(&TokenKind::Colon)?.is_some() {
            let value = self.expression()?;

            let span = name.span.merge(value.span);

            Ok(NamedArgument::Full(name, value).at(self.file_id, &span))
        } else {
            Ok(NamedArgument::Short(name.clone()).at(self.file_id, &name))
        }
    }

    #[trace_parser]
    pub fn type_expression(&mut self) -> Result<Loc<TypeExpression>> {
        if let Some(val) = self.int_literal()? {
            Ok(TypeExpression::Integer(val.inner.clone().as_signed()).at_loc(&val))
        } else if let Some(val) = self.str_literal()? {
            Ok(TypeExpression::String(val.inner.clone()).at_loc(&val))
        } else if self.peek_kind(&TokenKind::OpenBrace)? {
            let (expr, span) = self.surrounded(
                &TokenKind::OpenBrace,
                |s| s.expression(),
                &TokenKind::CloseBrace,
            )?;
            Ok(TypeExpression::ConstGeneric(Box::new(expr)).at(self.file_id, &span))
        } else {
            let inner = self.type_spec(false)?;

            Ok(TypeExpression::TypeSpec(Box::new(inner.clone())).at_loc(&inner))
        }
    }

    // Types
    #[trace_parser]
    pub fn type_spec(&mut self, accept_impl: bool) -> Result<Loc<TypeSpec>> {
        if let Some(inv) = self.peek_and_eat(&TokenKind::Inv)? {
            let rest = self.type_expression()?;
            Ok(TypeSpec::Inverted(Box::new(rest.clone())).between(self.file_id, &inv, &rest))
        } else if let Some(tilde) = self.peek_and_eat(&TokenKind::Tilde)? {
            return Err(Diagnostic::error(
                tilde.clone(),
                "The syntax for inverted ports has changed from ~ to inv",
            )
            .primary_label("~ cannot be used in a type")
            .span_suggest("Consider using inv", tilde, "inv "));
        } else if let Some(wire_sign) = self.peek_and_eat(&TokenKind::Ampersand)? {
            if let Some(mut_) = self.peek_and_eat(&TokenKind::Mut)? {
                return Err(Diagnostic::error(
                    &().at(self.file_id, &mut_),
                    "The syntax of &mut has changed to inv &",
                )
                .primary_label("&mut is now written as inv &")
                .span_suggest_replace(
                    "Consider using inv &",
                    ().between(self.file_id, &wire_sign, &mut_),
                    "inv &",
                ));
            }

            let rest = self.type_expression()?;
            Ok(TypeSpec::Wire(Box::new(rest.clone())).between(self.file_id, &wire_sign, &rest))
        } else if let Some(r#impl) = self.peek_and_eat(&TokenKind::Impl)? {
            let traits = self
                .token_separated(
                    Self::trait_spec,
                    &TokenKind::Plus,
                    vec![
                        TokenKind::Assignment,
                        TokenKind::Comma,
                        TokenKind::CloseBrace,
                        TokenKind::CloseParen,
                        TokenKind::Gt,
                        TokenKind::OpenBrace,
                    ],
                )
                .extra_expected(vec!["identifier"])?
                .into_iter()
                .map(|spec| {
                    let loc = ().at_loc(&spec.path);
                    spec.at_loc(&loc)
                })
                .collect::<Vec<_>>();

            let span_end = traits.last().map(|t| t.span).unwrap_or(r#impl.loc().span);

            if !accept_impl {
                return Err(Diagnostic::error(
                    ().between(self.file_id, &r#impl, &span_end),
                    "`impl Trait` syntax cannot be used in this context",
                )
                .primary_label("`impl Trait` type cannot be used in this context")
                .note("`impl Trait` can only be used inside unit parameters"));
            }

            Ok(TypeSpec::Impl(traits).between(self.file_id, &r#impl, &span_end))
        } else if let Some(tuple) = self.tuple_spec()? {
            Ok(tuple)
        } else if let Some(array) = self.array_spec()? {
            Ok(array)
        } else {
            if !self.peek_cond(TokenKind::is_identifier, "Identifier")? {
                return Err(Diagnostic::from(UnexpectedToken {
                    got: self.peek()?,
                    expected: vec!["type"],
                }));
            }
            // Single type, maybe with generics
            let (path, span) = self.path()?.separate();

            if path.to_named_strs().as_slice() == [Some("_")] {
                return Ok(TypeSpec::Wildcard.at(self.file_id, &span));
            }

            // Check if this type has generic params
            let generics = if self.peek_kind(&TokenKind::Lt)? {
                let generic_start = self.eat_unconditional()?;
                let type_exprs = self
                    .comma_separated(Self::type_expression, &TokenKind::Gt)
                    .extra_expected(vec!["type expression"])?;
                let generic_end = self.eat(&TokenKind::Gt)?;
                Some(type_exprs.between(self.file_id, &generic_start.span, &generic_end.span))
            } else {
                None
            };

            let span_end = generics.as_ref().map(|g| g.span).unwrap_or(span);
            Ok(TypeSpec::Named(path, generics).between(self.file_id, &span, &span_end))
        }
    }

    #[trace_parser]
    pub fn tuple_spec(&mut self) -> Result<Option<Loc<TypeSpec>>> {
        let start = peek_for!(self, &TokenKind::OpenParen);
        if let Some(_) = self.peek_and_eat(&TokenKind::Comma)? {
            let closer = self.eat(&TokenKind::CloseParen)?;
            return Ok(Some(TypeSpec::Tuple(vec![]).between(
                self.file_id,
                &start,
                &closer,
            )));
        }

        let inner = self
            .comma_separated(Self::type_expression, &TokenKind::CloseParen)
            .no_context()?;
        let end = self.eat(&TokenKind::CloseParen)?;

        let span = lspan(start.span).merge(lspan(end.span));

        Ok(Some(TypeSpec::Tuple(inner).at(self.file_id, &span)))
    }

    #[trace_parser]
    pub fn array_spec(&mut self) -> Result<Option<Loc<TypeSpec>>> {
        let start = peek_for!(self, &TokenKind::OpenBracket);

        let inner = self.type_expression()?;

        if let Some(end) = self.peek_and_eat(&TokenKind::CloseBracket)? {
            return Err(Diagnostic::error(
                ().between_locs(&start.loc(), &end.loc()),
                "missing array size",
            )
            .primary_label("missing size for this array type")
            .note("array types need a specified size")
            .span_suggest_insert_before("insert a size here", end, "; /* N */"));
        }

        self.eat(&TokenKind::Semi)?;

        let size = self.type_expression()?;

        let end = self.eat(&TokenKind::CloseBracket)?;

        Ok(Some(
            TypeSpec::Array {
                inner: Box::new(inner),
                size: Box::new(size),
            }
            .between(self.file_id, &start, &end),
        ))
    }

    /// A name with an associated type, as used in argument definitions as well
    /// as struct definitions
    ///
    /// name: Type
    #[trace_parser]
    pub fn name_and_type(&mut self, accept_impl: bool) -> Result<(Loc<Identifier>, Loc<TypeSpec>)> {
        let name = self.identifier()?;
        self.eat(&TokenKind::Colon)?;
        let t = self.type_spec(accept_impl)?;
        Ok((name, t))
    }

    #[trace_parser]
    pub fn pattern(&mut self) -> Result<Loc<Pattern>> {
        let result = self.first_successful(vec![
            &|s| {
                let start = peek_for!(s, &TokenKind::OpenParen);
                let inner = s
                    .comma_separated(Self::pattern, &TokenKind::CloseParen)
                    .no_context()?;
                let end = s.eat(&TokenKind::CloseParen)?;

                Ok(Some(Pattern::Tuple(inner).between(
                    s.file_id,
                    &start.span,
                    &end.span,
                )))
            },
            &|s| {
                let start = peek_for!(s, &TokenKind::OpenBracket);
                let inner = s
                    .comma_separated(Self::pattern, &TokenKind::CloseBracket)
                    .no_context()?;
                let end = s.eat(&TokenKind::CloseBracket)?;
                Ok(Some(Pattern::Array(inner).between(
                    s.file_id,
                    &start.span,
                    &end.span,
                )))
            },
            &|s| {
                Ok(s.int_literal()?
                    // Map option, then map Loc
                    .map(|val| val.map(Pattern::Integer)))
            },
            &|s| {
                Ok(s.bool_literal()?
                    // Map option, then map Loc
                    .map(|val| val.map(Pattern::Bool)))
            },
            &|s| Ok(s.ascii_char_literal()?.map(|val| val.map(Pattern::Integer))),
            &|s| {
                let path = s.path()?;
                let path_span = path.span;

                if let Some(start_paren) = s.peek_and_eat(&TokenKind::OpenParen)? {
                    let inner = s
                        .comma_separated(Self::pattern, &TokenKind::CloseParen)
                        .no_context()?;
                    let end_paren = s.eat(&TokenKind::CloseParen)?;

                    Ok(Some(
                        Pattern::Type(
                            path,
                            ArgumentPattern::Positional(inner).between(
                                s.file_id,
                                &start_paren.span,
                                &end_paren.span,
                            ),
                        )
                        .between(s.file_id, &path_span, &end_paren.span),
                    ))
                } else if let Some(start_brace) = s.peek_and_eat(&TokenKind::Dollar)? {
                    s.eat(&TokenKind::OpenParen)?;
                    let inner_parser = |s: &mut Self| {
                        let lhs = s.identifier()?;
                        let rhs = if s.peek_and_eat(&TokenKind::Colon)?.is_some() {
                            Some(s.pattern()?)
                        } else {
                            None
                        };

                        Ok((lhs, rhs))
                    };
                    let inner = s
                        .comma_separated(inner_parser, &TokenKind::CloseParen)
                        .extra_expected(vec![":"])?;
                    let end_brace = s.eat(&TokenKind::CloseParen)?;

                    Ok(Some(
                        Pattern::Type(
                            path,
                            ArgumentPattern::Named(inner).between(
                                s.file_id,
                                &start_brace.span,
                                &end_brace.span,
                            ),
                        )
                        .between(s.file_id, &path_span, &end_brace.span),
                    ))
                } else {
                    Ok(Some(Pattern::Path(path.clone()).at(s.file_id, &path)))
                }
            },
        ])?;

        if let Some(result) = result {
            Ok(result)
        } else {
            Err(Diagnostic::from(UnexpectedToken {
                got: self.eat_unconditional()?,
                expected: vec!["Pattern"],
            }))
        }
    }

    #[trace_parser]
    pub fn statements(
        &mut self,
        allow_stages: bool,
    ) -> Result<(Vec<Loc<Statement>>, Option<Loc<Expression>>)> {
        fn semi_validator(next: Token) -> Result<TokenKind> {
            match next.kind {
                TokenKind::GreekQuestionMark => Err(Diagnostic::error(
                    next.clone(),
                    format!("Expected `;`, got a greek question mark (;)"),
                )
                .help("The greek question mark (;) looks similar to the normal `;` character")),
                other => Ok(other),
            }
        }
        let semi_continuation = |inner: Loc<Statement>, parser: &mut Parser| {
            let next = parser.peek()?;
            let span = next.loc();
            match semi_validator(next) {
                Ok(TokenKind::Semi) => {
                    parser.eat_unconditional()?;
                    Ok(inner)
                }
                Ok(other) => Err(Diagnostic::error(
                    span,
                    format!("Expected `;`, got `{}`", other.as_str()),
                )
                .primary_label("Expected `;`")
                .span_suggest_insert_after(
                    "You probably forgot to end this statement with a `;`",
                    inner,
                    ";",
                )),
                Err(err) => Err(err),
            }
        };

        let mut final_expr = None;
        let members = self.keyword_peeking_parser_or_else_seq(
            vec![
                Box::new(BindingParser {}.then(semi_continuation)),
                Box::new(RegisterParser {}.then(semi_continuation).then(
                    move |statement, _parser| {
                        if let Statement::PipelineRegMarker(_, _) = statement.inner {
                            if !allow_stages {
                                return Err(Diagnostic::error(
                                    statement.loc(),
                                    "stage outside pipeline",
                                )
                                .primary_label("stage is not allowed here")
                                .note("stages are only allowed in the root block of a pipeline"));
                            }
                        }
                        Ok(statement)
                    },
                )),
                Box::new(DeclParser {}.then(semi_continuation)),
                Box::new(LabelParser {}),
                Box::new(AssertParser {}.then(semi_continuation)),
                Box::new(SetParser {}.then(semi_continuation)),
            ],
            true,
            vec![|tok| tok == &TokenKind::CloseBrace],
            |parser, attrs| {
                let start_token = parser.peek()?;
                if parser.peek_kind(&TokenKind::CloseBrace)? {
                    parser.disallow_attributes(&attrs, &start_token)?;
                    return Ok(None);
                }
                let (expr, loc) = parser.non_comptime_expression()?.separate_loc();
                if matches!(semi_validator(parser.peek()?)?, TokenKind::Semi) {
                    parser.eat_unconditional()?;
                    Ok(Some(Statement::Expression(expr, attrs).at_loc(&loc)))
                } else {
                    parser.disallow_attributes(&attrs, &start_token)?;
                    // no semicolon afterwards - set as return value and break out of loop
                    final_expr = Some(expr);
                    Ok(None)
                }
            },
        )?;

        Ok((members, final_expr))
    }

    #[trace_parser]
    pub fn parameter(
        &mut self,
        accept_impl: bool,
    ) -> Result<(AttributeList, Loc<Identifier>, Loc<TypeSpec>)> {
        let attrs = self.attributes()?;
        let (name, ty) = self.name_and_type(accept_impl)?;

        Ok((attrs, name, ty))
    }

    #[trace_parser]
    pub fn parameter_list(&mut self, accept_impl: bool) -> Result<ParameterList> {
        let mut first_attrs = self.attributes()?;

        let self_ = if self.peek_cond(
            |tok| matches!(tok, TokenKind::Identifier(i) if i.as_str() == "self"),
            "Expected argument",
        )? {
            let self_tok = self.eat_unconditional()?;
            self.peek_and_eat(&TokenKind::Comma)?;
            let attrs;
            (first_attrs, attrs) = (AttributeList::empty(), first_attrs);
            Some(attrs.at(self.file_id, &self_tok))
        } else {
            None
        };

        let mut args = self
            .comma_separated(|s| s.parameter(accept_impl), &TokenKind::CloseParen)
            .no_context()?;

        if !first_attrs.is_empty() {
            let Some(first_arg) = args.first_mut() else {
                // At this point this parser will definitely fail, we run it just for its diagnostic
                self.eat_cond(TokenKind::is_identifier, "Identifier")?;
                unreachable!();
            };

            // Patch attributes into the first parameter
            first_arg.0 = first_attrs;
        }

        Ok(ParameterList { self_, args })
    }

    #[tracing::instrument(skip(self))]
    pub fn type_parameter_list(&mut self) -> Result<ParameterList> {
        Ok(ParameterList::without_self(
            self.comma_separated(|s| s.parameter(false), &TokenKind::CloseBrace)
                .no_context()?,
        ))
    }

    #[trace_parser]
    pub fn type_param(&mut self) -> Result<Loc<TypeParam>> {
        // If this is a type level integer
        if let Some(_hash) = self.peek_and_eat(&TokenKind::Hash)? {
            let meta_type = self.identifier()?;
            let name = self.identifier()?;
            let loc = ().between_locs(&meta_type, &name);

            let default = if self.peek_and_eat(&TokenKind::Assignment)?.is_some() {
                Some(self.type_expression()?)
            } else {
                None
            };

            Ok(TypeParam::TypeWithMeta {
                meta: meta_type,
                name,
                default,
            }
            .at_loc(&loc))
        } else {
            let (id, loc) = self.identifier()?.separate();
            let traits = if self.peek_and_eat(&TokenKind::Colon)?.is_some() {
                self.token_separated(
                    Self::trait_spec,
                    &TokenKind::Plus,
                    vec![TokenKind::Assignment, TokenKind::Comma, TokenKind::Gt],
                )
                .no_context()?
                .into_iter()
                .map(|spec| {
                    let loc = ().at_loc(&spec.path);
                    spec.at_loc(&loc)
                })
                .collect()
            } else {
                vec![]
            };
            let default = if self.peek_and_eat(&TokenKind::Assignment)?.is_some() {
                Some(self.type_expression()?)
            } else {
                None
            };
            Ok(TypeParam::TypeName {
                name: id,
                traits,
                default,
            }
            .at(self.file_id, &loc))
        }
    }

    #[trace_parser]
    pub fn generics_list(&mut self) -> Result<Option<Loc<Vec<Loc<TypeParam>>>>> {
        if self.peek_kind(&TokenKind::Lt)? {
            let (params, loc) = self.surrounded(
                &TokenKind::Lt,
                |s| {
                    s.comma_separated(Self::type_param, &TokenKind::Gt)
                        .extra_expected(vec!["type parameter"])
                },
                &TokenKind::Gt,
            )?;
            Ok(Some(params.at_loc(&loc)))
        } else {
            Ok(None)
        }
    }

    #[trace_parser]
    pub fn generic_spec_list(&mut self) -> Result<Option<Loc<Vec<Loc<TypeExpression>>>>> {
        if self.peek_kind(&TokenKind::Lt)? {
            let (params, loc) = self.surrounded(
                &TokenKind::Lt,
                |s| {
                    s.comma_separated(Self::type_expression, &TokenKind::Gt)
                        .extra_expected(vec!["type spec"])
                },
                &TokenKind::Gt,
            )?;
            Ok(Some(params.at_loc(&loc)))
        } else {
            Ok(None)
        }
    }

    #[trace_parser]
    pub fn trait_spec(&mut self) -> Result<TraitSpec> {
        let path = self.path()?;
        let mut type_params = self.generic_spec_list()?;
        let mut paren_syntax = false;

        if self.peek_cond(|tok| tok == &TokenKind::OpenParen, "(")? {
            let param_tuple_type = self.tuple_spec()?.unwrap().map(|tuple| {
                let TypeSpec::Tuple(contents) = tuple else {
                    unreachable!();
                };

                TypeExpression::TypeSpec(Box::new(Loc::nowhere(TypeSpec::Tuple(contents))))
            });

            let start = param_tuple_type.loc();
            let (return_type, end) = if self.peek_and_eat(&TokenKind::SlimArrow)?.is_some() {
                let ty = self.type_expression()?;
                let loc = ty.loc();
                (ty, loc)
            } else {
                let dummy = Loc::nowhere(TypeExpression::TypeSpec(Box::new(Loc::nowhere(
                    TypeSpec::Tuple(vec![]),
                ))));
                (dummy, param_tuple_type.loc())
            };

            let mut new_type_params = type_params.unwrap_or(vec![].nowhere()).inner;
            new_type_params.extend_from_slice(&[param_tuple_type, return_type]);
            type_params = Some(new_type_params.between_locs(&start, &end));

            paren_syntax = true;
        };

        Ok(TraitSpec {
            path,
            type_params,
            paren_syntax,
        })
    }

    fn disallow_attributes(&self, attributes: &AttributeList, item_start: &Token) -> Result<()> {
        if attributes.0.is_empty() {
            Ok(())
        } else {
            Err(Diagnostic::error(
                ().between_locs(attributes.0.first().unwrap(), attributes.0.last().unwrap()),
                "invalid attribute location",
            )
            .primary_label("attributes are not allowed here")
            .secondary_label(
                item_start.loc(),
                format!("{} cannot have attributes", item_start.kind.as_str()),
            )
            .note("attributes are allowed on modules, `use` aliases, traits, structs, enums, their variants functions, entities and pipelines"))
        }
    }

    fn disallow_visibility(&self, visibility: &Loc<Visibility>, item_start: &Token) -> Result<()> {
        if visibility.inner == Visibility::Implicit {
            Ok(())
        } else {
            Err(
                Diagnostic::error(visibility, "invalid visibility marker location")
                    .primary_label("visibility markers are not allowed here")
                    .secondary_label(
                        item_start.loc(),
                        format!(
                            "{} cannot have a visibility marker",
                            item_start.kind.as_str()
                        ),
                    ),
            )
        }
    }

    pub fn unit_kind(&mut self, start_token: &Token) -> Result<Option<Loc<UnitKind>>> {
        match start_token.kind {
            TokenKind::Pipeline => {
                self.eat_unconditional()?;
                let (depth, depth_span) = self.surrounded(
                    &TokenKind::OpenParen,
                    |s| match s.type_expression() {
                        Ok(t) => Ok(t),
                        Err(diag) => Err(diag.secondary_label(
                            ().at(s.file_id, start_token),
                            "Pipelines require a pipeline depth",
                        )),
                    },
                    &TokenKind::CloseParen,
                )?;

                Ok(Some(UnitKind::Pipeline(depth).between(
                    self.file_id,
                    start_token,
                    &depth_span,
                )))
            }
            TokenKind::Function => {
                self.eat_unconditional()?;
                Ok(Some(UnitKind::Function.at(self.file_id, start_token)))
            }
            TokenKind::Entity => {
                self.eat_unconditional()?;
                Ok(Some(UnitKind::Entity.at(self.file_id, start_token)))
            }
            _ => Ok(None),
        }
    }

    #[trace_parser]
    #[tracing::instrument(skip(self))]
    fn visibility(&mut self) -> Result<Loc<Visibility>> {
        if let Some(pub_kw) = self.peek_and_eat(&TokenKind::Pub)? {
            if self.peek_and_eat(&TokenKind::OpenParen)?.is_some() {
                let next_token = self.peek()?;
                let visibility = match next_token.kind {
                    TokenKind::Identifier(ref name) => match name.as_str() {
                        "lib" => Some(Visibility::AtLib),
                        "self" => Some(Visibility::AtSelf),
                        "super" => Some(Visibility::AtSuper),
                        _ => None,
                    },
                    _ => None,
                };

                let Some(visibility) = visibility else {
                    return Err(Diagnostic::error(
                        next_token,
                        "Expected `self`, `super` or `lib`",
                    ));
                };

                self.eat_unconditional()?;

                let Some(close_parens) = self.peek_and_eat(&TokenKind::CloseParen)? else {
                    let next_token = self.peek()?;
                    return Err(Diagnostic::error(next_token, "Expected closing `)`"));
                };

                Ok(visibility.between_locs(&pub_kw.loc(), &close_parens.loc()))
            } else {
                Ok(Visibility::Public.at_loc(&pub_kw.loc()))
            }
        } else {
            Ok(Visibility::Implicit.nowhere())
        }
    }

    #[trace_parser]
    #[tracing::instrument(skip(self))]
    pub fn unit_head(
        &mut self,
        attributes: &AttributeList,
        visibility: &Loc<Visibility>,
    ) -> Result<Option<Loc<UnitHead>>> {
        let unsafe_token = self.peek_and_eat(&TokenKind::Unsafe)?;
        let extern_token = self.peek_and_eat(&TokenKind::Extern)?;
        let start_token = self.peek()?;
        let Some(unit_kind) = self.unit_kind(&start_token)? else {
            if let Some(prev) = unsafe_token.or(extern_token) {
                return Err(Diagnostic::error(
                    start_token,
                    "Expected `fn`, `entity` or `pipeline`",
                )
                .primary_label("Expected `fn`, `entity` or `pipeline`")
                .secondary_label(prev, "Because of this keyword"));
            } else {
                return Ok(None);
            }
        };

        let name = self.identifier()?;

        let type_params = self.generics_list()?;

        // Input types
        let (inputs, inputs_loc) = self.surrounded(
            &TokenKind::OpenParen,
            |s| s.parameter_list(true),
            &TokenKind::CloseParen,
        )?;
        let inputs = inputs.at_loc(&inputs_loc);

        // Return type
        let output_type = if let Some(arrow) = self.peek_and_eat(&TokenKind::SlimArrow)? {
            Some((arrow.loc(), self.type_spec(false)?))
        } else {
            None
        };

        let where_clauses = self.where_clauses()?;

        let end = output_type
            .as_ref()
            .map(|o| o.1.loc())
            .unwrap_or(inputs.loc());

        Ok(Some(
            UnitHead {
                visibility: visibility.clone(),
                unsafe_token: unsafe_token.map(|token| token.loc()),
                extern_token: extern_token.map(|token| token.loc()),
                attributes: attributes.clone(),
                unit_kind,
                name,
                inputs,
                output_type,
                type_params,
                where_clauses,
            }
            .between(self.file_id, &start_token, &end),
        ))
    }

    fn where_clauses(&mut self) -> Result<Vec<WhereClause>> {
        if let Some(where_kw) = self.peek_and_eat(&TokenKind::Where)? {
            let clauses = self
                .token_separated(
                    |s| {
                        if s.peek_cond(|t| matches!(t, &TokenKind::Identifier(_)), "identifier")? {
                            let name = s.path()?;
                            if let Some(_colon) = s.peek_and_eat(&TokenKind::Colon)? {
                                // We'll grandfather in the old : {} syntax for now
                                if s.peek_cond(
                                    |tok| tok == &TokenKind::OpenBrace || tok == &TokenKind::Semi,
                                    "{",
                                )? {
                                    let expression = s
                                        .surrounded(
                                            &TokenKind::OpenBrace,
                                            Self::expression,
                                            &TokenKind::CloseBrace,
                                        )?
                                        .0;

                                    Ok(WhereClause::GenericInt {
                                        target: name,
                                        kind: spade_ast::Inequality::Eq,
                                        expression,
                                        if_unsatisfied: None,
                                    })
                                } else {
                                    let traits = s
                                        .token_separated(
                                            Self::trait_spec,
                                            &TokenKind::Plus,
                                            vec![
                                                TokenKind::Comma,
                                                TokenKind::OpenBrace,
                                                TokenKind::Semi,
                                            ],
                                        )
                                        .extra_expected(vec!["identifier"])?
                                        .into_iter()
                                        .map(|spec| {
                                            let loc = ().at_loc(&spec.path);
                                            spec.at_loc(&loc)
                                        })
                                        .collect();

                                    Ok(WhereClause::TraitBounds {
                                        target: name,
                                        traits,
                                    })
                                }
                            } else {
                                let next = s.eat_unconditional()?;
                                let inequality = match next.kind {
                                    TokenKind::Equals => Inequality::Eq,
                                    TokenKind::NotEquals => Inequality::Neq,
                                    TokenKind::Gt => Inequality::Gt,
                                    TokenKind::Ge => Inequality::Geq,
                                    TokenKind::Lt => Inequality::Lt,
                                    TokenKind::Le => Inequality::Leq,
                                    _ => {
                                        return Err(Diagnostic::from(UnexpectedToken {
                                            got: next,
                                            expected: vec![":", "==", "!=", ">", ">=", "<=", "<"],
                                        })
                                        .into())
                                    }
                                };

                                let expression = s.expression()?;

                                let if_unsatisfied =
                                    if let Some(_) = s.peek_and_eat(&TokenKind::Else)? {
                                        let message = s.eat_unconditional()?;
                                        match message.kind {
                                            TokenKind::String(s) => Some(s),
                                            _ => {
                                                return Err(Diagnostic::from(UnexpectedToken {
                                                    got: message,
                                                    expected: vec!["\""],
                                                }))
                                            }
                                        }
                                    } else {
                                        None
                                    };

                                Ok(WhereClause::GenericInt {
                                    target: name,
                                    kind: inequality,
                                    expression,
                                    if_unsatisfied,
                                })
                            }
                        } else {
                            Err(Diagnostic::bug(
                                ().at(s.file_id, &where_kw),
                                "Comma separated should not show this error",
                            ))
                        }
                    },
                    &TokenKind::Comma,
                    vec![TokenKind::OpenBrace, TokenKind::Semi],
                )
                .extra_expected(vec!["identifier"])?;

            Ok(clauses)
        } else {
            Ok(vec![])
        }
    }

    #[trace_parser]
    pub fn impl_body(&mut self) -> Result<Vec<Loc<Unit>>> {
        let result = self.keyword_peeking_parser_seq(
            vec![Box::new(items::UnitParser {}.map(|u| Ok(u)))],
            true,
            vec![|tok| tok == &TokenKind::CloseBrace],
        )?;

        Ok(result)
    }

    #[trace_parser]
    #[tracing::instrument(level = "debug", skip(self))]
    pub fn enum_variant(&mut self) -> Result<EnumVariant> {
        let attributes = self.attributes()?;

        let name = self.identifier()?;

        let args = if let Some(start) = self.peek_and_eat(&TokenKind::OpenBrace)? {
            let result = self.type_parameter_list()?;
            let end = self.eat(&TokenKind::CloseBrace)?;
            Some(result.between(self.file_id, &start, &end))
        } else if self.peek_kind(&TokenKind::Comma)? || self.peek_kind(&TokenKind::CloseBrace)? {
            None
        } else {
            let token = self.peek()?;
            let message = unexpected_token_message(&token.kind, "`{`, `,` or `}`");
            // FIXME: Error::Eof => Diagnostic
            let mut err = Diagnostic::error(token, message);
            self.maybe_suggest_brace_enum_variant(&mut err)?;
            return Err(err);
        };

        Ok(EnumVariant {
            attributes,
            name,
            args,
        })
    }

    fn maybe_suggest_brace_enum_variant(&mut self, err: &mut Diagnostic) -> Result<bool> {
        let open_paren = match self.peek_and_eat(&TokenKind::OpenParen)? {
            Some(open_paren) => open_paren.loc(),
            _ => return Ok(false),
        };
        let mut try_parameter_list = self.clone();
        if try_parameter_list.parameter_list(false).is_err() {
            return Ok(false);
        }
        let close_paren = match try_parameter_list.peek_and_eat(&TokenKind::CloseParen)? {
            Some(close_paren) => close_paren.loc(),
            _ => return Ok(false),
        };
        err.push_subdiagnostic(
            SuggestBraceEnumVariant {
                open_paren,
                close_paren,
            }
            .into(),
        );
        Ok(true)
    }

    // Parses `<identifier>=<subtree>` if `identifier` matches the specified identifier
    #[trace_parser]
    #[tracing::instrument(skip(self, value))]
    pub fn attribute_key_value<T>(
        &mut self,
        key: &str,
        value: impl Fn(&mut Self) -> Result<T>,
    ) -> Result<Option<(Loc<String>, T)>> {
        let next = self.peek()?;
        if matches!(next.kind, TokenKind::Identifier(k) if k.as_str() == key) {
            self.eat_unconditional()?;

            self.eat(&TokenKind::Assignment)?;

            Ok(Some((
                key.to_string().at(self.file_id, &next),
                value(self)?,
            )))
        } else {
            Ok(None)
        }
    }

    #[trace_parser]
    #[tracing::instrument(skip(self))]
    pub fn attribute_inner(&mut self) -> Result<Attribute> {
        let start = self.identifier()?;

        macro_rules! bool_or_payload {
            ($name:ident bool) => {
                let mut $name = false;
            };
            ($name:ident $rest:tt) => {
                let mut $name = None;
            };
        }
        macro_rules! rhs_or_present {
            ($name:ident, $tok:expr, $s:ident, bool) => {
                $name = true
            };
            ($name:ident, $tok:expr, $s:ident, $subparser:tt) => {{
                if let Some(prev) = &$name {
                    return Err(Diagnostic::error(
                        $tok,
                        format!("{} specified more than once", stringify!($name)),
                    )
                    .primary_label("Specified multiple times")
                    .secondary_label(prev, "Previously specified here")
                    .into());
                }

                $s.peek_and_eat(&TokenKind::Assignment)?;
                $name = Some($subparser?)
            }};
        }

        macro_rules! check_required {
            ($attr_token:expr, $name:ident) => {};
            ($attr_token:expr, $name:ident $required:ident) => {
                let $name = if let Some(inner) = $name {
                    inner
                } else {
                    return Err(Diagnostic::error(
                        $attr_token,
                        format!("Missing argument '{}'", stringify!($name)),
                    )
                    .primary_label(format!("Missing argument '{}'", stringify!($name)))
                    .into());
                };
            };
        }

        macro_rules! attribute_arg_parser {
            ($attr:expr, $self:expr, $s:ident, $result_struct:path{ $($name:ident $([$required:ident])?:  $assignment:tt),* }) => {
                {
                $( bool_or_payload!($name $assignment) );*;

                let params = vec![$(stringify!($name)),*];

                $self.surrounded(
                    &TokenKind::OpenParen, |$s| {
                        loop {
                            let next = $s.peek()?;
                            match &next.kind {
                                $(
                                    TokenKind::Identifier(ident) if ident.as_str() == stringify!($name) => {
                                        $s.eat_unconditional()?;
                                        rhs_or_present!($name, next, $s, $assignment);
                                    }
                                ),*
                                TokenKind::Identifier(_) => {
                                    return Err(Diagnostic::error(next, format!("Invalid parameter for {}", $attr))
                                        .primary_label("Invalid parameter")
                                        .note(if params.is_empty() {
                                            format!(
                                                "{} does not take any parameters",
                                                $attr
                                            )
                                        } else if params.len() == 1 {
                                            format!(
                                                "{} only takes the parameter {}",
                                                $attr,
                                                params[0]
                                            )
                                        } else {
                                            format!(
                                                "{} only takes the parameters {} or {}",
                                                $attr,
                                                params.iter().take(params.len()-1).join(", "),
                                                params[params.len() - 1]
                                            )
                                        })
                                        .into()
                                    )
                                }
                                TokenKind::Comma => {
                                    $s.eat_unconditional()?;
                                }
                                TokenKind::CloseParen => {
                                    break
                                },
                                _ => {
                                    return Err(Diagnostic::from(UnexpectedToken {
                                        got: next,
                                        expected: vec!["identifier", ",", ")"],
                                    }).into())
                                }
                            }
                        }

                        Ok(())
                    },
                    &TokenKind::CloseParen
                )?;

                $(check_required!($attr, $name $($required)?);)*

                $result_struct {
                    $($name),*
                }
            }
            }
        }

        match start.inner.as_str() {
            "spadec_paren_sugar" => Ok(Attribute::SpadecParenSugar),
            "verilog_attrs" => {
                let (entries, _) = self.surrounded(
                    &TokenKind::OpenParen,
                    |s| {
                        s.comma_separated(|s| s.verilog_attr(), &TokenKind::CloseParen)
                            .no_context()
                    },
                    &TokenKind::CloseParen,
                )?;
                Ok(Attribute::VerilogAttrs { entries })
            }
            "no_mangle" => {
                if self.peek_kind(&TokenKind::OpenParen)? {
                    let (all, _) = self.surrounded(
                        &TokenKind::OpenParen,
                        Self::identifier,
                        &TokenKind::CloseParen,
                    )?;
                    if all.inner.as_str() != "all" {
                        Err(Diagnostic::error(&all, "Invalid attribute syntax")
                            .primary_label("Unexpected parameter to `#[no_mangle])")
                            .span_suggest_replace("Did you mean `#[no_mangle(all)]`?", all, "all"))
                    } else {
                        Ok(Attribute::NoMangle { all: true })
                    }
                } else {
                    Ok(Attribute::NoMangle { all: false })
                }
            }
            "fsm" => {
                if self.peek_kind(&TokenKind::OpenParen)? {
                    let (state, _) = self.surrounded(
                        &TokenKind::OpenParen,
                        Self::identifier,
                        &TokenKind::CloseParen,
                    )?;
                    Ok(Attribute::Fsm { state: Some(state) })
                } else {
                    Ok(Attribute::Fsm { state: None })
                }
            }
            "optimize" => {
                let (passes, _) = self.surrounded(
                    &TokenKind::OpenParen,
                    |s| {
                        s.comma_separated(|s| s.identifier(), &TokenKind::CloseParen)
                            .no_context()
                    },
                    &TokenKind::CloseParen,
                )?;

                Ok(Attribute::Optimize {
                    passes: passes
                        .into_iter()
                        .map(|loc| loc.map(|ident| ident.as_str().to_owned()))
                        .collect(),
                })
            }
            "deprecated" => {
                if self.peek_kind(&TokenKind::OpenParen)? {
                    Ok(attribute_arg_parser!(
                        start,
                        self,
                        s,
                        Attribute::Deprecated {
                            since: { s.str_literal().map(Option::unwrap) },
                            note: { s.str_literal().map(Option::unwrap) }
                        }
                    ))
                } else if self.peek_and_eat(&TokenKind::Assignment)?.is_some() {
                    let note = self.str_literal()?;
                    Ok(Attribute::Deprecated { since: None, note })
                } else {
                    Ok(Attribute::Deprecated {
                        since: None,
                        note: None,
                    })
                }
            }
            "surfer_translator" => {
                let (result, _) = self.surrounded(
                    &TokenKind::OpenParen,
                    |s| {
                        let tok = s.peek()?;
                        if let TokenKind::String(name) = tok.kind {
                            s.eat_unconditional()?;
                            Ok(Attribute::SurferTranslator(name))
                        } else {
                            Err(UnexpectedToken {
                                got: tok,
                                expected: vec!["string"],
                            }
                            .into())
                        }
                    },
                    &TokenKind::CloseParen,
                )?;
                Ok(result)
            }
            "inline" => Ok(Attribute::Inline),
            "wal_trace" => {
                if self.peek_kind(&TokenKind::OpenParen)? {
                    Ok(attribute_arg_parser!(
                        start,
                        self,
                        s,
                        Attribute::WalTrace {
                            clk: { s.expression() },
                            rst: { s.expression() }
                        }
                    ))
                } else {
                    Ok(Attribute::WalTrace {
                        clk: None,
                        rst: None,
                    })
                }
            }
            "wal_traceable" => Ok(attribute_arg_parser!(
                start,
                self,
                s,
                Attribute::WalTraceable {
                    suffix: { s.identifier() },
                    uses_clk: bool,
                    uses_rst: bool
                }
            )),
            "wal_suffix" => Ok(attribute_arg_parser!(start, self, s, Attribute::WalSuffix {
                suffix [required]: {s.identifier()}
            })),
            other => Err(
                Diagnostic::error(&start, format!("Unknown attribute '{other}'"))
                    .primary_label("Unrecognised attribute"),
            ),
        }
    }

    #[trace_parser]
    fn verilog_attr(&mut self) -> Result<(Loc<Identifier>, Option<Loc<String>>)> {
        let key = self.identifier()?;
        let value = if self.peek_and_eat(&TokenKind::Assignment)?.is_some() {
            let token = self.eat_cond(TokenKind::is_string, "string")?;
            match &token.kind {
                TokenKind::String(val) => Some(val.clone().at_loc(&token.loc())),
                _ => unreachable!(),
            }
        } else {
            None
        };
        Ok((key, value))
    }

    #[trace_parser]
    pub fn attributes(&mut self) -> Result<AttributeList> {
        // peek_for!(self, &TokenKind::Hash)
        let mut result = AttributeList(vec![]);
        loop {
            if let Some(start) = self.peek_and_eat(&TokenKind::Hash)? {
                let (inner, loc) = self.surrounded(
                    &TokenKind::OpenBracket,
                    Self::attribute_inner,
                    &TokenKind::CloseBracket,
                )?;

                result.0.push(inner.between(self.file_id, &start, &loc));
            } else if self.peek_cond(
                |tk| matches!(tk, TokenKind::OutsideDocumentation(_)),
                "Outside doc-comment",
            )? {
                let token = self.eat_unconditional()?;
                let TokenKind::OutsideDocumentation(doc) = token.kind else {
                    unreachable!("eat_cond should have checked this");
                };
                result
                    .0
                    .push(Attribute::Documentation { content: doc }.at(token.file_id, &token.span));
            } else {
                break;
            }
        }
        Ok(result)
    }

    #[trace_parser]
    #[tracing::instrument(skip(self))]
    pub fn module_body(&mut self) -> Result<ModuleBody> {
        let mut documentation = vec![];
        while self.peek_cond(
            |tk| matches!(tk, TokenKind::InsideDocumentation(_)),
            "Inside doc-comment",
        )? {
            let token = self.eat_unconditional()?;
            let TokenKind::InsideDocumentation(doc) = token.kind else {
                unreachable!("eat_cond should have checked this");
            };
            documentation.push(doc);
        }

        let members = self.keyword_peeking_parser_seq(
            vec![
                Box::new(items::UnitParser {}.map(|inner| Ok(Item::Unit(inner)))),
                Box::new(items::TraitDefParser {}.map(|inner| Ok(Item::TraitDef(inner)))),
                Box::new(items::ImplBlockParser {}.map(|inner| Ok(Item::ImplBlock(inner)))),
                Box::new(items::StructParser {}.map(|inner| Ok(Item::Type(inner)))),
                Box::new(items::EnumParser {}.map(|inner| Ok(Item::Type(inner)))),
                Box::new(items::ModuleParser {}),
                Box::new(items::UseParser {}.map(|inner| Ok(Item::Use(inner.0, inner.1)))),
            ],
            true,
            vec![],
        )?;
        Ok(ModuleBody {
            members,
            documentation,
        })
    }

    /// A module body which is not part of a `mod`. Errors if there is anything
    /// but an item found after the last item
    #[trace_parser]
    #[tracing::instrument(skip(self))]
    pub fn top_level_module_body(&mut self) -> Result<Loc<ModuleBody>> {
        let start_token = self.peek()?;
        let result = (|| {
            let result = self.module_body()?;
            let end_token = self.peek()?;

            Ok(result.between(self.file_id, &start_token, &end_token))
        })();

        if !self.peek_kind(&TokenKind::Eof)? {
            let got = self.peek()?;
            Diagnostic::error(
                got.loc(),
                format!("expected item, got `{}`", got.kind.as_str()),
            )
            .primary_label("expected item")
            .handle_in(&mut self.diags);
        }

        match result {
            Ok(result) => Ok(result),
            e @ Err(_) => {
                e.handle_in(&mut self.diags);

                Ok(ModuleBody {
                    members: vec![],
                    documentation: vec![],
                }
                .between(self.file_id, &start_token, &self.peek()?))
            }
        }
    }
}

// Helper functions for combining parsers
impl<'a> Parser<'a> {
    #[tracing::instrument(skip_all, fields(parsers = parsers.len()))]
    fn first_successful<T>(
        &mut self,
        parsers: Vec<&dyn Fn(&mut Self) -> Result<Option<T>>>,
    ) -> Result<Option<T>> {
        for parser in parsers {
            match parser(self) {
                Ok(Some(val)) => {
                    event!(Level::INFO, "Parser matched");
                    return Ok(Some(val));
                }
                Ok(None) => continue,
                Err(e) => return Err(e),
            }
        }
        event!(Level::INFO, "No parser matched");
        Ok(None)
    }

    /// Attempts to parse an inner structure surrounded by two tokens, like `( x )`.
    ///
    /// If the `start` token is not found, an error is produced.
    ///
    /// If the end token is not found, return a mismatch error
    #[tracing::instrument(level = "debug", skip(self, inner))]
    fn surrounded<T>(
        &mut self,
        start: &TokenKind,
        mut inner: impl FnMut(&mut Self) -> Result<T>,
        end_kind: &TokenKind,
    ) -> Result<(T, Loc<()>)> {
        let opener = self.eat(start)?;
        let result = inner(self)?;
        // FIXME: Better error handling here. We are throwing away potential EOFs
        let end = if let Some(end) = self.peek_and_eat(end_kind)? {
            end
        } else {
            let got = self.eat_unconditional()?;
            return Err(Diagnostic::error(
                got.loc(),
                format!(
                    "expected closing `{}`, got `{}`",
                    end_kind.as_str(),
                    got.kind.as_str()
                ),
            )
            .primary_label(format!("expected `{}`", end_kind.as_str()))
            .secondary_label(
                opener.loc(),
                format!("...to close this `{}`", start.as_str()),
            ));
        };

        Ok((
            result,
            Loc::new((), lspan(opener.span).merge(lspan(end.span)), self.file_id),
        ))
    }

    pub fn comma_separated<T>(
        &mut self,
        inner: impl Fn(&mut Self) -> Result<T>,
        // This end marker is used for allowing trailing commas. It should
        // be whatever ends the collection that is searched. I.e. (a,b,c,) should have
        // `)`, and {} should have `}`
        end_marker: &TokenKind,
    ) -> CommaSeparatedResult<Vec<T>> {
        self.token_separated(inner, &TokenKind::Comma, vec![end_marker.clone()])
    }

    // NOTE: This cannot currently use #[trace_parser] as it returns an error which is not
    // convertible into `Error`. If we end up with more functions like this, that
    // macro should probably be made smarter
    #[tracing::instrument(level = "debug", skip(self, inner))]
    pub fn token_separated<T>(
        &mut self,
        inner: impl Fn(&mut Self) -> Result<T>,
        separator: &TokenKind,
        // This end marker is used for allowing trailing commas. It should
        // be whatever ends the collection that is searched. I.e. (a,b,c,) should have
        // `)`, and {} should have `}`
        end_markers: Vec<TokenKind>,
    ) -> CommaSeparatedResult<Vec<T>> {
        self.parse_stack
            .push(ParseStackEntry::Enter("comma_separated".to_string()));
        let ret = || -> CommaSeparatedResult<Vec<T>> {
            let mut result = vec![];
            loop {
                // The list might be empty
                if end_markers
                    .iter()
                    .map(|m| self.peek_kind(m))
                    .collect::<Result<Vec<_>>>()?
                    .into_iter()
                    .any(|x| x)
                {
                    break;
                }
                result.push(inner(self)?);

                // Now we expect to either find a comma, in which case we resume the
                // search, or an end marker, in which case we abort
                if end_markers
                    .iter()
                    .map(|m| self.peek_kind(m))
                    .collect::<Result<Vec<_>>>()?
                    .into_iter()
                    .any(|x| x)
                {
                    break;
                } else if self.peek_kind(separator)? {
                    self.eat_unconditional()?;
                } else {
                    return Err(TokenSeparatedError::UnexpectedToken {
                        got: self.peek()?,
                        separator: separator.clone(),
                        end_tokens: end_markers,
                    });
                }
            }
            Ok(result)
        }();
        if let Err(e) = &ret {
            self.parse_stack
                .push(ParseStackEntry::ExitWithDiagnostic(e.clone().no_context()));
        } else {
            self.parse_stack.push(ParseStackEntry::Exit);
        }

        ret
    }

    fn keyword_peeking_parser_seq<T>(
        &mut self,
        parsers: Vec<Box<dyn KeywordPeekingParser<T>>>,
        support_attributes: bool,
        additional_continuations: Vec<fn(&TokenKind) -> bool>,
    ) -> Result<Vec<T>> {
        self.keyword_peeking_parser_or_else_seq(
            parsers,
            support_attributes,
            additional_continuations,
            |_, _| Ok(None),
        )
    }

    /// Works like `keyword_peeking_parser_seq` but runs the `other` function if none of the keyword parsers matched.
    ///
    /// If the `other` function returns a value, it is added to the result and the loop continues.
    /// If the `other` function returns `None`, the loop ends.
    fn keyword_peeking_parser_or_else_seq<T, F>(
        &mut self,
        parsers: Vec<Box<dyn KeywordPeekingParser<T>>>,
        support_attributes: bool,
        additional_continuations: Vec<fn(&TokenKind) -> bool>,
        mut other: F,
    ) -> Result<Vec<T>>
    where
        F: FnMut(&mut Self, AttributeList) -> Result<Option<T>>,
    {
        let mut result = vec![];
        let continuations = parsers
            .iter()
            .map(|p| p.is_leading_token())
            .chain(additional_continuations)
            .collect::<Vec<_>>();
        loop {
            let mut attributes = AttributeList::empty();

            let inner = self.with_recovery(
                |s| {
                    if support_attributes {
                        attributes = s.attributes()?;
                    }

                    let visibility = s.visibility()?;

                    let next = s.peek()?;
                    let mut result = None;
                    for parser in &parsers {
                        if parser.is_leading_token()(&next.kind) {
                            result = Some(parser.parse(s, &attributes, &visibility)?)
                        }
                    }
                    Ok(result)
                },
                continuations.clone(),
            );

            match inner {
                RecoveryResult::Ok(Some(stmt)) => result.push(stmt),
                RecoveryResult::Ok(None) => {
                    if let Some(other_res) = (other)(self, attributes)? {
                        result.push(other_res);
                    } else {
                        break;
                    }
                }
                RecoveryResult::Recovered => continue,
            }
        }
        Ok(result)
    }

    pub fn with_recovery<T>(
        &mut self,
        mut inner: impl FnMut(&mut Self) -> Result<T>,
        continuations: Vec<fn(&TokenKind) -> bool>,
    ) -> RecoveryResult<T> {
        let new_continuations = continuations.len();
        self.recovering_tokens.extend(continuations);
        let result = match inner(self) {
            Ok(result) => RecoveryResult::Ok(result),
            Err(e) => {
                self.diags.errors.push(e);

                // Once we error, consume tokens until we find a token in the
                // current continuation set.
                while let Ok(tok) = self.peek() {
                    if self
                        .recovering_tokens
                        .iter()
                        .rev()
                        .any(|peeker| peeker(&tok.kind))
                    {
                        break;
                    }
                    // Safe unwrap, we already peeked
                    self.eat_unconditional().unwrap();
                }

                RecoveryResult::Recovered
            }
        };
        // Pop the newly added continuations
        let _ = self
            .recovering_tokens
            .split_off(self.recovering_tokens.len() - new_continuations);
        result
    }
}

// Helper functions for advancing the token stream
impl<'a> Parser<'a> {
    fn eat(&mut self, expected: &TokenKind) -> Result<Token> {
        self.parse_stack
            .push(ParseStackEntry::EatingExpected(expected.clone()));
        // Calling keep and eat in order to correctly handle >> as > > if desired
        let next = self.eat_unconditional()?;
        if &next.kind == expected {
            Ok(next)
        } else if expected == &TokenKind::Gt && next.kind == TokenKind::RightShift {
            self.peeked = Some(Token {
                kind: TokenKind::Gt,
                span: next.span.end..next.span.end,
                file_id: next.file_id,
            });
            Ok(Token {
                kind: TokenKind::Gt,
                span: next.span.start..next.span.start,
                file_id: next.file_id,
            })
        } else if expected == &TokenKind::Gt && next.kind == TokenKind::ArithmeticRightShift {
            self.peeked = Some(Token {
                kind: TokenKind::RightShift,
                span: next.span.start + 1..next.span.end,
                file_id: next.file_id,
            });
            Ok(Token {
                kind: TokenKind::Gt,
                span: next.span.start..next.span.start,
                file_id: next.file_id,
            })
        } else {
            Err(Diagnostic::from(UnexpectedToken {
                got: next,
                expected: vec![expected.as_str()],
            }))
        }
    }

    fn eat_cond(
        &mut self,
        condition: impl Fn(&TokenKind) -> bool,
        expected_description: &'static str,
    ) -> Result<Token> {
        // Check if we already have a peeked token
        let next = self.eat_unconditional()?;

        // Make sure we ate the correct token
        if !condition(&next.kind) {
            Err(Diagnostic::from(UnexpectedToken {
                got: next,
                expected: vec![expected_description],
            }))
        } else {
            Ok(next)
        }
    }

    fn eat_unconditional(&mut self) -> Result<Token> {
        let food = self
            .peeked
            .take()
            .map(Ok)
            .unwrap_or_else(|| self.next_token())?;

        self.parse_stack.push(ParseStackEntry::Ate(food.clone()));
        self.last_token = Some(food.clone());
        Ok(food)
    }

    /// Peeks the next token. If it is the specified kind, returns that token, otherwise
    /// returns None.
    ///
    /// If kind is > and the peeking is also done for >>, which if found, is split
    /// into > which is returned, and > which populates the peek buffer
    fn peek_and_eat(&mut self, kind: &TokenKind) -> Result<Option<Token>> {
        // peek_cond_no_tracing because peek_kind handles >> -> > > transformation
        // which we don't want here
        if self.peek_kind(kind)? {
            Ok(Some(self.eat(kind)?))
        } else {
            Ok(None)
        }
    }

    pub fn peek(&mut self) -> Result<Token> {
        if let Some(peeked) = self.peeked.clone() {
            Ok(peeked)
        } else {
            let result = match self.next_token() {
                Ok(token) => token,
                Err(e) => return Err(e),
            };
            self.peeked = Some(result.clone());

            Ok(result)
        }
    }

    fn peek_kind(&mut self, expected: &TokenKind) -> Result<bool> {
        let mut result = self.peek_cond_no_tracing(|kind| kind == expected)?;
        if expected == &TokenKind::Gt {
            result |= self.peek_cond_no_tracing(|kind| kind == &TokenKind::RightShift)?
                | self.peek_cond_no_tracing(|kind| kind == &TokenKind::ArithmeticRightShift)?
        }
        self.parse_stack
            .push(ParseStackEntry::PeekingFor(expected.clone(), result));
        Ok(result)
    }

    /// Peek the next token, returning true if the result satisfies the condition.
    ///
    /// If we reached EOF and the peek returns None, returns false
    fn peek_cond(&mut self, cond: impl Fn(&TokenKind) -> bool, msg: &str) -> Result<bool> {
        let result = self.peek_cond_no_tracing(cond)?;
        self.parse_stack.push(ParseStackEntry::PeekingWithCondition(
            msg.to_string(),
            result,
        ));
        Ok(result)
    }

    fn peek_cond_no_tracing(&mut self, cond: impl Fn(&TokenKind) -> bool) -> Result<bool> {
        self.peek().map(|token| cond(&token.kind))
    }

    fn next_token(&mut self) -> Result<Token> {
        self.next_token_helper(0)
    }

    fn next_token_helper(&mut self, block_comment_depth: usize) -> Result<Token> {
        let lex_dot_next = {
            let mut break_value: Option<std::result::Result<_, _>> = None;
            while let Some(next) = self.lex.next() {
                if matches!(next, Ok(TokenKind::Comment)) {
                    self.comments.push(Comment::Line(Token {
                        kind: TokenKind::Comment,
                        span: self.lex.span(),
                        file_id: self.file_id,
                    }));
                } else {
                    break_value = Some(next);
                    break;
                }
            }
            break_value
        };

        let out = match lex_dot_next {
            Some(Ok(k)) => Ok(Token::new(k, &self.lex, self.file_id)),
            Some(Err(_)) => Err(Diagnostic::error(
                Loc::new((), lspan(self.lex.span()), self.file_id),
                "Lexer error, unexpected symbol",
            )),
            None => Ok(match &self.last_token {
                Some(last) => Token {
                    kind: TokenKind::Eof,
                    span: last.span.end..last.span.end,
                    file_id: last.file_id,
                },
                None => Token {
                    kind: TokenKind::Eof,
                    span: logos::Span { start: 0, end: 0 },
                    file_id: self.file_id,
                },
            }),
        }?;

        match out.kind {
            TokenKind::BlockCommentStart => loop {
                let next = match self.next_token_helper(block_comment_depth + 1) {
                    Ok(next) => next,
                    // We don't actually care about lexer errors inside block comments,
                    // so let's just continue.
                    Err(_) => continue,
                };
                match next.kind {
                    TokenKind::BlockCommentEnd => {
                        if block_comment_depth == 0 {
                            self.comments.push(Comment::Block(out, next));
                        }
                        break self.next_token_helper(block_comment_depth);
                    }
                    TokenKind::Eof => {
                        break Err(Diagnostic::error(next, "Unterminated block comment")
                            .primary_label("Expected */")
                            .secondary_label(out, "to close this block comment"))
                    }
                    _ => {}
                }
            },
            _ => Ok(out),
        }
    }
}

impl<'a> Parser<'a> {
    fn set_item_context(&mut self, context: Loc<UnitKind>) -> Result<()> {
        if let Some(prev) = &self.unit_context {
            Err(Diagnostic::bug(
                context.loc(),
                "overwriting previously uncleared item context",
            )
            .primary_label("new context set because of this")
            .secondary_label(prev.loc(), "previous context set here"))
        } else {
            self.unit_context = Some(context);
            Ok(())
        }
    }

    fn clear_item_context(&mut self) {
        self.unit_context = None
    }

    #[cfg(test)]
    fn set_parsing_entity(&mut self) {
        self.set_item_context(UnitKind::Entity.nowhere()).unwrap()
    }
}

trait KeywordPeekingParser<T> {
    fn is_leading_token(&self) -> fn(&TokenKind) -> bool;
    fn parse(
        &self,
        parser: &mut Parser,
        attributes: &AttributeList,
        visibility: &Loc<Visibility>,
    ) -> Result<T>;
}

trait SizedKeywordPeekingParser<T>: Sized + KeywordPeekingParser<T> {
    fn map<F, O>(self, mapper: F) -> MappingParser<Self, F, T, O>
    where
        F: Fn(T) -> Result<O>,
    {
        MappingParser {
            inner: Box::new(self),
            mapper: Box::new(mapper),
            _phantoms: Default::default(),
        }
    }

    fn then<F>(self, then: F) -> ThenParser<Self, F, T>
    where
        F: Fn(T, &mut Parser) -> Result<T>,
    {
        ThenParser {
            inner: Box::new(self),
            then: Box::new(then),
            _phantoms: Default::default(),
        }
    }
}
impl<TOuter, TInner> SizedKeywordPeekingParser<TInner> for TOuter where
    TOuter: KeywordPeekingParser<TInner> + Sized
{
}

struct MappingParser<Inner, Mapper, I, T>
where
    Inner: SizedKeywordPeekingParser<I> + ?Sized,
    Mapper: Fn(I) -> Result<T>,
{
    inner: Box<Inner>,
    mapper: Box<Mapper>,
    _phantoms: (PhantomData<I>, PhantomData<T>),
}

impl<Inner, Mapper, I, T> KeywordPeekingParser<T> for MappingParser<Inner, Mapper, I, T>
where
    Inner: SizedKeywordPeekingParser<I> + ?Sized,
    Mapper: Fn(I) -> Result<T>,
{
    fn is_leading_token(&self) -> fn(&TokenKind) -> bool {
        self.inner.is_leading_token()
    }

    fn parse(
        &self,
        parser: &mut Parser,
        attributes: &AttributeList,
        visibility: &Loc<Visibility>,
    ) -> Result<T> {
        (self.mapper)(self.inner.parse(parser, attributes, visibility)?)
    }
}

/// Allows running parsing tasks after successfully running an inner parser. Used
/// for example to require `;` after some statements with a helpful error message to
/// point out where the `;` is missing.
/// This cannot be used to change the type of `T`, which is intentional as that could
/// easily change the grammar from LL(1)
struct ThenParser<Inner, After, T>
where
    Inner: SizedKeywordPeekingParser<T> + ?Sized,
    After: Fn(T, &mut Parser) -> Result<T>,
{
    inner: Box<Inner>,
    then: Box<After>,
    _phantoms: PhantomData<T>,
}

impl<Inner, After, T> KeywordPeekingParser<T> for ThenParser<Inner, After, T>
where
    Inner: SizedKeywordPeekingParser<T> + ?Sized,
    After: Fn(T, &mut Parser) -> Result<T>,
{
    fn is_leading_token(&self) -> fn(&TokenKind) -> bool {
        self.inner.is_leading_token()
    }

    fn parse(
        &self,
        parser: &mut Parser,
        attributes: &AttributeList,
        visibility: &Loc<Visibility>,
    ) -> Result<T> {
        let inner = self.inner.parse(parser, attributes, visibility)?;
        (self.then)(inner, parser)
    }
}

#[derive(Debug)]
pub enum RecoveryResult<T> {
    Ok(T),
    Recovered,
}

#[local_impl]
impl<T> OptionExt for Option<T> {
    fn or_error(
        self,
        parser: &mut Parser,
        err: impl Fn(&mut Parser) -> Result<Diagnostic>,
    ) -> Result<T> {
        match self {
            Some(val) => Ok(val),
            None => Err(err(parser)?),
        }
    }
}

#[derive(Clone)]
pub enum ParseStackEntry {
    Enter(String),
    Ate(Token),
    PeekingWithCondition(String, bool),
    PeekingFor(TokenKind, bool),
    EatingExpected(TokenKind),
    Exit,
    ExitWithDiagnostic(Diagnostic),
}
pub fn format_parse_stack(stack: &[ParseStackEntry]) -> String {
    let mut result = String::new();
    let mut indent_amount = 0;

    for entry in stack {
        let mut next_indent_amount = indent_amount;
        let message = match entry {
            ParseStackEntry::Enter(function) => {
                next_indent_amount += 1;
                format!("{} `{}`", "trying".white(), function.blue())
            }
            ParseStackEntry::Ate(token) => format!(
                "{} '{}'",
                "Eating".bright_yellow(),
                token.kind.as_str().bright_purple()
            ),
            ParseStackEntry::PeekingFor(kind, success) => format!(
                "{} {} {}",
                "peeking for".white(),
                kind.as_str().bright_blue(),
                if *success {
                    "✓".green()
                } else {
                    "𐄂".red()
                }
            ),
            ParseStackEntry::PeekingWithCondition(needle, success) => format!(
                "{} {} {}",
                "peeking conditionally for ".white(),
                needle.bright_blue(),
                if *success {
                    "✓".green()
                } else {
                    "𐄂".red()
                }
            ),
            ParseStackEntry::EatingExpected(kind) => {
                format!(
                    "{} {}",
                    "eating expected".purple(),
                    kind.as_str().bright_purple()
                )
            }
            ParseStackEntry::Exit => {
                next_indent_amount -= 1;
                String::new()
            }
            ParseStackEntry::ExitWithDiagnostic(_diag) => {
                next_indent_amount -= 1;
                "Giving up".bright_red().to_string()
            }
        };
        if let ParseStackEntry::Exit = entry {
        } else {
            for _ in 0..indent_amount {
                result += "| ";
            }
            result += &message;
            result += "\n"
        }
        indent_amount = next_indent_amount;
    }
    result
}

#[cfg(test)]
mod tests {
    use spade_ast as ast;
    use spade_ast::testutil::{ast_ident, ast_path};
    use spade_ast::*;
    use spade_common::num_ext::InfallibleToBigInt;

    use crate::lexer::TokenKind;
    use crate::*;

    use logos::Logos;

    use spade_common::location_info::WithLocation;

    #[macro_export]
    macro_rules! check_parse {
        ($string:expr , $method:ident$(($($arg:expr),*))?, $expected:expr$(, $run_on_parser:expr)?) => {
            let mut parser = Parser::new(TokenKind::lexer($string), 0);

            $($run_on_parser(&mut parser);)?

            let result = parser.$method($($($arg),*)?);
            // This is needed because type inference fails for some unexpected reason
            let expected: Result<_> = $expected;

            if result != expected {
                println!("Parser state:\n{}", format_parse_stack(&parser.parse_stack));
                panic!(
                    "\n\n     {}: {:?}\n{}: {:?}",
                    "Got".red(),
                    result,
                    "Expected".green(),
                    expected
                );
            };
        };
    }

    #[test]
    fn parsing_identifier_works() {
        check_parse!("abc123_", identifier, Ok(ast_ident("abc123_")));
    }

    #[test]
    fn parsing_paths_works() {
        let expected = Path::from_strs(&["path", "to", "thing"]).nowhere();
        check_parse!("path::to::thing", path, Ok(expected));
    }

    #[test]
    fn literals_are_expressions() {
        check_parse!(
            "123",
            expression,
            Ok(Expression::int_literal_signed(123).nowhere())
        );
    }

    #[test]
    fn size_types_work() {
        let expected = TypeSpec::Named(
            ast_path("uint"),
            Some(vec![TypeExpression::Integer(10u32.to_bigint()).nowhere()].nowhere()),
        )
        .nowhere();
        check_parse!("uint<10>", type_spec(false), Ok(expected));
    }

    #[test]
    fn nested_generics_work() {
        let code = "Option<int<5>>";

        let expected = TypeSpec::Named(
            ast_path("Option"),
            Some(
                vec![TypeExpression::TypeSpec(Box::new(
                    TypeSpec::Named(
                        ast_path("int"),
                        Some(vec![TypeExpression::Integer(5u32.to_bigint()).nowhere()].nowhere()),
                    )
                    .nowhere(),
                ))
                .nowhere()]
                .nowhere(),
            ),
        )
        .nowhere();

        check_parse!(code, type_spec(false), Ok(expected));
    }

    #[test]
    fn module_body_parsing_works() {
        let code = include_str!("../parser_test_code/multiple_entities.sp");

        let e1 = Unit {
            head: UnitHead {
                visibility: Visibility::Implicit.nowhere(),
                unsafe_token: None,
                extern_token: None,
                attributes: AttributeList::empty(),
                unit_kind: UnitKind::Entity.nowhere(),
                name: ast_ident("e1"),
                inputs: aparams![],
                output_type: None,
                type_params: None,
                where_clauses: vec![],
            },
            body: Some(
                Expression::Block(Box::new(Block {
                    statements: vec![],
                    result: Some(Expression::int_literal_signed(0).nowhere()),
                }))
                .nowhere(),
            ),
        }
        .nowhere();

        let e2 = Unit {
            head: UnitHead {
                visibility: Visibility::Implicit.nowhere(),
                unsafe_token: None,
                extern_token: None,
                attributes: AttributeList::empty(),
                unit_kind: UnitKind::Entity.nowhere(),
                name: ast_ident("e2"),
                inputs: aparams![],
                output_type: None,
                type_params: None,
                where_clauses: vec![],
            },
            body: Some(
                Expression::Block(Box::new(Block {
                    statements: vec![],
                    result: Some(Expression::int_literal_signed(1).nowhere()),
                }))
                .nowhere(),
            ),
        }
        .nowhere();

        let expected = ModuleBody {
            members: vec![Item::Unit(e1), Item::Unit(e2)],
            documentation: vec![],
        };

        check_parse!(code, module_body, Ok(expected));
    }

    #[test]
    fn dec_int_literals_work() {
        let code = "1";
        let expected = IntLiteral::unsized_(1).nowhere();

        check_parse!(code, int_literal, Ok(Some(expected)));
    }
    #[test]
    fn dec_negative_int_literals_work() {
        let code = "-1";
        let expected = IntLiteral::unsized_(-1).nowhere();

        check_parse!(code, int_literal, Ok(Some(expected)));
    }
    #[test]
    fn hex_int_literals_work() {
        let code = "0xff";
        let expected = IntLiteral::unsized_(255).nowhere();

        check_parse!(code, int_literal, Ok(Some(expected)));
    }
    #[test]
    fn bin_int_literals_work() {
        let code = "0b101";
        let expected = IntLiteral::unsized_(5).nowhere();

        check_parse!(code, int_literal, Ok(Some(expected)));
    }

    #[test]
    fn type_spec_with_multiple_generics_works() {
        let code = "A<X, Y>";

        let expected = TypeSpec::Named(
            ast_path("A"),
            Some(
                vec![
                    TypeExpression::TypeSpec(Box::new(
                        TypeSpec::Named(ast_path("X"), None).nowhere(),
                    ))
                    .nowhere(),
                    TypeExpression::TypeSpec(Box::new(
                        TypeSpec::Named(ast_path("Y"), None).nowhere(),
                    ))
                    .nowhere(),
                ]
                .nowhere(),
            ),
        )
        .nowhere();

        check_parse!(code, type_spec(false), Ok(expected));
    }

    #[test]
    fn entity_instantiation() {
        let code = "inst some_entity(x, y, z)";

        let expected = Expression::Call {
            kind: CallKind::Entity(().nowhere()),
            callee: ast_path("some_entity"),
            args: ArgumentList::Positional(vec![
                Expression::Identifier(ast_path("x")).nowhere(),
                Expression::Identifier(ast_path("y")).nowhere(),
                Expression::Identifier(ast_path("z")).nowhere(),
            ])
            .nowhere(),
            turbofish: None,
        }
        .nowhere();

        check_parse!(code, expression, Ok(expected), Parser::set_parsing_entity);
    }

    #[test]
    fn named_args_work() {
        let code = "x: a";

        let expected = NamedArgument::Full(
            ast_ident("x"),
            Expression::Identifier(ast_path("a")).nowhere(),
        )
        .nowhere();

        check_parse!(code, named_argument, Ok(expected));
    }

    #[test]
    fn named_capture_shorthand_works() {
        let code = "x";

        let expected = NamedArgument::Short(ast_ident("x")).nowhere();

        check_parse!(code, named_argument, Ok(expected));
    }

    #[test]
    fn tuple_patterns_work() {
        let code = "(x, y)";

        let expected = Pattern::Tuple(vec![Pattern::name("x"), Pattern::name("y")]).nowhere();

        check_parse!(code, pattern, Ok(expected));
    }

    #[test]
    fn integer_patterns_work() {
        let code = "1";

        let expected = Pattern::integer(1).nowhere();

        check_parse!(code, pattern, Ok(expected));
    }

    #[test]
    fn hex_integer_patterns_work() {
        let code = "0xff";

        let expected = Pattern::integer(255).nowhere();

        check_parse!(code, pattern, Ok(expected));
    }

    #[test]
    fn bin_integer_patterns_work() {
        let code = "0b101";

        let expected = Pattern::integer(5).nowhere();

        check_parse!(code, pattern, Ok(expected));
    }

    #[test]
    fn bool_patterns_work() {
        let code = "true";

        let expected = Pattern::Bool(true).nowhere();

        check_parse!(code, pattern, Ok(expected));
    }

    #[test]
    fn positional_type_patterns_work() {
        let code = "SomeType(x, y)";

        let expected = Pattern::Type(
            ast_path("SomeType"),
            ArgumentPattern::Positional(vec![Pattern::name("x"), Pattern::name("y")]).nowhere(),
        )
        .nowhere();

        check_parse!(code, pattern, Ok(expected));
    }

    #[test]
    fn named_type_patterns_work() {
        let code = "SomeType$(x: a, y)";

        let expected = Pattern::Type(
            ast_path("SomeType"),
            ArgumentPattern::Named(vec![
                (ast_ident("x"), Some(Pattern::name("a"))),
                (ast_ident("y"), None),
            ])
            .nowhere(),
        )
        .nowhere();

        check_parse!(code, pattern, Ok(expected));
    }

    #[test]
    fn modules_can_be_empty() {
        let code = r#"mod X {}"#;

        let expected = ModuleBody {
            members: vec![Item::Module(
                Module {
                    visibility: Visibility::Implicit.nowhere(),
                    name: ast_ident("X"),
                    body: ModuleBody {
                        members: vec![],
                        documentation: vec![],
                    }
                    .nowhere(),
                    attributes: AttributeList::empty(),
                }
                .nowhere(),
            )],
            documentation: vec![],
        };

        check_parse!(code, module_body, Ok(expected));
    }

    #[test]
    fn modules_containing_items_work() {
        let code = r#"mod X {mod Y {}}"#;

        let expected = ModuleBody {
            members: vec![Item::Module(
                Module {
                    visibility: Visibility::Implicit.nowhere(),
                    name: ast_ident("X"),
                    body: ModuleBody {
                        members: vec![Item::Module(
                            Module {
                                visibility: Visibility::Implicit.nowhere(),
                                name: ast_ident("Y"),
                                body: ModuleBody {
                                    members: vec![],
                                    documentation: vec![],
                                }
                                .nowhere(),
                                attributes: AttributeList::empty(),
                            }
                            .nowhere(),
                        )],
                        documentation: vec![],
                    }
                    .nowhere(),
                    attributes: AttributeList::empty(),
                }
                .nowhere(),
            )],
            documentation: vec![],
        };

        check_parse!(code, module_body, Ok(expected));
    }
}
