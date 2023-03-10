mod comptime;
pub mod error;
pub mod error_reporting;
mod expression;
pub mod item_type;
pub mod lexer;

use colored::*;
use error::{ExpectedArgumentList, SuggestBraceEnumVariant};
use local_impl::local_impl;
use logos::Lexer;
use num::{BigInt, ToPrimitive, Zero};
use tracing::{event, Level};

use spade_ast::{
    ArgumentList, ArgumentPattern, AttributeList, Block, CallKind, ComptimeConfig, Enum,
    Expression, FunctionDecl, ImplBlock, IntLiteral, Item, Module, ModuleBody, NamedArgument,
    ParameterList, Pattern, PipelineStageReference, Register, Statement, Struct, TraitDef,
    TypeDeclKind, TypeDeclaration, TypeExpression, TypeParam, TypeSpec, Unit, UnitKind,
    UseStatement,
};
use spade_common::location_info::{lspan, AsLabel, FullSpan, HasCodespan, Loc, WithLocation};
use spade_common::name::{Identifier, Path};
use spade_diagnostics::Diagnostic;
use spade_macros::trace_parser;

use crate::error::{
    CSErrorTransformations, CommaSeparatedError, CommaSeparatedResult, Error, Result,
};
use crate::error_reporting::unexpected_token_message;
use crate::item_type::UnitKindLocal;
use crate::lexer::TokenKind;

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
    fn codespan(&self) -> codespan::Span {
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
        }
    }
}

/// Peek the next token. If it matches the specified token, get that token
/// otherwise return Ok(none)
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
            Ok(Identifier(name).at(self.file_id, &token.span))
        } else {
            unreachable!("eat_cond should have checked this");
        }
    }

    #[trace_parser]
    pub fn path(&mut self) -> Result<Loc<Path>> {
        let mut result = vec![];
        loop {
            result.push(self.identifier()?);

            if self.peek_and_eat(&TokenKind::PathSeparator)?.is_none() {
                break;
            }
        }
        // NOTE: (safe unwrap) The vec will have at least one element because the first thing
        // in the loop must pus an identifier.
        let start = result.first().unwrap().span;
        let end = result.last().unwrap().span;
        Ok(Path(result).between(self.file_id, &start, &end))
    }

    #[trace_parser]
    fn array_literal(&mut self) -> Result<Option<Loc<Expression>>> {
        let start = peek_for!(self, &TokenKind::OpenBracket);

        let inner = self
            .comma_separated(Self::expression, &TokenKind::CloseBracket)
            .no_context()?;

        let end = self.eat(&TokenKind::CloseBracket)?;

        Ok(Some(Expression::ArrayLiteral(inner).between(
            self.file_id,
            &start,
            &end,
        )))
    }

    #[trace_parser]
    fn tuple_literal(&mut self) -> Result<Option<Loc<Expression>>> {
        let start = peek_for!(self, &TokenKind::OpenParen);

        let mut inner = self
            .comma_separated(Self::expression, &TokenKind::CloseParen)
            .no_context()?;
        let result = if inner.is_empty() {
            let end = self.eat_unconditional()?;
            // NOTE: Early return because we have now consumed the closing paren
            return Err(Diagnostic::error(
                ().between(self.file_id, &start, &end),
                "Tuples of 0 elements are not supported",
            )
            .into());
        } else if inner.len() == 1 {
            // NOTE: safe unwrap, we know the size of the array
            Ok(inner.pop().unwrap())
        } else {
            let span = inner
                .first()
                .unwrap()
                .span
                .merge(inner.last().unwrap().span);
            Ok(Expression::TupleLiteral(inner).at(self.file_id, &span))
        };
        self.eat(&TokenKind::CloseParen)?;
        result.map(Some)
    }

    #[trace_parser]
    #[tracing::instrument(skip(self))]
    fn entity_instance(&mut self) -> Result<Option<Loc<Expression>>> {
        let start = peek_for!(self, &TokenKind::Instance);
        let start_loc = ().at(self.file_id, &start);

        self.unit_context
            .allows_inst(().at(self.file_id, &start.span()))?;
        // Check if this is a pipeline or not
        let pipeline_depth = if self.peek_kind(&TokenKind::OpenParen)? {
            Some(self.surrounded(
                &TokenKind::OpenParen,
                |s| {
                    s.maybe_comptime(&|s| {
                        s.int_literal()?.or_error(s, |p| {
                            Ok(Error::ExpectedPipelineDepth {
                                got: p.eat_unconditional()?,
                            })
                        })
                    })
                },
                &TokenKind::CloseParen,
            )?)
        } else {
            None
        };

        let name = self.path()?;
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
                }
                .between(self.file_id, &start.span, &args),
            ))
        } else {
            Ok(Some(
                Expression::Call {
                    kind: CallKind::Entity(start_loc),
                    callee: name,
                    args: args.clone(),
                }
                .between(self.file_id, &start.span, &args),
            ))
        }
    }

    #[trace_parser]
    pub fn if_expression(&mut self) -> Result<Option<Loc<Expression>>> {
        let start = peek_for!(self, &TokenKind::If);

        let cond = self.expression()?;

        let on_true = self.expression()?;
        self.eat(&TokenKind::Else)?;
        let (on_false, end_span) = self.expression()?.separate();

        Ok(Some(
            Expression::If(Box::new(cond), Box::new(on_true), Box::new(on_false)).between(
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
                        s.eat(&TokenKind::FatArrow)?;
                        let value = s.expression()?;

                        Ok((pattern, value))
                    },
                    &TokenKind::CloseBrace,
                )
                .no_context()
            },
            &TokenKind::CloseBrace,
        )?;
        let patterns = patterns.at_loc(&body_loc);

        Ok(Some(
            Expression::Match(Box::new(expression), patterns).between(
                self.file_id,
                &start.span,
                &body_loc,
            ),
        ))
    }

    #[trace_parser]
    pub fn int_literal(&mut self) -> Result<Option<Loc<IntLiteral>>> {
        if self.peek_cond(TokenKind::is_integer, "integer")? {
            let token = self.eat_unconditional()?;
            match &token.kind {
                TokenKind::Integer(val)
                | TokenKind::HexInteger(val)
                | TokenKind::BinInteger(val) => {
                    let (val_int, sign) = val;

                    let inner = match sign {
                        crate::lexer::LiteralKind::Signed => IntLiteral::Signed(val_int.clone()),
                        crate::lexer::LiteralKind::Unsigned => {
                            if val_int < &BigInt::zero() {
                                return Err(Diagnostic::error(
                                    token,
                                    "An unsigned int literal can not be negative",
                                )
                                .into());
                            } else {
                                IntLiteral::Unsigned(val_int.to_biguint().unwrap())
                            }
                        }
                    };
                    Ok(Some(Loc::new(inner, lspan(token.span), self.file_id)))
                }
                _ => unreachable!(),
            }
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
    #[tracing::instrument(skip(self))]
    pub fn block(&mut self, is_pipeline: bool) -> Result<Option<Loc<Block>>> {
        let start = peek_for!(self, &TokenKind::OpenBrace);

        let statements = self.statements(is_pipeline)?;
        let output_value = self.non_comptime_expression()?;
        let end = self.eat(&TokenKind::CloseBrace)?;

        Ok(Some(
            Block {
                statements,
                result: output_value,
            }
            .between(self.file_id, &start.span, &end.span),
        ))
    }

    #[trace_parser]
    pub fn pipeline_reference(&mut self) -> Result<Option<Loc<Expression>>> {
        let start = peek_for!(self, &TokenKind::Stage);

        self.eat(&TokenKind::OpenParen)?;

        let next = self.peek()?;
        let reference = match next.kind {
            TokenKind::Identifier(_) => PipelineStageReference::Absolute(self.identifier()?),
            TokenKind::Plus => {
                let plus = self.eat(&TokenKind::Plus)?;
                let num = if let Some(d) = self.int_literal()? {
                    d
                } else {
                    return Err(Error::ExpectedOffset {
                        got: self.eat_unconditional()?,
                    });
                };

                let offset = (num.inner.clone().as_signed()).between(plus.file_id, &plus, &num);
                PipelineStageReference::Relative(offset)
            }
            _ => {
                let num = if let Some(d) = self.int_literal()? {
                    d
                } else {
                    return Err(Error::UnexpectedToken {
                        got: next,
                        expected: vec!["integer", "identifier"],
                    });
                };
                let offset = num.map(IntLiteral::as_signed);
                PipelineStageReference::Relative(offset)
            }
        };

        let close_paren = self.eat(&TokenKind::CloseParen)?;

        self.eat(&TokenKind::Dot)?;

        let ident = self.identifier()?;

        Ok(Some(
            Expression::PipelineReference {
                stage_kw_and_reference_loc: ().between(
                    self.file_id,
                    &start.span,
                    &close_paren.span,
                ),
                stage: reference,
                name: ident.clone(),
            }
            .between(self.file_id, &start.span, &ident),
        ))
    }

    #[trace_parser]
    fn argument_list(&mut self) -> Result<Option<Loc<ArgumentList>>> {
        let is_named = self.peek_and_eat(&TokenKind::Dollar)?.is_some();
        let opener = peek_for!(self, &TokenKind::OpenParen);

        let argument_list = if is_named {
            let args = self
                .comma_separated(Self::named_argument, &TokenKind::CloseParen)
                .extra_expected(vec![":"])?
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
            match val.inner.clone().as_unsigned() {
                Some(u) => Ok(TypeExpression::Integer(u).at_loc(&val)),
                None => Err(Diagnostic::error(val, "Negative type level integer")
                    .primary_label("Type level integers must be positive")
                    .into()),
            }
        } else {
            let inner = self.type_spec()?;

            Ok(TypeExpression::TypeSpec(Box::new(inner.clone())).at_loc(&inner))
        }
    }

    // Types
    #[trace_parser]
    pub fn type_spec(&mut self) -> Result<Loc<TypeSpec>> {
        let wire_sign = self.peek_and_eat(&TokenKind::Ampersand)?;
        let mut_sign = if wire_sign.is_some() {
            self.peek_and_eat(&TokenKind::Mut)?
        } else {
            None
        };

        let inner = if let Some(tuple) = self.tuple_spec()? {
            tuple
        } else if let Some(array) = self.array_spec()? {
            array
        } else {
            // Single type, maybe with generics
            let (path, span) = self
                .path()
                .map_err(|e| e.specify_unexpected_token(Error::ExpectedType))?
                .separate();

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

            let span_end = generics.as_ref().map(|g| g.span.clone()).unwrap_or(span);
            TypeSpec::Named(path, generics).between(self.file_id, &span, &span_end)
        };

        let result = match (wire_sign, mut_sign) {
            (Some(wire), Some(_mut)) => TypeSpec::Backward(Box::new(inner.clone())).between(
                self.file_id,
                &wire.span,
                &inner,
            ),
            (Some(wire), None) => {
                TypeSpec::Wire(Box::new(inner.clone())).between(self.file_id, &wire.span, &inner)
            }
            (None, _) => inner,
        };

        Ok(result)
    }

    #[trace_parser]
    pub fn tuple_spec(&mut self) -> Result<Option<Loc<TypeSpec>>> {
        let start = peek_for!(self, &TokenKind::OpenParen);

        let inner = self
            .comma_separated(Self::type_spec, &TokenKind::CloseParen)
            .no_context()?;
        let end = self.eat(&TokenKind::CloseParen)?;

        let span = lspan(start.span).merge(lspan(end.span));

        Ok(Some(TypeSpec::Tuple(inner).at(self.file_id, &span)))
    }

    #[trace_parser]
    pub fn array_spec(&mut self) -> Result<Option<Loc<TypeSpec>>> {
        let start = peek_for!(self, &TokenKind::OpenBracket);

        let inner = self.type_spec()?;

        if let Some(end) = self.peek_and_eat(&TokenKind::CloseBracket)? {
            return Err(Error::ExpectedArraySize {
                array: ().between(self.file_id, &start, &end),
                inner,
            });
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
    pub fn name_and_type(&mut self) -> Result<(Loc<Identifier>, Loc<TypeSpec>)> {
        let name = self.identifier()?;
        self.eat(&TokenKind::Colon)?;
        let t = self.type_spec()?;
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
                Ok(s.int_literal()?
                    // Map option, then map Loc
                    .map(|val| val.map(Pattern::Integer)))
            },
            &|s| {
                Ok(s.bool_literal()?
                    // Map option, then map Loc
                    .map(|val| val.map(Pattern::Bool)))
            },
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
            Err(Error::UnexpectedToken {
                got: self.eat_unconditional()?,
                expected: vec!["Pattern"],
            })
        }
    }

    // Statements

    #[trace_parser]
    pub fn binding(&mut self) -> Result<Option<Loc<Statement>>> {
        peek_for!(self, &TokenKind::Let);

        let (pattern, start_span) = self.pattern()?.separate();

        let t = if self.peek_and_eat(&TokenKind::Colon)?.is_some() {
            Some(self.type_spec()?)
        } else {
            None
        };

        self.eat(&TokenKind::Assignment)?;
        let (value, end_span) = self.expression()?.separate();

        Ok(Some(Statement::Binding(pattern, t, value).between(
            self.file_id,
            &start_span,
            &end_span,
        )))
    }

    #[trace_parser]
    pub fn register_reset_definition(&mut self) -> Result<(Loc<Expression>, Loc<Expression>)> {
        let condition = self.expression()?;
        self.eat(&TokenKind::Colon)?;
        let value = self.expression()?;

        Ok((condition, value))
    }

    #[trace_parser]
    pub fn register(&mut self) -> Result<Option<Loc<Statement>>> {
        let start_token = peek_for!(self, &TokenKind::Reg);

        // If this is a reg marker for a pipeline
        if self.peek_kind(&TokenKind::Semi)? || self.peek_kind(&TokenKind::Asterisk)? {
            let count = if self.peek_and_eat(&TokenKind::Asterisk)?.is_some() {
                if let Some(val) = self.int_literal()? {
                    val.inner
                        .clone()
                        .as_unsigned()
                        .ok_or_else(|| {
                            Diagnostic::error(&val, "Negative number of registers")
                                .primary_label("Expected positive number of stages")
                        })?
                        .to_usize()
                        .ok_or_else(|| {
                            Diagnostic::bug(&val, "Excessive number of registers").primary_label(
                                format!("At most {} registers are supported", usize::MAX),
                            )
                        })?
                } else {
                    return Err(Error::ExpectedRegisterCount {
                        got: self.eat_unconditional()?,
                    });
                }
            } else {
                1
            };

            return Ok(Some(
                Statement::PipelineRegMarker(count).at(self.file_id, &start_token),
            ));
        }

        self.unit_context
            .allows_reg(().at(self.file_id, &start_token.span()))?;

        // Clock selection
        let (clock, _clock_paren_span) = self.surrounded(
            &TokenKind::OpenParen,
            |s| s.expression().map(Some),
            &TokenKind::CloseParen,
        )?;

        // Identifier parsing can not fail since we map it into a Some. Therefore,
        // unwrap is safe
        let clock = clock.unwrap();

        // Name
        let pattern = self.pattern()?;

        // Optional type
        let value_type = if self.peek_and_eat(&TokenKind::Colon)?.is_some() {
            Some(self.type_spec()?)
        } else {
            None
        };

        // Optional reset
        let reset = if self.peek_and_eat(&TokenKind::Reset)?.is_some() {
            let (reset, _) = self.surrounded(
                &TokenKind::OpenParen,
                |s| s.register_reset_definition().map(Some),
                &TokenKind::CloseParen,
            )?;
            reset
        } else {
            None
        };

        // Value
        self.eat(&TokenKind::Assignment)?;
        let (value, end_span) = self.expression()?.separate();

        let span = lspan(start_token.span).merge(end_span);
        let result = Statement::Register(
            Register {
                pattern,
                clock,
                reset,
                value,
                value_type,
            }
            .at(self.file_id, &span),
        )
        .at(self.file_id, &span);
        Ok(Some(result))
    }

    #[trace_parser]
    pub fn declaration(&mut self) -> Result<Option<Loc<Statement>>> {
        let start_token = peek_for!(self, &TokenKind::Decl);

        let mut identifiers = vec![];
        while self.peek_cond(|t| t.is_identifier(), "expected identifier")? {
            identifiers.push(self.identifier()?);

            if self.peek_and_eat(&TokenKind::Comma)?.is_none() {
                break;
            }
        }

        if identifiers.is_empty() {
            return Err(Error::EmptyDeclStatement {
                at: ().at(self.file_id, &start_token.span),
            });
        }

        let last_ident = identifiers.last().unwrap().clone();

        Ok(Some(Statement::Declaration(identifiers).between(
            self.file_id,
            &start_token.span,
            &last_ident,
        )))
    }

    #[trace_parser]
    pub fn label(&mut self) -> Result<Option<Loc<Statement>>> {
        let tok = peek_for!(self, &TokenKind::SingleQuote);

        let name = self.identifier()?;
        Ok(Some(Statement::Label(name.clone()).between(
            self.file_id,
            &tok.span,
            &name,
        )))
    }

    #[trace_parser]
    pub fn assert(&mut self) -> Result<Option<Loc<Statement>>> {
        let tok = peek_for!(self, &TokenKind::Assert);

        let expr = self.expression()?;

        Ok(Some(Statement::Assert(expr.clone()).between(
            self.file_id,
            &tok.span,
            &expr,
        )))
    }

    #[trace_parser]
    pub fn comptime_statement(&mut self, allow_stages: bool) -> Result<Option<Loc<Statement>>> {
        let inner = |s: &mut Self| s.exhaustive_statements(allow_stages, &TokenKind::CloseBrace);

        let result = self.comptime_condition(&inner, &|condition, loc| {
            Statement::Comptime(condition).at_loc(&loc)
        });
        result
    }

    #[trace_parser]
    pub fn set(&mut self) -> Result<Option<Loc<Statement>>> {
        let tok = peek_for!(self, &TokenKind::Set);

        let target = self.expression()?;

        self.eat(&TokenKind::Assignment)?;

        let value = self.expression()?;

        Ok(Some(
            Statement::Set {
                target,
                value: value.clone(),
            }
            .between(self.file_id, &tok.span, &value),
        ))
    }

    /// If the next token is the start of a statement, return that statement,
    /// otherwise None
    #[trace_parser]
    #[tracing::instrument(skip(self))]
    pub fn statement(&mut self, allow_stages: bool) -> Result<Option<Loc<Statement>>> {
        let result = self.first_successful(vec![
            &Self::binding,
            &Self::register,
            &Self::declaration,
            &Self::label,
            &Self::assert,
            &Self::set,
            &|s| s.comptime_statement(allow_stages),
        ])?;

        if let Some(statement) = &result {
            if let Statement::Label(_) | Statement::Comptime(_) = statement.inner {
            } else {
                self.eat(&TokenKind::Semi)?;
            }

            if let Statement::PipelineRegMarker(_) = statement.inner {
                if !allow_stages {
                    return Err(Error::StageOutsidePipeline(statement.loc()));
                }
            }
        }
        Ok(result)
    }

    #[trace_parser]
    pub fn statements(&mut self, allow_stages: bool) -> Result<Vec<Loc<Statement>>> {
        let mut result = vec![];
        while let Some(statement) = self.statement(allow_stages)? {
            result.push(statement)
        }
        Ok(result)
    }

    pub fn exhaustive_statements(
        &mut self,
        allow_stages: bool,
        end_token: &TokenKind,
    ) -> Result<Vec<Loc<Statement>>> {
        let result = self.statements(allow_stages)?;

        let next = self.peek()?;
        if &next.kind == end_token {
            Ok(result)
        } else {
            Err(Error::UnexpectedToken {
                got: next,
                expected: vec![end_token.as_str(), "statement"],
            })
        }
    }

    #[trace_parser]
    pub fn self_arg(&mut self) -> Result<Option<Loc<()>>> {
        if self.peek_cond(
            |t| t == &TokenKind::Identifier("self".to_string()),
            "looking for self",
        )? {
            let tok = self.eat_unconditional()?;
            Ok(Some(().at(self.file_id, &tok.span)))
        } else {
            Ok(None)
        }
    }

    #[trace_parser]
    pub fn parameter_list(&mut self) -> Result<ParameterList> {
        let self_ = if self.peek_cond(
            |tok| tok == &TokenKind::Identifier(String::from("self")),
            "Expected argument",
        )? {
            let self_tok = self.eat_unconditional()?;
            self.peek_and_eat(&TokenKind::Comma)?;
            Some(().at(self.file_id, &self_tok))
        } else {
            None
        };

        Ok(ParameterList {
            self_,
            args: self
                .comma_separated(Self::name_and_type, &TokenKind::CloseParen)
                .no_context()?,
        })
    }

    #[tracing::instrument(skip(self))]
    pub fn type_parameter_list(&mut self) -> Result<ParameterList> {
        Ok(ParameterList::without_self(
            self.comma_separated(Self::name_and_type, &TokenKind::CloseBrace)
                .no_context()?,
        ))
    }

    #[trace_parser]
    pub fn type_param(&mut self) -> Result<Loc<TypeParam>> {
        // If this is a type level integer
        if let Some(hash) = self.peek_and_eat(&TokenKind::Hash)? {
            let (id, loc) = self.identifier()?.separate();
            Ok(TypeParam::Integer(id).between(self.file_id, &hash.span, &loc))
        } else {
            let (id, loc) = self.identifier()?.separate();
            Ok(TypeParam::TypeName(id).at(self.file_id, &loc))
        }
    }

    #[trace_parser]
    pub fn generics_list(&mut self) -> Result<Vec<Loc<TypeParam>>> {
        if self.peek_kind(&TokenKind::Lt)? {
            let (params, _) = self.surrounded(
                &TokenKind::Lt,
                |s| {
                    s.comma_separated(Self::type_param, &TokenKind::Gt)
                        .extra_expected(vec!["type parameter"])
                },
                &TokenKind::Gt,
            )?;
            Ok(params)
        } else {
            Ok(vec![])
        }
    }

    fn disallow_attributes(&self, attributes: &AttributeList, item_start: &Token) -> Result<()> {
        if attributes.0.is_empty() {
            Ok(())
        } else {
            Err(Error::DisallowedAttributes {
                attributes: ().between(
                    self.file_id,
                    attributes.0.first().unwrap(),
                    attributes.0.last().unwrap(),
                ),
                item_start: Loc::new(
                    item_start.clone().kind,
                    lspan(item_start.span.clone()),
                    self.file_id,
                ),
            })
        }
    }

    // Entities
    #[trace_parser]
    #[tracing::instrument(skip(self))]
    pub fn unit(&mut self, attributes: &AttributeList) -> Result<Option<Loc<Unit>>> {
        let start_token = self.peek()?;
        let unit_kind = match start_token.kind {
            TokenKind::Pipeline => {
                self.eat_unconditional()?;

                let (depth, depth_span) = self.surrounded(
                    &TokenKind::OpenParen,
                    |s| {
                        s.maybe_comptime(&|s| {
                            s.int_literal()?.or_error(s, |p| {
                                Ok(Error::ExpectedPipelineDepth {
                                    got: p.eat_unconditional()?,
                                })
                            })
                        })
                    },
                    &TokenKind::CloseParen,
                )?;

                UnitKind::Pipeline(depth).between(self.file_id, &start_token, &depth_span)
            }
            TokenKind::Function => {
                self.eat_unconditional()?;
                UnitKind::Function.at(self.file_id, &start_token)
            }
            TokenKind::Entity => {
                self.eat_unconditional()?;
                UnitKind::Entity.at(self.file_id, &start_token)
            }
            _ => return Ok(None),
        };

        self.set_item_context(unit_kind.clone())?;

        let name = self.identifier()?;

        let type_params = self.generics_list()?;

        // Input types
        let (inputs, inputs_loc) = self.surrounded(
            &TokenKind::OpenParen,
            Self::parameter_list,
            &TokenKind::CloseParen,
        )?;
        let inputs = inputs.at_loc(&inputs_loc);

        // Return type
        let output_type = if self.peek_and_eat(&TokenKind::SlimArrow)?.is_some() {
            Some(self.type_spec()?)
        } else {
            None
        };

        let allow_stages = unit_kind.is_pipeline();
        let (block, block_span) = if let Some(block) = self.block(allow_stages)? {
            let (block, block_span) = block.separate();
            (Some(block), block_span)
        } else if self.peek_kind(&TokenKind::Builtin)? {
            let tok = self.eat_unconditional()?;

            (None, ().at(self.file_id, &tok.span).span)
        } else {
            // The end of the entity definition depends on whether or not
            // a type is present.
            let end_loc = output_type
                .map(|t| t.loc())
                .unwrap_or_else(|| inputs_loc)
                .span;

            let rest_loc = Loc::new((), lspan(start_token.span).merge(end_loc), self.file_id);
            let next = self.peek()?;
            return Err(Diagnostic::error(
                next.clone(),
                format!(
                    "Unexpected `{}`, expected body or `{}`",
                    next.kind.as_str(),
                    TokenKind::Builtin.as_str()
                ),
            )
            .primary_label(format!("Unexpected {}", &next.kind.as_str()))
            .secondary_label(rest_loc, format!("Expected body for this {unit_kind}"))
            .into());
        };

        self.clear_item_context();

        Ok(Some(
            Unit {
                attributes: attributes.clone(),
                unit_kind,
                name,
                inputs,
                output_type,
                body: block.map(|inner| inner.map(|inner| Expression::Block(Box::new(inner)))),
                type_params,
            }
            .between(self.file_id, &start_token.span, &block_span),
        ))
    }

    // Traits
    #[trace_parser]
    pub fn function_decl(
        &mut self,
        attributes: &AttributeList,
    ) -> Result<Option<Loc<FunctionDecl>>> {
        let start_token = peek_for!(self, &TokenKind::Function);

        self.disallow_attributes(attributes, &start_token)?;

        let name = self.identifier()?;

        let type_params = self.generics_list()?;

        let (inputs, inputs_loc) = self.surrounded(
            &TokenKind::OpenParen,
            Self::parameter_list,
            &TokenKind::CloseParen,
        )?;

        // Return type
        let return_type = if self.peek_and_eat(&TokenKind::SlimArrow)?.is_some() {
            Some(self.type_spec()?)
        } else {
            None
        };

        let end_token = self.eat(&TokenKind::Semi)?;

        Ok(Some(
            FunctionDecl {
                name,
                inputs: inputs.at_loc(&inputs_loc),
                return_type,
                type_params,
            }
            .between(self.file_id, &start_token.span, &end_token.span),
        ))
    }

    #[trace_parser]
    #[tracing::instrument(skip(self))]
    pub fn trait_def(&mut self, attributes: &AttributeList) -> Result<Option<Loc<TraitDef>>> {
        let start_token = peek_for!(self, &TokenKind::Trait);
        self.disallow_attributes(attributes, &start_token)?;

        let name = self.identifier()?;

        let mut result = TraitDef {
            name,
            functions: vec![],
        };

        self.eat(&TokenKind::OpenBrace)?;

        while let Some(decl) = self.function_decl(&AttributeList::empty())? {
            result.functions.push(decl);
        }
        let end_token = self.eat(&TokenKind::CloseBrace)?;

        Ok(Some(result.between(
            self.file_id,
            &start_token.span,
            &end_token.span,
        )))
    }

    #[trace_parser]
    #[tracing::instrument(level = "debug", skip(self))]
    pub fn impl_block(&mut self, attributes: &AttributeList) -> Result<Option<Loc<ImplBlock>>> {
        let start_token = peek_for!(self, &TokenKind::Impl);
        self.disallow_attributes(&attributes, &start_token)?;

        let trait_or_target = self.path()?;

        let (r#trait, target) = if self.peek_and_eat(&TokenKind::For)?.is_some() {
            let target = self.path()?;
            (Some(trait_or_target), target)
        } else {
            (None, trait_or_target)
        };

        let (body, body_span) = self.surrounded(
            &TokenKind::OpenBrace,
            Self::impl_body,
            &TokenKind::CloseBrace,
        )?;

        Ok(Some(
            ImplBlock {
                r#trait,
                target,
                units: body,
            }
            .between(self.file_id, &start_token.span, &body_span.span),
        ))
    }

    #[trace_parser]
    pub fn impl_body(&mut self) -> Result<Vec<Loc<Unit>>> {
        let mut result = vec![];
        while let Some(u) = self.unit(&AttributeList::empty())? {
            if u.unit_kind.is_pipeline() {
                return Err(Diagnostic::error(
                    u.unit_kind.loc(),
                    "Pipelines are currently not allowed in impl blocks",
                )
                .primary_label("Not allowed here")
                .note("This limitation is likely to be lifted in the future")
                .help("Consider defining a free-standing pipeline for now")
                .into());
            }

            result.push(u);
        }

        Ok(result)
    }

    #[trace_parser]
    #[tracing::instrument(level = "debug", skip(self))]
    pub fn enum_option(&mut self) -> Result<(Loc<Identifier>, Option<Loc<ParameterList>>)> {
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
            return Err(err.into());
        };

        Ok((name, args))
    }

    fn maybe_suggest_brace_enum_variant(&mut self, err: &mut Diagnostic) -> Result<bool> {
        let open_paren = match self.peek_and_eat(&TokenKind::OpenParen)? {
            Some(open_paren) => open_paren.loc(),
            _ => return Ok(false),
        };
        let mut try_parameter_list = self.clone();
        if try_parameter_list.parameter_list().is_err() {
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

    #[trace_parser]
    #[tracing::instrument(skip(self))]
    pub fn enum_declaration(
        &mut self,
        attributes: &AttributeList,
    ) -> Result<Option<Loc<TypeDeclaration>>> {
        let start_token = peek_for!(self, &TokenKind::Enum);
        self.disallow_attributes(attributes, &start_token)?;

        let name = self.identifier()?;

        let generic_args = self.generics_list()?;

        let (options, options_loc) = self.surrounded(
            &TokenKind::OpenBrace,
            |s: &mut Self| {
                s.comma_separated(Self::enum_option, &TokenKind::CloseBrace)
                    .no_context()
            },
            &TokenKind::CloseBrace,
        )?;

        let result = TypeDeclaration {
            name: name.clone(),
            kind: TypeDeclKind::Enum(Enum { name, options }.between(
                self.file_id,
                &start_token.span,
                &options_loc,
            )),
            generic_args,
        }
        .between(self.file_id, &start_token.span, &options_loc);

        Ok(Some(result))
    }

    #[trace_parser]
    #[tracing::instrument(skip(self))]
    pub fn struct_declaration(
        &mut self,
        attributes: &AttributeList,
    ) -> Result<Option<Loc<TypeDeclaration>>> {
        let start_token = peek_for!(self, &TokenKind::Struct);
        self.disallow_attributes(attributes, &start_token)?;

        let port_keyword = self
            .peek_and_eat(&TokenKind::Port)?
            .map(|tok| ().at(self.file_id, &tok.span()));

        let name = self.identifier()?;

        let generic_args = self.generics_list()?;

        let (members, members_loc) = self.surrounded(
            &TokenKind::OpenBrace,
            Self::type_parameter_list,
            &TokenKind::CloseBrace,
        )?;
        let members = members.at_loc(&members_loc);

        let result = TypeDeclaration {
            name: name.clone(),
            kind: TypeDeclKind::Struct(
                Struct {
                    name,
                    members,
                    port_keyword,
                }
                .between(self.file_id, &start_token.span, &members_loc),
            ),
            generic_args,
        }
        .between(self.file_id, &start_token.span, &members_loc);

        Ok(Some(result))
    }

    #[trace_parser]
    #[tracing::instrument(skip(self))]
    pub fn type_declaration(
        &mut self,
        attributes: &AttributeList,
    ) -> Result<Option<Loc<TypeDeclaration>>> {
        // The head of all type declarations will be `(enum|struct|type...) Name<T, S, ...>`
        // since we want access to the name and type params, we'll parse all those three, then
        // defer to parsing the rest.
        self.first_successful(vec![&|s| Self::enum_declaration(s, attributes), &|s| {
            Self::struct_declaration(s, attributes)
        }])
    }

    #[trace_parser]
    pub fn module(&mut self, attributes: &AttributeList) -> Result<Option<Loc<Module>>> {
        let start = peek_for!(self, &TokenKind::Mod);
        self.disallow_attributes(attributes, &start)?;

        let name = self.identifier()?;

        let open_brace = self.peek()?;
        let (body, end) = self.surrounded(
            &TokenKind::OpenBrace,
            Self::module_body,
            &TokenKind::CloseBrace,
        )?;

        Ok(Some(
            Module {
                name,
                body: body.between(self.file_id, &open_brace.span, &end.span),
            }
            .between(self.file_id, &start, &end),
        ))
    }

    #[trace_parser]
    #[tracing::instrument(skip(self))]
    pub fn r#use(&mut self, attributes: &AttributeList) -> Result<Option<Loc<UseStatement>>> {
        let start = peek_for!(self, &TokenKind::Use);
        self.disallow_attributes(attributes, &start)?;

        let path = self.path()?;

        let alias = if (self.peek_and_eat(&TokenKind::As)?).is_some() {
            Some(self.identifier()?)
        } else {
            None
        };

        let end = self.eat(&TokenKind::Semi)?;

        Ok(Some(UseStatement { path, alias }.between(
            self.file_id,
            &start.span(),
            &end.span(),
        )))
    }

    #[trace_parser]
    #[tracing::instrument(skip(self))]
    pub fn comptime_item(
        &mut self,
        attributes: &AttributeList,
    ) -> Result<Option<Loc<ComptimeConfig>>> {
        let start = peek_for!(self, &TokenKind::ComptimeConfig);
        self.disallow_attributes(attributes, &start)?;

        let name = self.identifier()?;
        self.eat(&TokenKind::Assignment)?;

        let val = if let Some(v) = self.int_literal()? {
            v.map(IntLiteral::as_signed)
        } else {
            return Err(Error::UnexpectedToken {
                got: self.eat_unconditional()?,
                expected: vec!["integer"],
            });
        };

        Ok(Some(
            ComptimeConfig {
                name,
                val: val.clone(),
            }
            .between(self.file_id, &start.span(), &val.span()),
        ))
    }

    #[trace_parser]
    pub fn attributes(&mut self) -> Result<AttributeList> {
        // peek_for!(self, &TokenKind::Hash)
        let mut result = AttributeList(vec![]);
        while let Some(start) = self.peek_and_eat(&TokenKind::Hash)? {
            let (ident, loc) = self.surrounded(
                &TokenKind::OpenBracket,
                Self::identifier,
                &TokenKind::CloseBracket,
            )?;

            result
                .0
                .push(ident.inner.between(self.file_id, &start, &loc));
        }
        Ok(result)
    }

    #[trace_parser]
    #[tracing::instrument(skip(self))]
    pub fn item(&mut self) -> Result<Option<Item>> {
        let attrs = self.attributes()?;
        self.first_successful(vec![
            &|s: &mut Self| s.unit(&attrs).map(|e| e.map(Item::Unit)),
            &|s: &mut Self| s.trait_def(&attrs).map(|e| e.map(Item::TraitDef)),
            &|s: &mut Self| s.impl_block(&attrs).map(|e| e.map(Item::ImplBlock)),
            &|s: &mut Self| s.type_declaration(&attrs).map(|e| e.map(Item::Type)),
            &|s: &mut Self| s.module(&attrs).map(|e| e.map(Item::Module)),
            &|s: &mut Self| s.r#use(&attrs).map(|e| e.map(Item::Use)),
            &|s: &mut Self| s.comptime_item(&attrs).map(|e| e.map(Item::Config)),
        ])
    }

    #[trace_parser]
    #[tracing::instrument(skip(self))]
    pub fn module_body(&mut self) -> Result<ModuleBody> {
        let mut members = vec![];
        while let Some(item) = self.item()? {
            members.push(item)
        }
        Ok(ModuleBody { members })
    }

    /// A module body which is not part of a `mod`. Errors if there is anything
    /// but an item found after the last item
    #[trace_parser]
    #[tracing::instrument(skip(self))]
    pub fn top_level_module_body(&mut self) -> Result<ModuleBody> {
        let result = self.module_body()?;

        if self.peek_kind(&TokenKind::Eof)? {
            Ok(result)
        } else {
            Err(Error::ExpectedItem { got: self.peek()? })
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
    /// If the `start` token is found, but the inner parser returns `None`, `None` is returned.
    ///
    /// If the end token is not found, return a mismatch error
    #[tracing::instrument(level = "debug", skip(self, inner))]
    fn surrounded<T>(
        &mut self,
        start: &TokenKind,
        inner: impl Fn(&mut Self) -> Result<T>,
        end_kind: &TokenKind,
    ) -> Result<(T, Loc<()>)> {
        let opener = self.eat(start)?;
        let result = inner(self)?;
        // FIXME: Better error handling here. We are throwing away potential EOFs
        let end = if let Some(end) = self.peek_and_eat(end_kind)? {
            end
        } else {
            return Err(Error::UnmatchedPair {
                friend: opener,
                expected: end_kind.clone(),
                got: self.eat_unconditional()?,
            });
        };

        Ok((
            result,
            Loc::new((), lspan(opener.span).merge(lspan(end.span)), self.file_id),
        ))
    }

    // NOTE: This can not currently use #[trace_parser] as it returns an error which is not
    // convertible into `Error`. If we end up with more functions like this, that
    // macro should probably be made smarter
    #[tracing::instrument(level = "debug", skip(self, inner))]
    pub fn comma_separated<T>(
        &mut self,
        inner: impl Fn(&mut Self) -> Result<T>,
        // This end marker is used for allowing trailing commas. It should
        // be whatever ends the collection that is searched. I.e. (a,b,c,) should have
        // `)`, and {} should have `}`
        end_marker: &TokenKind,
    ) -> CommaSeparatedResult<Vec<T>> {
        self.parse_stack
            .push(ParseStackEntry::Enter("comma_separated".to_string()));
        let ret = || -> CommaSeparatedResult<Vec<T>> {
            let mut result = vec![];
            loop {
                // The list might be empty
                if self.peek_kind(end_marker)? {
                    break;
                }
                result.push(inner(self)?);

                // Now we expect to either find a comma, in which case we resume the
                // search, or an end marker, in which case we abort
                if self.peek_kind(end_marker)? {
                    break;
                } else if self.peek_kind(&TokenKind::Comma)? {
                    self.eat_unconditional()?;
                } else {
                    return Err(CommaSeparatedError::UnexpectedToken {
                        got: self.eat_unconditional()?,
                        end_token: end_marker.clone(),
                    });
                }
            }
            Ok(result)
        }();
        if let Err(e) = &ret {
            self.parse_stack
                .push(ParseStackEntry::ExitWithError(e.clone().no_context()));
        } else {
            self.parse_stack.push(ParseStackEntry::Exit);
        }

        ret
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
            Err(Error::UnexpectedToken {
                got: next,
                expected: vec![expected.as_str()],
            })
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
            Err(Error::UnexpectedToken {
                got: next,
                expected: vec![expected_description],
            })
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

    fn peek(&mut self) -> Result<Token> {
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
        let tok = self
            .lex
            .next()
            .map(|k| Token::new(k, &self.lex, self.file_id))
            .unwrap_or({
                match &self.last_token {
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
                }
            });

        if let TokenKind::Error = tok.kind {
            return Err(Error::LexerError(self.file_id, lspan(self.lex.span())));
        };

        Ok(tok)
    }
}

impl<'a> Parser<'a> {
    fn set_item_context(&mut self, context: Loc<UnitKind>) -> Result<()> {
        if let Some(prev) = &self.unit_context {
            Err(Error::InternalOverwritingItemContext {
                at: context.loc(),
                prev: prev.loc(),
            })
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

#[local_impl]
impl<T> OptionExt for Option<T> {
    fn or_error(
        self,
        parser: &mut Parser,
        err: impl Fn(&mut Parser) -> Result<Error>,
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
    ExitWithError(Error),
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
                format!("")
            }
            ParseStackEntry::ExitWithError(err) => {
                next_indent_amount -= 1;
                format!("{} {}", "Giving up: ".bright_red(), err)
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
    use ast::comptime::{ComptimeCondOp, ComptimeCondition, MaybeComptime};
    use spade_ast as ast;
    use spade_ast::testutil::{ast_ident, ast_path};
    use spade_ast::*;
    use spade_common::num_ext::{InfallibleToBigInt, InfallibleToBigUint};

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
        let expected = Path(vec![ast_ident("path"), ast_ident("to"), ast_ident("thing")]).nowhere();
        check_parse!("path::to::thing", path, Ok(expected));
    }

    #[test]
    fn literals_are_expressions() {
        check_parse!(
            "123",
            expression,
            Ok(Expression::int_literal(123).nowhere())
        );
    }

    #[test]
    fn bindings_work() {
        let expected = Statement::Binding(
            Pattern::name("test"),
            None,
            Expression::int_literal(123).nowhere(),
        )
        .nowhere();
        check_parse!("let test = 123;", binding, Ok(Some(expected)));
    }

    #[test]
    fn declarations_work() {
        let expected = Statement::Declaration(vec![ast_ident("x"), ast_ident("y")]).nowhere();

        check_parse!("decl x, y;", declaration, Ok(Some(expected)));
    }

    #[test]
    fn empty_declaration_results_in_error() {
        check_parse!(
            "decl;",
            declaration,
            Err(Error::EmptyDeclStatement { at: ().nowhere() })
        );
    }

    #[test]
    fn bindings_with_types_work() {
        let expected = Statement::Binding(
            Pattern::name("test"),
            Some(TypeSpec::Named(ast_path("bool"), None).nowhere()),
            Expression::int_literal(123).nowhere(),
        )
        .nowhere();
        check_parse!(
            "let test: bool = 123;",
            statement(false),
            Ok(Some(expected))
        );
    }

    #[test]
    fn entity_without_inputs() {
        let code = include_str!("../parser_test_code/entity_without_inputs.sp");
        let expected = Unit {
            attributes: AttributeList::empty(),
            unit_kind: UnitKind::Entity.nowhere(),
            name: Identifier("no_inputs".to_string()).nowhere(),
            inputs: aparams![],
            output_type: None,
            body: Some(
                Expression::Block(Box::new(Block {
                    statements: vec![
                        Statement::Binding(
                            Pattern::name("test"),
                            None,
                            Expression::int_literal(123).nowhere(),
                        )
                        .nowhere(),
                        Statement::Binding(
                            Pattern::name("test2"),
                            None,
                            Expression::int_literal(123).nowhere(),
                        )
                        .nowhere(),
                    ],
                    result: Expression::Identifier(ast_path("test")).nowhere(),
                }))
                .nowhere(),
            ),
            type_params: vec![],
        }
        .nowhere();

        check_parse!(code, unit(&AttributeList::empty()), Ok(Some(expected)));
    }

    #[test]
    fn entity_with_inputs() {
        let code = include_str!("../parser_test_code/entity_with_inputs.sp");
        let expected = Unit {
            attributes: AttributeList::empty(),
            unit_kind: UnitKind::Entity.nowhere(),
            name: ast_ident("with_inputs"),
            inputs: aparams![("clk", tspec!("bool")), ("rst", tspec!("bool"))],
            output_type: Some(TypeSpec::Named(ast_path("bool"), None).nowhere()),
            body: Some(
                Expression::Block(Box::new(Block {
                    statements: vec![],
                    result: Expression::Identifier(ast_path("clk")).nowhere(),
                }))
                .nowhere(),
            ),
            type_params: vec![],
        }
        .nowhere();

        check_parse!(code, unit(&AttributeList::empty()), Ok(Some(expected)));
    }

    #[test]
    fn entity_with_generics() {
        let code = include_str!("../parser_test_code/entity_with_generics.sp");
        let expected = Unit {
            attributes: AttributeList::empty(),
            unit_kind: UnitKind::Entity.nowhere(),
            name: ast_ident("with_generics"),
            inputs: aparams![],
            output_type: None,
            body: Some(
                Expression::Block(Box::new(Block {
                    statements: vec![],
                    result: Expression::Identifier(ast_path("clk")).nowhere(),
                }))
                .nowhere(),
            ),
            type_params: vec![
                TypeParam::TypeName(ast_ident("X")).nowhere(),
                TypeParam::Integer(ast_ident("Y")).nowhere(),
            ],
        }
        .nowhere();

        check_parse!(code, unit(&AttributeList::empty()), Ok(Some(expected)));
    }

    #[test]
    fn parsing_register_without_reset_works() {
        let code = "reg(clk) name = 1;";

        let expected = Statement::Register(
            Register {
                pattern: Pattern::name("name"),
                clock: Expression::Identifier(ast_path("clk")).nowhere(),
                reset: None,
                value: Expression::int_literal(1).nowhere(),
                value_type: None,
            }
            .nowhere(),
        )
        .nowhere();

        check_parse!(
            code,
            statement(false),
            Ok(Some(expected)),
            Parser::set_parsing_entity
        );
    }

    #[test]
    fn parsing_register_with_reset_works() {
        let code = "reg(clk) name reset (rst: 0) = 1;";

        let expected = Statement::Register(
            Register {
                pattern: Pattern::name("name"),
                clock: Expression::Identifier(ast_path("clk")).nowhere(),
                reset: Some((
                    Expression::Identifier(ast_path("rst")).nowhere(),
                    Expression::int_literal(0).nowhere(),
                )),
                value: Expression::int_literal(1).nowhere(),
                value_type: None,
            }
            .nowhere(),
        )
        .nowhere();

        check_parse!(
            code,
            statement(false),
            Ok(Some(expected)),
            Parser::set_parsing_entity
        );
    }

    #[test]
    fn parsing_register_with_reset_and_clock() {
        let code = "reg(clk) name: Type reset (rst: 0) = 1;";

        let expected = Statement::Register(
            Register {
                pattern: Pattern::name("name"),
                clock: Expression::Identifier(ast_path("clk")).nowhere(),
                reset: Some((
                    Expression::Identifier(ast_path("rst")).nowhere(),
                    Expression::int_literal(0).nowhere(),
                )),
                value: Expression::int_literal(1).nowhere(),
                value_type: Some(TypeSpec::Named(ast_path("Type"), None).nowhere()),
            }
            .nowhere(),
        )
        .nowhere();

        check_parse!(
            code,
            statement(false),
            Ok(Some(expected)),
            Parser::set_parsing_entity
        );
    }

    #[test]
    fn size_types_work() {
        let expected = TypeSpec::Named(
            ast_path("uint"),
            Some(vec![TypeExpression::Integer(10u32.to_biguint()).nowhere()].nowhere()),
        )
        .nowhere();
        check_parse!("uint<10>", type_spec, Ok(expected));
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
                        Some(vec![TypeExpression::Integer(5u32.to_biguint()).nowhere()].nowhere()),
                    )
                    .nowhere(),
                ))
                .nowhere()]
                .nowhere(),
            ),
        )
        .nowhere();

        check_parse!(code, type_spec, Ok(expected));
    }

    #[test]
    fn wire_type_specs_work() {
        let code = "&int<5>";

        let expected = TypeSpec::Wire(Box::new(
            TypeSpec::Named(
                ast_path("int"),
                Some(vec![TypeExpression::Integer(5u32.to_biguint()).nowhere()].nowhere()),
            )
            .nowhere(),
        ))
        .nowhere();

        check_parse!(code, type_spec, Ok(expected));
    }

    #[test]
    fn mut_wire_type_specs_work() {
        let code = "&mut int<5>";

        let expected = TypeSpec::Backward(Box::new(
            TypeSpec::Named(
                ast_path("int"),
                Some(vec![TypeExpression::Integer(5u32.to_biguint()).nowhere()].nowhere()),
            )
            .nowhere(),
        ))
        .nowhere();

        check_parse!(code, type_spec, Ok(expected));
    }

    #[test]
    fn module_body_parsing_works() {
        let code = include_str!("../parser_test_code/multiple_entities.sp");

        let e1 = Unit {
            attributes: AttributeList::empty(),
            unit_kind: UnitKind::Entity.nowhere(),
            name: Identifier("e1".to_string()).nowhere(),
            inputs: aparams![],
            output_type: None,
            body: Some(
                Expression::Block(Box::new(Block {
                    statements: vec![],
                    result: Expression::int_literal(0).nowhere(),
                }))
                .nowhere(),
            ),
            type_params: vec![],
        }
        .nowhere();

        let e2 = Unit {
            attributes: AttributeList::empty(),
            unit_kind: UnitKind::Entity.nowhere(),
            name: Identifier("e2".to_string()).nowhere(),
            inputs: aparams![],
            output_type: None,
            body: Some(
                Expression::Block(Box::new(Block {
                    statements: vec![],
                    result: Expression::int_literal(1).nowhere(),
                }))
                .nowhere(),
            ),
            type_params: vec![],
        }
        .nowhere();

        let expected = ModuleBody {
            members: vec![Item::Unit(e1), Item::Unit(e2)],
        };

        check_parse!(code, module_body, Ok(expected));
    }

    #[test]
    fn invalid_top_level_tokens_cause_errors() {
        let code = r#"+ x() -> bool {
            false
        }

        entity x() -> bool {
            false
        }
        "#;

        check_parse!(
            code,
            top_level_module_body,
            Err(Error::ExpectedItem {
                got: Token {
                    kind: TokenKind::Plus,
                    span: 0..1,
                    file_id: 0
                }
            })
        );
    }

    #[test]
    fn function_declarations_work() {
        let code = "fn some_fn(self, a: bit) -> bit;";

        let expected = FunctionDecl {
            name: ast_ident("some_fn"),
            inputs: aparams![self, ("a", tspec!("bit"))],
            return_type: Some(TypeSpec::Named(ast_path("bit"), None).nowhere()),
            type_params: vec![],
        }
        .nowhere();

        check_parse!(
            code,
            function_decl(&AttributeList::empty()),
            Ok(Some(expected))
        );
    }

    #[test]
    fn function_declarations_with_only_self_arg_work() {
        let code = "fn some_fn(self) -> bit;";

        let expected = FunctionDecl {
            name: ast_ident("some_fn"),
            inputs: aparams![self],
            return_type: Some(TypeSpec::Named(ast_path("bit"), None).nowhere()),
            type_params: vec![],
        }
        .nowhere();

        check_parse!(
            code,
            function_decl(&AttributeList::empty()),
            Ok(Some(expected))
        );
    }

    #[test]
    fn function_declarations_with_no_type_have_unit_type() {
        let code = "fn some_fn(self);";

        let expected = FunctionDecl {
            name: ast_ident("some_fn"),
            inputs: aparams![self],
            return_type: None,
            type_params: vec![],
        }
        .nowhere();

        check_parse!(
            code,
            function_decl(&AttributeList::empty()),
            Ok(Some(expected))
        );
    }

    #[test]
    fn function_decls_with_generic_type_works() {
        let code = "fn some_fn<X>(self);";

        let expected = FunctionDecl {
            name: ast_ident("some_fn"),
            inputs: aparams![self],
            return_type: None,
            type_params: vec![TypeParam::TypeName(ast_ident("X")).nowhere()],
        }
        .nowhere();

        check_parse!(
            code,
            function_decl(&AttributeList::empty()),
            Ok(Some(expected))
        );
    }

    #[test]
    fn trait_definitions_work() {
        let code = r#"
        trait SomeTrait {
            fn some_fn(self, a: bit) -> bit;
            fn another_fn(self) -> bit;
        }
        "#;

        let fn1 = FunctionDecl {
            name: ast_ident("some_fn"),
            inputs: aparams![self, ("a", tspec!("bit"))],
            return_type: Some(TypeSpec::Named(ast_path("bit"), None).nowhere()),
            type_params: vec![],
        }
        .nowhere();
        let fn2 = FunctionDecl {
            name: ast_ident("another_fn"),
            inputs: aparams![self],
            return_type: Some(TypeSpec::Named(ast_path("bit"), None).nowhere()),
            type_params: vec![],
        }
        .nowhere();

        let expected = TraitDef {
            name: ast_ident("SomeTrait"),
            functions: vec![fn1, fn2],
        }
        .nowhere();

        check_parse!(code, trait_def(&AttributeList::empty()), Ok(Some(expected)));
    }

    #[test]
    fn anonymous_impl_blocks_work() {
        let code = r#"
        impl SomeType {
            fn some_fn() __builtin__
        }
        "#;

        let expected = ImplBlock {
            r#trait: None,
            target: ast_path("SomeType"),
            units: vec![Unit {
                attributes: AttributeList::empty(),
                unit_kind: UnitKind::Function.nowhere(),
                name: ast_ident("some_fn"),
                inputs: ParameterList::without_self(vec![]).nowhere(),
                output_type: None,
                body: None,
                type_params: vec![],
            }
            .nowhere()],
        }
        .nowhere();

        check_parse!(
            code,
            impl_block(&AttributeList::empty()),
            Ok(Some(expected))
        );
    }

    #[test]
    fn non_anonymous_impl_blocks_work() {
        let code = r#"
        impl SomeTrait for SomeType {
            fn some_fn() __builtin__
        }
        "#;

        let expected = ImplBlock {
            r#trait: Some(ast_path("SomeTrait")),
            target: ast_path("SomeType"),
            units: vec![Unit {
                attributes: AttributeList::empty(),
                unit_kind: UnitKind::Function.nowhere(),
                name: ast_ident("some_fn"),
                inputs: ParameterList::without_self(vec![]).nowhere(),
                output_type: None,
                body: None,
                type_params: vec![],
            }
            .nowhere()],
        }
        .nowhere();

        check_parse!(
            code,
            impl_block(&AttributeList::empty()),
            Ok(Some(expected))
        );
    }

    #[test]
    fn typenames_parse() {
        let code = "X";

        let expected = TypeParam::TypeName(ast_ident("X")).nowhere();

        check_parse!(code, type_param(), Ok(expected));
    }

    #[test]
    fn typeints_parse() {
        let code = "#X";

        let expected = TypeParam::Integer(ast_ident("X")).nowhere();

        check_parse!(code, type_param(), Ok(expected));
    }

    #[test]
    fn dec_int_literals_work() {
        let code = "1";
        let expected = IntLiteral::signed(1).nowhere();

        check_parse!(code, int_literal, Ok(Some(expected)));
    }
    #[test]
    fn dec_uint_literals_work() {
        let code = "1u";
        let expected = IntLiteral::Unsigned(1u32.to_biguint()).nowhere();

        check_parse!(code, int_literal, Ok(Some(expected)));
    }
    #[test]
    fn dec_negative_int_literals_work() {
        let code = "-1";
        let expected = IntLiteral::signed(-1).nowhere();

        check_parse!(code, int_literal, Ok(Some(expected)));
    }
    #[test]
    fn hex_int_literals_work() {
        let code = "0xff";
        let expected = IntLiteral::signed(255).nowhere();

        check_parse!(code, int_literal, Ok(Some(expected)));
    }
    #[test]
    fn hex_uint_literals_work() {
        let code = "0xffu";
        let expected = IntLiteral::Unsigned(255u32.to_biguint()).nowhere();

        check_parse!(code, int_literal, Ok(Some(expected)));
    }
    #[test]
    fn bin_int_literals_work() {
        let code = "0b101";
        let expected = IntLiteral::signed(5).nowhere();

        check_parse!(code, int_literal, Ok(Some(expected)));
    }

    #[test]
    fn bin_uint_literals_work() {
        let code = "0b101u";
        let expected = IntLiteral::Unsigned(5u32.to_biguint()).nowhere();

        check_parse!(code, int_literal, Ok(Some(expected)));
    }

    #[test]
    fn array_type_specs_work() {
        let code = "[int; 5]";

        let expected = TypeSpec::Array {
            inner: Box::new(TypeSpec::Named(ast_path("int"), None).nowhere()),
            size: Box::new(TypeExpression::Integer(5u32.to_biguint()).nowhere()),
        }
        .nowhere();

        check_parse!(code, type_spec, Ok(expected));
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

        check_parse!(code, type_spec, Ok(expected));
    }

    #[test]
    fn builtin_entities_work() {
        let code = "entity X() __builtin__";

        let expected = Some(
            Unit {
                attributes: AttributeList::empty(),
                unit_kind: UnitKind::Entity.nowhere(),
                name: ast_ident("X"),
                inputs: ParameterList::without_self(vec![]).nowhere(),
                output_type: None,
                body: None,
                type_params: vec![],
            }
            .nowhere(),
        );

        check_parse!(code, unit(&AttributeList::empty()), Ok(expected));
    }

    #[test]
    fn builtin_pipelines_work() {
        let code = "pipeline(1) X() __builtin__";

        let expected = Some(
            Unit {
                attributes: AttributeList::empty(),
                name: ast_ident("X"),
                inputs: ParameterList::without_self(vec![]).nowhere(),
                output_type: None,
                unit_kind: UnitKind::Pipeline(
                    MaybeComptime::Raw(IntLiteral::signed(1).nowhere()).nowhere(),
                )
                .nowhere(),
                body: None,
                type_params: vec![],
            }
            .nowhere(),
        );

        check_parse!(code, unit(&AttributeList::empty()), Ok(expected));
    }

    #[test]
    fn builtin_functions_work() {
        let code = "fn X() __builtin__";

        let expected = Some(
            Unit {
                attributes: AttributeList::empty(),
                unit_kind: UnitKind::Function.nowhere(),
                name: ast_ident("X"),
                inputs: ParameterList::without_self(vec![]).nowhere(),
                output_type: None,
                body: None,
                type_params: vec![],
            }
            .nowhere(),
        );

        check_parse!(code, unit(&AttributeList::empty()), Ok(expected));
    }

    #[test]
    fn functions_can_have_attributes() {
        let code = r#"
            #[attr]
            fn X() __builtin__"#;

        let expected = Some(Item::Unit(
            Unit {
                attributes: AttributeList(vec![ast_ident("attr")]),
                unit_kind: UnitKind::Function.nowhere(),
                name: ast_ident("X"),
                inputs: ParameterList::without_self(vec![]).nowhere(),
                output_type: None,
                body: None,
                type_params: vec![],
            }
            .nowhere(),
        ));

        check_parse!(code, item, Ok(expected));
    }

    #[test]
    fn entities_can_have_attributes() {
        let code = r#"
            #[attr]
            entity X() __builtin__"#;

        let expected = Some(Item::Unit(
            Unit {
                attributes: AttributeList(vec![ast_ident("attr")]),
                unit_kind: UnitKind::Entity.nowhere(),
                name: ast_ident("X"),
                inputs: ParameterList::without_self(vec![]).nowhere(),
                output_type: None,
                body: None,
                type_params: vec![],
            }
            .nowhere(),
        ));

        check_parse!(code, item, Ok(expected));
    }

    #[test]
    fn pipelines_can_have_attributes() {
        let code = r#"
            #[attr]
            pipeline(2) test(a: bool) __builtin__
        "#;

        let expected = Item::Unit(
            Unit {
                attributes: AttributeList(vec![ast_ident("attr")]),
                unit_kind: UnitKind::Pipeline(
                    MaybeComptime::Raw(IntLiteral::signed(2).nowhere()).nowhere(),
                )
                .nowhere(),
                name: ast_ident("test"),
                inputs: aparams![("a", tspec!("bool"))],
                output_type: None,
                body: None,
                type_params: vec![],
            }
            .nowhere(),
        );

        check_parse!(code, item, Ok(Some(expected)));
    }

    #[test]
    fn functions_do_not_allow_regs() {
        let code = "fn X() {
            reg(clk) x;
            true
        }";

        check_parse!(
            code,
            unit(&AttributeList::empty()),
            Err(Error::RegInFunction {
                at: ().nowhere(),
                fn_keyword: ().nowhere()
            })
        );
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
        }
        .nowhere();

        check_parse!(code, expression, Ok(expected), Parser::set_parsing_entity);
    }

    #[test]
    fn entity_instantiation_with_a_named_arg() {
        let code = "inst some_entity$(z: a)";

        let expected = Expression::Call {
            kind: CallKind::Entity(().nowhere()),
            callee: ast_path("some_entity"),
            args: ArgumentList::Named(vec![NamedArgument::Full(
                ast_ident("z"),
                Expression::Identifier(ast_path("a")).nowhere(),
            )])
            .nowhere(),
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
    fn incorrect_named_args_gives_good_error() {
        let code = "$(x = a)";

        check_parse!(
            code,
            argument_list,
            Err(Error::UnexpectedToken {
                expected: vec![":", ",", ")"],
                got: Token {
                    kind: TokenKind::Assignment,
                    span: (4..5),
                    file_id: 0,
                },
            })
        );
    }

    #[test]
    fn named_capture_shorthand_works() {
        let code = "x";

        let expected = NamedArgument::Short(ast_ident("x")).nowhere();

        check_parse!(code, named_argument, Ok(expected));
    }

    #[test]
    fn pipeline_parsing_works() {
        let code = r#"
            pipeline(2) test(a: bool) -> bool {
                    's0
                reg;
                    let b = 0;
                reg;
                    's2
                    let c = 0;
                    0
            }
        "#;

        let expected = Unit {
            attributes: AttributeList::empty(),
            unit_kind: UnitKind::Pipeline(
                MaybeComptime::Raw(IntLiteral::signed(2).nowhere()).nowhere(),
            )
            .nowhere(),
            name: ast_ident("test"),
            inputs: aparams![("a", tspec!("bool"))],
            output_type: Some(TypeSpec::Named(ast_path("bool"), None).nowhere()),
            body: Some(
                Expression::Block(Box::new(Block {
                    statements: vec![
                        Statement::Label(ast_ident("s0")).nowhere(),
                        Statement::PipelineRegMarker(1).nowhere(),
                        Statement::Binding(
                            Pattern::name("b"),
                            None,
                            Expression::int_literal(0).nowhere(),
                        )
                        .nowhere(),
                        Statement::PipelineRegMarker(1).nowhere(),
                        Statement::Label(ast_ident("s2")).nowhere(),
                        Statement::Binding(
                            Pattern::name("c"),
                            None,
                            Expression::int_literal(0).nowhere(),
                        )
                        .nowhere(),
                    ],
                    result: Expression::int_literal(0).nowhere(),
                }))
                .nowhere(),
            ),
            type_params: vec![],
        }
        .nowhere();

        check_parse!(code, unit(&AttributeList::empty()), Ok(Some(expected)));
    }

    #[test]
    fn pipeline_parsing_with_many_regs_works() {
        let code = r#"
            pipeline(2) test(a: bool) -> bool {
                reg*3;
                    0
            }
        "#;

        let expected = Unit {
            attributes: AttributeList::empty(),
            unit_kind: UnitKind::Pipeline(
                MaybeComptime::Raw(IntLiteral::signed(2).nowhere()).nowhere(),
            )
            .nowhere(),
            name: ast_ident("test"),
            inputs: aparams![("a", tspec!("bool"))],
            output_type: Some(TypeSpec::Named(ast_path("bool"), None).nowhere()),
            body: Some(
                Expression::Block(Box::new(Block {
                    statements: vec![Statement::PipelineRegMarker(3).nowhere()],
                    result: Expression::int_literal(0).nowhere(),
                }))
                .nowhere(),
            ),
            type_params: vec![],
        }
        .nowhere();

        check_parse!(code, unit(&AttributeList::empty()), Ok(Some(expected)));
    }

    #[test]
    fn pipelines_are_items() {
        let code = r#"
            pipeline(2) test(a: bool) -> bool {
                0
            }
        "#;

        let expected = ModuleBody {
            members: vec![Item::Unit(
                Unit {
                    attributes: AttributeList::empty(),
                    unit_kind: UnitKind::Pipeline(
                        MaybeComptime::Raw(IntLiteral::signed(2).nowhere()).nowhere(),
                    )
                    .nowhere(),
                    name: ast_ident("test"),
                    inputs: aparams![("a", tspec!("bool"))],
                    output_type: Some(TypeSpec::Named(ast_path("bool"), None).nowhere()),
                    body: Some(
                        Expression::Block(Box::new(Block {
                            statements: vec![],
                            result: Expression::int_literal(0).nowhere(),
                        }))
                        .nowhere(),
                    ),
                    type_params: vec![],
                }
                .nowhere(),
            )],
        };

        check_parse!(code, module_body, Ok(expected));
    }

    #[test]
    fn pipeline_instantiation_works() {
        let code = "inst(2) some_pipeline(x, y, z)";

        let expected = Expression::Call {
            kind: CallKind::Pipeline(
                ().nowhere(),
                MaybeComptime::Raw(IntLiteral::signed(2).nowhere()).nowhere(),
            ),
            callee: ast_path("some_pipeline"),
            args: ArgumentList::Positional(vec![
                Expression::Identifier(ast_path("x")).nowhere(),
                Expression::Identifier(ast_path("y")).nowhere(),
                Expression::Identifier(ast_path("z")).nowhere(),
            ])
            .nowhere(),
        }
        .nowhere();

        check_parse!(code, expression, Ok(expected), Parser::set_parsing_entity);
    }

    #[test]
    fn enum_declarations_parse() {
        let code = "enum State {
            First,
            Second{a: bool},
            Third{a: bool, b: bool}
        }";

        let expected = Item::Type(
            TypeDeclaration {
                name: ast_ident("State"),
                kind: TypeDeclKind::Enum(
                    Enum {
                        name: ast_ident("State"),
                        options: vec![
                            (ast_ident("First"), None),
                            (ast_ident("Second"), Some(aparams![("a", tspec!("bool")),])),
                            (
                                ast_ident("Third"),
                                Some(aparams![("a", tspec!("bool")), ("b", tspec!("bool"))]),
                            ),
                        ],
                    }
                    .nowhere(),
                ),
                generic_args: vec![],
            }
            .nowhere(),
        );

        check_parse!(code, item, Ok(Some(expected)));
    }

    #[test]
    fn enum_declarations_with_type_args_parse() {
        let code = "enum State<T, #N> {
            First,
            Second{a: T},
            Third{a: N, b: bool}
        }";

        let expected = Item::Type(
            TypeDeclaration {
                name: ast_ident("State"),
                kind: TypeDeclKind::Enum(
                    Enum {
                        name: ast_ident("State"),
                        options: vec![
                            (ast_ident("First"), None),
                            (ast_ident("Second"), Some(aparams![("a", tspec!("T"))])),
                            (
                                ast_ident("Third"),
                                Some(aparams![("a", tspec!("N")), ("b", tspec!("bool")),]),
                            ),
                        ],
                    }
                    .nowhere(),
                ),
                generic_args: vec![
                    TypeParam::TypeName(ast_ident("T")).nowhere(),
                    TypeParam::Integer(ast_ident("N")).nowhere(),
                ],
            }
            .nowhere(),
        );

        check_parse!(code, item, Ok(Some(expected)));
    }

    #[test]
    fn struct_declarations_parse() {
        let code = "struct State { a: bool, b: bool }";

        let expected = Item::Type(
            TypeDeclaration {
                name: ast_ident("State"),
                kind: TypeDeclKind::Struct(
                    Struct {
                        name: ast_ident("State"),
                        members: aparams![("a", tspec!("bool")), ("b", tspec!("bool"))],
                        port_keyword: None,
                    }
                    .nowhere(),
                ),
                generic_args: vec![],
            }
            .nowhere(),
        );

        check_parse!(code, item, Ok(Some(expected)));
    }

    #[test]
    fn port_struct_declarations_parse() {
        let code = "struct port State { a: bool, b: bool }";

        let expected = Item::Type(
            TypeDeclaration {
                name: ast_ident("State"),
                kind: TypeDeclKind::Struct(
                    Struct {
                        name: ast_ident("State"),
                        members: aparams![("a", tspec!("bool")), ("b", tspec!("bool"))],
                        port_keyword: Some(().nowhere()),
                    }
                    .nowhere(),
                ),
                generic_args: vec![],
            }
            .nowhere(),
        );

        check_parse!(code, item, Ok(Some(expected)));
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
    fn missing_semicolon_error_points_to_correct_token() {
        check_parse!(
            "let a = 1 let b = 2;",
            statements(false),
            Err(Error::UnexpectedToken {
                expected: vec![";"],
                got: Token {
                    kind: TokenKind::Let,
                    span: 10..13,
                    file_id: 0,
                },
            })
        );
    }

    #[test]
    fn modules_can_be_empty() {
        let code = r#"mod X {}"#;

        let expected = ModuleBody {
            members: vec![Item::Module(
                Module {
                    name: ast_ident("X"),
                    body: ModuleBody { members: vec![] }.nowhere(),
                }
                .nowhere(),
            )],
        };

        check_parse!(code, module_body, Ok(expected));
    }

    #[test]
    fn modules_containing_items_work() {
        let code = r#"mod X {mod Y {}}"#;

        let expected = ModuleBody {
            members: vec![Item::Module(
                Module {
                    name: ast_ident("X"),
                    body: ModuleBody {
                        members: vec![Item::Module(
                            Module {
                                name: ast_ident("Y"),
                                body: ModuleBody { members: vec![] }.nowhere(),
                            }
                            .nowhere(),
                        )],
                    }
                    .nowhere(),
                }
                .nowhere(),
            )],
        };

        check_parse!(code, module_body, Ok(expected));
    }

    #[test]
    fn simple_use_statement_parses() {
        let code = r#"use X::y;"#;

        let expected = Item::Use(
            UseStatement {
                path: Path::from_strs(&["X", "y"]).nowhere(),
                alias: None,
            }
            .nowhere(),
        );

        check_parse!(code, item, Ok(Some(expected)));
    }

    #[test]
    fn use_statement_with_alias_works() {
        let code = r#"use X::y as z;"#;

        let expected = Item::Use(
            UseStatement {
                path: Path::from_strs(&["X", "y"]).nowhere(),
                alias: Some(ast_ident("z")),
            }
            .nowhere(),
        );

        check_parse!(code, item, Ok(Some(expected)));
    }

    #[test]
    fn assertions_parse() {
        let code = r#"assert x;"#;

        let expected = Statement::Assert(Expression::Identifier(ast_path("x")).nowhere()).nowhere();

        check_parse!(code, statement(false), Ok(Some(expected)));
    }

    #[test]
    fn config_define_works() {
        let code = r#"$config A = 5"#;

        let expected = Item::Config(
            ComptimeConfig {
                name: ast_ident("A"),
                val: 5.to_bigint().nowhere(),
            }
            .nowhere(),
        );
        check_parse!(code, item, Ok(Some(expected)));
    }

    #[test]
    fn comptime_if_can_conditionally_bind_statement() {
        let code = r#"$if A == 1 {
            let a = 0;
        }"#;

        let expected = Statement::Comptime(ComptimeCondition {
            condition: (ast_path("A"), ComptimeCondOp::Eq, 1.to_bigint().nowhere()),
            on_true: Box::new(vec![Statement::Binding(
                Pattern::name("a"),
                None,
                Expression::int_literal(0).nowhere(),
            )
            .nowhere()]),
            on_false: None,
        })
        .nowhere();
        check_parse!(code, statement(true), Ok(Some(expected)));
    }

    #[test]
    fn comptime_if_else_works() {
        let code = r#"$if A == 1 {
            let a = 0;
        }
        $else
        {
            let b = 0;
        }"#;

        let expected = Statement::Comptime(ComptimeCondition {
            condition: (ast_path("A"), ComptimeCondOp::Eq, 1.to_bigint().nowhere()),
            on_true: Box::new(vec![Statement::Binding(
                Pattern::name("a"),
                None,
                Expression::int_literal(0).nowhere(),
            )
            .nowhere()]),
            on_false: Some(Box::new(vec![Statement::Binding(
                Pattern::name("b"),
                None,
                Expression::int_literal(0).nowhere(),
            )
            .nowhere()])),
        })
        .nowhere();
        check_parse!(code, statement(true), Ok(Some(expected)));
    }

    #[test]
    fn set_statements_work() {
        let code = r#"set x = y;"#;

        let expected = Statement::Set {
            target: Expression::Identifier(ast_path("x")).nowhere(),
            value: Expression::Identifier(ast_path("y")).nowhere(),
        }
        .nowhere();

        check_parse!(code, statement(false), Ok(Some(expected)));
    }

    #[test]
    fn comptime_expression_works() {
        let code = r#"
            $if x == 0 {
                1
            }
            $else {
                0
            }
        "#;

        let expected = Expression::Comptime(Box::new(
            ComptimeCondition {
                condition: (ast_path("x"), ComptimeCondOp::Eq, 0.to_bigint().nowhere()),
                on_true: Box::new(
                    Expression::IntLiteral(IntLiteral::Signed(1.to_bigint())).nowhere(),
                ),
                on_false: Some(Box::new(
                    Expression::IntLiteral(IntLiteral::Signed(0.to_bigint())).nowhere(),
                )),
            }
            .nowhere(),
        ))
        .nowhere();

        check_parse!(code, expression, Ok(expected));
    }
}
