mod comptime;
pub mod error;
mod expression;
pub mod item_type;
pub mod lexer;

use colored::*;
use itertools::Itertools;
use local_impl::local_impl;
use logos::Lexer;
use num::ToPrimitive;
use tracing::{event, Level};

use spade_ast::{
    ArgumentList, ArgumentPattern, Attribute, AttributeList, Binding, BitLiteral, Block, CallKind,
    ComptimeConfig, Enum, Expression, ImplBlock, IntLiteral, Item, Module, ModuleBody,
    NamedArgument, NamedTurbofish, ParameterList, Pattern, PipelineStageReference, Register,
    Statement, Struct, TraitDef, TraitSpec, TurbofishInner, TypeDeclKind, TypeDeclaration,
    TypeExpression, TypeParam, TypeSpec, Unit, UnitHead, UnitKind, UseStatement,
};
use spade_common::location_info::{lspan, AsLabel, FullSpan, HasCodespan, Loc, WithLocation};
use spade_common::name::{Identifier, Path};
use spade_common::num_ext::InfallibleToBigInt;
use spade_common::{format_list, pluralize};
use spade_diagnostics::Diagnostic;
use spade_macros::trace_parser;

use crate::error::{
    expected_pipeline_depth, unexpected_token_message, CSErrorTransformations,
    CommaSeparatedResult, ExpectedArgumentList, Result, SuggestBraceEnumVariant,
    TokenSeparatedError, UnexpectedToken,
};
use crate::item_type::UnitKindLocal;
use crate::lexer::{LiteralKind, TokenKind};

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
        // in the loop must push an identifier.
        let start = result.first().unwrap().span;
        let end = result.last().unwrap().span;
        Ok(Path(result).between(self.file_id, &start, &end))
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
            result.push(self.identifier()?);

            // NOTE: (safe unwrap) The vec will have at least one element because the first thing
            // in the loop must push an identifier.
            let path_start = result.first().unwrap().span;
            let path_end = result.last().unwrap().span;

            if self.peek_and_eat(&TokenKind::PathSeparator)?.is_none() {
                break Ok(Some((
                    Path(result).between(self.file_id, &path_start, &path_end),
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
        let first = self.expression()?;

        let expr = if self.peek_and_eat(&TokenKind::Semi).unwrap().is_some() {
            // array shorthand ([<expr>; N])
            let amount = self.eat_cond(TokenKind::is_integer, "integer")?;
            Expression::ArrayShorthandLiteral(
                Box::new(first),
                amount.kind.as_biguint().unwrap().at_loc(&amount.loc()),
            )
        } else {
            // eat comma, if any
            let _ = self.peek_and_eat(&TokenKind::Comma)?;
            // now we can continue with the rest of the elements
            let mut inner = self
                .comma_separated(Self::expression, &TokenKind::CloseBracket)
                .no_context()?;
            inner.insert(0, first);
            Expression::ArrayLiteral(inner)
        };

        let end = self.eat(&TokenKind::CloseBracket)?;

        Ok(Some(expr.between(self.file_id, &start, &end)))
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
                "Tuples with no elements are not supported",
            ));
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

        // inst is only allowed in entity/pipeline, so check that we are in one of those
        self.unit_context
            .allows_inst(().at(self.file_id, &start.span()))?;

        // Check if this is a pipeline or not
        let pipeline_depth = if self.peek_kind(&TokenKind::OpenParen)? {
            Some(self.surrounded(
                &TokenKind::OpenParen,
                |s| {
                    s.maybe_comptime(&|s| {
                        s.int_literal()?
                            .or_error(s, |p| Ok(expected_pipeline_depth(&p.peek()?)))
                    })
                },
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

    #[trace_parser]
    #[tracing::instrument(skip(self))]
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
    fn bit_literal(&mut self) -> Result<Option<Loc<BitLiteral>>> {
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

        let statements = self.statements(is_pipeline)?;

        let (result, end) = if let Some(end) = self.peek_and_eat(&TokenKind::CloseBrace)? {
            (None, end)
        } else {
            let output_value = self.non_comptime_expression()?;
            let end = self.eat(&TokenKind::CloseBrace)?;
            (Some(output_value), end)
        };

        Ok(Some(Block { statements, result }.between(
            self.file_id,
            &start.span,
            &end.span,
        )))
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
            TokenKind::Identifier(_) => PipelineStageReference::Absolute(self.identifier()?),
            _ => {
                let num = if let Some(d) = self.int_literal()? {
                    d
                } else {
                    return Err(Diagnostic::from(UnexpectedToken {
                        got: next,
                        expected: vec!["integer", "identifier"],
                    }));
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

        match ident.inner.0.as_str() {
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
    fn named_argument_list(&mut self) -> Result<Vec<NamedArgument>> {
        let args = self
            .comma_separated(Self::named_argument, &TokenKind::CloseParen)
            .extra_expected(vec![":"])
            .map_err(|e| {
                let Ok(tok) = self.peek() else {
                    return e;
                };
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
        Ok(args)
    }

    #[trace_parser]
    fn positional_argument_list(&mut self) -> Result<Vec<Loc<Expression>>> {
        let args = self
            .comma_separated(Self::expression, &TokenKind::CloseParen)
            .no_context()?;

        Ok(args)
    }

    #[trace_parser]
    fn argument_list(&mut self) -> Result<Option<Loc<ArgumentList>>> {
        let is_named = self.peek_and_eat(&TokenKind::Dollar)?.is_some();
        let opener = peek_for!(self, &TokenKind::OpenParen);
        let argument_list = if is_named {
            ArgumentList::Named(self.named_argument_list()?)
        } else {
            ArgumentList::Positional(self.positional_argument_list()?)
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
                    .primary_label("Type level integers must be positive")),
            }
        } else if self.peek_kind(&TokenKind::OpenBrace)? {
            let (expr, span) = self.surrounded(
                &TokenKind::OpenBrace,
                |s| s.expression(),
                &TokenKind::CloseBrace,
            )?;
            Ok(TypeExpression::ConstGeneric(expr).at(self.file_id, &span))
        } else {
            let inner = self.type_spec()?;

            Ok(TypeExpression::TypeSpec(Box::new(inner.clone())).at_loc(&inner))
        }
    }

    // Types
    #[trace_parser]
    pub fn type_spec(&mut self) -> Result<Loc<TypeSpec>> {
        if let Some(tilde) = self.peek_and_eat(&TokenKind::Tilde)? {
            let rest = self.type_spec()?;
            return Ok(TypeSpec::Inverted(Box::new(rest.clone())).between(
                self.file_id,
                &tilde,
                &rest,
            ));
        }

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
            if !self.peek_cond(TokenKind::is_identifier, "Identifier")? {
                return Err(Diagnostic::from(UnexpectedToken {
                    got: self.peek()?,
                    expected: vec!["type"],
                }));
            }
            // Single type, maybe with generics
            let (path, span) = self.path()?.separate();

            if path.as_strs() == ["_"] {
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

    // Statements

    #[trace_parser]
    pub fn binding(&mut self, attrs: &AttributeList) -> Result<Option<Loc<Statement>>> {
        let let_token = peek_for!(self, &TokenKind::Let);

        let pattern = self.pattern()?;

        let ty = if self.peek_and_eat(&TokenKind::Colon)?.is_some() {
            Some(self.type_spec()?)
        } else {
            None
        };

        self.eat(&TokenKind::Assignment)?;

        if let Some(reg_token) = self.peek_and_eat(&TokenKind::Reg)? {
            self.register(reg_token.loc(), pattern, ty, attrs).map(Some)
        } else {
            let (value, end_span) = self.expression()?.separate();
            Ok(Some(
                Statement::Binding(Binding {
                    pattern,
                    ty,
                    value,
                    attrs: attrs.clone(),
                })
                .between(self.file_id, &let_token, &end_span),
            ))
        }
    }

    pub fn register_marker(&mut self) -> Result<Option<Loc<Statement>>> {
        let reg_token = peek_for!(self, &TokenKind::Reg);

        // NOTE: It might be nicer to use () but that complicates the compiler slightly more
        // annoying to write, so I'll use [] initially as a proof of concept
        let cond = if self.peek_kind(&TokenKind::OpenBracket)? {
            Some(
                self.surrounded(
                    &TokenKind::OpenBracket,
                    Self::expression,
                    &TokenKind::CloseBracket,
                )?
                .0,
            )
        } else {
            None
        };

        let count = if self.peek_and_eat(&TokenKind::Asterisk)?.is_some() {
            if let Some(val) = self.int_literal()? {
                Some(
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
                        .at_loc(&val),
                )
            } else {
                let got = self.peek()?;
                return Err(Diagnostic::error(
                    got.loc(),
                    format!("expected register count, got `{}`", got.kind.as_str()),
                )
                .primary_label("expected register count here")
                .help("register counts can only be integer constants"));
            }
        } else {
            None
        };

        let full_loc = if let Some(c) = count {
            ().between(self.file_id, &reg_token, &c.loc())
        } else {
            ().at(self.file_id, &reg_token)
        };

        Ok(Some(
            Statement::PipelineRegMarker(count, cond).at_loc(&full_loc),
        ))
    }

    #[trace_parser]
    fn register(
        &mut self,
        reg_loc: Loc<()>,
        pattern: Loc<Pattern>,
        value_type: Option<Loc<TypeSpec>>,
        attributes: &AttributeList,
    ) -> Result<Loc<Statement>> {
        self.unit_context.allows_reg(reg_loc)?;

        macro_rules! reg_arguments {
            ( $argument:expr, $unknown:expr, { $( $pat:pat => $var:expr  ),* $(,)? } ) => {
                match $argument {
                    NamedArgument::Full(arg, value) => match arg.inner.0.as_str() {
                        $( $pat => {
                            $var = Some(value);
                        } )*
                        unknown => $unknown.push(unknown.to_string())
                    }
                    NamedArgument::Short(arg) => match arg.inner.0.as_str() {
                        $( $pat => {
                            $var = Some(
                                Expression::Identifier(Path::ident(arg.clone()).at_loc(&arg))
                                    .at_loc(&arg)
                            );
                        } )*
                        unknown => $unknown.push(unknown.to_string())
                    }
                }
            }
        }

        let mut clock = None;
        let mut reset = None;
        let mut initial = None;
        let known_arguments = vec!["clk", "reset", "initial"];
        let arg_list_start = self.eat(&TokenKind::OpenParen)?;
        let mut unknown_arguments = Vec::new();
        for argument in self.named_argument_list()? {
            reg_arguments!(
                argument,
                unknown_arguments,
                {
                    "clk" => clock,
                    "reset" => reset,
                    "initial" => initial,
                }
            );
        }
        let arg_list_end = self.eat(&TokenKind::CloseParen)?;
        let arg_list_loc = arg_list_start.loc().merge(&arg_list_end.loc());
        if !unknown_arguments.is_empty() {
            return Err(Diagnostic::error(
                &arg_list_loc,
                format!(
                    "Unknown register {}",
                    pluralize(unknown_arguments.len(), "argument", "arguments")
                ),
            )
            .primary_label(format!(
                "{} {} unknown register {}",
                format_list(&unknown_arguments),
                pluralize(unknown_arguments.len(), "is an", "are"),
                pluralize(unknown_arguments.len(), "argument", "arguments")
            ))
            .help(format!(
                "Known register arguments are {}",
                format_list(&known_arguments)
            )));
        }

        let Some(clock) = clock else {
            return Err(Diagnostic::error(
                reg_loc.merge(&arg_list_loc),
                "Register is missing a clock",
            )
            .primary_label("This register has no specified clock")
            .span_suggest_insert_after("Try adding a clock", arg_list_start, "clk, "));
        };

        let value = self.expression()?;
        let loc = reg_loc.merge(&value.loc());
        Ok(Statement::Register(
            Register {
                pattern,
                clock,
                reset,
                initial,
                value,
                value_type,
                attributes: attributes.clone(),
            }
            .at_loc(&loc),
        )
        .at_loc(&loc))
    }

    #[trace_parser]
    pub fn declaration(&mut self, attrs: &AttributeList) -> Result<Option<Loc<Statement>>> {
        let start_token = peek_for!(self, &TokenKind::Decl);
        self.disallow_attributes(attrs, &start_token)?;

        let mut identifiers = vec![];
        while self.peek_cond(|t| t.is_identifier(), "expected identifier")? {
            identifiers.push(self.identifier()?);

            if self.peek_and_eat(&TokenKind::Comma)?.is_none() {
                break;
            }
        }

        if identifiers.is_empty() {
            return Err(Diagnostic::error(start_token.loc(), "empty decl statement")
                .primary_label("this decl does not declare anything"));
        }

        let last_ident = identifiers.last().unwrap().clone();

        Ok(Some(Statement::Declaration(identifiers).between(
            self.file_id,
            &start_token.span,
            &last_ident,
        )))
    }

    #[trace_parser]
    pub fn label(&mut self, attrs: &AttributeList) -> Result<Option<Loc<Statement>>> {
        let tok = peek_for!(self, &TokenKind::SingleQuote);
        self.disallow_attributes(attrs, &tok)?;

        let name = self.identifier()?;
        Ok(Some(Statement::Label(name.clone()).between(
            self.file_id,
            &tok.span,
            &name,
        )))
    }

    #[trace_parser]
    pub fn assert(&mut self, attrs: &AttributeList) -> Result<Option<Loc<Statement>>> {
        let tok = peek_for!(self, &TokenKind::Assert);
        self.disallow_attributes(attrs, &tok)?;

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

        self.comptime_condition(&inner, &|condition, loc| {
            Statement::Comptime(condition).at_loc(&loc)
        })
    }

    #[trace_parser]
    pub fn set(&mut self, attrs: &AttributeList) -> Result<Option<Loc<Statement>>> {
        let tok = peek_for!(self, &TokenKind::Set);
        self.disallow_attributes(attrs, &tok)?;

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
        let attrs = self.attributes()?;
        let result = self.first_successful(vec![
            &|s| s.binding(&attrs),
            &|s| s.register_marker(),
            &|s| s.declaration(&attrs),
            &|s| s.label(&attrs),
            &|s| s.assert(&attrs),
            &|s| s.set(&attrs),
            &|s| s.comptime_statement(allow_stages),
        ])?;

        if let Some(statement) = &result {
            if let Statement::Label(_) | Statement::Comptime(_) = statement.inner {
            } else {
                self.eat(&TokenKind::Semi)?;
            }

            if let Statement::PipelineRegMarker(_, _) = statement.inner {
                if !allow_stages {
                    return Err(Diagnostic::error(statement.loc(), "stage outside pipeline")
                        .primary_label("stage is not allowed here")
                        .note("stages are only allowed in the root block of a pipeline"));
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
            Err(Diagnostic::from(UnexpectedToken {
                got: next,
                expected: vec![end_token.as_str(), "statement"],
            }))
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
    pub fn parameter(&mut self) -> Result<(AttributeList, Loc<Identifier>, Loc<TypeSpec>)> {
        let attrs = self.attributes()?;
        let (name, ty) = self.name_and_type()?;
        Ok((attrs, name, ty))
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
                .comma_separated(Self::parameter, &TokenKind::CloseParen)
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
            let traits = if self.peek_and_eat(&TokenKind::Colon)?.is_some() {
                self.token_separated(
                    Self::path,
                    &TokenKind::Plus,
                    vec![TokenKind::Comma, TokenKind::Gt],
                )
                .no_context()?
            } else {
                vec![]
            };
            Ok(TypeParam::TypeName { name: id, traits }.at(self.file_id, &loc))
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
                format!("...because this is a {}", item_start.kind.as_str()),
            )
            .note("attributes are only allowed on enums, functions and pipelines"))
        }
    }

    #[trace_parser]
    #[tracing::instrument(skip(self))]
    pub fn unit_head(&mut self, attributes: &AttributeList) -> Result<Option<Loc<UnitHead>>> {
        let start_token = self.peek()?;
        let unit_kind = match start_token.kind {
            TokenKind::Pipeline => {
                self.eat_unconditional()?;
                let (depth, depth_span) = self.surrounded(
                    &TokenKind::OpenParen,
                    |s| {
                        s.maybe_comptime(&|s| {
                            s.int_literal()?
                                .or_error(s, |p| Ok(expected_pipeline_depth(&p.peek()?)))
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

        let where_clauses = if let Some(where_kw) = self.peek_and_eat(&TokenKind::Where)? {
            let clauses = self
                .comma_separated(
                    |s| {
                        if s.peek_cond(|t| matches!(t, &TokenKind::Identifier(_)), "identifier")? {
                            let name = s.path()?;
                            let _colon = s.eat(&TokenKind::Colon)?;
                            let value = s.expression()?;
                            Ok((name, value))
                        } else {
                            Err(Diagnostic::bug(
                                ().at(s.file_id, &where_kw),
                                "Comma separated should not show this error",
                            ))
                        }
                        // NOTE: With this ending symbol we won't support __builtin__ with where
                        // clauses.
                    },
                    &TokenKind::OpenBrace,
                )
                .extra_expected(vec!["identifier"])?;

            clauses
        } else {
            vec![]
        };

        let end = output_type
            .as_ref()
            .map(|o| o.loc())
            .unwrap_or(inputs.loc());

        Ok(Some(
            UnitHead {
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

    // Entities
    #[trace_parser]
    #[tracing::instrument(skip(self))]
    pub fn unit(&mut self, attributes: &AttributeList) -> Result<Option<Loc<Unit>>> {
        let head = if let Some(head) = self.unit_head(attributes)? {
            head
        } else {
            return Ok(None);
        };

        self.set_item_context(head.unit_kind.clone())?;

        let allow_stages = head.unit_kind.is_pipeline();
        let (block, block_span) = if let Some(block) = self.block(allow_stages)? {
            let (block, block_span) = block.separate();
            (Some(block), block_span)
        } else if self.peek_kind(&TokenKind::Builtin)? {
            let tok = self.eat_unconditional()?;

            (None, ().at(self.file_id, &tok.span).span)
        } else {
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
            .secondary_label(&head, format!("Expected body for this {}", head.unit_kind)));
        };

        self.clear_item_context();

        Ok(Some(
            Unit {
                head: head.inner.clone(),
                body: block.map(|inner| inner.map(|inner| Expression::Block(Box::new(inner)))),
            }
            .between(self.file_id, &head, &block_span),
        ))
    }

    // Traits
    #[trace_parser]
    #[tracing::instrument(skip(self))]
    pub fn trait_def(&mut self, attributes: &AttributeList) -> Result<Option<Loc<TraitDef>>> {
        let start_token = peek_for!(self, &TokenKind::Trait);
        self.disallow_attributes(attributes, &start_token)?;

        let name = self.identifier()?;

        let type_params = self.generics_list()?;

        let mut result = TraitDef {
            name,
            type_params,
            methods: vec![],
        };

        self.eat(&TokenKind::OpenBrace)?;

        while let Some(decl) = self.unit_head(&AttributeList::empty())? {
            result.methods.push(decl);
            self.eat(&TokenKind::Semi)?;
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
        self.disallow_attributes(attributes, &start_token)?;

        let type_params = self.generics_list()?;

        let trait_or_target_path = self.type_spec()?;

        let (r#trait, target) = if self.peek_and_eat(&TokenKind::For)?.is_some() {
            let (trait_path, params) = match trait_or_target_path.inner.clone() {
                TypeSpec::Named(p, params) => (p, params),
                other => {
                    return Err(Diagnostic::error(
                        trait_or_target_path,
                        format!("{other} is not a trait"),
                    ))
                }
            };
            let r#trait = TraitSpec {
                path: trait_path.clone(),
                type_params: params,
            }
            .at_loc(&trait_or_target_path);

            let target = self.type_spec()?;

            (Some(r#trait), target)
        } else {
            let target = trait_or_target_path;
            (None, target)
        };

        let (body, body_span) = self.surrounded(
            &TokenKind::OpenBrace,
            Self::impl_body,
            &TokenKind::CloseBrace,
        )?;

        Ok(Some(
            ImplBlock {
                r#trait,
                type_params,
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
            if u.head.unit_kind.is_pipeline() {
                return Err(Diagnostic::error(
                    u.head.unit_kind.loc(),
                    "Pipelines are currently not allowed in impl blocks",
                )
                .primary_label("Not allowed here")
                .note("This limitation is likely to be lifted in the future")
                .help("Consider defining a free-standing pipeline for now"));
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
            return Err(err);
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

        let type_params = self.generics_list()?;

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
            generic_args: type_params,
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

        let port_keyword = self
            .peek_and_eat(&TokenKind::Port)?
            .map(|tok| ().at(self.file_id, &tok.span()));

        let name = self.identifier()?;

        let type_params = self.generics_list()?;

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
                    attributes: attributes.clone(),
                }
                .between(self.file_id, &start_token.span, &members_loc),
            ),
            generic_args: type_params,
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
            return Err(Diagnostic::from(UnexpectedToken {
                got: self.eat_unconditional()?,
                expected: vec!["integer"],
            }));
        };

        Ok(Some(
            ComptimeConfig {
                name,
                val: val.clone(),
            }
            .between(self.file_id, &start.span(), &val.span()),
        ))
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
        if next.kind == TokenKind::Identifier(key.to_string()) {
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
                                    TokenKind::Identifier(ident) if ident == stringify!($name) => {
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

        match start.inner.0.as_str() {
            "no_mangle" => Ok(Attribute::NoMangle),
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
                        .map(|loc| loc.map(|ident| ident.0))
                        .collect(),
                })
            }
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
    pub fn attributes(&mut self) -> Result<AttributeList> {
        // peek_for!(self, &TokenKind::Hash)
        let mut result = AttributeList(vec![]);
        while let Some(start) = self.peek_and_eat(&TokenKind::Hash)? {
            let (inner, loc) = self.surrounded(
                &TokenKind::OpenBracket,
                Self::attribute_inner,
                &TokenKind::CloseBracket,
            )?;

            result.0.push(inner.between(self.file_id, &start, &loc));
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
            let got = self.peek()?;
            Err(Diagnostic::error(
                got.loc(),
                format!("expected item, got `{}`", got.kind.as_str()),
            )
            .primary_label("expected item"))
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
        let out = match self.lex.next() {
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
                let next = self.next_token()?;
                match next.kind {
                    TokenKind::BlockCommentEnd => break self.next_token(),
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
    use ast::comptime::{ComptimeCondOp, ComptimeCondition, MaybeComptime};
    use spade_ast as ast;
    use spade_ast::testutil::{ast_ident, ast_path, ast_trait_spec, ast_type_expr, ast_type_spec};
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
            Ok(Expression::int_literal_signed(123).nowhere())
        );
    }

    #[test]
    fn bindings_work() {
        let expected = Statement::binding(
            Pattern::name("test"),
            None,
            Expression::int_literal_signed(123).nowhere(),
        )
        .nowhere();
        check_parse!(
            "let test = 123;",
            binding(&AttributeList::empty()),
            Ok(Some(expected))
        );
    }

    #[test]
    fn declarations_work() {
        let expected = Statement::Declaration(vec![ast_ident("x"), ast_ident("y")]).nowhere();

        check_parse!(
            "decl x, y;",
            declaration(&AttributeList::empty()),
            Ok(Some(expected))
        );
    }

    #[test]
    fn bindings_with_types_work() {
        let expected = Statement::binding(
            Pattern::name("test"),
            Some(TypeSpec::Named(ast_path("bool"), None).nowhere()),
            Expression::int_literal_signed(123).nowhere(),
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
            head: UnitHead {
                attributes: AttributeList::empty(),
                unit_kind: UnitKind::Entity.nowhere(),
                name: Identifier("no_inputs".to_string()).nowhere(),
                inputs: aparams![],
                output_type: None,
                type_params: None,
                where_clauses: vec![],
            },
            body: Some(
                Expression::Block(Box::new(Block {
                    statements: vec![
                        Statement::binding(
                            Pattern::name("test"),
                            None,
                            Expression::int_literal_signed(123).nowhere(),
                        )
                        .nowhere(),
                        Statement::binding(
                            Pattern::name("test2"),
                            None,
                            Expression::int_literal_signed(123).nowhere(),
                        )
                        .nowhere(),
                    ],
                    result: Some(Expression::Identifier(ast_path("test")).nowhere()),
                }))
                .nowhere(),
            ),
        }
        .nowhere();

        check_parse!(code, unit(&AttributeList::empty()), Ok(Some(expected)));
    }

    #[test]
    fn entity_with_inputs() {
        let code = include_str!("../parser_test_code/entity_with_inputs.sp");
        let expected = Unit {
            head: UnitHead {
                attributes: AttributeList::empty(),
                unit_kind: UnitKind::Entity.nowhere(),
                name: ast_ident("with_inputs"),
                inputs: aparams![("clk", tspec!("bool")), ("rst", tspec!("bool"))],
                output_type: Some(TypeSpec::Named(ast_path("bool"), None).nowhere()),
                type_params: None,
                where_clauses: vec![],
            },
            body: Some(
                Expression::Block(Box::new(Block {
                    statements: vec![],
                    result: Some(Expression::Identifier(ast_path("clk")).nowhere()),
                }))
                .nowhere(),
            ),
        }
        .nowhere();

        check_parse!(code, unit(&AttributeList::empty()), Ok(Some(expected)));
    }

    #[test]
    fn entity_with_generics() {
        let code = include_str!("../parser_test_code/entity_with_generics.sp");
        let expected = Unit {
            head: UnitHead {
                attributes: AttributeList::empty(),
                unit_kind: UnitKind::Entity.nowhere(),
                name: ast_ident("with_generics"),
                inputs: aparams![],
                output_type: None,
                type_params: Some(
                    vec![
                        TypeParam::TypeName {
                            name: ast_ident("X"),
                            traits: vec![],
                        }
                        .nowhere(),
                        TypeParam::Integer(ast_ident("Y")).nowhere(),
                    ]
                    .nowhere(),
                ),
                where_clauses: vec![],
            },
            body: Some(
                Expression::Block(Box::new(Block {
                    statements: vec![],
                    result: Some(Expression::Identifier(ast_path("clk")).nowhere()),
                }))
                .nowhere(),
            ),
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
                initial: None,
                value: Expression::int_literal_signed(1).nowhere(),
                value_type: None,
                attributes: ast::AttributeList::empty(),
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
                reset: Some(
                    Expression::TupleLiteral(vec![
                        Expression::Identifier(ast_path("rst")).nowhere(),
                        Expression::int_literal_signed(0).nowhere(),
                    ])
                    .nowhere(),
                ),
                initial: None,
                value: Expression::int_literal_signed(1).nowhere(),
                value_type: None,
                attributes: ast::AttributeList::empty(),
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
                reset: Some(
                    Expression::TupleLiteral(vec![
                        Expression::Identifier(ast_path("rst")).nowhere(),
                        Expression::int_literal_signed(0).nowhere(),
                    ])
                    .nowhere(),
                ),
                initial: None,
                value: Expression::int_literal_signed(1).nowhere(),
                value_type: Some(TypeSpec::Named(ast_path("Type"), None).nowhere()),
                attributes: ast::AttributeList::empty(),
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
            head: UnitHead {
                attributes: AttributeList::empty(),
                unit_kind: UnitKind::Entity.nowhere(),
                name: Identifier("e1".to_string()).nowhere(),
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
                attributes: AttributeList::empty(),
                unit_kind: UnitKind::Entity.nowhere(),
                name: Identifier("e2".to_string()).nowhere(),
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
        };

        check_parse!(code, module_body, Ok(expected));
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
            type_params: None,
            target: ast_type_spec("SomeType"),
            units: vec![Unit {
                head: UnitHead {
                    attributes: AttributeList::empty(),
                    unit_kind: UnitKind::Function.nowhere(),
                    name: ast_ident("some_fn"),
                    inputs: ParameterList::without_self(vec![]).nowhere(),
                    output_type: None,
                    type_params: None,
                    where_clauses: vec![],
                },
                body: None,
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
            r#trait: Some(ast_trait_spec("SomeTrait", None)),
            type_params: None,
            target: ast_type_spec("SomeType"),
            units: vec![Unit {
                head: UnitHead {
                    attributes: AttributeList::empty(),
                    unit_kind: UnitKind::Function.nowhere(),
                    name: ast_ident("some_fn"),
                    inputs: ParameterList::without_self(vec![]).nowhere(),
                    output_type: None,
                    type_params: None,
                    where_clauses: vec![],
                },
                body: None,
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
    fn non_anonymous_impl_blocks_with_type_params_work() {
        let code = r#"
        impl SomeTrait<SomeTypeParam> for SomeType {
            fn some_fn() __builtin__
        }
        "#;

        let expected = ImplBlock {
            r#trait: Some(ast_trait_spec(
                "SomeTrait",
                Some(vec![ast_type_expr("SomeTypeParam")]),
            )),
            type_params: None,
            target: ast_type_spec("SomeType"),
            units: vec![Unit {
                head: UnitHead {
                    attributes: AttributeList::empty(),
                    unit_kind: UnitKind::Function.nowhere(),
                    name: ast_ident("some_fn"),
                    inputs: ParameterList::without_self(vec![]).nowhere(),
                    output_type: None,
                    type_params: None,
                    where_clauses: vec![],
                },
                body: None,
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

        let expected = TypeParam::TypeName {
            name: ast_ident("X"),
            traits: vec![],
        }
        .nowhere();

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
                head: UnitHead {
                    attributes: AttributeList::empty(),
                    unit_kind: UnitKind::Entity.nowhere(),
                    name: ast_ident("X"),
                    inputs: ParameterList::without_self(vec![]).nowhere(),
                    output_type: None,
                    type_params: None,
                    where_clauses: vec![],
                },
                body: None,
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
                head: UnitHead {
                    attributes: AttributeList::empty(),
                    name: ast_ident("X"),
                    inputs: ParameterList::without_self(vec![]).nowhere(),
                    output_type: None,
                    unit_kind: UnitKind::Pipeline(
                        MaybeComptime::Raw(IntLiteral::unsized_(1).nowhere()).nowhere(),
                    )
                    .nowhere(),
                    type_params: None,
                    where_clauses: vec![],
                },
                body: None,
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
                head: UnitHead {
                    attributes: AttributeList::empty(),
                    unit_kind: UnitKind::Function.nowhere(),
                    name: ast_ident("X"),
                    inputs: ParameterList::without_self(vec![]).nowhere(),
                    output_type: None,
                    type_params: None,
                    where_clauses: vec![],
                },
                body: None,
            }
            .nowhere(),
        );

        check_parse!(code, unit(&AttributeList::empty()), Ok(expected));
    }

    #[test]
    fn functions_can_have_attributes() {
        let code = r#"
            #[no_mangle]
            fn X() __builtin__"#;

        let expected = Some(Item::Unit(
            Unit {
                head: UnitHead {
                    attributes: AttributeList(vec![Attribute::NoMangle.nowhere()]),
                    unit_kind: UnitKind::Function.nowhere(),
                    name: ast_ident("X"),
                    inputs: ParameterList::without_self(vec![]).nowhere(),
                    output_type: None,
                    type_params: None,
                    where_clauses: vec![],
                },
                body: None,
            }
            .nowhere(),
        ));

        check_parse!(code, item, Ok(expected));
    }

    #[test]
    fn entities_can_have_attributes() {
        let code = r#"
            #[no_mangle]
            entity X() __builtin__"#;

        let expected = Some(Item::Unit(
            Unit {
                head: UnitHead {
                    attributes: AttributeList(vec![Attribute::NoMangle.nowhere()]),
                    unit_kind: UnitKind::Entity.nowhere(),
                    name: ast_ident("X"),
                    inputs: ParameterList::without_self(vec![]).nowhere(),
                    output_type: None,
                    type_params: None,
                    where_clauses: vec![],
                },
                body: None,
            }
            .nowhere(),
        ));

        check_parse!(code, item, Ok(expected));
    }

    #[test]
    fn pipelines_can_have_attributes() {
        let code = r#"
            #[no_mangle]
            pipeline(2) test(a: bool) __builtin__
        "#;

        let expected = Item::Unit(
            Unit {
                head: UnitHead {
                    attributes: AttributeList(vec![Attribute::NoMangle.nowhere()]),
                    unit_kind: UnitKind::Pipeline(
                        MaybeComptime::Raw(IntLiteral::unsized_(2).nowhere()).nowhere(),
                    )
                    .nowhere(),
                    name: ast_ident("test"),
                    inputs: aparams![("a", tspec!("bool"))],
                    output_type: None,
                    type_params: None,
                    where_clauses: vec![],
                },
                body: None,
            }
            .nowhere(),
        );

        check_parse!(code, item, Ok(Some(expected)));
    }

    #[test]
    fn reg_has_fsm_attribute() {
        let code = r#"
            entity X() {
                #[fsm(state)]
                reg(clk) state = false;
                false
            }"#;

        let expected = Some(Item::Unit(
            Unit {
                head: UnitHead {
                    attributes: AttributeList::empty(),
                    unit_kind: UnitKind::Entity.nowhere(),
                    name: ast_ident("X"),
                    inputs: ParameterList::without_self(vec![]).nowhere(),
                    output_type: None,
                    type_params: None,
                    where_clauses: vec![],
                },
                body: Some(
                    Expression::Block(Box::new(Block {
                        statements: vec![Statement::Register(
                            Register {
                                pattern: Pattern::Path(ast_path("state")).nowhere(),
                                clock: Expression::Identifier(ast_path("clk")).nowhere(),
                                reset: None,
                                initial: None,
                                value: Expression::BoolLiteral(false).nowhere(),
                                value_type: None,
                                attributes: AttributeList::from_vec(vec![Attribute::Fsm {
                                    state: Some(ast_ident("state")),
                                }
                                .nowhere()]),
                            }
                            .nowhere(),
                        )
                        .nowhere()],
                        result: Some(Expression::BoolLiteral(false).nowhere()),
                    }))
                    .nowhere(),
                ),
            }
            .nowhere(),
        ));

        check_parse!(code, item, Ok(expected));
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
            head: UnitHead {
                attributes: AttributeList::empty(),
                unit_kind: UnitKind::Pipeline(
                    MaybeComptime::Raw(IntLiteral::unsized_(2).nowhere()).nowhere(),
                )
                .nowhere(),
                name: ast_ident("test"),
                inputs: aparams![("a", tspec!("bool"))],
                output_type: Some(TypeSpec::Named(ast_path("bool"), None).nowhere()),
                type_params: None,
                where_clauses: vec![],
            },
            body: Some(
                Expression::Block(Box::new(Block {
                    statements: vec![
                        Statement::Label(ast_ident("s0")).nowhere(),
                        Statement::PipelineRegMarker(None, None).nowhere(),
                        Statement::binding(
                            Pattern::name("b"),
                            None,
                            Expression::int_literal_signed(0).nowhere(),
                        )
                        .nowhere(),
                        Statement::PipelineRegMarker(None, None).nowhere(),
                        Statement::Label(ast_ident("s2")).nowhere(),
                        Statement::binding(
                            Pattern::name("c"),
                            None,
                            Expression::int_literal_signed(0).nowhere(),
                        )
                        .nowhere(),
                    ],
                    result: Some(Expression::int_literal_signed(0).nowhere()),
                }))
                .nowhere(),
            ),
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
            head: UnitHead {
                attributes: AttributeList::empty(),
                unit_kind: UnitKind::Pipeline(
                    MaybeComptime::Raw(IntLiteral::unsized_(2).nowhere()).nowhere(),
                )
                .nowhere(),
                name: ast_ident("test"),
                inputs: aparams![("a", tspec!("bool"))],
                output_type: Some(TypeSpec::Named(ast_path("bool"), None).nowhere()),
                type_params: None,
                where_clauses: vec![],
            },
            body: Some(
                Expression::Block(Box::new(Block {
                    statements: vec![
                        Statement::PipelineRegMarker(Some(3.nowhere()), None).nowhere()
                    ],
                    result: Some(Expression::int_literal_signed(0).nowhere()),
                }))
                .nowhere(),
            ),
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
                    head: UnitHead {
                        attributes: AttributeList::empty(),
                        unit_kind: UnitKind::Pipeline(
                            MaybeComptime::Raw(IntLiteral::unsized_(2).nowhere()).nowhere(),
                        )
                        .nowhere(),
                        name: ast_ident("test"),
                        inputs: aparams![("a", tspec!("bool"))],
                        output_type: Some(TypeSpec::Named(ast_path("bool"), None).nowhere()),
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
                MaybeComptime::Raw(IntLiteral::unsized_(2).nowhere()).nowhere(),
            ),
            callee: ast_path("some_pipeline"),
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
                generic_args: None,
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
                generic_args: Some(
                    vec![
                        TypeParam::TypeName {
                            name: ast_ident("T"),
                            traits: vec![],
                        }
                        .nowhere(),
                        TypeParam::Integer(ast_ident("N")).nowhere(),
                    ]
                    .nowhere(),
                ),
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
                        attributes: AttributeList::empty(),
                    }
                    .nowhere(),
                ),
                generic_args: None,
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
                        attributes: AttributeList::empty(),
                    }
                    .nowhere(),
                ),
                generic_args: None,
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
            on_true: Box::new(vec![Statement::binding(
                Pattern::name("a"),
                None,
                Expression::int_literal_signed(0).nowhere(),
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
            on_true: Box::new(vec![Statement::binding(
                Pattern::name("a"),
                None,
                Expression::int_literal_signed(0).nowhere(),
            )
            .nowhere()]),
            on_false: Some(Box::new(vec![Statement::binding(
                Pattern::name("b"),
                None,
                Expression::int_literal_signed(0).nowhere(),
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
                on_true: Box::new(Expression::int_literal_signed(1).nowhere()),
                on_false: Some(Box::new(Expression::int_literal_signed(0).nowhere())),
            }
            .nowhere(),
        ))
        .nowhere();

        check_parse!(code, expression, Ok(expected));
    }
}
