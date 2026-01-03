use spade_ast::{AttributeList, Binding, Expression, Register, Statement};
use spade_common::location_info::{lspan, AsLabel, Loc, WithLocation};
use spade_diagnostics::{diag_bail, Diagnostic};
use spade_macros::trace_parser;

use crate::{
    error::Result, item_type::UnitKindLocal, lexer::TokenKind, peek_for, KeywordPeekingParser,
    ParseStackEntry, Parser, Token,
};

pub(crate) struct BindingParser {}

impl KeywordPeekingParser<Loc<Statement>> for BindingParser {
    fn is_leading_token(&self) -> fn(&TokenKind) -> bool {
        |kind| kind == &TokenKind::Let
    }

    fn parse(&self, parser: &mut Parser, attributes: &AttributeList) -> Result<Loc<Statement>> {
        let _ = parser.eat_unconditional()?;

        let (pattern, start_span) = parser.pattern()?.separate();

        let ty = if parser.peek_and_eat(&TokenKind::Colon)?.is_some() {
            Some(parser.type_spec()?)
        } else {
            None
        };

        parser.eat(&TokenKind::Assignment)?;
        let (value, end_span) = parser.expression()?.separate();

        Ok(Statement::Binding(Binding {
            pattern,
            ty,
            value,
            attrs: attributes.clone(),
        })
        .between(parser.file_id, &start_span, &end_span))
    }
}

pub(crate) struct RegisterParser {}

impl KeywordPeekingParser<Loc<Statement>> for RegisterParser {
    fn is_leading_token(&self) -> fn(&TokenKind) -> bool {
        |kind| kind == &TokenKind::Reg
    }

    fn parse(&self, parser: &mut Parser, attributes: &AttributeList) -> Result<Loc<Statement>> {
        let start_token = parser.eat_unconditional()?;

        // NOTE: It might be nicer to use () but that complicates the compiler slightly more
        // annoying to write, so I'll use [] initially as a proof of concept
        let cond = if parser.peek_kind(&TokenKind::OpenBracket)? {
            Some(
                parser
                    .surrounded(
                        &TokenKind::OpenBracket,
                        Parser::expression,
                        &TokenKind::CloseBracket,
                    )?
                    .0,
            )
        } else {
            None
        };

        // If this is a reg marker for a pipeline
        if parser.peek_kind(&TokenKind::Semi)? || parser.peek_kind(&TokenKind::Asterisk)? {
            let count = if let Some(ast) = parser.peek_and_eat(&TokenKind::Asterisk)? {
                match parser.type_expression() {
                    Ok(t) => Some(t),
                    Err(diag) => {
                        return Err(
                            diag.secondary_label(ast, "* is used to specify a register count")
                        )
                    }
                }
            } else {
                None
            };

            let full_loc = if let Some(c) = &count {
                ().between(parser.file_id, &start_token, &c.loc())
            } else {
                ().at(parser.file_id, &start_token)
            };

            return Ok(Statement::PipelineRegMarker(count, cond).at_loc(&full_loc));
        }

        parser
            .unit_context
            .allows_reg(().at(parser.file_id, &start_token.span()))?;

        // Clock selection
        let (clock, _clock_paren_span) = parser.surrounded(
            &TokenKind::OpenParen,
            |s| s.expression().map(Some),
            &TokenKind::CloseParen,
        )?;

        // Identifier parsing cannot fail since we map it into a Some. Therefore,
        // unwrap is safe
        let clock = clock.unwrap();

        // Name
        let pattern = parser.pattern()?;

        // Optional type
        let value_type = if parser.peek_and_eat(&TokenKind::Colon)?.is_some() {
            Some(parser.type_spec()?)
        } else {
            None
        };

        // Optional reset
        let reset = parser.register_reset()?;
        let initial = parser.register_initial()?;
        // Try parsing reset again, if we find two resets, error out
        let reset = match (reset, parser.register_reset()?) {
            (Some(first), None) => Some(first),
            (None, Some(second)) => Some(second),
            (Some(first), Some(second)) => {
                return Err(Diagnostic::error(
                    ().between_locs(&second.0, &second.1),
                    "Multiple resets specified",
                )
                .primary_label("Second reset")
                .secondary_label(().between_locs(&first.0, &first.1), "First reset"))
            }
            (None, None) => None,
        };

        // Value
        parser.eat(&TokenKind::Assignment)?;
        let (value, end_span) = parser.expression()?.separate();

        let span = lspan(start_token.span).merge(end_span);
        let result = Statement::Register(
            Register {
                pattern,
                clock,
                reset,
                initial,
                value,
                value_type,
                attributes: attributes.clone(),
            }
            .at(parser.file_id, &span),
        )
        .at(parser.file_id, &span);
        Ok(result)
    }
}

impl<'a> Parser<'a> {
    #[trace_parser]
    pub fn register_reset_definition(&mut self) -> Result<(Loc<Expression>, Loc<Expression>)> {
        let condition = self.expression()?;
        self.eat(&TokenKind::Colon)?;
        let value = self.expression()?;

        Ok((condition, value))
    }

    #[trace_parser]
    pub fn register_reset(&mut self) -> Result<Option<(Loc<Expression>, Loc<Expression>)>> {
        peek_for!(self, &TokenKind::Reset);
        let (reset, _) = self.surrounded(
            &TokenKind::OpenParen,
            |s| s.register_reset_definition().map(Some),
            &TokenKind::CloseParen,
        )?;
        // NOTE: Safe unwrap, register_reset_definition can not fail
        Ok(Some(reset.unwrap()))
    }

    #[trace_parser]
    pub fn register_initial(&mut self) -> Result<Option<Loc<Expression>>> {
        peek_for!(self, &TokenKind::Initial);
        let (reset, _) = self.surrounded(
            &TokenKind::OpenParen,
            Self::expression,
            &TokenKind::CloseParen,
        )?;
        Ok(Some(reset))
    }
}

pub(crate) struct DeclParser {}

impl KeywordPeekingParser<Loc<Statement>> for DeclParser {
    fn is_leading_token(&self) -> fn(&TokenKind) -> bool {
        |kind| kind == &TokenKind::Decl
    }

    fn parse(&self, parser: &mut Parser, attributes: &AttributeList) -> Result<Loc<Statement>> {
        let start_token = parser.eat_unconditional()?;
        parser.disallow_attributes(attributes, &start_token)?;

        let mut identifiers = vec![];
        while parser.peek_cond(|t| t.is_identifier(), "expected identifier")? {
            identifiers.push(parser.identifier()?);

            if parser.peek_and_eat(&TokenKind::Comma)?.is_none() {
                break;
            }
        }

        if identifiers.is_empty() {
            return Err(Diagnostic::error(start_token.loc(), "empty decl statement")
                .primary_label("this decl does not declare anything"));
        }

        let last_ident = identifiers.last().unwrap().clone();

        Ok(Statement::Declaration(identifiers).between(
            parser.file_id,
            &start_token.span,
            &last_ident,
        ))
    }
}

pub(crate) struct LabelParser {}

impl KeywordPeekingParser<Loc<Statement>> for LabelParser {
    fn is_leading_token(&self) -> fn(&TokenKind) -> bool {
        |kind| matches!(kind, TokenKind::Label(_))
    }

    fn parse(&self, parser: &mut Parser, attributes: &AttributeList) -> Result<Loc<Statement>> {
        let tok @ Token {
            kind: TokenKind::Label(l),
            ..
        } = &parser.eat_unconditional()?
        else {
            diag_bail!(
                parser.peek()?,
                "Label parser was called but it did not get a label"
            )
        };
        parser.disallow_attributes(attributes, &tok)?;

        Ok(Statement::Label(l.clone().at(parser.file_id, &tok.span)).at(parser.file_id, &tok.span))
    }
}

pub(crate) struct AssertParser {}

impl KeywordPeekingParser<Loc<Statement>> for AssertParser {
    fn is_leading_token(&self) -> fn(&TokenKind) -> bool {
        |kind| kind == &TokenKind::Assert
    }

    fn parse(&self, parser: &mut Parser, attributes: &AttributeList) -> Result<Loc<Statement>> {
        let tok = parser.eat_unconditional()?;
        parser.disallow_attributes(attributes, &tok)?;

        let expr = parser.expression()?;

        Ok(Statement::Assert(expr.clone()).between(parser.file_id, &tok.span, &expr))
    }
}

pub(crate) struct SetParser {}

impl KeywordPeekingParser<Loc<Statement>> for SetParser {
    fn is_leading_token(&self) -> fn(&TokenKind) -> bool {
        |kind| kind == &TokenKind::Set
    }

    fn parse(&self, parser: &mut Parser, attributes: &AttributeList) -> Result<Loc<Statement>> {
        let tok = parser.eat_unconditional()?;
        parser.disallow_attributes(attributes, &tok)?;

        let target = parser.expression()?;

        parser.eat(&TokenKind::Assignment)?;

        let value = parser.expression()?;

        Ok(Statement::Set {
            target,
            value: value.clone(),
        }
        .between(parser.file_id, &tok.span, &value))
    }
}
