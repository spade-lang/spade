pub mod error_reporting;
pub mod lexer;

use spade_ast::{
    ArgumentList, ArgumentPattern, BinaryOperator, Block, Entity, Enum, Expression, FunctionDecl,
    Item, ModuleBody, NamedArgument, ParameterList, Pattern, Pipeline, PipelineBindModifier,
    PipelineBinding, PipelineStage, Register, Statement, TraitDef, TypeDeclKind, TypeDeclaration,
    TypeExpression, TypeParam, TypeSpec,
};
use spade_common::{
    location_info::{lspan, Loc, WithLocation},
    name::{Identifier, Path},
};

use colored::*;
use logos::Lexer;
use thiserror::Error;

use parse_tree_macros::trace_parser;

use crate::lexer::TokenKind;

/// A token with location info
#[derive(Clone, Debug, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: logos::Span,
}

impl Token {
    pub fn new(kind: TokenKind, lexer: &Lexer<TokenKind>) -> Self {
        Self {
            kind,
            span: lexer.span(),
        }
    }
}

#[derive(Error, Debug, Clone, PartialEq)]
pub enum Error {
    #[error("End of file")]
    Eof,
    #[error("Lexer error at {}", 0.0)]
    LexerError(codespan::Span),
    #[error("Unexpected token. got {}, expected {expected:?}", got.kind.as_str())]
    UnexpectedToken {
        got: Token,
        expected: Vec<&'static str>,
    },
    #[error("Expected to find a {} to match {friend:?}", expected.as_str())]
    UnmatchedPair { friend: Token, expected: TokenKind },

    #[error("Expected expression, got {got:?}")]
    ExpectedExpression { got: Token },

    #[error("Entity missing block for {for_what}")]
    ExpectedBlock {
        for_what: String,
        got: Token,
        loc: Loc<()>,
    },

    #[error("Expected type, got {0:?}")]
    ExpectedType(Token),

    #[error("Expected argument list for {0}")]
    ExpectedArgumentList(Loc<Path>),

    #[error("Missing tuple index")]
    MissingTupleIndex { hash_loc: Loc<()> },

    #[error("Expected pipeline depth")]
    ExpectedPipelineDepth { got: Token },

    #[error("Expected expression or stage")]
    ExpectedExpressionOrStage { got: Token },
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

pub struct Parser<'a> {
    lex: Lexer<'a, TokenKind>,
    peeked: Option<Token>,
    pub parse_stack: Vec<ParseStackEntry>,
}

impl<'a> Parser<'a> {
    pub fn new(lex: Lexer<'a, TokenKind>) -> Self {
        Self {
            lex,
            peeked: None,
            parse_stack: vec![],
        }
    }
}

/// Peek the next token. If it matches the specified token, return that token
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

macro_rules! operator_expr {
    ($this_operator:ident, $condition:ident, $next:ident) => {
        fn $this_operator(&mut self) -> Result<Loc<Expression>> {
            self.binary_operator(Self::$next, Self::$condition, Self::$this_operator)
        }
    };
}

// Actual parsing functions
impl<'a> Parser<'a> {
    #[trace_parser]
    pub fn identifier(&mut self) -> Result<Loc<Identifier>> {
        let token = self.eat_cond(TokenKind::is_ident, "Identifier")?;

        if let TokenKind::Identifier(name) = token.kind {
            Ok(Identifier(name).at(&token.span))
        } else {
            unreachable!("eat_cond should have checked this");
        }
    }

    #[trace_parser]
    pub fn path(&mut self) -> Result<Loc<Path>> {
        let mut result = vec![];
        loop {
            result.push(self.identifier()?);

            if let None = self.peek_and_eat(&TokenKind::PathSeparator)? {
                break;
            }
        }
        // NOTE: (safe unwrap) The vec will have at least one element because the first thing
        // in the loop must pus an identifier.
        let start = result.first().unwrap().span;
        let end = result.last().unwrap().span;
        Ok(Path(result).between(&start, &end))
    }

    pub fn binary_operator(
        &mut self,
        lhs: impl Fn(&mut Self) -> Result<Loc<Expression>>,
        condition: impl Fn(&mut Self) -> Result<bool>,
        rhs: impl Fn(&mut Self) -> Result<Loc<Expression>>,
    ) -> Result<Loc<Expression>> {
        let start = lhs(self)?;

        if condition(self)? {
            let operator = self.eat_unconditional()?;
            let rest = rhs(self)?;

            let span = start.span.merge(rest.span);

            let op = match operator.kind {
                TokenKind::Plus => BinaryOperator::Add,
                TokenKind::Minus => BinaryOperator::Sub,
                TokenKind::Asterisk => BinaryOperator::Mul,
                TokenKind::Equals => BinaryOperator::Equals,
                // We have to handle left and right shifts separately because otherwise
                // their parsing interferes with generic arguments
                TokenKind::Lt => BinaryOperator::Lt,
                TokenKind::Gt => BinaryOperator::Gt,
                TokenKind::RightShift => BinaryOperator::RightShift,
                TokenKind::LeftShift => BinaryOperator::LeftShift,
                TokenKind::LogicalOr => BinaryOperator::LogicalOr,
                TokenKind::LogicalAnd => BinaryOperator::LogicalAnd,
                TokenKind::BitwiseAnd => BinaryOperator::BitwiseAnd,
                TokenKind::BitwiseOr => BinaryOperator::BitwiseOr,
                x => unreachable!("{:?} ({}) is not an operator", x, x.as_str()),
            };
            Ok(Expression::BinaryOperator(Box::new(start), op, Box::new(rest)).at(&span))
        } else {
            Ok(start)
        }
    }

    // Expression parsing
    #[trace_parser]
    pub fn expression(&mut self) -> Result<Loc<Expression>> {
        let expr = self.logical_or_expression()?;

        if let Some(hash) = self.peek_and_eat(&TokenKind::Hash)? {
            if let Some(index) = self.int_literal()? {
                let span = expr.span.merge(lspan(hash.span));
                Ok(Expression::TupleIndex(Box::new(expr), index).at(&span))
            } else {
                Err(Error::MissingTupleIndex {
                    hash_loc: Loc::new((), lspan(hash.span)),
                })
            }
        } else {
            Ok(expr)
        }
    }

    operator_expr!(
        logical_or_expression,
        is_next_logical_or,
        logical_and_expression
    );
    operator_expr!(
        logical_and_expression,
        is_next_logical_and,
        bitwise_or_expression
    );
    operator_expr!(
        bitwise_or_expression,
        is_next_bitwise_or,
        bitwise_and_expression
    );
    operator_expr!(
        bitwise_and_expression,
        is_next_bitwise_and,
        comparison_operator
    );
    operator_expr!(
        comparison_operator,
        is_next_comparison_operator,
        shift_expression
    );
    operator_expr!(
        shift_expression,
        is_next_shift_operator,
        additive_expression
    );
    operator_expr!(
        additive_expression,
        is_next_addition_operator,
        multiplicative_expression
    );
    operator_expr!(
        multiplicative_expression,
        is_next_multiplication_operator,
        base_expression
    );

    #[trace_parser]
    fn argument_list(&mut self) -> Result<Option<Loc<ArgumentList>>> {
        let is_named = self.peek_and_eat(&TokenKind::Dollar)?.is_some();
        let opener = peek_for!(self, &TokenKind::OpenParen);

        if is_named {
            let args = self
                .comma_separated(Self::named_argument, &TokenKind::CloseParen)?
                .into_iter()
                .map(Loc::strip)
                .collect();
            let end = self.eat(&TokenKind::CloseParen)?;

            let span = lspan(opener.span).merge(lspan(end.span));
            Ok(Some(ArgumentList::Named(args).at(&span)))
        } else {
            let args = self.comma_separated(Self::expression, &TokenKind::CloseParen)?;
            let end = self.eat(&TokenKind::CloseParen)?;

            let span = lspan(opener.span.clone()).merge(lspan(end.span));

            Ok(Some(ArgumentList::Positional(args).at(&span)))
        }
    }

    #[trace_parser]
    pub fn base_expression(&mut self) -> Result<Loc<Expression>> {
        if self.peek_and_eat(&TokenKind::OpenParen)?.is_some() {
            let mut inner = self.comma_separated(Self::expression, &TokenKind::CloseParen)?;
            let result = if inner.is_empty() {
                todo!("Implement unit literals")
            } else if inner.len() == 1 {
                // NOTE: safe unwrap, we know the size of the array
                Ok(inner.pop().unwrap())
            } else {
                let span = inner
                    .first()
                    .unwrap()
                    .span
                    .merge(inner.last().unwrap().span);
                Ok(Expression::TupleLiteral(inner).at(&span))
            };
            self.eat(&TokenKind::CloseParen)?;
            result
        } else if let Some(start) = self.peek_and_eat(&TokenKind::Instance)? {
            // TODO: Clean this up a bit
            // Check if this is a pipeline or not
            let pipeline_depth = if self.peek_and_eat(&TokenKind::OpenParen)?.is_some() {
                if let Some(depth) = self.int_literal()? {
                    self.eat(&TokenKind::CloseParen)?;
                    Some(depth)
                } else {
                    return Err(Error::ExpectedPipelineDepth {
                        got: self.eat_unconditional()?,
                    });
                }
            } else {
                None
            };

            let name = self.path()?;

            let args = self
                .argument_list()?
                .ok_or(Error::ExpectedArgumentList(name.clone()))?;

            if let Some(depth) = pipeline_depth {
                Ok(Expression::PipelineInstance(depth, name, args.clone())
                    .between(&start.span, &args))
            } else {
                Ok(Expression::EntityInstance(name, args.clone()).between(&start.span, &args))
            }
        } else if let Some(val) = self.bool_literal()? {
            Ok(val.map(Expression::BoolLiteral))
        } else if let Some(val) = self.int_literal()? {
            Ok(val.map(Expression::IntLiteral))
        } else if let Some(block) = self.block()? {
            Ok(block.map(Box::new).map(Expression::Block))
        } else if let Some(if_expr) = self.if_expression()? {
            Ok(if_expr)
        } else if let Some(match_expr) = self.match_expression()? {
            Ok(match_expr)
        } else {
            match self.path() {
                Ok(path) => {
                    let span = path.span;
                    // Check if this is a function call by looking for an argument list
                    if let Some(args) = self.argument_list()? {
                        // Doing this avoids cloning result and args
                        let span = ().between(&path, &args);

                        Ok(Expression::FnCall(path, args).at_loc(&span))
                    } else {
                        Ok(Expression::Identifier(path).at(&span))
                    }
                }
                Err(Error::UnexpectedToken { got, .. }) => Err(Error::ExpectedExpression { got }),
                Err(e) => Err(e),
            }
        }
    }

    #[trace_parser]
    fn named_argument(&mut self) -> Result<Loc<NamedArgument>> {
        // This is a named arg
        let name = self.identifier()?;
        if self.peek_and_eat(&TokenKind::Assignment)?.is_some() {
            let value = self.expression()?;

            let span = name.span.merge(value.span);

            Ok(NamedArgument::Full(name, value).at(&span))
        } else {
            Ok(NamedArgument::Short(name.clone()).at(&name))
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
            Expression::If(Box::new(cond), Box::new(on_true), Box::new(on_false))
                .between(&start.span, &end_span),
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
            },
            &TokenKind::CloseBrace,
        )?;

        Ok(Some(
            Expression::Match(Box::new(expression), patterns).between(&start.span, &body_loc),
        ))
    }

    #[trace_parser]
    pub fn int_literal(&mut self) -> Result<Option<Loc<u128>>> {
        if self.peek_cond(TokenKind::is_integer, "integer")? {
            let token = self.eat_unconditional()?;
            match token.kind {
                TokenKind::Integer(val) => Ok(Some(Loc::new(val, lspan(token.span)))),
                _ => unreachable!(),
            }
        } else {
            Ok(None)
        }
    }

    #[trace_parser]
    fn bool_literal(&mut self) -> Result<Option<Loc<bool>>> {
        if let Some(tok) = self.peek_and_eat(&TokenKind::True)? {
            Ok(Some(true.at(&tok.span)))
        } else if let Some(tok) = self.peek_and_eat(&TokenKind::False)? {
            Ok(Some(false.at(&tok.span)))
        } else {
            Ok(None)
        }
    }

    #[trace_parser]
    pub fn block(&mut self) -> Result<Option<Loc<Block>>> {
        let start = peek_for!(self, &TokenKind::OpenBrace);

        let statements = self.statements()?;
        let output_value = self.expression()?;
        let end = self.eat(&TokenKind::CloseBrace)?;

        Ok(Some(
            Block {
                statements,
                result: output_value,
            }
            .between(&start.span, &end.span),
        ))
    }

    #[trace_parser]
    pub fn type_expression(&mut self) -> Result<Loc<TypeExpression>> {
        if let Some(val) = self.int_literal()? {
            Ok(val.map(TypeExpression::Integer))
        } else {
            let inner = self.type_spec()?;

            Ok(TypeExpression::TypeSpec(Box::new(inner.clone())).at_loc(&inner))
        }
    }

    // Types
    #[trace_parser]
    pub fn type_spec(&mut self) -> Result<Loc<TypeSpec>> {
        if let Some(tuple) = self.tuple_spec()? {
            Ok(tuple)
        } else {
            let (path, span) = self
                .path()
                .map_err(|e| e.specify_unexpected_token(|t| Error::ExpectedType(t)))?
                .separate();

            // Check if this type has generic params
            let (params, generic_span) = if self.peek_kind(&TokenKind::Lt)? {
                let generic_start = self.eat_unconditional()?;
                let type_expr = self.type_expression()?;

                let generic_end = if let Some(end) = self.peek_and_eat(&TokenKind::Gt)? {
                    end
                }
                // We need to do some trickery to avoid problems with >> being lexed as right shift
                else if let Some(end) = self.peek_and_eat(&TokenKind::RightShift)? {
                    assert!(self.peeked.is_none());
                    self.peeked = Some(Token {
                        kind: TokenKind::Gt,
                        span: end.span.clone(),
                    });
                    Token {
                        kind: TokenKind::Gt,
                        ..end
                    }
                } else {
                    return Err(Error::UnmatchedPair {
                        friend: generic_start,
                        expected: TokenKind::Gt,
                    });
                };

                (
                    vec![type_expr],
                    ().between(&generic_start.span, &generic_end.span).span,
                )
            } else {
                (vec![], span)
            };

            Ok(TypeSpec::Named(path, params).between(&span, &generic_span))
        }
    }

    #[trace_parser]
    pub fn tuple_spec(&mut self) -> Result<Option<Loc<TypeSpec>>> {
        let start = peek_for!(self, &TokenKind::OpenParen);

        let inner = self.comma_separated(Self::type_spec, &TokenKind::CloseParen)?;
        let end = self.eat(&TokenKind::CloseParen)?;

        let span = lspan(start.span).merge(lspan(end.span));

        Ok(Some(TypeSpec::Tuple(inner).at(&span)))
    }

    /// A name with an associated type, as used in argument definitions as well
    /// as struct defintions
    ///
    /// name: Type
    // TODO: Use this for let bindings
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
                let inner = s.comma_separated(Self::pattern, &TokenKind::CloseParen)?;
                let end = s.eat(&TokenKind::CloseParen)?;

                Ok(Some(Pattern::Tuple(inner).between(&start.span, &end.span)))
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

                if let Some(start_paren) = s.peek_and_eat(&TokenKind::OpenParen)? {
                    let inner = s.comma_separated(Self::pattern, &TokenKind::CloseParen)?;
                    let end = s.eat(&TokenKind::CloseParen)?;

                    Ok(Some(
                        Pattern::Type(path, ArgumentPattern::Positional(inner).nowhere())
                            .between(&start_paren.span, &end.span),
                    ))
                } else if let Some(start_brace) = s.peek_and_eat(&TokenKind::OpenBrace)? {
                    let inner_parser = |s: &mut Self| {
                        let lhs = s.identifier()?;
                        s.eat(&TokenKind::Colon)?;
                        let rhs = s.pattern()?;

                        Ok((lhs, rhs))
                    };
                    let inner = s.comma_separated(inner_parser, &TokenKind::CloseBrace)?;
                    let end = s.eat(&TokenKind::CloseBrace)?;

                    Ok(Some(
                        Pattern::Type(path, ArgumentPattern::Named(inner).nowhere())
                            .between(&start_brace.span, &end.span),
                    ))
                } else {
                    Ok(Some(Pattern::Path(path.clone()).at(&path)))
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

    // Statemenets

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

        Ok(Some(
            Statement::Binding(pattern, t, value).between(&start_span, &end_span),
        ))
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
            .at(&span),
        )
        .at(&span);
        Ok(Some(result))
    }

    /// If the next token is the start of a statement, return that statement,
    /// otherwise None
    #[trace_parser]
    pub fn statement(&mut self) -> Result<Option<Loc<Statement>>> {
        let result = self.first_successful(vec![&Self::binding, &Self::register])?;
        if result.is_some() {
            self.eat(&TokenKind::Semi)?;
        }
        Ok(result)
    }

    #[trace_parser]
    pub fn statements(&mut self) -> Result<Vec<Loc<Statement>>> {
        let mut result = vec![];
        while let Some(statement) = self.statement()? {
            result.push(statement)
        }
        Ok(result)
    }

    #[trace_parser]
    pub fn self_arg(&mut self) -> Result<Option<Loc<()>>> {
        if self.peek_cond(
            |t| t == &TokenKind::Identifier("self".to_string()),
            "looking for self",
        )? {
            let tok = self.eat_unconditional()?;
            Ok(Some(().at(&tok.span)))
        } else {
            Ok(None)
        }
    }

    #[trace_parser]
    pub fn parameter_list(&mut self) -> Result<ParameterList> {
        Ok(ParameterList(self.comma_separated(
            Self::name_and_type,
            &TokenKind::CloseParen,
        )?))
    }

    // Entities
    #[trace_parser]
    pub fn entity(&mut self) -> Result<Option<Loc<Entity>>> {
        let start_token = peek_for!(self, &TokenKind::Entity);

        let name = self.identifier()?;

        let type_params = self.generics_list()?;

        // Input types
        self.eat(&TokenKind::OpenParen)?;
        let inputs = self.parameter_list()?;
        let close_paren = self.eat(&TokenKind::CloseParen)?;

        // Return type
        let output_type = if self.peek_and_eat(&TokenKind::SlimArrow)?.is_some() {
            Some(self.type_spec()?)
        } else {
            None
        };

        // Body (TODO: might want to make this a separate structure like a block)
        let (block, block_span) = if let Some(block) = self.block()? {
            block.separate()
        } else {
            // The end of the entity definition depends on wether or not
            // a type is present.
            let end_loc = output_type
                .map(|t| t.loc().span)
                .unwrap_or_else(|| lspan(close_paren.span));

            return Err(Error::ExpectedBlock {
                // NOTE: Unwrap should be safe becase we have already checked
                // if this is a { or not
                for_what: "entity".to_string(),
                got: self.peek()?.unwrap(),
                loc: Loc::new((), lspan(start_token.span).merge(end_loc)),
            });
        };

        Ok(Some(
            Entity {
                name,
                inputs,
                output_type,
                body: block.map(|inner| Expression::Block(Box::new(inner))),
                type_params,
            }
            .between(&start_token.span, &block_span),
        ))
    }

    #[trace_parser]
    pub fn pipeline_binding(&mut self) -> Result<Option<Loc<PipelineBinding>>> {
        let start = peek_for!(self, &TokenKind::Let);

        let modifier = if let Some(t) = self.peek_and_eat(&TokenKind::Reg)? {
            Some(PipelineBindModifier::Reg.at(&t.span))
        } else {
            None
        };

        let name = self.identifier()?;

        let type_spec = if self.peek_and_eat(&TokenKind::Colon)?.is_some() {
            Some(self.type_spec()?)
        } else {
            None
        };

        self.eat(&TokenKind::Assignment)?;

        let value = self.expression()?;

        let end = self.eat(&TokenKind::Semi)?;

        Ok(Some(
            PipelineBinding {
                name,
                modifier,
                type_spec,
                value,
            }
            .between(&start.span, &end.span),
        ))
    }

    #[trace_parser]
    pub fn pipeline_stage(&mut self) -> Result<Option<Loc<PipelineStage>>> {
        let start = peek_for!(self, &TokenKind::Stage);

        self.eat(&TokenKind::OpenBrace)?;

        let mut bindings = vec![];
        while let Some(statement) = self.pipeline_binding()? {
            bindings.push(statement)
        }

        let end = self.eat(&TokenKind::CloseBrace).map_err(|e| match e {
            Error::UnexpectedToken { got, mut expected } => {
                expected.push("Pipeline binding");
                Error::UnexpectedToken { got, expected }
            }
            other => other,
        })?;

        Ok(Some(
            PipelineStage { bindings }.between(&start.span, &end.span),
        ))
    }

    #[trace_parser]
    pub fn pipeline(&mut self) -> Result<Option<Loc<Pipeline>>> {
        let start = peek_for!(self, &TokenKind::Pipeline);

        // Depth
        self.eat(&TokenKind::OpenParen)?;
        let depth = if let Some(d) = self.int_literal()? {
            d
        } else {
            return Err(Error::ExpectedPipelineDepth {
                got: self.eat_unconditional()?,
            });
        };
        self.eat(&TokenKind::CloseParen)?;

        let name = self.identifier()?;

        // Input types
        self.eat(&TokenKind::OpenParen)?;
        // TODO: Can we use surrounded here?
        let inputs = self.parameter_list()?;
        self.eat(&TokenKind::CloseParen)?;

        // Return type
        let output_type = if self.peek_and_eat(&TokenKind::SlimArrow)?.is_some() {
            Some(self.type_spec()?)
        } else {
            None
        };

        self.eat(&TokenKind::OpenBrace)?;

        let mut stages = vec![];
        while let Some(stage) = self.pipeline_stage()? {
            stages.push(stage)
        }

        let result = self.expression().map_err(|e| match e {
            Error::ExpectedExpression { got } => Error::ExpectedExpressionOrStage { got },
            other => other,
        })?;

        let end = self.eat(&TokenKind::CloseBrace)?;

        Ok(Some(
            Pipeline {
                depth,
                name,
                inputs,
                output_type,
                stages,
                result,
            }
            .between(&start.span, &end.span),
        ))
    }

    #[trace_parser]
    pub fn type_param(&mut self) -> Result<Loc<TypeParam>> {
        // If this is a type level integer
        if let Some(hash) = self.peek_and_eat(&TokenKind::Hash)? {
            let (id, loc) = self.identifier()?.separate();
            Ok(TypeParam::Integer(id).between(&hash.span, &loc))
        } else {
            let (id, loc) = self.identifier()?.separate();
            Ok(TypeParam::TypeName(id).at(&loc))
        }
    }

    #[trace_parser]
    pub fn generics_list(&mut self) -> Result<Vec<Loc<TypeParam>>> {
        if let Some(lt) = self.peek_and_eat(&TokenKind::Lt)? {
            let params = self.comma_separated(Self::type_param, &TokenKind::Gt)?;
            self.eat(&TokenKind::Gt).map_err(|_| Error::UnmatchedPair {
                friend: lt,
                expected: TokenKind::Gt,
            })?;
            Ok(params)
        } else {
            Ok(vec![])
        }
    }

    // Traits
    #[trace_parser]
    pub fn function_decl(&mut self) -> Result<Option<Loc<FunctionDecl>>> {
        let start_token = peek_for!(self, &TokenKind::Function);

        let name = self.identifier()?;

        let type_params = self.generics_list()?;

        // Input types
        self.eat(&TokenKind::OpenParen)?;
        let (self_arg, more_args) = if let Some(arg) = self.self_arg()? {
            if let Some(_) = self.peek_and_eat(&TokenKind::Comma)? {
                (Some(arg), true)
            } else if let Some(_) = self.peek_and_eat(&TokenKind::CloseParen)? {
                (Some(arg), false)
            } else {
                let next = self.eat_unconditional()?;
                return Err(Error::UnexpectedToken {
                    got: next,
                    expected: vec![TokenKind::Comma.as_str(), TokenKind::CloseParen.as_str()],
                });
            }
        } else {
            (None, true)
        };

        let inputs = if more_args {
            let inputs = self.parameter_list()?;
            self.eat(&TokenKind::CloseParen)?;
            inputs
        } else {
            ParameterList(vec![])
        };

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
                self_arg,
                inputs,
                return_type,
                type_params,
            }
            .between(&start_token.span, &end_token.span),
        ))
    }

    #[trace_parser]
    pub fn trait_def(&mut self) -> Result<Option<Loc<TraitDef>>> {
        let start_token = peek_for!(self, &TokenKind::Trait);

        let name = self.identifier()?;

        let mut result = TraitDef {
            name,
            functions: vec![],
        };

        self.eat(&TokenKind::OpenBrace)?;

        while let Some(decl) = self.function_decl()? {
            result.functions.push(decl);
        }
        let end_token = self.eat(&TokenKind::CloseBrace)?;

        Ok(Some(result.between(&start_token.span, &end_token.span)))
    }

    #[trace_parser]
    pub fn enum_option(&mut self) -> Result<(Loc<Identifier>, Option<ParameterList>)> {
        let name = self.identifier()?;

        let args = if self.peek_and_eat(&TokenKind::OpenParen)?.is_some() {
            let result = Some(self.parameter_list()?);
            self.eat(&TokenKind::CloseParen)?;
            result
        } else {
            None
        };

        Ok((name, args))
    }

    #[trace_parser]
    pub fn enum_declaration(&mut self) -> Result<Option<Loc<TypeDeclaration>>> {
        let start_token = peek_for!(self, &TokenKind::Enum);

        let name = self.identifier()?;

        let generic_args = self.generics_list()?;

        let (options, options_loc) = self.surrounded(
            &TokenKind::OpenBrace,
            |s: &mut Self| s.comma_separated(Self::enum_option, &TokenKind::CloseBrace),
            &TokenKind::CloseBrace,
        )?;

        let result = TypeDeclaration {
            name: name.clone(),
            kind: TypeDeclKind::Enum(
                Enum { name, options }.between(&start_token.span, &options_loc),
            ),
            generic_args,
        }
        .between(&start_token.span, &options_loc);

        Ok(Some(result))
    }

    #[trace_parser]
    pub fn type_declaration(&mut self) -> Result<Option<Loc<TypeDeclaration>>> {
        // The head of all type declarations will be `(enum|struct|type...) Name<T, S, ...>`
        // since we want access to the name and type params, we'll parse all those three, then
        // defer to parsing the rest.

        self.first_successful(vec![&Self::enum_declaration])
    }

    #[trace_parser]
    pub fn item(&mut self) -> Result<Option<Item>> {
        self.first_successful(vec![
            &|s: &mut Self| s.entity().map(|e| e.map(Item::Entity)),
            &|s: &mut Self| s.trait_def().map(|e| e.map(Item::TraitDef)),
            &|s: &mut Self| s.pipeline().map(|e| e.map(Item::Pipeline)),
            &|s: &mut Self| s.type_declaration().map(|e| e.map(Item::Type)),
        ])
    }

    #[trace_parser]
    pub fn module_body(&mut self) -> Result<ModuleBody> {
        let mut members = vec![];
        while let Some(item) = self.item()? {
            members.push(item)
        }
        Ok(ModuleBody { members })
    }
}

macro_rules! def_is_operators {
    ($( $name:ident [ $($token_kind:ident),* ] ),*$(,)?) => {
        $(fn $name(&mut self) -> Result<bool> {
            Ok(match self.peek()?.map(|token| token.kind) {
                $(Some(TokenKind::$token_kind) => true),*,
                _ => false
            })
        })*
    }
}
// Helper functions for checking the type of tokens
impl<'a> Parser<'a> {
    def_is_operators! {
        is_next_addition_operator [Plus, Minus],
        is_next_shift_operator [LeftShift, RightShift],
        is_next_multiplication_operator [Asterisk],
        is_next_comparison_operator [Equals, Gt, Lt],
        is_next_logical_and [LogicalAnd],
        is_next_logical_or [LogicalOr],
        is_next_bitwise_and [BitwiseAnd],
        is_next_bitwise_or [BitwiseOr]
    }
}

// Helper functions for combining parsers
impl<'a> Parser<'a> {
    fn first_successful<T>(
        &mut self,
        parsers: Vec<&dyn Fn(&mut Self) -> Result<Option<T>>>,
    ) -> Result<Option<T>> {
        for parser in parsers {
            match parser(self) {
                Ok(Some(val)) => return Ok(Some(val)),
                Ok(None) => continue,
                Err(e) => return Err(e),
            }
        }
        Ok(None)
    }

    /// Attempts to parse an inner structure surrouned by two tokens, like `( x )`.
    ///
    /// If the `start` token is not found, an error is produced.
    ///
    /// If the `start` token is found, but the inner parser returns `None`, `None` is returned.
    ///
    /// If the end token is not found, return a mismatch error
    fn surrounded<T>(
        &mut self,
        start: &TokenKind,
        inner: impl Fn(&mut Self) -> Result<T>,
        end: &TokenKind,
    ) -> Result<(T, Loc<()>)> {
        let opener = self.eat(start)?;
        let result = inner(self)?;
        // TODO: Better error handling here. We are throwing away potential EOFs
        let end = self.eat(end).map_err(|_| Error::UnmatchedPair {
            friend: opener.clone(),
            expected: end.clone(),
        })?;

        Ok((
            result,
            Loc::new((), lspan(opener.span).merge(lspan(end.span))),
        ))
    }

    #[trace_parser]
    pub fn comma_separated<T>(
        &mut self,
        inner: impl Fn(&mut Self) -> Result<T>,
        // This end marker is used for allowing trailing commas. It should
        // be whatever ends the collection that is searched. I.e. (a,b,c,) should have
        // `)`, and {} should have `}`
        end_marker: &TokenKind,
    ) -> Result<Vec<T>> {
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
            } else {
                self.eat(&TokenKind::Comma)?;
            }
        }
        Ok(result)
    }
}

// Helper functions for advancing the token stream
impl<'a> Parser<'a> {
    fn eat(&mut self, expected: &TokenKind) -> Result<Token> {
        self.eat_cond(|k| k == expected, expected.as_str())
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
        Ok(food)
    }

    /// Peeks the next token. If it is the sepcified kind, returns that token, otherwise
    /// returns None
    fn peek_and_eat(&mut self, kind: &TokenKind) -> Result<Option<Token>> {
        if self.peek_kind(kind)? {
            Ok(Some(self.eat_unconditional()?))
        } else {
            Ok(None)
        }
    }

    fn peek(&mut self) -> Result<Option<Token>> {
        if let Some(prev) = self.peeked.clone() {
            Ok(Some(prev))
        } else {
            let result = match self.next_token() {
                Ok(token) => Some(token),
                Err(Error::Eof) => None,
                Err(e) => return Err(e),
            };
            self.peeked = result.clone();
            Ok(result)
        }
    }

    fn peek_kind(&mut self, expected: &TokenKind) -> Result<bool> {
        let result = self.peek_cond_no_tracing(|kind| kind == expected)?;
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
        self.peek().map(|token| {
            if let Some(inner) = token {
                cond(&inner.kind)
            } else {
                false
            }
        })
    }

    fn next_token(&mut self) -> Result<Token> {
        let kind = self.lex.next().ok_or(Error::Eof)?;

        if let TokenKind::Error = kind {
            Err(Error::LexerError(lspan(self.lex.span())))?
        };

        Ok(Token::new(kind, &self.lex))
    }
}

pub enum ParseStackEntry {
    Enter(String),
    Ate(Token),
    PeekingWithCondition(String, bool),
    PeekingFor(TokenKind, bool),
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
    use spade_ast as ast;
    use spade_ast::testutil::{ast_ident, ast_path};
    use spade_ast::*;

    use crate::lexer::TokenKind;
    use crate::*;

    use logos::Logos;

    use spade_common::location_info::{Loc, WithLocation};

    macro_rules! check_parse {
        ($string:expr , $method:ident, $expected:expr) => {
            let mut parser = Parser::new(TokenKind::lexer($string));
            let result = parser.$method();
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
            }
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
    fn addition_operatoins_are_expressions() {
        let expected_value = Expression::BinaryOperator(
            Box::new(Expression::Identifier(ast_path("a")).nowhere()),
            BinaryOperator::Add,
            Box::new(Expression::Identifier(ast_path("b")).nowhere()),
        )
        .nowhere();

        check_parse!("a + b", expression, Ok(expected_value.clone()));
    }

    #[test]
    fn bitwise_and_operatoins_are_expressions() {
        let expected_value = Expression::BinaryOperator(
            Box::new(Expression::Identifier(ast_path("a")).nowhere()),
            BinaryOperator::BitwiseAnd,
            Box::new(Expression::Identifier(ast_path("b")).nowhere()),
        )
        .nowhere();

        check_parse!("a & b", expression, Ok(expected_value.clone()));
    }

    #[test]
    fn bitwise_or_operatoins_are_expressions() {
        let expected_value = Expression::BinaryOperator(
            Box::new(Expression::Identifier(ast_path("a")).nowhere()),
            BinaryOperator::BitwiseOr,
            Box::new(Expression::Identifier(ast_path("b")).nowhere()),
        )
        .nowhere();

        check_parse!("a | b", expression, Ok(expected_value.clone()));
    }

    #[ignore]
    #[test]
    fn multiplication() {}
    /*
    #[test]
    fn multiplications_are_expressions() {
        let expected_value = Expression::BinaryOperator(
            Box::new(Expression::Identifier(ast_path("a")).nowhere()),
            TokenKind::Asterisk,
            Box::new(Expression::Identifier(ast_path("b")).nowhere()),
        )
        .nowhere();

        check_parse!("a * b", expression, Ok(expected_value.clone()));
    }

    #[test]
    fn multiplication_before_addition() {
        let expected_value = Expression::BinaryOperator(
            Box::new(
                Expression::BinaryOperator(
                    Box::new(Expression::Identifier(ast_path("a")).nowhere()),
                    TokenKind::Asterisk,
                    Box::new(Expression::Identifier(ast_path("b")).nowhere()),
                )
                .nowhere(),
            ),
            TokenKind::Plus,
            Box::new(Expression::Identifier(ast_path("c")).nowhere()),
        )
        .nowhere();

        check_parse!("a*b + c", expression, Ok(expected_value.clone()));
    }
    */

    #[test]
    fn equals_after_addition() {
        let expected_value = Expression::BinaryOperator(
            Box::new(
                Expression::BinaryOperator(
                    Box::new(Expression::Identifier(ast_path("a")).nowhere()),
                    BinaryOperator::Add,
                    Box::new(Expression::Identifier(ast_path("b")).nowhere()),
                )
                .nowhere(),
            ),
            BinaryOperator::Equals,
            Box::new(Expression::Identifier(ast_path("c")).nowhere()),
        )
        .nowhere();

        check_parse!("a+b == c", expression, Ok(expected_value.clone()));
    }

    #[test]
    fn and_after_equals() {
        {
            let expected_value = Expression::BinaryOperator(
                Box::new(
                    Expression::BinaryOperator(
                        Box::new(Expression::Identifier(ast_path("a")).nowhere()),
                        BinaryOperator::Equals,
                        Box::new(Expression::Identifier(ast_path("b")).nowhere()),
                    )
                    .nowhere(),
                ),
                BinaryOperator::LogicalAnd,
                Box::new(Expression::Identifier(ast_path("c")).nowhere()),
            )
            .nowhere();

            check_parse!("a == b && c", expression, Ok(expected_value.clone()));
        }
        {
            let expected_value = Expression::BinaryOperator(
                Box::new(Expression::Identifier(ast_path("a")).nowhere()),
                BinaryOperator::LogicalAnd,
                Box::new(
                    Expression::BinaryOperator(
                        Box::new(Expression::Identifier(ast_path("b")).nowhere()),
                        BinaryOperator::Equals,
                        Box::new(Expression::Identifier(ast_path("c")).nowhere()),
                    )
                    .nowhere(),
                ),
            )
            .nowhere();

            check_parse!("a && b == c", expression, Ok(expected_value.clone()));
        }
    }

    #[test]
    fn bracketed_expressions_are_expressions() {
        let expected_value = Expression::BinaryOperator(
            Box::new(Expression::Identifier(ast_path("a")).nowhere()),
            BinaryOperator::Add,
            Box::new(
                Expression::BinaryOperator(
                    Box::new(Expression::Identifier(ast_path("b")).nowhere()),
                    BinaryOperator::Add,
                    Box::new(Expression::Identifier(ast_path("c")).nowhere()),
                )
                .nowhere(),
            ),
        )
        .nowhere();

        check_parse!("a + (b + c)", expression, Ok(expected_value.clone()));
    }

    #[test]
    fn repeated_bracketed_expressions_work() {
        let expected_value = Expression::BinaryOperator(
            Box::new(
                Expression::BinaryOperator(
                    Box::new(Expression::Identifier(ast_path("b")).nowhere()),
                    BinaryOperator::Add,
                    Box::new(Expression::Identifier(ast_path("c")).nowhere()),
                )
                .nowhere(),
            ),
            BinaryOperator::Add,
            Box::new(Expression::Identifier(ast_path("a")).nowhere()),
        )
        .nowhere();

        check_parse!("((b + c) + a)", expression, Ok(expected_value.clone()));
    }

    #[test]
    fn literals_are_expressions() {
        check_parse!("123", expression, Ok(Expression::IntLiteral(123).nowhere()));
    }

    #[test]
    fn if_expressions_work() {
        let code = r#"
        if a {b} else {c}
        "#;

        let expected = Expression::If(
            Box::new(Expression::Identifier(ast_path("a")).nowhere()),
            Box::new(
                Expression::Block(Box::new(Block {
                    statements: vec![],
                    result: Expression::Identifier(ast_path("b")).nowhere(),
                }))
                .nowhere(),
            ),
            Box::new(
                Expression::Block(Box::new(Block {
                    statements: vec![],
                    result: Expression::Identifier(ast_path("c")).nowhere(),
                }))
                .nowhere(),
            ),
        )
        .nowhere();

        check_parse!(code, expression, Ok(expected));
    }

    #[test]
    fn if_expressions_do_not_require_blocks() {
        let code = r#"
        if a b else c
        "#;

        let expected = Expression::If(
            Box::new(Expression::Identifier(ast_path("a")).nowhere()),
            Box::new(Expression::Identifier(ast_path("b")).nowhere()),
            Box::new(Expression::Identifier(ast_path("c")).nowhere()),
        )
        .nowhere();

        check_parse!(code, expression, Ok(expected));
    }

    #[test]
    fn match_expressions_work() {
        let code = r#"
        match x {
            (0, y) => y,
            (x, y) => x,
        }
        "#;

        let expected = Expression::Match(
            Box::new(Expression::Identifier(ast_path("x")).nowhere()),
            vec![
                (
                    Pattern::Tuple(vec![Pattern::Integer(0).nowhere(), Pattern::name("y")])
                        .nowhere(),
                    Expression::Identifier(ast_path("y")).nowhere(),
                ),
                (
                    Pattern::Tuple(vec![Pattern::name("x"), Pattern::name("y")]).nowhere(),
                    Expression::Identifier(ast_path("x")).nowhere(),
                ),
            ],
        )
        .nowhere();

        check_parse!(code, expression, Ok(expected));
    }

    #[test]
    fn blocks_work() {
        let code = r#"
            {
                let a = 0;
                1
            }
            "#;

        let expected = Block {
            statements: vec![Statement::Binding(
                Pattern::name("a"),
                None,
                Expression::IntLiteral(0).nowhere(),
            )
            .nowhere()],
            result: Expression::IntLiteral(1).nowhere(),
        }
        .nowhere();

        check_parse!(code, block, Ok(Some(expected)));
    }

    #[test]
    fn blocks_are_expressions() {
        let code = r#"
            {
                let a = 0;
                1
            }
            "#;

        let expected = Expression::Block(Box::new(Block {
            statements: vec![Statement::Binding(
                Pattern::name("a"),
                None,
                Expression::IntLiteral(0).nowhere(),
            )
            .nowhere()],
            result: Expression::IntLiteral(1).nowhere(),
        }))
        .nowhere();

        check_parse!(code, expression, Ok(expected));
    }

    #[test]
    fn bindings_work() {
        let expected = Statement::Binding(
            Pattern::name("test"),
            None,
            Expression::IntLiteral(123).nowhere(),
        )
        .nowhere();
        check_parse!("let test = 123;", binding, Ok(Some(expected)));
    }

    #[test]
    fn bindings_with_types_work() {
        let expected = Statement::Binding(
            Pattern::name("test"),
            Some(TypeSpec::Named(ast_path("bool"), vec![]).nowhere()),
            Expression::IntLiteral(123).nowhere(),
        )
        .nowhere();
        check_parse!("let test: bool = 123;", statement, Ok(Some(expected)));
    }

    #[test]
    fn entity_without_inputs() {
        let code = include_str!("../parser_test_code/entity_without_inputs.sp");
        let expected = Entity {
            name: Identifier("no_inputs".to_string()).nowhere(),
            inputs: aparams![],
            output_type: None,
            body: Expression::Block(Box::new(Block {
                statements: vec![
                    Statement::Binding(
                        Pattern::name("test"),
                        None,
                        Expression::IntLiteral(123).nowhere(),
                    )
                    .nowhere(),
                    Statement::Binding(
                        Pattern::name("test2"),
                        None,
                        Expression::IntLiteral(123).nowhere(),
                    )
                    .nowhere(),
                ],
                result: Expression::Identifier(ast_path("test")).nowhere(),
            }))
            .nowhere(),
            type_params: vec![],
        }
        .nowhere();

        check_parse!(code, entity, Ok(Some(expected)));
    }

    #[test]
    fn entity_with_inputs() {
        let code = include_str!("../parser_test_code/entity_with_inputs.sp");
        let expected = Entity {
            name: ast_ident("with_inputs"),
            inputs: aparams![("clk", tspec!("bool")), ("rst", tspec!("bool"))],
            output_type: Some(TypeSpec::Named(ast_path("bool"), vec![]).nowhere()),
            body: Expression::Block(Box::new(Block {
                statements: vec![],
                result: Expression::Identifier(ast_path("clk")).nowhere(),
            }))
            .nowhere(),
            type_params: vec![],
        }
        .nowhere();

        check_parse!(code, entity, Ok(Some(expected)));
    }

    #[test]
    fn entity_with_generics() {
        let code = include_str!("../parser_test_code/entity_with_generics.sp");
        let expected = Entity {
            name: ast_ident("with_generics"),
            inputs: aparams![],
            output_type: None,
            body: Expression::Block(Box::new(Block {
                statements: vec![],
                result: Expression::Identifier(ast_path("clk")).nowhere(),
            }))
            .nowhere(),
            type_params: vec![
                TypeParam::TypeName(ast_ident("X")).nowhere(),
                TypeParam::Integer(ast_ident("Y")).nowhere(),
            ],
        }
        .nowhere();

        check_parse!(code, entity, Ok(Some(expected)));
    }

    #[test]
    fn parsing_register_without_reset_works() {
        let code = "reg(clk) name = 1;";

        let expected = Statement::Register(
            Register {
                pattern: Pattern::name("name"),
                clock: Expression::Identifier(ast_path("clk")).nowhere(),
                reset: None,
                value: Expression::IntLiteral(1).nowhere(),
                value_type: None,
            }
            .nowhere(),
        )
        .nowhere();

        check_parse!(code, statement, Ok(Some(expected)));
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
                    Expression::IntLiteral(0).nowhere(),
                )),
                value: Expression::IntLiteral(1).nowhere(),
                value_type: None,
            }
            .nowhere(),
        )
        .nowhere();

        check_parse!(code, statement, Ok(Some(expected)));
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
                    Expression::IntLiteral(0).nowhere(),
                )),
                value: Expression::IntLiteral(1).nowhere(),
                value_type: Some(TypeSpec::Named(ast_path("Type"), vec![]).nowhere()),
            }
            .nowhere(),
        )
        .nowhere();

        check_parse!(code, statement, Ok(Some(expected)));
    }

    #[test]
    fn size_types_work() {
        let expected = TypeSpec::Named(
            ast_path("uint"),
            vec![TypeExpression::Integer(10).nowhere()],
        )
        .nowhere();
        check_parse!("uint<10>", type_spec, Ok(expected));
    }

    #[test]
    fn nested_generics_work() {
        let code = "Option<int<5>>";

        let expected = TypeSpec::Named(
            ast_path("Option"),
            vec![TypeExpression::TypeSpec(Box::new(
                TypeSpec::Named(ast_path("int"), vec![TypeExpression::Integer(5).nowhere()])
                    .nowhere(),
            ))
            .nowhere()],
        )
        .nowhere();

        check_parse!(code, type_spec, Ok(expected));
    }

    #[test]
    fn module_body_parsing_works() {
        let code = include_str!("../parser_test_code/multiple_entities.sp");

        let e1 = Entity {
            name: Identifier("e1".to_string()).nowhere(),
            inputs: aparams![],
            output_type: None,
            body: Expression::Block(Box::new(Block {
                statements: vec![],
                result: Expression::IntLiteral(0).nowhere(),
            }))
            .nowhere(),
            type_params: vec![],
        }
        .nowhere();

        let e2 = Entity {
            name: Identifier("e2".to_string()).nowhere(),
            inputs: aparams![],
            output_type: None,
            body: Expression::Block(Box::new(Block {
                statements: vec![],
                result: Expression::IntLiteral(1).nowhere(),
            }))
            .nowhere(),
            type_params: vec![],
        }
        .nowhere();

        let expected = ModuleBody {
            members: vec![Item::Entity(e1), Item::Entity(e2)],
        };

        check_parse!(code, module_body, Ok(expected));
    }

    #[test]
    fn function_declarations_work() {
        let code = "fn some_fn(self, a: bit) -> bit;";

        let expected = FunctionDecl {
            name: ast_ident("some_fn"),
            self_arg: Some(().nowhere()),
            inputs: aparams![("a", tspec!("bit"))],
            return_type: Some(TypeSpec::Named(ast_path("bit"), vec![]).nowhere()),
            type_params: vec![],
        }
        .nowhere();

        check_parse!(code, function_decl, Ok(Some(expected)));
    }

    #[test]
    fn function_declarations_with_only_self_arg_work() {
        let code = "fn some_fn(self) -> bit;";

        let expected = FunctionDecl {
            name: ast_ident("some_fn"),
            self_arg: Some(().nowhere()),
            inputs: aparams![],
            return_type: Some(TypeSpec::Named(ast_path("bit"), vec![]).nowhere()),
            type_params: vec![],
        }
        .nowhere();

        check_parse!(code, function_decl, Ok(Some(expected)));
    }

    #[test]
    fn function_declarations_with_no_type_have_unit_type() {
        let code = "fn some_fn(self);";

        let expected = FunctionDecl {
            name: ast_ident("some_fn"),
            self_arg: Some(().nowhere()),
            inputs: aparams![],
            return_type: None,
            type_params: vec![],
        }
        .nowhere();

        check_parse!(code, function_decl, Ok(Some(expected)));
    }

    #[test]
    fn function_decls_with_generic_type_works() {
        let code = "fn some_fn<X>(self);";

        let expected = FunctionDecl {
            name: ast_ident("some_fn"),
            self_arg: Some(().nowhere()),
            inputs: aparams![],
            return_type: None,
            type_params: vec![TypeParam::TypeName(ast_ident("X")).nowhere()],
        }
        .nowhere();

        check_parse!(code, function_decl, Ok(Some(expected)));
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
            self_arg: Some(().nowhere()),
            inputs: aparams![("a", tspec!("bit"))],
            return_type: Some(TypeSpec::Named(ast_path("bit"), vec![]).nowhere()),
            type_params: vec![],
        }
        .nowhere();
        let fn2 = FunctionDecl {
            name: ast_ident("another_fn"),
            self_arg: Some(().nowhere()),
            inputs: aparams![],
            return_type: Some(TypeSpec::Named(ast_path("bit"), vec![]).nowhere()),
            type_params: vec![],
        }
        .nowhere();

        let expected = TraitDef {
            name: ast_ident("SomeTrait"),
            functions: vec![fn1, fn2],
        }
        .nowhere();

        check_parse!(code, trait_def, Ok(Some(expected)));
    }

    #[test]
    fn typenames_parse() {
        let code = "X";

        let expected = TypeParam::TypeName(ast_ident("X")).nowhere();

        check_parse!(code, type_param, Ok(expected));
    }

    #[test]
    fn typeints_parse() {
        let code = "#X";

        let expected = TypeParam::Integer(ast_ident("X")).nowhere();

        check_parse!(code, type_param, Ok(expected));
    }

    #[test]
    fn tuple_literals_parse() {
        let code = "(1, true)";

        let expected = Expression::TupleLiteral(vec![
            Expression::IntLiteral(1).nowhere(),
            Expression::BoolLiteral(true).nowhere(),
        ])
        .nowhere();

        check_parse!(code, expression, Ok(expected));
    }

    #[test]
    fn tuple_indexing_parsese() {
        let code = "a#0";

        let expected = Expression::TupleIndex(
            Box::new(Expression::Identifier(ast_path("a")).nowhere()),
            Loc::new(0, ().nowhere().span),
        )
        .nowhere();

        check_parse!(code, expression, Ok(expected));
    }

    #[test]
    fn tuple_type_specs_work() {
        let code = "(int, bool)";

        let expected = TypeSpec::Tuple(vec![
            TypeSpec::Named(ast_path("int"), vec![]).nowhere(),
            TypeSpec::Named(ast_path("bool"), vec![]).nowhere(),
        ])
        .nowhere();

        check_parse!(code, type_spec, Ok(expected));
    }

    #[test]
    fn entity_instanciation() {
        let code = "inst some_entity(x, y, z)";

        let expected = Expression::EntityInstance(
            ast_path("some_entity"),
            ArgumentList::Positional(vec![
                Expression::Identifier(ast_path("x")).nowhere(),
                Expression::Identifier(ast_path("y")).nowhere(),
                Expression::Identifier(ast_path("z")).nowhere(),
            ])
            .nowhere(),
        )
        .nowhere();

        check_parse!(code, expression, Ok(expected));
    }

    #[test]
    fn entity_instanciation_with_a_named_arg() {
        let code = "inst some_entity$(z=a)";

        let expected = Expression::EntityInstance(
            ast_path("some_entity"),
            ArgumentList::Named(vec![NamedArgument::Full(
                ast_ident("z"),
                Expression::Identifier(ast_path("a")).nowhere(),
            )])
            .nowhere(),
        )
        .nowhere();

        check_parse!(code, expression, Ok(expected));
    }
    #[test]
    fn named_args_work() {
        let code = "x=a";

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
    fn pipeline_stage_parsing_works() {
        let code = r#"
            stage {
                let y = 0;
                let reg x = 0;
                let reg x: bool = 0;
            }
            "#;

        let expected = PipelineStage {
            bindings: vec![
                PipelineBinding {
                    name: ast_ident("y"),
                    modifier: None,
                    type_spec: None,
                    value: Expression::IntLiteral(0).nowhere(),
                }
                .nowhere(),
                PipelineBinding {
                    name: ast_ident("x"),
                    modifier: Some(PipelineBindModifier::Reg.nowhere()),
                    type_spec: None,
                    value: Expression::IntLiteral(0).nowhere(),
                }
                .nowhere(),
                PipelineBinding {
                    name: ast_ident("x"),
                    modifier: Some(PipelineBindModifier::Reg.nowhere()),
                    type_spec: Some(TypeSpec::Named(ast_path("bool"), vec![]).nowhere()),
                    value: Expression::IntLiteral(0).nowhere(),
                }
                .nowhere(),
            ],
        }
        .nowhere();

        check_parse!(code, pipeline_stage, Ok(Some(expected)));
    }

    #[test]
    fn pipeline_parsing_works() {
        let code = r#"
            pipeline(2) test(a: bool) -> bool {
                stage {
                    let reg b = 0;
                }
                stage {
                    let c = 0;
                }
                0
            }
        "#;

        let expected = Pipeline {
            depth: Loc::new(2, lspan(0..0)),
            name: ast_ident("test"),
            inputs: aparams![("a", tspec!("bool"))],
            output_type: Some(TypeSpec::Named(ast_path("bool"), vec![]).nowhere()),
            stages: vec![
                PipelineStage {
                    bindings: vec![PipelineBinding {
                        name: ast_ident("b"),
                        modifier: Some(PipelineBindModifier::Reg.nowhere()),
                        type_spec: None,
                        value: Expression::IntLiteral(0).nowhere(),
                    }
                    .nowhere()],
                }
                .nowhere(),
                PipelineStage {
                    bindings: vec![PipelineBinding {
                        name: ast_ident("c"),
                        modifier: None,
                        type_spec: None,
                        value: Expression::IntLiteral(0).nowhere(),
                    }
                    .nowhere()],
                }
                .nowhere(),
            ],
            result: Expression::IntLiteral(0).nowhere(),
        }
        .nowhere();

        check_parse!(code, pipeline, Ok(Some(expected)));
    }

    #[test]
    fn pipelines_are_items() {
        let code = r#"
            pipeline(2) test(a: bool) -> bool {
                0
            }
        "#;

        let expected = ModuleBody {
            members: vec![Item::Pipeline(
                Pipeline {
                    depth: Loc::new(2, lspan(0..0)),
                    name: ast_ident("test"),
                    inputs: aparams![("a", tspec!("bool"))],
                    output_type: Some(TypeSpec::Named(ast_path("bool"), vec![]).nowhere()),
                    stages: vec![],
                    result: Expression::IntLiteral(0).nowhere(),
                }
                .nowhere(),
            )],
        };

        check_parse!(code, module_body, Ok(expected));
    }

    #[test]
    fn pipeline_instanciation_works() {
        let code = "inst(2) some_pipeline(x, y, z)";

        let expected = Expression::PipelineInstance(
            2.nowhere(),
            ast_path("some_pipeline"),
            ArgumentList::Positional(vec![
                Expression::Identifier(ast_path("x")).nowhere(),
                Expression::Identifier(ast_path("y")).nowhere(),
                Expression::Identifier(ast_path("z")).nowhere(),
            ])
            .nowhere(),
        )
        .nowhere();

        check_parse!(code, expression, Ok(expected));
    }

    #[test]
    fn enums_declarations_parse() {
        let code = "enum State {
            First,
            Second(a: bool),
            Third(a: bool, b: bool)
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
    fn enums_declarations_with_type_args_parse() {
        let code = "enum State<T, #N> {
            First,
            Second(a: T),
            Third(a: N, b: bool)
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
    fn functions_work() {
        let code = "test(1, 2)";

        let expected = Expression::FnCall(
            ast_path("test"),
            ArgumentList::Positional(vec![
                Expression::IntLiteral(1).nowhere(),
                Expression::IntLiteral(2).nowhere(),
            ])
            .nowhere(),
        )
        .nowhere();

        check_parse!(code, expression, Ok(expected));
    }

    #[test]
    fn functions_with_named_arguments_work() {
        let code = "test$(a, b)";

        let expected = Expression::FnCall(
            ast_path("test"),
            ArgumentList::Named(vec![
                NamedArgument::Short(ast_ident("a")),
                NamedArgument::Short(ast_ident("b")),
            ])
            .nowhere(),
        )
        .nowhere();

        check_parse!(code, expression, Ok(expected));
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

        let expected = Pattern::Integer(1).nowhere();

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
        let code = "SomeType{x: a, y: b}";

        let expected = Pattern::Type(
            ast_path("SomeType"),
            ArgumentPattern::Named(vec![
                (ast_ident("x"), Pattern::name("a")),
                (ast_ident("y"), Pattern::name("b")),
            ])
            .nowhere(),
        )
        .nowhere();

        check_parse!(code, pattern, Ok(expected));
    }
}
