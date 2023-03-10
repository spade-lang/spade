use num::ToPrimitive;
use spade_ast::{ArgumentList, BinaryOperator, CallKind, Expression, UnaryOperator};
use spade_common::location_info::{lspan, Loc, WithLocation};
use spade_diagnostics::Diagnostic;
use spade_macros::trace_parser;

use crate::error::{Error, ExpectedArgumentList, Result};
use crate::{lexer::TokenKind, ParseStackEntry, Parser};

#[derive(PartialEq, PartialOrd, Eq, Ord)]
enum OpBindingPower {
    None,
    LogicalOr,
    LogicalAnd,
    LogicalXor,
    BitwiseOr,
    BitwiseXor,
    BitwiseAnd,
    Equality,
    RelationalCmp,
    Shift,
    AddLike,
    MulLike,
    // Unary operator appearing before the expression it applies to such as
    // - and !
    PrefixUnary,
}

fn binop_binding_power(op: &BinaryOperator) -> OpBindingPower {
    match op {
        BinaryOperator::Add => OpBindingPower::AddLike,
        BinaryOperator::Sub => OpBindingPower::AddLike,
        BinaryOperator::Mul => OpBindingPower::MulLike,
        BinaryOperator::Equals => OpBindingPower::Equality,
        BinaryOperator::Lt => OpBindingPower::RelationalCmp,
        BinaryOperator::Gt => OpBindingPower::RelationalCmp,
        BinaryOperator::Le => OpBindingPower::RelationalCmp,
        BinaryOperator::Ge => OpBindingPower::RelationalCmp,
        BinaryOperator::LogicalAnd => OpBindingPower::LogicalAnd,
        BinaryOperator::LogicalOr => OpBindingPower::LogicalOr,
        BinaryOperator::LogicalXor => OpBindingPower::LogicalXor,
        BinaryOperator::LeftShift => OpBindingPower::Shift,
        BinaryOperator::RightShift => OpBindingPower::Shift,
        BinaryOperator::ArithmeticRightShift => OpBindingPower::Shift,
        BinaryOperator::BitwiseAnd => OpBindingPower::BitwiseAnd,
        BinaryOperator::BitwiseOr => OpBindingPower::BitwiseOr,
        BinaryOperator::BitwiseXor => OpBindingPower::BitwiseXor,
    }
}

fn unop_binding_power(op: &UnaryOperator) -> OpBindingPower {
    match op {
        UnaryOperator::Sub => OpBindingPower::PrefixUnary,
        UnaryOperator::Not => OpBindingPower::PrefixUnary,
        UnaryOperator::BitwiseNot => OpBindingPower::PrefixUnary,
        UnaryOperator::Dereference => OpBindingPower::PrefixUnary,
        UnaryOperator::Reference => OpBindingPower::PrefixUnary,
    }
}

impl<'a> Parser<'a> {
    fn binop_from_kind(kind: &TokenKind) -> Option<BinaryOperator> {
        match kind {
            TokenKind::Plus => Some(BinaryOperator::Add),
            TokenKind::Minus => Some(BinaryOperator::Sub),
            TokenKind::Asterisk => Some(BinaryOperator::Mul),
            TokenKind::Equals => Some(BinaryOperator::Equals),
            // We have to handle left and right shifts separately because otherwise
            // their parsing interferes with generic arguments
            TokenKind::Lt => Some(BinaryOperator::Lt),
            TokenKind::Gt => Some(BinaryOperator::Gt),
            TokenKind::Le => Some(BinaryOperator::Le),
            TokenKind::Ge => Some(BinaryOperator::Ge),
            TokenKind::RightShift => Some(BinaryOperator::RightShift),
            TokenKind::ArithmeticRightShift => Some(BinaryOperator::ArithmeticRightShift),
            TokenKind::LeftShift => Some(BinaryOperator::LeftShift),
            TokenKind::LogicalOr => Some(BinaryOperator::LogicalOr),
            TokenKind::LogicalAnd => Some(BinaryOperator::LogicalAnd),
            TokenKind::LogicalXor => Some(BinaryOperator::LogicalXor),
            TokenKind::Ampersand => Some(BinaryOperator::BitwiseAnd),
            TokenKind::BitwiseOr => Some(BinaryOperator::BitwiseOr),
            TokenKind::BitwiseXor => Some(BinaryOperator::BitwiseXor),
            _ => None,
        }
    }

    fn unop_from_kind(kind: &TokenKind) -> Option<UnaryOperator> {
        match kind {
            TokenKind::Minus => Some(UnaryOperator::Sub),
            TokenKind::Not => Some(UnaryOperator::Not),
            TokenKind::Tilde => Some(UnaryOperator::BitwiseNot),
            TokenKind::Ampersand => Some(UnaryOperator::Reference),
            _ => None,
        }
    }

    #[tracing::instrument(skip(self))]
    pub fn expression(&mut self) -> Result<Loc<Expression>> {
        let comptime = self.maybe_comptime(&Self::non_comptime_expression)?;

        Ok(comptime
            .inner
            .transpose(|i| Expression::Comptime(Box::new(i.clone())).at_loc(&i)))
    }

    /// We need a function like this in order to not run into parser conflicts when
    /// parsing blocks, since both statements and expressions can start with $if.
    #[tracing::instrument(skip(self))]
    pub fn non_comptime_expression(&mut self) -> Result<Loc<Expression>> {
        self.custom_infix_operator()
    }

    fn custom_infix_operator(&mut self) -> Result<Loc<Expression>> {
        let lhs_val = self.expr_bp(OpBindingPower::None)?;

        if self.peek_kind(&TokenKind::InfixOperatorSeparator)? {
            let (callee, _) = self.surrounded(
                &TokenKind::InfixOperatorSeparator,
                Self::path,
                &TokenKind::InfixOperatorSeparator,
            )?;

            let rhs_val = self.custom_infix_operator()?;

            Ok(Expression::Call {
                kind: CallKind::Function,
                callee,
                args: ArgumentList::Positional(vec![lhs_val.clone(), rhs_val.clone()]).between(
                    self.file_id,
                    &lhs_val,
                    &rhs_val,
                ),
            }
            .between(self.file_id, &lhs_val, &rhs_val))
        } else {
            Ok(lhs_val)
        }
    }

    // Based on matklads blog post on pratt parsing:
    // https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html
    fn expr_bp(&mut self, min_power: OpBindingPower) -> Result<Loc<Expression>> {
        let next_tok = self.peek()?;
        let mut lhs = if let Some((tok, op)) =
            Self::unop_from_kind(&next_tok.kind).map(|op| (next_tok, op))
        {
            self.eat_unconditional()?;
            let op_power = unop_binding_power(&op);

            let rhs = self.expr_bp(op_power)?;

            Expression::UnaryOperator(op, Box::new(rhs.clone())).between(self.file_id, &tok, &rhs)
        } else {
            self.base_expression()?
        };

        while let Some(op) = Self::binop_from_kind(&self.peek()?.kind) {
            let op_power = binop_binding_power(&op);

            if op_power <= min_power {
                break;
            }

            self.eat_unconditional()?;

            let rhs = self.expr_bp(op_power)?;
            lhs = Expression::BinaryOperator(Box::new(lhs.clone()), op, Box::new(rhs.clone()))
                .between(self.file_id, &lhs, &rhs)
        }

        Ok(lhs)
    }

    // Expression parsing

    #[trace_parser]
    fn base_expression(&mut self) -> Result<Loc<Expression>> {
        let expr = if let Some(tuple) = self.tuple_literal()? {
            Ok(tuple)
        } else if let Some(array) = self.array_literal()? {
            Ok(array)
        } else if let Some(instance) = self.entity_instance()? {
            Ok(instance)
        } else if let Some(val) = self.bool_literal()? {
            Ok(val.map(Expression::BoolLiteral))
        } else if let Some(val) = self.int_literal()? {
            Ok(val.map(Expression::IntLiteral))
        } else if let Some(block) = self.block(false)? {
            Ok(block.map(Box::new).map(Expression::Block))
        } else if let Some(if_expr) = self.if_expression()? {
            Ok(if_expr)
        } else if let Some(match_expr) = self.match_expression()? {
            Ok(match_expr)
        } else if let Some(operator) = self.unary_operator()? {
            Ok(operator)
        } else if let Some(stageref) = self.pipeline_reference()? {
            Ok(stageref)
        } else {
            match self.path() {
                Ok(path) => {
                    let span = path.span;
                    // Check if this is a function call by looking for an argument list
                    if let Some(args) = self.argument_list()? {
                        // Doing this avoids cloning result and args
                        let span = ().between(self.file_id, &path, &args);

                        Ok(Expression::Call {
                            kind: CallKind::Function,
                            callee: path,
                            args,
                        }
                        .at_loc(&span))
                    } else {
                        Ok(Expression::Identifier(path).at(self.file_id, &span))
                    }
                }
                Err(Error::UnexpectedToken { got, .. }) => Err(Error::ExpectedExpression { got }),
                Err(e) => Err(e),
            }
        }?;

        self.expression_suffix(expr)
    }

    fn unary_operator(&mut self) -> Result<Option<Loc<Expression>>> {
        let t = self.peek()?;
        let operator = match t.kind {
            TokenKind::Minus => Some(UnaryOperator::Sub.at(self.file_id, &t.span)),
            TokenKind::Not => Some(UnaryOperator::Not.at(self.file_id, &t.span)),
            TokenKind::Tilde => Some(UnaryOperator::BitwiseNot.at(self.file_id, &t.span)),
            TokenKind::Asterisk => Some(UnaryOperator::Dereference.at(self.file_id, &t.span)),
            _ => None,
        };

        Ok(match operator {
            Some(op) => {
                self.eat_unconditional()?;
                let expr = self.expression()?;
                Some(
                    Expression::UnaryOperator(op.inner.clone(), Box::new(expr.clone())).between(
                        self.file_id,
                        &op,
                        &expr,
                    ),
                )
            }
            None => None,
        })
    }

    #[trace_parser]
    fn expression_suffix(&mut self, expr: Loc<Expression>) -> Result<Loc<Expression>> {
        let base = if let Some(hash) = self.peek_and_eat(&TokenKind::Hash)? {
            if let Some(index) = self.int_literal()? {
                let index = index.try_map_ref(|idx| -> Result<u128> {
                    let as_u128 = idx
                        .clone()
                        .as_unsigned()
                        .ok_or_else(|| {
                            Diagnostic::error(&index, "Tuple indices must be positive")
                                .primary_label("Negative tuple index")
                        })?
                        .to_u128()
                        .ok_or_else(|| {
                            Diagnostic::bug(&index, "Tuple index too large")
                                .primary_label("Tuple index too large")
                                .note(format!("Tuple index can be at most {}", u128::MAX))
                        })?;

                    Ok(as_u128)
                })?;
                let span = expr.span.merge(lspan(hash.span));
                Ok(Expression::TupleIndex(Box::new(expr), index).at(self.file_id, &span))
            } else {
                Err(Error::MissingTupleIndex {
                    hash_loc: Loc::new((), lspan(hash.span), self.file_id),
                })
            }
        } else if self.peek_and_eat(&TokenKind::Dot)?.is_some() {
            let inst = self.peek_and_eat(&TokenKind::Instance)?;

            let field = self.identifier()?;

            if let Some(args) = self.argument_list()? {
                Ok(Expression::MethodCall {
                    target: Box::new(expr.clone()),
                    name: field.clone(),
                    args: args.clone(),
                    kind: inst
                        .map(|i| CallKind::Entity(().at(self.file_id, &i)))
                        .unwrap_or(CallKind::Function),
                }
                .between(self.file_id, &expr, &args))
            } else if let Some(inst_keyword) = inst {
                Err(ExpectedArgumentList {
                    next_token: self.peek()?,
                    base_expr: ().between(self.file_id, &inst_keyword, &field),
                }
                .with_suggestions()
                .into())
            } else {
                Ok(
                    Expression::FieldAccess(Box::new(expr.clone()), field.clone()).between(
                        self.file_id,
                        &expr,
                        &field,
                    ),
                )
            }
        } else if self.peek_kind(&TokenKind::OpenBracket)? {
            let (index, _) = self.surrounded(
                &TokenKind::OpenBracket,
                Self::expression,
                &TokenKind::CloseBracket,
            )?;

            Ok(
                Expression::Index(Box::new(expr.clone()), Box::new(index.clone())).between(
                    self.file_id,
                    &expr,
                    &index,
                ),
            )
        } else {
            return Ok(expr);
        }?;

        self.expression_suffix(base)
    }
}

#[cfg(test)]
mod test {
    use spade_ast::testutil::{ast_ident, ast_path};
    use spade_ast::*;
    use spade_common::num_ext::InfallibleToBigInt;

    use super::*;
    use crate::lexer::TokenKind;
    use crate::{check_parse, format_parse_stack};

    use colored::Colorize;
    use logos::Logos;

    use spade_common::location_info::WithLocation;

    #[test]
    fn addition_operatoins_are_expressions() {
        let expected_value = Expression::BinaryOperator(
            Box::new(Expression::Identifier(ast_path("a")).nowhere()),
            BinaryOperator::Add,
            Box::new(Expression::Identifier(ast_path("b")).nowhere()),
        )
        .nowhere();

        check_parse!("a + b", expression, Ok(expected_value));
    }

    #[test]
    fn unary_suptraction_works() {
        let expected_value = Expression::UnaryOperator(
            UnaryOperator::Sub,
            Box::new(Expression::Identifier(ast_path("b")).nowhere()),
        )
        .nowhere();

        check_parse!("- b", expression, Ok(expected_value));
    }

    #[test]
    fn not_operator_works() {
        let expected_value = Expression::UnaryOperator(
            UnaryOperator::Not,
            Box::new(Expression::Identifier(ast_path("b")).nowhere()),
        )
        .nowhere();

        check_parse!("!b", expression, Ok(expected_value));
    }

    #[test]
    fn bitwise_and_operatoins_are_expressions() {
        let expected_value = Expression::BinaryOperator(
            Box::new(Expression::Identifier(ast_path("a")).nowhere()),
            BinaryOperator::BitwiseAnd,
            Box::new(Expression::Identifier(ast_path("b")).nowhere()),
        )
        .nowhere();

        check_parse!("a & b", expression, Ok(expected_value));
    }

    #[test]
    fn bitwise_or_operatoins_are_expressions() {
        let expected_value = Expression::BinaryOperator(
            Box::new(Expression::Identifier(ast_path("a")).nowhere()),
            BinaryOperator::BitwiseOr,
            Box::new(Expression::Identifier(ast_path("b")).nowhere()),
        )
        .nowhere();

        check_parse!("a | b", expression, Ok(expected_value));
    }

    #[test]
    fn multiplications_are_expressions() {
        let expected_value = Expression::BinaryOperator(
            Box::new(Expression::Identifier(ast_path("a")).nowhere()),
            BinaryOperator::Mul,
            Box::new(Expression::Identifier(ast_path("b")).nowhere()),
        )
        .nowhere();

        check_parse!("a * b", expression, Ok(expected_value));
    }

    #[test]
    fn multiplication_before_addition() {
        let expected_value = Expression::BinaryOperator(
            Box::new(
                Expression::BinaryOperator(
                    Box::new(Expression::Identifier(ast_path("a")).nowhere()),
                    BinaryOperator::Mul,
                    Box::new(Expression::Identifier(ast_path("b")).nowhere()),
                )
                .nowhere(),
            ),
            BinaryOperator::Add,
            Box::new(Expression::Identifier(ast_path("c")).nowhere()),
        )
        .nowhere();

        check_parse!("a*b + c", expression, Ok(expected_value));
    }

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

        check_parse!("a+b == c", expression, Ok(expected_value));
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

            check_parse!("a == b && c", expression, Ok(expected_value));
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

            check_parse!("a && b == c", expression, Ok(expected_value));
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

        check_parse!("a + (b + c)", expression, Ok(expected_value));
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

        check_parse!("((b + c) + a)", expression, Ok(expected_value));
    }

    #[test]
    fn functions_work() {
        let code = "test(1, 2)";

        let expected = Expression::Call {
            kind: CallKind::Function,
            callee: ast_path("test"),
            args: ArgumentList::Positional(vec![
                Expression::int_literal(1).nowhere(),
                Expression::int_literal(2).nowhere(),
            ])
            .nowhere(),
        }
        .nowhere();

        check_parse!(code, expression, Ok(expected));
    }

    #[test]
    fn functions_with_named_arguments_work() {
        let code = "test$(a, b)";

        let expected = Expression::Call {
            kind: CallKind::Function,
            callee: ast_path("test"),
            args: ArgumentList::Named(vec![
                NamedArgument::Short(ast_ident("a")),
                NamedArgument::Short(ast_ident("b")),
            ])
            .nowhere(),
        }
        .nowhere();

        check_parse!(code, expression, Ok(expected));
    }

    #[test]
    fn tuple_literals_parse() {
        let code = "(1, true)";

        let expected = Expression::TupleLiteral(vec![
            Expression::int_literal(1).nowhere(),
            Expression::BoolLiteral(true).nowhere(),
        ])
        .nowhere();

        check_parse!(code, expression, Ok(expected));
    }

    #[test]
    fn array_literals_parse() {
        let code = "[1, 2, 3]";

        let expected = Expression::ArrayLiteral(vec![
            Expression::int_literal(1).nowhere(),
            Expression::int_literal(2).nowhere(),
            Expression::int_literal(3).nowhere(),
        ])
        .nowhere();

        check_parse!(code, expression, Ok(expected));
    }

    #[test]
    fn array_indexing_works() {
        let code = "a[0]";

        let expected = Expression::Index(
            Box::new(Expression::Identifier(ast_path("a")).nowhere()),
            Box::new(Expression::int_literal(0).nowhere()),
        )
        .nowhere();

        check_parse!(code, expression, Ok(expected));
    }

    #[test]
    fn tuple_indexing_parsese() {
        let code = "a#0";

        let expected = Expression::TupleIndex(
            Box::new(Expression::Identifier(ast_path("a")).nowhere()),
            Loc::new(0, ().nowhere().span, 0),
        )
        .nowhere();

        check_parse!(code, expression, Ok(expected));
    }

    #[test]
    fn field_access_parses() {
        let code = "a.b";
        let expected = Expression::FieldAccess(
            Box::new(Expression::Identifier(ast_path("a")).nowhere()),
            ast_ident("b"),
        )
        .nowhere();

        check_parse!(code, expression, Ok(expected));
    }

    #[test]
    fn method_call_parses() {
        let code = "a.b(x)";

        let expected = Expression::MethodCall {
            target: Box::new(Expression::Identifier(ast_path("a")).nowhere()),
            name: ast_ident("b"),
            args: ArgumentList::Positional(vec![Expression::Identifier(ast_path("x")).nowhere()])
                .nowhere(),
            kind: CallKind::Function,
        }
        .nowhere();

        check_parse!(code, expression, Ok(expected));
    }

    #[test]
    fn inst_method_call_parses() {
        let code = "a.inst b(x)";

        let expected = Expression::MethodCall {
            target: Box::new(Expression::Identifier(ast_path("a")).nowhere()),
            name: ast_ident("b"),
            args: ArgumentList::Positional(vec![Expression::Identifier(ast_path("x")).nowhere()])
                .nowhere(),
            kind: CallKind::Entity(().nowhere()),
        }
        .nowhere();

        check_parse!(code, expression, Ok(expected));
    }

    #[test]
    fn method_call_with_named_args_works() {
        let code = "a.b$(x: y)";

        let expected = Expression::MethodCall {
            target: Box::new(Expression::Identifier(ast_path("a")).nowhere()),
            name: ast_ident("b"),
            args: ArgumentList::Named(vec![NamedArgument::Full(
                ast_ident("x"),
                Expression::Identifier(ast_path("y")).nowhere(),
            )])
            .nowhere(),
            kind: CallKind::Function,
        }
        .nowhere();

        check_parse!(code, expression, Ok(expected));
    }

    #[test]
    fn tuple_type_specs_work() {
        let code = "(int, bool)";

        let expected = TypeSpec::Tuple(vec![
            TypeSpec::Named(ast_path("int"), None).nowhere(),
            TypeSpec::Named(ast_path("bool"), None).nowhere(),
        ])
        .nowhere();

        check_parse!(code, type_spec, Ok(expected));
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
                    Pattern::Tuple(vec![Pattern::integer(0).nowhere(), Pattern::name("y")])
                        .nowhere(),
                    Expression::Identifier(ast_path("y")).nowhere(),
                ),
                (
                    Pattern::Tuple(vec![Pattern::name("x"), Pattern::name("y")]).nowhere(),
                    Expression::Identifier(ast_path("x")).nowhere(),
                ),
            ]
            .nowhere(),
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
                Expression::int_literal(0).nowhere(),
            )
            .nowhere()],
            result: Expression::int_literal(1).nowhere(),
        }
        .nowhere();

        check_parse!(code, block(false), Ok(Some(expected)));
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
                Expression::int_literal(0).nowhere(),
            )
            .nowhere()],
            result: Expression::int_literal(1).nowhere(),
        }))
        .nowhere();

        check_parse!(code, expression, Ok(expected));
    }

    #[test]
    fn infix_operators_work() {
        let code = r#"
            1 `infix` 2
            "#;

        let expected = Expression::Call {
            kind: CallKind::Function,
            callee: ast_path("infix"),
            args: ArgumentList::Positional(vec![
                Expression::int_literal(1).nowhere(),
                Expression::int_literal(2).nowhere(),
            ])
            .nowhere(),
        }
        .nowhere();

        check_parse!(code, expression, Ok(expected));
    }

    #[test]
    fn infix_operator_precedence_is_unchanged() {
        // NOTE: the exact ordering here is somewhat unimportant, in general one
        // should probably put parentheses around infix operators anyway. The main
        // purpose of this test is to prevent accidental changes to the order in the future
        let code = r#"
            0 || 1 `infix` 2 `infix` 3
            "#;

        let expected = Expression::Call {
            kind: CallKind::Function,
            callee: ast_path("infix"),
            args: ArgumentList::Positional(vec![
                Expression::BinaryOperator(
                    Box::new(Expression::int_literal(0).nowhere()),
                    BinaryOperator::LogicalOr,
                    Box::new(Expression::int_literal(1).nowhere()),
                )
                .nowhere(),
                Expression::Call {
                    kind: CallKind::Function,
                    callee: ast_path("infix"),
                    args: ArgumentList::Positional(vec![
                        Expression::int_literal(2).nowhere(),
                        Expression::int_literal(3).nowhere(),
                    ])
                    .nowhere(),
                }
                .nowhere(),
            ])
            .nowhere(),
        }
        .nowhere();

        check_parse!(code, expression, Ok(expected));
    }

    #[test]
    fn field_access_operator_does_not_require_parens() {
        let code = r#"x.y.z"#;

        let expected = Expression::FieldAccess(
            Box::new(
                Expression::FieldAccess(
                    Box::new(Expression::Identifier(ast_path("x")).nowhere()),
                    ast_ident("y"),
                )
                .nowhere(),
            ),
            ast_ident("z"),
        )
        .nowhere();

        check_parse!(code, expression, Ok(expected));
    }

    #[test]
    fn array_index_operator_precedence_is_correct() {
        let code = r#"x && y[z]"#;

        let expected = Expression::BinaryOperator(
            Box::new(Expression::Identifier(ast_path("x")).nowhere()),
            BinaryOperator::LogicalAnd,
            Box::new(
                Expression::Index(
                    Box::new(Expression::Identifier(ast_path("y")).nowhere()),
                    Box::new(Expression::Identifier(ast_path("z")).nowhere()),
                )
                .nowhere(),
            ),
        )
        .nowhere();

        check_parse!(code, expression, Ok(expected));
    }

    #[test]
    fn tuple_index_operator_precedence_is_correct() {
        let code = r#"y#1#2"#;

        let expected = Expression::TupleIndex(
            Box::new(
                Expression::TupleIndex(
                    Box::new(Expression::Identifier(ast_path("y")).nowhere()),
                    1u128.nowhere(),
                )
                .nowhere(),
            ),
            2.nowhere(),
        )
        .nowhere();

        check_parse!(code, expression, Ok(expected));
    }

    #[test]
    fn absolute_pipeline_references_parse() {
        let code = r#"stage(s).var"#;

        let expected = Expression::PipelineReference {
            stage_kw_and_reference_loc: ().nowhere(),
            stage: PipelineStageReference::Absolute(ast_ident("s")),
            name: ast_ident("var"),
        }
        .nowhere();

        check_parse!(code, expression, Ok(expected));
    }

    #[test]
    fn relative_forward_pipeline_references_parse() {
        let code = r#"stage(+5).var"#;

        let expected = Expression::PipelineReference {
            stage_kw_and_reference_loc: ().nowhere(),
            stage: PipelineStageReference::Relative(5.to_bigint().nowhere()),
            name: ast_ident("var"),
        }
        .nowhere();

        check_parse!(code, expression, Ok(expected));
    }

    #[test]
    fn relative_backward_pipeline_references_parse() {
        let code = r#"stage(-5).var"#;

        let expected = Expression::PipelineReference {
            stage_kw_and_reference_loc: ().nowhere(),
            stage: PipelineStageReference::Relative((-5).to_bigint().nowhere()),
            name: ast_ident("var"),
        }
        .nowhere();

        check_parse!(code, expression, Ok(expected));
    }

    // Precedence related tests
    #[test]
    fn subtraction_occurs_in_correct_order() {
        let expected_value = Expression::BinaryOperator(
            Box::new(
                Expression::BinaryOperator(
                    Box::new(Expression::Identifier(ast_path("a")).nowhere()),
                    BinaryOperator::Sub,
                    Box::new(Expression::Identifier(ast_path("b")).nowhere()),
                )
                .nowhere(),
            ),
            BinaryOperator::Sub,
            Box::new(Expression::Identifier(ast_path("c")).nowhere()),
        )
        .nowhere();

        check_parse!("a - b - c", expression, Ok(expected_value));
    }

    #[test]
    fn not_function_call_does_not_invert_function() {
        let expected_value = Expression::UnaryOperator(
            UnaryOperator::Not,
            Box::new(
                Expression::Call {
                    kind: CallKind::Function,
                    callee: ast_path("a"),
                    args: ArgumentList::Positional(vec![]).nowhere(),
                }
                .nowhere(),
            ),
        )
        .nowhere();

        check_parse!("!a()", expression, Ok(expected_value));
    }

    #[test]
    fn chained_array_indexing_is_left_to_right() {
        let expected_value = Expression::Index(
            Box::new(
                Expression::Index(
                    Box::new(Expression::Identifier(ast_path("a")).nowhere()),
                    Box::new(Expression::Identifier(ast_path("b")).nowhere()),
                )
                .nowhere(),
            ),
            Box::new(Expression::Identifier(ast_path("c")).nowhere()),
        )
        .nowhere();

        check_parse!("a[b][c]", expression, Ok(expected_value));
    }

    #[test]
    fn not_index_result_inverts_whole_result() {
        let expected_value = Expression::UnaryOperator(
            UnaryOperator::Not,
            Box::new(
                Expression::Index(
                    Box::new(Expression::Identifier(ast_path("a")).nowhere()),
                    Box::new(Expression::Identifier(ast_path("b")).nowhere()),
                )
                .nowhere(),
            ),
        )
        .nowhere();

        check_parse!("!a[b]", expression, Ok(expected_value));
    }

    #[test]
    fn unary_sub_binds_correctly() {
        let expexte_value = Expression::BinaryOperator(
            Box::new(
                Expression::UnaryOperator(
                    UnaryOperator::Sub,
                    Box::new(Expression::Identifier(ast_path("a")).nowhere()),
                )
                .nowhere(),
            ),
            BinaryOperator::Add,
            Box::new(Expression::Identifier(ast_path("b")).nowhere()),
        )
        .nowhere();

        check_parse!("-a + b", expression, Ok(expexte_value));
    }

    #[test]
    fn deref_operator_works() {
        let expected = Expression::UnaryOperator(
            UnaryOperator::Dereference,
            Box::new(Expression::Identifier(ast_path("a")).nowhere()),
        )
        .nowhere();

        check_parse!("*a", expression, Ok(expected));
    }

    #[test]
    fn ref_operator_works() {
        let expected = Expression::UnaryOperator(
            UnaryOperator::Reference,
            Box::new(Expression::Identifier(ast_path("a")).nowhere()),
        )
        .nowhere();

        check_parse!("&a", expression, Ok(expected));
    }
}
