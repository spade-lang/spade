// This algorithm is based off the excelent lecture here
// https://www.youtube.com/watch?v=xJXcZp2vgLs

use std::collections::HashMap;

use colored::*;
use parse_tree_macros::trace_typechecker;

use crate::hir::Entity;
use crate::hir::{ExprKind, Expression};
use crate::types::Type;
use crate::{global_symbols::GlobalSymbols, hir::Statement};
use crate::{hir::Block, location_info::Loc};

pub mod equation;
pub mod result;

use equation::{TypeEquations, TypeVar, TypedExpression};
use result::{Error, Result};

use self::result::UnificationError;

pub struct TypeState<'a> {
    equations: TypeEquations,
    _global_symbols: &'a GlobalSymbols,
    next_typeid: u64,

    pub trace_stack: Vec<TraceStack>,
}

impl<'a> TypeState<'a> {
    pub fn new(global_symbols: &'a GlobalSymbols) -> Self {
        Self {
            equations: HashMap::new(),
            _global_symbols: global_symbols,
            next_typeid: 0,
            trace_stack: vec![],
        }
    }

    /// Returns the type of the expression with the specified id. Error if unknown
    pub fn type_of(&self, expr: &TypedExpression) -> Result<TypeVar> {
        for (e, t) in &self.equations {
            if e == expr {
                return Ok(t.clone());
            }
        }
        Err(Error::UnknownType(expr.clone()).into())
    }

    // /// Visit an item to assign type variables and equations to every subexpression
    // /// in the item
    // pub fn visit_item(&mut self, item: &Item) {
    //     match item {
    //         Item::Entity(e) => self.visit_entity(&e.inner),
    //     }
    // }

    #[trace_typechecker]
    pub fn visit_entity(&mut self, entity: &Entity) -> Result<()> {
        // Add equations for the inputs
        for (name, t) in &entity.inputs {
            self.add_equation(
                TypedExpression::Name(name.clone().to_path()),
                TypeVar::Known(t.inner.clone(), Some(t.loc())),
            );
        }

        self.visit_expression(&entity.body)?;

        // Ensure that the output type matches what the user specified
        self.unify_types(
            &TypedExpression::Id(entity.body.inner.id),
            &entity.output_type.inner,
        )
        .map_err(|(got, expected)| Error::EntityOutputTypeMissmatch {
            expected,
            got,
            type_spec: entity.output_type.loc(),
            output_expr: entity.body.loc(),
        })?;
        Ok(())
    }

    #[trace_typechecker]
    pub fn visit_expression(&mut self, expression: &Loc<Expression>) -> Result<()> {
        let new_id = self.new_typeid();
        self.add_equation(
            TypedExpression::Id(expression.inner.id),
            TypeVar::Generic(new_id),
        );
        // Recurse down the expression
        match &expression.inner.kind {
            ExprKind::Identifier(ident) => {
                // Add an equation for the anonymous id
                self.unify_expression_generic_error(
                    &expression,
                    &TypedExpression::Name(ident.inner.clone()),
                )?;
            }
            ExprKind::IntLiteral(_) => {
                self.unify_types(&Type::KnownInt, &expression.inner)
                    .map_err(|(_, got)| Error::IntLiteralIncompatible {
                        got,
                        loc: expression.loc(),
                    })?;
            }
            ExprKind::BoolLiteral(_) => {
                unimplemented! {}
            }
            ExprKind::FnCall(_, _) => {
                unimplemented! {}
            }
            ExprKind::Block(block) => {
                self.visit_block(block)?;

                // Unify the return type of the block with the type of this expression
                self.unify_types(&expression.inner, &block.result.inner)
                    // NOTE: We could be more specific about this error specifying
                    // that the type of the block must match the return type, though
                    // that might just be spammy.
                    .map_err(|(expected, got)| Error::UnspecifiedTypeError {
                        expected,
                        got,
                        loc: block.result.loc(),
                    })?;
            }
            ExprKind::If(cond, on_true, on_false) => {
                self.visit_expression(&cond)?;
                self.visit_expression(&on_true)?;
                self.visit_expression(&on_false)?;

                self.unify_types(&cond.inner, &Type::Bool)
                    .map_err(|(got, _)| Error::NonBooleanCondition {
                        got,
                        loc: cond.loc(),
                    })?;
                self.unify_types(&on_true.inner, &on_false.inner)
                    .map_err(|(expected, got)| Error::IfConditionMissmatch {
                        expected,
                        got,
                        first_branch: on_true.loc(),
                        incorrect_branch: on_false.loc(),
                    })?;
                self.unify_types(expression, &on_false.inner)
                    .map_err(|(got, expected)| Error::UnspecifiedTypeError {
                        expected,
                        got,
                        loc: expression.loc(),
                    })?;
            }
        }
        Ok(())
    }

    #[trace_typechecker]
    pub fn visit_block(&mut self, block: &Block) -> Result<()> {
        if !block.statements.is_empty() {
            todo!("Blocks with statements are currently not type checked")
        }
        self.visit_expression(&block.result)
    }

    pub fn visit_statement(&mut self, _statement: &Statement) {
        unimplemented!()
    }
}

// Private helper functions
impl<'a> TypeState<'a> {
    fn new_typeid(&mut self) -> u64 {
        let result = self.next_typeid;
        self.next_typeid += 1;
        result
    }

    fn add_equation(&mut self, expression: TypedExpression, var: TypeVar) {
        self.trace_stack
            .push(TraceStack::AddingEquation(expression.clone(), var.clone()));
        self.equations.insert(expression, var);
    }

    fn unify_types(
        &mut self,
        e1: &impl HasType,
        e2: &impl HasType,
    ) -> std::result::Result<(), UnificationError> {
        let v1 = e1
            .get_type(self)
            .expect("Tried to unify types but the lhs was not found");
        let v2 = e2
            .get_type(self)
            .expect("Tried to unify types but the rhs was not found");

        // Used because we want to avoid borrowchecker errors when we add stuff to the
        // trace
        let v1cpy = v1.clone();
        let v2cpy = v2.clone();
        // Figure out the most general type, and take note if we need to
        // do any replacement of the types in the rest of the state
        let (new_type, replaced_type) = match (&v1, &v2) {
            (TypeVar::Known(t1, _), TypeVar::Known(t2, _)) => {
                if t1 == t2 {
                    Ok((v1, None))
                } else {
                    Err((v1.clone(), v2.clone()))
                }
            }
            (TypeVar::Known(_, _), TypeVar::Generic(_)) => Ok((v1, Some(v2))),
            (TypeVar::Generic(_), TypeVar::Known(_, _)) => Ok((v2, Some(v1))),
            (TypeVar::Generic(_), TypeVar::Generic(_)) => Ok((v1, Some(v2))),
        }?;

        if let Some(replaced_type) = replaced_type {
            for (_, rhs) in &mut self.equations {
                if *rhs == replaced_type {
                    *rhs = new_type.clone()
                }
            }
        }

        self.trace_stack
            .push(TraceStack::Unified(v1cpy, v2cpy, new_type.clone()));
        Ok(())
    }

    fn unify_expression_generic_error(
        &mut self,
        expr: &Loc<Expression>,
        other: &impl HasType,
    ) -> Result<()> {
        self.unify_types(&expr.inner, other)
            .map_err(|(got, expected)| Error::UnspecifiedTypeError {
                got,
                expected,
                loc: expr.loc(),
            })
    }
}

#[cfg(test)]
impl<'a> TypeState<'a> {
    pub fn print_equations(&self) {
        for (lhs, rhs) in &self.equations {
            println!("{:?}: {:?}", lhs, rhs);
        }
    }
}

pub trait HasType {
    fn get_type<'a>(&self, state: &TypeState<'a>) -> Result<TypeVar>;
}

impl HasType for TypeVar {
    fn get_type<'a>(&self, _: &TypeState<'a>) -> Result<TypeVar> {
        Ok(self.clone())
    }
}
impl HasType for TypedExpression {
    fn get_type<'a>(&self, state: &TypeState<'a>) -> Result<TypeVar> {
        state.type_of(self)
    }
}
impl HasType for Expression {
    fn get_type<'a>(&self, state: &TypeState<'a>) -> Result<TypeVar> {
        state.type_of(&TypedExpression::Id(self.id))
    }
}
impl HasType for Loc<Expression> {
    fn get_type<'a>(&self, state: &TypeState<'a>) -> Result<TypeVar> {
        state.type_of(&TypedExpression::Id(self.inner.id))
    }
}
impl HasType for Type {
    fn get_type<'a>(&self, _: &TypeState<'a>) -> Result<TypeVar> {
        Ok(TypeVar::Known(self.clone(), None))
    }
}
impl HasType for Loc<Type> {
    fn get_type<'a>(&self, _: &TypeState<'a>) -> Result<TypeVar> {
        Ok(TypeVar::Known(self.inner.clone(), Some(self.loc())))
    }
}

pub enum TraceStack {
    /// Entering the specified visitor
    Enter(String),
    /// Exited the most recent visitor and the node had the specified type
    Exit,
    /// Unified .0 with .1 producing .2
    Unified(TypeVar, TypeVar, TypeVar),
    AddingEquation(TypedExpression, TypeVar),
}

pub fn format_trace_stack(stack: &[TraceStack]) -> String {
    let mut result = String::new();
    let mut indent_amount = 0;

    for entry in stack {
        let mut next_indent_amount = indent_amount;
        let message = match entry {
            TraceStack::Enter(function) => {
                next_indent_amount += 1;
                format!("{} `{}`", "visiting".white(), function.blue())
            }
            TraceStack::AddingEquation(expr, t) => {
                format!("{} {:?} <- {:?}", "eq".yellow(), expr, t)
            }
            TraceStack::Unified(lhs, rhs, result) => {
                format!("{} {:?}, {:?} -> {:?}", "unified".green(), lhs, rhs, result)
            }
            TraceStack::Exit => {
                next_indent_amount -= 1;
                format!("")
            }
        };
        if let TraceStack::Exit = entry {
        } else {
            for _ in 0..indent_amount {
                result += "| ";
            }
            result += &message;
            result += "\n";
        }
        indent_amount = next_indent_amount;
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    use super::TypeVar as TVar;
    use super::TypedExpression as TExpr;

    use crate::location_info::WithLocation;
    use crate::{
        assert_matches,
        hir::{Block, Identifier, Path},
    };

    macro_rules! get_type {
        ($state:ident, $e:expr) => {
            if let Ok(t) = $state.type_of($e) {
                t
            } else {
                println!("{}", format_trace_stack(&$state.trace_stack));
                panic!("Failed to get type of {:?}", $e)
            }
        };
    }

    macro_rules! ensure_same_type {
        ($state:ident, $t1:expr, $t2:expr) => {
            if $t1.get_type(&$state) != $t2.get_type(&$state) {
                println!("{}", format_trace_stack(&$state.trace_stack));
                $state.print_equations();
                panic!("Types are not the same")
            }
        };
    }

    #[test]
    fn int_literals_have_type_known_int() {
        let symtab = GlobalSymbols::new();
        let mut state = TypeState::new(&symtab);

        let input = ExprKind::IntLiteral(0).with_id(0).nowhere();

        state.visit_expression(&input).expect("Type error");

        assert_eq!(
            state.type_of(&TExpr::Id(0)),
            Ok(TVar::Known(Type::KnownInt, None))
        );
    }

    #[test]
    fn if_statements_have_correctly_infered_types() {
        let symtab = GlobalSymbols::new();
        let mut state = TypeState::new(&symtab);

        let input = ExprKind::If(
            Box::new(Expression::ident(0, "a").nowhere()),
            Box::new(Expression::ident(1, "b").nowhere()),
            Box::new(Expression::ident(2, "c").nowhere()),
        )
        .with_id(3)
        .nowhere();

        // Add eqs for the literals
        let expr_a = TExpr::Name(Path::from_strs(&["a"]));
        let expr_b = TExpr::Name(Path::from_strs(&["b"]));
        let expr_c = TExpr::Name(Path::from_strs(&["c"]));
        state.add_equation(expr_a.clone(), TVar::Generic(100));
        state.add_equation(expr_b.clone(), TVar::Generic(101));
        state.add_equation(expr_c.clone(), TVar::Generic(102));

        state.visit_expression(&input).unwrap();

        let t0 = get_type!(state, &TExpr::Id(0));
        let t1 = get_type!(state, &TExpr::Id(1));
        let t2 = get_type!(state, &TExpr::Id(2));
        let t3 = get_type!(state, &TExpr::Id(3));

        let ta = get_type!(state, &expr_a);
        let tb = get_type!(state, &expr_b);
        let tc = get_type!(state, &expr_c);

        // Check the generic type variables
        ensure_same_type!(state, t0, TVar::Known(Type::Bool, None));
        ensure_same_type!(state, t1, t2);
        ensure_same_type!(state, t1, t3);

        // Check the constraints added to the literals
        ensure_same_type!(state, t0, ta);
        ensure_same_type!(state, t1, tb);
        ensure_same_type!(state, t2, tc);
    }

    #[test]
    fn if_statements_get_correct_type_when_branches_are_of_known_type() {
        let symtab = GlobalSymbols::new();
        let mut state = TypeState::new(&symtab);

        let input = ExprKind::If(
            Box::new(Expression::ident(0, "a").nowhere()),
            Box::new(Expression::ident(1, "b").nowhere()),
            Box::new(Expression::ident(2, "c").nowhere()),
        )
        .with_id(3)
        .nowhere();

        // Add eqs for the literals
        let expr_a = TExpr::Name(Path::from_strs(&["a"]));
        let expr_b = TExpr::Name(Path::from_strs(&["b"]));
        let expr_c = TExpr::Name(Path::from_strs(&["c"]));
        state.add_equation(expr_a.clone(), TVar::Generic(100));
        state.add_equation(expr_b.clone(), TVar::Known(Type::KnownInt, None));
        state.add_equation(expr_c.clone(), TVar::Generic(102));

        state.visit_expression(&input).unwrap();

        let t0 = get_type!(state, &TExpr::Id(0));
        let t1 = get_type!(state, &TExpr::Id(1));
        let t2 = get_type!(state, &TExpr::Id(2));
        let t3 = get_type!(state, &TExpr::Id(3));

        let ta = get_type!(state, &expr_a);
        let tb = get_type!(state, &expr_b);
        let tc = get_type!(state, &expr_c);

        // Check the generic type variables
        ensure_same_type!(state, t0, TVar::Known(Type::Bool, None));
        ensure_same_type!(state, t1, TVar::Known(Type::KnownInt, None));
        ensure_same_type!(state, t2, TVar::Known(Type::KnownInt, None));
        ensure_same_type!(state, t3, TVar::Known(Type::KnownInt, None));

        // Check the constraints added to the literals
        ensure_same_type!(state, t0, ta);
        ensure_same_type!(state, t1, tb);
        ensure_same_type!(state, t2, tc);
    }

    #[test]
    fn type_inference_fails_if_if_branches_have_incompatible_types() {
        let symtab = GlobalSymbols::new();
        let mut state = TypeState::new(&symtab);

        let input = ExprKind::If(
            Box::new(Expression::ident(0, "a").nowhere()),
            Box::new(Expression::ident(1, "b").nowhere()),
            Box::new(Expression::ident(2, "c").nowhere()),
        )
        .with_id(3)
        .nowhere();

        // Add eqs for the literals
        let expr_a = TExpr::Name(Path::from_strs(&["a"]));
        let expr_b = TExpr::Name(Path::from_strs(&["b"]));
        let expr_c = TExpr::Name(Path::from_strs(&["c"]));
        state.add_equation(expr_a.clone(), TVar::Generic(100));
        state.add_equation(expr_b.clone(), TVar::Known(Type::KnownInt, None));
        state.add_equation(expr_c.clone(), TVar::Known(Type::Clock, None));

        assert_ne!(state.visit_expression(&input), Ok(()));
    }

    #[test]
    fn type_inference_for_entities_works() {
        let input = Entity {
            name: Identifier::Named("test".to_string()).nowhere(),
            inputs: vec![(
                Identifier::Named("input".to_string()).nowhere(),
                Type::Int(5).nowhere(),
            )],
            output_type: Type::Int(5).nowhere(),
            body: ExprKind::Identifier(Path::from_strs(&["input"]).nowhere())
                .with_id(0)
                .nowhere(),
        };

        let symtab = GlobalSymbols::new();
        let mut state = TypeState::new(&symtab);

        state.visit_entity(&input).unwrap();

        let t0 = get_type!(state, &TExpr::Id(0));
        ensure_same_type!(state, t0, TypeVar::Known(Type::Int(5), None));
    }

    #[test]
    fn entity_return_types_must_match() {
        let input = Entity {
            name: Identifier::Named("test".to_string()).nowhere(),
            inputs: vec![(
                Identifier::Named("input".to_string()).nowhere(),
                Type::Int(5).nowhere(),
            )],
            output_type: Type::Bool.nowhere(),
            body: ExprKind::Identifier(Path::from_strs(&["input"]).nowhere())
                .with_id(0)
                .nowhere(),
        };

        let symtab = GlobalSymbols::new();
        let mut state = TypeState::new(&symtab);

        assert_matches!(
            state.visit_entity(&input),
            Err(Error::EntityOutputTypeMissmatch { .. })
        );
    }

    #[test]
    fn block_visiting_without_definitions_works() {
        let input = ExprKind::Block(Box::new(Block {
            statements: vec![],
            result: ExprKind::IntLiteral(5).with_id(0).nowhere(),
        }))
        .with_id(1)
        .nowhere();

        let symtab = GlobalSymbols::new();
        let mut state = TypeState::new(&symtab);

        state.visit_expression(&input).unwrap();

        ensure_same_type!(state, TExpr::Id(0), TVar::Known(Type::KnownInt, None));
        ensure_same_type!(state, TExpr::Id(1), TVar::Known(Type::KnownInt, None));
    }
}
