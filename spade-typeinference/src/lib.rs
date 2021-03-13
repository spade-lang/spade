// This algorithm is based off the excelent lecture here
// https://www.youtube.com/watch?v=xJXcZp2vgLs

use parse_tree_macros::trace_typechecker;
use spade_common::location_info::Loc;
use spade_hir as hir;
use spade_hir::{
    expression::BinaryOperator, Block, Entity, ExprKind, Expression, NameID, Register, Statement,
};
use spade_types::{BaseType, ConcreteType, KnownType};

use std::collections::HashMap;

use colored::*;

pub mod equation;
pub mod error_reporting;
pub mod fixed_types;
pub mod result;

use crate::fixed_types::t_clock;
use crate::fixed_types::{t_bool, t_int};

use equation::{TypeEquations, TypeVar, TypedExpression};
use result::{Error, Result};

use self::result::{UnificationError, UnificationErrorExt, UnificationTrace};

pub struct TypeState {
    equations: TypeEquations,
    next_typeid: u64,

    pub trace_stack: Vec<TraceStack>,
}

impl TypeState {
    pub fn new() -> Self {
        Self {
            equations: HashMap::new(),
            next_typeid: 0,
            trace_stack: vec![],
        }
    }

    pub fn hir_type_expr_to_var(e: &hir::TypeExpression) -> TypeVar {
        match e {
            hir::TypeExpression::Integer(i) => TypeVar::Known(KnownType::Integer(*i), vec![], None),
            hir::TypeExpression::TypeSpec(spec) => Self::type_var_from_hir(spec),
        }
    }

    pub fn type_var_from_hir(hir_type: &crate::hir::TypeSpec) -> TypeVar {
        match hir_type {
            hir::TypeSpec::Concrete(base, params) => {
                let params = params
                    .into_iter()
                    .map(|e| Self::hir_type_expr_to_var(e))
                    .collect();

                TypeVar::Known(KnownType::Type(base.inner.clone()), params, None)
            }
            hir::TypeSpec::Tuple(inner) => {
                let inner = inner.iter().map(|t| Self::type_var_from_hir(t)).collect();
                TypeVar::Tuple(inner)
            }
            hir::TypeSpec::Generic(_) => {
                todo!("Support generic parameters")
            }
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

    /// Converts the specified type to a concrete type, returning None
    /// if it fails
    pub fn ungenerify_type(var: &TypeVar) -> Option<ConcreteType> {
        match var {
            TypeVar::Known(t, params, _) => {
                let params = params
                    .iter()
                    .map(Self::ungenerify_type)
                    .collect::<Option<Vec<_>>>()?;

                Some(ConcreteType::Single {
                    base: t.clone(),
                    params,
                })
            }
            TypeVar::Tuple(inner) => {
                let inner = inner
                    .iter()
                    .map(Self::ungenerify_type)
                    .collect::<Option<Vec<_>>>()?;
                Some(ConcreteType::Tuple(inner))
            }
            TypeVar::Generic(_) => None,
        }
    }

    /// Returns the type of the specified name as a concrete type. If the type is not known,
    /// or tye type is Generic, panics
    pub fn type_of_name(&self, name: &NameID) -> ConcreteType {
        Self::ungenerify_type(
            &self
                .type_of(&TypedExpression::Name(name.clone()))
                .expect("Expression had no specified type"),
        )
        .expect("Expr had generic type")
    }

    pub fn new_generic_int(&mut self) -> TypeVar {
        TypeVar::Known(t_int(), vec![self.new_generic()], None)
    }

    fn new_generic(&mut self) -> TypeVar {
        let id = self.new_typeid();
        TypeVar::Generic(id)
    }

    #[trace_typechecker]
    pub fn visit_entity(&mut self, entity: &Entity) -> Result<()> {
        // Add equations for the inputs
        for (name, t) in &entity.head.inputs {
            self.add_equation(
                TypedExpression::Name(name.clone()),
                Self::type_var_from_hir(t),
            );
        }

        self.visit_expression(&entity.body)?;

        // Ensure that the output type matches what the user specified, and unit otherwise
        if let Some(output_type) = &entity.head.output_type {
            self.unify_types(
                &TypedExpression::Id(entity.body.inner.id),
                &Self::type_var_from_hir(&output_type),
            )
            .map_err(|(got, expected)| Error::EntityOutputTypeMissmatch {
                expected,
                got,
                type_spec: output_type.loc(),
                output_expr: entity.body.loc(),
            })?;
        } else {
            self.unify_types(
                &TypedExpression::Id(entity.body.inner.id),
                &TypeVar::Known(KnownType::Type(BaseType::Unit), vec![], None),
            )
            .map_err(|(got, expected)| Error::UnspecedEntityOutputTypeMissmatch {
                expected,
                got,
                output_expr: entity.body.loc(),
            })?;
        }
        Ok(())
    }

    #[trace_typechecker]
    pub fn visit_expression(&mut self, expression: &Loc<Expression>) -> Result<()> {
        let new_type = self.new_generic();
        self.add_equation(TypedExpression::Id(expression.inner.id), new_type);
        // Recurse down the expression
        match &expression.inner.kind {
            ExprKind::Identifier(ident) => {
                // Add an equation for the anonymous id
                self.unify_expression_generic_error(
                    &expression,
                    &TypedExpression::Name(ident.clone()),
                )?;
            }
            ExprKind::IntLiteral(_) => {
                let t = self.new_generic_int();
                self.unify_types(&t, &expression.inner)
                    .map_err(|(_, got)| Error::IntLiteralIncompatible {
                        got,
                        loc: expression.loc(),
                    })?;
            }
            ExprKind::BoolLiteral(_) => {
                self.unify_expression_generic_error(&expression, &t_bool())?;
            }
            ExprKind::FnCall(_name, _params) => {
                // TODO: Propper error handling
                todo!("Type check function calls")
            }
            ExprKind::TupleLiteral(inner) => {
                let mut inner_types = vec![];
                for expr in inner {
                    self.visit_expression(expr)?;
                    // NOTE: safe unwrap, we know this expr has a type because we just visited
                    let t = self.type_of(&TypedExpression::Id(expr.id)).unwrap();

                    inner_types.push(t);
                }

                self.unify_expression_generic_error(&expression, &TypeVar::Tuple(inner_types))?;
            }
            ExprKind::TupleIndex(tup, index) => {
                self.visit_expression(tup)?;
                let t = self.type_of(&TypedExpression::Id(tup.id));

                match t {
                    Ok(TypeVar::Tuple(inner)) => {
                        if (index.inner as usize) < inner.len() {
                            self.unify_expression_generic_error(
                                &expression,
                                &inner[index.inner as usize],
                            )?
                        } else {
                            return Err(Error::TupleIndexOutOfBounds {
                                index: index.clone(),
                                actual_size: inner.len() as u128,
                            });
                        }
                    }
                    Ok(t @ TypeVar::Known(_, _, _)) => {
                        return Err(Error::TupleIndexOfNonTuple {
                            got: t.clone(),
                            loc: tup.loc(),
                        })
                    }
                    Ok(TypeVar::Generic(_)) => {
                        return Err(Error::TupleIndexOfGeneric { loc: tup.loc() })
                    }
                    Err(e) => return Err(e),
                }
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

                self.unify_types(&cond.inner, &t_bool())
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
            ExprKind::BinaryOperator(lhs, op, rhs) => {
                self.visit_expression(&lhs)?;
                self.visit_expression(&rhs)?;
                match *op {
                    BinaryOperator::Add
                    | BinaryOperator::Sub
                    | BinaryOperator::LeftShift
                    | BinaryOperator::RightShift => {
                        let int_type = self.new_generic_int();
                        // TODO: Make generic over types that can be added
                        self.unify_expression_generic_error(&lhs, &int_type)?;
                        self.unify_expression_generic_error(&lhs, &rhs.inner)?;
                        self.unify_expression_generic_error(expression, &rhs.inner)?
                    }
                    BinaryOperator::Eq | BinaryOperator::Gt | BinaryOperator::Lt => {
                        let int_type = self.new_generic_int();
                        // TODO: Make generic over types that can be added
                        self.unify_expression_generic_error(&lhs, &int_type)?;
                        self.unify_expression_generic_error(&lhs, &rhs.inner)?;
                        self.unify_expression_generic_error(expression, &t_bool())?
                    }
                    BinaryOperator::LogicalAnd | BinaryOperator::LogicalOr => {
                        // TODO: Make generic over types that can be ored
                        self.unify_expression_generic_error(&lhs, &t_bool())?;
                        self.unify_expression_generic_error(&lhs, &rhs.inner)?;

                        self.unify_expression_generic_error(expression, &t_bool())?
                    }
                    other => panic!("unrecognised intrinsic {:?}", other),
                }
            }
        }
        Ok(())
    }

    #[trace_typechecker]
    pub fn visit_block(&mut self, block: &Block) -> Result<()> {
        for statement in &block.statements {
            self.visit_statement(statement)?
        }
        self.visit_expression(&block.result)
    }

    #[trace_typechecker]
    pub fn visit_statement(&mut self, stmt: &Loc<Statement>) -> Result<()> {
        match &stmt.inner {
            Statement::Binding(name, t, value) => {
                self.visit_expression(value)?;

                if t.is_some() {
                    todo!("Let bindings with fixed types are unsupported")
                }

                let new_type = self.new_generic();
                self.add_equation(TypedExpression::Name(name.clone().inner), new_type);

                self.unify_expression_generic_error(
                    &value,
                    &TypedExpression::Name(name.clone().inner),
                )?;

                Ok(())
            }
            Statement::Register(reg) => self.visit_register(reg),
        }
    }

    #[trace_typechecker]
    pub fn visit_register(&mut self, reg: &Register) -> Result<()> {
        let new_type = self.new_generic();
        self.add_equation(TypedExpression::Name(reg.name.clone().inner), new_type);

        if let Some(t) = &reg.value_type {
            self.unify_types(
                &TypedExpression::Name(reg.name.inner.clone()),
                &Self::type_var_from_hir(&t),
            )
            .map_err(|(got, expected)| Error::UnspecifiedTypeError {
                expected,
                got,
                loc: reg.name.loc(),
            })?;
        }

        self.visit_expression(&reg.clock)?;
        self.visit_expression(&reg.value)?;

        if let Some((rst_cond, rst_value)) = &reg.reset {
            self.visit_expression(&rst_cond)?;
            self.visit_expression(&rst_value)?;
            // Ensure cond is a boolean
            self.unify_types(&rst_cond.inner, &t_bool())
                .map_err(|(got, expected)| Error::NonBoolReset {
                    expected,
                    got,
                    loc: rst_cond.loc(),
                })?;

            // Ensure the reset value has the same type as the register itself
            self.unify_types(&rst_value.inner, &reg.value.inner)
                .map_err(|(got, expected)| Error::RegisterResetMissmatch {
                    expected,
                    got,
                    loc: rst_cond.loc(),
                })?;
        }

        self.unify_types(&reg.clock, &t_clock())
            .map_err(|(got, expected)| Error::NonClockClock {
                expected,
                got,
                loc: reg.clock.loc(),
            })?;

        self.unify_expression_generic_error(
            &reg.value,
            &TypedExpression::Name(reg.name.clone().inner),
        )?;

        Ok(())
    }
}

// Private helper functions
impl<'a> TypeState {
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
            (TypeVar::Known(t1, p1, _), TypeVar::Known(t2, p2, _)) => {
                if p1.len() != p2.len() {
                    return Err((
                        UnificationTrace::new(v1.clone()),
                        UnificationTrace::new(v2.clone()),
                    ));
                }

                for (t1, t2) in p1.iter().zip(p2.iter()) {
                    self.unify_types(t1, t2)
                        .add_context(v1.clone(), v2.clone())?
                }

                if t1 == t2 {
                    Ok((v1, None))
                } else {
                    Err((
                        UnificationTrace::new(v1.clone()),
                        UnificationTrace::new(v2.clone()),
                    ))
                }
            }
            (TypeVar::Tuple(i1), TypeVar::Tuple(i2)) => {
                if i1.len() != i2.len() {
                    return Err((
                        UnificationTrace::new(v1.clone()),
                        UnificationTrace::new(v2.clone()),
                    ));
                }

                for (t1, t2) in i1.iter().zip(i2.iter()) {
                    self.unify_types(t1, t2)
                        .add_context(v1.clone(), v2.clone())?
                }

                Ok((v1, None))
            }
            (TypeVar::Known(_, _, _), TypeVar::Tuple(_)) => Err((
                UnificationTrace::new(v1.clone()),
                UnificationTrace::new(v2.clone()),
            )),
            (TypeVar::Tuple(_), TypeVar::Known(_, _, _)) => Err((
                UnificationTrace::new(v1.clone()),
                UnificationTrace::new(v2.clone()),
            )),
            (TypeVar::Generic(_), TypeVar::Generic(_)) => Ok((v1, Some(v2))),
            (_other, TypeVar::Generic(_)) => Ok((v1, Some(v2))),
            (TypeVar::Generic(_), _other) => Ok((v2, Some(v1))),
        }?;

        if let Some(replaced_type) = replaced_type {
            for (_, rhs) in &mut self.equations {
                Self::replace_type_var(rhs, &replaced_type, new_type.clone())
            }
        }

        self.trace_stack
            .push(TraceStack::Unified(v1cpy, v2cpy, new_type.clone()));
        Ok(())
    }

    fn replace_type_var(in_var: &mut TypeVar, from: &TypeVar, replacement: TypeVar) {
        // First, do recursive replacement
        match in_var {
            TypeVar::Known(_, params, _) => {
                for param in params {
                    Self::replace_type_var(param, from, replacement.clone())
                }
            }
            TypeVar::Tuple(inner) => {
                for t in inner {
                    Self::replace_type_var(t, from, replacement.clone())
                }
            }
            TypeVar::Generic(_) => {}
        }

        if in_var == from {
            *in_var = replacement;
        }
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
impl TypeState {
    pub fn print_equations(&self) {
        for (lhs, rhs) in &self.equations {
            println!("{}: {}", lhs, rhs);
        }
    }
}

pub trait HasType {
    fn get_type<'a>(&self, state: &TypeState) -> Result<TypeVar>;
}

impl HasType for TypeVar {
    fn get_type<'a>(&self, _: &TypeState) -> Result<TypeVar> {
        Ok(self.clone())
    }
}
impl HasType for Loc<TypeVar> {
    fn get_type<'a>(&self, _: &TypeState) -> Result<TypeVar> {
        Ok(self.inner.clone())
    }
}
impl HasType for TypedExpression {
    fn get_type<'a>(&self, state: &TypeState) -> Result<TypeVar> {
        state.type_of(self)
    }
}
impl HasType for Expression {
    fn get_type<'a>(&self, state: &TypeState) -> Result<TypeVar> {
        state.type_of(&TypedExpression::Id(self.id))
    }
}
impl HasType for Loc<Expression> {
    fn get_type<'a>(&self, state: &TypeState) -> Result<TypeVar> {
        state.type_of(&TypedExpression::Id(self.inner.id))
    }
}
impl HasType for KnownType {
    fn get_type<'a>(&self, _state: &TypeState) -> Result<TypeVar> {
        Ok(TypeVar::Known(self.clone(), vec![], None))
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
                format!("{} {}, {} -> {}", "unified".green(), lhs, rhs, result)
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

    use crate::{
        fixed_types::t_clock,
        hir::{self, Block},
    };
    use spade_common::location_info::WithLocation;
    use spade_testutil::name_id;

    fn sized_int(size: u128) -> TVar {
        TVar::Known(
            t_int(),
            vec![TVar::Known(KnownType::Integer(size), vec![], None)],
            None,
        )
    }

    fn unsized_int(id: u64) -> TVar {
        TVar::Known(t_int(), vec![TVar::Generic(id)], None)
    }

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
            let _t1 = $t1.get_type(&$state);
            let _t2 = $t2.get_type(&$state);
            if _t1 != _t2 {
                println!("{}", format_trace_stack(&$state.trace_stack));
                $state.print_equations();

                if let (Ok(t1), Ok(t2)) = (&_t1, &_t2) {
                    println!("Types were OK and have values {}, {}", t1, t2);
                    println!("Raw: {:?}, {:?}", t1, t2);
                } else {
                    println!("{:?}\n!=\n{:?}", _t1, _t2);
                }
                panic!("Types are not the same")
            }
        };
    }

    #[test]
    fn int_literals_have_type_known_int() {
        let mut state = TypeState::new();

        let input = ExprKind::IntLiteral(0).with_id(0).nowhere();

        state.visit_expression(&input).expect("Type error");

        assert_eq!(state.type_of(&TExpr::Id(0)), Ok(unsized_int(1)));
    }

    #[test]
    fn if_statements_have_correctly_infered_types() {
        let mut state = TypeState::new();

        let input = ExprKind::If(
            Box::new(Expression::ident(0, 0, "a").nowhere()),
            Box::new(Expression::ident(1, 1, "b").nowhere()),
            Box::new(Expression::ident(2, 2, "c").nowhere()),
        )
        .with_id(3)
        .nowhere();

        // Add eqs for the literals
        let expr_a = TExpr::Name(name_id(0, "a").inner);
        let expr_b = TExpr::Name(name_id(1, "b").inner);
        let expr_c = TExpr::Name(name_id(2, "c").inner);
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
        ensure_same_type!(state, t0, TVar::Known(t_bool(), vec![], None));
        ensure_same_type!(state, t1, t2);
        ensure_same_type!(state, t1, t3);

        // Check the constraints added to the literals
        ensure_same_type!(state, t0, ta);
        ensure_same_type!(state, t1, tb);
        ensure_same_type!(state, t2, tc);
    }

    #[test]
    fn if_statements_get_correct_type_when_branches_are_of_known_type() {
        let mut state = TypeState::new();

        let input = ExprKind::If(
            Box::new(Expression::ident(0, 0, "a").nowhere()),
            Box::new(Expression::ident(1, 1, "b").nowhere()),
            Box::new(Expression::ident(2, 2, "c").nowhere()),
        )
        .with_id(3)
        .nowhere();

        // Add eqs for the literals
        let expr_a = TExpr::Name(name_id(0, "a").inner);
        let expr_b = TExpr::Name(name_id(1, "b").inner);
        let expr_c = TExpr::Name(name_id(2, "c").inner);
        state.add_equation(expr_a.clone(), TVar::Generic(100));
        state.add_equation(expr_b.clone(), unsized_int(101));
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
        ensure_same_type!(state, t0, TVar::Known(t_bool(), vec![], None));
        ensure_same_type!(state, t1, unsized_int(101));
        ensure_same_type!(state, t2, unsized_int(101));
        ensure_same_type!(state, t3, unsized_int(101));

        // Check the constraints added to the literals
        ensure_same_type!(state, t0, ta);
        ensure_same_type!(state, t1, tb);
        ensure_same_type!(state, t2, tc);
    }

    #[test]
    fn type_inference_fails_if_if_branches_have_incompatible_types() {
        let mut state = TypeState::new();

        let input = ExprKind::If(
            Box::new(Expression::ident(0, 0, "a").nowhere()),
            Box::new(Expression::ident(1, 1, "b").nowhere()),
            Box::new(Expression::ident(2, 2, "c").nowhere()),
        )
        .with_id(3)
        .nowhere();

        // Add eqs for the literals
        let expr_a = TExpr::Name(name_id(0, "a").inner);
        let expr_b = TExpr::Name(name_id(1, "b").inner);
        let expr_c = TExpr::Name(name_id(2, "c").inner);
        state.add_equation(expr_a.clone(), TVar::Generic(100));
        state.add_equation(expr_b.clone(), unsized_int(101));
        state.add_equation(expr_c.clone(), TVar::Known(t_clock(), vec![], None));

        assert_ne!(state.visit_expression(&input), Ok(()));
    }

    #[ignore]
    #[test]
    fn type_inference_for_entities_works() {
        todo!("Figure out how we handle built in types and name_ids");
        // let input = Entity {
        //     head: EntityHead {
        //         inputs: vec![(
        //             name_id(0, "input"),
        //             hir::Type::Generic(
        //                 Path::from_strs(&["int"]).nowhere(),
        //                 vec![hir::TypeExpression::Integer(5).nowhere()],
        //             )
        //             .nowhere(),
        //         )],
        //         output_type: hir::Type::Generic(
        //             Path::from_strs(&["int"]).nowhere(),
        //             vec![hir::TypeExpression::Integer(5).nowhere()],
        //         )
        //         .nowhere(),
        //         type_params: vec![],
        //     },
        //     body: ExprKind::Identifier(Path::from_strs(&["input"]).nowhere())
        //         .with_id(0)
        //         .nowhere(),
        // };

        // let mut state = TypeState::new();

        // state.visit_entity(&input).unwrap();

        // let t0 = get_type!(state, &TExpr::Id(0));
        // ensure_same_type!(
        //     state,
        //     t0,
        //     TypeVar::Known(
        //         t_int(),
        //         vec![TypeVar::Known(KnownType::Integer(5), vec![], None)],
        //         None
        //     )
        // );
    }

    #[ignore]
    #[test]
    fn entity_return_types_must_match() {
        todo!("Figure out how we handle built in types and name_ids");
        // let input = Entity {
        //     head: EntityHead {
        //         inputs: vec![(
        //             Identifier::Named("input".to_string()).nowhere(),
        //             hir::Type::Generic(
        //                 Path::from_strs(&["int"]).nowhere(),
        //                 vec![hir::TypeExpression::Integer(5).nowhere()],
        //             )
        //             .nowhere(),
        //         )],
        //         output_type: hir::Type::Concrete(Path::from_strs(&["bool"])).nowhere(),
        //         type_params: vec![],
        //     },
        //     body: ExprKind::Identifier(Path::from_strs(&["input"]).nowhere())
        //         .with_id(0)
        //         .nowhere(),
        // };

        // let mut state = TypeState::new();

        // assert_matches!(
        //     state.visit_entity(&input),
        //     Err(Error::EntityOutputTypeMissmatch { .. })
        // );
    }

    #[test]
    fn block_visiting_without_definitions_works() {
        let input = ExprKind::Block(Box::new(Block {
            statements: vec![],
            result: ExprKind::IntLiteral(5).with_id(0).nowhere(),
        }))
        .with_id(1)
        .nowhere();

        let mut state = TypeState::new();

        state.visit_expression(&input).unwrap();

        ensure_same_type!(state, TExpr::Id(0), unsized_int(2));
        ensure_same_type!(state, TExpr::Id(1), unsized_int(2));
    }

    #[test]
    fn integer_literals_are_compatible_with_fixed_size_ints() {
        let mut state = TypeState::new();

        let input = ExprKind::If(
            Box::new(Expression::ident(0, 0, "a").nowhere()),
            Box::new(Expression::ident(1, 1, "b").nowhere()),
            Box::new(Expression::ident(2, 2, "c").nowhere()),
        )
        .with_id(3)
        .nowhere();

        // Add eqs for the literals
        let expr_a = TExpr::Name(name_id(0, "a").inner);
        let expr_b = TExpr::Name(name_id(1, "b").inner);
        let expr_c = TExpr::Name(name_id(2, "c").inner);
        state.add_equation(expr_a.clone(), TVar::Generic(100));
        state.add_equation(expr_b.clone(), unsized_int(101));
        state.add_equation(expr_c.clone(), sized_int(5));

        state.visit_expression(&input).unwrap();

        let t0 = get_type!(state, &TExpr::Id(0));
        let t1 = get_type!(state, &TExpr::Id(1));
        let t2 = get_type!(state, &TExpr::Id(2));
        let t3 = get_type!(state, &TExpr::Id(3));

        let ta = get_type!(state, &expr_a);
        let tb = get_type!(state, &expr_b);
        let tc = get_type!(state, &expr_c);

        // Check the generic type variables
        ensure_same_type!(state, t0, TVar::Known(t_bool(), vec![], None));
        ensure_same_type!(state, t1, sized_int(5));
        ensure_same_type!(state, t2, sized_int(5));
        ensure_same_type!(state, t3, sized_int(5));

        // Check the constraints added to the literals
        ensure_same_type!(state, t0, ta);
        ensure_same_type!(state, t1, tb);
        ensure_same_type!(state, t2, tc);
    }

    #[test]
    fn registers_typecheck_correctly() {
        let input = hir::Register {
            name: name_id(0, "a"),
            clock: ExprKind::Identifier(name_id(1, "clk").inner)
                .with_id(3)
                .nowhere(),
            reset: None,
            value: ExprKind::IntLiteral(0).with_id(0).nowhere(),
            value_type: None,
        };

        let mut state = TypeState::new();

        let expr_clk = TExpr::Name(name_id(1, "clk").inner);
        state.add_equation(expr_clk.clone(), TVar::Generic(100));

        state.visit_register(&input).unwrap();

        let t0 = get_type!(state, &TExpr::Id(0));
        let ta = get_type!(state, &TExpr::Name(name_id(0, "a").inner));
        let tclk = get_type!(state, &TExpr::Name(name_id(1, "clk").inner));
        ensure_same_type!(state, t0, unsized_int(3));
        ensure_same_type!(state, ta, unsized_int(3));
        ensure_same_type!(state, tclk, t_clock());
    }

    #[test]
    fn self_referential_registers_typepcheck_correctly() {
        let input = hir::Register {
            name: name_id(0, "a"),
            clock: ExprKind::Identifier(name_id(1, "clk").inner)
                .with_id(3)
                .nowhere(),
            reset: None,
            value: ExprKind::Identifier(name_id(0, "a").inner)
                .with_id(0)
                .nowhere(),
            value_type: None,
        };

        let mut state = TypeState::new();

        let expr_clk = TExpr::Name(name_id(1, "clk").inner);
        state.add_equation(expr_clk.clone(), TVar::Generic(100));

        state.visit_register(&input).unwrap();

        let ta = get_type!(state, &TExpr::Name(name_id(0, "a").inner));
        let tclk = get_type!(state, &TExpr::Name(name_id(1, "clk").inner));
        ensure_same_type!(state, ta, TVar::Generic(2));
        ensure_same_type!(state, tclk, t_clock());
    }

    #[test]
    fn registers_with_resets_typecheck_correctly() {
        let rst_cond = name_id(2, "rst").inner;
        let rst_value = name_id(3, "rst_value").inner;
        let input = hir::Register {
            name: name_id(0, "a"),
            clock: ExprKind::Identifier(name_id(1, "clk").inner)
                .with_id(3)
                .nowhere(),
            reset: Some((
                ExprKind::Identifier(rst_cond.clone()).with_id(1).nowhere(),
                ExprKind::Identifier(rst_value.clone()).with_id(2).nowhere(),
            )),
            value: ExprKind::IntLiteral(0).with_id(0).nowhere(),
            value_type: None,
        };

        let mut state = TypeState::new();

        let expr_clk = TExpr::Name(name_id(1, "clk").inner);
        let expr_rst_cond = TExpr::Name(name_id(2, "rst").inner);
        let expr_rst_value = TExpr::Name(name_id(3, "rst_value").inner);
        state.add_equation(expr_clk.clone(), TVar::Generic(100));
        state.add_equation(expr_rst_cond.clone(), TVar::Generic(101));
        state.add_equation(expr_rst_value.clone(), TVar::Generic(102));

        state.visit_register(&input).unwrap();

        let t0 = get_type!(state, &TExpr::Id(0));
        let ta = get_type!(state, &TExpr::Name(name_id(0, "a").inner));
        let tclk = get_type!(state, &TExpr::Name(name_id(1, "clk").inner));
        let trst_cond = get_type!(state, &TExpr::Name(rst_cond.clone()));
        let trst_val = get_type!(state, &TExpr::Name(rst_value.clone()));
        ensure_same_type!(state, t0, unsized_int(3));
        ensure_same_type!(state, ta, unsized_int(3));
        ensure_same_type!(state, tclk, t_clock());
        ensure_same_type!(state, trst_cond, t_bool());
        ensure_same_type!(state, trst_val, unsized_int(3));
    }

    #[test]
    fn untyped_let_bindings_typecheck_correctly() {
        let input = hir::Statement::Binding(
            name_id(0, "a"),
            None,
            ExprKind::IntLiteral(0).with_id(0).nowhere(),
        )
        .nowhere();

        let mut state = TypeState::new();

        state.visit_statement(&input).unwrap();

        let ta = get_type!(state, &TExpr::Name(name_id(0, "a").inner));
        ensure_same_type!(state, ta, unsized_int(1));
    }

    #[test]
    fn tuple_type_specs_propagate_correctly() {
        let input = Register {
            name: name_id(0, "test"),
            clock: ExprKind::Identifier(name_id(1, "clk").inner)
                .with_id(0)
                .nowhere(),
            reset: None,
            value: ExprKind::TupleLiteral(vec![
                ExprKind::IntLiteral(5).with_id(1).nowhere(),
                ExprKind::BoolLiteral(true).with_id(2).nowhere(),
            ])
            .with_id(3)
            .nowhere(),
            value_type: Some(
                hir::TypeSpec::Tuple(vec![
                    hir::TypeSpec::Concrete(
                        BaseType::Int.nowhere(),
                        vec![hir::TypeExpression::Integer(5).nowhere()],
                    )
                    .nowhere(),
                    hir::TypeSpec::Concrete(BaseType::Bool.nowhere(), vec![]).nowhere(),
                ])
                .nowhere(),
            ),
        };

        let mut state = TypeState::new();

        let expr_clk = TExpr::Name(name_id(1, "clk").inner);
        state.add_equation(expr_clk.clone(), TVar::Generic(100));

        state.visit_register(&input).unwrap();

        let ttup = get_type!(state, &TExpr::Id(3));
        let reg = get_type!(state, &TExpr::Name(name_id(0, "test").inner));
        let expected = TypeVar::Tuple(vec![sized_int(5), TypeVar::Known(t_bool(), vec![], None)]);
        ensure_same_type!(state, ttup, expected);
        ensure_same_type!(state, reg, expected);
    }
}