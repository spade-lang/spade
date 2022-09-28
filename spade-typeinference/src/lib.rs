// This algorithm is based off the excellent lecture here
// https://www.youtube.com/watch?v=xJXcZp2vgLs
//
// The basic idea is to go through every node in the HIR tree, for every typed thing,
// add an equation indicating a constraint on that thing. This can only be done once
// and should be done by the visitor for that node. The visitor should then unify
// types according to the rules of the node.

use constraints::{ConstraintExpr, ConstraintRhs, ConstraintSource, TypeConstraints};
use hir::param_util::{match_args_with_params, Argument};
use hir::symbol_table::{Patternable, PatternableKind, TypeSymbol};
use hir::{ArgumentList, FunctionLike, Pattern, PatternArgument, TypeParam};
use hir::{ExecutableItem, ItemList};
use parse_tree_macros::trace_typechecker;
use requirements::{Replacement, Requirement};
use spade_common::location_info::{Loc, WithLocation};
use spade_common::name::{Identifier, NameID, Path};
use spade_hir as hir;
use spade_hir::symbol_table::SymbolTable;
use spade_hir::{Block, Entity, ExprKind, Expression, Register, Statement};
use spade_types::KnownType;
use std::collections::HashMap;
use std::sync::Arc;
use trace_stack::TraceStack;
use tracing::{info, trace};

mod constraints;
pub mod dump;
pub mod equation;
pub mod error_reporting;
pub mod expression;
pub mod fixed_types;
pub mod mir_type_lowering;
pub mod pipeline;
mod requirements;
pub mod result;
pub mod testutil;
pub mod trace_stack;

use crate::constraints::ce_var;
use crate::fixed_types::t_clock;
use crate::fixed_types::{t_bool, t_int};
use crate::trace_stack::{format_trace_stack, TraceStackEntry};

use equation::{TypeEquations, TypeVar, TypedExpression};
use result::{Error, Result};

use self::result::{UnificationError, UnificationErrorExt, UnificationTrace};

// NOTE(allow) This is a debug macro which is not normally used but can come in handy
#[allow(unused_macros)]
macro_rules! add_trace {
    ($self:expr, $($arg : tt) *) => {
        $self.trace_stack.push(TraceStack::Message(format!($($arg)*)))
    }
}

pub struct ProcessedEntity {
    pub entity: Entity,
    pub type_state: TypeState,
}

pub struct ProcessedPipeline {
    pub pipeline: hir::Pipeline,
    pub type_state: TypeState,
}

pub enum ProcessedItem {
    EnumInstance,
    StructInstance,
    Entity(ProcessedEntity),
    Pipeline(ProcessedPipeline),
    BuiltinEntity(Loc<hir::EntityHead>),
    BuiltinPipeline(Loc<hir::PipelineHead>),
}

pub struct ProcessedItemList {
    pub executables: Vec<ProcessedItem>,
}

impl ProcessedItemList {
    pub fn typecheck(
        items: &ItemList,
        symbol_table: &SymbolTable,
        print_trace: bool,
    ) -> Result<Self> {
        Ok(Self {
            executables: items
                .executables
                .clone()
                .into_iter()
                .map(|(_name, item)| {
                    let mut type_state = TypeState::new();

                    // To avoid borrowing type_state too early, we'll do a macro to build
                    // closures. Kind of ugly, but it gets the job done
                    macro_rules! err_processor {
                        () => {
                            |e| {
                                if print_trace {
                                    println!("{}", format_trace_stack(&type_state.trace_stack))
                                }
                                e
                            }
                        };
                    }

                    match item {
                        ExecutableItem::EnumInstance { .. } => Ok(ProcessedItem::EnumInstance),
                        ExecutableItem::StructInstance { .. } => Ok(ProcessedItem::StructInstance),
                        ExecutableItem::Entity(entity) => {
                            type_state
                                .visit_entity(&entity, symbol_table)
                                .map_err(err_processor!())?;
                            Ok(ProcessedItem::Entity(ProcessedEntity {
                                entity: entity.inner,
                                type_state,
                            }))
                        }
                        ExecutableItem::Pipeline(pipeline) => {
                            type_state
                                .visit_pipeline(&pipeline, symbol_table)
                                .map_err(err_processor!())?;
                            Ok(ProcessedItem::Pipeline(ProcessedPipeline {
                                pipeline: pipeline.inner,
                                type_state,
                            }))
                        }
                        ExecutableItem::BuiltinEntity(_, head) => {
                            Ok(ProcessedItem::BuiltinEntity(head))
                        }
                        ExecutableItem::BuiltinPipeline(_, head) => {
                            Ok(ProcessedItem::BuiltinPipeline(head))
                        }
                    }
                })
                .collect::<Result<Vec<_>>>()?,
        })
    }
}

#[derive(Debug)]
pub enum GenericListSource<'a> {
    /// For when you just need a new generic list but have no need to refer back
    /// to it in the future
    Anonymous,
    /// For managing the generics of callable with the specified name when type checking
    /// their body
    Definition(&'a NameID),
    /// For expressions which instantiate generic items
    Expression(u64),
}

/// Stored version of GenericListSource
#[derive(Clone, Hash, Eq, PartialEq, Debug)]
pub enum GenericListToken {
    Anonymous(usize),
    Definition(NameID),
    Expression(u64),
}

/// State of the type inference algorithm
#[derive(Clone)]
pub struct TypeState {
    equations: TypeEquations,
    next_typeid: u64,
    // List of the mapping between generic parameters and type vars.
    // The key is the index of the expression for which this generic list is associated. (if this
    // is a generic list for a call whose expression id is x to f<A, B>, then generic_lists[x] will
    // be {A: <type var>, b: <type var>}
    // Managed here because unification must update *all* TypeVars in existence.
    generic_lists: HashMap<GenericListToken, HashMap<NameID, TypeVar>>,

    constraints: TypeConstraints,

    /// Requirements which must be fulfilled but which do not guide further type inference.
    /// For example, if seeing `let y = x.a` before knowing the type of `x`, a requirement is
    /// added to say "x has field a, and y should be the type of that field"
    requirements: Vec<Requirement>,

    replacements: HashMap<TypeVar, TypeVar>,

    pub trace_stack: Arc<TraceStack>,
}

impl TypeState {
    pub fn new() -> Self {
        Self {
            equations: HashMap::new(),
            next_typeid: 0,
            trace_stack: Arc::new(TraceStack::new()),
            constraints: TypeConstraints::new(),
            requirements: vec![],
            replacements: HashMap::new(),
            generic_lists: HashMap::new(),
        }
    }

    pub fn get_equations(&self) -> &TypeEquations {
        &self.equations
    }

    // Get a generic list with a safe unwrap since a token is acquired
    pub fn get_generic_list<'a>(
        &'a self,
        generic_list_token: &'a GenericListToken,
    ) -> &'a HashMap<NameID, TypeVar> {
        &self.generic_lists[&generic_list_token]
    }

    #[tracing::instrument(level = "trace", skip_all)]
    fn hir_type_expr_to_var<'a>(
        &'a self,
        e: &Loc<hir::TypeExpression>,
        generic_list_token: &GenericListToken,
    ) -> TypeVar {
        match &e.inner {
            hir::TypeExpression::Integer(i) => TypeVar::Known(KnownType::Integer(*i), vec![]),
            hir::TypeExpression::TypeSpec(spec) => {
                self.type_var_from_hir(&spec.clone().at_loc(&e.loc()), generic_list_token)
            }
        }
    }

    #[tracing::instrument(level = "trace", skip_all, fields(%hir_type))]
    pub fn type_var_from_hir<'a>(
        &'a self,
        hir_type: &crate::hir::TypeSpec,
        generic_list_token: &GenericListToken,
    ) -> TypeVar {
        let generic_list = self.get_generic_list(generic_list_token);
        match &hir_type {
            hir::TypeSpec::Declared(base, params) => {
                let params = params
                    .into_iter()
                    .map(|e| self.hir_type_expr_to_var(&e, generic_list_token))
                    .collect();

                TypeVar::Known(KnownType::Type(base.inner.clone()), params)
            }
            hir::TypeSpec::Generic(name) => match generic_list.get(&name.inner) {
                Some(t) => t.clone(),
                None => {
                    for (list_source, _) in &self.generic_lists {
                        info!("Generic lists exist for {list_source:?}");
                    }
                    info!("Current source is {generic_list_token:?}");
                    panic!("No entry in generic list for {name}");
                }
            },
            hir::TypeSpec::Tuple(inner) => {
                let inner = inner
                    .iter()
                    .map(|t| self.type_var_from_hir(t, generic_list_token))
                    .collect();
                TypeVar::Tuple(inner)
            }
            hir::TypeSpec::Array { inner, size } => {
                let inner = self.type_var_from_hir(&inner, generic_list_token);
                let size = self.hir_type_expr_to_var(&size, generic_list_token);

                TypeVar::Array {
                    inner: Box::new(inner),
                    size: Box::new(size),
                }
            }
            hir::TypeSpec::Unit(_) => {
                todo!("Support unit type in type inference")
            }
            hir::TypeSpec::Backward(inner) => {
                TypeVar::Backward(Box::new(self.type_var_from_hir(inner, generic_list_token)))
            }
            hir::TypeSpec::Wire(inner) => {
                TypeVar::Wire(Box::new(self.type_var_from_hir(inner, generic_list_token)))
            }
        }
    }

    /// Returns the type of the expression with the specified id. Error if no equation
    /// for the specified epxression exists
    pub fn type_of<'a>(&'a self, expr: &TypedExpression) -> Result<TypeVar> {
        for (e, t) in &self.equations {
            if e == expr {
                return Ok(t.clone());
            }
        }
        Err(Error::UnknownType(expr.clone()).into())
    }

    pub fn new_generic_int(&mut self, symtab: &SymbolTable) -> TypeVar {
        TypeVar::Known(t_int(symtab), vec![self.new_generic()])
    }

    /// Return a new generic int. The first returned value is int<N>, and the second
    /// value is N
    pub fn new_split_generic_int(&mut self, symtab: &SymbolTable) -> (TypeVar, TypeVar) {
        let size = self.new_generic();
        let full = TypeVar::Known(t_int(symtab), vec![size.clone()]);
        (full, size)
    }

    pub fn new_generic(&mut self) -> TypeVar {
        let id = self.new_typeid();
        TypeVar::Unknown(id)
    }

    #[trace_typechecker]
    #[tracing::instrument(level = "trace", skip_all, fields(%entity.name))]
    pub fn visit_entity(&mut self, entity: &Entity, symtab: &SymbolTable) -> Result<()> {
        let generic_list = self.create_generic_list(
            GenericListSource::Definition(&entity.name.name_id().inner),
            &entity.head.type_params,
        );

        // Add equations for the inputs
        for (name, t) in &entity.inputs {
            let tvar = self.type_var_from_hir(t, &generic_list);
            self.add_equation(TypedExpression::Name(name.inner.clone()), tvar)
        }

        self.visit_expression(&entity.body, symtab, &generic_list)?;

        // Ensure that the output type matches what the user specified, and unit otherwise
        if let Some(output_type) = &entity.head.output_type {
            let tvar = self.type_var_from_hir(&output_type, &generic_list);
            self.unify(&TypedExpression::Id(entity.body.inner.id), &tvar, symtab)
                .map_normal_err(|(got, expected)| Error::EntityOutputTypeMismatch {
                    expected,
                    got,
                    type_spec: output_type.loc(),
                    output_expr: entity.body.loc(),
                })?;
        } else {
            todo!("Support unit types")
            // self.unify_types(
            //     &TypedExpression::Id(entity.body.inner.id),
            //     &TypeVar::Known(KnownType::Type(BaseType::Unit), vec![], None),
            // )
            // .map_err(|(got, expected)| Error::UnspecedEntityOutputTypeMismatch {
            //     expected,
            //     got,
            //     output_expr: entity.body.loc(),
            // })?;
        }

        self.check_requirements(symtab)?;

        Ok(())
    }

    #[trace_typechecker]
    fn visit_argument_list(
        &mut self,
        args: &[Argument],
        symtab: &SymbolTable,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        for (
            i,
            Argument {
                target,
                target_type,
                value,
                kind,
            },
        ) in args.into_iter().enumerate()
        {
            self.visit_expression(&value, symtab, generic_list)?;
            let target_type = self.type_var_from_hir(&target_type, generic_list);

            self.unify(&target_type, &value.inner, symtab)
                .map_normal_err(|(expected, got)| match kind {
                    hir::param_util::ArgumentKind::Positional => {
                        Error::PositionalArgumentMismatch {
                            index: i,
                            expr: value.loc(),
                            expected,
                            got,
                        }
                    }
                    hir::param_util::ArgumentKind::Named => Error::NamedArgumentMismatch {
                        name: (*target).clone(),
                        expr: value.loc(),
                        expected,
                        got,
                    },
                    hir::param_util::ArgumentKind::ShortNamed => {
                        Error::ShortNamedArgumentMismatch {
                            name: (*target).clone(),
                            expected,
                            got,
                        }
                    }
                })?;
        }

        Ok(())
    }

    #[tracing::instrument(level = "trace", skip_all)]
    #[trace_typechecker]
    pub fn visit_expression(
        &mut self,
        expression: &Loc<Expression>,
        symtab: &SymbolTable,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        let new_type = self.new_generic();
        self.add_equation(TypedExpression::Id(expression.inner.id), new_type);

        // Recurse down the expression
        match &expression.inner.kind {
            ExprKind::Identifier(_) => self.visit_identifier(expression, symtab)?,
            ExprKind::IntLiteral(_) => self.visit_int_literal(expression, symtab)?,
            ExprKind::BoolLiteral(_) => self.visit_bool_literal(expression, symtab)?,
            ExprKind::TupleLiteral(_) => {
                self.visit_tuple_literal(expression, symtab, generic_list)?
            }
            ExprKind::TupleIndex(_, _) => {
                self.visit_tuple_index(expression, symtab, generic_list)?
            }
            ExprKind::ArrayLiteral(_) => {
                self.visit_array_literal(expression, symtab, generic_list)?
            }
            ExprKind::FieldAccess(_, _) => {
                self.visit_field_access(expression, symtab, generic_list)?
            }
            ExprKind::Index(_, _) => self.visit_index(expression, symtab, generic_list)?,
            ExprKind::Block(_) => self.visit_block_expr(expression, symtab, generic_list)?,
            ExprKind::If(_, _, _) => self.visit_if(expression, symtab, generic_list)?,
            ExprKind::Match(_, _) => self.visit_match(expression, symtab, generic_list)?,
            ExprKind::BinaryOperator(_, _, _) => {
                self.visit_binary_operator(expression, symtab, generic_list)?
            }
            ExprKind::UnaryOperator(_, _) => {
                self.visit_unary_operator(expression, symtab, generic_list)?
            }
            ExprKind::EntityInstance(name, args) => {
                let head = symtab.entity_by_id(&name.inner);
                self.handle_function_like(expression, &name.inner, &head.inner, args, symtab)?;
            }
            ExprKind::PipelineInstance {
                depth: _,
                name,
                args,
            } => {
                let head = symtab.pipeline_by_id(&name.inner);
                self.handle_function_like(expression, &name.inner, &head.inner, args, symtab)?;
            }
            ExprKind::FnCall(name, args) => {
                let head = symtab.function_by_id(&name.inner);
                self.handle_function_like(expression, &name.inner, &head.inner, args, symtab)?;
            }
            ExprKind::PipelineRef { .. } => {
                self.visit_pipeline_ref(expression, symtab)?;
            }
        }
        Ok(())
    }

    // Common handler for entities, functions and pipelines
    #[tracing::instrument(level = "trace", skip_all, fields(%name))]
    #[trace_typechecker]
    fn handle_function_like(
        &mut self,
        expression: &Loc<Expression>,
        name: &NameID,
        head: &impl FunctionLike,
        args: &Loc<ArgumentList>,
        symtab: &SymbolTable,
    ) -> Result<()> {
        // Add new symbols for all the type parameters
        let generic_list = self.create_generic_list(
            GenericListSource::Expression(expression.id),
            head.type_params(),
        );

        let type_params = head.type_params();

        // Special handling of built in functions
        macro_rules! handle_special_functions {
            ($([$($path:expr),*] => $handler:expr),*) => {
                $(
                    let path = Path(vec![$(Identifier($path.to_string()).nowhere()),*]).nowhere();
                    if symtab
                        .try_lookup_final_id(&path)
                        .map(|n| &n == name)
                        .unwrap_or(false)
                    {
                        $handler
                    };
                )*
            }
        }

        // NOTE: These would be better as a closure, but unfortunately that does not satisfy
        // the borrow checker
        macro_rules! generic_arg {
            ($idx:expr) => {
                self.get_generic_list(&generic_list)[&type_params[$idx].name_id()].clone()
            };
        }

        let args = match_args_with_params(args, head.inputs())?;

        handle_special_functions! {
            ["std", "conv", "concat"] => {

                let lhs_size = generic_arg!(0);
                let rhs_size = generic_arg!(1);
                let result_size = generic_arg!(2);

                // Result size is sum of input sizes
                self.add_constraint(
                    result_size.clone(),
                    ce_var(&lhs_size) + ce_var(&rhs_size),
                    expression.loc(),
                    &result_size,
                    ConstraintSource::Concatenation
                );
                self.add_constraint(
                    lhs_size.clone(),
                    ce_var(&result_size) + -ce_var(&rhs_size),
                    args[0].value.loc(),
                    &lhs_size,
                    ConstraintSource::Concatenation
                );
                self.add_constraint(rhs_size.clone(),
                    ce_var(&result_size) + -ce_var(&lhs_size),
                    args[1].value.loc(),
                    &rhs_size,
                    ConstraintSource::Concatenation
                );
            }
        };

        let return_type = self.type_var_from_hir(
            head.output_type()
                .as_ref()
                .expect("Unit return type from entity is unsupported"),
            &generic_list,
        );

        // Unify the types of the arguments
        self.visit_argument_list(&args, symtab, &generic_list)?;

        self.unify_expression_generic_error(expression, &return_type, symtab)?;

        Ok(())
    }

    #[tracing::instrument(level = "trace", skip(self))]
    pub fn create_generic_list(
        &mut self,
        source: GenericListSource,
        params: &[Loc<TypeParam>],
    ) -> GenericListToken {
        let new_list = params
            .iter()
            .map(|param| {
                let name = match &param.inner {
                    hir::TypeParam::TypeName(_, name) => name.clone(),
                    hir::TypeParam::Integer(_, name) => name.clone(),
                };

                let t = self.new_generic();
                (name, t)
            })
            .map(|(name, t)| (name, t.clone()))
            .collect();

        self.add_mapped_generic_list(source, new_list)
    }

    /// Adds a generic list with parameters already mapped to types
    pub fn add_mapped_generic_list(
        &mut self,
        source: GenericListSource,
        mapping: HashMap<NameID, TypeVar>,
    ) -> GenericListToken {
        let reference = match source {
            GenericListSource::Anonymous => GenericListToken::Anonymous(self.generic_lists.len()),
            GenericListSource::Definition(name) => GenericListToken::Definition(name.clone()),
            GenericListSource::Expression(id) => GenericListToken::Expression(id),
        };

        if let Some(_) = self.generic_lists.insert(reference.clone(), mapping) {
            panic!("A generic list already existed for {reference:?}");
        }
        reference
    }

    #[tracing::instrument(level = "trace", skip_all)]
    #[trace_typechecker]
    pub fn visit_block(
        &mut self,
        block: &Block,
        symtab: &SymbolTable,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        for statement in &block.statements {
            self.visit_statement(statement, symtab, generic_list)?;
        }
        self.visit_expression(&block.result, symtab, generic_list)?;
        Ok(())
    }

    #[trace_typechecker]
    pub fn visit_pattern(
        &mut self,
        pattern: &Loc<Pattern>,
        symtab: &SymbolTable,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        let new_type = self.new_generic();
        self.add_equation(TypedExpression::Id(pattern.inner.id), new_type);
        match &pattern.inner.kind {
            hir::PatternKind::Integer(_) => {
                let int_t = &self.new_generic_int(&symtab);
                self.unify(pattern, int_t, symtab)
                    .expect("Failed to unify new_generic with int");
            }
            hir::PatternKind::Bool(_) => {
                self.unify(pattern, &t_bool(symtab), symtab)
                    .expect("Expected new_generic with boolean");
            }
            hir::PatternKind::Name { name, pre_declared } => {
                if !pre_declared {
                    self.add_equation(
                        TypedExpression::Name(name.clone().inner),
                        pattern.get_type(self)?,
                    );
                }
                self.unify(
                    &TypedExpression::Id(pattern.id),
                    &TypedExpression::Name(name.clone().inner),
                    symtab,
                )
                .map_normal_err(|(lhs, rhs)| Error::UnspecifiedTypeError {
                    expected: lhs,
                    got: rhs,
                    loc: name.loc(),
                })?;
            }
            hir::PatternKind::Tuple(subpatterns) => {
                for pattern in subpatterns {
                    self.visit_pattern(pattern, symtab, generic_list)?;
                }
                let tuple_type = TypeVar::Tuple(
                    subpatterns
                        .iter()
                        .map(|pattern| {
                            let p_type = pattern.get_type(self)?;
                            Ok(p_type)
                        })
                        .collect::<Result<_>>()?,
                );

                self.unify(pattern, &tuple_type, symtab)
                    .expect("Unification of new_generic with tuple type can not fail");
            }
            hir::PatternKind::Type(name, args) => {
                let (condition_type, params, generic_list) =
                    match symtab.patternable_type_by_id(name).inner {
                        Patternable {
                            kind: PatternableKind::Enum,
                            params: _,
                        } => {
                            let enum_variant = symtab.enum_variant_by_id(name).inner;
                            let generic_list = self.create_generic_list(
                                GenericListSource::Anonymous,
                                &enum_variant.type_params,
                            );

                            let condition_type =
                                self.type_var_from_hir(&enum_variant.output_type, &generic_list);

                            (condition_type, enum_variant.params, generic_list)
                        }
                        Patternable {
                            kind: PatternableKind::Struct,
                            params: _,
                        } => {
                            let s = symtab.struct_by_id(name).inner;
                            let generic_list = self
                                .create_generic_list(GenericListSource::Anonymous, &s.type_params);

                            let condition_type =
                                self.type_var_from_hir(&s.self_type, &generic_list);

                            (condition_type, s.params, generic_list)
                        }
                    };

                self.unify(pattern, &condition_type, symtab)
                    .expect("Unification of new_generic with enum can not fail");

                for (
                    i,
                    (
                        PatternArgument {
                            target,
                            value: pattern,
                            kind,
                        },
                        (_, target_type),
                    ),
                ) in args.iter().zip(params.0.iter()).enumerate()
                {
                    self.visit_pattern(pattern, symtab, &generic_list)?;
                    let target_type = self.type_var_from_hir(&target_type, &generic_list);

                    self.unify(&target_type, pattern, symtab).map_normal_err(
                        |(expected, got)| match kind {
                            hir::ArgumentKind::Positional => Error::PositionalArgumentMismatch {
                                index: i,
                                expr: pattern.loc(),
                                expected,
                                got,
                            },
                            hir::ArgumentKind::Named => Error::NamedArgumentMismatch {
                                name: target.clone(),
                                expr: pattern.loc(),
                                expected,
                                got,
                            },
                            hir::ArgumentKind::ShortNamed => Error::ShortNamedArgumentMismatch {
                                name: target.clone(),
                                expected,
                                got,
                            },
                        },
                    )?;
                }
            }
        }
        Ok(())
    }

    #[trace_typechecker]
    pub fn visit_statement(
        &mut self,
        stmt: &Loc<Statement>,
        symtab: &SymbolTable,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        match &stmt.inner {
            Statement::Binding(pattern, t, value) => {
                trace!("Visiting `let {} = ..`", pattern.kind);
                self.visit_expression(value, symtab, generic_list)?;

                self.visit_pattern(pattern, symtab, generic_list)?;

                self.unify(&TypedExpression::Id(pattern.id), value, symtab)
                    .map_normal_err(|(got, expected)| Error::PatternTypeMismatch {
                        pattern: pattern.loc(),
                        expected,
                        reason: t.as_ref().map(|t| t.loc()).unwrap_or_else(|| value.loc()),
                        got,
                    })?;

                if let Some(t) = t {
                    let tvar = self.type_var_from_hir(&t, &generic_list);
                    self.unify(&TypedExpression::Id(pattern.id), &tvar, symtab)
                        .map_normal_err(|(got, expected)| Error::UnspecifiedTypeError {
                            expected,
                            got,
                            loc: value.loc(),
                        })?;
                }

                Ok(())
            }
            Statement::Register(reg) => self.visit_register(reg, symtab, generic_list),
            Statement::Declaration(names) => {
                for name in names {
                    let new_type = self.new_generic();
                    self.add_equation(TypedExpression::Name(name.clone().inner), new_type);
                }
                Ok(())
            }
            // These statements have no effect on the types
            Statement::PipelineRegMarker | Statement::Label(_) => Ok(()),
            Statement::Assert(expr) => {
                self.visit_expression(expr, symtab, generic_list)?;
                self.unify_expression_generic_error(expr, &t_bool(symtab), symtab)?;
                Ok(())
            }
            Statement::Set { target, value } => {
                self.visit_expression(target, symtab, generic_list)?;
                self.visit_expression(value, symtab, generic_list)?;

                let inner_type = self.new_generic();
                let outer_type = TypeVar::Backward(Box::new(inner_type.clone()));
                self.unify_expression_generic_error(target, &outer_type, symtab)?;
                self.unify_expression_generic_error(value, &inner_type, symtab)?;

                Ok(())
            }
        }
    }

    #[trace_typechecker]
    pub fn visit_register(
        &mut self,
        reg: &Register,
        symtab: &SymbolTable,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        self.visit_pattern(&reg.pattern, symtab, generic_list)?;

        self.visit_expression(&reg.clock, symtab, generic_list)?;
        self.visit_expression(&reg.value, symtab, generic_list)?;

        if let Some((rst_cond, rst_value)) = &reg.reset {
            self.visit_expression(&rst_cond, symtab, generic_list)?;
            self.visit_expression(&rst_value, symtab, generic_list)?;
            // Ensure cond is a boolean
            self.unify(&rst_cond.inner, &t_bool(symtab), symtab)
                .map_normal_err(|(got, expected)| Error::NonBoolReset {
                    expected,
                    got,
                    loc: rst_cond.loc(),
                })?;

            // Ensure the reset value has the same type as the register itself
            self.unify(&rst_value.inner, &reg.value.inner, symtab)
                .map_normal_err(|(got, expected)| Error::RegisterResetMismatch {
                    expected,
                    got,
                    loc: rst_cond.loc(),
                })?;
        }

        self.unify(&reg.clock, &t_clock(symtab), symtab)
            .map_normal_err(|(got, expected)| Error::NonClockClock {
                expected,
                got,
                loc: reg.clock.loc(),
            })?;

        if let Some(t) = &reg.value_type {
            let tvar = self.type_var_from_hir(&t, &generic_list);
            self.unify(&reg.value, &tvar, symtab)
                .map_normal_err(|(got, expected)| Error::UnspecifiedTypeError {
                    expected,
                    got,
                    loc: reg.value.loc(),
                })?;
        }

        self.unify(&TypedExpression::Id(reg.pattern.id), &reg.value, symtab)
            .map_normal_err(|(got, expected)| Error::PatternTypeMismatch {
                pattern: reg.pattern.loc(),
                reason: reg
                    .value_type
                    .as_ref()
                    .map(|t| t.loc())
                    .unwrap_or_else(|| reg.value.loc()),
                expected,
                got,
            })?;

        Ok(())
    }
}

// Private helper functions
impl TypeState {
    fn new_typeid(&mut self) -> u64 {
        let result = self.next_typeid;
        self.next_typeid += 1;
        result
    }

    fn check_var_for_replacement(&self, var: TypeVar) -> TypeVar {
        if let Some(new) = self.replacements.get(&var) {
            return new.clone();
        };
        match var {
            TypeVar::Known(base, params) => TypeVar::Known(
                base,
                params
                    .into_iter()
                    .map(|p| self.check_var_for_replacement(p))
                    .collect(),
            ),
            TypeVar::Tuple(inner) => TypeVar::Tuple(
                inner
                    .into_iter()
                    .map(|p| self.check_var_for_replacement(p))
                    .collect(),
            ),
            TypeVar::Array { inner, size } => TypeVar::Array {
                inner: Box::new(self.check_var_for_replacement(*inner)),
                size: Box::new(self.check_var_for_replacement(*size)),
            },
            TypeVar::Backward(inner) => {
                TypeVar::Backward(Box::new(self.check_var_for_replacement(*inner)))
            }
            TypeVar::Wire(inner) => TypeVar::Wire(Box::new(self.check_var_for_replacement(*inner))),
            u @ TypeVar::Unknown(_) => u,
        }
    }

    fn check_expr_for_replacement(&self, val: ConstraintExpr) -> ConstraintExpr {
        match val {
            v @ ConstraintExpr::Integer(_) => v,
            ConstraintExpr::Var(var) => ConstraintExpr::Var(self.check_var_for_replacement(var)),
            ConstraintExpr::Sum(lhs, rhs) => ConstraintExpr::Sum(
                Box::new(self.check_expr_for_replacement(*lhs)),
                Box::new(self.check_expr_for_replacement(*rhs)),
            ),
            ConstraintExpr::Sub(inner) => {
                ConstraintExpr::Sub(Box::new(self.check_expr_for_replacement(*inner)))
            }
            ConstraintExpr::BitsToRepresent(inner) => {
                ConstraintExpr::BitsToRepresent(Box::new(self.check_expr_for_replacement(*inner)))
            }
        }
    }

    pub fn add_equation(&mut self, expression: TypedExpression, var: TypeVar) {
        let var = self.check_var_for_replacement(var);

        self.trace_stack.push(TraceStackEntry::AddingEquation(
            expression.clone(),
            var.clone(),
        ));
        if let Some(prev) = self.equations.insert(expression.clone(), var.clone()) {
            let var = var.clone();
            let expr = expression.clone();
            println!("{}", format_trace_stack(&self.trace_stack));
            panic!("Adding equation for {} == {} but a previous eq exists.\n\tIt was previously bound to {}", expr, var, prev)
        }
    }

    fn add_constraint(
        &mut self,
        lhs: TypeVar,
        rhs: ConstraintExpr,
        loc: Loc<()>,
        inside: &TypeVar,
        source: ConstraintSource,
    ) {
        let replaces = lhs.clone();
        let lhs = self.check_var_for_replacement(lhs);
        let rhs = self
            .check_expr_for_replacement(rhs)
            .with_context(&replaces, &inside.clone(), source)
            .at_loc(&loc);

        self.constraints.add_constraint(lhs, rhs);
    }

    fn add_requirement(&mut self, requirement: Requirement) {
        let replaced = match requirement {
            Requirement::HasField {
                target_type,
                field,
                expr,
            } => Requirement::HasField {
                field,
                target_type: self
                    .check_var_for_replacement(target_type.inner.clone())
                    .at_loc(&target_type),
                expr: self
                    .check_var_for_replacement(expr.inner.clone())
                    .at_loc(&expr),
            },
        };

        self.requirements.push(replaced)
    }

    #[cfg(test)]
    fn add_eq_from_tvar(&mut self, expression: TypedExpression, var: TypeVar) {
        self.add_equation(expression, var)
    }

    /// Performs unification but does not update constraints. This is done to avoid
    /// updating constraints more often than necessary. Technically, constraints can
    /// be updated even less often, but `unify` is a pretty natural point to do so.

    fn unify_inner(
        &mut self,
        e1: &impl HasType,
        e2: &impl HasType,
        symtab: &SymbolTable,
    ) -> std::result::Result<TypeVar, UnificationError> {
        let v1 = e1
            .get_type(self)
            .expect("Tried to unify types but the lhs was not found");
        let v2 = e2
            .get_type(self)
            .expect("Tried to unify types but the rhs was not found");

        trace!("Unifying {v1} with {v2}");

        let v1 = self.check_var_for_replacement(v1);
        let v2 = self.check_var_for_replacement(v2);

        self.trace_stack
            .push(TraceStackEntry::TryingUnify(v1.clone(), v2.clone()));

        // Copy the original types so we can properly trace the progress of the
        // unification
        let v1cpy = v1.clone();
        let v2cpy = v2.clone();

        macro_rules! err_producer {
            () => {
                UnificationError::Normal((
                    UnificationTrace::new(self.check_var_for_replacement(v1)),
                    UnificationTrace::new(self.check_var_for_replacement(v2)),
                ))
            };
        }

        macro_rules! unify_if {
            ($condition:expr, $new_type:expr, $replaced_type:expr) => {
                if $condition {
                    Ok(($new_type, $replaced_type))
                } else {
                    Err(err_producer!())
                }
            };
        }

        macro_rules! try_with_context {
            ($value: expr) => {
                match $value {
                    Ok(result) => result,
                    e => {
                        return e.add_context(v1.clone(), v2.clone());
                    }
                }
            };
        }

        // Figure out the most general type, and take note if we need to
        // do any replacement of the types in the rest of the state
        let result = match (&v1, &v2) {
            (TypeVar::Known(t1, p1), TypeVar::Known(t2, p2)) => match (t1, t2) {
                (KnownType::Integer(val1), KnownType::Integer(val2)) => {
                    unify_if!(val1 == val2, v1, None)
                }
                (KnownType::Type(n1), KnownType::Type(n2)) => {
                    match (
                        &symtab.type_symbol_by_id(&n1).inner,
                        &symtab.type_symbol_by_id(&n2).inner,
                    ) {
                        (TypeSymbol::Declared(_, _), TypeSymbol::Declared(_, _)) => {
                            if n1 != n2 {
                                return Err(err_producer!());
                            }
                            if p1.len() != p2.len() {
                                return Err(err_producer!());
                            }

                            for (t1, t2) in p1.iter().zip(p2.iter()) {
                                try_with_context!(self.unify_inner(t1, t2, symtab));
                            }

                            let new_ts1 = symtab.type_symbol_by_id(&n1).inner;
                            let new_ts2 = symtab.type_symbol_by_id(&n2).inner;
                            let new_v1 = e1
                                .get_type(self)
                                .expect("Tried to unify types but the lhs was not found");
                            unify_if!(new_ts1 == new_ts2, new_v1, None)
                        }
                        (TypeSymbol::Declared(_, _), TypeSymbol::GenericArg) => Ok((v1, Some(v2))),
                        (TypeSymbol::GenericArg, TypeSymbol::Declared(_, _)) => Ok((v2, Some(v1))),
                        (TypeSymbol::GenericArg, TypeSymbol::GenericArg) => Ok((v1, Some(v2))),
                        (TypeSymbol::Declared(_, _), TypeSymbol::GenericInt) => todo!(),
                        (TypeSymbol::GenericArg, TypeSymbol::GenericInt) => todo!(),
                        (TypeSymbol::GenericInt, TypeSymbol::Declared(_, _)) => todo!(),
                        (TypeSymbol::GenericInt, TypeSymbol::GenericArg) => todo!(),
                        (TypeSymbol::GenericInt, TypeSymbol::GenericInt) => todo!(),
                    }
                }
                (KnownType::Integer(_), KnownType::Type(_)) => Err(err_producer!()),
                (KnownType::Type(_), KnownType::Integer(_)) => Err(err_producer!()),
            },
            (TypeVar::Tuple(i1), TypeVar::Tuple(i2)) => {
                if i1.len() != i2.len() {
                    return Err(err_producer!());
                }

                for (t1, t2) in i1.iter().zip(i2.iter()) {
                    try_with_context!(self.unify_inner(t1, t2, symtab));
                }

                Ok((self.check_var_for_replacement(v1), None))
            }
            (
                TypeVar::Array {
                    inner: i1,
                    size: s1,
                },
                TypeVar::Array {
                    inner: i2,
                    size: s2,
                },
            ) => {
                let inner = try_with_context!(self.unify_inner(i1.as_ref(), i2.as_ref(), symtab));
                let size = try_with_context!(self.unify_inner(s1.as_ref(), s2.as_ref(), symtab));

                Ok((
                    TypeVar::Array {
                        inner: Box::new(inner),
                        size: Box::new(size),
                    },
                    None,
                ))
            }
            (TypeVar::Backward(i1), TypeVar::Backward(i2)) => {
                let new_inner =
                    try_with_context!(self.unify_inner(i1.as_ref(), i2.as_ref(), symtab));

                Ok((TypeVar::Backward(Box::new(new_inner)), None))
            }
            (TypeVar::Wire(i1), TypeVar::Wire(i2)) => {
                let new_inner =
                    try_with_context!(self.unify_inner(i1.as_ref(), i2.as_ref(), symtab));

                Ok((TypeVar::Wire(Box::new(new_inner)), None))
            }
            // Unknown with other
            (TypeVar::Unknown(_), TypeVar::Unknown(_)) => Ok((v1, Some(v2))),
            (_other, TypeVar::Unknown(_)) => Ok((v1, Some(v2))),
            (TypeVar::Unknown(_), _other) => Ok((v2, Some(v1))),
            // Incompatibilities
            (TypeVar::Known(_, _), _other) => Err(err_producer!()),
            (_other, TypeVar::Known(_, _)) => Err(err_producer!()),
            (TypeVar::Tuple(_), _other) => Err(err_producer!()),
            (_other, TypeVar::Tuple(_)) => Err(err_producer!()),
            (TypeVar::Backward(_), _other) => Err(err_producer!()),
            (_other, TypeVar::Backward(_)) => Err(err_producer!()),
            (TypeVar::Wire(_), _other) => Err(err_producer!()),
            (_other, TypeVar::Wire(_)) => Err(err_producer!()),
        };

        let (new_type, replaced_type) = result?;

        self.trace_stack
            .push(TraceStackEntry::Unified(v1cpy, v2cpy, new_type.clone()));

        if let Some(replaced_type) = replaced_type {
            self.replacements
                .insert(replaced_type.clone(), new_type.clone());

            for (_, rhs) in &mut self.equations {
                TypeState::replace_type_var(rhs, &replaced_type, &new_type)
            }
            for generic_list in &mut self.generic_lists.values_mut() {
                for (_, lhs) in generic_list.iter_mut() {
                    TypeState::replace_type_var(lhs, &replaced_type, &new_type)
                }
            }
            for requirement in &mut self.requirements {
                requirement.replace_type_var(&replaced_type, &new_type)
            }

            self.constraints.inner = self
                .constraints
                .inner
                .clone()
                .into_iter()
                .map(|(mut lhs, mut rhs)| {
                    TypeState::replace_type_var(&mut lhs, &replaced_type, &new_type);
                    TypeState::replace_type_var_in_constraint_rhs(
                        &mut rhs,
                        &replaced_type,
                        &new_type,
                    );

                    (lhs, rhs)
                })
                .collect()
        }

        Ok(new_type)
    }

    #[tracing::instrument(level = "trace", skip_all)]
    pub fn unify(
        &mut self,
        e1: &impl HasType,
        e2: &impl HasType,
        symtab: &SymbolTable,
    ) -> std::result::Result<TypeVar, UnificationError> {
        let new_type = self.unify_inner(e1, e2, symtab)?;

        // With replacement done, some of our constraints may have been updated to provide
        // more type inference information. Try to do unification of those new constraints too
        loop {
            trace!("Updating constraints");
            let new_info = self.constraints.update_constraints();

            if new_info.is_empty() {
                break;
            }

            for constraint in new_info {
                let ((var, replacement), loc) = constraint.split_loc();

                self.trace_stack
                    .push(TraceStackEntry::InferringFromConstraints(
                        var.clone(),
                        replacement.val,
                    ));

                let var = self.check_var_for_replacement(var);

                if replacement.val < 0 {
                    // lifeguard spade#126
                    panic!("Inferred a negative integer from constraints");
                }

                let expected_type = &KnownType::Integer(replacement.val as u128);
                match self.unify_inner(&var, expected_type, symtab) {
                    Ok(_) => {}
                    Err(UnificationError::Normal((mut lhs, mut rhs))) => {
                        let mut source_lhs = replacement.context.inside.clone();
                        Self::replace_type_var(
                            &mut source_lhs,
                            &replacement.context.replaces,
                            &lhs.outer(),
                        );
                        let mut source_rhs = replacement.context.inside.clone();
                        Self::replace_type_var(
                            &mut source_rhs,
                            &replacement.context.replaces,
                            &rhs.outer(),
                        );
                        lhs.inside.replace(source_lhs);
                        rhs.inside.replace(source_rhs);
                        return Err(UnificationError::FromConstraints {
                            got: rhs,
                            expected: lhs,
                            source: replacement.context.source,
                            loc,
                        });
                    }
                    Err(e @ UnificationError::FromConstraints { .. }) => return Err(e),
                };
            }
        }

        Ok(new_type)
    }

    fn replace_type_var(in_var: &mut TypeVar, from: &TypeVar, replacement: &TypeVar) {
        // First, do recursive replacement
        match in_var {
            TypeVar::Known(_, params) => {
                for param in params {
                    Self::replace_type_var(param, from, replacement)
                }
            }
            TypeVar::Tuple(inner) => {
                for t in inner {
                    Self::replace_type_var(t, from, replacement)
                }
            }
            TypeVar::Array { inner, size } => {
                Self::replace_type_var(inner, from, replacement);
                Self::replace_type_var(size, from, replacement);
            }
            TypeVar::Unknown(_) => {}
            TypeVar::Backward(inner) => Self::replace_type_var(inner, from, replacement),
            TypeVar::Wire(inner) => Self::replace_type_var(inner, from, replacement),
        }

        if in_var == from {
            *in_var = replacement.clone();
        }
    }

    fn replace_type_var_in_constraint_expr(
        in_constraint: &mut ConstraintExpr,
        from: &TypeVar,
        replacement: &TypeVar,
    ) {
        match in_constraint {
            ConstraintExpr::Integer(_) => {}
            ConstraintExpr::Var(v) => {
                Self::replace_type_var(v, from, replacement);

                match v {
                    TypeVar::Known(KnownType::Integer(val), _) => {
                        *in_constraint = ConstraintExpr::Integer(*val as i128)
                    }
                    _ => {}
                }
            }
            ConstraintExpr::Sum(lhs, rhs) => {
                Self::replace_type_var_in_constraint_expr(lhs, from, replacement);
                Self::replace_type_var_in_constraint_expr(rhs, from, replacement);
            }
            ConstraintExpr::Sub(i) | ConstraintExpr::BitsToRepresent(i) => {
                Self::replace_type_var_in_constraint_expr(i, from, replacement);
            }
        }
    }

    fn replace_type_var_in_constraint_rhs(
        in_constraint: &mut ConstraintRhs,
        from: &TypeVar,
        replacement: &TypeVar,
    ) {
        Self::replace_type_var_in_constraint_expr(&mut in_constraint.constraint, from, replacement);
        // NOTE: We do not want to replace type variables here as that that removes
        // information about where the constraint relates. Instead, this replacement
        // is preformed when reporting ther error
        // Self::replace_type_var(&mut in_constraint.from, from, replacement);
    }

    pub fn unify_expression_generic_error<'a>(
        &mut self,
        expr: &Loc<Expression>,
        other: &impl HasType,
        symtab: &SymbolTable,
    ) -> Result<TypeVar> {
        self.unify(&expr.inner, other, symtab)
            .map_normal_err(|(got, expected)| Error::UnspecifiedTypeError {
                got,
                expected,
                loc: expr.loc(),
            })
    }

    fn check_requirements(&mut self, symtab: &SymbolTable) -> Result<()> {
        // Once we are done type checking the rest of the entity, check all requirements
        loop {
            // Walk through all the requirements, checking each one. If the requirement
            // is still undetermined, take note to retain that id, otherwise store the
            // replacement to be performed
            let (retain, replacements): (Vec<_>, Vec<_>) = self
                .requirements
                .clone()
                .iter()
                .map(|req| match req.check(self, symtab)? {
                    requirements::RequirementResult::NoChange => Ok((true, None)),
                    requirements::RequirementResult::Satisfied(replacement) => {
                        Ok((false, Some(replacement)))
                    }
                })
                .collect::<Result<Vec<_>>>()?
                .into_iter()
                .unzip();

            if replacements.is_empty() {
                break;
            }

            for Replacement { from, to } in replacements.into_iter().filter_map(|x| x).flatten() {
                self.unify(&from, &to, symtab)
                    .map_normal_err(|(got, expected)| Error::UnspecifiedTypeError {
                        got,
                        expected,
                        loc: from.loc(),
                    })?;
            }

            // Drop all replacements that have now been applied
            self.requirements = self
                .requirements
                .drain(0..)
                .zip(retain.into_iter())
                .filter_map(|(req, keep)| if keep { Some(req) } else { None })
                .collect();
        }

        Ok(())
    }
}

impl TypeState {
    pub fn print_equations(&self) {
        for (lhs, rhs) in &self.equations {
            println!("{}: {}", lhs, rhs);
        }
    }
}

pub trait HasType: std::fmt::Debug {
    fn get_type(&self, state: &TypeState) -> Result<TypeVar>;
}

impl HasType for TypeVar {
    fn get_type(&self, state: &TypeState) -> Result<TypeVar> {
        Ok(state.check_var_for_replacement(self.clone()))
    }
}
impl HasType for Loc<TypeVar> {
    fn get_type(&self, state: &TypeState) -> Result<TypeVar> {
        self.inner.get_type(state)
    }
}
impl HasType for TypedExpression {
    fn get_type(&self, state: &TypeState) -> Result<TypeVar> {
        state.type_of(self)
    }
}
impl HasType for Expression {
    fn get_type(&self, state: &TypeState) -> Result<TypeVar> {
        state.type_of(&TypedExpression::Id(self.id))
    }
}
impl HasType for Loc<Expression> {
    fn get_type(&self, state: &TypeState) -> Result<TypeVar> {
        state.type_of(&TypedExpression::Id(self.inner.id))
    }
}
impl HasType for Pattern {
    fn get_type(&self, state: &TypeState) -> Result<TypeVar> {
        state.type_of(&TypedExpression::Id(self.id))
    }
}
impl HasType for Loc<Pattern> {
    fn get_type(&self, state: &TypeState) -> Result<TypeVar> {
        state.type_of(&TypedExpression::Id(self.inner.id))
    }
}
impl HasType for KnownType {
    fn get_type(&self, _state: &TypeState) -> Result<TypeVar> {
        Ok(TypeVar::Known(self.clone(), vec![]))
    }
}
impl HasType for NameID {
    fn get_type(&self, state: &TypeState) -> Result<TypeVar> {
        state.type_of(&TypedExpression::Name(self.clone()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use super::TypeVar as TVar;
    use super::TypedExpression as TExpr;

    use crate::testutil::{sized_int, unsized_int};
    use crate::{ensure_same_type, get_type};
    use crate::{
        fixed_types::t_clock,
        hir::{self, Block},
    };
    use hir::symbol_table::TypeDeclKind;
    use hir::PatternKind;
    use hir::{dtype, testutil::t_num, ArgumentList};
    use spade_ast::testutil::{ast_ident, ast_path};
    use spade_common::location_info::WithLocation;
    use spade_common::name::testutil::name_id;
    use spade_hir::symbol_table::{SymbolTable, Thing};

    #[test]
    fn int_literals_have_type_known_int() {
        let mut state = TypeState::new();
        let mut symtab = SymbolTable::new();
        let generic_list = state.create_generic_list(GenericListSource::Anonymous, &vec![]);
        spade_ast_lowering::builtins::populate_symtab(&mut symtab, &mut ItemList::new());

        let input = ExprKind::IntLiteral(0).with_id(0).nowhere();

        state
            .visit_expression(&input, &symtab, &generic_list)
            .expect("Type error");

        ensure_same_type!(state, TExpr::Id(0), unsized_int(1, &symtab));
    }

    #[test]
    fn if_statements_have_correctly_inferred_types() {
        let mut state = TypeState::new();
        let mut symtab = SymbolTable::new();
        spade_ast_lowering::builtins::populate_symtab(&mut symtab, &mut ItemList::new());

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
        state.add_eq_from_tvar(expr_a.clone(), TVar::Unknown(100));
        state.add_eq_from_tvar(expr_b.clone(), TVar::Unknown(101));
        state.add_eq_from_tvar(expr_c.clone(), TVar::Unknown(102));

        let generic_list = state.create_generic_list(GenericListSource::Anonymous, &vec![]);
        state
            .visit_expression(&input, &symtab, &generic_list)
            .unwrap();

        // Check the generic type variables
        ensure_same_type!(state, TExpr::Id(0), TVar::Known(t_bool(&symtab), vec![]));
        ensure_same_type!(state, TExpr::Id(1), TExpr::Id(2));
        ensure_same_type!(state, TExpr::Id(1), TExpr::Id(3));

        // Check the constraints added to the literals
        ensure_same_type!(state, TExpr::Id(0), expr_a);
        ensure_same_type!(state, TExpr::Id(1), expr_b);
        ensure_same_type!(state, TExpr::Id(2), expr_c);
    }

    #[test]
    fn if_expressions_get_correct_type_when_branches_are_of_known_type() {
        let mut state = TypeState::new();
        let mut symtab = SymbolTable::new();
        spade_ast_lowering::builtins::populate_symtab(&mut symtab, &mut ItemList::new());

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
        state.add_eq_from_tvar(expr_a.clone(), TVar::Unknown(100));
        state.add_eq_from_tvar(expr_b.clone(), unsized_int(101, &symtab));
        state.add_eq_from_tvar(expr_c.clone(), TVar::Unknown(102));

        let generic_list = state.create_generic_list(GenericListSource::Anonymous, &vec![]);
        state
            .visit_expression(&input, &symtab, &generic_list)
            .unwrap();

        // Check the generic type variables
        ensure_same_type!(state, TExpr::Id(0), TVar::Known(t_bool(&symtab), vec![]));
        ensure_same_type!(state, TExpr::Id(1), unsized_int(101, &symtab));
        ensure_same_type!(state, TExpr::Id(2), unsized_int(101, &symtab));
        ensure_same_type!(state, TExpr::Id(3), unsized_int(101, &symtab));

        // Check the constraints added to the literals
        ensure_same_type!(state, TExpr::Id(0), expr_a);
        ensure_same_type!(state, TExpr::Id(1), expr_b);
        ensure_same_type!(state, TExpr::Id(2), expr_c);
    }

    #[test]
    fn type_inference_fails_if_if_branches_have_incompatible_types() {
        let mut state = TypeState::new();
        let mut symtab = SymbolTable::new();
        spade_ast_lowering::builtins::populate_symtab(&mut symtab, &mut ItemList::new());

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
        state.add_eq_from_tvar(expr_a.clone(), TVar::Unknown(100));
        state.add_eq_from_tvar(expr_b.clone(), unsized_int(101, &symtab));
        state.add_eq_from_tvar(expr_c.clone(), TVar::Known(t_clock(&symtab), vec![]));

        let generic_list = state.create_generic_list(GenericListSource::Anonymous, &vec![]);
        assert_ne!(
            state.visit_expression(&input, &symtab, &generic_list),
            Ok(())
        );
    }

    #[test]
    fn match_expressions_have_correctly_inferred_types() {
        let mut state = TypeState::new();
        let mut symtab = SymbolTable::new();
        spade_ast_lowering::builtins::populate_symtab(&mut symtab, &mut ItemList::new());

        let first_pattern = PatternKind::Tuple(vec![
            PatternKind::name(name_id(10, "x1")).with_id(20).nowhere(),
            PatternKind::name(name_id(11, "x2")).with_id(21).nowhere(),
        ])
        .with_id(22)
        .nowhere();

        let input = ExprKind::Match(
            Box::new(Expression::ident(0, 0, "a").nowhere()),
            vec![
                (first_pattern, Expression::ident(1, 1, "b").nowhere()),
                (
                    PatternKind::name(name_id(12, "y")).with_id(23).nowhere(),
                    Expression::ident(2, 2, "c").nowhere(),
                ),
            ],
        )
        .with_id(3)
        .nowhere();

        // Add eqs for the literals
        let expr_a = TExpr::Name(name_id(0, "a").inner);
        let expr_b = TExpr::Name(name_id(1, "b").inner);
        let expr_c = TExpr::Name(name_id(2, "c").inner);
        state.add_eq_from_tvar(expr_a.clone(), TVar::Unknown(100));
        state.add_eq_from_tvar(expr_b.clone(), unsized_int(101, &symtab));
        state.add_eq_from_tvar(expr_c.clone(), TVar::Unknown(102));

        let generic_list = state.create_generic_list(GenericListSource::Anonymous, &vec![]);
        state
            .visit_expression(&input, &symtab, &generic_list)
            .unwrap();

        // Ensure branches have the same type
        ensure_same_type!(state, expr_b, &expr_c);
        // And that the match block has the same type
        ensure_same_type!(state, expr_c, TExpr::Id(3));

        // Ensure patterns have same type as each other, and as the expression
        ensure_same_type!(state, expr_a, TExpr::Id(22));
        ensure_same_type!(state, TExpr::Id(22), TExpr::Id(23));
    }

    #[test]
    fn patterns_constrain_expression_types() {
        let mut state = TypeState::new();
        let mut symtab = SymbolTable::new();
        spade_ast_lowering::builtins::populate_symtab(&mut symtab, &mut ItemList::new());

        let first_pattern = PatternKind::Tuple(vec![
            PatternKind::Bool(true).with_id(20).nowhere(),
            PatternKind::Bool(true).with_id(21).nowhere(),
        ])
        .with_id(22)
        .nowhere();

        let input = ExprKind::Match(
            Box::new(Expression::ident(0, 0, "a").nowhere()),
            vec![
                (first_pattern, Expression::ident(1, 1, "b").nowhere()),
                (
                    PatternKind::name(name_id(11, "y")).with_id(23).nowhere(),
                    Expression::ident(2, 2, "c").nowhere(),
                ),
            ],
        )
        .with_id(3)
        .nowhere();

        // Add eqs for the literals
        let expr_a = TExpr::Name(name_id(0, "a").inner);
        let expr_b = TExpr::Name(name_id(1, "b").inner);
        let expr_c = TExpr::Name(name_id(2, "c").inner);
        state.add_eq_from_tvar(expr_a.clone(), TVar::Unknown(100));
        state.add_eq_from_tvar(expr_b.clone(), TVar::Unknown(101));
        state.add_eq_from_tvar(expr_c.clone(), TVar::Unknown(102));

        let generic_list = state.create_generic_list(GenericListSource::Anonymous, &vec![]);
        state
            .visit_expression(&input, &symtab, &generic_list)
            .unwrap();

        let expected_type = TVar::Tuple(vec![kvar!(t_bool(&symtab)), kvar!(t_bool(&symtab))]);

        // Ensure patterns have same type as each other, and as the expression
        ensure_same_type!(state, expr_a, expected_type);
    }

    #[test]
    fn not_all_types_are_the_same() {
        let mut state = TypeState::new();
        let mut symtab = SymbolTable::new();
        spade_ast_lowering::builtins::populate_symtab(&mut symtab, &mut ItemList::new());

        let not_bool = symtab.add_type_with_id(
            100,
            ast_path("not_bool").inner,
            TypeSymbol::Declared(vec![], TypeDeclKind::Enum).nowhere(),
        );

        let lhs = PatternKind::name(name_id(0, "x")).with_id(22).nowhere();

        state.add_eq_from_tvar(
            TExpr::Name(name_id(1, "a").inner),
            kvar!(KnownType::Type(not_bool)),
        );

        let input = Statement::Binding(
            lhs,
            Some(dtype!(symtab => "bool")),
            Expression::ident(1, 1, "a").nowhere(),
        )
        .nowhere();

        let generic_list = state.create_generic_list(GenericListSource::Anonymous, &vec![]);
        assert!(state
            .visit_statement(&input, &symtab, &generic_list)
            .is_err());
    }

    #[test]
    fn block_visiting_without_definitions_works() {
        let mut symtab = SymbolTable::new();
        spade_ast_lowering::builtins::populate_symtab(&mut symtab, &mut ItemList::new());

        let input = ExprKind::Block(Box::new(Block {
            statements: vec![],
            result: ExprKind::IntLiteral(5).with_id(0).nowhere(),
        }))
        .with_id(1)
        .nowhere();

        let mut state = TypeState::new();

        let generic_list = state.create_generic_list(GenericListSource::Anonymous, &vec![]);
        state
            .visit_expression(&input, &symtab, &generic_list)
            .unwrap();

        ensure_same_type!(state, TExpr::Id(0), unsized_int(2, &symtab));
        ensure_same_type!(state, TExpr::Id(1), unsized_int(2, &symtab));
    }

    #[test]
    fn integer_literals_are_compatible_with_fixed_size_ints() {
        let mut state = TypeState::new();
        let mut symtab = SymbolTable::new();
        spade_ast_lowering::builtins::populate_symtab(&mut symtab, &mut ItemList::new());

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
        state.add_eq_from_tvar(expr_a.clone(), TVar::Unknown(100));
        state.add_eq_from_tvar(expr_b.clone(), unsized_int(101, &symtab));
        state.add_eq_from_tvar(expr_c.clone(), sized_int(5, &symtab));

        let generic_list = state.create_generic_list(GenericListSource::Anonymous, &vec![]);
        state
            .visit_expression(&input, &symtab, &generic_list)
            .unwrap();

        // Check the generic type variables
        ensure_same_type!(state, TExpr::Id(0), TVar::Known(t_bool(&symtab), vec![]));
        ensure_same_type!(state, TExpr::Id(1), sized_int(5, &symtab));
        ensure_same_type!(state, TExpr::Id(2), sized_int(5, &symtab));
        ensure_same_type!(state, TExpr::Id(3), sized_int(5, &symtab));

        // Check the constraints added to the literals
        ensure_same_type!(state, TExpr::Id(0), expr_a);
        ensure_same_type!(state, TExpr::Id(1), expr_b);
        ensure_same_type!(state, TExpr::Id(2), expr_c);
    }

    #[test]
    fn array_indexing_infers_all_types_correctly() {
        let mut state = TypeState::new();
        let mut symtab = SymbolTable::new();
        spade_ast_lowering::builtins::populate_symtab(&mut symtab, &mut ItemList::new());

        let input = ExprKind::Index(
            Box::new(
                ExprKind::Identifier(name_id(0, "a").inner)
                    .with_id(1)
                    .nowhere(),
            ),
            Box::new(
                ExprKind::Identifier(name_id(1, "b").inner)
                    .with_id(2)
                    .nowhere(),
            ),
        )
        .with_id(3)
        .nowhere();

        // Add eqs for the literals
        let expr_a = TExpr::Name(name_id(0, "a").inner);
        let expr_b = TExpr::Name(name_id(1, "b").inner);
        state.add_eq_from_tvar(expr_a.clone(), TVar::Unknown(100));
        state.add_eq_from_tvar(expr_b.clone(), TVar::Unknown(101));

        let generic_list = state.create_generic_list(GenericListSource::Anonymous, &vec![]);
        state
            .visit_expression(&input, &symtab, &generic_list)
            .unwrap();

        // The index should be an integer
        ensure_same_type!(state, expr_b, unsized_int(5, &symtab));
        // The target should be an array

        ensure_same_type!(
            state,
            &expr_a,
            TVar::Array {
                inner: Box::new(TVar::Unknown(0)),
                size: Box::new(TVar::Unknown(4))
            }
        );

        // The result should be the inner type
        ensure_same_type!(state, TExpr::Id(3), TVar::Unknown(0));
    }

    #[test]
    fn registers_typecheck_correctly() {
        let mut symtab = SymbolTable::new();
        spade_ast_lowering::builtins::populate_symtab(&mut symtab, &mut ItemList::new());

        let input = hir::Register {
            pattern: PatternKind::name(name_id(0, "a")).with_id(10).nowhere(),
            clock: ExprKind::Identifier(name_id(1, "clk").inner)
                .with_id(3)
                .nowhere(),
            reset: None,
            value: ExprKind::IntLiteral(0).with_id(0).nowhere(),
            value_type: None,
        };

        let mut state = TypeState::new();

        let expr_clk = TExpr::Name(name_id(1, "clk").inner);
        state.add_eq_from_tvar(expr_clk.clone(), TVar::Unknown(100));

        let generic_list = state.create_generic_list(GenericListSource::Anonymous, &vec![]);
        state
            .visit_register(&input, &symtab, &generic_list)
            .unwrap();

        ensure_same_type!(state, TExpr::Id(0), unsized_int(3, &symtab));
        ensure_same_type!(
            state,
            TExpr::Name(name_id(0, "a").inner),
            unsized_int(3, &symtab)
        );
        ensure_same_type!(state, expr_clk, t_clock(&symtab));
    }

    #[test]
    fn self_referential_registers_typepcheck_correctly() {
        let mut symtab = SymbolTable::new();
        spade_ast_lowering::builtins::populate_symtab(&mut symtab, &mut ItemList::new());

        let input = hir::Register {
            pattern: PatternKind::name(name_id(0, "a")).with_id(10).nowhere(),
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
        state.add_eq_from_tvar(expr_clk.clone(), TVar::Unknown(100));

        let generic_list = state.create_generic_list(GenericListSource::Anonymous, &vec![]);
        state
            .visit_register(&input, &symtab, &generic_list)
            .unwrap();

        ensure_same_type!(state, TExpr::Name(name_id(0, "a").inner), TVar::Unknown(2));
        ensure_same_type!(state, expr_clk, t_clock(&symtab));
    }

    #[test]
    fn registers_with_resets_typecheck_correctly() {
        let mut symtab = SymbolTable::new();
        spade_ast_lowering::builtins::populate_symtab(&mut symtab, &mut ItemList::new());

        let rst_cond = name_id(2, "rst").inner;
        let rst_value = name_id(3, "rst_value").inner;
        let input = hir::Register {
            pattern: PatternKind::name(name_id(0, "a")).with_id(10).nowhere(),
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
        state.add_eq_from_tvar(expr_clk.clone(), TVar::Unknown(100));
        state.add_eq_from_tvar(expr_rst_cond.clone(), TVar::Unknown(101));
        state.add_eq_from_tvar(expr_rst_value.clone(), TVar::Unknown(102));

        let generic_list = state.create_generic_list(GenericListSource::Anonymous, &vec![]);
        state
            .visit_register(&input, &symtab, &generic_list)
            .unwrap();

        let t0 = get_type!(state, &TExpr::Id(0));
        let ta = get_type!(state, &TExpr::Name(name_id(0, "a").inner));
        let tclk = get_type!(state, &TExpr::Name(name_id(1, "clk").inner));
        let trst_cond = get_type!(state, &TExpr::Name(rst_cond.clone()));
        let trst_val = get_type!(state, &TExpr::Name(rst_value.clone()));
        ensure_same_type!(state, t0, unsized_int(3, &symtab));
        ensure_same_type!(state, ta, unsized_int(3, &symtab));
        ensure_same_type!(state, tclk, t_clock(&symtab));
        ensure_same_type!(state, trst_cond, t_bool(&symtab));
        ensure_same_type!(state, trst_val, unsized_int(3, &symtab));
    }

    #[test]
    fn untyped_let_bindings_typecheck_correctly() {
        let mut symtab = SymbolTable::new();
        spade_ast_lowering::builtins::populate_symtab(&mut symtab, &mut ItemList::new());

        let input = hir::Statement::Binding(
            PatternKind::name(name_id(0, "a")).with_id(10).nowhere(),
            None,
            ExprKind::IntLiteral(0).with_id(0).nowhere(),
        )
        .nowhere();

        let mut state = TypeState::new();

        let generic_list = state.create_generic_list(GenericListSource::Anonymous, &vec![]);
        state
            .visit_statement(&input, &symtab, &generic_list)
            .unwrap();

        let ta = get_type!(state, &TExpr::Name(name_id(0, "a").inner));
        ensure_same_type!(state, ta, unsized_int(1, &symtab));
    }

    #[test]
    fn typed_let_bindings_typecheck_correctly() {
        let mut symtab = SymbolTable::new();
        spade_ast_lowering::builtins::populate_symtab(&mut symtab, &mut ItemList::new());

        let input = hir::Statement::Binding(
            PatternKind::name(name_id(0, "a")).with_id(10).nowhere(),
            Some(dtype!(symtab => "int"; (t_num(5)))),
            ExprKind::IntLiteral(0).with_id(0).nowhere(),
        )
        .nowhere();

        let mut state = TypeState::new();

        let generic_list = state.create_generic_list(GenericListSource::Anonymous, &vec![]);
        state
            .visit_statement(&input, &symtab, &generic_list)
            .unwrap();

        let ta = get_type!(state, &TExpr::Name(name_id(0, "a").inner));
        ensure_same_type!(state, ta, sized_int(5, &symtab));
    }

    #[test]
    fn tuple_type_specs_propagate_correctly() {
        let mut symtab = SymbolTable::new();
        spade_ast_lowering::builtins::populate_symtab(&mut symtab, &mut ItemList::new());

        let input = Register {
            pattern: PatternKind::name(name_id(0, "test")).with_id(10).nowhere(),
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
                    dtype!(symtab => "int"; ( t_num(5) )),
                    hir::dtype!(symtab => "bool"),
                ])
                .nowhere(),
            ),
        };

        let mut state = TypeState::new();

        let expr_clk = TExpr::Name(name_id(1, "clk").inner);
        state.add_eq_from_tvar(expr_clk.clone(), TVar::Unknown(100));

        let generic_list = state.create_generic_list(GenericListSource::Anonymous, &vec![]);
        state
            .visit_register(&input, &symtab, &generic_list)
            .unwrap();

        let ttup = get_type!(state, &TExpr::Id(3));
        let reg = get_type!(state, &TExpr::Name(name_id(0, "test").inner));
        let expected = TypeVar::Tuple(vec![
            sized_int(5, &symtab),
            TypeVar::Known(t_bool(&symtab), vec![]),
        ]);
        ensure_same_type!(state, ttup, &expected);
        ensure_same_type!(state, reg, &expected);
    }

    #[test]
    fn entity_type_inference_works() {
        // Add the head to the symtab
        let mut symtab = SymbolTable::new();
        spade_ast_lowering::builtins::populate_symtab(&mut symtab, &mut ItemList::new());

        // Add the entity to the symtab
        let entity = hir::EntityHead {
            inputs: hir::ParameterList(vec![
                (ast_ident("a"), dtype!(symtab => "bool")),
                (ast_ident("b"), dtype!(symtab => "int"; (t_num(10)))),
            ]),
            output_type: Some(dtype!(symtab => "int"; (t_num(5)))),
            type_params: vec![],
        };

        let entity_name = symtab.add_thing(ast_path("test").inner, Thing::Entity(entity.nowhere()));

        let input = ExprKind::EntityInstance(
            entity_name.nowhere(),
            ArgumentList::Positional(vec![
                Expression::ident(0, 0, "x").nowhere(),
                Expression::ident(1, 1, "b").nowhere(),
            ])
            .nowhere(),
        )
        .with_id(2)
        .nowhere();

        let mut state = TypeState::new();

        // Add eqs for the literals
        let expr_a = TExpr::Name(name_id(0, "a").inner);
        let expr_b = TExpr::Name(name_id(1, "b").inner);
        state.add_eq_from_tvar(expr_a.clone(), TVar::Unknown(100));
        state.add_eq_from_tvar(expr_b.clone(), TVar::Unknown(101));

        let generic_list = state.create_generic_list(GenericListSource::Anonymous, &vec![]);
        state
            .visit_expression(&input, &symtab, &generic_list)
            .unwrap();

        let t0 = get_type!(state, &TExpr::Id(0));
        let t1 = get_type!(state, &TExpr::Id(1));
        let t2 = get_type!(state, &TExpr::Id(2));

        let ta = get_type!(state, &expr_a);
        let tb = get_type!(state, &expr_b);

        // Check the generic type variables
        ensure_same_type!(state, t0.clone(), TVar::Known(t_bool(&symtab), vec![]));
        ensure_same_type!(
            state,
            t1.clone(),
            TVar::Known(
                t_int(&symtab),
                vec![TypeVar::Known(KnownType::Integer(10), vec![])],
            )
        );
        ensure_same_type!(
            state,
            t2,
            TVar::Known(
                t_int(&symtab),
                vec![TypeVar::Known(KnownType::Integer(5), vec![])],
            )
        );

        // Check the constraints added to the literals
        ensure_same_type!(state, t0.clone(), ta);
        ensure_same_type!(state, t1.clone(), tb);
    }

    #[test]
    fn pipeline_type_inference_works() {
        // Add the head to the symtab
        let mut symtab = SymbolTable::new();
        spade_ast_lowering::builtins::populate_symtab(&mut symtab, &mut ItemList::new());

        // Add the entity to the symtab
        let entity = hir::PipelineHead {
            depth: 2.nowhere(),
            inputs: hir::ParameterList(vec![
                (ast_ident("a"), dtype!(symtab => "bool")),
                (ast_ident("b"), dtype!(symtab => "int"; ( t_num(10) ))),
            ]),
            output_type: Some(dtype!(symtab => "int"; ( t_num(5) ))),
            type_params: vec![],
        };

        let entity_name =
            symtab.add_thing(ast_path("test").inner, Thing::Pipeline(entity.nowhere()));

        let input = ExprKind::PipelineInstance {
            depth: 2.nowhere(),
            name: entity_name.nowhere(),
            args: ArgumentList::Positional(vec![
                Expression::ident(0, 0, "x").nowhere(),
                Expression::ident(1, 1, "b").nowhere(),
            ])
            .nowhere(),
        }
        .with_id(2)
        .nowhere();

        let mut state = TypeState::new();

        // Add eqs for the literals
        let expr_a = TExpr::Name(name_id(0, "a").inner);
        let expr_b = TExpr::Name(name_id(1, "b").inner);
        state.add_eq_from_tvar(expr_a.clone(), TVar::Unknown(100));
        state.add_eq_from_tvar(expr_b.clone(), TVar::Unknown(101));

        let generic_list = state.create_generic_list(GenericListSource::Anonymous, &vec![]);
        state
            .visit_expression(&input, &symtab, &generic_list)
            .unwrap();

        // Check the generic type variables
        ensure_same_type!(state, TExpr::Id(0), TVar::Known(t_bool(&symtab), vec![]));
        ensure_same_type!(
            state,
            TExpr::Id(1),
            TVar::Known(
                t_int(&symtab),
                vec![TypeVar::Known(KnownType::Integer(10), vec![])],
            )
        );
        ensure_same_type!(
            state,
            TExpr::Id(2),
            TVar::Known(
                t_int(&symtab),
                vec![TypeVar::Known(KnownType::Integer(5), vec![])],
            )
        );

        // Check the constraints added to the literals
        ensure_same_type!(state, &TExpr::Id(0), &expr_a);
        ensure_same_type!(state, &TExpr::Id(1), &expr_b);
    }
}
