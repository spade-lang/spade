// This algorithm is based off the excellent lecture here
// https://www.youtube.com/watch?v=xJXcZp2vgLs
//
// The basic idea is to go through every node in the HIR tree, for every typed thing,
// add an equation indicating a constraint on that thing. This can onlytydone once
// and should be done by the visitor for that node. The visitor should then unify
// types according to the rules of the node.

use std::cmp::PartialEq;
use std::collections::{BTreeSet, HashMap};
use std::sync::Arc;

use colored::Colorize;
use hir::expression::CallKind;
use hir::{
    param_util, Binding, ConstGeneric, Parameter, PipelineRegMarkerExtra, TypeExpression, TypeSpec,
    UnitHead, UnitKind, WalTrace, WhereClause,
};
use itertools::Itertools;
use method_resolution::{FunctionLikeName, IntoImplTarget};
use num::{BigInt, Zero};
use serde::{Deserialize, Serialize};
use spade_common::id_tracker::{ExprID, ImplID};
use spade_common::num_ext::InfallibleToBigInt;
use spade_diagnostics::{diag_anyhow, diag_bail, Diagnostic};
use spade_macros::trace_typechecker;
use spade_types::meta_types::{unify_meta, MetaType};
use trace_stack::TraceStack;
use tracing::{info, trace};

use spade_common::location_info::{Loc, WithLocation};
use spade_common::name::{Identifier, NameID, Path};
use spade_hir::param_util::{match_args_with_params, Argument};
use spade_hir::symbol_table::{Patternable, PatternableKind, SymbolTable, TypeSymbol};
use spade_hir::{self as hir, ConstGenericWithId, ImplTarget};
use spade_hir::{
    ArgumentList, Block, ExprKind, Expression, ItemList, Pattern, PatternArgument, Register,
    Statement, TraitName, TraitSpec, TypeParam, Unit,
};
use spade_types::KnownType;

use constraints::{
    bits_to_store, ce_int, ce_var, ConstraintExpr, ConstraintRhs, ConstraintSource, TypeConstraints,
};
use equation::{TraitList, TraitReq, TypeEquations, TypeVar, TypedExpression};
use error::{
    error_pattern_type_mismatch, Result, UnificationError, UnificationErrorExt, UnificationTrace,
};
use fixed_types::{t_bool, t_clock, t_int, t_uint};
use requirements::{Replacement, Requirement};
use trace_stack::{format_trace_stack, TraceStackEntry};

use crate::error::TypeMismatch as Tm;
use crate::fixed_types::t_void;
use crate::requirements::ConstantInt;
use crate::traits::{TraitImpl, TraitImplList};

mod constraints;
pub mod dump;
pub mod equation;
pub mod error;
pub mod expression;
pub mod fixed_types;
pub mod method_resolution;
pub mod mir_type_lowering;
mod requirements;
pub mod testutil;
pub mod trace_stack;
pub mod traits;

pub struct Context<'a> {
    pub symtab: &'a SymbolTable,
    pub items: &'a ItemList,
    pub trait_impls: &'a TraitImplList,
}

// NOTE(allow) This is a debug macro which is not normally used but can come in handy
#[allow(unused_macros)]
macro_rules! add_trace {
    ($self:expr, $($arg : tt) *) => {
        $self.trace_stack.push(TraceStack::Message(format!($($arg)*)))
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
    ImplBlock {
        target: &'a ImplTarget,
        id: ImplID,
    },
    /// For expressions which instantiate generic items
    Expression(ExprID),
}

/// Stored version of GenericListSource
#[derive(Clone, Hash, Eq, PartialEq, Debug)]
pub enum GenericListToken {
    Anonymous(usize),
    Definition(NameID),
    ImplBlock(ImplTarget, ImplID),
    Expression(ExprID),
}

pub struct TurbofishCtx<'a> {
    turbofish: &'a Loc<ArgumentList<TypeExpression>>,
    prev_generic_list: &'a GenericListToken,
    type_ctx: &'a Context<'a>,
}

#[derive(Clone)]
pub struct PipelineState {
    current_stage_depth: TypeVar,
    total_depth: Loc<TypeVar>,
    pipeline_loc: Loc<()>,
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

    /// The type var containing the depth of the pipeline stage we are currently in
    pipeline_state: Option<PipelineState>,

    pub trait_impls: TraitImplList,

    pub trace_stack: Arc<TraceStack>,

    /// (Experimental) Use Affine- or Interval-Arithmetic to bounds check integers in a separate
    /// module.
    pub use_wordlenght_inference: bool,
}

impl Default for TypeState {
    fn default() -> Self {
        Self::new()
    }
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
            trait_impls: TraitImplList::new(),
            pipeline_state: None,
            use_wordlenght_inference: false,
        }
    }

    pub fn set_wordlength_inferece(self, use_wordlenght_inference: bool) -> Self {
        Self {
            use_wordlenght_inference,
            ..self
        }
    }

    pub fn get_equations(&self) -> &TypeEquations {
        &self.equations
    }

    pub fn get_constraints(&self) -> &TypeConstraints {
        &self.constraints
    }

    // Get a generic list with a safe unwrap since a token is acquired
    pub fn get_generic_list<'a>(
        &'a self,
        generic_list_token: &'a GenericListToken,
    ) -> &'a HashMap<NameID, TypeVar> {
        &self.generic_lists[generic_list_token]
    }

    #[tracing::instrument(level = "trace", skip_all)]
    fn hir_type_expr_to_var<'a>(
        &'a mut self,
        e: &Loc<hir::TypeExpression>,
        generic_list_token: &GenericListToken,
    ) -> Result<TypeVar> {
        let tvar = match &e.inner {
            hir::TypeExpression::Integer(i) => {
                TypeVar::Known(e.loc(), KnownType::Integer(i.clone()), vec![])
            }
            hir::TypeExpression::TypeSpec(spec) => {
                self.type_var_from_hir(e.loc(), &spec.clone(), generic_list_token)?
            }
            hir::TypeExpression::ConstGeneric(g) => {
                let constraint = self.visit_const_generic(g, generic_list_token)?;

                let tvar = self.new_generic_tlnumber(e.loc());
                self.add_constraint(
                    tvar.clone(),
                    constraint,
                    g.loc(),
                    &tvar,
                    ConstraintSource::Where,
                );

                tvar
            }
        };

        Ok(tvar)
    }

    #[tracing::instrument(level = "trace", skip_all, fields(%hir_type))]
    pub fn type_var_from_hir<'a>(
        &'a mut self,
        loc: Loc<()>,
        hir_type: &crate::hir::TypeSpec,
        generic_list_token: &GenericListToken,
    ) -> Result<TypeVar> {
        let generic_list = self.get_generic_list(generic_list_token);
        match &hir_type {
            hir::TypeSpec::Declared(base, params) => {
                let params = params
                    .iter()
                    .map(|e| self.hir_type_expr_to_var(e, generic_list_token))
                    .collect::<Result<Vec<_>>>()?;

                Ok(TypeVar::Known(
                    loc,
                    KnownType::Named(base.inner.clone()),
                    params,
                ))
            }
            hir::TypeSpec::Generic(name) => match generic_list.get(&name.inner) {
                Some(t) => Ok(t.clone()),
                None => {
                    for list_source in self.generic_lists.keys() {
                        info!("Generic lists exist for {list_source:?}");
                    }
                    info!("Current source is {generic_list_token:?}");
                    panic!("No entry in generic list for {name}");
                }
            },
            hir::TypeSpec::Tuple(inner) => {
                let inner = inner
                    .iter()
                    .map(|t| self.type_var_from_hir(loc, t, generic_list_token))
                    .collect::<Result<_>>()?;
                Ok(TypeVar::tuple(loc, inner))
            }
            hir::TypeSpec::Array { inner, size } => {
                let inner = self.type_var_from_hir(loc, inner, generic_list_token)?;
                let size = self.hir_type_expr_to_var(size, generic_list_token)?;

                Ok(TypeVar::array(loc, inner, size))
            }
            hir::TypeSpec::Unit(_) => {
                todo!("Support unit type in type inference")
            }
            hir::TypeSpec::Wire(inner) => Ok(TypeVar::wire(
                loc,
                self.type_var_from_hir(loc, inner, generic_list_token)?,
            )),
            hir::TypeSpec::Inverted(inner) => Ok(TypeVar::inverted(
                loc,
                self.type_var_from_hir(loc, inner, generic_list_token)?,
            )),
            hir::TypeSpec::Wildcard(_) => Ok(self.new_generic_any()),
            hir::TypeSpec::TraitSelf(_) => {
                panic!("Trying to convert TraitSelf to type inference type var")
            }
        }
    }

    /// Returns the type of the expression with the specified id. Error if no equation
    /// for the specified expression exists
    pub fn type_of(&self, expr: &TypedExpression) -> Result<TypeVar> {
        for (e, t) in &self.equations {
            if e == expr {
                return Ok(t.clone());
            }
        }
        panic!("Tried looking up the type of {expr:?} but it was not found")
    }

    pub fn new_generic_int(&mut self, loc: Loc<()>, symtab: &SymbolTable) -> TypeVar {
        TypeVar::Known(loc, t_int(symtab), vec![self.new_generic_tluint(loc)])
    }

    /// Return a new generic int. The first returned value is int<N>, and the second
    /// value is N
    pub fn new_split_generic_int(
        &mut self,
        loc: Loc<()>,
        symtab: &SymbolTable,
    ) -> (TypeVar, TypeVar) {
        let size = self.new_generic_tlint(loc);
        let full = TypeVar::Known(loc, t_int(symtab), vec![size.clone()]);
        (full, size)
    }

    pub fn new_split_generic_uint(
        &mut self,
        loc: Loc<()>,
        symtab: &SymbolTable,
    ) -> (TypeVar, TypeVar) {
        let size = self.new_generic_tluint(loc);
        let full = TypeVar::Known(loc, t_uint(symtab), vec![size.clone()]);
        (full, size)
    }

    pub fn new_generic_with_meta(&mut self, loc: Loc<()>, meta: MetaType) -> TypeVar {
        let id = self.new_typeid();
        TypeVar::Unknown(loc, id, TraitList::empty(), meta)
    }

    pub fn new_generic_type(&mut self, loc: Loc<()>) -> TypeVar {
        let id = self.new_typeid();
        TypeVar::Unknown(loc, id, TraitList::empty(), MetaType::Type)
    }

    pub fn new_generic_any(&mut self) -> TypeVar {
        let id = self.new_typeid();
        // NOTE: ().nowhere() is fine here, we can never fail to unify with MetaType::Any so
        // this loc will never be displayed
        TypeVar::Unknown(().nowhere(), id, TraitList::empty(), MetaType::Any)
    }

    pub fn new_generic_tlbool(&mut self, loc: Loc<()>) -> TypeVar {
        let id = self.new_typeid();
        TypeVar::Unknown(loc, id, TraitList::empty(), MetaType::Bool)
    }

    pub fn new_generic_tluint(&mut self, loc: Loc<()>) -> TypeVar {
        let id = self.new_typeid();
        TypeVar::Unknown(loc, id, TraitList::empty(), MetaType::Uint)
    }

    pub fn new_generic_tlint(&mut self, loc: Loc<()>) -> TypeVar {
        let id = self.new_typeid();
        TypeVar::Unknown(loc, id, TraitList::empty(), MetaType::Int)
    }

    pub fn new_generic_tlnumber(&mut self, loc: Loc<()>) -> TypeVar {
        let id = self.new_typeid();
        TypeVar::Unknown(loc, id, TraitList::empty(), MetaType::Number)
    }

    pub fn new_generic_number(&mut self, loc: Loc<()>, ctx: &Context) -> (TypeVar, TypeVar) {
        let number = ctx
            .symtab
            .lookup_trait(&Path::from_strs(&["Number"]).nowhere())
            .expect("Did not find number in symtab")
            .0;
        let id = self.new_typeid();
        let size = self.new_generic_tluint(loc);
        let t = TraitReq {
            name: TraitName::Named(number.nowhere()),
            type_params: vec![size.clone()],
        }
        .nowhere();
        (
            TypeVar::Unknown(loc, id, TraitList::from_vec(vec![t]), MetaType::Type),
            size,
        )
    }

    pub fn new_generic_with_traits(&mut self, loc: Loc<()>, traits: TraitList) -> TypeVar {
        let id = self.new_typeid();
        TypeVar::Unknown(loc, id, traits, MetaType::Type)
    }

    /// Returns the current pipeline state. `access_loc` is *not* used to specify where to get the
    /// state from, it is only used for the Diagnostic::bug that gets emitted if there is no
    /// pipeline state
    pub fn get_pipeline_state<T>(&self, access_loc: &Loc<T>) -> Result<&PipelineState> {
        self.pipeline_state
            .as_ref()
            .ok_or_else(|| diag_anyhow!(access_loc, "Expected to have a pipeline state"))
    }

    #[trace_typechecker]
    #[tracing::instrument(level = "trace", skip_all, fields(%entity.name))]
    pub fn visit_unit(&mut self, entity: &Loc<Unit>, ctx: &Context) -> Result<()> {
        self.trait_impls = ctx.trait_impls.clone();

        let generic_list = self.create_generic_list(
            GenericListSource::Definition(&entity.name.name_id().inner),
            &entity.head.unit_type_params,
            &entity.head.scope_type_params,
            None,
            // NOTE: I'm not 100% sure we need to pass these here, the information
            // is probably redundant
            &entity.head.where_clauses,
        )?;

        // Add equations for the inputs
        for (name, t) in &entity.inputs {
            let tvar = self.type_var_from_hir(t.loc(), t, &generic_list)?;
            self.add_equation(TypedExpression::Name(name.inner.clone()), tvar)
        }

        if let UnitKind::Pipeline {
            depth,
            depth_typeexpr_id,
        } = &entity.head.unit_kind.inner
        {
            let depth_var = self.hir_type_expr_to_var(depth, &generic_list)?;
            self.add_equation(TypedExpression::Id(*depth_typeexpr_id), depth_var.clone());
            self.pipeline_state = Some(PipelineState {
                current_stage_depth: TypeVar::Known(
                    entity.head.unit_kind.loc(),
                    KnownType::Integer(BigInt::zero()),
                    vec![],
                ),
                pipeline_loc: entity.loc(),
                total_depth: depth_var.clone().at_loc(depth),
            });
            self.add_requirement(Requirement::PositivePipelineDepth {
                depth: depth_var.at_loc(depth),
            });
            self.unify(
                &TypedExpression::Name(entity.inputs[0].0.clone().inner),
                &t_clock(ctx.symtab).at_loc(&entity.head.unit_kind),
                ctx,
            )
            .into_diagnostic(
                entity.inputs[0].1.loc(),
                |diag,
                 Tm {
                     g: got,
                     e: _expected,
                 }| {
                    diag.message(format!(
                        "First pipeline argument must be a clock. Got {got}"
                    ))
                    .primary_label("expected clock")
                },
            )?;
            // In order to catch negative depth early when they are specified as literals,
            // we'll instantly check requirements here
            self.check_requirements(ctx)?;
        }

        self.visit_expression(&entity.body, ctx, &generic_list)?;

        // Ensure that the output type matches what the user specified, and unit otherwise
        if let Some(output_type) = &entity.head.output_type {
            let tvar = self.type_var_from_hir(output_type.loc(), output_type, &generic_list)?;

            self.trace_stack.push(TraceStackEntry::Message(format!(
                "Unifying with output type {tvar:?}"
            )));
            self.unify(&TypedExpression::Id(entity.body.inner.id), &tvar, ctx)
                .into_diagnostic_no_expected_source(
                    &entity.body,
                    |diag,
                     Tm {
                         g: got,
                         e: expected,
                     }| {
                        // FIXME: Might want to check if there is no return value in the block
                        // and in that case suggest adding it.
                        diag.message(format!(
                            "Output type mismatch. Expected {expected}, got {got}"
                        ))
                        .primary_label(format!("Found type {got}"))
                        .secondary_label(output_type, format!("{expected} type specified here"))
                    },
                )?;
        } else {
            // No output type, so unify with the unit type.
            self.unify(
                &TypedExpression::Id(entity.body.inner.id),
                &t_void(ctx.symtab).at_loc(&entity.head.name),
                ctx
            )
            .into_diagnostic_no_expected_source(entity.body.loc(), |diag, Tm{g: got, e: _expected}| {
                diag.message("Output type mismatch")
                    .primary_label(format!("Found type {got}"))
                    .note(format!(
                        "The {} does not specify a return type.\nAdd a return type, or remove the return value.",
                        entity.head.unit_kind.name()
                    ))
            })?;
        }

        if let Some(PipelineState {
            current_stage_depth,
            pipeline_loc,
            total_depth,
        }) = self.pipeline_state.clone()
        {
            self.unify(&total_depth.inner, &current_stage_depth, ctx)
                .into_diagnostic_no_expected_source(pipeline_loc, |diag, tm| {
                    let (e, g) = tm.display_e_g();
                    diag.message(format!("Pipeline depth mismatch. Expected {g} got {e}"))
                        .primary_label(format!("Found {e} stages in this pipeline"))
                })?;
        }

        self.check_requirements(ctx)?;

        // NOTE: We may accidentally leak a stage depth if this function returns early. However,
        // since we only use stage depths in pipelines where we re-set it when we enter,
        // accidentally leaving a depth in place should not trigger any *new* compiler bugs, but
        // may help track something down
        self.pipeline_state = None;

        Ok(())
    }

    #[trace_typechecker]
    #[tracing::instrument(level = "trace", skip_all)]
    fn visit_argument_list(
        &mut self,
        args: &Loc<ArgumentList<Expression>>,
        ctx: &Context,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        for expr in args.expressions() {
            self.visit_expression(expr, ctx, generic_list)?;
        }
        Ok(())
    }

    #[trace_typechecker]
    fn type_check_argument_list(
        &mut self,
        args: &[Argument<Expression, TypeSpec>],
        ctx: &Context,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        for Argument {
            target,
            target_type,
            value,
            kind,
        } in args.iter()
        {
            let target_type = self.type_var_from_hir(value.loc(), target_type, generic_list)?;

            let loc = match kind {
                hir::param_util::ArgumentKind::Positional => value.loc(),
                hir::param_util::ArgumentKind::Named => value.loc(),
                hir::param_util::ArgumentKind::ShortNamed => target.loc(),
            };

            self.unify(&value.inner, &target_type, ctx)
                .into_diagnostic(
                    loc,
                    |d,
                     Tm {
                         e: expected,
                         g: got,
                     }| {
                        d.message(format!(
                            "Argument type mismatch. Expected {expected} got {got}"
                        ))
                        .primary_label(format!("expected {expected}"))
                    },
                )?;
        }

        Ok(())
    }

    #[tracing::instrument(level = "trace", skip_all)]
    #[trace_typechecker]
    pub fn visit_expression(
        &mut self,
        expression: &Loc<Expression>,
        ctx: &Context,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        let new_type = self.new_generic_type(expression.loc());
        self.add_equation(TypedExpression::Id(expression.inner.id), new_type);

        // Recurse down the expression
        match &expression.inner.kind {
            ExprKind::Identifier(_) => self.visit_identifier(expression, ctx)?,
            ExprKind::TypeLevelInteger(_) => {
                self.visit_type_level_integer(expression, generic_list, ctx)?
            }
            ExprKind::IntLiteral(_, _) => self.visit_int_literal(expression, ctx)?,
            ExprKind::BoolLiteral(_) => self.visit_bool_literal(expression, ctx)?,
            ExprKind::BitLiteral(_) => self.visit_bit_literal(expression, ctx)?,
            ExprKind::TupleLiteral(_) => self.visit_tuple_literal(expression, ctx, generic_list)?,
            ExprKind::TupleIndex(_, _) => self.visit_tuple_index(expression, ctx, generic_list)?,
            ExprKind::ArrayLiteral(_) => self.visit_array_literal(expression, ctx, generic_list)?,
            ExprKind::ArrayShorthandLiteral(_, _) => {
                self.visit_array_shorthand_literal(expression, ctx, generic_list)?
            }
            ExprKind::CreatePorts => self.visit_create_ports(expression, ctx, generic_list)?,
            ExprKind::FieldAccess(_, _) => {
                self.visit_field_access(expression, ctx, generic_list)?
            }
            ExprKind::MethodCall { .. } => self.visit_method_call(expression, ctx, generic_list)?,
            ExprKind::Index(_, _) => self.visit_index(expression, ctx, generic_list)?,
            ExprKind::RangeIndex { .. } => self.visit_range_index(expression, ctx, generic_list)?,
            ExprKind::Block(_) => self.visit_block_expr(expression, ctx, generic_list)?,
            ExprKind::If(_, _, _) => self.visit_if(expression, ctx, generic_list)?,
            ExprKind::Match(_, _) => self.visit_match(expression, ctx, generic_list)?,
            ExprKind::BinaryOperator(_, _, _) => {
                self.visit_binary_operator(expression, ctx, generic_list)?
            }
            ExprKind::UnaryOperator(_, _) => {
                self.visit_unary_operator(expression, ctx, generic_list)?
            }
            ExprKind::Call {
                kind,
                callee,
                args,
                turbofish,
            } => {
                let head = ctx.symtab.unit_by_id(&callee.inner);

                self.handle_function_like(
                    expression.map_ref(|e| e.id),
                    &expression.get_type(self)?,
                    &FunctionLikeName::Free(callee.inner.clone()),
                    &head,
                    kind,
                    args,
                    ctx,
                    true,
                    false,
                    turbofish.as_ref().map(|turbofish| TurbofishCtx {
                        turbofish,
                        prev_generic_list: generic_list,
                        type_ctx: ctx,
                    }),
                    generic_list,
                )?;
            }
            ExprKind::PipelineRef { .. } => {
                self.visit_pipeline_ref(expression, generic_list, ctx)?;
            }
            ExprKind::StageReady | ExprKind::StageValid => {
                self.unify_expression_generic_error(
                    expression,
                    &t_bool(ctx.symtab).at_loc(expression),
                    ctx,
                )?;
            }
            ExprKind::TypeLevelIf(cond, on_true, on_false) => {
                let cond_var = self.visit_const_generic_with_id(
                    cond,
                    generic_list,
                    ConstraintSource::TypeLevelIf,
                    ctx,
                )?;
                let t_bool = self.new_generic_tlbool(cond.loc());
                self.unify(&cond_var, &t_bool, ctx).into_diagnostic(
                    cond,
                    |diag, Tm { e: _, g }| {
                        diag.message(format!("gen if conditions must be #bool, got {g}"))
                    },
                )?;

                self.visit_expression(on_true, ctx, generic_list)?;
                self.visit_expression(on_false, ctx, generic_list)?;

                self.unify_expression_generic_error(expression, on_true.as_ref(), ctx)?;
                self.unify_expression_generic_error(expression, on_false.as_ref(), ctx)?;
            }
            ExprKind::Null => {}
        }
        Ok(())
    }

    // Common handler for entities, functions and pipelines
    #[tracing::instrument(level = "trace", skip_all, fields(%name))]
    #[trace_typechecker]
    fn handle_function_like(
        &mut self,
        expression_id: Loc<ExprID>,
        expression_type: &TypeVar,
        name: &FunctionLikeName,
        head: &Loc<UnitHead>,
        call_kind: &CallKind,
        args: &Loc<ArgumentList<Expression>>,
        ctx: &Context,
        // Whether or not to visit the argument expressions passed to the function here. This
        // should not be done if the expressoins have been visited before, for example, when
        // handling methods
        visit_args: bool,
        // If we are calling a method, we have an implicit self argument which means
        // that any error reporting number of arguments should be reduced by one
        is_method: bool,
        turbofish: Option<TurbofishCtx>,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        // Add new symbols for all the type parameters
        let unit_generic_list = self.create_generic_list(
            GenericListSource::Expression(expression_id.inner),
            &head.unit_type_params,
            &head.scope_type_params,
            turbofish,
            &head.where_clauses,
        )?;

        match (&head.unit_kind.inner, call_kind) {
            (
                UnitKind::Pipeline {
                    depth: udepth,
                    depth_typeexpr_id: _,
                },
                CallKind::Pipeline {
                    inst_loc: _,
                    depth: cdepth,
                    depth_typeexpr_id: cdepth_typeexpr_id,
                },
            ) => {
                let definition_depth = self.hir_type_expr_to_var(udepth, &unit_generic_list)?;
                let call_depth = self.hir_type_expr_to_var(cdepth, generic_list)?;

                // NOTE: We're not adding udepth_typeexpr_id here as that would break
                // in the future if we try to do recursion. We will also never need to look
                // up the depth in the definition
                self.add_equation(TypedExpression::Id(*cdepth_typeexpr_id), call_depth.clone());

                self.unify(&call_depth, &definition_depth, ctx)
                    .into_diagnostic_no_expected_source(cdepth, |diag, Tm { e, g }| {
                        diag.message("Pipeline depth mismatch")
                            .primary_label(format!("Expected depth {e}, got {g}"))
                            .secondary_label(udepth, format!("{name} has depth {e}"))
                    })?;
            }
            _ => {}
        }

        if visit_args {
            self.visit_argument_list(args, ctx, &generic_list)?;
        }

        let type_params = &head.get_type_params();

        // Special handling of built in functions
        macro_rules! handle_special_functions {
            ($([$($path:expr),*] => $handler:expr),*) => {
                $(
                    let path = Path(vec![$(Identifier($path.to_string()).nowhere()),*]).nowhere();
                    if ctx.symtab
                        .try_lookup_final_id(&path)
                        .map(|n| &FunctionLikeName::Free(n) == name)
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
                self.get_generic_list(&unit_generic_list)[&type_params[$idx].name_id()].clone()
            };
        }

        let matched_args =
            match_args_with_params(args, &head.inputs.inner, is_method).map_err(|e| {
                let diag: Diagnostic = e.into();
                diag.secondary_label(
                    head,
                    format!("{kind} defined here", kind = head.unit_kind.name()),
                )
            })?;

        handle_special_functions! {
            ["std", "conv", "concat"] => {
                self.handle_concat(
                    expression_id,
                    generic_arg!(0),
                    generic_arg!(1),
                    generic_arg!(2),
                    &matched_args,
                    ctx
                )?
            },
            ["std", "conv", "trunc"] => {
                self.handle_trunc(
                    expression_id,
                    generic_arg!(0),
                    generic_arg!(1),
                    &matched_args,
                    ctx
                )?
            },
            ["std", "ops", "comb_div"] => {
                self.handle_comb_mod_or_div(
                    generic_arg!(0),
                    &matched_args,
                    ctx
                )?
            },
            ["std", "ops", "comb_mod"] => {
                self.handle_comb_mod_or_div(
                    generic_arg!(0),
                    &matched_args,
                    ctx
                )?
            },
            ["std", "mem", "clocked_memory"]  => {
                let num_elements = generic_arg!(0);
                let addr_size = generic_arg!(2);

                self.handle_clocked_memory(num_elements, addr_size, &matched_args, ctx)?
            },
            // NOTE: the last argument of _init does not need special treatment, so
            // we can use the same code path for both for now
            ["std", "mem", "clocked_memory_init"]  => {
                let num_elements = generic_arg!(0);
                let addr_size = generic_arg!(2);

                self.handle_clocked_memory(num_elements, addr_size, &matched_args, ctx)?
            },
            ["std", "mem", "read_memory"]  => {
                let addr_size = generic_arg!(0);
                let num_elements = generic_arg!(2);

                self.handle_read_memory(num_elements, addr_size, &matched_args, ctx)?
            }
        };

        // Unify the types of the arguments
        self.type_check_argument_list(&matched_args, ctx, &unit_generic_list)?;

        let return_type = head
            .output_type
            .as_ref()
            .map(|o| self.type_var_from_hir(expression_id.loc(), o, &unit_generic_list))
            .transpose()?
            .unwrap_or_else(|| TypeVar::Known(expression_id.loc(), t_void(ctx.symtab), vec![]));

        self.unify(expression_type, &return_type, ctx)
            .into_default_diagnostic(expression_id.loc())?;

        Ok(())
    }

    pub fn handle_concat(
        &mut self,
        expression_id: Loc<ExprID>,
        source_lhs_ty: TypeVar,
        source_rhs_ty: TypeVar,
        source_result_ty: TypeVar,
        args: &[Argument<Expression, TypeSpec>],
        ctx: &Context,
    ) -> Result<()> {
        let (lhs_type, lhs_size) = self.new_generic_number(expression_id.loc(), ctx);
        let (rhs_type, rhs_size) = self.new_generic_number(expression_id.loc(), ctx);
        let (result_type, result_size) = self.new_generic_number(expression_id.loc(), ctx);
        self.unify(&source_lhs_ty, &lhs_type, ctx)
            .into_default_diagnostic(args[0].value.loc())?;
        self.unify(&source_rhs_ty, &rhs_type, ctx)
            .into_default_diagnostic(args[1].value.loc())?;
        self.unify(&source_result_ty, &result_type, ctx)
            .into_default_diagnostic(expression_id.loc())?;

        // Result size is sum of input sizes
        self.add_constraint(
            result_size.clone(),
            ce_var(&lhs_size) + ce_var(&rhs_size),
            expression_id.loc(),
            &result_size,
            ConstraintSource::Concatenation,
        );
        self.add_constraint(
            lhs_size.clone(),
            ce_var(&result_size) + -ce_var(&rhs_size),
            args[0].value.loc(),
            &lhs_size,
            ConstraintSource::Concatenation,
        );
        self.add_constraint(
            rhs_size.clone(),
            ce_var(&result_size) + -ce_var(&lhs_size),
            args[1].value.loc(),
            &rhs_size,
            ConstraintSource::Concatenation,
        );

        self.add_requirement(Requirement::SharedBase(vec![
            lhs_type.at_loc(args[0].value),
            rhs_type.at_loc(args[1].value),
            result_type.at_loc(&expression_id.loc()),
        ]));
        Ok(())
    }

    pub fn handle_trunc(
        &mut self,
        expression_id: Loc<ExprID>,
        source_in_ty: TypeVar,
        source_result_ty: TypeVar,
        args: &[Argument<Expression, TypeSpec>],
        ctx: &Context,
    ) -> Result<()> {
        let (in_ty, _) = self.new_generic_number(expression_id.loc(), ctx);
        let (result_type, _) = self.new_generic_number(expression_id.loc(), ctx);
        self.unify(&source_in_ty, &in_ty, ctx)
            .into_default_diagnostic(args[0].value.loc())?;
        self.unify(&source_result_ty, &result_type, ctx)
            .into_default_diagnostic(expression_id.loc())?;

        self.add_requirement(Requirement::SharedBase(vec![
            in_ty.at_loc(args[0].value),
            result_type.at_loc(&expression_id.loc()),
        ]));
        Ok(())
    }

    pub fn handle_comb_mod_or_div(
        &mut self,
        n_ty: TypeVar,
        args: &[Argument<Expression, TypeSpec>],
        ctx: &Context,
    ) -> Result<()> {
        let (num, _) = self.new_generic_number(args[0].value.loc(), ctx);
        self.unify(&n_ty, &num, ctx)
            .into_default_diagnostic(args[0].value.loc())?;
        Ok(())
    }

    pub fn handle_clocked_memory(
        &mut self,
        num_elements: TypeVar,
        addr_size_arg: TypeVar,
        args: &[Argument<Expression, TypeSpec>],
        ctx: &Context,
    ) -> Result<()> {
        // FIXME: When we support where clauses, we should move this
        // definition into the definition of clocked_memory
        let (addr_type, addr_size) = self.new_split_generic_uint(args[1].value.loc(), ctx.symtab);
        let arg1_loc = args[1].value.loc();
        let port_type = TypeVar::array(
            arg1_loc,
            TypeVar::tuple(
                args[1].value.loc(),
                vec![
                    self.new_generic_type(arg1_loc),
                    addr_type,
                    self.new_generic_type(arg1_loc),
                ],
            ),
            self.new_generic_tluint(arg1_loc),
        );

        self.add_constraint(
            addr_size.clone(),
            bits_to_store(ce_var(&num_elements) - ce_int(1.to_bigint())),
            args[1].value.loc(),
            &port_type,
            ConstraintSource::MemoryIndexing,
        );

        // NOTE: Unwrap is safe, size is still generic at this point
        self.unify(&addr_size, &addr_size_arg, ctx).unwrap();
        self.unify_expression_generic_error(args[1].value, &port_type, ctx)?;

        Ok(())
    }

    pub fn handle_read_memory(
        &mut self,
        num_elements: TypeVar,
        addr_size_arg: TypeVar,
        args: &[Argument<Expression, TypeSpec>],
        ctx: &Context,
    ) -> Result<()> {
        let (addr_type, addr_size) = self.new_split_generic_uint(args[1].value.loc(), ctx.symtab);

        self.add_constraint(
            addr_size.clone(),
            bits_to_store(ce_var(&num_elements) - ce_int(1.to_bigint())),
            args[1].value.loc(),
            &addr_type,
            ConstraintSource::MemoryIndexing,
        );

        // NOTE: Unwrap is safe, size is still generic at this point
        self.unify(&addr_size, &addr_size_arg, ctx).unwrap();

        Ok(())
    }

    #[tracing::instrument(level = "trace", skip(self, turbofish, where_clauses))]
    pub fn create_generic_list(
        &mut self,
        source: GenericListSource,
        type_params: &[Loc<TypeParam>],
        scope_type_params: &[Loc<TypeParam>],
        turbofish: Option<TurbofishCtx>,
        where_clauses: &[Loc<WhereClause>],
    ) -> Result<GenericListToken> {
        let turbofish_params = if let Some(turbofish) = turbofish.as_ref() {
            if type_params.is_empty() {
                return Err(Diagnostic::error(
                    turbofish.turbofish,
                    "Turbofish on non-generic function",
                )
                .primary_label("Turbofish on non-generic function"));
            }

            let matched_params =
                param_util::match_args_with_params(turbofish.turbofish, &type_params, false)?;

            // We want this to be positional, but the params we get from matching are
            // named, transform it. We'll do some unwrapping here, but it is safe
            // because we know all params are present
            matched_params
                .iter()
                .map(|matched_param| {
                    let i = type_params
                        .iter()
                        .enumerate()
                        .find_map(|(i, param)| match &param.inner {
                            TypeParam {
                                ident,
                                name_id: _,
                                trait_bounds: _,
                                meta: _,
                            } => {
                                if ident == matched_param.target {
                                    Some(i)
                                } else {
                                    None
                                }
                            }
                        })
                        .unwrap();
                    (i, matched_param)
                })
                .sorted_by_key(|(i, _)| *i)
                .map(|(_, mp)| Some(mp.value))
                .collect::<Vec<_>>()
        } else {
            type_params.iter().map(|_| None).collect::<Vec<_>>()
        };

        let mut inline_trait_bounds: Vec<Loc<WhereClause>> = vec![];

        let scope_type_params = scope_type_params
            .iter()
            .map(|param| {
                let hir::TypeParam {
                    ident,
                    name_id,
                    trait_bounds,
                    meta,
                } = &param.inner;
                if !trait_bounds.is_empty() {
                    if let MetaType::Type = meta {
                        inline_trait_bounds.push(
                            WhereClause::Type {
                                target: name_id.clone().at_loc(ident),
                                traits: trait_bounds.clone(),
                            }
                            .at_loc(param),
                        );
                    } else {
                        return Err(Diagnostic::bug(param, "Trait bounds on generic int")
                            .primary_label("Trait bounds are only allowed on type parameters"));
                    }
                }
                Ok((
                    name_id.clone(),
                    self.new_generic_with_meta(param.loc(), meta.clone()),
                ))
            })
            .collect::<Result<Vec<_>>>()?;

        let new_list = type_params
            .iter()
            .enumerate()
            .map(|(i, param)| {
                let hir::TypeParam {
                    ident,
                    name_id,
                    trait_bounds,
                    meta,
                } = &param.inner;

                let t = self.new_generic_with_meta(param.loc(), meta.clone());

                if let Some(tf) = &turbofish_params[i] {
                    let tf_ctx = turbofish.as_ref().unwrap();
                    let ty = self.hir_type_expr_to_var(tf, tf_ctx.prev_generic_list)?;
                    self.unify(&ty, &t, tf_ctx.type_ctx)
                        .into_default_diagnostic(param)?;
                }

                if !trait_bounds.is_empty() {
                    if let MetaType::Type = meta {
                        inline_trait_bounds.push(
                            WhereClause::Type {
                                target: name_id.clone().at_loc(ident),
                                traits: trait_bounds.clone(),
                            }
                            .at_loc(param),
                        );
                    }
                    Ok((name_id.clone(), t))
                } else {
                    Ok((name_id.clone(), self.check_var_for_replacement(t)))
                }
            })
            .collect::<Result<Vec<_>>>()?
            .into_iter()
            .chain(scope_type_params.into_iter())
            .map(|(name, t)| (name, t.clone()))
            .collect::<HashMap<_, _>>();

        self.trace_stack
            .push(TraceStackEntry::NewGenericList(new_list.clone()));

        let token = self.add_mapped_generic_list(source, new_list.clone());

        for constraint in where_clauses.iter().chain(inline_trait_bounds.iter()) {
            match &constraint.inner {
                WhereClause::Type { target, traits } => {
                    self.visit_trait_bounds(target, traits.as_slice(), &token)?;
                }
                WhereClause::Int { target, constraint } => {
                    let int_constraint = self.visit_const_generic(constraint, &token)?;
                    let tvar = new_list.get(target).ok_or_else(|| {
                        Diagnostic::error(
                            target,
                            format!("{target} is not a generic parameter on this unit"),
                        )
                        .primary_label("Not a generic parameter")
                    })?;

                    self.add_constraint(
                        tvar.clone(),
                        int_constraint,
                        constraint.loc(),
                        &tvar,
                        ConstraintSource::Where,
                    );
                }
            }
        }

        Ok(token)
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
            GenericListSource::ImplBlock { target, id } => {
                GenericListToken::ImplBlock(target.clone(), id)
            }
            GenericListSource::Expression(id) => GenericListToken::Expression(id),
        };

        if self
            .generic_lists
            .insert(reference.clone(), mapping)
            .is_some()
        {
            panic!("A generic list already existed for {reference:?}");
        }
        reference
    }

    #[tracing::instrument(level = "trace", skip_all)]
    #[trace_typechecker]
    pub fn visit_block(
        &mut self,
        block: &Block,
        ctx: &Context,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        for statement in &block.statements {
            self.visit_statement(statement, ctx, generic_list)?;
        }
        if let Some(result) = &block.result {
            self.visit_expression(result, ctx, generic_list)?;
        }
        Ok(())
    }

    #[tracing::instrument(level = "trace", skip_all)]
    #[trace_typechecker]
    pub fn visit_impl_blocks(&mut self, item_list: &ItemList) -> Result<TraitImplList> {
        let mut trait_impls = TraitImplList::new();
        for (target, impls) in &item_list.impls {
            for ((trait_name, type_expressions), impl_block) in impls {
                let generic_list = self.create_generic_list(
                    GenericListSource::ImplBlock {
                        target,
                        id: impl_block.id,
                    },
                    &[],
                    impl_block.type_params.as_slice(),
                    None,
                    &[],
                )?;

                let loc = trait_name
                    .name_loc()
                    .map(|n| ().at_loc(&n))
                    .unwrap_or(().at_loc(&impl_block));

                let mapped_type_vars = type_expressions
                    .iter()
                    .map(|param| {
                        self.hir_type_expr_to_var(&param.clone().at_loc(&loc), &generic_list)
                    })
                    .collect::<Result<_>>()?;

                trait_impls
                    .inner
                    .entry(target.clone())
                    .or_default()
                    .push(TraitImpl {
                        name: trait_name.clone(),
                        type_params: mapped_type_vars,
                        impl_block: impl_block.inner.clone(),
                    });
            }
        }

        Ok(trait_impls)
    }

    #[trace_typechecker]
    pub fn visit_pattern(
        &mut self,
        pattern: &Loc<Pattern>,
        ctx: &Context,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        let new_type = self.new_generic_type(pattern.loc());
        self.add_equation(TypedExpression::Id(pattern.inner.id), new_type);
        match &pattern.inner.kind {
            hir::PatternKind::Integer(val) => {
                let (num_t, _) = &self.new_generic_number(pattern.loc(), ctx);
                self.add_requirement(Requirement::FitsIntLiteral {
                    value: ConstantInt::Literal(val.clone()),
                    target_type: num_t.clone().at_loc(pattern),
                });
                self.unify(pattern, num_t, ctx)
                    .expect("Failed to unify new_generic with int");
            }
            hir::PatternKind::Bool(_) => {
                self.unify(pattern, &t_bool(ctx.symtab).at_loc(pattern), ctx)
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
                    ctx,
                )
                .into_default_diagnostic(name.loc())?;
            }
            hir::PatternKind::Tuple(subpatterns) => {
                for pattern in subpatterns {
                    self.visit_pattern(pattern, ctx, generic_list)?;
                }
                let tuple_type = TypeVar::tuple(
                    pattern.loc(),
                    subpatterns
                        .iter()
                        .map(|pattern| {
                            let p_type = pattern.get_type(self)?;
                            Ok(p_type)
                        })
                        .collect::<Result<_>>()?,
                );

                self.unify(pattern, &tuple_type, ctx)
                    .expect("Unification of new_generic with tuple type cannot fail");
            }
            hir::PatternKind::Array(inner) => {
                for pattern in inner {
                    self.visit_pattern(pattern, ctx, generic_list)?;
                }
                if inner.len() == 0 {
                    return Err(
                        Diagnostic::error(pattern, "Empty array patterns are unsupported")
                            .primary_label("Empty array pattern"),
                    );
                } else {
                    let inner_t = inner[0].get_type(self)?;

                    for pattern in inner.iter().skip(1) {
                        self.unify(pattern, &inner_t, ctx)
                            .into_default_diagnostic(pattern)?;
                    }

                    self.unify(
                        pattern,
                        &TypeVar::Known(
                            pattern.loc(),
                            KnownType::Array,
                            vec![
                                inner_t,
                                TypeVar::Known(
                                    pattern.loc(),
                                    KnownType::Integer(inner.len().to_bigint()),
                                    vec![],
                                ),
                            ],
                        ),
                        ctx,
                    )
                    .into_default_diagnostic(pattern)?;
                }
            }
            hir::PatternKind::Type(name, args) => {
                let (condition_type, params, generic_list) =
                    match ctx.symtab.patternable_type_by_id(name).inner {
                        Patternable {
                            kind: PatternableKind::Enum,
                            params: _,
                        } => {
                            let enum_variant = ctx.symtab.enum_variant_by_id(name).inner;
                            let generic_list = self.create_generic_list(
                                GenericListSource::Anonymous,
                                &enum_variant.type_params,
                                &[],
                                None,
                                &[],
                            )?;

                            let condition_type = self.type_var_from_hir(
                                pattern.loc(),
                                &enum_variant.output_type,
                                &generic_list,
                            )?;

                            (condition_type, enum_variant.params, generic_list)
                        }
                        Patternable {
                            kind: PatternableKind::Struct,
                            params: _,
                        } => {
                            let s = ctx.symtab.struct_by_id(name).inner;
                            let generic_list = self.create_generic_list(
                                GenericListSource::Anonymous,
                                &s.type_params,
                                &[],
                                None,
                                &[],
                            )?;

                            let condition_type =
                                self.type_var_from_hir(pattern.loc(), &s.self_type, &generic_list)?;

                            (condition_type, s.params, generic_list)
                        }
                    };

                self.unify(pattern, &condition_type, ctx)
                    .expect("Unification of new_generic with enum cannot fail");

                for (
                    PatternArgument {
                        target,
                        value: pattern,
                        kind,
                    },
                    Parameter {
                        name: _,
                        ty: target_type,
                        no_mangle: _,
                    },
                ) in args.iter().zip(params.0.iter())
                {
                    self.visit_pattern(pattern, ctx, &generic_list)?;
                    let target_type =
                        self.type_var_from_hir(target_type.loc(), target_type, &generic_list)?;

                    let loc = match kind {
                        hir::ArgumentKind::Positional => pattern.loc(),
                        hir::ArgumentKind::Named => pattern.loc(),
                        hir::ArgumentKind::ShortNamed => target.loc(),
                    };

                    self.unify(pattern, &target_type, ctx).into_diagnostic(
                        loc,
                        |d,
                         Tm {
                             e: expected,
                             g: got,
                         }| {
                            d.message(format!(
                                "Argument type mismatch. Expected {expected} got {got}"
                            ))
                            .primary_label(format!("expected {expected}"))
                        },
                    )?;
                }
            }
        }
        Ok(())
    }

    #[trace_typechecker]
    pub fn visit_wal_trace(
        &mut self,
        trace: &Loc<WalTrace>,
        ctx: &Context,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        let WalTrace { clk, rst } = &trace.inner;
        clk.as_ref()
            .map(|x| {
                self.visit_expression(x, ctx, generic_list)?;
                self.unify_expression_generic_error(x, &t_clock(ctx.symtab).at_loc(trace), ctx)
            })
            .transpose()?;
        rst.as_ref()
            .map(|x| {
                self.visit_expression(x, ctx, generic_list)?;
                self.unify_expression_generic_error(x, &t_bool(ctx.symtab).at_loc(trace), ctx)
            })
            .transpose()?;
        Ok(())
    }

    #[trace_typechecker]
    pub fn visit_statement(
        &mut self,
        stmt: &Loc<Statement>,
        ctx: &Context,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        match &stmt.inner {
            Statement::Binding(Binding {
                pattern,
                ty,
                value,
                wal_trace,
            }) => {
                trace!("Visiting `let {} = ..`", pattern.kind);
                self.visit_expression(value, ctx, generic_list)?;

                self.visit_pattern(pattern, ctx, generic_list)?;

                self.unify(&TypedExpression::Id(pattern.id), value, ctx)
                    .into_diagnostic(
                        pattern.loc(),
                        error_pattern_type_mismatch(
                            ty.as_ref().map(|t| t.loc()).unwrap_or_else(|| value.loc()),
                        ),
                    )?;

                if let Some(t) = ty {
                    let tvar = self.type_var_from_hir(t.loc(), t, generic_list)?;
                    self.unify(&TypedExpression::Id(pattern.id), &tvar, ctx)
                        .into_default_diagnostic(value.loc())?;
                }

                wal_trace
                    .as_ref()
                    .map(|wt| self.visit_wal_trace(wt, ctx, generic_list))
                    .transpose()?;

                Ok(())
            }
            Statement::Register(reg) => self.visit_register(reg, ctx, generic_list),
            Statement::Declaration(names) => {
                for name in names {
                    let new_type = self.new_generic_type(name.loc());
                    self.add_equation(TypedExpression::Name(name.clone().inner), new_type);
                }
                Ok(())
            }
            Statement::PipelineRegMarker(extra) => {
                match extra {
                    Some(PipelineRegMarkerExtra::Condition(cond)) => {
                        self.visit_expression(cond, ctx, generic_list)?;
                        self.unify_expression_generic_error(
                            cond,
                            &t_bool(ctx.symtab).at_loc(cond),
                            ctx,
                        )?;
                    }
                    Some(PipelineRegMarkerExtra::Count {
                        count: _,
                        count_typeexpr_id: _,
                    }) => {}
                    None => {}
                }

                let current_stage_depth = self
                    .pipeline_state
                    .clone()
                    .ok_or_else(|| {
                        diag_anyhow!(stmt, "Found a pipeline reg marker in a non-pipeline")
                    })?
                    .current_stage_depth;

                let new_depth = self.new_generic_tlint(stmt.loc());
                let offset = match extra {
                    Some(PipelineRegMarkerExtra::Count {
                        count,
                        count_typeexpr_id,
                    }) => {
                        let var = self.hir_type_expr_to_var(count, generic_list)?;
                        self.add_equation(TypedExpression::Id(*count_typeexpr_id), var.clone());
                        var
                    }
                    Some(PipelineRegMarkerExtra::Condition(_)) | None => {
                        TypeVar::Known(stmt.loc(), KnownType::Integer(1.to_bigint()), vec![])
                    }
                };

                let total_depth = ConstraintExpr::Sum(
                    Box::new(ConstraintExpr::Var(offset)),
                    Box::new(ConstraintExpr::Var(current_stage_depth)),
                );
                self.pipeline_state
                    .as_mut()
                    .expect("Expected to have a pipeline state")
                    .current_stage_depth = new_depth.clone();

                self.add_constraint(
                    new_depth.clone(),
                    total_depth,
                    stmt.loc(),
                    &new_depth,
                    ConstraintSource::PipelineRegCount {
                        reg: stmt.loc(),
                        total: self.get_pipeline_state(stmt)?.total_depth.loc(),
                    },
                );

                Ok(())
            }
            Statement::Label(name) => {
                let key = TypedExpression::Name(name.inner.clone());
                let var = if !self.equations.contains_key(&key) {
                    let var = self.new_generic_tlint(name.loc());
                    self.trace_stack.push(TraceStackEntry::AddingPipelineLabel(
                        name.inner.clone(),
                        var.clone(),
                    ));
                    self.add_equation(key.clone(), var.clone());
                    var
                } else {
                    let var = self.equations.get(&key).unwrap().clone();
                    self.trace_stack
                        .push(TraceStackEntry::RecoveringPipelineLabel(
                            name.inner.clone(),
                            var.clone(),
                        ));
                    var
                };
                // Safe unwrap, unifying with a fresh var
                self.unify(
                    &var,
                    &self.get_pipeline_state(name)?.current_stage_depth.clone(),
                    ctx,
                )
                .unwrap();
                Ok(())
            }
            Statement::WalSuffixed { .. } => Ok(()),
            Statement::Assert(expr) => {
                self.visit_expression(expr, ctx, generic_list)?;
                self.unify_expression_generic_error(expr, &t_bool(ctx.symtab).at_loc(stmt), ctx)?;
                Ok(())
            }
            Statement::Set { target, value } => {
                self.visit_expression(target, ctx, generic_list)?;
                self.visit_expression(value, ctx, generic_list)?;

                let inner_type = self.new_generic_type(value.loc());
                let outer_type = TypeVar::backward(stmt.loc(), inner_type.clone());
                self.unify_expression_generic_error(target, &outer_type, ctx)?;
                self.unify_expression_generic_error(value, &inner_type, ctx)?;

                Ok(())
            }
        }
    }

    #[trace_typechecker]
    pub fn visit_register(
        &mut self,
        reg: &Register,
        ctx: &Context,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        self.visit_pattern(&reg.pattern, ctx, generic_list)?;

        let type_spec_type = match &reg.value_type {
            Some(t) => Some(self.type_var_from_hir(t.loc(), t, generic_list)?.at_loc(t)),
            None => None,
        };

        // We need to do this before visiting value, in case it constrains the
        // type of the identifiers in the pattern
        if let Some(tvar) = &type_spec_type {
            self.unify(&TypedExpression::Id(reg.pattern.id), tvar, ctx)
                .into_diagnostic_no_expected_source(
                    reg.pattern.loc(),
                    error_pattern_type_mismatch(tvar.loc()),
                )?;
        }

        self.visit_expression(&reg.clock, ctx, generic_list)?;
        self.visit_expression(&reg.value, ctx, generic_list)?;

        if let Some(tvar) = &type_spec_type {
            self.unify(&reg.value, tvar, ctx)
                .into_default_diagnostic(reg.value.loc())?;
        }

        if let Some((rst_cond, rst_value)) = &reg.reset {
            self.visit_expression(rst_cond, ctx, generic_list)?;
            self.visit_expression(rst_value, ctx, generic_list)?;
            // Ensure cond is a boolean
            self.unify(&rst_cond.inner, &t_bool(ctx.symtab).at_loc(rst_cond), ctx)
                .into_diagnostic(
                    rst_cond.loc(),
                    |diag,
                     Tm {
                         g: got,
                         e: _expected,
                     }| {
                        diag.message(format!(
                            "Register reset condition must be a bool, got {got}"
                        ))
                        .primary_label("expected bool")
                    },
                )?;

            // Ensure the reset value has the same type as the register itself
            self.unify(&rst_value.inner, &reg.value.inner, ctx)
                .into_diagnostic(
                    rst_value.loc(),
                    |diag,
                     Tm {
                         g: got,
                         e: expected,
                     }| {
                        diag.message(format!(
                            "Register reset value mismatch. Expected {expected} got {got}"
                        ))
                        .primary_label(format!("expected {expected}"))
                        .secondary_label(&reg.pattern, format!("because this has type {expected}"))
                    },
                )?;
        }

        if let Some(initial) = &reg.initial {
            self.visit_expression(initial, ctx, generic_list)?;

            self.unify(&initial.inner, &reg.value.inner, ctx)
                .into_diagnostic(
                    initial.loc(),
                    |diag,
                     Tm {
                         g: got,
                         e: expected,
                     }| {
                        diag.message(format!(
                            "Register initial value mismatch. Expected {expected} got {got}"
                        ))
                        .primary_label(format!("expected {expected}, got {got}"))
                        .secondary_label(&reg.pattern, format!("because this has type {got}"))
                    },
                )?;
        }

        self.unify(&reg.clock, &t_clock(ctx.symtab).at_loc(&reg.clock), ctx)
            .into_diagnostic(
                reg.clock.loc(),
                |diag,
                 Tm {
                     g: got,
                     e: _expected,
                 }| {
                    diag.message(format!("Expected clock, got {got}"))
                        .primary_label("expected clock")
                },
            )?;

        self.unify(&TypedExpression::Id(reg.pattern.id), &reg.value, ctx)
            .into_diagnostic(
                reg.pattern.loc(),
                error_pattern_type_mismatch(reg.value.loc()),
            )?;

        Ok(())
    }

    #[trace_typechecker]
    pub fn visit_trait_spec(
        &mut self,
        trait_spec: &Loc<TraitSpec>,
        generic_list: &GenericListToken,
    ) -> Result<Loc<TraitReq>> {
        let type_params = if let Some(type_params) = &trait_spec.inner.type_params {
            type_params
                .inner
                .iter()
                .map(|te| self.hir_type_expr_to_var(te, generic_list))
                .collect::<Result<_>>()?
        } else {
            vec![]
        };

        Ok(TraitReq {
            name: trait_spec.name.clone(),
            type_params,
        }
        .at_loc(trait_spec))
    }

    #[trace_typechecker]
    pub fn visit_trait_bounds(
        &mut self,
        target: &Loc<NameID>,
        traits: &[Loc<TraitSpec>],
        generic_list: &GenericListToken,
    ) -> Result<()> {
        let trait_reqs = traits
            .iter()
            .map(|spec| self.visit_trait_spec(spec, generic_list))
            .collect::<Result<BTreeSet<_>>>()?
            .into_iter()
            .collect_vec();

        if !trait_reqs.is_empty() {
            let trait_list = TraitList::from_vec(trait_reqs);

            let generic_list = self.generic_lists.get_mut(generic_list).unwrap();

            let Some(tvar) = generic_list.get(&target.inner) else {
                return Err(Diagnostic::bug(
                    target,
                    "Couldn't find generic from where clause in generic list",
                )
                .primary_label(format!(
                    "Generic type {} not found in generic list",
                    target.inner
                )));
            };

            self.trace_stack.push(TraceStackEntry::AddingTraitBounds(
                tvar.clone(),
                trait_list.clone(),
            ));

            let TypeVar::Unknown(loc, id, old_trait_list, MetaType::Type) = tvar else {
                return Err(Diagnostic::bug(
                    target,
                    "Trait bounds on known type or type-level integer",
                )
                .primary_label(format!(
                    "Trait bounds on {}, which should've been caught in ast-lowering",
                    target.inner
                )));
            };

            let new_tvar = TypeVar::Unknown(
                *loc,
                *id,
                old_trait_list.clone().extend(trait_list),
                MetaType::Type,
            );

            trace!(
                "Adding trait bound {} on type {}",
                new_tvar.display_with_meta(true),
                target.inner
            );

            generic_list.insert(target.inner.clone(), new_tvar);
        }

        Ok(())
    }

    pub fn visit_const_generic_with_id(
        &mut self,
        gen: &Loc<ConstGenericWithId>,
        generic_list_token: &GenericListToken,
        constraint_source: ConstraintSource,
        ctx: &Context,
    ) -> Result<TypeVar> {
        let var = match &gen.inner.inner {
            ConstGeneric::Name(name) => {
                let ty = &ctx.symtab.type_symbol_by_id(&name);
                match &ty.inner {
                    TypeSymbol::Declared(_, _) => {
                        return Err(Diagnostic::error(
                            name,
                            "{type_decl_kind} cannot be used in a const generic expression",
                        )
                        .primary_label("Type in  const generic")
                        .secondary_label(ty, "{name} is declared here"))
                    }
                    TypeSymbol::GenericArg { .. } | TypeSymbol::GenericMeta(MetaType::Type) => {
                        return Err(Diagnostic::error(
                            name,
                            "Generic types cannot be used in const generic expressions",
                        )
                        .primary_label("Type in  const generic")
                        .secondary_label(ty, "{name} is declared here")
                        .span_suggest_insert_before(
                            "Consider making this a value",
                            ty.loc(),
                            "#uint ",
                        ))
                    }
                    TypeSymbol::GenericMeta(MetaType::Number) => {
                        self.new_generic_tlnumber(gen.loc())
                    }
                    TypeSymbol::GenericMeta(MetaType::Int) => self.new_generic_tlint(gen.loc()),
                    TypeSymbol::GenericMeta(MetaType::Uint) => self.new_generic_tluint(gen.loc()),
                    TypeSymbol::GenericMeta(MetaType::Bool) => self.new_generic_tlbool(gen.loc()),
                    TypeSymbol::GenericMeta(MetaType::Any) => {
                        diag_bail!(gen, "Found any meta type")
                    }
                    TypeSymbol::Alias(_) => {
                        return Err(Diagnostic::error(
                            gen,
                            "Aliases are not currently supported in const generics",
                        )
                        .secondary_label(ty, "Alias defined here"))
                    }
                }
            }
            ConstGeneric::Const(_)
            | ConstGeneric::Add(_, _)
            | ConstGeneric::Sub(_, _)
            | ConstGeneric::Mul(_, _)
            | ConstGeneric::UintBitsToFit(_) => self.new_generic_tlnumber(gen.loc()),
            ConstGeneric::Eq(_, _) | ConstGeneric::NotEq(_, _) => {
                self.new_generic_tlbool(gen.loc())
            }
        };
        let constraint = self.visit_const_generic(&gen.inner.inner, generic_list_token)?;
        self.add_equation(TypedExpression::Id(gen.id), var.clone());
        self.add_constraint(var.clone(), constraint, gen.loc(), &var, constraint_source);
        Ok(var)
    }

    #[trace_typechecker]
    pub fn visit_const_generic(
        &self,
        constraint: &ConstGeneric,
        generic_list: &GenericListToken,
    ) -> Result<ConstraintExpr> {
        let constraint = match constraint {
            ConstGeneric::Name(n) => {
                let var = self.get_generic_list(generic_list).get(n).ok_or_else(|| {
                    Diagnostic::bug(n, "Found non-generic argument in where clause")
                })?;
                ConstraintExpr::Var(self.check_var_for_replacement(var.clone()))
            }
            ConstGeneric::Const(val) => ConstraintExpr::Integer(val.clone()),
            ConstGeneric::Add(lhs, rhs) => ConstraintExpr::Sum(
                Box::new(self.visit_const_generic(lhs, generic_list)?),
                Box::new(self.visit_const_generic(rhs, generic_list)?),
            ),
            ConstGeneric::Sub(lhs, rhs) => ConstraintExpr::Difference(
                Box::new(self.visit_const_generic(lhs, generic_list)?),
                Box::new(self.visit_const_generic(rhs, generic_list)?),
            ),
            ConstGeneric::Mul(lhs, rhs) => ConstraintExpr::Product(
                Box::new(self.visit_const_generic(lhs, generic_list)?),
                Box::new(self.visit_const_generic(rhs, generic_list)?),
            ),
            ConstGeneric::Eq(lhs, rhs) => ConstraintExpr::Eq(
                Box::new(self.visit_const_generic(lhs, generic_list)?),
                Box::new(self.visit_const_generic(rhs, generic_list)?),
            ),
            ConstGeneric::NotEq(lhs, rhs) => ConstraintExpr::NotEq(
                Box::new(self.visit_const_generic(lhs, generic_list)?),
                Box::new(self.visit_const_generic(rhs, generic_list)?),
            ),
            ConstGeneric::UintBitsToFit(a) => ConstraintExpr::UintBitsToRepresent(Box::new(
                self.visit_const_generic(a, generic_list)?,
            )),
        };
        Ok(constraint)
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
            if new == &var {
                panic!("Type var {new} has been replaced by itself");
            }
            // We need to do this recursively if we have multiple long lived vars
            return self.check_var_for_replacement(new.clone());
        };
        match var {
            TypeVar::Known(loc, base, params) => TypeVar::Known(
                loc,
                base,
                params
                    .into_iter()
                    .map(|p| self.check_var_for_replacement(p))
                    .collect(),
            ),
            TypeVar::Unknown(loc, id, traits, meta) => TypeVar::Unknown(
                loc,
                id,
                TraitList::from_vec(
                    traits
                        .inner
                        .iter()
                        .map(|t| {
                            TraitReq {
                                name: t.inner.name.clone(),
                                type_params: t
                                    .inner
                                    .type_params
                                    .iter()
                                    .map(|v| self.check_var_for_replacement(v.clone()))
                                    .collect(),
                            }
                            .at_loc(t)
                        })
                        .collect(),
                ),
                meta,
            ),
        }
    }

    fn check_expr_for_replacement(&self, val: ConstraintExpr) -> ConstraintExpr {
        // FIXME: AS this gets more complicated, consider rewriting it to clone `val` and
        // then just replacing the inner values, this is error prone when copy pasting
        match val {
            v @ ConstraintExpr::Integer(_) => v,
            v @ ConstraintExpr::Bool(_) => v,
            ConstraintExpr::Var(var) => ConstraintExpr::Var(self.check_var_for_replacement(var)),
            ConstraintExpr::Sum(lhs, rhs) => ConstraintExpr::Sum(
                Box::new(self.check_expr_for_replacement(*lhs)),
                Box::new(self.check_expr_for_replacement(*rhs)),
            ),
            ConstraintExpr::Difference(lhs, rhs) => ConstraintExpr::Difference(
                Box::new(self.check_expr_for_replacement(*lhs)),
                Box::new(self.check_expr_for_replacement(*rhs)),
            ),
            ConstraintExpr::Product(lhs, rhs) => ConstraintExpr::Product(
                Box::new(self.check_expr_for_replacement(*lhs)),
                Box::new(self.check_expr_for_replacement(*rhs)),
            ),
            ConstraintExpr::Eq(lhs, rhs) => ConstraintExpr::Eq(
                Box::new(self.check_expr_for_replacement(*lhs)),
                Box::new(self.check_expr_for_replacement(*rhs)),
            ),
            ConstraintExpr::NotEq(lhs, rhs) => ConstraintExpr::NotEq(
                Box::new(self.check_expr_for_replacement(*lhs)),
                Box::new(self.check_expr_for_replacement(*rhs)),
            ),
            ConstraintExpr::Sub(inner) => {
                ConstraintExpr::Sub(Box::new(self.check_expr_for_replacement(*inner)))
            }
            ConstraintExpr::UintBitsToRepresent(inner) => ConstraintExpr::UintBitsToRepresent(
                Box::new(self.check_expr_for_replacement(*inner)),
            ),
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
            println!("{}", format_trace_stack(self));
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

        self.trace_stack.push(TraceStackEntry::AddingConstraint(
            lhs.clone(),
            rhs.inner.clone(),
        ));

        self.constraints.add_int_constraint(lhs, rhs);
    }

    fn add_requirement(&mut self, requirement: Requirement) {
        macro_rules! replace {
            ($name:expr) => {
                self.check_var_for_replacement($name.inner.clone())
                    .at_loc(&$name)
            };
        }

        let replaced = match requirement {
            Requirement::HasField {
                target_type,
                field,
                expr,
            } => Requirement::HasField {
                field,
                target_type: replace!(target_type),
                expr: replace!(expr),
            },
            Requirement::HasMethod {
                expr_id,
                target_type,
                trait_list,
                method,
                expr,
                args,
                turbofish,
                prev_generic_list,
                call_kind,
            } => Requirement::HasMethod {
                expr_id,
                target_type: replace!(target_type),
                trait_list,
                method,
                expr: replace!(expr),
                args,
                turbofish,
                prev_generic_list,
                call_kind,
            },
            Requirement::FitsIntLiteral { value, target_type } => Requirement::FitsIntLiteral {
                value: match value {
                    ConstantInt::Generic(var) => {
                        ConstantInt::Generic(replace!(var.clone().nowhere()).inner)
                    }
                    lit @ ConstantInt::Literal(_) => lit,
                },
                target_type: replace!(target_type),
            },
            Requirement::ValidPipelineOffset {
                definition_depth,
                current_stage,
                reference_offset,
            } => Requirement::ValidPipelineOffset {
                definition_depth: replace!(definition_depth),
                current_stage: replace!(current_stage),
                reference_offset: replace!(reference_offset),
            },
            Requirement::RangeIndexInArray { index, size } => Requirement::RangeIndexInArray {
                index: replace!(index),
                size: replace!(size),
            },
            Requirement::RangeIndexEndAfterStart { expr, start, end } => {
                Requirement::RangeIndexEndAfterStart {
                    expr,
                    start: replace!(start),
                    end: replace!(end),
                }
            }
            Requirement::PositivePipelineDepth { depth } => Requirement::PositivePipelineDepth {
                depth: replace!(depth),
            },
            Requirement::ArrayIndexeeIsNonZero {
                index,
                array,
                array_size,
            } => Requirement::ArrayIndexeeIsNonZero {
                index,
                array: replace!(array),
                array_size: replace!(array_size),
            },
            Requirement::SharedBase(types) => {
                Requirement::SharedBase(types.iter().map(|ty| replace!(ty)).collect())
            }
        };

        self.trace_stack
            .push(TraceStackEntry::AddRequirement(replaced.clone()));
        self.requirements.push(replaced)
    }

    /// Performs unification but does not update constraints. This is done to avoid
    /// updating constraints more often than necessary. Technically, constraints can
    /// be updated even less often, but `unify` is a pretty natural point to do so.

    fn unify_inner(
        &mut self,
        e1: &impl HasType,
        e2: &impl HasType,
        ctx: &Context,
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
            () => {{
                self.trace_stack
                    .push(TraceStackEntry::Message("Produced error".to_string()));
                UnificationError::Normal(Tm {
                    g: UnificationTrace::new(self.check_var_for_replacement(v1)),
                    e: UnificationTrace::new(self.check_var_for_replacement(v2)),
                })
            }};
        }
        macro_rules! meta_err_producer {
            () => {{
                self.trace_stack
                    .push(TraceStackEntry::Message("Produced error".to_string()));
                UnificationError::MetaMismatch(Tm {
                    g: UnificationTrace::new(self.check_var_for_replacement(v1)),
                    e: UnificationTrace::new(self.check_var_for_replacement(v2)),
                })
            }};
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
                try_with_context!($value, v1, v2)
            };
            ($value: expr, $v1:expr, $v2:expr) => {
                match $value {
                    Ok(result) => result,
                    e => {
                        self.trace_stack
                            .push(TraceStackEntry::Message("Adding context".to_string()));
                        return e.add_context($v1.clone(), $v2.clone());
                    }
                }
            };
        }

        macro_rules! unify_params_ {
            ($p1:expr, $p2:expr) => {
                if $p1.len() != $p2.len() {
                    return Err(err_producer!());
                }

                for (t1, t2) in $p1.iter().zip($p2.iter()) {
                    try_with_context!(self.unify_inner(t1, t2, ctx));
                }
            };
        }

        // Figure out the most general type, and take note if we need to
        // do any replacement of the types in the rest of the state
        let result = match (&v1, &v2) {
            (TypeVar::Known(_, t1, p1), TypeVar::Known(_, t2, p2)) => {
                macro_rules! unify_params {
                    () => {
                        unify_params_!(p1, p2)
                    };
                }
                match (t1, t2) {
                    (KnownType::Integer(val1), KnownType::Integer(val2)) => {
                        unify_if!(val1 == val2, v1, vec![])
                    }
                    (KnownType::Named(n1), KnownType::Named(n2)) => {
                        match (
                            &ctx.symtab.type_symbol_by_id(n1).inner,
                            &ctx.symtab.type_symbol_by_id(n2).inner,
                        ) {
                            (TypeSymbol::Declared(_, _), TypeSymbol::Declared(_, _)) => {
                                if n1 != n2 {
                                    return Err(err_producer!());
                                }

                                unify_params!();
                                let new_ts1 = ctx.symtab.type_symbol_by_id(n1).inner;
                                let new_ts2 = ctx.symtab.type_symbol_by_id(n2).inner;
                                let new_v1 = e1
                                    .get_type(self)
                                    .expect("Tried to unify types but the lhs was not found");
                                unify_if!(
                                    new_ts1 == new_ts2,
                                    self.check_var_for_replacement(new_v1),
                                    vec![]
                                )
                            }
                            (TypeSymbol::Declared(_, _), TypeSymbol::GenericArg { traits }) => {
                                if !traits.is_empty() {
                                    todo!("Implement trait unifictaion");
                                }
                                Ok((v1, vec![v2]))
                            }
                            (TypeSymbol::GenericArg { traits }, TypeSymbol::Declared(_, _)) => {
                                if !traits.is_empty() {
                                    todo!("Implement trait unifictaion");
                                }
                                Ok((v2, vec![v1]))
                            }
                            (
                                TypeSymbol::GenericArg { traits: ltraits },
                                TypeSymbol::GenericArg { traits: rtraits },
                            ) => {
                                if !ltraits.is_empty() || !rtraits.is_empty() {
                                    todo!("Implement trait unifictaion");
                                }
                                Ok((v1, vec![v2]))
                            }
                            (TypeSymbol::Declared(_, _), TypeSymbol::GenericMeta(_)) => todo!(),
                            (TypeSymbol::GenericArg { traits: _ }, TypeSymbol::GenericMeta(_)) => {
                                todo!()
                            }
                            (TypeSymbol::GenericMeta(_), TypeSymbol::Declared(_, _)) => todo!(),
                            (TypeSymbol::GenericMeta(_), TypeSymbol::GenericArg { traits: _ }) => {
                                todo!()
                            }
                            (TypeSymbol::Alias(_), _) | (_, TypeSymbol::Alias(_)) => {
                                return Err(UnificationError::Specific(Diagnostic::bug(
                                    ().nowhere(),
                                    "Encountered a raw type alias during unification",
                                )))
                            }
                            (TypeSymbol::GenericMeta(_), TypeSymbol::GenericMeta(_)) => todo!(),
                        }
                    }
                    (KnownType::Array, KnownType::Array)
                    | (KnownType::Tuple, KnownType::Tuple)
                    | (KnownType::Wire, KnownType::Wire)
                    | (KnownType::Inverted, KnownType::Inverted) => {
                        unify_params!();
                        // Note, replacements should only occur when a variable goes from Unknown
                        // to Known, not when the base is the same. Replacements take care
                        // of parameters. Therefore, None is returned here
                        Ok((self.check_var_for_replacement(v2), vec![]))
                    }
                    (_, _) => Err(err_producer!()),
                }
            }
            // Unknown with unknown requires merging traits
            (
                TypeVar::Unknown(loc1, _, traits1, meta1),
                TypeVar::Unknown(loc2, _, traits2, meta2),
            ) => {
                let new_loc = if meta1.is_more_concrete_than(meta2) {
                    loc1
                } else {
                    loc2
                };
                let new_t = match unify_meta(meta1, meta2) {
                    Some(meta @ MetaType::Any) | Some(meta @ MetaType::Number) => {
                        if traits1.inner.is_empty() || traits2.inner.is_empty() {
                            panic!("Inferred an any meta-type with traits",);
                        }
                        self.new_generic_with_meta(*loc1, meta)
                    }
                    Some(MetaType::Type) => {
                        let new_trait_names = traits1
                            .inner
                            .iter()
                            .chain(traits2.inner.iter())
                            .map(|t| t.name.clone())
                            .collect::<BTreeSet<_>>()
                            .into_iter()
                            .collect::<Vec<_>>();

                        let new_traits = new_trait_names
                            .iter()
                            .map(
                                |name| match (traits1.get_trait(name), traits2.get_trait(name)) {
                                    (Some(req1), Some(req2)) => {
                                        let new_params = req1
                                            .inner
                                            .type_params
                                            .iter()
                                            .zip(req2.inner.type_params.iter())
                                            .map(|(p1, p2)| self.unify(p1, p2, ctx))
                                            .collect::<std::result::Result<_, UnificationError>>(
                                            )?;

                                        Ok(TraitReq {
                                            name: name.clone(),
                                            type_params: new_params,
                                        }
                                        .at_loc(req1))
                                    }
                                    (Some(t), None) => Ok(t.clone()),
                                    (None, Some(t)) => Ok(t.clone()),
                                    (None, None) => panic!("Found a trait but neither side has it"),
                                },
                            )
                            .collect::<std::result::Result<Vec<_>, UnificationError>>()?;

                        self.new_generic_with_traits(*new_loc, TraitList::from_vec(new_traits))
                    }
                    Some(MetaType::Int) => self.new_generic_tlint(*new_loc),
                    Some(MetaType::Uint) => self.new_generic_tluint(*new_loc),
                    Some(MetaType::Bool) => self.new_generic_tlbool(*new_loc),
                    None => return Err(meta_err_producer!()),
                };
                Ok((new_t, vec![v1, v2]))
            }
            (
                other @ TypeVar::Known(loc, base, params),
                uk @ TypeVar::Unknown(ukloc, _, traits, meta),
            )
            | (
                uk @ TypeVar::Unknown(ukloc, _, traits, meta),
                other @ TypeVar::Known(loc, base, params),
            ) => {
                let trait_is_expected = match (&v1, &v2) {
                    (TypeVar::Known(_, _, _), _) => true,
                    _ => false,
                };

                self.ensure_impls(other, traits, trait_is_expected, ukloc, ctx)?;

                let mut new_params = params.clone();
                for t in &traits.inner {
                    if !t.type_params.is_empty() {
                        if t.type_params.len() != params.len() {
                            return Err(err_producer!());
                        }

                        // If we don't cheat a bit, we'll get bad error messages in this case when
                        // we unify, for example, `Number<10>` with `uint<9>`. Since we know the
                        // outer types match already, we'll create a fake type for the lhs where
                        // we preemptively crate uint<T>
                        let fake_type = TypeVar::Known(*loc, base.clone(), t.type_params.clone());

                        new_params = t
                            .type_params
                            .iter()
                            .zip(new_params.iter())
                            .map(|(t1, t2)| {
                                Ok(try_with_context!(
                                    self.unify_inner(t1, t2, ctx),
                                    fake_type,
                                    other
                                ))
                            })
                            .collect::<std::result::Result<_, _>>()?;
                    }
                }

                match (base, meta) {
                    // Any matches all types
                    (_, MetaType::Any)
                    // All types are types
                    | (KnownType::Named(_), MetaType::Type)
                    | (KnownType::Tuple, MetaType::Type)
                    | (KnownType::Array, MetaType::Type)
                    | (KnownType::Wire, MetaType::Type)
                    | (KnownType::Bool(_), MetaType::Bool)
                    | (KnownType::Inverted, MetaType::Type)
                    // Integers match ints and numbers
                    | (KnownType::Integer(_), MetaType::Int)
                    | (KnownType::Integer(_), MetaType::Number)
                    => {
                        let new = TypeVar::Known(*loc, base.clone(), new_params);

                        Ok((new, vec![uk.clone()]))
                    },
                    // Integers match uints but only if the concrete integer is >= 0
                    (KnownType::Integer(val), MetaType::Uint)
                    => {
                        if val < &0.to_bigint() {
                            Err(meta_err_producer!())
                        } else {
                            let new = TypeVar::Known(*loc, base.clone(), new_params);

                            Ok((new, vec![uk.clone()]))
                        }
                    },

                    // Integer with type
                    (KnownType::Integer(_), MetaType::Type) => Err(meta_err_producer!()),

                    // Bools only unify with any or bool
                    (_, MetaType::Bool) => Err(meta_err_producer!()),
                    (KnownType::Bool(_), _) => Err(meta_err_producer!()),

                    // Type with integer
                    (KnownType::Named(_), MetaType::Int | MetaType::Number | MetaType::Uint)
                    | (KnownType::Tuple, MetaType::Int | MetaType::Uint | MetaType::Number)
                    | (KnownType::Array, MetaType::Int | MetaType::Uint | MetaType::Number)
                    | (KnownType::Wire, MetaType::Int | MetaType::Uint | MetaType::Number)
                    | (KnownType::Inverted, MetaType::Int | MetaType::Uint | MetaType::Number)
                    => Err(meta_err_producer!())
                }
            }
        };

        let (new_type, replaced_types) = result?;

        self.trace_stack.push(TraceStackEntry::Unified(
            v1cpy,
            v2cpy,
            new_type.clone(),
            replaced_types.clone(),
        ));

        for replaced_type in replaced_types {
            self.replacements
                .insert(replaced_type.clone(), new_type.clone());

            for rhs in self.equations.values_mut() {
                TypeState::replace_type_var(rhs, &replaced_type, &new_type)
            }
            for generic_list in &mut self.generic_lists.values_mut() {
                for (_, lhs) in generic_list.iter_mut() {
                    TypeState::replace_type_var(lhs, &replaced_type, &new_type)
                }
            }
            for traits in &mut self.trait_impls.inner.values_mut() {
                for TraitImpl {
                    name: _,
                    type_params,
                    impl_block: _,
                } in traits.iter_mut()
                {
                    for tvar in type_params.iter_mut() {
                        TypeState::replace_type_var(tvar, &replaced_type, &new_type);
                    }
                }
            }
            for requirement in &mut self.requirements {
                requirement.replace_type_var(&replaced_type, &new_type)
            }

            if let Some(PipelineState {
                current_stage_depth,
                pipeline_loc: _,
                total_depth,
            }) = &mut self.pipeline_state
            {
                TypeState::replace_type_var(current_stage_depth, &replaced_type, &new_type);
                TypeState::replace_type_var(&mut total_depth.inner, &replaced_type, &new_type);
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
        ctx: &Context,
    ) -> std::result::Result<TypeVar, UnificationError> {
        let new_type = self.unify_inner(e1, e2, ctx)?;

        // With replacement done, some of our constraints may have been updated to provide
        // more type inference information. Try to do unification of those new constraints too
        loop {
            trace!("Updating constraints");
            let new_info = self.constraints.update_type_level_value_constraints();

            if new_info.is_empty() {
                break;
            }

            for constraint in new_info {
                trace!(
                    "Constraint replaces {} with {:?}",
                    constraint.inner.0,
                    constraint.inner.1
                );

                let ((var, replacement), loc) = constraint.split_loc();

                self.trace_stack
                    .push(TraceStackEntry::InferringFromConstraints(
                        var.clone(),
                        replacement.val.clone(),
                    ));

                let var = self.check_var_for_replacement(var);

                // NOTE: safe unwrap. We already checked the constraint above
                let expected_type = replacement.val;
                let result = self.unify_inner(&expected_type.clone().at_loc(&loc), &var, ctx);
                let is_meta_error = matches!(result, Err(UnificationError::MetaMismatch { .. }));
                match result {
                    Ok(_) => {}
                    Err(UnificationError::Normal(Tm { mut e, mut g }))
                    | Err(UnificationError::MetaMismatch(Tm { mut e, mut g })) => {
                        let mut source_lhs = replacement.context.inside.clone();
                        Self::replace_type_var(
                            &mut source_lhs,
                            &replacement.context.replaces,
                            e.outer(),
                        );
                        let mut source_rhs = replacement.context.inside.clone();
                        Self::replace_type_var(
                            &mut source_rhs,
                            &replacement.context.replaces,
                            g.outer(),
                        );
                        e.inside.replace(source_lhs);
                        g.inside.replace(source_rhs);
                        return Err(UnificationError::FromConstraints {
                            got: g,
                            expected: e,
                            source: replacement.context.source,
                            loc,
                            is_meta_error,
                        });
                    }
                    Err(
                        e @ UnificationError::FromConstraints { .. }
                        | e @ UnificationError::Specific { .. }
                        | e @ UnificationError::UnsatisfiedTraits { .. },
                    ) => return Err(e),
                };
            }
        }

        Ok(new_type)
    }

    fn ensure_impls(
        &mut self,
        var: &TypeVar,
        traits: &TraitList,
        trait_is_expected: bool,
        trait_list_loc: &Loc<()>,
        ctx: &Context,
    ) -> std::result::Result<(), UnificationError> {
        self.trace_stack.push(TraceStackEntry::EnsuringImpls(
            var.clone(),
            traits.clone(),
            trait_is_expected,
        ));

        let number = ctx
            .symtab
            .lookup_trait(&Path::from_strs(&["Number"]).nowhere())
            .expect("Did not find number in symtab")
            .0;

        macro_rules! error_producer {
            ($required_traits:expr) => {
                if trait_is_expected {
                    if $required_traits.inner.len() == 1
                        && $required_traits
                            .get_trait(&TraitName::Named(number.clone().nowhere()))
                            .is_some()
                    {
                        Err(UnificationError::Normal(Tm {
                            e: UnificationTrace::new(
                                self.new_generic_with_traits(*trait_list_loc, $required_traits),
                            ),
                            g: UnificationTrace::new(var.clone()),
                        }))
                    } else {
                        Err(UnificationError::UnsatisfiedTraits {
                            var: var.clone(),
                            traits: $required_traits.inner,
                            target_loc: trait_list_loc.clone(),
                        })
                    }
                } else {
                    Err(UnificationError::Normal(Tm {
                        e: UnificationTrace::new(var.clone()),
                        g: UnificationTrace::new(
                            self.new_generic_with_traits(*trait_list_loc, $required_traits),
                        ),
                    }))
                }
            };
        }

        match var {
            TypeVar::Known(_, known, _) if known.into_impl_target().is_some() => {
                let Some(target) = known.into_impl_target() else {
                    unreachable!()
                };

                let unsatisfied = traits
                    .inner
                    .iter()
                    .filter(|trait_req| {
                        // Number is special cased for now because we can't impl traits
                        // on generic types
                        if trait_req.name.name_loc().is_some_and(|n| n.inner == number) {
                            let int_type = &ctx
                                .symtab
                                .lookup_type_symbol(&Path::from_strs(&["int"]).nowhere())
                                .expect("The type int was not in the symtab")
                                .0;
                            let uint_type = &ctx
                                .symtab
                                .lookup_type_symbol(&Path::from_strs(&["uint"]).nowhere())
                                .expect("The type uint was not in the symtab")
                                .0;

                            !(target == ImplTarget::Named(int_type.clone())
                                || target == ImplTarget::Named(uint_type.clone()))
                        } else {
                            if let Some(impld) = self.trait_impls.inner.get(&target) {
                                !impld.iter().any(|trait_impl| {
                                    trait_impl.name == trait_req.name
                                        && trait_impl.type_params == trait_req.type_params
                                })
                            } else {
                                true
                            }
                        }
                    })
                    .cloned()
                    .collect::<Vec<_>>();

                if unsatisfied.is_empty() {
                    Ok(())
                } else {
                    error_producer!(TraitList::from_vec(unsatisfied.clone()))
                }
            }
            TypeVar::Unknown(_, _, _, _) => {
                panic!("running ensure_impls on an unknown type")
            }
            _ => {
                if traits.inner.is_empty() {
                    Ok(())
                } else {
                    error_producer!(traits.clone())
                }
            }
        }
    }

    fn replace_type_var(in_var: &mut TypeVar, from: &TypeVar, replacement: &TypeVar) {
        // First, do recursive replacement
        match in_var {
            TypeVar::Known(_, _, params) => {
                for param in params {
                    Self::replace_type_var(param, from, replacement)
                }
            }
            TypeVar::Unknown(_, _, traits, _) => {
                for t in traits.inner.iter_mut() {
                    for param in t.type_params.iter_mut() {
                        Self::replace_type_var(param, from, replacement)
                    }
                }
            }
        }

        let is_same = match (&in_var, &from) {
            // Traits do not matter for comparison
            (TypeVar::Unknown(_, id1, _, _), TypeVar::Unknown(_, id2, _, _)) => id1 == id2,
            (l, r) => l == r,
        };

        if is_same {
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
            ConstraintExpr::Bool(_) => {}
            ConstraintExpr::Var(v) => {
                Self::replace_type_var(v, from, replacement);

                match v {
                    TypeVar::Known(_, KnownType::Integer(val), _) => {
                        *in_constraint = ConstraintExpr::Integer(val.clone())
                    }
                    _ => {}
                }
            }
            ConstraintExpr::Sum(lhs, rhs) => {
                Self::replace_type_var_in_constraint_expr(lhs, from, replacement);
                Self::replace_type_var_in_constraint_expr(rhs, from, replacement);
            }
            ConstraintExpr::Difference(lhs, rhs) => {
                Self::replace_type_var_in_constraint_expr(lhs, from, replacement);
                Self::replace_type_var_in_constraint_expr(rhs, from, replacement);
            }
            ConstraintExpr::Product(lhs, rhs) => {
                Self::replace_type_var_in_constraint_expr(lhs, from, replacement);
                Self::replace_type_var_in_constraint_expr(rhs, from, replacement);
            }
            ConstraintExpr::Eq(lhs, rhs) => {
                Self::replace_type_var_in_constraint_expr(lhs, from, replacement);
                Self::replace_type_var_in_constraint_expr(rhs, from, replacement);
            }
            ConstraintExpr::NotEq(lhs, rhs) => {
                Self::replace_type_var_in_constraint_expr(lhs, from, replacement);
                Self::replace_type_var_in_constraint_expr(rhs, from, replacement);
            }
            ConstraintExpr::Sub(i) | ConstraintExpr::UintBitsToRepresent(i) => {
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
        // is performed when reporting the error
        // Self::replace_type_var(&mut in_constraint.from, from, replacement);
    }

    pub fn unify_expression_generic_error(
        &mut self,
        expr: &Loc<Expression>,
        other: &impl HasType,
        ctx: &Context,
    ) -> Result<TypeVar> {
        self.unify(&expr.inner, other, ctx)
            .into_default_diagnostic(expr.loc())
    }

    pub fn check_requirements(&mut self, ctx: &Context) -> Result<()> {
        // Once we are done type checking the rest of the entity, check all requirements
        loop {
            // Walk through all the requirements, checking each one. If the requirement
            // is still undetermined, take note to retain that id, otherwise store the
            // replacement to be performed
            let (retain, replacements_option): (Vec<_>, Vec<_>) = self
                .requirements
                .clone()
                .iter()
                .map(|req| match req.check(self, ctx)? {
                    requirements::RequirementResult::NoChange => Ok((true, None)),
                    requirements::RequirementResult::Satisfied(replacement) => {
                        self.trace_stack
                            .push(TraceStackEntry::ResolvedRequirement(req.clone()));
                        Ok((false, Some(replacement)))
                    }
                })
                .collect::<Result<Vec<_>>>()?
                .into_iter()
                .unzip();

            let replacements = replacements_option
                .into_iter()
                .flatten()
                .flatten()
                .collect::<Vec<_>>();

            // Drop all replacements that have now been applied
            self.requirements = self
                .requirements
                .drain(0..)
                .zip(retain)
                .filter_map(|(req, keep)| if keep { Some(req) } else { None })
                .collect();

            if replacements.is_empty() {
                break;
            }

            for Replacement { from, to, context } in replacements {
                self.unify(&to, &from, ctx)
                    .into_diagnostic_or_default(from.loc(), context)?;
            }
        }

        Ok(())
    }
}

impl TypeState {
    pub fn print_equations(&self) {
        for (lhs, rhs) in &self.equations {
            println!(
                "{} -> {}",
                format!("{lhs}").blue(),
                format!("{rhs:?}").green()
            )
        }

        println!("\nReplacments:");

        for (lhs, rhs) in self.replacements.iter().sorted() {
            println!(
                "{} -> {}",
                format!("{lhs:?}").blue(),
                format!("{rhs:?}").green()
            )
        }

        println!("\n Requirements:");

        for requirement in &self.requirements {
            println!("{:?}", requirement)
        }

        println!()
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
impl HasType for Loc<KnownType> {
    fn get_type(&self, _state: &TypeState) -> Result<TypeVar> {
        Ok(TypeVar::Known(self.loc(), self.inner.clone(), vec![]))
    }
}
impl HasType for NameID {
    fn get_type(&self, state: &TypeState) -> Result<TypeVar> {
        state.type_of(&TypedExpression::Name(self.clone()))
    }
}

/// Mapping between names and concrete type used for lookup, without being
/// able to do more type inference
/// Required because we can't serde the whole TypeState
#[derive(Serialize, Deserialize)]
pub struct TypeMap {
    equations: TypeEquations,
}

impl TypeMap {
    pub fn type_of(&self, thing: &TypedExpression) -> Option<&TypeVar> {
        self.equations.get(thing)
    }
}

impl From<TypeState> for TypeMap {
    fn from(val: TypeState) -> Self {
        TypeMap {
            equations: val.equations,
        }
    }
}
