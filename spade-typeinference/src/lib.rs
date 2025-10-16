// This algorithm is based off the excellent lecture here
// https://www.youtube.com/watch?v=xJXcZp2vgLs
//
// The basic idea is to go through every node in the HIR tree, for every typed thing,
// add an equation indicating a constraint on that thing. This can onlytydone once
// and should be done by the visitor for that node. The visitor should then unify
// types according to the rules of the node.

use std::cell::RefCell;
use std::cmp::PartialEq;
use std::collections::{BTreeMap, BTreeSet, HashMap};

use colored::Colorize;
use fixed_types::{t_int, t_uint};
use hir::expression::CallKind;
use hir::{
    param_util, Binding, ConstGeneric, Parameter, PipelineRegMarkerExtra, TypeExpression, TypeSpec,
    UnitHead, UnitKind, WalTrace, WhereClause,
};
use itertools::{Either, Itertools};
use method_resolution::{FunctionLikeName, IntoImplTarget};
use num::{BigInt, BigUint, Zero};
use replacement::ReplacementStack;
use serde::{Deserialize, Serialize};
use spade_common::id_tracker::{ExprID, ImplID};
use spade_common::num_ext::InfallibleToBigInt;
use spade_diagnostics::diag_list::{DiagList, ResultExt};
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
    bits_to_store, ce_int, ce_var, ConstraintExpr, ConstraintSource, TypeConstraints,
};
use equation::{TemplateTypeVarID, TypeEquations, TypeVar, TypeVarID, TypedExpression};
use error::{
    error_pattern_type_mismatch, Result, UnificationError, UnificationErrorExt, UnificationTrace,
};
use requirements::{Replacement, Requirement};
use trace_stack::{format_trace_stack, TraceStackEntry};
use traits::{TraitList, TraitReq};

use crate::error::TypeMismatch as Tm;
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
mod replacement;
mod requirements;
pub mod testutil;
pub mod trace_stack;
pub mod traits;

pub struct Context<'a> {
    pub symtab: &'a SymbolTable,
    pub items: &'a ItemList,
    pub trait_impls: &'a TraitImplList,
}
impl<'a> std::fmt::Debug for Context<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{context omitted}}")
    }
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
#[derive(Clone, Hash, Eq, PartialEq, Debug, Serialize, Deserialize)]
pub enum GenericListToken {
    Anonymous(usize),
    Definition(NameID),
    ImplBlock(ImplTarget, ImplID),
    Expression(ExprID),
}

#[derive(Debug)]
pub struct TurbofishCtx<'a> {
    turbofish: &'a Loc<ArgumentList<TypeExpression>>,
    prev_generic_list: &'a GenericListToken,
    type_ctx: &'a Context<'a>,
}

#[derive(Clone, Serialize, Deserialize)]
pub struct PipelineState {
    current_stage_depth: TypeVarID,
    total_depth: Loc<TypeVarID>,
    pipeline_loc: Loc<()>,
}

/// State of the type inference algorithm
#[derive(Clone, Serialize, Deserialize)]
pub struct TypeState {
    /// All types are referred to by their index to allow type vars changing inside
    /// the type state while the types are "out in the wild". The TypeVarID is an index
    /// into this type_vars list which is used to look up the actual type as currently
    /// seen by the type state
    type_vars: Vec<TypeVar>,
    /// This key is used to prevent bugs when multiple type states are mixed. Each TypeVarID
    /// holds the value of the key of the type state which created it, and this is checked
    /// to ensure that type vars are not mixed. The key is initialized randomly on type
    /// state creation
    key: u64,
    /// A type state can also support keys from other sources, this is tracked here
    keys: BTreeSet<u64>,

    equations: TypeEquations,
    // NOTE: This is kind of redundant, we could use TypeVarIDs instead of having dedicated
    // numbers for unknown types.
    next_typeid: RefCell<u64>,
    // List of the mapping between generic parameters and type vars.
    // The key is the index of the expression for which this generic list is associated. (if this
    // is a generic list for a call whose expression id is x to f<A, B>, then generic_lists[x] will
    // be {A: <type var>, b: <type var>}
    // Managed here because unification must update *all* TypeVars in existence.
    generic_lists: HashMap<GenericListToken, HashMap<NameID, TypeVarID>>,

    constraints: TypeConstraints,

    /// Requirements which must be fulfilled but which do not guide further type inference.
    /// For example, if seeing `let y = x.a` before knowing the type of `x`, a requirement is
    /// added to say "x has field a, and y should be the type of that field"
    #[serde(skip)]
    requirements: Vec<Requirement>,

    replacements: ReplacementStack,
    // Skipping serialization of these is fine as we only push checkpoints during
    // trait resolution
    #[serde(skip)]
    checkpoints: Vec<(Vec<Requirement>, TypeConstraints)>,

    /// The type var containing the depth of the pipeline stage we are currently in
    pipeline_state: Option<PipelineState>,

    /// An error type that can be accessed anywhere without mut access. This is an option
    /// to facilitate safe initialization, in practice it can never be None
    error_type: Option<TypeVarID>,

    pub trait_impls: TraitImplList,

    #[serde(skip)]
    pub trace_stack: TraceStack,

    #[serde(skip)]
    pub diags: DiagList,
}

impl TypeState {
    /// Create a fresh type state, in most cases, this should be .create_child of an
    /// existing type state
    pub fn fresh() -> Self {
        let key = fastrand::u64(..);
        let mut result = Self {
            type_vars: vec![],
            key,
            keys: [key].into_iter().collect(),
            equations: HashMap::new(),
            next_typeid: RefCell::new(0),
            trace_stack: TraceStack::new(),
            constraints: TypeConstraints::new(),
            requirements: vec![],
            replacements: ReplacementStack::new(),
            generic_lists: HashMap::new(),
            trait_impls: TraitImplList::new(),
            checkpoints: vec![],
            error_type: None,
            pipeline_state: None,
            diags: DiagList::new(),
        };
        result.error_type =
            Some(result.add_type_var(TypeVar::Known(().nowhere(), KnownType::Error, vec![])));
        result
    }

    pub fn create_child(&self) -> Self {
        let mut result = self.clone();
        result.key = fastrand::u64(..);
        result.keys.insert(result.key);
        result
    }

    pub fn add_type_var(&mut self, var: TypeVar) -> TypeVarID {
        let idx = self.type_vars.len();
        self.type_vars.push(var);
        TypeVarID {
            inner: idx,
            type_state_key: self.key,
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
    ) -> Option<&'a HashMap<NameID, TypeVarID>> {
        self.generic_lists.get(generic_list_token)
    }

    #[tracing::instrument(level = "trace", skip_all)]
    fn hir_type_expr_to_var<'a>(
        &'a mut self,
        e: &Loc<hir::TypeExpression>,
        generic_list_token: &GenericListToken,
    ) -> Result<TypeVarID> {
        let id = match &e.inner {
            hir::TypeExpression::Integer(i) => self.add_type_var(TypeVar::Known(
                e.loc(),
                KnownType::Integer(i.clone()),
                vec![],
            )),
            hir::TypeExpression::String(s) => self.add_type_var(TypeVar::Known(
                e.loc(),
                KnownType::String(s.clone()),
                vec![],
            )),
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
        Ok(id)
    }

    #[tracing::instrument(level = "trace", skip_all, fields(%hir_type))]
    pub fn type_var_from_hir<'a>(
        &'a mut self,
        loc: Loc<()>,
        hir_type: &crate::hir::TypeSpec,
        generic_list_token: &GenericListToken,
    ) -> Result<TypeVarID> {
        let generic_list = self.get_generic_list(generic_list_token);
        let var = match &hir_type {
            hir::TypeSpec::Declared(base, params) => {
                let params = params
                    .iter()
                    .map(|e| self.hir_type_expr_to_var(e, generic_list_token))
                    .collect::<Result<Vec<_>>>()?;

                self.add_type_var(TypeVar::Known(
                    loc,
                    KnownType::Named(base.inner.clone()),
                    params,
                ))
            }
            hir::TypeSpec::Generic(name) => match generic_list
                .ok_or_else(|| diag_anyhow!(loc, "Found no generic list for {name}"))?
                .get(&name.inner)
            {
                Some(t) => t.clone(),
                None => {
                    for list_source in self.generic_lists.keys() {
                        info!("Generic lists exist for {list_source:?}");
                    }
                    info!("Current source is {generic_list_token:?}");
                    panic!("No entry in generic list for {name:?}");
                }
            },
            hir::TypeSpec::Tuple(inner) => {
                let inner = inner
                    .iter()
                    .map(|t| self.type_var_from_hir(loc, t, generic_list_token))
                    .collect::<Result<_>>()?;
                self.add_type_var(TypeVar::tuple(loc, inner))
            }
            hir::TypeSpec::Array { inner, size } => {
                let inner = self.type_var_from_hir(loc, inner, generic_list_token)?;
                let size = self.hir_type_expr_to_var(size, generic_list_token)?;

                self.add_type_var(TypeVar::array(loc, inner, size))
            }
            hir::TypeSpec::Wire(inner) => {
                let inner = self.type_var_from_hir(loc, inner, generic_list_token)?;
                self.add_type_var(TypeVar::wire(loc, inner))
            }
            hir::TypeSpec::Inverted(inner) => {
                let inner = self.type_var_from_hir(loc, inner, generic_list_token)?;
                self.add_type_var(TypeVar::inverted(loc, inner))
            }
            hir::TypeSpec::Wildcard(_) => self.new_generic_any(),
            hir::TypeSpec::TraitSelf(_) => {
                diag_bail!(
                    loc,
                    "Trying to convert TraitSelf to type inference type var"
                )
            }
        };

        Ok(var)
    }

    /// Returns the type of the expression with the specified id. Error if no equation
    /// for the specified expression exists
    pub fn type_of(&self, expr: &TypedExpression) -> TypeVarID {
        if let Some(t) = self.equations.get(expr) {
            *t
        } else {
            panic!("Tried looking up the type of {expr:?} but it was not found")
        }
    }

    pub fn maybe_type_of(&self, expr: &TypedExpression) -> Option<&TypeVarID> {
        self.equations.get(expr)
    }

    pub fn new_generic_int(&mut self, loc: Loc<()>, symtab: &SymbolTable) -> TypeVar {
        TypeVar::Known(loc, t_int(symtab), vec![self.new_generic_tluint(loc)])
    }

    pub fn new_concrete_int(&mut self, size: BigUint, loc: Loc<()>) -> TypeVarID {
        TypeVar::Known(loc, KnownType::Integer(size.to_bigint()), vec![]).insert(self)
    }

    /// Return a new generic int. The first returned value is int<N>, and the second
    /// value is N
    pub fn new_split_generic_int(
        &mut self,
        loc: Loc<()>,
        symtab: &SymbolTable,
    ) -> (TypeVarID, TypeVarID) {
        let size = self.new_generic_tlint(loc);
        let full = self.add_type_var(TypeVar::Known(loc, t_int(symtab), vec![size.clone()]));
        (full, size)
    }

    pub fn new_split_generic_uint(
        &mut self,
        loc: Loc<()>,
        symtab: &SymbolTable,
    ) -> (TypeVarID, TypeVarID) {
        let size = self.new_generic_tluint(loc);
        let full = self.add_type_var(TypeVar::Known(loc, t_uint(symtab), vec![size.clone()]));
        (full, size)
    }

    pub fn new_generic_with_meta(&mut self, loc: Loc<()>, meta: MetaType) -> TypeVarID {
        let id = self.new_typeid();
        self.add_type_var(TypeVar::Unknown(loc, id, TraitList::empty(), meta))
    }

    pub fn new_generic_type(&mut self, loc: Loc<()>) -> TypeVarID {
        let id = self.new_typeid();
        self.add_type_var(TypeVar::Unknown(
            loc,
            id,
            TraitList::empty(),
            MetaType::Type,
        ))
    }

    pub fn new_generic_any(&mut self) -> TypeVarID {
        let id = self.new_typeid();
        // NOTE: ().nowhere() is fine here, we can never fail to unify with MetaType::Any so
        // this loc will never be displayed
        self.add_type_var(TypeVar::Unknown(
            ().nowhere(),
            id,
            TraitList::empty(),
            MetaType::Any,
        ))
    }

    pub fn new_generic_tlbool(&mut self, loc: Loc<()>) -> TypeVarID {
        let id = self.new_typeid();
        self.add_type_var(TypeVar::Unknown(
            loc,
            id,
            TraitList::empty(),
            MetaType::Bool,
        ))
    }

    pub fn new_generic_tlstr(&mut self, loc: Loc<()>) -> TypeVarID {
        let id = self.new_typeid();
        self.add_type_var(TypeVar::Unknown(loc, id, TraitList::empty(), MetaType::Str))
    }

    pub fn new_generic_tluint(&mut self, loc: Loc<()>) -> TypeVarID {
        let id = self.new_typeid();
        self.add_type_var(TypeVar::Unknown(
            loc,
            id,
            TraitList::empty(),
            MetaType::Uint,
        ))
    }

    pub fn new_generic_tlint(&mut self, loc: Loc<()>) -> TypeVarID {
        let id = self.new_typeid();
        self.add_type_var(TypeVar::Unknown(loc, id, TraitList::empty(), MetaType::Int))
    }

    pub fn new_generic_tlnumber(&mut self, loc: Loc<()>) -> TypeVarID {
        let id = self.new_typeid();
        self.add_type_var(TypeVar::Unknown(
            loc,
            id,
            TraitList::empty(),
            MetaType::Number,
        ))
    }

    pub fn new_generic_number(&mut self, loc: Loc<()>, ctx: &Context) -> (TypeVarID, TypeVarID) {
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
            self.add_type_var(TypeVar::Unknown(
                loc,
                id,
                TraitList::from_vec(vec![t]),
                MetaType::Type,
            )),
            size,
        )
    }

    pub fn new_generic_with_traits(&mut self, loc: Loc<()>, traits: TraitList) -> TypeVarID {
        let id = self.new_typeid();
        self.add_type_var(TypeVar::Unknown(loc, id, traits, MetaType::Type))
    }

    /// Returns the current pipeline state. `access_loc` is *not* used to specify where to get the
    /// state from, it is only used for the Diagnostic::bug that gets emitted if there is no
    /// pipeline state
    pub fn get_pipeline_state<T>(&self, access_loc: &Loc<T>) -> Result<&PipelineState> {
        self.pipeline_state
            .as_ref()
            .ok_or_else(|| diag_anyhow!(access_loc, "Expected to have a pipeline state"))
    }

    /// Visit a unit but before doing any preprocessing run the `pp` function.
    pub fn visit_unit_with_preprocessing(
        &mut self,
        entity: &Loc<Unit>,
        pp: impl Fn(&mut TypeState, &Loc<Unit>, &GenericListToken, &Context) -> Result<()>,
        ctx: &Context,
    ) -> Result<()> {
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

        pp(self, entity, &generic_list, ctx)?;

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
            self.setup_pipeline_state(
                &entity.head.unit_kind,
                &entity.body,
                &generic_list,
                depth,
                depth_typeexpr_id,
            )?;

            let clock_index = if entity.head.is_nonstatic_method {
                1
            } else {
                0
            };

            TypedExpression::Name(entity.inputs[clock_index].0.clone().inner)
                .unify_with(&self.t_clock(entity.head.unit_kind.loc(), ctx.symtab), self)
                .commit(self, ctx)
                .into_diagnostic(
                    entity.inputs[0].1.loc(),
                    |diag,
                     Tm {
                         g: got,
                         e: _expected,
                     }| {
                        diag.message(format!(
                            "First pipeline argument must be a clock. Got {}",
                            got.display(self)
                        ))
                        .primary_label("expected clock")
                    },
                    self,
                )?;
            // In order to catch negative depth early when they are specified as literals,
            // we'll instantly check requirements here
            self.check_requirements(false, ctx)?;
        }

        self.visit_expression(&entity.body, ctx, &generic_list);

        // Ensure that the output type matches what the user specified, and unit otherwise
        if let Some(output_type) = &entity.head.output_type {
            let tvar = self.type_var_from_hir(output_type.loc(), output_type, &generic_list)?;

            self.trace_stack.push(TraceStackEntry::Message(format!(
                "Unifying with output type {}",
                tvar.debug_resolve(self)
            )));
            self.unify(&TypedExpression::Id(entity.body.inner.id), &tvar, ctx)
                .into_diagnostic_no_expected_source(
                    &entity.body,
                    |diag,
                     Tm {
                         g: got,
                         e: expected,
                     }| {
                        let expected = expected.display(self);
                        let got = got.display(self);
                        // FIXME: Might want to check if there is no return value in the block
                        // and in that case suggest adding it.
                        diag.message(format!(
                            "Output type mismatch. Expected {expected}, got {got}"
                        ))
                        .primary_label(format!("Found type {got}"))
                        .secondary_label(output_type, format!("{expected} type specified here"))
                    },
                    self,
                )?;
        } else {
            // No output type, so unify with the unit type.
            TypedExpression::Id(entity.body.inner.id)
                .unify_with(&self.add_type_var(TypeVar::unit(entity.head.name.loc())), self)
                .commit(self, ctx)
                .into_diagnostic_no_expected_source(entity.body.loc(), |diag, Tm{g: got, e: _expected}| {
                    diag.message("Output type mismatch")
                        .primary_label(format!("Found type {got}", got = got.display(self)))
                        .note(format!(
                            "The {} does not specify a return type.\nAdd a return type, or remove the return value.",
                            entity.head.unit_kind.name()
                        ))
                }, self)?;
        }

        if let Some(PipelineState {
            current_stage_depth,
            pipeline_loc,
            total_depth,
        }) = self.pipeline_state.clone()
        {
            self.unify(&total_depth.inner, &current_stage_depth, ctx)
                .into_diagnostic_no_expected_source(
                    pipeline_loc,
                    |diag, tm| {
                        let (e, g) = tm.display_e_g(self);
                        diag.message(format!("Pipeline depth mismatch. Expected {g} got {e}"))
                            .primary_label(format!("Found {e} stages in this pipeline"))
                    },
                    self,
                )?;
        }

        self.check_requirements(true, ctx)?;

        // NOTE: We may accidentally leak a stage depth if this function returns early. However,
        // since we only use stage depths in pipelines where we re-set it when we enter,
        // accidentally leaving a depth in place should not trigger any *new* compiler bugs, but
        // may help track something down
        self.pipeline_state = None;

        Ok(())
    }

    fn setup_pipeline_state(
        &mut self,
        unit_kind: &Loc<UnitKind>,
        body_loc: &Loc<Expression>,
        generic_list: &GenericListToken,
        depth: &Loc<TypeExpression>,
        depth_typeexpr_id: &ExprID,
    ) -> Result<()> {
        let depth_var = self.hir_type_expr_to_var(depth, generic_list)?;
        self.add_equation(TypedExpression::Id(*depth_typeexpr_id), depth_var.clone());
        self.pipeline_state = Some(PipelineState {
            current_stage_depth: self.add_type_var(TypeVar::Known(
                unit_kind.loc(),
                KnownType::Integer(BigInt::zero()),
                vec![],
            )),
            pipeline_loc: body_loc.loc(),
            total_depth: depth_var.clone().at_loc(depth),
        });
        self.add_requirement(Requirement::PositivePipelineDepth {
            depth: depth_var.at_loc(depth),
        });
        Ok(())
    }

    #[trace_typechecker]
    #[tracing::instrument(level = "trace", skip_all, fields(%entity.name))]
    pub fn visit_unit(&mut self, entity: &Loc<Unit>, ctx: &Context) -> Result<()> {
        self.visit_unit_with_preprocessing(entity, |_, _, _, _| Ok(()), ctx)
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
            self.visit_expression(expr, ctx, generic_list);
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
                    |d, tm| {
                        let (expected, got) = tm.display_e_g(self);
                        d.message(format!(
                            "Argument type mismatch. Expected {expected} got {got}"
                        ))
                        .primary_label(format!("expected {expected}"))
                    },
                    self,
                )?;
        }

        Ok(())
    }

    #[trace_typechecker]
    pub fn visit_expression_result(
        &mut self,
        expression: &Loc<Expression>,
        ctx: &Context,
        generic_list: &GenericListToken,
        new_type: TypeVarID,
    ) -> Result<()> {
        // Recurse down the expression
        match &expression.inner.kind {
            ExprKind::Error => {
                new_type
                    .unify_with(&self.t_err(expression.loc()), self)
                    .commit(self, ctx)
                    .unwrap();
            }
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
                safety: _,
            } => {
                let head = ctx.symtab.unit_by_id(&callee.inner);

                self.handle_function_like(
                    expression.map_ref(|e| e.id),
                    &expression.get_type(self),
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
                expression
                    .unify_with(&self.t_bool(expression.loc(), ctx.symtab), self)
                    .commit(self, ctx)
                    .into_default_diagnostic(expression, self)?;
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
                    |diag, tm| {
                        let (_e, g) = tm.display_e_g(self);
                        diag.message(format!("gen if conditions must be #bool, got {g}"))
                    },
                    self,
                )?;

                self.visit_expression(on_true, ctx, generic_list);
                self.visit_expression(on_false, ctx, generic_list);

                self.unify_expression_generic_error(expression, on_true.as_ref(), ctx)?;
                self.unify_expression_generic_error(expression, on_false.as_ref(), ctx)?;
            }
            ExprKind::LambdaDef {
                unit_kind,
                arguments,
                body,
                lambda_type,
                lambda_type_params,
                captured_generic_params,
                lambda_unit: _,
                clock,
            } => {
                for arg in arguments {
                    self.visit_pattern(arg, ctx, generic_list)?;
                }

                if let Some(clock) = clock {
                    clock
                        .unify_with(&self.t_clock(clock.loc(), ctx.symtab), self)
                        .commit(self, ctx)
                        .into_default_diagnostic(clock, self)?;
                }

                let outer_pipeline_state = self.pipeline_state.take();
                if let UnitKind::Pipeline {
                    depth,
                    depth_typeexpr_id,
                } = &unit_kind.inner
                {
                    self.setup_pipeline_state(
                        unit_kind,
                        body,
                        &generic_list,
                        depth,
                        depth_typeexpr_id,
                    )?;
                }
                self.visit_expression(body, ctx, generic_list);
                self.pipeline_state = outer_pipeline_state;

                let lambda_params = arguments
                    .iter()
                    .map(|arg| arg.get_type(self))
                    .chain(vec![body.get_type(self)])
                    .chain(
                        captured_generic_params
                            .iter()
                            .map(|cap| {
                                let t = self
                                    .get_generic_list(generic_list)
                                    .ok_or_else(|| {
                                        diag_anyhow!(
                                            expression,
                                            "Found a captured generic but no generic list"
                                        )
                                    })?
                                    .get(&cap.name_in_body)
                                    .ok_or_else(|| {
                                        diag_anyhow!(
                                            &cap.name_in_body,
                                            "Did not find an entry for {} in lambda generic list",
                                            cap.name_in_body
                                        )
                                    });
                                Ok(t?.clone())
                            })
                            .collect::<Result<Vec<_>>>()?
                            .into_iter(),
                    )
                    .collect::<Vec<_>>();

                let self_type = TypeVar::Known(
                    expression.loc(),
                    KnownType::Named(lambda_type.clone()),
                    lambda_params.clone(),
                );

                let unit_generic_list = self.create_generic_list(
                    GenericListSource::Expression(expression.id),
                    &lambda_type_params,
                    &[],
                    None,
                    &[],
                )?;

                for (p, tp) in lambda_params.iter().zip(lambda_type_params) {
                    let gl = self.get_generic_list(&unit_generic_list).unwrap();
                    // Safe unwrap, we're just unifying unknowns with unknowns
                    p.unify_with(
                        gl.get(&tp.name_id).ok_or_else(|| {
                            diag_anyhow!(
                                expression,
                                "Lambda unit list did not contain {}",
                                tp.name_id
                            )
                        })?,
                        self,
                    )
                    .commit(self, ctx)
                    .into_default_diagnostic(expression, self)?;
                }
                expression
                    .unify_with(&self.add_type_var(self_type), self)
                    .commit(self, ctx)
                    .into_default_diagnostic(expression, self)?;
            }
            ExprKind::StaticUnreachable(_) => {}
            ExprKind::Null => {}
        }
        Ok(())
    }

    #[tracing::instrument(level = "trace", skip_all)]
    pub fn visit_expression(
        &mut self,
        expression: &Loc<Expression>,
        ctx: &Context,
        generic_list: &GenericListToken,
    ) {
        let new_type = self.new_generic_type(expression.loc());
        self.add_equation(TypedExpression::Id(expression.inner.id), new_type);

        match self.visit_expression_result(expression, ctx, generic_list, new_type) {
            Ok(_) => {}
            Err(e) => {
                new_type
                    .unify_with(&self.t_err(expression.loc()), self)
                    .commit(self, ctx)
                    .unwrap();

                self.diags.errors.push(e);
            }
        }
    }

    // Common handler for entities, functions and pipelines
    #[tracing::instrument(level = "trace", skip_all, fields(%name))]
    #[trace_typechecker]
    fn handle_function_like(
        &mut self,
        expression_id: Loc<ExprID>,
        expression_type: &TypeVarID,
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
                    .into_diagnostic_no_expected_source(
                        cdepth,
                        |diag, tm| {
                            let (e, g) = tm.display_e_g(self);
                            diag.message("Pipeline depth mismatch")
                                .primary_label(format!("Expected depth {e}, got {g}"))
                                .secondary_label(udepth, format!("{name} has depth {e}"))
                        },
                        self,
                    )?;
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
                        .try_lookup_final_id(&path, &[])
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
                self.get_generic_list(&unit_generic_list)
                    .ok_or_else(|| diag_anyhow!(expression_id, "Found no generic list for call"))?
                    [&type_params[$idx].name_id()]
                    .clone()
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
            .unwrap_or_else(|| {
                self.add_type_var(TypeVar::Known(
                    expression_id.loc(),
                    KnownType::Tuple,
                    vec![],
                ))
            });

        self.unify(expression_type, &return_type, ctx)
            .into_default_diagnostic(expression_id.loc(), self)?;

        Ok(())
    }

    pub fn handle_concat(
        &mut self,
        expression_id: Loc<ExprID>,
        source_lhs_ty: TypeVarID,
        source_rhs_ty: TypeVarID,
        source_result_ty: TypeVarID,
        args: &[Argument<Expression, TypeSpec>],
        ctx: &Context,
    ) -> Result<()> {
        let (lhs_type, lhs_size) = self.new_generic_number(expression_id.loc(), ctx);
        let (rhs_type, rhs_size) = self.new_generic_number(expression_id.loc(), ctx);
        let (result_type, result_size) = self.new_generic_number(expression_id.loc(), ctx);
        self.unify(&source_lhs_ty, &lhs_type, ctx)
            .into_default_diagnostic(args[0].value.loc(), self)?;
        self.unify(&source_rhs_ty, &rhs_type, ctx)
            .into_default_diagnostic(args[1].value.loc(), self)?;
        self.unify(&source_result_ty, &result_type, ctx)
            .into_default_diagnostic(expression_id.loc(), self)?;

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
        source_in_ty: TypeVarID,
        source_result_ty: TypeVarID,
        args: &[Argument<Expression, TypeSpec>],
        ctx: &Context,
    ) -> Result<()> {
        let (in_ty, _) = self.new_generic_number(expression_id.loc(), ctx);
        let (result_type, _) = self.new_generic_number(expression_id.loc(), ctx);
        self.unify(&source_in_ty, &in_ty, ctx)
            .into_default_diagnostic(args[0].value.loc(), self)?;
        self.unify(&source_result_ty, &result_type, ctx)
            .into_default_diagnostic(expression_id.loc(), self)?;

        self.add_requirement(Requirement::SharedBase(vec![
            in_ty.at_loc(args[0].value),
            result_type.at_loc(&expression_id.loc()),
        ]));
        Ok(())
    }

    pub fn handle_comb_mod_or_div(
        &mut self,
        n_ty: TypeVarID,
        args: &[Argument<Expression, TypeSpec>],
        ctx: &Context,
    ) -> Result<()> {
        let (num, _) = self.new_generic_number(args[0].value.loc(), ctx);
        self.unify(&n_ty, &num, ctx)
            .into_default_diagnostic(args[0].value.loc(), self)?;
        Ok(())
    }

    pub fn handle_clocked_memory(
        &mut self,
        num_elements: TypeVarID,
        addr_size_arg: TypeVarID,
        args: &[Argument<Expression, TypeSpec>],
        ctx: &Context,
    ) -> Result<()> {
        // FIXME: When we support where clauses, we should move this
        // definition into the definition of clocked_memory
        let (addr_type, addr_size) = self.new_split_generic_uint(args[1].value.loc(), ctx.symtab);
        let arg1_loc = args[1].value.loc();
        let tup = TypeVar::tuple(
            args[1].value.loc(),
            vec![
                self.new_generic_type(arg1_loc),
                addr_type,
                self.new_generic_type(arg1_loc),
            ],
        );
        let port_type = TypeVar::array(
            arg1_loc,
            self.add_type_var(tup),
            self.new_generic_tluint(arg1_loc),
        )
        .insert(self);

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
        num_elements: TypeVarID,
        addr_size_arg: TypeVarID,
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
                        .into_default_diagnostic(param, self)?;
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
                    Ok((name_id.clone(), t))
                }
            })
            .collect::<Result<Vec<_>>>()?
            .into_iter()
            .chain(scope_type_params.into_iter())
            .map(|(name, t)| (name, t.clone()))
            .collect::<HashMap<_, _>>();

        self.trace_stack.push(TraceStackEntry::NewGenericList(
            new_list
                .iter()
                .map(|(name, var)| (name.clone(), var.debug_resolve(self)))
                .collect(),
        ));

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
        mapping: HashMap<NameID, TypeVarID>,
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

    pub fn remove_generic_list(&mut self, source: GenericListSource) {
        let reference = match source {
            GenericListSource::Anonymous => GenericListToken::Anonymous(self.generic_lists.len()),
            GenericListSource::Definition(name) => GenericListToken::Definition(name.clone()),
            GenericListSource::ImplBlock { target, id } => {
                GenericListToken::ImplBlock(target.clone(), id)
            }
            GenericListSource::Expression(id) => GenericListToken::Expression(id),
        };

        self.generic_lists.remove(&reference.clone());
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
            self.visit_statement(statement, ctx, generic_list);
        }
        if let Some(result) = &block.result {
            self.visit_expression(result, ctx, generic_list);
        }
        Ok(())
    }

    #[tracing::instrument(level = "trace", skip_all)]
    pub fn visit_impl_blocks(&mut self, item_list: &ItemList) -> TraitImplList {
        let mut trait_impls = TraitImplList::new();
        for (target, impls) in &item_list.impls.inner {
            for (trait_name, impls) in impls {
                for (target_args, impls) in impls {
                    for (trait_args, impl_block) in impls {
                        let result =
                            (|| {
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

                                let trait_type_params = trait_args
                                    .iter()
                                    .map(|param| {
                                        Ok(TemplateTypeVarID::new(self.hir_type_expr_to_var(
                                            &param.clone().at_loc(&loc),
                                            &generic_list,
                                        )?))
                                    })
                                    .collect::<Result<_>>()?;

                                let target_type_params = target_args
                                    .iter()
                                    .map(|param| {
                                        Ok(TemplateTypeVarID::new(self.hir_type_expr_to_var(
                                            &param.clone().at_loc(&loc),
                                            &generic_list,
                                        )?))
                                    })
                                    .collect::<Result<_>>()?;

                                trait_impls.inner.entry(target.clone()).or_default().push(
                                    TraitImpl {
                                        name: trait_name.clone(),
                                        target_type_params,
                                        trait_type_params,

                                        impl_block: impl_block.inner.clone(),
                                    },
                                );

                                Ok(())
                            })();

                        match result {
                            Ok(()) => {}
                            Err(e) => self.diags.errors.push(e),
                        }
                    }
                }
            }
        }

        trait_impls
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
                pattern
                    .unify_with(&self.t_bool(pattern.loc(), ctx.symtab), self)
                    .commit(self, ctx)
                    .expect("Expected new_generic with boolean");
            }
            hir::PatternKind::Name { name, pre_declared } => {
                if !pre_declared {
                    self.add_equation(
                        TypedExpression::Name(name.clone().inner),
                        pattern.get_type(self),
                    );
                }
                self.unify(
                    &TypedExpression::Id(pattern.id),
                    &TypedExpression::Name(name.clone().inner),
                    ctx,
                )
                .into_default_diagnostic(name.loc(), self)?;
            }
            hir::PatternKind::Tuple(subpatterns) => {
                for pattern in subpatterns {
                    self.visit_pattern(pattern, ctx, generic_list)?;
                }
                let tuple_type = self.add_type_var(TypeVar::tuple(
                    pattern.loc(),
                    subpatterns
                        .iter()
                        .map(|pattern| {
                            let p_type = pattern.get_type(self);
                            Ok(p_type)
                        })
                        .collect::<Result<_>>()?,
                ));

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
                    let inner_t = inner[0].get_type(self);

                    for pattern in inner.iter().skip(1) {
                        self.unify(pattern, &inner_t, ctx)
                            .into_default_diagnostic(pattern, self)?;
                    }

                    pattern
                        .unify_with(
                            &TypeVar::Known(
                                pattern.loc(),
                                KnownType::Array,
                                vec![
                                    inner_t,
                                    self.add_type_var(TypeVar::Known(
                                        pattern.loc(),
                                        KnownType::Integer(inner.len().to_bigint()),
                                        vec![],
                                    )),
                                ],
                            )
                            .insert(self),
                            self,
                        )
                        .commit(self, ctx)
                        .into_default_diagnostic(pattern, self)?;
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
                        field_translator: _,
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
                        |d, tm| {
                            let (expected, got) = tm.display_e_g(self);
                            d.message(format!(
                                "Argument type mismatch. Expected {expected} got {got}"
                            ))
                            .primary_label(format!("expected {expected}"))
                        },
                        self,
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
                self.visit_expression(x, ctx, generic_list);
                x.unify_with(&self.t_clock(trace.loc(), ctx.symtab), self)
                    .commit(self, ctx)
                    .into_default_diagnostic(x, self)
            })
            .transpose()?;
        rst.as_ref()
            .map(|x| {
                self.visit_expression(x, ctx, generic_list);
                x.unify_with(&self.t_bool(trace.loc(), ctx.symtab), self)
                    .commit(self, ctx)
                    .into_default_diagnostic(x, self)
            })
            .transpose()?;
        Ok(())
    }

    #[trace_typechecker]
    pub fn visit_statement_error(
        &mut self,
        stmt: &Loc<Statement>,
        ctx: &Context,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        match &stmt.inner {
            Statement::Error => {
                if let Some(current_stage_depth) =
                    self.pipeline_state.as_ref().map(|s| s.current_stage_depth)
                {
                    current_stage_depth
                        .unify_with(&self.t_err(stmt.loc()), self)
                        .commit(self, ctx)
                        .unwrap();
                }
                Ok(())
            }
            Statement::Binding(Binding {
                pattern,
                ty,
                value,
                wal_trace,
            }) => {
                trace!("Visiting `let {} = ..`", pattern.kind);
                self.visit_expression(value, ctx, generic_list);

                self.visit_pattern(pattern, ctx, generic_list)
                    .handle_in(&mut self.diags);

                self.unify(&TypedExpression::Id(pattern.id), value, ctx)
                    .into_diagnostic(
                        pattern.loc(),
                        error_pattern_type_mismatch(
                            ty.as_ref().map(|t| t.loc()).unwrap_or_else(|| value.loc()),
                            self,
                        ),
                        self,
                    )
                    .handle_in(&mut self.diags);

                if let Some(t) = ty {
                    let tvar = self.type_var_from_hir(t.loc(), t, generic_list)?;
                    self.unify(&TypedExpression::Id(pattern.id), &tvar, ctx)
                        .into_default_diagnostic(value.loc(), self)
                        .handle_in(&mut self.diags);
                }

                wal_trace
                    .as_ref()
                    .map(|wt| self.visit_wal_trace(wt, ctx, generic_list))
                    .transpose()
                    .handle_in(&mut self.diags);

                Ok(())
            }
            Statement::Expression(expr) => {
                self.visit_expression(expr, ctx, generic_list);
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
                        self.visit_expression(cond, ctx, generic_list);
                        cond.unify_with(&self.t_bool(cond.loc(), ctx.symtab), self)
                            .commit(self, ctx)
                            .into_default_diagnostic(cond, self)?;
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
                    Some(PipelineRegMarkerExtra::Condition(_)) | None => self.add_type_var(
                        TypeVar::Known(stmt.loc(), KnownType::Integer(1.to_bigint()), vec![]),
                    ),
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
                        var.debug_resolve(self),
                    ));
                    self.add_equation(key.clone(), var.clone());
                    var
                } else {
                    let var = self.equations.get(&key).unwrap().clone();
                    self.trace_stack
                        .push(TraceStackEntry::RecoveringPipelineLabel(
                            name.inner.clone(),
                            var.debug_resolve(self),
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
                self.visit_expression(expr, ctx, generic_list);

                expr.unify_with(&self.t_bool(stmt.loc(), ctx.symtab), self)
                    .commit(self, ctx)
                    .into_default_diagnostic(expr, self)
                    .handle_in(&mut self.diags);
                Ok(())
            }
            Statement::Set { target, value } => {
                self.visit_expression(target, ctx, generic_list);
                self.visit_expression(value, ctx, generic_list);

                let inner_type = self.new_generic_type(value.loc());
                let outer_type = TypeVar::inverted(stmt.loc(), inner_type.clone()).insert(self);
                self.unify_expression_generic_error(target, &outer_type, ctx)
                    .handle_in(&mut self.diags);
                self.unify_expression_generic_error(value, &inner_type, ctx)
                    .handle_in(&mut self.diags);

                Ok(())
            }
        }
    }

    pub fn visit_statement(
        &mut self,
        stmt: &Loc<Statement>,
        ctx: &Context,
        generic_list: &GenericListToken,
    ) {
        if let Err(e) = self.visit_statement_error(stmt, ctx, generic_list) {
            self.diags.errors.push(e);
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
                    error_pattern_type_mismatch(tvar.loc(), self),
                    self,
                )?;
        }

        self.visit_expression(&reg.clock, ctx, generic_list);
        self.visit_expression(&reg.value, ctx, generic_list);

        if let Some(tvar) = &type_spec_type {
            self.unify(&reg.value, tvar, ctx)
                .into_default_diagnostic(reg.value.loc(), self)?;
        }

        if let Some((rst_cond, rst_value)) = &reg.reset {
            self.visit_expression(rst_cond, ctx, generic_list);
            self.visit_expression(rst_value, ctx, generic_list);
            // Ensure cond is a boolean
            rst_cond
                .unify_with(&self.t_bool(rst_cond.loc(), ctx.symtab), self)
                .commit(self, ctx)
                .into_diagnostic(
                    rst_cond.loc(),
                    |diag,
                     Tm {
                         g: got,
                         e: _expected,
                     }| {
                        diag.message(format!(
                            "Register reset condition must be a bool, got {got}",
                            got = got.display(self)
                        ))
                        .primary_label("expected bool")
                    },
                    self,
                )?;

            // Ensure the reset value has the same type as the register itself
            self.unify(&rst_value.inner, &reg.value.inner, ctx)
                .into_diagnostic(
                    rst_value.loc(),
                    |diag, tm| {
                        let (expected, got) = tm.display_e_g(self);
                        diag.message(format!(
                            "Register reset value mismatch. Expected {expected} got {got}"
                        ))
                        .primary_label(format!("expected {expected}"))
                        .secondary_label(&reg.pattern, format!("because this has type {expected}"))
                    },
                    self,
                )?;
        }

        if let Some(initial) = &reg.initial {
            self.visit_expression(initial, ctx, generic_list);

            self.unify(&initial.inner, &reg.value.inner, ctx)
                .into_diagnostic(
                    initial.loc(),
                    |diag, tm| {
                        let (expected, got) = tm.display_e_g(self);
                        diag.message(format!(
                            "Register initial value mismatch. Expected {expected} got {got}"
                        ))
                        .primary_label(format!("expected {expected}, got {got}"))
                        .secondary_label(&reg.pattern, format!("because this has type {got}"))
                    },
                    self,
                )?;
        }

        reg.clock
            .unify_with(&self.t_clock(reg.clock.loc(), ctx.symtab), self)
            .commit(self, ctx)
            .into_diagnostic(
                reg.clock.loc(),
                |diag,
                 Tm {
                     g: got,
                     e: _expected,
                 }| {
                    diag.message(format!(
                        "Expected clock, got {got}",
                        got = got.display(self)
                    ))
                    .primary_label("expected clock")
                },
                self,
            )?;

        self.unify(&TypedExpression::Id(reg.pattern.id), &reg.value, ctx)
            .into_diagnostic(
                reg.pattern.loc(),
                error_pattern_type_mismatch(reg.value.loc(), self),
                self,
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
        generic_list_tok: &GenericListToken,
    ) -> Result<()> {
        let trait_reqs = traits
            .iter()
            .map(|spec| self.visit_trait_spec(spec, generic_list_tok))
            .collect::<Result<BTreeSet<_>>>()?
            .into_iter()
            .collect_vec();

        if !trait_reqs.is_empty() {
            let trait_list = TraitList::from_vec(trait_reqs);

            let generic_list = self.generic_lists.get(generic_list_tok).unwrap();

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
                tvar.debug_resolve(self),
                trait_list.clone(),
            ));

            match tvar.resolve(self) {
                TypeVar::Known(_, _, _) => {
                    // NOTE: This branch is a no-op as it is only triggered when re-visiting
                    // units for typeinference during monomorpization, a process which replaces
                    // some unknown types with known counterparts.
                    // Ideally, we'd re-run ensure_impls here but that requires a context which
                    // isn't necessarily available here, so #yolo
                }
                TypeVar::Unknown(loc, id, old_trait_list, _meta_type) => {
                    let new_tvar = self.add_type_var(TypeVar::Unknown(
                        *loc,
                        *id,
                        old_trait_list.clone().extend(trait_list),
                        MetaType::Type,
                    ));

                    trace!(
                        "Adding trait bound {} on type {}",
                        new_tvar.display_with_meta(true, self),
                        target.inner
                    );

                    let generic_list = self.generic_lists.get_mut(generic_list_tok).unwrap();
                    generic_list.insert(target.inner.clone(), new_tvar);
                }
            }
        }

        Ok(())
    }

    pub fn visit_const_generic_with_id(
        &mut self,
        gen: &Loc<ConstGenericWithId>,
        generic_list_token: &GenericListToken,
        constraint_source: ConstraintSource,
        ctx: &Context,
    ) -> Result<TypeVarID> {
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
                    TypeSymbol::GenericMeta(MetaType::Str) => self.new_generic_tlstr(gen.loc()),
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
            ConstGeneric::Int(_)
            | ConstGeneric::Add(_, _)
            | ConstGeneric::Sub(_, _)
            | ConstGeneric::Mul(_, _)
            | ConstGeneric::Div(_, _)
            | ConstGeneric::Mod(_, _)
            | ConstGeneric::UintBitsToFit(_) => self.new_generic_tlnumber(gen.loc()),
            ConstGeneric::Str(_) => self.new_generic_tlstr(gen.loc()),
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
        let wrap = |lhs,
                    rhs,
                    wrapper: fn(Box<ConstraintExpr>, Box<ConstraintExpr>) -> ConstraintExpr|
         -> Result<_> {
            Ok(wrapper(
                Box::new(self.visit_const_generic(lhs, generic_list)?),
                Box::new(self.visit_const_generic(rhs, generic_list)?),
            ))
        };
        let constraint = match constraint {
            ConstGeneric::Name(n) => {
                let var = self
                    .get_generic_list(generic_list)
                    .ok_or_else(|| diag_anyhow!(n, "Found no generic list"))?
                    .get(n)
                    .ok_or_else(|| {
                        Diagnostic::bug(n, "Found non-generic argument in where clause")
                    })?;
                ConstraintExpr::Var(*var)
            }
            ConstGeneric::Int(val) => ConstraintExpr::Integer(val.clone()),
            ConstGeneric::Str(val) => ConstraintExpr::String(val.clone()),
            ConstGeneric::Add(lhs, rhs) => wrap(lhs, rhs, ConstraintExpr::Sum)?,
            ConstGeneric::Sub(lhs, rhs) => wrap(lhs, rhs, ConstraintExpr::Difference)?,
            ConstGeneric::Mul(lhs, rhs) => wrap(lhs, rhs, ConstraintExpr::Product)?,
            ConstGeneric::Div(lhs, rhs) => wrap(lhs, rhs, ConstraintExpr::Div)?,
            ConstGeneric::Mod(lhs, rhs) => wrap(lhs, rhs, ConstraintExpr::Mod)?,
            ConstGeneric::Eq(lhs, rhs) => wrap(lhs, rhs, ConstraintExpr::Eq)?,
            ConstGeneric::NotEq(lhs, rhs) => wrap(lhs, rhs, ConstraintExpr::NotEq)?,
            ConstGeneric::UintBitsToFit(a) => ConstraintExpr::UintBitsToRepresent(Box::new(
                self.visit_const_generic(a, generic_list)?,
            )),
        };
        Ok(constraint)
    }
}

// Private helper functions
impl TypeState {
    fn new_typeid(&self) -> u64 {
        let mut next = self.next_typeid.borrow_mut();
        let result = *next;
        *next += 1;
        result
    }

    pub fn add_equation(&mut self, expression: TypedExpression, var: TypeVarID) {
        self.trace_stack.push(TraceStackEntry::AddingEquation(
            expression.clone(),
            var.debug_resolve(self),
        ));
        if let Some(prev) = self.equations.insert(expression.clone(), var.clone()) {
            let var = var.clone();
            let expr = expression.clone();
            println!("{}", format_trace_stack(self));
            panic!("Adding equation for {} == {} but a previous eq exists.\n\tIt was previously bound to {}", expr, var.debug_resolve(self), prev.debug_resolve(self))
        }
    }

    fn add_constraint(
        &mut self,
        lhs: TypeVarID,
        rhs: ConstraintExpr,
        loc: Loc<()>,
        inside: &TypeVarID,
        source: ConstraintSource,
    ) {
        let replaces = lhs.clone();
        let rhs = rhs.with_context(&replaces, &inside, source).at_loc(&loc);

        self.trace_stack.push(TraceStackEntry::AddingConstraint(
            lhs.debug_resolve(self),
            rhs.inner.clone(),
        ));

        self.constraints.add_int_constraint(lhs, rhs);
    }

    fn add_requirement(&mut self, requirement: Requirement) {
        self.trace_stack
            .push(TraceStackEntry::AddRequirement(requirement.clone()));
        self.requirements.push(requirement)
    }

    /// Performs unification but does not update constraints. This is done to avoid
    /// updating constraints more often than necessary. Technically, constraints can
    /// be updated even less often, but `unify` is a pretty natural point to do so.

    fn unify_inner(
        &mut self,
        e1: &impl HasType,
        e2: &impl HasType,
        ctx: &Context,
    ) -> std::result::Result<TypeVarID, UnificationError> {
        let v1 = e1.get_type(self);
        let v2 = e2.get_type(self);

        trace!(
            "Unifying {} with {}",
            v1.debug_resolve(self),
            v2.debug_resolve(self)
        );

        self.trace_stack.push(TraceStackEntry::TryingUnify(
            v1.debug_resolve(self),
            v2.debug_resolve(self),
        ));

        macro_rules! err_producer {
            () => {{
                self.trace_stack
                    .push(TraceStackEntry::Message("Produced error".to_string()));
                UnificationError::Normal(Tm {
                    g: UnificationTrace::new(v1),
                    e: UnificationTrace::new(v2),
                })
            }};
        }
        macro_rules! meta_err_producer {
            () => {{
                self.trace_stack
                    .push(TraceStackEntry::Message("Produced error".to_string()));
                UnificationError::MetaMismatch(Tm {
                    g: UnificationTrace::new(v1),
                    e: UnificationTrace::new(v2),
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

        let unify_params = |s: &mut Self,
                            p1: &[TypeVarID],
                            p2: &[TypeVarID]|
         -> std::result::Result<(), UnificationError> {
            if p1.len() != p2.len() {
                return Err({
                    s.trace_stack
                        .push(TraceStackEntry::Message("Produced error".to_string()));
                    UnificationError::Normal(Tm {
                        g: UnificationTrace::new(v1),
                        e: UnificationTrace::new(v2),
                    })
                });
            }

            for (t1, t2) in p1.iter().zip(p2.iter()) {
                match s.unify_inner(t1, t2, ctx) {
                    Ok(result) => result,
                    Err(e) => {
                        s.trace_stack
                            .push(TraceStackEntry::Message("Adding context".to_string()));
                        return Err(e).add_context(v1.clone(), v2.clone());
                    }
                };
            }
            Ok(())
        };

        // Figure out the most general type, and take note if we need to
        // do any replacement of the types in the rest of the state
        let result = match (
            &(v1, v1.resolve(self).clone()),
            &(v2, v2.resolve(self).clone()),
        ) {
            ((_, TypeVar::Known(_, KnownType::Error, _)), _) => Ok((v1, vec![v2])),
            (_, (_, TypeVar::Known(_, KnownType::Error, _))) => Ok((v2, vec![v1])),
            ((_, TypeVar::Known(_, t1, p1)), (_, TypeVar::Known(_, t2, p2))) => {
                match (t1, t2) {
                    (KnownType::Integer(val1), KnownType::Integer(val2)) => {
                        // NOTE: We get better error messages if we don't actually
                        // replace v1 with v2. Not entirely sure why, but since they already
                        // have the same known type, we're fine. The same applies
                        // to all known types
                        unify_if!(val1 == val2, v1, vec![])
                    }
                    (KnownType::String(val1), KnownType::String(val2)) => {
                        // Copied from the (Integer, Integer) case, its remark may also apply
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

                                let new_ts1 = ctx.symtab.type_symbol_by_id(n1).inner;
                                let new_ts2 = ctx.symtab.type_symbol_by_id(n2).inner;
                                unify_params(self, &p1, &p2)?;
                                unify_if!(new_ts1 == new_ts2, v1, vec![])
                            }
                            (TypeSymbol::Declared(_, _), TypeSymbol::GenericArg { traits }) => {
                                if !traits.is_empty() {
                                    todo!("Implement trait unifictaion");
                                }
                                Ok((v1, vec![]))
                            }
                            (TypeSymbol::GenericArg { traits }, TypeSymbol::Declared(_, _)) => {
                                if !traits.is_empty() {
                                    todo!("Implement trait unifictaion");
                                }
                                Ok((v2, vec![]))
                            }
                            (
                                TypeSymbol::GenericArg { traits: ltraits },
                                TypeSymbol::GenericArg { traits: rtraits },
                            ) => {
                                if !ltraits.is_empty() || !rtraits.is_empty() {
                                    todo!("Implement trait unifictaion");
                                }
                                Ok((v1, vec![]))
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
                        // Note, replacements should only occur when a variable goes from Unknown
                        // to Known, not when the base is the same. Replacements take care
                        // of parameters. Therefore, None is returned here
                        unify_params(self, &p1, &p2)?;
                        Ok((v1, vec![]))
                    }
                    (_, _) => Err(err_producer!()),
                }
            }
            // Unknown with unknown requires merging traits
            (
                (_, TypeVar::Unknown(loc1, _, traits1, meta1)),
                (_, TypeVar::Unknown(loc2, _, traits2, meta2)),
            ) => {
                let new_loc = if meta1.is_more_concrete_than(meta2) {
                    loc1
                } else {
                    loc2
                };
                let new_t = match unify_meta(meta1, meta2) {
                    Some(meta @ MetaType::Any) | Some(meta @ MetaType::Number) => {
                        if traits1.inner.is_empty() || traits2.inner.is_empty() {
                            return Err(UnificationError::Specific(diag_anyhow!(
                                new_loc,
                                "Inferred an any meta-type with traits"
                            )));
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
                    Some(MetaType::Str) => self.new_generic_tlstr(*new_loc),
                    None => return Err(meta_err_producer!()),
                };
                Ok((new_t, vec![v1, v2]))
            }
            (
                (otherid, TypeVar::Known(loc, base, params)),
                (ukid, TypeVar::Unknown(ukloc, _, traits, meta)),
            )
            | (
                (ukid, TypeVar::Unknown(ukloc, _, traits, meta)),
                (otherid, TypeVar::Known(loc, base, params)),
            ) => {
                let trait_is_expected = match (&v1.resolve(self), &v2.resolve(self)) {
                    (TypeVar::Known(_, _, _), _) => true,
                    _ => false,
                };

                let impls = self.ensure_impls(otherid, traits, trait_is_expected, ukloc, ctx)?;

                self.trace_stack.push(TraceStackEntry::Message(
                    "Unifying trait_parameters".to_string(),
                ));
                let mut new_params = params.clone();
                for (trait_impl, trait_req) in impls {
                    let mut param_map = BTreeMap::new();

                    for (l, r) in trait_req
                        .type_params
                        .iter()
                        .zip(trait_impl.trait_type_params)
                    {
                        let copy = r.make_copy_with_mapping(self, &mut param_map);
                        self.unify(l, &copy, ctx)?;
                    }

                    new_params = trait_impl
                        .target_type_params
                        .iter()
                        .zip(new_params)
                        .map(|(l, r)| {
                            let copy = l.make_copy_with_mapping(self, &mut param_map);
                            self.unify(&copy, &r, ctx).add_context(*ukid, *otherid)
                        })
                        .collect::<std::result::Result<_, _>>()?
                }

                match (base, meta) {
                    (KnownType::Error, _) => {
                        unreachable!()
                    }
                    // Any matches all types
                    (_, MetaType::Any)
                    // All types are types
                    | (KnownType::Named(_), MetaType::Type)
                    | (KnownType::Tuple, MetaType::Type)
                    | (KnownType::Array, MetaType::Type)
                    | (KnownType::Wire, MetaType::Type)
                    | (KnownType::Bool(_), MetaType::Bool)
                    | (KnownType::String(_), MetaType::Str)
                    | (KnownType::Inverted, MetaType::Type)
                    // Integers match ints and numbers
                    | (KnownType::Integer(_), MetaType::Int)
                    | (KnownType::Integer(_), MetaType::Number)
                    => {
                        let new = self.add_type_var(TypeVar::Known(*loc, base.clone(), new_params));

                        Ok((new, vec![otherid.clone(), ukid.clone()]))
                    },
                    // Integers match uints but only if the concrete integer is >= 0
                    (KnownType::Integer(val), MetaType::Uint)
                    => {
                        if val < &0.to_bigint() {
                            Err(meta_err_producer!())
                        } else {
                            let new = self.add_type_var(TypeVar::Known(*loc, base.clone(), new_params));

                            Ok((new, vec![otherid.clone(), ukid.clone()]))
                        }
                    },

                    // Integer with type
                    (KnownType::Integer(_), MetaType::Type) => Err(meta_err_producer!()),

                    // Bools only unify with any or bool
                    (_, MetaType::Bool) => Err(meta_err_producer!()),
                    (KnownType::Bool(_), _) => Err(meta_err_producer!()),

                    // Strings only unify with any or str
                    (_, MetaType::Str) => Err(meta_err_producer!()),
                    (KnownType::String(_), _) => Err(meta_err_producer!()),

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
            v1.debug_resolve(self),
            v2.debug_resolve(self),
            new_type.debug_resolve(self),
            replaced_types
                .iter()
                .map(|v| v.debug_resolve(self))
                .collect(),
        ));

        for replaced_type in &replaced_types {
            if v1.inner != v2.inner {
                let (from, to) = (replaced_type.get_type(self), new_type.get_type(self));
                self.replacements.insert(from, to);
                if let Err(rec) = self.check_type_for_recursion(to, &mut vec![]) {
                    let err_t = self.t_err(().nowhere());
                    self.replacements.insert(to, err_t);
                    return Err(UnificationError::RecursiveType(rec));
                }
            }
        }

        Ok(new_type)
    }

    pub fn can_unify(&mut self, e1: &impl HasType, e2: &impl HasType, ctx: &Context) -> bool {
        self.trace_stack
            .push(TraceStackEntry::Enter("Running can_unify".to_string()));
        let result = self.do_and_restore(|s| s.unify(e1, e2, ctx)).is_ok();
        self.trace_stack.push(TraceStackEntry::Exit);
        result
    }

    #[tracing::instrument(level = "trace", skip_all)]
    pub fn unify(
        &mut self,
        e1: &impl HasType,
        e2: &impl HasType,
        ctx: &Context,
    ) -> std::result::Result<TypeVarID, UnificationError> {
        let new_type = self.unify_inner(e1, e2, ctx)?;

        // With replacement done, some of our constraints may have been updated to provide
        // more type inference information. Try to do unification of those new constraints too
        loop {
            trace!("Updating constraints");
            // NOTE: Cloning here is kind of ugly
            let new_info;
            (self.constraints, new_info) = self
                .constraints
                .clone()
                .update_type_level_value_constraints(self);

            if new_info.is_empty() {
                break;
            }

            for constraint in new_info {
                trace!(
                    "Constraint replaces {} with {:?}",
                    constraint.inner.0.display(self),
                    constraint.inner.1
                );

                let ((var, replacement), loc) = constraint.split_loc();

                self.trace_stack
                    .push(TraceStackEntry::InferringFromConstraints(
                        var.debug_resolve(self),
                        replacement.val.clone(),
                    ));

                // NOTE: safe unwrap. We already checked the constraint above
                let expected_type = self.add_type_var(TypeVar::Known(loc, replacement.val, vec![]));
                let result = self.unify_inner(&expected_type.clone().at_loc(&loc), &var, ctx);
                let is_meta_error = matches!(result, Err(UnificationError::MetaMismatch { .. }));
                match result {
                    Ok(_) => {}
                    Err(UnificationError::Normal(Tm { mut e, mut g }))
                    | Err(UnificationError::MetaMismatch(Tm { mut e, mut g })) => {
                        e.inside.replace(
                            replacement
                                .context
                                .inside
                                .replace_inside(var, e.failing, self),
                        );
                        g.inside.replace(
                            replacement
                                .context
                                .inside
                                .replace_inside(var, g.failing, self),
                        );
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
                        | e @ UnificationError::RecursiveType(_)
                        | e @ UnificationError::UnsatisfiedTraits { .. },
                    ) => return Err(e),
                };
            }
        }

        Ok(new_type)
    }

    fn check_type_for_recursion(
        &self,
        ty: TypeVarID,
        seen: &mut Vec<TypeVarID>,
    ) -> std::result::Result<(), String> {
        seen.push(ty);
        match ty.resolve(self) {
            TypeVar::Known(_, base, params) => {
                for (i, param) in params.iter().enumerate() {
                    if seen.contains(param) {
                        return Err("*".to_string());
                    }

                    if let Err(rest) = self.check_type_for_recursion(*param, seen) {
                        let list = params
                            .iter()
                            .enumerate()
                            .map(|(j, _)| {
                                if j == i {
                                    rest.clone()
                                } else {
                                    "_".to_string()
                                }
                            })
                            .join(", ");

                        match base {
                            KnownType::Error => {}
                            KnownType::Named(name_id) => {
                                return Err(format!("{name_id}<{}>", list));
                            }
                            KnownType::Bool(_) | KnownType::Integer(_) | KnownType::String(_) => {
                                unreachable!("Encountered recursive type level bool, int or str")
                            }
                            KnownType::Tuple => return Err(format!("({})", list)),
                            KnownType::Array => return Err(format!("[{}]", list)),
                            KnownType::Wire => return Err(format!("&{}", list)),
                            KnownType::Inverted => return Err(format!("inv {}", list)),
                        }
                    }
                }
            }
            TypeVar::Unknown(_, _, traits, _) => {
                for t in &traits.inner {
                    for param in &t.type_params {
                        if seen.contains(param) {
                            return Err("...".to_string());
                        }

                        self.check_type_for_recursion(*param, seen)?;
                    }
                }
            }
        }
        seen.pop();
        Ok(())
    }

    fn ensure_impls(
        &mut self,
        var: &TypeVarID,
        traits: &TraitList,
        trait_is_expected: bool,
        trait_list_loc: &Loc<()>,
        ctx: &Context,
    ) -> std::result::Result<Vec<(TraitImpl, TraitReq)>, UnificationError> {
        self.trace_stack.push(TraceStackEntry::EnsuringImpls(
            var.debug_resolve(self),
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
                            var: *var,
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

        match &var.resolve(self).clone() {
            TypeVar::Known(_, known, params) if known.into_impl_target().is_some() => {
                let Some(target) = known.into_impl_target() else {
                    unreachable!()
                };

                let (impls, unsatisfied): (Vec<_>, Vec<_>) = traits
                    .inner
                    .iter()
                    .map(|trait_req| {
                        if let Some(impld) = self.trait_impls.inner.get(&target).cloned() {
                            // Get a list of implementations of this trait where the type
                            // parameters can match
                            let target_impls = impld
                                .iter()
                                .filter_map(|trait_impl| {
                                    self.checkpoint();
                                    let trait_params_match = trait_impl
                                        .trait_type_params
                                        .iter()
                                        .zip(trait_req.type_params.iter())
                                        .all(|(l, r)| {
                                            let l = l.make_copy(self);
                                            self.unify(&l, r, ctx).is_ok()
                                        });

                                    let impl_params_match =
                                        trait_impl.target_type_params.iter().zip(params).all(
                                            |(l, r)| {
                                                let l = l.make_copy(self);
                                                self.unify(&l, r, ctx).is_ok()
                                            },
                                        );
                                    self.restore();

                                    if trait_impl.name == trait_req.name
                                        && trait_params_match
                                        && impl_params_match
                                    {
                                        Some(trait_impl)
                                    } else {
                                        None
                                    }
                                })
                                .collect::<Vec<_>>();

                            if target_impls.len() == 0 {
                                Ok(Either::Right(trait_req.clone()))
                            } else if target_impls.len() == 1 {
                                let target_impl = *target_impls.last().unwrap();
                                Ok(Either::Left((target_impl.clone(), trait_req.inner.clone())))
                            } else {
                                Err(UnificationError::Specific(diag_anyhow!(
                                    trait_req,
                                    "Found more than one impl of {} for {}",
                                    trait_req.display(self),
                                    var.display(self)
                                )))
                            }
                        } else {
                            Ok(Either::Right(trait_req.clone()))
                        }
                    })
                    .collect::<std::result::Result<Vec<_>, _>>()?
                    .into_iter()
                    .partition_map(|x| x);

                if unsatisfied.is_empty() {
                    self.trace_stack.push(TraceStackEntry::Message(
                        "Ensuring impl successful".to_string(),
                    ));
                    Ok(impls)
                } else {
                    error_producer!(TraitList::from_vec(unsatisfied.clone()))
                }
            }
            TypeVar::Unknown(_, _, _, _) => {
                panic!("running ensure_impls on an unknown type")
            }
            _ => {
                if traits.inner.is_empty() {
                    Ok(vec![])
                } else {
                    error_producer!(traits.clone())
                }
            }
        }
    }

    pub fn unify_expression_generic_error(
        &mut self,
        expr: &Loc<Expression>,
        other: &impl HasType,
        ctx: &Context,
    ) -> Result<TypeVarID> {
        self.unify(&expr.inner, other, ctx)
            .into_default_diagnostic(expr.loc(), self)
    }

    pub fn check_requirements(&mut self, is_final_check: bool, ctx: &Context) -> Result<()> {
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
                    requirements::RequirementResult::UnsatisfiedNow(diag) => {
                        if is_final_check {
                            Err(diag)
                        } else {
                            Ok((true, None))
                        }
                    }
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
                self.unify(&to, &from, ctx).into_diagnostic_or_default(
                    from.loc(),
                    context,
                    self,
                )?;
            }
        }

        Ok(())
    }

    pub fn get_replacement(&self, var: &TypeVarID) -> TypeVarID {
        self.replacements.get(*var)
    }

    pub fn do_and_restore<T, E>(
        &mut self,
        inner: impl Fn(&mut Self) -> std::result::Result<T, E>,
    ) -> std::result::Result<T, E> {
        self.checkpoint();
        let result = inner(self);
        self.restore();
        result
    }

    /// Create a "checkpoint" to which we can restore later using `restore`. This acts
    /// like a stack, nested checkpoints are possible
    fn checkpoint(&mut self) {
        self.trace_stack
            .push(TraceStackEntry::Enter("Creating checkpoint".to_string()));
        self.replacements.push();

        // This is relatively expensive if these lists are large, however, for now
        // this is a much simpler solution than attempting to roll-back replaced requirements
        // later
        self.checkpoints
            .push((self.requirements.clone(), self.constraints.clone()));
    }

    fn restore(&mut self) {
        self.replacements.discard_top();
        self.trace_stack.push(TraceStackEntry::Exit);

        let (requirements, constraints) = self
            .checkpoints
            .pop()
            .expect("Popped a checkpoint without any existing checkpoints.");

        self.requirements = requirements;
        self.constraints = constraints;
    }
}

impl TypeState {
    pub fn print_equations(&self) {
        for (lhs, rhs) in &self.equations {
            println!(
                "{} -> {}",
                format!("{lhs}").blue(),
                format!("{}", rhs.debug_resolve(self)).green()
            )
        }

        println!("\nReplacments:");

        for repl_stack in &self.replacements.all() {
            let replacements = { repl_stack.borrow().clone() };
            for (lhs, rhs) in replacements.iter().sorted() {
                println!(
                    "{} -> {} ({} -> {})",
                    format!("{}", lhs.inner).blue(),
                    format!("{}", rhs.inner).green(),
                    format!("{}", lhs.debug_resolve(self)).blue(),
                    format!("{}", rhs.debug_resolve(self)).green(),
                )
            }
            println!("---")
        }

        println!("\n Requirements:");

        for requirement in &self.requirements {
            println!("{:?}", requirement)
        }

        println!()
    }
}

#[must_use]
pub struct UnificationBuilder {
    lhs: TypeVarID,
    rhs: TypeVarID,
}
impl UnificationBuilder {
    pub fn commit(
        self,
        state: &mut TypeState,
        ctx: &Context,
    ) -> std::result::Result<TypeVarID, UnificationError> {
        state.unify(&self.lhs, &self.rhs, ctx)
    }
}

pub trait HasType: std::fmt::Debug {
    fn get_type(&self, state: &TypeState) -> TypeVarID {
        self.try_get_type(state)
            .unwrap_or(state.error_type.unwrap())
    }

    fn try_get_type(&self, state: &TypeState) -> Option<TypeVarID> {
        let id = self.get_type_impl(state);
        id.map(|id| state.get_replacement(&id))
    }

    fn get_type_impl(&self, state: &TypeState) -> Option<TypeVarID>;

    fn unify_with(&self, rhs: &dyn HasType, state: &TypeState) -> UnificationBuilder {
        UnificationBuilder {
            lhs: self.get_type(state),
            rhs: rhs.get_type(state),
        }
    }
}

impl HasType for TypeVarID {
    fn get_type_impl(&self, _state: &TypeState) -> Option<TypeVarID> {
        Some(*self)
    }
}
impl HasType for Loc<TypeVarID> {
    fn get_type_impl(&self, state: &TypeState) -> Option<TypeVarID> {
        self.inner.try_get_type(state)
    }
}
impl HasType for TypedExpression {
    fn get_type_impl(&self, state: &TypeState) -> Option<TypeVarID> {
        state.maybe_type_of(self).cloned()
    }
}
impl HasType for Expression {
    fn get_type_impl(&self, state: &TypeState) -> Option<TypeVarID> {
        state.maybe_type_of(&TypedExpression::Id(self.id)).cloned()
    }
}
impl HasType for Loc<Expression> {
    fn get_type_impl(&self, state: &TypeState) -> Option<TypeVarID> {
        state
            .maybe_type_of(&TypedExpression::Id(self.inner.id))
            .cloned()
    }
}
impl HasType for Pattern {
    fn get_type_impl(&self, state: &TypeState) -> Option<TypeVarID> {
        state.maybe_type_of(&TypedExpression::Id(self.id)).cloned()
    }
}
impl HasType for Loc<Pattern> {
    fn get_type_impl(&self, state: &TypeState) -> Option<TypeVarID> {
        state
            .maybe_type_of(&TypedExpression::Id(self.inner.id))
            .cloned()
    }
}
impl HasType for NameID {
    fn get_type_impl(&self, state: &TypeState) -> Option<TypeVarID> {
        state
            .maybe_type_of(&TypedExpression::Name(self.clone()))
            .cloned()
    }
}
