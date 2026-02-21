use std::collections::BTreeMap;

use num::ToPrimitive;

use local_impl::local_impl;
use mir::ValueName;
use mir::ValueNameSource;
use spade_common::location_info::WithLocation;
use spade_common::name::Path;
use spade_common::{location_info::Loc, name::NameID};
use spade_diagnostics::diag_anyhow;
use spade_diagnostics::diag_bail;
use spade_diagnostics::diagnostic::SuggestionParts;
use spade_diagnostics::Diagnostic;
use spade_hir::expression::CallKind;
use spade_hir::Binding;
use spade_hir::TypeSpec;
use spade_hir::{ExprKind, Expression, Pattern, Statement};
use spade_mir as mir;
use spade_types::ConcreteType;

use crate::Context;
use crate::ExprLocal;
use crate::{statement_list::StatementList, MirLowerable, NameIDExt, Result};

pub struct PipelineContext {
    /// Mapping from stage index to the corresponding enable signal, i.e. what
    /// `stage.ready` should map to. If the stage is unconditionally enabled,
    /// the corresponding value is `None`
    // NOTE: Current stage is being kept track of by [Context::Substitutions]
    pub ready_signals: Vec<Option<ValueName>>,
    /// Mapping from stage index to the corresponding valid signal. I.e. what
    /// `stage.valid` should map to. If the stage is always valid, the corresponding
    /// value is `None`
    pub valid_signals: Vec<Option<ValueName>>,
}

pub enum MaybePipelineContext {
    NotPipeline,
    Pipeline(PipelineContext),
}
impl MaybePipelineContext {
    /// Returns the pipeline context if we are in a pipeline, otherwise bails
    /// with a Diagnostic::bug on the specified Loc
    pub fn get<T>(&mut self, request_loc: &Loc<T>) -> Result<&mut PipelineContext> {
        match self {
            MaybePipelineContext::NotPipeline => {
                diag_bail!(request_loc, "Requesting pipeline context without pipeline")
            }
            MaybePipelineContext::Pipeline(ctx) => Ok(ctx),
        }
    }
}

pub fn handle_pattern(pat: &Pattern, live_vars: &mut Vec<NameID>) {
    // Add this variable to the live vars list
    for name in pat.get_names() {
        live_vars.push(name.inner.clone());
    }
}

pub fn handle_statement(
    statement: &Loc<Statement>,
    ctx: &mut Context,
    name_map: &mut BTreeMap<NameID, NameID>,
    statements: &mut StatementList,
    clock: &Loc<NameID>,
    local_conds: &mut Vec<Option<ValueName>>,
    stage_enable_names: &mut Vec<Option<ValueName>>,
    current_stage: &mut usize,
) -> Result<()> {
    match &statement.inner {
        Statement::Error => {}
        Statement::Binding(Binding {
            pattern: pat,
            value: expr,
            wal_trace: _,
            ty: _,
        }) => {
            let time = expr.inner.available_in(ctx)?;
            for name in pat.get_names() {
                let ty = ctx.types.concrete_type_of_name(
                    &name,
                    ctx.symtab.symtab(),
                    &ctx.item_list.types,
                )?;

                ctx.subs
                    .set_available(name, time.unwrap_or(0), *current_stage, ty)
            }
        }
        Statement::Expression(_) => {}
        Statement::Register(reg) => {
            let time = reg.value.available_in(ctx)?;
            for name in reg.pattern.get_names() {
                let ty = ctx.types.concrete_type_of_name(
                    &name,
                    ctx.symtab.symtab(),
                    &ctx.item_list.types,
                )?;

                ctx.subs
                    .set_available(name, time.unwrap_or(0), *current_stage, ty)
            }
        }
        Statement::Declaration(_) => {
            // Declarations have no effect on pipeline state
        }
        Statement::PipelineRegMarker(extra) => {
            let local_cond = match extra {
                Some(spade_hir::PipelineRegMarkerExtra::Condition(cond)) => {
                    statements.append(cond.lower(ctx)?);
                    Some(cond.variable(ctx)?)
                }
                Some(spade_hir::PipelineRegMarkerExtra::Count {
                    count,
                    count_typeexpr_id: _,
                }) => {
                    diag_bail!(count, "Expected to have lowered multiplied pipeline stage")
                }
                None => None,
            };
            local_conds.push(local_cond);
            let live_vars = ctx.subs.next_stage(ctx.symtab);

            // Generate pipeline regs for previous live vars
            for reg in &live_vars {
                if name_map
                    .insert(reg.new.clone(), reg.original.inner.clone())
                    .is_some()
                {
                    // NOTE: Panic because this should not occur in user code
                    panic!("inserted duplicate in name map");
                }

                let reg_type = ctx
                    .types
                    .concrete_type_of_name(
                        &reg.original,
                        ctx.symtab.symtab(),
                        &ctx.item_list.types,
                    )?
                    .to_mir_type();
                // If this stage has an enable signal, generate a mux to optionally select
                // the previous value, otherwise use the previous value right away
                let next = if let Some(enable) = &stage_enable_names[*current_stage] {
                    let next_name = ValueName::Expr(ctx.idtracker.next());
                    statements.push_secondary(
                        mir::Statement::Binding(mir::Binding {
                            name: next_name.clone(),
                            operator: mir::Operator::Select,
                            operands: vec![
                                enable.clone(),
                                reg.previous.value_name(),
                                reg.new.value_name(),
                            ],
                            ty: reg_type.clone(),
                            loc: Some(statement.loc()),
                        }),
                        &reg.original,
                        "Pipeline enable mux",
                    );
                    next_name
                } else {
                    reg.previous.value_name()
                };

                statements.push_secondary(
                    mir::Statement::Register(mir::Register {
                        name: reg
                            .new
                            .value_name_with_alternate_source(ValueNameSource::Name(
                                reg.original.inner.clone(),
                            )),
                        ty: reg_type,
                        clock: clock.value_name(),
                        reset: None,
                        initial: None,
                        value: next,
                        traced: None,
                        // NOTE: Do we/can we also want to point to the declaration
                        // of the variable?
                        loc: Some(statement.loc()),
                    }),
                    &reg.original,
                    "Pipelined",
                );
            }

            *current_stage += 1;
        }
        Statement::Label(_) => {
            // Labels have no effect on codegen
        }
        Statement::Assert(_) => {
            // Assertions have no effect on pipeline state
        }
        Statement::WalSuffixed { .. } => {
            // Wal suffixes have no effect on pipeline state
        }
        Statement::Set { .. } => {
            // Set have no effect on pipeline state
        }
    }
    Ok(())
}

pub fn lower_pipeline<'a>(
    hir_inputs: &Vec<(Loc<NameID>, Loc<TypeSpec>)>,
    body: &Loc<Expression>,
    statements: &mut StatementList,
    ctx: &mut Context,
    // Map of names generated by codegen to the original name in the source code.
    name_map: &mut BTreeMap<NameID, NameID>,
    is_nonstatic_method: bool,
) -> Result<()> {
    let clock = &hir_inputs[if is_nonstatic_method { 1 } else { 0 }].0;

    let (body_statements, _) = if let ExprKind::Block(block) = &body.kind {
        (&block.statements, &block.result)
    } else {
        panic!("Pipeline body was not a block");
    };

    for (name, _) in hir_inputs {
        let ty =
            ctx.types
                .concrete_type_of_name(name, ctx.symtab.symtab(), &ctx.item_list.types)?;

        ctx.subs.set_available(name.clone(), 0, 0, ty)
    }

    let num_stages = body_statements
        .iter()
        .filter(|s| matches!(&s.inner, Statement::PipelineRegMarker(_)))
        .count();

    // If we have stage enable signals, we need to pre-allocate some variables
    // for the relevant stages, because the enable signal depends on downstream stages.
    // This builds a list of ValueNames which we need to fill in down the line, and
    // which will contain the enable signals.
    let mut stage_enable_names = vec![];
    let mut has_enable = false;
    for statement in body_statements.iter().rev() {
        match &statement.inner {
            Statement::PipelineRegMarker(cond) => {
                // Once we encounter the *last* reg statement with an enable, subsequent stages
                // have enables
                if cond.is_some() {
                    has_enable = true;
                }

                if has_enable {
                    let name = ctx.symtab.new_name(Path::from_strs(&[&format!(
                        "#s{}_enable",
                        num_stages - stage_enable_names.len()
                    )]));
                    stage_enable_names.push(Some(name.value_name()));
                } else {
                    stage_enable_names.push(None)
                }
            }
            _ => {}
        }
    }
    // We generated these in reverse order, so we need to reverse them back
    stage_enable_names.reverse();

    let mut current_stage = 0;
    let mut local_conds = vec![];
    for statement in body_statements {
        handle_statement(
            statement,
            ctx,
            name_map,
            statements,
            clock,
            &mut local_conds,
            &mut stage_enable_names,
            &mut current_stage,
        )?
    }

    // Codegen enable signals for the stages that need them. We need to generate them
    // in reverse order because upstream enables depend on downstream
    let mut current_enable = None;
    for (local_cond, enable_name) in local_conds.iter().zip(stage_enable_names.iter()).rev() {
        match (local_cond, &current_enable) {
            // First time we find a condition, alias it to the enable name for the current stage
            (Some(local), None) => {
                let name = enable_name
                    .clone()
                    .expect("No enable name for first stage that needs one");
                statements.push_anonymous(mir::Statement::Binding(mir::Binding {
                    name: name.clone(),
                    operator: mir::Operator::Alias,
                    operands: vec![local.clone()],
                    ty: mir::types::Type::Bool,
                    loc: None,
                }));
                current_enable = Some(name.clone());
            }
            (None, Some(prev)) => {
                let name = enable_name
                    .clone()
                    .expect("No enable name for first stage that needs one");
                // Since we have no new conditions, we can just alias the one from the previous
                // stage
                statements.push_anonymous(mir::Statement::Binding(mir::Binding {
                    name: name.clone(),
                    operator: mir::Operator::Alias,
                    operands: vec![prev.clone()],
                    ty: mir::types::Type::Bool,
                    loc: None,
                }));
                current_enable = Some(name.clone());
            }
            (Some(local), Some(prev)) => {
                let name = enable_name
                    .clone()
                    .expect("No enable name for first stage that needs one");
                statements.push_anonymous(mir::Statement::Binding(mir::Binding {
                    name: name.clone(),
                    operator: mir::Operator::LogicalAnd,
                    operands: vec![local.clone(), prev.clone()],
                    ty: mir::types::Type::Bool,
                    loc: None,
                }));
                current_enable = Some(name.clone());
            }
            (None, None) => {}
        }
    }

    let mut ready_signals = stage_enable_names.into_iter().collect::<Vec<_>>();
    // NOTE: The last stage needs a ready signal because you *can* use `stage.ready`
    // after the last `reg` in the final output expression, but it will be `None` because
    // there is no way to for it to be disabled
    ready_signals.push(None);

    /*
    The full logic for a a stage's validity looks like this

    decl valid;
    let valid_mux = if enable {prev_valid} else {valid};

    // If this is the most downstream stage that stalls
    let valid_next = if downstream_enable && !local_cond {
        false
    } else {
        valid_mux
    };
    // Simplified
    let valid_next = !(downstream_enable && !local_cond) && valid_mux
    reg(clk) valid = valid_next;

    It corresponds to this hardware

          <prev valid>
               |
      +----+   |               <local cond>
      |    |   |                    |
      |  __v___v__                  v
      |  \ 0   1 / <---------------{&}       // valid_mux, valid_select
      |      |                      ^        // (local_valid_select is the non-local enable)
      |      |        <local cond>  |
      |      |             |        |
      |      |     +--o<|--+        |
      |      |     v                |
      |     {&}<-o{&}<--------------+        // valid_next, stall_here_inv, stall_here
      |      |                      |        // downstream_inv
      | _____v____                  |
      | |> valid |                  |        // (valid_name) valid_signals[i]
      |      |                      |
      +------+                      |
             |                      |
        <new valid>        <downstream enable>
    */

    // Codegen valid signals
    // The first stage, before any `reg` statement is valid, so we can initialize the vector
    // with `None`
    let mut valid_signals = vec![None];
    let mut prev_valid: Option<ValueName> = None;
    for (i, local_cond) in local_conds.into_iter().enumerate() {
        let downstream_enable = ready_signals.get(i + 1).cloned().flatten().or_const_true();
        let valid_select = &ready_signals[i];

        let valid_name = ctx
            .symtab
            .new_name(Path::from_strs(&[&format!("#s{}_valid", i + 1)]))
            .value_name();

        let valid_mux = constexpr_select(
            prev_valid.clone().or_const_true(),
            MaybeConst::Val(valid_name.clone()),
            valid_select.clone().or_const_true(),
            statements,
            ctx,
        );

        let local_cond_inv = constexpr_inv(local_cond.or_const_true(), statements, ctx);
        let stall_here = constexpr_and(local_cond_inv, downstream_enable, statements, ctx);
        let stall_here_inv = constexpr_inv(stall_here, statements, ctx);
        let valid_next = constexpr_and(valid_mux, stall_here_inv, statements, ctx);

        match valid_next {
            MaybeConst::Val(next) => {
                statements.push_anonymous(mir::Statement::Register(mir::Register {
                    name: valid_name.clone(),
                    ty: mir::types::Type::Bool,
                    clock: clock.value_name(),
                    reset: None,
                    initial: None,
                    value: next,
                    loc: None,
                    traced: None,
                }));
                prev_valid = Some(valid_name.clone());
                valid_signals.push(Some(valid_name))
            }
            MaybeConst::Const(true) => valid_signals.push(None),
            MaybeConst::Const(false) => {
                diag_bail!(body, "Found a stage which is always invalid")
            }
        }
    }

    *ctx.pipeline_context = MaybePipelineContext::Pipeline(PipelineContext {
        ready_signals,
        valid_signals,
    });

    let result_latency = body.available_in(ctx)?.unwrap_or(0);
    if result_latency != 0 {
        let ExprKind::Block(block) = &body.kind else {
            diag_bail!(body, "Unit result was not a block")
        };
        let Some(result) = &block.result else {
            diag_bail!(body, "Found a block with latency but without a result");
        };
        return Err(
            Diagnostic::error(result, "Use of result before it is ready")
                .primary_label("Use of result before it is ready")
                .span_suggest_multipart(
                    "Consider binding the result to a variable and adding the required pipeline stages",
                    SuggestionParts::new()
                        .part(result.start_span(), "let result = ")
                        .part(result.end_span(), format!("; reg * {result_latency}; result"))
                )
        );
    }

    Ok(())
}

pub enum MaybeConst {
    Val(ValueName),
    Const(bool),
}

impl MaybeConst {
    fn to_value_name(self, statements: &mut StatementList, ctx: &mut Context) -> ValueName {
        match self {
            MaybeConst::Val(n) => n,
            MaybeConst::Const(v) => {
                let id = ctx.idtracker.next();
                let new_name = mir::ValueName::Expr(id);

                statements.push_anonymous(mir::Statement::Constant(
                    new_name.clone(),
                    mir::types::Type::Bool,
                    mir::ConstantValue::Bool(v),
                ));

                new_name
            }
        }
    }
}

#[local_impl::local_impl]
impl OptionExt for Option<ValueName> {
    fn or_const_true(self) -> MaybeConst {
        match self {
            Some(v) => MaybeConst::Val(v),
            None => MaybeConst::Const(true),
        }
    }
}

pub fn constexpr_and(
    l: MaybeConst,
    r: MaybeConst,
    statements: &mut StatementList,
    ctx: &mut Context,
) -> MaybeConst {
    match (l, r) {
        (MaybeConst::Val(l), MaybeConst::Val(r)) => {
            let new_name = mir::ValueName::Expr(ctx.idtracker.next());

            statements.push_anonymous(mir::Statement::Binding(mir::Binding {
                name: new_name.clone(),
                operator: mir::Operator::LogicalAnd,
                operands: vec![l.clone(), r.clone()],
                ty: mir::types::Type::Bool,
                loc: None,
            }));

            MaybeConst::Val(new_name)
        }
        (MaybeConst::Const(false), _) => MaybeConst::Const(false),
        (_, MaybeConst::Const(false)) => MaybeConst::Const(false),
        (l, MaybeConst::Const(true)) => l,
        (MaybeConst::Const(true), r) => r,
    }
}

pub fn constexpr_select(
    on_true: MaybeConst,
    on_false: MaybeConst,
    select: MaybeConst,
    statements: &mut StatementList,
    ctx: &mut Context,
) -> MaybeConst {
    match (on_true, on_false, select) {
        (t, f, MaybeConst::Val(sel)) => {
            let new_name = mir::ValueName::Expr(ctx.idtracker.next());

            let t = t.to_value_name(statements, ctx);
            let f = f.to_value_name(statements, ctx);

            statements.push_anonymous(mir::Statement::Binding(mir::Binding {
                name: new_name.clone(),
                operator: mir::Operator::Select,
                operands: vec![sel, t, f],
                ty: mir::types::Type::Bool,
                loc: None,
            }));

            MaybeConst::Val(new_name)
        }
        (t, _, MaybeConst::Const(true)) => t,
        (_, f, MaybeConst::Const(false)) => f,
    }
}

pub fn constexpr_inv(
    input: MaybeConst,
    statements: &mut StatementList,
    ctx: &mut Context,
) -> MaybeConst {
    match input {
        MaybeConst::Val(name) => {
            let new_name = mir::ValueName::Expr(ctx.idtracker.next());
            statements.push_anonymous(mir::Statement::Binding(mir::Binding {
                name: new_name.clone(),
                operator: mir::Operator::Not,
                operands: vec![name],
                ty: mir::types::Type::Bool,
                loc: None,
            }));

            MaybeConst::Val(new_name)
        }
        MaybeConst::Const(true) => MaybeConst::Const(false),
        MaybeConst::Const(false) => MaybeConst::Const(true),
    }
}

/// Computes the time at which the specified expressions will be available. If there
/// is a mismatch, an error is returned
pub fn try_compute_availability(
    exprs: &[impl std::borrow::Borrow<Loc<Expression>>],
    ctx: &Context,
) -> Result<Option<usize>> {
    let mut result = None;
    for expr in exprs {
        let a = expr.borrow().available_in(ctx)?;

        result = match (a, result) {
            (a, None) => a,
            (None, prev) => prev,
            (Some(a), Some(prev)) if a == prev => result,
            // NOTE: Safe index. This branch can only be reached in iteration 2 of the loop
            (Some(a), Some(_)) => {
                let prev = exprs[0].borrow().clone().map(|_| result.unwrap());
                let new = expr.borrow().clone().map(|_| a);
                return Err(Diagnostic::error(
                    new,
                    "All subexpressions need the same pipeline delay",
                )
                .primary_label(format!("This has delay {new}"))
                .secondary_label(prev, format!("But this has delay {prev}")));
            }
        }
    }
    Ok(result)
}

#[local_impl]
impl PipelineAvailability for Expression {
    // Computes the availability of an expression. Returns `None` if the expression is always
    // available, i.e. it is constant or a port
    fn available_in(&self, ctx: &Context) -> Result<Option<usize>> {
        // Port types are considered always available
        match ctx.types.concrete_type_of(
            &self.clone().nowhere(),
            ctx.symtab.symtab(),
            &ctx.item_list.types,
        ) {
            Ok(ty) => {
                if ty.is_port() {
                    return Ok(None);
                }
            }
            _ => {}
        }

        match &self.kind {
            ExprKind::Error => Ok(None),
            ExprKind::Identifier(_) => Ok(Some(0)),
            ExprKind::IntLiteral(_, _) => Ok(None),
            ExprKind::TypeLevelInteger(_) => Ok(None),
            ExprKind::BoolLiteral(_) => Ok(None),
            ExprKind::TypeLevelBool(_) => Ok(None),
            ExprKind::TriLiteral(_) => Ok(None),
            ExprKind::CreatePorts => Ok(None),
            ExprKind::StageReady | ExprKind::StageValid => Ok(Some(0)),
            ExprKind::TupleLiteral(inner) => try_compute_availability(inner, ctx),
            ExprKind::ArrayLiteral(elems) => try_compute_availability(elems, ctx),
            ExprKind::ArrayShorthandLiteral(inner, _) => {
                try_compute_availability(&[inner.as_ref()], ctx)
            }
            ExprKind::Index(lhs, idx) => {
                try_compute_availability(&[lhs.as_ref(), idx.as_ref()], ctx)
            }
            ExprKind::RangeIndex {
                target,
                start: _,
                end: _,
            } => try_compute_availability(&[target.as_ref()], ctx),
            ExprKind::TupleIndex(lhs, _) => lhs.inner.available_in(ctx),
            ExprKind::FieldAccess(lhs, _) => lhs.inner.available_in(ctx),
            ExprKind::BinaryOperator(lhs, _, rhs) => {
                try_compute_availability(&[lhs.as_ref(), rhs.as_ref()], ctx)
            }
            ExprKind::UnaryOperator(_, val) => val.inner.available_in(ctx),
            ExprKind::Match(_, values) => try_compute_availability(
                &values
                    .iter()
                    .flat_map(|(_, if_cond, expr)| [if_cond.as_ref(), Some(expr)])
                    .flatten()
                    .collect::<Vec<_>>(),
                ctx,
            ),
            ExprKind::Block(inner) => {
                // NOTE: Do we want to allow delayed values inside blocks? That could lead to some
                // strange issues like
                // {
                //      let x = inst(10) subpipe();
                //      x // Will appear as having availability 1
                // }
                if let Some(result) = &inner.result {
                    result.available_in(ctx)
                } else {
                    Ok(None)
                }
            }
            ExprKind::Call { kind, args, .. } => {
                // FIXME: Re-add this check to allow nested pipelines
                let arg_availability = try_compute_availability(
                    &args
                        .expressions()
                        .iter()
                        .map(|arg| *arg)
                        .collect::<Vec<_>>(),
                    ctx,
                )?;
                match &kind {
                    CallKind::Pipeline {
                        inst_loc,
                        depth,
                        depth_typeexpr_id,
                    } => {
                        match ctx.types.concrete_type_of(
                            depth_typeexpr_id.at_loc(depth),
                            ctx.symtab.symtab(),
                            &ctx.item_list.types,
                        ) {
                            Ok(ConcreteType::Integer(val)) => Ok(Some(
                                arg_availability.unwrap_or(0)
                                    + val.to_usize().ok_or_else(|| {
                                        diag_anyhow!(
                                            inst_loc,
                                            "Inferred more than `usize::MAX` pipeline stages"
                                        )
                                    })?,
                            )),
                            Ok(_) => diag_bail!(depth, "Found non-integer for pipeline depth"),
                            Err(_) => Err(Diagnostic::error(
                                depth,
                                "The latency of this pipeline instantiation is not known",
                            )
                            .primary_label("Unknown latency")),
                        }
                    }
                    _ => Ok(arg_availability),
                }
            }
            ExprKind::If(_, t, f) => try_compute_availability(&[t.as_ref(), f.as_ref()], ctx),
            ExprKind::PipelineRef { .. } => Ok(Some(0)),
            ExprKind::TypeLevelIf(cond, _, _) => diag_bail!(
                cond,
                "Type level if should already have been lowered by this point"
            ),
            ExprKind::MethodCall { name, .. } => diag_bail!(
                name,
                "Method call should already have been lowered by this point"
            ),
            ExprKind::StaticUnreachable(message) => {
                diag_bail!(
                    message,
                    "Static unreachable during pipeline lowering ({message})"
                )
            }
            ExprKind::LambdaDef { .. } => {
                panic!("Lambda def should have been lowered at this point")
            }
            ExprKind::Null => {
                panic!("Null expression during pipeline lowering")
            }
        }
    }
}
