use std::collections::HashMap;

use spade_common::location_info::{Loc, WithLocation};
use spade_diagnostics::{diag_bail, Diagnostic};
use spade_hir::{
    domains::{DomainConstraint, DomainName},
    param_util::{match_args_with_params, Argument},
    pretty_debug::PrettyDebug,
    Binding, Expression, Parameter, Pattern, PatternArgument, Register, Statement, Unit,
};
use spade_typeinference::{
    equation::{TypeVar, TypeVarID},
    HasType,
};
use spade_types::KnownType;

use crate::{
    domain_var::LocExt, tracing::TraceEntry, Context, DomainState, DomainVar, DomainedExpression,
    HasDomain, Result, TypeVarIDExt,
};

impl DomainState {
    pub fn visit_unit(&mut self, unit: &Loc<Unit>, ctx: &Context) -> Result<()> {
        let result = self.visit_unit_inner(unit, ctx);
        self.pipeline_domain = None;
        result
    }
    pub fn visit_unit_inner(&mut self, unit: &Loc<Unit>, ctx: &Context) -> Result<()> {
        let _t = self.trace_scope(|| TraceEntry::VisitingUnit(unit.name.to_string()));

        for domain in &unit.head.domains {
            let var = self.add_domain_var(DomainVar::Known(
                domain.name.clone(),
                domain.constraints.clone(),
            ));
            let name = match &domain.name {
                DomainName::Annonymous => DomainedExpression::AnnonymousOuter(unit.head.name.loc()),
                DomainName::Named(name) => DomainedExpression::Name(name.inner.clone()),
            };
            self.equations.insert(name, var);
        }

        if unit.head.unit_kind.is_pipeline() {
            let dexpr = match &unit
                .head
                .inputs
                .0
                .first()
                .map(|i| &i.domain)
                .ok_or_else(|| Diagnostic::bug(unit, "Pipeline without arguments"))?
            {
                DomainName::Annonymous => DomainedExpression::AnnonymousOuter(unit.head.name.loc()),
                DomainName::Named(name) => DomainedExpression::Name(name.inner.clone()),
            };

            let pipeline_domain = dexpr.get_domain(self);
            match pipeline_domain.resolve_domain(self) {
                DomainVar::Error => {}
                DomainVar::Unknown(_) => {
                    diag_bail!(&unit.head.name, "First argument had unknown domain")
                }
                DomainVar::Known(_, constraints) => {
                    if let Some(c) = constraints
                        .iter()
                        .find(|c| matches!(c.inner, DomainConstraint::NoClock))
                    {
                        self.diags.push(Diagnostic::error(
                            c,
                            "The domain of a pipeline cannot be NoClock",
                        ))
                    }
                }
            }
            self.pipeline_domain = Some(pipeline_domain)
        }

        for (
            Parameter {
                no_mangle: _,
                name: _,
                ty: _,
                domain,
                field_translator: _,
            },
            (name_id, _),
        ) in unit.head.inputs.0.iter().zip(unit.inputs.iter())
        {
            let dexpr = match &domain {
                DomainName::Annonymous => DomainedExpression::AnnonymousOuter(unit.head.name.loc()),
                DomainName::Named(name) => DomainedExpression::Name(name.inner.clone()),
            };

            dexpr
                .get_domain(self)
                .insert_for_domained(DomainedExpression::Name(name_id.inner.clone()), self);
        }

        let output_domain = unit
            .head
            .output_type
            .as_ref()
            .map(|(domain, _)| {
                match domain {
                    DomainName::Annonymous => {
                        DomainedExpression::AnnonymousOuter(unit.head.name.loc())
                    }
                    DomainName::Named(name) => DomainedExpression::Name(name.inner.clone()),
                }
                .get_domain(self)
            })
            // If there is no output type, we can support any domain for the "output" since
            // there will not be an output
            .unwrap_or_else(|| self.new_any());

        // TODO: That Loc is all wrong
        self.check_expression(
            &unit.body,
            output_domain.at_loc(&unit.head.output_type().loc()),
            ctx,
        )?;
        Ok(())
    }

    fn visit_statement(&mut self, stmt: &Loc<Statement>, ctx: &Context) -> Result<()> {
        let _t = self.trace_scope(|| TraceEntry::VisitingStatement(stmt.pretty_debug()));

        match &stmt.inner {
            Statement::Error => Ok(()),
            Statement::Binding(Binding {
                pattern,
                ty: _,
                value,
                wal_trace: _,
            }) => {
                let pattern_ty = self.synth_pattern(pattern, ctx)?;
                self.check_expression(value, pattern_ty.at_loc(pattern), ctx)?;

                Ok(())
            }
            Statement::Expression(expr) => {
                self.synth_expression(expr, ctx)?;
                Ok(())
            }
            Statement::Register(Register {
                pattern,
                clock,
                reset,
                initial,
                value,
                value_type: _,
                attributes: _,
            }) => {
                // Ensure that there is a clock in this domain
                let value_domain =
                    self.new_with_constraints(vec![DomainConstraint::HasClock.at_loc(stmt)]);

                self.check_expression(value, value_domain.at_loc(stmt), ctx)?;
                self.check_expression(clock, value_domain.at_loc(value), ctx)?;

                if let Some((rst_trig, rst_val)) = reset {
                    self.check_expression(rst_trig, value_domain.at_loc(value), ctx)?;
                    self.check_expression(rst_val, value_domain.at_loc(value), ctx)?;
                }
                if let Some(initial) = initial {
                    self.check_expression(initial, value_domain.at_loc(value), ctx)?;
                }

                self.check_pattern(pattern, value_domain.at_loc(value), ctx)?;

                Ok(())
            }
            Statement::Declaration(names) => {
                for name in names {
                    self.new_any()
                        .insert_for_domained(DomainedExpression::Name(name.inner.clone()), self);
                }

                Ok(())
            }
            Statement::PipelineRegMarker(_) => Ok(()),
            Statement::Label(_) => Ok(()),
            // We won't enforce anything for assertions since users may want to check
            // cross domain things here
            Statement::Assert(_) => Ok(()),
            Statement::Set { target, value } => {
                let value_domain = self.synth_expression(value, ctx)?;
                self.check_expression(target, value_domain.at_loc(value), ctx)?;
                Ok(())
            }
            Statement::WalSuffixed { .. } => Ok(()),
        }
    }

    fn synth_pattern(&mut self, pattern: &Loc<Pattern>, ctx: &Context) -> Result<TypeVarID> {
        let _t = self.trace_scope(|| TraceEntry::SynthPattern(pattern.pretty_debug()));

        let result = match &pattern.inner.kind {
            spade_hir::PatternKind::Integer(_) | spade_hir::PatternKind::Bool(_) => self.new_any(),
            spade_hir::PatternKind::Name { name, pre_declared } => {
                if *pre_declared {
                    // We don't place additional constraints on this with a pattern, but we do
                    // need to lookup the name
                    name.get_domain(self)
                } else {
                    let var_id = self.new_any();
                    var_id.insert_for_domained(DomainedExpression::Name(name.inner.clone()), self);
                    var_id
                }
            }
            spade_hir::PatternKind::Tuple(members) | spade_hir::PatternKind::Array(members) => {
                if members.is_empty() {
                    self.new_any()
                } else {
                    let first_domain = self.synth_pattern(&members[0], ctx)?;
                    for member in &members[1..] {
                        self.check_pattern(member, first_domain.at_loc(&members[0]), ctx)?;
                    }
                    first_domain
                }
            }
            spade_hir::PatternKind::Type(_, args) => {
                if args.is_empty() {
                    self.new_any()
                } else {
                    let first_domain = self.synth_pattern(&args[0].value, ctx)?;
                    for PatternArgument {
                        target: _,
                        value,
                        kind: _,
                    } in &args[1..]
                    {
                        self.check_pattern(value, first_domain.at_loc(&args[0].value), ctx)?;
                    }
                    first_domain
                }
            }
        };

        result.insert_for_domained(DomainedExpression::Id(pattern.id), self);
        Ok(result)
    }

    fn check_pattern(
        &mut self,
        pattern: &Loc<Pattern>,
        expected: Loc<TypeVarID>,
        ctx: &Context,
    ) -> Result<()> {
        let _t = self.trace_scope(|| TraceEntry::CheckPattern(pattern.pretty_debug()));
        // All patterns have a synthesizeable type if we look hard enough
        let inner = self.synth_pattern(pattern, ctx)?;

        // NOTE: There is a potential for optimization here if we don't merge vars that are
        // the same
        let merged = inner
            .resolve_domain(self)
            .at_loc(pattern)
            .merge_domains(&expected.map(|d| d.resolve_domain(self)))?;

        let merged_id = self.add_domain_var(merged);

        self.replace(expected.inner, merged_id);
        self.replace(inner, merged_id);

        Ok(())
    }

    fn synth_expression(&mut self, expr: &Loc<Expression>, ctx: &Context) -> Result<TypeVarID> {
        let _t = self.trace_scope(|| TraceEntry::SynthExpr(expr.pretty_debug()));
        let result = match &expr.inner.kind {
            spade_hir::ExprKind::Error => Ok(self.error_domain.unwrap()),
            spade_hir::ExprKind::Identifier(name) => Ok(name.get_domain(self)),
            spade_hir::ExprKind::PipelineRef {
                stage: _,
                name,
                declares_name: _,
                depth_typeexpr_id: _,
            } => Ok(name.get_domain(self)),
            spade_hir::ExprKind::TupleLiteral(members) => {
                // If there are no members, we can be in any domain
                if members.is_empty() {
                    Ok(self.new_any())
                } else {
                    let inner_domain = self.synth_expression(&members[0], ctx)?;
                    for member in &members[1..] {
                        self.check_expression(member, inner_domain.at_loc(&members[0]), ctx)
                            .map_err(|e| e.help("All tuple members must be in the same domain"))?;
                    }

                    Ok(inner_domain)
                }
            }
            spade_hir::ExprKind::ArrayLiteral(members) => {
                // If there are no members, we can be in any domain
                if members.is_empty() {
                    Ok(self.new_any())
                } else {
                    let inner_domain = self.synth_expression(&members[0], ctx)?;
                    for member in &members[1..] {
                        self.check_expression(member, inner_domain.at_loc(&members[0]), ctx)
                            .map_err(|e| e.help("All array members must be in the same domain"))?;
                    }

                    Ok(inner_domain)
                }
            }
            spade_hir::ExprKind::ArrayShorthandLiteral(inner, _) => {
                self.synth_expression(inner, ctx)
            }

            spade_hir::ExprKind::IntLiteral(_, _)
            | spade_hir::ExprKind::BoolLiteral(_)
            | spade_hir::ExprKind::BitLiteral(_)
            | spade_hir::ExprKind::TypeLevelInteger(_)
            | spade_hir::ExprKind::CreatePorts => Ok(self.new_any()),

            // For items whose domain depends on sub-expressions, we can synthesize those
            spade_hir::ExprKind::Index(op, _)
            | spade_hir::ExprKind::RangeIndex { target: op, .. }
            | spade_hir::ExprKind::TupleIndex(op, _)
            | spade_hir::ExprKind::UnaryOperator(_, op)
            | spade_hir::ExprKind::FieldAccess(op, _) => self.synth_expression(op, ctx),

            spade_hir::ExprKind::BinaryOperator(opa, _, opb) => {
                let expected = self.synth_expression(opa, ctx)?;
                self.check_expression(opb, expected.at_loc(opa), ctx)?;
                Ok(expected)
            }

            // If we're in synthesis mode and find expressions which need checking,
            // we can return any since we can always fall back on the annonymous domain
            spade_hir::ExprKind::Call {
                kind: _,
                callee,
                args,
                turbofish: _,
                safety: _,
            } => {
                let callee = ctx.symtab.unit_by_id(&callee);

                let calee_domains = callee
                    .domains
                    .iter()
                    .map(|dom| {
                        (
                            &dom.name,
                            self.new_with_constraints(dom.constraints.clone()),
                        )
                    })
                    .collect::<HashMap<_, _>>();

                for Argument {
                    target,
                    value,
                    target_type: (target_domain, _target_type),
                    kind: _,
                } in match_args_with_params(args, &callee.inputs.inner, false)?
                {
                    let domain = *calee_domains.get(target_domain).ok_or_else(|| {
                        Diagnostic::bug(
                            target,
                            "The domain of this parameter is not in the domain list",
                        )
                    })?;

                    self.check_expression(value, domain.at_loc(&target), ctx)?;
                }

                let output_domain = match &callee.output_type {
                    Some((domain_name, _)) => *calee_domains.get(&domain_name).ok_or_else(|| Diagnostic::bug(&callee.name, "The output domain of this function was not declared in the domain list"))?,
                    None => {
                        self.new_any()
                    }
                };

                Ok(output_domain)
            }

            spade_hir::ExprKind::Match(cond, branches) => {
                let expected = self.synth_expression(cond, ctx)?;
                for (pat, val) in branches {
                    self.check_pattern(pat, expected.at_loc(cond), ctx)?;
                    self.check_expression(val, expected.at_loc(cond), ctx)?;
                }
                Ok(expected)
            }
            spade_hir::ExprKind::Block(block) => {
                for statement in &block.statements {
                    self.visit_statement(&statement, ctx)?;
                }
                if let Some(result) = &block.result {
                    self.synth_expression(result, ctx)
                } else {
                    Ok(self.new_any())
                }
            }
            spade_hir::ExprKind::If(cond, on_true, on_false) => {
                let expected = self.synth_expression(cond, ctx)?;
                self.check_expression(on_true, expected.at_loc(cond), ctx)?;
                self.check_expression(on_false, expected.at_loc(cond), ctx)?;
                Ok(expected)
            }
            spade_hir::ExprKind::TypeLevelIf(cond, on_true, on_false) => {
                match cond.get_type(ctx.types).resolve(ctx.types) {
                    TypeVar::Known(_, KnownType::Bool(val), _) => {
                        if *val {
                            self.synth_expression(on_true, ctx)
                        } else {
                            self.synth_expression(on_false, ctx)
                        }
                    }
                    _other => {
                        diag_bail!(cond, "Found non-bool in gen if condition")
                    }
                }
            }
            spade_hir::ExprKind::StageValid | spade_hir::ExprKind::StageReady => {
                self.pipeline_domain.ok_or_else(|| {
                    Diagnostic::bug(expr, "Stage ready/valid without a present pipeline domain")
                })
            }
            spade_hir::ExprKind::StaticUnreachable(_) => Ok(self.new_any()),
            spade_hir::ExprKind::Null => Ok(self.new_any()),

            spade_hir::ExprKind::MethodCall { .. } => {
                diag_bail!(expr, "Method should be lowered already")
            }
            spade_hir::ExprKind::LambdaDef { .. } => {
                diag_bail!(expr, "Lambda should be lowered already")
            }
        }?;
        result.insert_for_domained(DomainedExpression::Id(expr.id), self);
        Ok(result)
    }

    fn check_expression(
        &mut self,
        expr: &Loc<Expression>,
        expected: Loc<TypeVarID>,
        ctx: &Context,
    ) -> Result<()> {
        let _t = self.trace_scope(|| TraceEntry::CheckExpr {
            expr: expr.inner.clone(),
            expected: expected.resolve_domain(self).clone(),
        });
        let self_domain = match &expr.inner.kind {
            spade_hir::ExprKind::Error => self.synth_expression(expr, ctx),
            spade_hir::ExprKind::Identifier(_) |
            // Pipeline refs are just spicy identifiers
            // NOTE: This only holds until pipelines get upgraded to domains
            spade_hir::ExprKind::PipelineRef {
                stage: _,
                name: _,
                declares_name: _,
                depth_typeexpr_id: _,
            } => self.synth_expression(expr, ctx),

            // Literals can be in any domain, so check cannot fail
            spade_hir::ExprKind::IntLiteral(_, _)
            | spade_hir::ExprKind::BoolLiteral(_)
            | spade_hir::ExprKind::BitLiteral(_)
            | spade_hir::ExprKind::TypeLevelInteger(_)
            | spade_hir::ExprKind::CreatePorts |

            // Constructors of stuff end up in the same domain as their constituent parts,
            // if they match, otherwise there is an error
            spade_hir::ExprKind::TupleLiteral(_) |
            spade_hir::ExprKind::ArrayLiteral(_) |
            spade_hir::ExprKind::ArrayShorthandLiteral(_, _) => self.synth_expression(expr, ctx),

            spade_hir::ExprKind::TypeLevelIf(_, _, _) => self.synth_expression(expr, ctx),

            // Operators and friends have to have the same domain on all branches. We'll group
            // these based on their arity
            spade_hir::ExprKind::Index(_, _) |
            spade_hir::ExprKind::BinaryOperator(_, _, _) => {
                self.synth_expression(expr, ctx)
            },

            spade_hir::ExprKind::UnaryOperator(_, op) |
            spade_hir::ExprKind::FieldAccess(op, _) |
            spade_hir::ExprKind::TupleIndex(op, _) |
            spade_hir::ExprKind::RangeIndex { target: op, start: _, end: _ } => {
                self.synth_expression(op, ctx)
            },

            spade_hir::ExprKind::Match(_, _) => self.synth_expression(expr, ctx),
            spade_hir::ExprKind::If(_, _, _) => self.synth_expression(expr, ctx),

            // Functions are special and will need special treatment
            spade_hir::ExprKind::Call {
                ..
            } => self.synth_expression(expr, ctx),
            // Visit the statements, then ensure that the result has the same type as the result
            spade_hir::ExprKind::Block(_) => self.synth_expression(expr, ctx),

            // These have the same domain as the pipeline
            // NOTE: We need to enforce that
            spade_hir::ExprKind::StageValid |
            spade_hir::ExprKind::StageReady => self.synth_expression(expr, ctx),

            // Weird expressions
            spade_hir::ExprKind::StaticUnreachable(_) => self.synth_expression(expr, ctx),
            spade_hir::ExprKind::Null => self.synth_expression(expr, ctx),

            spade_hir::ExprKind::MethodCall { .. } => {
                diag_bail!(expr, "Method should be lowered already")
            }
            spade_hir::ExprKind::LambdaDef { .. } => {
                diag_bail!(expr, "Lambda should be lowered already")
            }
        };

        let self_domain = self_domain?;

        // NOTE: There is a potential for optimization here if we don't merge vars that are
        // the same
        let merged = self_domain
            .resolve_domain(self)
            .at_loc(expr)
            .merge_domains(&expected.map(|d| d.resolve_domain(self)))?;

        let merged_id = self.add_domain_var(merged);

        self.replace(expected.inner, merged_id);
        self.replace(self_domain, merged_id);

        Ok(())
    }
}
