use std::collections::HashMap;

use spade_common::location_info::{Loc, WithLocation};
use spade_diagnostics::{diag_anyhow, Diagnostic};
use spade_hir::{Expression, Pattern, Statement, Unit};
use spade_typeinference::equation::TypeVarID;

use crate::{domain_var::DomainVar, Context, DomainState, Result};

impl DomainState {
    pub fn visit_unit(&mut self, unit: &Loc<Unit>, ctx: &Context) -> Result<()> {
        let result = self.visit_unit_inner(unit, ctx);

        for (name, ty) in &unit.inputs {
            self.name_domains
                .insert(name.inner.clone(), self.domain_from_type_spec(&ty).inner);
        }

        let output_domain = unit
            .head
            .output_type
            .as_ref()
            .map(|ty| self.domain_from_type_spec(&ty))
            // NOTE: .nowhere() here is a bit sketchy, but since we can never fail
            // to unify with the async domain, this sohuld not appear.
            // TODO: Though we have to make sure we don't propagate this domain to
            // registers...
            .unwrap_or(DomainVar::Async.nowhere());

        self.check_expression(&unit.body, &output_domain, ctx)
            .add_expected_source(|d, expected| {
                d.secondary_label(&output_domain, format!("{expected} was specified here"))
            })?;

        result
    }
    pub fn visit_unit_inner(&mut self, unit: &Loc<Unit>, ctx: &Context) -> Result<()> {
        Ok(())
    }

    fn visit_statement(&mut self, stmt: &Loc<Statement>, ctx: &Context) -> Result<()> {
        todo!()
    }

    fn synth_pattern(&mut self, pattern: &Loc<Pattern>, ctx: &Context) -> Result<TypeVarID> {
        todo!()
    }

    fn check_pattern(
        &mut self,
        pattern: &Loc<Pattern>,
        expected: Loc<TypeVarID>,
        ctx: &Context,
    ) -> Result<()> {
        todo!()
    }

    fn synth_expression(&mut self, expr: &Loc<Expression>, ctx: &Context) -> Result<DomainVar> {
        match &expr.kind {
            spade_hir::ExprKind::Error => Ok(DomainVar::Error),
            spade_hir::ExprKind::Identifier(name) => Ok(self
                .name_domains
                .get(name)
                .ok_or_else(|| diag_anyhow!(expr, "Did not find a domain for this name"))?
                .clone()),

            spade_hir::ExprKind::IntLiteral(_, _)
            | spade_hir::ExprKind::BoolLiteral(_)
            | spade_hir::ExprKind::BitLiteral(_)
            | spade_hir::ExprKind::TypeLevelInteger(_) => Ok(DomainVar::Const),
            spade_hir::ExprKind::CreatePorts => todo!(),
            spade_hir::ExprKind::TupleLiteral(inner) => {
                let inner_domains = inner
                    .iter()
                    .map(|i| self.synth_expression(i, ctx).map(|d| d.at_loc(i)))
                    .collect::<Result<Vec<_>>>()?;
                Ok(DomainVar::Tuple(inner_domains))
            }

            spade_hir::ExprKind::ArrayLiteral(inner) => match inner.as_slice() {
                [] => Ok(DomainVar::Const),
                [single] => self.synth_expression(single, ctx),
                [first, rest @ ..] => {
                    let result = self.synth_expression(first, ctx)?;

                    for elem in rest {
                        self.check_expression(elem, &result.clone().at_loc(first), ctx)
                            .add_expected_source(|d, expected| {
                                d.secondary_label(
                                    first,
                                    format!("The domain of the first element is {expected}"),
                                )
                                .note("All array elements need to be in the same domain")
                            })?;
                    }
                    Ok(result)
                }
            },

            spade_hir::ExprKind::ArrayShorthandLiteral(loc, loc1) => todo!(),
            spade_hir::ExprKind::Index(loc, loc1) => todo!(),
            spade_hir::ExprKind::RangeIndex { target, start, end } => todo!(),
            spade_hir::ExprKind::TupleIndex(loc, loc1) => todo!(),
            spade_hir::ExprKind::FieldAccess(loc, loc1) => todo!(),
            spade_hir::ExprKind::MethodCall {
                target,
                name,
                args,
                call_kind,
                turbofish,
                safety,
            } => todo!(),
            spade_hir::ExprKind::Call {
                kind,
                callee,
                args,
                turbofish,
                safety,
            } => todo!(),
            spade_hir::ExprKind::BinaryOperator(loc, loc1, loc2) => todo!(),
            spade_hir::ExprKind::UnaryOperator(loc, loc1) => todo!(),
            spade_hir::ExprKind::Match(loc, items) => todo!(),
            spade_hir::ExprKind::Block(block) => todo!(),
            spade_hir::ExprKind::If(loc, loc1, loc2) => todo!(),
            spade_hir::ExprKind::TypeLevelIf(loc, loc1, loc2) => todo!(),
            spade_hir::ExprKind::PipelineRef {
                stage,
                name,
                declares_name,
                depth_typeexpr_id,
            } => todo!(),
            spade_hir::ExprKind::LambdaDef {
                lambda_type,
                lambda_type_params,
                captured_generic_params,
                lambda_unit,
                arguments,
                body,
            } => todo!(),
            spade_hir::ExprKind::StageValid => todo!(),
            spade_hir::ExprKind::StageReady => todo!(),
            spade_hir::ExprKind::StaticUnreachable(loc) => todo!(),
            spade_hir::ExprKind::Null => todo!(),
        }
    }

    fn check_expression(
        &mut self,
        expr: &Loc<Expression>,
        expected: &Loc<DomainVar>,
        ctx: &Context,
    ) -> std::result::Result<(), CheckError> {
        let result = match &expr.kind {
            // Anything can be an error ~~if you're brave enough
            spade_hir::ExprKind::Error => Ok(()),

            // The rules which are done in synthesis mode are handled here by synthesizing
            // a type, then subtyping
            // In the paper, literals appear to be roughly the same as `unit` types which are
            // checked. But in checking, we're not allowed to do subtyping so that would forbid
            // simple things like `entity () -> 'a bool {true}`. So we'll do synthesis
            spade_hir::ExprKind::IntLiteral(_, _)
            | spade_hir::ExprKind::BoolLiteral(_)
            | spade_hir::ExprKind::BitLiteral(_)
            | spade_hir::ExprKind::TypeLevelInteger(_)
            | spade_hir::ExprKind::TupleLiteral(_) |
            // Array literals are synthesized
            spade_hir::ExprKind::ArrayLiteral(_) |
            spade_hir::ExprKind::ArrayShorthandLiteral(_, _)
            // Identifiers are synthesized
            | spade_hir::ExprKind::Identifier(_) => {
                let synth_result = self
                    .synth_expression(expr, ctx)
                    .map_err(|e| CheckError::SynthesisFailure(e))?;

                match self.is_subtype_of(&expected, &synth_result) {
                    Some(_) => Ok(()),
                    None => Err(Diagnostic::error(
                        expr,
                        format!(
                            "Domain mismatch, expected {expected}, but it is in {synth_result}"
                        ),
                    )
                    .primary_label(format!("Expected domain {expected}, found {synth_result}"))),
                }
            }
            spade_hir::ExprKind::CreatePorts => todo!(),
            spade_hir::ExprKind::Index(loc, loc1) => todo!(),
            spade_hir::ExprKind::RangeIndex { target, start, end } => todo!(),
            spade_hir::ExprKind::TupleIndex(loc, loc1) => todo!(),
            spade_hir::ExprKind::FieldAccess(loc, loc1) => todo!(),
            spade_hir::ExprKind::MethodCall {
                target,
                name,
                args,
                call_kind,
                turbofish,
                safety,
            } => todo!(),
            spade_hir::ExprKind::Call {
                kind,
                callee,
                args,
                turbofish,
                safety,
            } => todo!(),
            spade_hir::ExprKind::BinaryOperator(loc, loc1, loc2) => todo!(),
            spade_hir::ExprKind::UnaryOperator(loc, loc1) => todo!(),
            spade_hir::ExprKind::Match(loc, items) => todo!(),
            spade_hir::ExprKind::Block(block) => {
                if !block.statements.is_empty() {
                    todo!("Handle statements")
                }

                if let Some(result) = &block.result {
                    self.check_expression(result, expected, ctx)?;
                    Ok(())
                } else {
                    Ok(())
                }
            }
            spade_hir::ExprKind::If(loc, loc1, loc2) => todo!(),
            spade_hir::ExprKind::TypeLevelIf(loc, loc1, loc2) => todo!(),
            spade_hir::ExprKind::PipelineRef {
                stage,
                name,
                declares_name,
                depth_typeexpr_id,
            } => todo!(),
            spade_hir::ExprKind::LambdaDef {
                lambda_type,
                lambda_type_params,
                captured_generic_params,
                lambda_unit,
                arguments,
                body,
            } => todo!(),
            spade_hir::ExprKind::StageValid => todo!(),
            spade_hir::ExprKind::StageReady => todo!(),
            spade_hir::ExprKind::StaticUnreachable(loc) => todo!(),
            spade_hir::ExprKind::Null => todo!(),
        };
        result.map_err(|e| CheckError::CheckFailure(e, expected.clone()))
    }

    fn is_subtype_of(&self, a: &DomainVar, b: &DomainVar) -> Option<DomainVar> {
        // TODO: Verify the latticeness of this
        // For ordering it is simpler to write this as a :> b, instead of `b <: a`
        match (a, b) {
            // Anything can subtype with error
            (DomainVar::Error, _) | (_, DomainVar::Error) => Some(DomainVar::Error),

            // The const domain is a subdomain of every other domain
            (k @ DomainVar::Const, DomainVar::Const)
            | (k @ DomainVar::Async, DomainVar::Const)
            | (k @ DomainVar::Known(_), DomainVar::Const)
            | (k @ DomainVar::Tuple(_), DomainVar::Const) => Some(k.clone()),

            // The async domain is not a subdomain of anything but itself
            (DomainVar::Async, DomainVar::Async) => Some(DomainVar::Async),
            (DomainVar::Const, DomainVar::Async)
            | (DomainVar::Known(_), DomainVar::Async)
            | (DomainVar::Tuple(_), DomainVar::Async) => None,

            (DomainVar::Const, DomainVar::Known(_)) => None,
            (DomainVar::Async, DomainVar::Known(_)) => Some(DomainVar::Async),
            (k @ DomainVar::Known(d1), DomainVar::Known(d2)) => {
                if d1 == d2 {
                    Some(k.clone())
                } else {
                    None
                }
            }
            // TODO Not entirely clear what we should do in this case. The only
            // case this holds is if this is (a, a) <: a
            (DomainVar::Tuple(_), DomainVar::Known(_)) => todo!(),

            (any, DomainVar::Tuple(inner)) => inner
                .into_iter()
                .all(|i| self.is_subtype_of(any, &i.inner).is_some())
                .then(|| Some(any.clone()))
                .unwrap_or_default(),
        }
    }
}

enum CheckError {
    CheckFailure(Diagnostic, Loc<DomainVar>),
    SynthesisFailure(Diagnostic),
}

impl CheckError {
    pub fn add_expected_source(
        self,
        f: impl Fn(Diagnostic, Loc<DomainVar>) -> Diagnostic,
    ) -> Diagnostic {
        match self {
            CheckError::CheckFailure(diagnostic, var) => f(diagnostic, var),
            CheckError::SynthesisFailure(diagnostic) => diagnostic,
        }
    }
}

trait ResultExt<T> {
    fn add_expected_source(self, f: impl Fn(Diagnostic, Loc<DomainVar>) -> Diagnostic)
        -> Result<T>;
}
impl<T> ResultExt<T> for std::result::Result<T, CheckError> {
    fn add_expected_source(
        self,
        f: impl Fn(Diagnostic, Loc<DomainVar>) -> Diagnostic,
    ) -> Result<T> {
        self.map_err(|e| e.add_expected_source(f))
    }
}
