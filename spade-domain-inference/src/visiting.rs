use std::collections::HashMap;

use spade_common::location_info::{Loc, WithLocation};
use spade_diagnostics::{diag_anyhow, diag_bail, Diagnostic};
use spade_hir::{ExprKind, Expression, Pattern, PatternKind, Register, Statement, Unit};
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
        match &stmt.inner {
            Statement::Error => {}
            Statement::Binding(binding) => todo!(),
            Statement::Expression(expr) => {
                self.synth_expression(expr, ctx)?;
            }
            Statement::Register(Register {
                pattern,
                clock,
                reset,
                initial,
                value,
                value_type,
                attributes,
            }) => {
                let expected = self.synth_expression(value, ctx)?.at_loc(value);

                // Ensure that the domain has a clock
                match &self.collapse_tuple_domains(&expected.inner) {
                    DomainVar::Error => {}
                    DomainVar::Const => {
                        // This should be an error unless we can infer a more specific
                        // domain later, like this:
                        //
                        // entity test() -> 'a bool {
                        //     reg x = y;
                        //     y
                        // }
                    }
                    DomainVar::Async => {
                        let mut diag = Diagnostic::error(
                            expected.loc(),
                            format!(
                                "A value in the {expected} domain cannot be stored in a register."
                            ),
                        )
                        .primary_label(format!("{expected} in a register"))
                        .help("Values stored in registers must have a clock");
                        if matches!(&expected.inner, DomainVar::Tuple(_)) {
                            diag.add_note("Tuples can only be stored in registers if all elements have a common domain");
                        }

                        return Err(diag)
                    }
                    DomainVar::Known(_) => {}
                    DomainVar::Tuple(_) => {
                        diag_bail!(expected, "Found a tuple after flattening tuples")
                    }
                }

                // TODO: Ensure that the clock, reset, and initial are in the right
                // domains

                self.check_pattern(pattern, expected, ctx)?;
            }
            Statement::Declaration(locs) => todo!(),
            Statement::PipelineRegMarker(pipeline_reg_marker_extra) => {}
            Statement::Label(loc) => {}
            // TODO: Consider if we should do domain checking on asserts
            Statement::Assert(_expr) => {}
            Statement::Set { target, value } => {
                let target_ty = self.synth_expression(target, ctx)?;
                self.check_expression(value, &target_ty.at_loc(target), ctx)
                    .add_expected_source(|d, exp| {
                        d.secondary_label(target, format!("{exp} inferred here"))
                        .help(format!("The domain of the set value must be compatible with the domain of the target"))
                    })?;
            }
            Statement::WalSuffixed { suffix, target } => todo!(),
        }

        Ok(())
    }

    fn synth_pattern(&mut self, pattern: &Loc<Pattern>, ctx: &Context) -> Result<TypeVarID> {
        todo!()
    }

    // TODO: This should return a CheckError
    fn check_pattern(
        &mut self,
        pattern: &Loc<Pattern>,
        expected: Loc<DomainVar>,
        ctx: &Context,
    ) -> Result<()> {
        match &pattern.kind {
            // Integer patterns are always 'const, so we don't need to check
            PatternKind::Integer(_) => Ok(()),
            PatternKind::Bool(_) => Ok(()),
            PatternKind::Name { name, pre_declared } => {
                if *pre_declared {
                    todo!("Handle pre-declared")
                }
                self.name_domains.insert(name.inner.clone(), expected.inner);
                Ok(())
            }
            PatternKind::Tuple(locs) => todo!(),
            PatternKind::Array(locs) => todo!(),
            PatternKind::Type(loc, pattern_arguments) => todo!(),
        }
    }

    fn synth_expression(&mut self, expr: &Loc<Expression>, ctx: &Context) -> Result<DomainVar> {
        match &expr.kind {
            ExprKind::Error => Ok(DomainVar::Error),
            ExprKind::Identifier(name) => Ok(self
                .name_domains
                .get(name)
                .ok_or_else(|| diag_anyhow!(expr, "Did not find a domain for this name"))?
                .clone()),

            ExprKind::IntLiteral(_, _)
            | ExprKind::BoolLiteral(_)
            | ExprKind::BitLiteral(_)
            | ExprKind::TypeLevelInteger(_) => Ok(DomainVar::Const),
            ExprKind::CreatePorts => todo!(),
            ExprKind::TupleLiteral(inner) => {
                let inner_domains = inner
                    .iter()
                    .map(|i| self.synth_expression(i, ctx))
                    .collect::<Result<Vec<_>>>()?;
                Ok(DomainVar::Tuple(inner_domains))
            }

            ExprKind::ArrayLiteral(inner) => match inner.as_slice() {
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

            ExprKind::ArrayShorthandLiteral(loc, loc1) => todo!(),
            ExprKind::Index(loc, loc1) => todo!(),
            ExprKind::RangeIndex { target, start, end } => todo!(),
            ExprKind::TupleIndex(loc, loc1) => todo!(),
            ExprKind::FieldAccess(loc, loc1) => todo!(),
            ExprKind::MethodCall {
                target,
                name,
                args,
                call_kind,
                turbofish,
                safety,
            } => todo!(),
            ExprKind::Call {
                kind,
                callee,
                args,
                turbofish,
                safety,
            } => todo!(),
            ExprKind::BinaryOperator(loc, loc1, loc2) => todo!(),
            ExprKind::UnaryOperator(loc, loc1) => todo!(),
            ExprKind::Match(loc, items) => todo!(),
            ExprKind::Block(block) => todo!(),
            ExprKind::If(loc, loc1, loc2) => todo!(),
            ExprKind::TypeLevelIf(loc, loc1, loc2) => todo!(),
            ExprKind::PipelineRef {
                stage,
                name,
                declares_name,
                depth_typeexpr_id,
            } => todo!(),
            ExprKind::LambdaDef {
                lambda_type,
                lambda_type_params,
                captured_generic_params,
                lambda_unit,
                arguments,
                body,
            } => todo!(),
            ExprKind::StageValid => todo!(),
            ExprKind::StageReady => todo!(),
            ExprKind::StaticUnreachable(loc) => todo!(),
            ExprKind::Null => todo!(),
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
            ExprKind::Error => Ok(()),

            // The rules which are done in synthesis mode are handled here by synthesizing
            // a type, then subtyping
            // In the paper, literals appear to be roughly the same as `unit` types which are
            // checked. But in checking, we're not allowed to do subtyping so that would forbid
            // simple things like `entity () -> 'a bool {true}`. So we'll do synthesis
            ExprKind::IntLiteral(_, _)
            | ExprKind::BoolLiteral(_)
            | ExprKind::BitLiteral(_)
            | ExprKind::TypeLevelInteger(_)
            | ExprKind::TupleLiteral(_) |
            // Array literals are synthesized
            ExprKind::ArrayLiteral(_) |
            ExprKind::ArrayShorthandLiteral(_, _)
            // Identifiers are synthesized
            | ExprKind::Identifier(_) => {
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
            ExprKind::CreatePorts => todo!(),
            ExprKind::Index(loc, loc1) => todo!(),
            ExprKind::RangeIndex { target, start, end } => todo!(),
            ExprKind::TupleIndex(loc, loc1) => todo!(),
            ExprKind::FieldAccess(loc, loc1) => todo!(),
            ExprKind::MethodCall {
                target,
                name,
                args,
                call_kind,
                turbofish,
                safety,
            } => todo!(),
            ExprKind::Call {
                kind,
                callee,
                args,
                turbofish,
                safety,
            } => todo!(),
            ExprKind::BinaryOperator(loc, loc1, loc2) => todo!(),
            ExprKind::UnaryOperator(_, value) => {
                self.check_expression(value, expected, ctx)?;
                Ok(())
            },
            ExprKind::Match(loc, items) => todo!(),
            ExprKind::Block(block) => {
                for stmt in &block.statements {
                    self.visit_statement(&stmt, ctx).map_err(CheckError::SynthesisFailure)?
                }

                if let Some(result) = &block.result {
                    self.check_expression(result, expected, ctx)?;
                    Ok(())
                } else {
                    Ok(())
                }
            }
            ExprKind::If(loc, loc1, loc2) => todo!(),
            ExprKind::TypeLevelIf(loc, loc1, loc2) => todo!(),
            ExprKind::PipelineRef {
                stage,
                name,
                declares_name,
                depth_typeexpr_id,
            } => todo!(),
            ExprKind::LambdaDef {
                lambda_type,
                lambda_type_params,
                captured_generic_params,
                lambda_unit,
                arguments,
                body,
            } => todo!(),
            ExprKind::StageValid => todo!(),
            ExprKind::StageReady => todo!(),
            ExprKind::StaticUnreachable(loc) => todo!(),
            ExprKind::Null => todo!(),
        };
        result.map_err(|e| CheckError::CheckFailure(e, expected.clone()))
    }

    // TODO: We could make this a static method as implemented
    // TODO: Can we implement this in terms of least_upper_domain
    fn is_subtype_of(&self, a: &DomainVar, b: &DomainVar) -> Option<DomainVar> {
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
                .all(|i| self.is_subtype_of(any, &i).is_some())
                .then(|| Some(any.clone()))
                .unwrap_or_default(),
        }
    }

    fn least_upper_domain(&self, a: &DomainVar, b: &DomainVar) -> DomainVar {
        match (a, b) {
            (DomainVar::Error, _) | (_, DomainVar::Error) => DomainVar::Error,
            (DomainVar::Const, DomainVar::Const) => a.clone(),
            (DomainVar::Async, _) | (_, DomainVar::Async) => DomainVar::Async,

            (DomainVar::Const, other) | (other, DomainVar::Const) => other.clone(),

            (DomainVar::Known(d1), DomainVar::Known(d2)) => {
                if d1 == d2 {
                    a.clone()
                } else {
                    DomainVar::Async
                }
            }

            (name @ DomainVar::Known(_), DomainVar::Tuple(inner))
            | (DomainVar::Tuple(inner), name @ DomainVar::Known(_)) => {
                let mut result = name.clone();
                for i in inner {
                    result = self.least_upper_domain(&result, i)
                }
                result
            }

            (DomainVar::Tuple(l), DomainVar::Tuple(r)) => DomainVar::Tuple(
                l.iter()
                    .zip(r)
                    .map(|(l, r)| self.least_upper_domain(l, r))
                    .collect(),
            ),
        }
    }

    /// Collapses the domains in a tuple into the least upper domain of all tuple elements.
    /// Primarily used for checking things like clock constraints
    fn collapse_tuple_domains(&self, var: &DomainVar) -> DomainVar {
        match var {
            DomainVar::Tuple(inner) => match inner.as_slice() {
                [] => DomainVar::Const,
                [single] => single.clone(),
                [first, rest @ ..] => {
                    let mut result = self.collapse_tuple_domains(first);
                    for i in rest {
                        result = self.least_upper_domain(&result, &self.collapse_tuple_domains(i))
                    }
                    result
                }
            },
            _ => var.clone(),
        }
    }
}

#[derive(Debug)]
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
