use spade_common::location_info::{Loc, WithLocation};
use spade_diagnostics::{diag_anyhow, diag_bail, Diagnostic};
use spade_hir::{
    domains::DomainName, Binding, ExprKind, Expression, Parameter, Pattern, PatternKind, Register,
    Statement, Unit,
};
use spade_typeinference::equation::TypeVarID;

use crate::{
    domain_var::{DomainVar, KnownDomain},
    Context, DomainState, Result,
};

impl DomainState {
    // TODO: Don't make this bail on first error
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
            Statement::Binding(Binding {
                pattern,
                ty: _,
                value,
                wal_trace: _,
            }) => {
                let expected = self.synth_expression(value, ctx)?.at_loc(value);

                self.check_pattern(pattern, &expected, ctx)
                    .add_default_source_message()?;
            }
            Statement::Expression(expr) => {
                self.synth_expression(expr, ctx)?;
            }
            Statement::Register(Register {
                pattern,
                clock,
                reset,
                // Initial values are checked elsewhere
                initial: _,
                value,
                value_type: _,
                attributes: _,
            }) => {
                let expected = self.synth_expression(value, ctx)?.at_loc(value);
                let collapsed = expected.collapse_tuple_domains().at_loc(value);

                // Ensure that the domain has a clock
                match &collapsed.inner {
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

                        return Err(diag);
                    }
                    DomainVar::Known(_) => {}
                    DomainVar::Tuple(_) => {
                        diag_bail!(expected, "Found a tuple after flattening tuples")
                    }
                }

                self.check_expression(clock, &collapsed, ctx)
                    .add_expected_source(|d, expected| {
                        d.secondary_label(&expected, format!("The value is in domain {expected}."))
                            .help(format!(
                                "The domain of the clock must be the same as the value"
                            ))
                    })?;

                match reset {
                    Some((trigger, value)) => {
                        self.check_expression(trigger, &collapsed, ctx).add_expected_source(|d, expected| {
                        d.secondary_label(&expected, format!("The value is in domain {expected}."))
                            .help(format!(
                                "The domain of the reset trigger must be the same as the register value"
                            ))
                        })?;

                        self.check_expression(value, &expected, ctx).add_expected_source(|d, expected| {
                        d.secondary_label(&expected, format!("The value is in domain {expected}."))
                            .help(format!(
                                "The domain of the reset value must be the same as the register value"
                            ))
                        })?;
                    }
                    None => {}
                }

                self.check_pattern(pattern, &expected, ctx)
                    .add_default_source_message()?;
            }
            Statement::Declaration(locs) => todo!(),
            Statement::PipelineRegMarker(_) => {}
            Statement::Label(_) => {}
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
            Statement::WalSuffixed {
                suffix: _,
                target: _,
            } => {}
        }

        Ok(())
    }

    fn check_pattern(
        &mut self,
        pattern: &Loc<Pattern>,
        expected: &Loc<DomainVar>,
        ctx: &Context,
    ) -> std::result::Result<(), CheckError> {
        match &pattern.kind {
            // Integer patterns are always 'const, so we don't need to check
            PatternKind::Integer(_) => Ok(()),
            PatternKind::Bool(_) => Ok(()),
            PatternKind::Name { name, pre_declared } => {
                if *pre_declared {
                    todo!("Handle pre-declared")
                }
                self.name_domains
                    .insert(name.inner.clone(), expected.inner.clone());
                Ok(())
            }
            PatternKind::Tuple(members) => match &expected.inner {
                DomainVar::Error | DomainVar::Const | DomainVar::Async | DomainVar::Known(_) => {
                    for member in members {
                        self.check_pattern(member, expected, ctx)?
                    }
                    Ok(())
                }
                DomainVar::Tuple(member_domains) => {
                    if member_domains.len() != members.len() {
                        Err(CheckError::SynthesisFailure(diag_anyhow!(pattern, "Found an expected domain with {} members, but a pattern with {} members", member_domains.len(), members.len())))
                    } else {
                        for (m, d) in members.iter().zip(member_domains) {
                            // NOTE: This Loc is not very helpful, but this is also infallible
                            self.check_pattern(m, &d.clone().at_loc(pattern), ctx)?;
                        }
                        Ok(())
                    }
                }
            },
            PatternKind::Array(values) => {
                for val in values {
                    self.check_pattern(val, &expected, ctx)?;
                }
                Ok(())
            }
            PatternKind::Type(loc, pattern_arguments) => todo!(),
        }
    }

    fn synth_expression(&mut self, expr: &Loc<Expression>, ctx: &Context) -> Result<DomainVar> {
        match &expr.kind {
            ExprKind::Error => Ok(DomainVar::Error),
            ExprKind::PipelineRef {
                stage: _,
                name,
                declares_name: _,
                depth_typeexpr_id: _,
            } => Ok(self
                .name_domains
                .get(name)
                .ok_or_else(|| diag_anyhow!(expr, "Did not find a domain for this name"))?
                .clone()),
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
            ExprKind::TupleIndex(indexee, index) => {
                let indexee_domain = self.synth_expression(indexee, ctx)?;

                match indexee_domain {
                    other @ DomainVar::Error
                    | other @ DomainVar::Const
                    | other @ DomainVar::Async
                    | other @ DomainVar::Known(_) => {
                        // TODO: This is a bit strange, and we should convince ourselves that
                        // it is the right strategy. The idea is that if we're not a tuple,
                        // the indexed value will have the same domain as the indexee
                        Ok(other)
                    }
                    DomainVar::Tuple(domain_vars) => {
                        let inner = domain_vars
                            .get(index.inner as usize)
                            .ok_or_else(|| diag_anyhow!(expr, "Tuple index out of range"))?;

                        Ok(inner.clone())
                    }
                }
            }

            ExprKind::ArrayShorthandLiteral(loc, loc1) => todo!(),
            ExprKind::Index(loc, loc1) => todo!(),
            ExprKind::RangeIndex { target, start, end } => todo!(),
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
                kind: _,
                callee,
                args,
                turbofish: _,
                safety: _,
            } => {
                let unit = ctx.symtab.unit_by_id(&callee);

                let mut inner_domain_map =
                    unit.inner
                        .domains
                        .iter()
                        .filter_map(|domain| match domain.name {
                            DomainName::Annonymous => Some((KnownDomain::Annonymous, None)),
                            DomainName::Const => None,
                            DomainName::Async => None,
                            DomainName::Named(name) => {
                                Some((KnownDomain::Named(name.inner.clone()), None))
                            }
                        });

                for (
                    Parameter {
                        no_mangle: _,
                        name,
                        ty,
                        field_translator: _,
                    },
                    expr,
                ) in unit.inputs.0.iter().zip(args.expressions())
                {
                    let callee_domain = self.domain_from_type_spec(ty);

                    // The default behaviour for arguments in a bidirectinoal
                    // type checker seems to be to check them against the 
                    // expected type. However, we have slightly different
                    // constraints here since all units are "generic" over a
                    // domain. Instead, we'll synthesize the domain of the argument
                    
                    let arg_domain = self.synth_expression(expr, ctx)?;

                    callee_domain.map_to_foreign(arg_domain);
                }
            }
            ExprKind::BinaryOperator(loc, loc1, loc2) => todo!(),
            ExprKind::UnaryOperator(loc, loc1) => todo!(),
            ExprKind::Match(loc, items) => todo!(),
            ExprKind::Block(block) => todo!(),
            ExprKind::If(loc, loc1, loc2) => todo!(),
            ExprKind::TypeLevelIf(loc, loc1, loc2) => todo!(),
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
            | ExprKind::TupleLiteral(_)
            // Calls require synthesizing the output domain
            | ExprKind::Call { .. }
            // Tuple indexing requires knowing the inner => synthesis
            | ExprKind::TupleIndex(_, _)
            // Array literals are synthesized
            | ExprKind::ArrayLiteral(_)
            | ExprKind::ArrayShorthandLiteral(_, _)
            // Identifiers are synthesized
            | ExprKind::PipelineRef {
                stage: _,
                name: _,
                declares_name: _,
                depth_typeexpr_id: _,
            }
            | ExprKind::Identifier(_) => {
                let synth_result = self
                    .synth_expression(expr, ctx)
                    .map_err(|e| CheckError::SynthesisFailure(e))?;

                if !expected.is_subdomain_of(&synth_result) {
                    Err(Diagnostic::error(
                        expr,
                        format!(
                            "Domain mismatch, expected {expected}, but it is in {synth_result}"
                        ),
                    )
                    .primary_label(format!("Expected domain {expected}, found {synth_result}")))
                } else {
                    Ok(())
                }
            }
            // Ports can be in any domain
            ExprKind::CreatePorts => {
                Ok(())
            },
            // TODO: Write a test
            ExprKind::Index(indexee, _) => {
                self.check_expression(indexee, expected, ctx)?;
                Ok(())
            },
            // TODO: Write a test
            ExprKind::RangeIndex { target, start: _, end: _ } => {
                self.check_expression(target, expected, ctx)?;
                Ok(())
            },
            // TODO: Write a test
            ExprKind::FieldAccess(target, _) => {
                self.check_expression(target, expected, ctx)?;
                Ok(())
            },
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
            ExprKind::StaticUnreachable(_) => todo!(),
            ExprKind::Null => todo!(),
            // TODO: Write a test
            ExprKind::MethodCall { .. } => {
                return Err(CheckError::SynthesisFailure(diag_anyhow!(expr, "Method call should already be lowered")))
            },
        };
        result.map_err(|e| CheckError::CheckFailure(e, expected.clone()))
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
    fn add_default_source_message(self) -> Result<T>;
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

    fn add_default_source_message(self) -> Result<T> {
        self.add_expected_source(|d, expected| {
            d.secondary_label(&expected, format!("Domain {expected} inferred here"))
        })
    }
}
