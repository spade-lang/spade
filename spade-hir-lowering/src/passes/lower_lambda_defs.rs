use rustc_hash::FxHashMap as HashMap;
use spade_common::{
    id_tracker::ExprIdTracker,
    location_info::{Loc, WithLocation},
    name::{Identifier, NameID},
};
use spade_diagnostics::{diag_anyhow, Diagnostic};
use spade_hir::{
    expression::{CallKind, Safety},
    ArgumentList, ExprKind, Expression, Parameter, ParameterList, Pattern, PatternKind, Statement,
    TypeParam, TypeSpec, Unit, UnitHead,
};
use spade_typeinference::{equation::KnownTypeVar, GenericListToken, HasType, TypeState};

use crate::error::Result;

use super::pass::Pass;

pub(crate) struct LambdaReplacement {
    pub new_body: Loc<Expression>,
    pub arguments: Vec<(Loc<Pattern>, KnownTypeVar)>,
    pub outer_type_params: HashMap<NameID, NameID>,
    pub clock: Option<Loc<NameID>>,
    pub captures: Vec<(Loc<Identifier>, Loc<NameID>)>,
}

impl LambdaReplacement {
    fn replace_type_params(&self, old: &Vec<Loc<TypeParam>>) -> Vec<Loc<TypeParam>> {
        old.clone()
            .into_iter()
            .map(|tp| {
                let loc = tp.loc();
                let TypeParam {
                    ident,
                    name_id,
                    trait_bounds,
                    meta,
                } = tp.inner;
                TypeParam {
                    name_id: self
                        .outer_type_params
                        .get(&name_id)
                        .cloned()
                        .unwrap_or(name_id),
                    ident,
                    trait_bounds,
                    meta,
                }
                .at_loc(&loc)
            })
            .collect::<Vec<_>>()
    }

    fn update_type_spec(&self, ts: Loc<TypeSpec>) -> Loc<TypeSpec> {
        let mut new_ts = ts.clone();
        for (from, to) in &self.outer_type_params {
            new_ts = new_ts.map(|ty| {
                ty.replace_in(
                    &TypeSpec::Generic(from.clone().at_loc(&ts)),
                    &TypeSpec::Generic(to.clone().at_loc(&ts)),
                )
            })
        }
        new_ts
    }

    pub fn replace_in(&self, old: Loc<Unit>, idtracker: &mut ExprIdTracker) -> Result<Loc<Unit>> {
        let arg_bindings = self
            .arguments
            .iter()
            .enumerate()
            .map(|(i, (arg, _))| {
                // .1, .0 is self
                let (input, _) = old
                    .inputs
                    .get(if self.clock.is_some() { 2 } else { 1 })
                    .ok_or_else(|| {
                        diag_anyhow!(
                            arg,
                            "Did not find any arguments to the generated lambda body"
                        )
                    })?;
                Ok(Statement::binding(
                    arg.clone(),
                    None,
                    ExprKind::TupleIndex(
                        Box::new(
                            ExprKind::Identifier(input.clone().inner)
                                .with_id(idtracker.next())
                                .at_loc(arg),
                        ),
                        (i as u128).at_loc(arg),
                    )
                    .with_id(idtracker.next())
                    .at_loc(input),
                )
                .at_loc(arg))
            })
            .collect::<Result<Vec<_>>>()?;

        let clock_binding = if let Some(clock) = &self.clock {
            let (input, _) = old.inputs.get(1).ok_or_else(|| {
                diag_anyhow!(
                    clock,
                    "Did not find any arguments to the generated lambda body"
                )
            })?;

            Some(
                Statement::binding(
                    PatternKind::Name {
                        name: clock.clone(),
                        pre_declared: false,
                    }
                    .with_id(idtracker.next())
                    .at_loc(&clock),
                    None,
                    ExprKind::Identifier(input.inner.clone())
                        .with_id(idtracker.next())
                        .at_loc(&clock),
                )
                .at_loc(&clock),
            )
        } else {
            None
        };

        let capture_bindings = self
            .captures
            .iter()
            .map(|(cap_ident, cap_name)| {
                Ok(Statement::binding(
                    PatternKind::Name {
                        name: cap_name.clone(),
                        pre_declared: false,
                    }
                    .with_id(idtracker.next())
                    .at_loc(cap_name),
                    None,
                    ExprKind::FieldAccess(
                        Box::new(
                            ExprKind::Identifier(
                                old.inputs
                                    .get(0)
                                    .ok_or_else(|| {
                                        diag_anyhow!(
                                            cap_name,
                                            "Did not find a self argument in lambda call"
                                        )
                                    })?
                                    .0
                                    .inner
                                    .clone(),
                            )
                            .with_id(idtracker.next())
                            .at_loc(cap_name),
                        ),
                        cap_ident.clone(),
                    )
                    .with_id(idtracker.next())
                    .at_loc(cap_name),
                )
                .at_loc(&cap_name.loc()))
            })
            .collect::<Result<Vec<_>>>()?;

        let new_bindings = arg_bindings
            .into_iter()
            .chain(clock_binding)
            .chain(capture_bindings)
            .collect::<Vec<_>>();

        let scope_type_params = self.replace_type_params(&old.head.scope_type_params);
        let unit_type_params = self.replace_type_params(&old.head.unit_type_params);

        let body = self.new_body.clone().map(|mut body| {
            let block = body.assume_block_mut();

            block.statements = new_bindings
                .clone()
                .into_iter()
                .chain(block.statements.clone())
                .collect::<Vec<_>>();

            body
        });

        let result = old.map_ref(move |unit| spade_hir::Unit {
            body: body.clone(),
            inputs: unit
                .inputs
                .iter()
                .map(|(n, t)| (n.clone(), self.update_type_spec(t.clone())))
                .collect(),
            head: UnitHead {
                scope_type_params: scope_type_params.clone(),
                unit_type_params: unit_type_params.clone(),
                inputs: ParameterList(
                    unit.head
                        .inputs
                        .0
                        .iter()
                        .cloned()
                        .map(|i| Parameter {
                            no_mangle: i.no_mangle,
                            name: i.name,
                            ty: self.update_type_spec(i.ty),
                            field_translator: i.field_translator,
                        })
                        .collect(),
                )
                .at_loc(&unit.head.inputs),
                ..unit.head.clone()
            },
            ..unit.clone()
        });
        Ok(result)
    }
}

pub(crate) struct LowerLambdaDefs<'a> {
    pub type_state: &'a mut TypeState,
    pub idtracker: &'a mut ExprIdTracker,

    pub replacements: &'a mut HashMap<(NameID, Vec<KnownTypeVar>), LambdaReplacement>,
}

impl<'a> Pass for LowerLambdaDefs<'a> {
    fn visit_expression(&mut self, expression: &mut Loc<Expression>) -> Result<()> {
        if let ExprKind::LambdaDef {
            unit_kind: _,
            lambda_unit,
            lambda_type,
            type_params,
            outer_generic_params,
            arguments,
            body,
            clock,
            captures,
        } = &expression.kind
        {
            let arguments = arguments
                .iter()
                .cloned()
                .map(|arg| {
                    let ty = arg
                        .get_type(&self.type_state)
                        .resolve(&self.type_state)
                        .into_known(&self.type_state)
                        .ok_or_else(|| {
                            Diagnostic::error(&arg, "The type of this argument is not fully known")
                                .primary_label("Type is not fully known")
                        })?;
                    Ok((arg, ty))
                })
                .collect::<Result<Vec<_>>>()?;

            let token = GenericListToken::Expression(expression.id);
            let generic_list = self.type_state.get_generic_list(&token).ok_or_else(|| {
                diag_anyhow!(&*expression, "Did not find a generic list for this lambda")
            })?;

            let concrete_type_params = type_params
                .all()
                .map(|tp| {
                    let result = generic_list
                        .get(&tp.name_id)
                        .ok_or_else(|| {
                            diag_anyhow!(
                            tp,
                            "The type of this type param in the lambda was not in the generic list"
                        )
                        })?
                        .resolve(&self.type_state)
                        .into_known(&self.type_state)
                        .ok_or_else(|| {
                            diag_anyhow!(tp, "The type of {} was not fully known", tp.name_id)
                        })?;
                    Ok(result)
                })
                .collect::<Result<_>>()?;

            self.replacements.insert(
                (lambda_unit.clone(), concrete_type_params),
                LambdaReplacement {
                    new_body: body.as_ref().clone(),
                    arguments: arguments.clone(),
                    outer_type_params: outer_generic_params
                        .iter()
                        .map(|tp| (tp.name_in_lambda.clone(), tp.name_in_body.inner.clone()))
                        .collect(),
                    clock: clock.clone(),
                    captures: captures.clone(),
                },
            );

            *expression = ExprKind::Call {
                kind: CallKind::Function,
                callee: lambda_type.clone().at_loc(expression),
                args: ArgumentList::Positional(
                    captures
                        .iter()
                        .map(|(_, name_id)| {
                            let id = self.idtracker.next();

                            self.type_state.add_equation(
                                spade_typeinference::equation::TypedExpression::Id(id),
                                name_id.get_type(self.type_state),
                            );

                            ExprKind::Identifier(name_id.clone().inner)
                                .with_id(id)
                                .at_loc(name_id)
                        })
                        .collect(),
                )
                .at_loc(expression),
                turbofish: None,
                safety: Safety::Default,
            }
            .with_id(expression.id)
            .at_loc(expression);

            Ok(())
        } else {
            Ok(())
        }
    }

    fn visit_unit(&mut self, _unit: &mut Unit) -> Result<()> {
        Ok(())
    }
}
