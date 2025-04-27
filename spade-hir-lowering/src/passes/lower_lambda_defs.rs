use std::collections::HashMap;

use spade_common::{
    id_tracker::ExprIdTracker,
    location_info::{Loc, WithLocation},
    name::NameID,
};
use spade_diagnostics::{diag_anyhow, Diagnostic};
use spade_hir::{
    expression::CallKind, ArgumentList, ExprKind, Expression, Pattern, Statement, Unit,
};
use spade_typeinference::{equation::KnownTypeVar, HasType, TypeState};

use crate::error::Result;

use super::pass::Pass;

pub(crate) struct LambdaReplacement {
    pub new_body: Loc<Expression>,
    pub arguments: Vec<(Loc<Pattern>, KnownTypeVar)>,
}

impl LambdaReplacement {
    pub fn replace_in(&self, old: Loc<Unit>, idtracker: &mut ExprIdTracker) -> Result<Loc<Unit>> {
        let arg_bindings = self
            .arguments
            .iter()
            .enumerate()
            .map(|(i, (arg, _))| {
                // .1, .0 is self
                let (input, _) = old.inputs.get(1).ok_or_else(|| {
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

        let body = self.new_body.clone().map(|mut body| {
            let block = body.assume_block_mut();

            block.statements = arg_bindings
                .clone()
                .into_iter()
                .chain(block.statements.clone())
                .collect::<Vec<_>>();

            body
        });

        Ok(old.map_ref(|unit| spade_hir::Unit {
            body: body.clone(),
            ..unit.clone()
        }))
    }
}

pub(crate) struct LowerLambdaDefs<'a> {
    pub type_state: &'a TypeState,

    pub replacements: &'a mut HashMap<NameID, LambdaReplacement>,
}

impl<'a> Pass for LowerLambdaDefs<'a> {
    fn visit_expression(&mut self, expression: &mut Loc<Expression>) -> Result<()> {
        if let ExprKind::LambdaDef {
            lambda_unit,
            lambda_type,
            lambda_type_params: _,
            arguments,
            body,
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
            self.replacements.insert(
                lambda_unit.clone(),
                LambdaReplacement {
                    new_body: body.as_ref().clone(),
                    arguments: arguments.clone(),
                },
            );

            *expression = ExprKind::Call {
                kind: CallKind::Function,
                callee: lambda_type.clone().at_loc(expression),
                args: ArgumentList::Positional(vec![]).at_loc(expression),
                turbofish: None,
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
