use num::BigUint;
use spade_common::location_info::{Loc, WithLocation};
use spade_diagnostics::diag_anyhow;

use crate::{
    BackOperator, Binding, Operator, Result, Statement, Type, passes::Pass, type_list::LirTypeList,
};

pub struct Backflip {}

impl Pass for Backflip {
    fn name(&self) -> &'static str {
        "backflip"
    }

    fn visit_entity(&mut self, entity: &mut crate::Entity) -> Result<()> {
        Ok(())
    }

    fn visit_statement(
        &mut self,
        statement: &Loc<Statement>,
        types: &LirTypeList,
    ) -> Result<Option<Vec<Loc<Statement>>>> {
        match &statement.inner {
            Statement::Binding(Binding {
                name,
                operator,
                operands,
                ty,
                loc,
            }) => match operator {
                Operator::Back(operator) => match operator {
                    BackOperator::Alias => Ok(Some(vec![
                        Statement::Binding(Binding {
                            name: operands
                                .get(0)
                                .ok_or_else(|| {
                                    diag_anyhow!(
                                        statement,
                                        "Did not get an operand for LIR alias operation"
                                    )
                                })?
                                .clone()
                                .inner,
                            operator: Operator::Alias,
                            operands: vec![name.clone().at_loc(statement)],
                            ty: ty.clone(),
                            loc: loc.clone(),
                        })
                        .at_loc(statement),
                    ])),
                    // TODO: Consider if we can get rid of this distinction since we drop aliases during MIR lowering
                    BackOperator::BlackBoxAlias => Ok(Some(vec![
                        Statement::Binding(Binding {
                            name: operands
                                .get(0)
                                .ok_or_else(|| {
                                    diag_anyhow!(
                                        statement,
                                        "Did not get an operand for LIR alias operation"
                                    )
                                })?
                                .clone()
                                .inner,
                            operator: Operator::BlackBoxAlias,
                            operands: vec![name.clone().at_loc(statement)],
                            ty: ty.clone(),
                            loc: loc.clone(),
                        })
                        .at_loc(statement),
                    ])),
                    BackOperator::Concat => {
                        // let back(x) = concat(back(a), back(b));
                        // ->
                        // let back(a) = back(x)[...]
                        // let back(b) = back(x)[...]

                        let mut starts = vec![];
                        let mut current_offset = BigUint::ZERO;
                        for operand in operands {
                            starts.push(current_offset.clone());
                            current_offset += types.lookup(&operand)?.size();
                        }
                        starts.push(current_offset);

                        let offsets = starts
                            .iter()
                            .cloned()
                            .zip(starts.clone().into_iter().skip(1));

                        let declaration = Statement::Binding(Binding {
                            name: name.clone(),
                            operator: Operator::Nop,
                            operands: vec![],
                            ty: ty.clone(),
                            loc: loc.clone(),
                        })
                        .at_loc(&statement);

                        let result = operands
                            .iter()
                            .zip(offsets)
                            .map(|(operand, (start, end))| Binding {
                                name: operand.inner.clone(),
                                operator: Operator::RangeSlice {
                                    start: start.clone(),
                                    end_exclusive: end.clone(),
                                },
                                operands: vec![name.clone().at_loc(statement)],
                                ty: Type::BitVector(end - start),
                                loc: loc.clone(),
                            })
                            .map(Statement::Binding)
                            .map(|s| s.near_loc(statement));

                        Ok(Some([declaration].into_iter().chain(result).collect()))
                    }
                    BackOperator::RangeSlice {
                        start,
                        end_exclusive,
                    } => todo!(),
                },
                _ => Ok(None),
            },
            _ => Ok(None),
        }
    }
}
