use num::BigUint;
use rustc_hash::FxHashMap as HashMap;
use spade_common::location_info::{Loc, WithLocation};
use spade_diagnostics::{diag_anyhow, diag_bail};

use crate::{
    BackOperator, Binding, Operator, Result, Statement, Type, ValueName, passes::Pass,
    type_list::LirTypeList,
};

pub struct FlipBackConcat {}

impl Pass for FlipBackConcat {
    type Payload = ();

    fn name(&self) -> &'static str {
        "FlipBackConcat"
    }

    fn visit_entity(&mut self, _entity: &mut crate::Entity) -> Result<()> {
        Ok(())
    }

    fn visit_statement(
        &mut self,
        statement: &Loc<Statement>,
        types: &LirTypeList,
        _payload: &mut Self::Payload,
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
                    BackOperator::RangeSlice { .. } => {
                        // Handled in FlipBackRangeIndex
                        Ok(None)
                    }
                },
                _ => Ok(None),
            },
            _ => Ok(None),
        }
    }
}

pub struct FlipBackRangeIndex {}

impl Pass for FlipBackRangeIndex {
    type Payload = HashMap<Loc<ValueName>, Vec<(ValueName, BigUint, BigUint)>>;

    fn name(&self) -> &'static str {
        "FlipBackRangeIndex"
    }

    fn visit_entity(&mut self, entity: &mut crate::Entity) -> Result<Self::Payload> {
        let segments = entity.statements.iter().filter_map(|stmt| {
            let Statement::Binding(Binding {
                name,
                operator,
                operands,
                ty: _,
                loc: _,
            }) = &stmt.inner
            else {
                return None;
            };

            let Operator::Back(BackOperator::RangeSlice {
                start,
                end_exclusive,
            }) = operator
            else {
                return None;
            };

            Some((
                operands[0].clone(),
                (name.clone(), start.clone(), end_exclusive.clone()),
            ))
        });

        let mut result: HashMap<_, Vec<_>> = HashMap::default();
        for (target, value) in segments {
            result.entry(target).or_default().push(value)
        }
        Ok(result)
    }

    fn visit_statement(
        &mut self,
        statement: &Loc<Statement>,
        _types: &LirTypeList,
        payload: &mut Self::Payload,
    ) -> Result<Option<Vec<Loc<Statement>>>> {
        let Statement::Binding(Binding {
            name: _,
            operator,
            operands,
            ty: _,
            loc,
        }) = &statement.inner
        else {
            return Ok(None);
        };

        let Operator::Back(BackOperator::RangeSlice {
            start: _,
            end_exclusive: _,
        }) = operator
        else {
            return Ok(None);
        };

        let destination = &operands[0];

        // The first time we see a back range index, we'll replace it with the concatenation
        // of the whole signal. If we see a RangeIndex with the same name later, that was
        // taken care of here, so we simply drop that statement
        if let Some(parts) = payload.get(destination) {
            let mut parts = parts.clone();
            parts.sort_by_key(|(_, start, _end)| start.clone());

            let mut offset = BigUint::ZERO;
            let mut involved_signals = vec![];
            for (source, start, end) in parts {
                if offset != start {
                    diag_bail!(
                        statement,
                        "Found a range index with a hole. Offset is {offset} but the next value starts at {start}"
                    );
                }

                involved_signals.push(source.near_loc(statement));

                offset = end;
            }

            payload.remove_entry(destination);

            Ok(Some(vec![
                Statement::Binding(Binding {
                    name: destination.inner.clone(),
                    operator: Operator::Concat,
                    operands: involved_signals,
                    ty: Type::BitVector(offset),
                    loc: loc.clone(),
                })
                .at_loc(statement),
            ]))
        } else {
            Ok(Some(vec![]))
        }
    }
}
