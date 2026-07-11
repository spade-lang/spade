use rustc_hash::FxHashMap as HashMap;
use spade_common::location_info::{Loc, WithLocation};
use spade_diagnostics::diag_bail;

use crate::{Binding, Operator, Statement, ValueName, passes::Pass};

/// When LIR is generated, `Nop` operations are used to define back wires to give them a type. Later,
/// Back(..) operations are used to give an actual value for those values. This pass drops definitions
/// which have been replaced, while doing some sanity checks to ensure that the type of a node hasn't changed.
pub struct DropBackNops {}

impl Pass for DropBackNops {
    type Payload = HashMap<ValueName, Vec<Loc<Binding>>>;

    fn name(&self) -> &'static str {
        "DropBackNops"
    }

    fn visit_entity(&mut self, entity: &mut crate::Entity) -> crate::Result<Self::Payload> {
        let mut result = HashMap::default();
        for statement in &entity.statements {
            match &statement.inner {
                Statement::Binding(b) => result
                    .entry(b.name.clone())
                    .or_insert(vec![])
                    .push(b.clone().at_loc(statement)),
                _ => {}
            }
        }

        Ok(result)
    }

    fn visit_statement(
        &mut self,
        statement: &spade_common::location_info::Loc<Statement>,
        _types: &crate::type_list::LirTypeList,
        payload: &mut Self::Payload,
    ) -> crate::Result<Option<Vec<spade_common::location_info::Loc<Statement>>>> {
        let Statement::Binding(b) = &statement.inner else {
            return Ok(None);
        };

        if b.operator == Operator::Nop {
            // Safe unwrap, the name must have been added at least once
            let other = payload.get(&b.name).unwrap();

            if other.len() == 1 {
                Ok(None)
            } else {
                let non_nops = other
                    .iter()
                    .filter(|op| op.operator != Operator::Nop)
                    .collect::<Vec<_>>();

                if non_nops.len() == 0 {
                    diag_bail!(
                        statement,
                        "Found multiple definitions of {}, but all were nops",
                        b.name
                    )
                } else if non_nops.len() > 1 {
                    diag_bail!(statement, "Found multiple non-nop defintions of {}", b.name)
                } else {
                    if b.ty != non_nops[0].ty {
                        diag_bail!(
                            statement,
                            "Found nop and non-nop definition of {}, but their types disagree ({} vs {})",
                            b.name,
                            b.ty,
                            non_nops[0].ty
                        )
                    }
                    Ok(Some(vec![]))
                }
            }
        } else {
            Ok(None)
        }
    }
}
