use spade_common::location_info::{Loc, WithLocation};
use spade_diagnostics::diag_bail;

use crate::{Binding, Operator, Result, Statement, passes::Pass, type_list::LirTypeList};

pub struct LowerSet {}

impl Pass for LowerSet {
    type Payload = ();

    fn name(&self) -> &'static str {
        "LowerSet"
    }

    fn visit_unit(&mut self, _entity: &mut crate::Entity) -> Result<Self::Payload> {
        Ok(())
    }

    fn visit_statement(
        &mut self,
        statement: &Loc<Statement>,
        types: &LirTypeList,
        _payload: &mut Self::Payload,
    ) -> Result<Option<Vec<Loc<Statement>>>> {
        if let Statement::Set(target, value) = &statement.inner {
            if types.lookup(&target)? != types.lookup(&value)? {
                diag_bail!(
                    statement,
                    "Found a type mismatch in a set statement ({target}, {value})"
                )
            }
            Ok(Some(vec![
                Statement::Binding(Binding {
                    name: target.inner.clone(),
                    operator: Operator::Alias,
                    operands: vec![value.clone()],
                    ty: types.lookup(&target)?,
                    loc: None,
                })
                .at_loc(statement),
            ]))
        } else {
            Ok(None)
        }
    }
}
