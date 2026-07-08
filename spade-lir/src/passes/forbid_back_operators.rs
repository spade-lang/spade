use spade_common::location_info::Loc;
use spade_diagnostics::diag_bail;

use crate::{Binding, Operator, Result, Statement, passes::Pass, type_list::LirTypeList};

pub struct ForbidBackOperators {}

impl Pass for ForbidBackOperators {
    type Payload = ();

    fn name(&self) -> &'static str {
        "ForbidBackOperators"
    }

    fn visit_entity(&mut self, _entity: &mut crate::Entity) -> Result<Self::Payload> {
        Ok(())
    }

    fn visit_statement(
        &mut self,
        statement: &Loc<Statement>,
        _types: &LirTypeList,
        _payload: &mut Self::Payload,
    ) -> Result<Option<Vec<Loc<Statement>>>> {
        let Statement::Binding(Binding {
            name: _,
            operator,
            operands: _,
            ty: _,
            loc: _,
        }) = &statement.inner
        else {
            return Ok(None);
        };
        if let Operator::Back(_) = operator {
            diag_bail!(
                statement,
                "Found a back operator ({operator}) that was not lowered already"
            );
        } else {
            Ok(None)
        }
    }
}
