pub mod backflip;
pub mod legalize;

use spade_common::location_info::Loc;

use crate::Entity;
use crate::Statement;

use crate::Result;
use crate::type_list::LirTypeList;

pub trait Pass {
    /// Visit an entity. If the head of the entity should be modified by the pass, this should be done here.
    ///
    /// For modifying the body of the entity, it is better to do so in `visit_statement` which is called after
    /// this function.
    fn visit_entity(&mut self, _entity: &mut Entity) -> Result<()> {
        Ok(())
    }

    /// Called on each statement in each entity. If the statement should remain in place, `Ok(None)` should
    /// be returned. If the statement should be replaced with one or more statements, return `Ok(<statements>)`
    ///
    /// This method is called after `visit_entity`
    fn visit_statement(
        &mut self,
        _statement: &Loc<Statement>,
        _types: &LirTypeList,
    ) -> Result<Option<Vec<Loc<Statement>>>> {
        Ok(None)
    }
}

pub fn run_passes(entity: &mut Entity, passes: &[Box<dyn Fn() -> Box<dyn Pass>>]) -> Result<()> {
    for pass in passes {
        let mut pass = pass();

        pass.visit_entity(entity)?;

        let types = LirTypeList::from_entity(entity);

        entity.statements = entity
            .statements
            .iter()
            .map(|stmt| {
                if let Some(new) = pass.visit_statement(stmt, &types)? {
                    Ok(new)
                } else {
                    Ok(vec![stmt.clone()])
                }
            })
            .collect::<Result<Vec<_>>>()?
            .into_iter()
            .flatten()
            .collect()
    }

    Ok(())
}
