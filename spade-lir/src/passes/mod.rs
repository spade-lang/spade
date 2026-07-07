pub mod backflip;
pub mod legalize;

use colored::Colorize;
use itertools::Itertools;
use spade_common::location_info::Loc;

use crate::Entity;
use crate::Statement;

use crate::Result;
use crate::type_list::LirTypeList;

pub trait Pass {
    fn name(&self) -> &'static str;

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
    let entity_name = entity.name.to_string();
    let maybe_trace = |trace: &dyn Fn()| {
        if std::env::var("SPADE_TRACE_LIR_PASSES")
            .map(|val| entity_name.contains(&val))
            .unwrap_or(false)
        {
            trace();
        }
    };
    maybe_trace(&|| {
        println!("Running passes on {}\n{}", entity.name.to_string().red(),
                format!("{entity}")
                    .lines()
                    .map(|line| format!("    {line}").green())
                    .join("\n")
        ); // TODO
    });

    for pass in passes {
        let mut pass = pass();

        maybe_trace(&|| {
            println!(
                "Running {} on {}",
                pass.name().blue(),
                entity.name.to_string().red()
            ); // TODO
        });


        maybe_trace(&|| println!("Gathering types"));
        let types = LirTypeList::from_entity(entity);

        maybe_trace(&|| println!("Visiting entity"));
        pass.visit_entity(entity)?;


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
            .collect::<Result<Vec<_>>>()
            .map_err(|e| {
                maybe_trace(&|| println!("{}", format!("Pass failed").bright_red()));
                e
            })?
            .into_iter()
            .flatten()
            .collect();

        maybe_trace(&|| {
            println!(
                "Result of {} on {}:\n{}",
                pass.name().blue(),
                entity.name.to_string().red(),
                format!("{entity}")
                    .lines()
                    .map(|line| format!("    {line}").cyan())
                    .join("\n")
            );
        });
    }

    Ok(())
}
