use num::ToPrimitive;

use spade_common::location_info::{Loc, WithLocation};
use spade_diagnostics::{diag_anyhow, Diagnostic};
use spade_hir::{symbol_table::FrozenSymtab, ItemList, PipelineRegMarkerExtra, Statement};
use spade_typeinference::TypeState;
use spade_types::ConcreteType;

use crate::error::Result;

use super::pass::Pass;

pub struct FlattenRegs<'a> {
    pub type_state: &'a TypeState,
    pub items: &'a ItemList,
    pub symtab: &'a FrozenSymtab,
}

impl<'a> Pass for FlattenRegs<'a> {
    fn visit_expression(&mut self, _expression: &mut Loc<spade_hir::Expression>) -> Result<()> {
        Ok(())
    }

    fn visit_statement(
        &mut self,
        statement: &Loc<Statement>,
    ) -> Result<Option<Vec<Loc<Statement>>>> {
        match &statement.inner {
            Statement::Binding(_) => Ok(None),
            Statement::Register(_) => Ok(None),
            Statement::Declaration(_) => Ok(None),
            Statement::PipelineRegMarker(extra) => match extra {
                Some(PipelineRegMarkerExtra::Count {
                    count,
                    count_typeexpr_id,
                }) => {
                    let ty = self.type_state.try_get_type_of_id(
                        *count_typeexpr_id,
                        self.symtab.symtab(),
                        &self.items.types,
                    );
                    let count = match ty {
                        Some(ConcreteType::Integer(val)) => val.to_usize().ok_or_else(|| {
                            diag_anyhow!(count, "Repetition count exceeds usize::MAX")
                        }),
                        Some(_) => Err(diag_anyhow!(
                            count,
                            "Inferred non-integer count for register repetition"
                        )),
                        None => Err(Diagnostic::error(count, "Could not infer register count")
                            .primary_label("Could not infer register count")
                            .help("This may becaused by a generic type used in the repition being unknown")),
                    }?;

                    Ok(Some(
                        (0..count)
                            .map(|_| Statement::PipelineRegMarker(None).at_loc(statement))
                            .collect(),
                    ))
                }
                Some(PipelineRegMarkerExtra::Condition(_)) => Ok(None),
                None => Ok(None),
            },
            Statement::Label(_) => Ok(None),
            Statement::Assert(_) => Ok(None),
            Statement::Set { .. } => Ok(None),
            Statement::WalSuffixed { .. } => Ok(None),
        }
    }

    fn visit_unit(&mut self, _unit: &mut spade_hir::Unit) -> Result<()> {
        Ok(())
    }
}
