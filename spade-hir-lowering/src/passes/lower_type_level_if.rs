use num::BigInt;
use spade_common::location_info::{Loc, WithLocation};
use spade_diagnostics::diag_bail;
use spade_hir::{symbol_table::FrozenSymtab, ExprKind, ItemList};
use spade_typeinference::TypeState;

use crate::error::Result;

use super::pass::Pass;

pub struct LowerTypeLevelIf<'a> {
    pub type_state: &'a TypeState,
    pub items: &'a ItemList,
    pub symtab: &'a FrozenSymtab,
}

impl<'a> Pass for LowerTypeLevelIf<'a> {
    fn visit_expression(&mut self, expression: &mut Loc<spade_hir::Expression>) -> Result<()> {
        // TODO: Somehow Make sure no TLIfs are in the wrong place
        match &expression.kind {
            ExprKind::TypeLevelIf(cond, on_true, on_false) => {
                // TODO: Promote this to a function
                let t = self.type_state.type_of_id_result(
                    cond.id.at_loc(cond),
                    self.symtab.symtab(),
                    &self.items.types,
                )?;

                match t {
                    spade_types::ConcreteType::Integer(val) => {
                        if val == BigInt::ZERO {
                            *expression = on_false.as_ref().clone()
                        } else {
                            *expression = on_true.as_ref().clone()
                        }
                        Ok(())
                    }
                    // TODO: Make sure this isn't triggered trivially
                    _ => diag_bail!(cond, "Inferred non type level integer for type level if"),
                }
            }
            _ => Ok(()),
        }
    }

    fn visit_unit(&mut self, _unit: &mut spade_hir::Unit) -> Result<()> {
        Ok(())
    }
}
