use std::collections::HashSet;

use num::BigInt;
use spade_common::{id_tracker::ExprID, location_info::Loc};
use spade_diagnostics::{diag_bail, Diagnostic};
use spade_hir::{symbol_table::FrozenSymtab, ExprKind, Expression, ItemList};
use spade_typeinference::TypeState;

use crate::error::Result;

use super::pass::Pass;

pub struct LowerTypeLevelIf<'a> {
    pub type_state: &'a TypeState,
    pub items: &'a ItemList,
    pub symtab: &'a FrozenSymtab,

    pub allowed_ids: HashSet<ExprID>,
}

impl<'a> Pass for LowerTypeLevelIf<'a> {
    fn visit_expression(&mut self, expression: &mut Loc<spade_hir::Expression>) -> Result<()> {
        match &expression.kind {
            ExprKind::TypeLevelIf(cond, on_true, on_false) => {
                if !self.allowed_ids.contains(&expression.id) {
                    return Err(Diagnostic::error(
                        &*expression,
                        "Type level if can only appear as the return value of a unit",
                    )
                    .primary_label("Type level if is not allowed here"));
                }

                let t = self.type_state.concrete_type_of(
                    cond,
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
                    _ => diag_bail!(cond, "Inferred non type level integer for type level if"),
                }
            }
            _ => Ok(()),
        }
    }

    fn visit_unit(&mut self, unit: &mut spade_hir::Unit) -> Result<()> {
        if let Some(result) = &unit.body.assume_block().result {
            self.mark_allowed_tlifs(result);
        }
        Ok(())
    }
}

impl<'a> LowerTypeLevelIf<'a> {
    fn mark_allowed_tlifs(&mut self, expr: &Expression) {
        match &expr.kind {
            ExprKind::TypeLevelIf(_loc, loc1, loc2) => {
                self.allowed_ids.insert(expr.id);
                self.mark_allowed_tlifs(loc1);
                self.mark_allowed_tlifs(loc2);
            }
            ExprKind::Block(block) => {
                if let Some(result) = &block.result {
                    self.mark_allowed_tlifs(result);
                }
            }
            _ => {}
        }
    }
}
