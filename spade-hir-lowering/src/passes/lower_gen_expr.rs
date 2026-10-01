use rustc_hash::FxHashSet as HashSet;
use spade_common::{
    id_tracker::ExprID,
    location_info::{Loc, WithLocation},
};
use spade_diagnostics::{Diagnostic, diag_bail};
use spade_hir::{ExprKind, Expression, ItemList, symbol_table::FrozenSymtab};
use spade_typeinference::TypeState;
use spade_types::ConcreteType;

use crate::error::Result;

use super::pass::Pass;

pub struct LowerGenExpr<'a> {
    pub type_state: &'a TypeState,
    pub items: &'a ItemList,
    pub symtab: &'a FrozenSymtab,

    pub allowed_ids: HashSet<ExprID>,
}

impl<'a> Pass for LowerGenExpr<'a> {
    fn visit_expression(&mut self, expression: &mut Loc<spade_hir::Expression>) -> Result<()> {
        match &expression.kind {
            ExprKind::TypeLevelIf {
                cond,
                on_true,
                on_false,
            } => {
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
                    spade_types::ConcreteType::Bool(val) => {
                        if val {
                            *expression = on_true.as_ref().clone()
                        } else {
                            *expression = on_false.as_ref().clone()
                        }
                        Ok(())
                    }
                    _ => diag_bail!(cond, "Inferred non type level bool for type level if"),
                }
            }
            ExprKind::TypeLevelMatch {
                expression: e,
                branches,
            } => {
                if !self.allowed_ids.contains(&expression.id) {
                    return Err(Diagnostic::error(
                        &*expression,
                        "Type level match can only appear as the return value of a unit",
                    )
                    .primary_label("Type level match is not allowed here"));
                }

                let concrete_e =
                    self.type_state
                        .concrete_type_of(e, self.symtab.symtab(), &self.items.types)?;

                for (pat, branch) in branches.clone() {
                    let loc = pat.loc();

                    let pat_matches_e = if let Some(p) = pat.inner {
                        let concrete_pat = self.type_state.concrete_type_of(
                            &p.at_loc(&loc),
                            self.symtab.symtab(),
                            &self.items.types,
                        )?;

                        concrete_pat == concrete_e
                    } else {
                        true
                    };

                    if pat_matches_e {
                        *expression = branch.clone();
                        return Ok(());
                    }
                }

                // No branch matched the value. Try to add a fallback `()` if it
                // typechecks, otherwise error.
                let concrete_ty = self.type_state.concrete_type_of(
                    &*expression,
                    self.symtab.symtab(),
                    &self.items.types,
                )?;

                if concrete_ty == ConcreteType::Tuple(vec![]) {
                    *expression = spade_hir::Expression {
                        kind: ExprKind::TupleLiteral(vec![]),
                        id: expression.id,
                    }
                    .at_loc(expression);

                    Ok(())
                } else {
                    return Err(Diagnostic::error(
                        &*expression,
                        "`gen match` is not exhaustive but is required to return a value",
                    )
                    .primary_label(format!("`{concrete_e}` is not covered")));
                }
            }
            _ => Ok(()),
        }
    }

    fn visit_unit(&mut self, unit: &mut spade_hir::Unit) -> Result<()> {
        self.mark_allowed_gen(&unit.body);
        Ok(())
    }
}

impl<'a> LowerGenExpr<'a> {
    fn mark_allowed_gen(&mut self, expr: &Expression) {
        match &expr.kind {
            ExprKind::TypeLevelIf {
                cond: _,
                on_true,
                on_false,
            } => {
                self.allowed_ids.insert(expr.id);
                self.mark_allowed_gen(on_true);
                self.mark_allowed_gen(on_false);
            }
            ExprKind::TypeLevelMatch {
                expression: _,
                branches,
            } => {
                self.allowed_ids.insert(expr.id);
                for (_, expr) in branches {
                    self.mark_allowed_gen(expr);
                }
            }
            ExprKind::Block(block) => {
                for stmt in &block.statements {
                    match &stmt.inner {
                        spade_hir::Statement::Binding(binding) => {
                            self.mark_allowed_gen(&binding.value);
                        }
                        _ => {}
                    }
                }
                if let Some(result) = &block.result {
                    self.mark_allowed_gen(result);
                }
            }
            _ => {}
        }
    }
}
