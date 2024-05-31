use spade_common::location_info::Loc;
use spade_hir::{symbol_table::FrozenSymtab, ItemList, Statement};
use spade_typeinference::TypeState;

use super::pass::Pass;

pub struct LowerFsms<'a> {
    pub type_state: &'a TypeState,
    pub items: &'a ItemList,
    pub symtab: &'a FrozenSymtab,
}

impl<'a> Pass for LowerFsms<'a> {
    fn visit_expression(
        &mut self,
        expression: &mut Loc<spade_hir::Expression>,
    ) -> crate::error::Result<()> {
        match &expression.inner.kind {
            spade_hir::ExprKind::Fsm(f) => {}
            spade_hir::ExprKind::Identifier(_)
            | spade_hir::ExprKind::IntLiteral(_)
            | spade_hir::ExprKind::BoolLiteral(_)
            | spade_hir::ExprKind::BitLiteral(_)
            | spade_hir::ExprKind::TypeLevelInteger(_)
            | spade_hir::ExprKind::CreatePorts
            | spade_hir::ExprKind::TupleLiteral(_)
            | spade_hir::ExprKind::ArrayLiteral(_)
            | spade_hir::ExprKind::Index(_, _)
            | spade_hir::ExprKind::RangeIndex { .. }
            | spade_hir::ExprKind::TupleIndex(_, _)
            | spade_hir::ExprKind::FieldAccess(_, _)
            | spade_hir::ExprKind::MethodCall { .. }
            | spade_hir::ExprKind::Call { .. }
            | spade_hir::ExprKind::BinaryOperator(_, _, _)
            | spade_hir::ExprKind::UnaryOperator(_, _)
            | spade_hir::ExprKind::Match(_, _)
            | spade_hir::ExprKind::Block(_)
            | spade_hir::ExprKind::If(_, _, _)
            | spade_hir::ExprKind::PipelineRef { .. }
            | spade_hir::ExprKind::StageValid
            | spade_hir::ExprKind::StageReady
            | spade_hir::ExprKind::Null => {}
        }

        Ok(())
    }
}

impl<'a> LowerFsms<'a> {
    fn desugar_loops(&mut self, statements: &mut Vec<Statement>) {}
}
