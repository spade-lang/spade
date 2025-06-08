use crate::{Context, SelfContext};
use spade_common::id_tracker::{ExprIdTracker, ImplIdTracker};
use spade_diagnostics::diag_list::DiagList;
use spade_hir::symbol_table::SymbolTable;
use spade_hir::ItemList;

pub fn test_context() -> Context {
    Context {
        symtab: SymbolTable::new(),
        item_list: ItemList::new(),
        idtracker: ExprIdTracker::new(),
        impl_idtracker: ImplIdTracker::new(),
        pipeline_ctx: None,
        self_ctx: SelfContext::FreeStanding,
        current_unit: None,
        diags: DiagList::new(),
    }
}
