use std::sync::{Arc, Mutex};

use crate::{Context, SelfContext};
use spade_common::id_tracker::{ExprIdTracker, GenericIdTracker, ImplIdTracker};
use spade_diagnostics::diag_list::DiagList;
use spade_hir::expression::Safety;
use spade_hir::symbol_table::SymbolTable;
use spade_hir::ItemList;

pub fn test_context() -> Context {
    let diags = Arc::new(Mutex::new(DiagList::new()));
    Context {
        symtab: SymbolTable::new(diags.clone()),
        item_list: ItemList::new(),
        idtracker: Arc::new(ExprIdTracker::new()),
        impl_idtracker: ImplIdTracker::new(),
        generic_idtracker: GenericIdTracker::new(),
        pipeline_ctx: None,
        self_ctx: SelfContext::FreeStanding,
        current_unit: None,
        diags,
        safety: Safety::Default,
    }
}
