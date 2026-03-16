use std::sync::{Arc, Mutex, RwLock};

use crate::{Context, SelfContext};
use rustc_hash::FxHashMap as HashMap;
use spade_common::id_tracker::{ExprIdTracker, GenericIdTracker, ImplIdTracker};
use spade_diagnostics::{CodeBundle, diag_list::DiagList};
use spade_hir::ItemList;
use spade_hir::expression::Safety;
use spade_hir::symbol_table::SymbolTable;

pub fn test_context() -> Context {
    let code = Arc::new(RwLock::new(CodeBundle::from_files(&[])));
    let diags = Arc::new(Mutex::new(DiagList::new()));

    Context {
        symtab: SymbolTable::new(diags.clone()),
        item_list: ItemList::new(),
        macros: HashMap::default(),
        code,
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
