#[macro_export]
macro_rules! test_context {
    () => {
        Context {
            symtab: &mut crate::SymbolTable::new(),
            idtracker: &mut crate::ExprIdTracker::new(),
            impl_idtracker: &mut crate::ImplIdTracker::new(),
            pipeline_ctx: None,
            self_ctx: &crate::SelfContext::FreeStanding,
        }
    };
}
