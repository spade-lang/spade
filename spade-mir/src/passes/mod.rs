use rustc_hash::FxHashMap as HashMap;
use spade_common::id_tracker::ExprIdTracker;

use crate::Statement;

pub mod auto_clock_gating;
pub mod deduplicate_mut_wires;
mod split_compound_regs;

pub trait MirPass {
    fn name(&self) -> &'static str;

    fn transform_statements(
        &self,
        stmts: &[Statement],
        expr_idtracker: &ExprIdTracker,
    ) -> Vec<Statement>;
}

pub fn mir_passes() -> HashMap<&'static str, Box<dyn MirPass + Sync + Send>> {
    vec![
        Box::new(auto_clock_gating::AutoGating {}) as Box<dyn MirPass + Sync + Send>,
        Box::new(split_compound_regs::SplitCompoundRegs {}) as Box<dyn MirPass + Sync + Send>,
    ]
    .into_iter()
    .map(|p| (p.name(), p))
    .collect()
}
