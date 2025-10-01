use std::sync::{Arc, RwLock};

use spade_hir::{Expression};
use spade_typeinference::equation::TypeVarID;

use crate::{domain_var::DomainVar, DomainState};

#[derive(Clone)]
pub enum TraceEntry {
    VisitingUnit(String),
    SynthExpr(String),
    CheckExpr {
        expr: Expression,
        expected: DomainVar,
    },
    VisitingStatement(String),
    SynthPattern(String),
    CheckPattern(String),
    Binding(String, TypeVarID),
    Replacing(DomainVar, DomainVar),
    Exit,
}

#[must_use]
pub struct TraceBomb {
    t: Arc<RwLock<Vec<TraceEntry>>>,
}

impl Drop for TraceBomb {
    fn drop(&mut self) {
        if std::env::var("SPADE_TRACE_DOMAININFERENCE").is_ok() {
            self.t.write().unwrap().push(TraceEntry::Exit)
        }
    }
}

impl DomainState {
    pub fn trace(&self, tracer: impl Fn() -> TraceEntry) {
        if std::env::var("SPADE_TRACE_DOMAININFERENCE").is_ok() {
            self.traces.write().unwrap().push(tracer());
        }
    }

    pub fn trace_scope(&self, tracer: impl Fn() -> TraceEntry) -> Option<TraceBomb> {
        if std::env::var("SPADE_TRACE_DOMAININFERENCE").is_ok() {
            let t = self.traces.clone();
            t.write().unwrap().push(tracer());
            Some(TraceBomb { t })
        } else {
            None
        }
    }

    pub fn maybe_print_trace(&self) {
        if std::env::var("SPADE_TRACE_DOMAININFERENCE").is_ok() {}
    }
}
