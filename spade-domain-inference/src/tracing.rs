use std::sync::{Arc, RwLock};

use colored::Colorize;
use spade_hir::{pretty_debug::PrettyDebug, Expression};
use spade_typeinference::equation::TypeVarID;

use crate::{domain_var::DomainVar, DomainState, TypeVarIDExt};

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
    Replacing(TypeVarID, TypeVarID),
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
        if std::env::var("SPADE_TRACE_DOMAININFERENCE").is_ok() {
            for stack in self.replacements.all() {
                for (from, to) in stack.borrow().iter() {
                    println!("{} -> {}", from.inner, to.inner)
                }
            }

            let mut result = String::new();
            let mut indent_level = 0;

            for entry in self.traces.read().unwrap().iter() {
                let mut next_indent_level = indent_level;
                let message = match entry {
                    TraceEntry::VisitingUnit(name) => {
                        next_indent_level += 1;
                        format!("{} `{}`", "visiting unit".blue(), name.white())
                    }
                    TraceEntry::SynthExpr(expr) => {
                        next_indent_level += 1;
                        format!("{} `{}`", "synth expr".green(), expr.white())
                    }
                    TraceEntry::CheckExpr { expr, expected } => {
                        next_indent_level += 1;
                        format!(
                            "{} `{}` == {:?}",
                            "check expr".purple(),
                            expr.pretty_debug().white(),
                            expected
                        )
                    }
                    TraceEntry::VisitingStatement(statement) => {
                        next_indent_level += 1;
                        format!("{} `{}`", "visiting statement".blue(), statement.white())
                    }
                    TraceEntry::SynthPattern(pat) => {
                        next_indent_level += 1;
                        format!("{} `{}`", "synth pat".green(), pat.white())
                    }
                    TraceEntry::CheckPattern(pat) => {
                        next_indent_level += 1;
                        format!("{} `{}`", "check pat".purple(), pat.white())
                    }
                    TraceEntry::Binding(binder, bindee) => {
                        format!("{} {}->{}", "binding".yellow(), binder, bindee.inner)
                    }
                    TraceEntry::Replacing(from, to) => {
                        format!(
                            "{} {}->{} ({:?} -> {:?})",
                            "replacing".bright_yellow(),
                            from.inner,
                            to.inner,
                            from.resolve_domain(self),
                            to.resolve_domain(self)
                        )
                    }
                    TraceEntry::Exit => {
                        next_indent_level -= 1;
                        String::new()
                    }
                };

                if let TraceEntry::Exit = entry {
                } else {
                    for _ in 0..indent_level {
                        result += "| ";
                    }
                    result += &message;
                    result += "\n";
                }
                indent_level = next_indent_level;
            }
            println!("{result}")
        }
    }
}
