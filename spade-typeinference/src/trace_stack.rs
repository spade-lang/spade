use colored::*;
use itertools::Itertools;
use rustc_hash::FxHashMap as HashMap;
use spade_common::{cloning_rwlock::CloningRWLock, name::NameID};
use spade_types::KnownType;

use crate::{
    constraints::ConstraintRhs,
    equation::{TypeVarString, TypedExpression},
    requirements::Requirement,
    traits::TraitList,
    TypeState,
};

#[derive(Clone)]
pub struct TraceStack {
    entries: CloningRWLock<Vec<TraceStackEntry>>,
}

impl Default for TraceStack {
    fn default() -> Self {
        Self::new()
    }
}

impl TraceStack {
    pub fn new() -> Self {
        Self {
            entries: CloningRWLock::new(vec![]),
        }
    }

    // Inline because we don't want the compiler to construct the entries if they are
    // not going to be used
    #[inline]
    pub fn push(&self, entry_gen: impl Fn() -> TraceStackEntry) {
        if std::env::var("SPADE_TRACE_TYPEINFERENCE").is_ok() {
            self.entries.write().unwrap().push((entry_gen)())
        }
    }
}

#[derive(Clone)]
pub enum TraceStackEntry {
    /// Entering the specified visitor
    Enter(String),
    /// Exited the most recent visitor and the node had the specified type
    Exit,
    TryingUnify(TypeVarString, TypeVarString),
    /// Unified .0 with .1 producing .2. .3 were replaced
    Unified(
        TypeVarString,
        TypeVarString,
        TypeVarString,
        Vec<TypeVarString>,
    ),
    EnsuringImpls(TypeVarString, TraitList, bool),
    AddingEquation(TypedExpression, TypeVarString),
    AddingTraitBounds(TypeVarString, TraitList),
    AddRequirement(Requirement),
    ResolvedRequirement(Requirement),
    NewGenericList(HashMap<NameID, TypeVarString>),
    AddingConstraint(TypeVarString, ConstraintRhs),
    /// Inferring more from constraints
    InferringFromConstraints(TypeVarString, KnownType),
    AddingPipelineLabel(NameID, TypeVarString),
    RecoveringPipelineLabel(NameID, TypeVarString),
    PreAddingPipelineLabel(NameID, TypeVarString),
    /// Arbitrary message
    Message(String),
}

pub fn format_trace_stack(type_state: &TypeState) -> String {
    let stack = &type_state.owned.trace_stack;
    let mut result = String::new();
    let mut indent_amount = 0;

    for entry in stack.entries.read().unwrap().iter() {
        let mut next_indent_amount = indent_amount;
        let message = match entry {
            TraceStackEntry::Enter(function) => {
                next_indent_amount += 1;
                format!("{} `{}`", "call".white(), function.blue())
            }
            TraceStackEntry::AddingEquation(expr, t) => {
                format!("{} {:?} <- {}", "eq".yellow(), expr, t)
            }
            TraceStackEntry::Unified(lhs, rhs, result, replaced) => {
                next_indent_amount -= 1;
                format!(
                    "{} {}, {} -> {} (replacing {}) {}",
                    "unified".green(),
                    lhs,
                    rhs,
                    result,
                    replaced.iter().join(","),
                    format!(
                        "{}, {} -> {} (replacing {})",
                        lhs.1.inner,
                        rhs.1.inner,
                        result.1.inner,
                        replaced.iter().map(|r| r.1.inner).join(",")
                    )
                    .bright_black()
                )
            }
            TraceStackEntry::TryingUnify(lhs, rhs) => {
                next_indent_amount += 1;
                format!("{} of {} with {}", "trying unification".cyan(), lhs, rhs)
            }
            TraceStackEntry::EnsuringImpls(ty, tr, trait_is_expected) => {
                format!(
                    "{} {ty} as {} (trait_is_expected: {trait_is_expected})",
                    "ensuring impls".yellow(),
                    tr.display_with_meta(true, type_state),
                )
            }
            TraceStackEntry::InferringFromConstraints(lhs, rhs) => {
                format!("{} {lhs} as {rhs:?} from constraints", "inferring".purple(),)
            }
            TraceStackEntry::AddingConstraint(lhs, rhs) => {
                format!(
                    "adding constraint for {lhs} ({})",
                    rhs.debug_display(type_state)
                )
            }
            TraceStackEntry::NewGenericList(mapping) => {
                format!(
                    "{}: {}",
                    "new generic list".bright_cyan(),
                    mapping
                        .iter()
                        .map(|(k, v)| format!("{k} -> {v}"))
                        .join(", ")
                )
            }
            TraceStackEntry::AddingPipelineLabel(name, var) => {
                format!("{} {name:?} as {var}", "declaring label".bright_black())
            }
            TraceStackEntry::PreAddingPipelineLabel(name, var) => {
                format!("{} {name:?} as {var}", "pre-declaring label".bright_black())
            }
            TraceStackEntry::RecoveringPipelineLabel(name, var) => {
                format!(
                    "{} {name:?} as {var}",
                    "using previously declared label".bright_black()
                )
            }
            TraceStackEntry::Message(msg) => {
                format!("{}: {}", "m".purple(), msg)
            }
            TraceStackEntry::Exit => {
                next_indent_amount -= 1;
                String::new()
            }
            TraceStackEntry::AddRequirement(req) => format!("{} {req:?}", "added".yellow()),
            TraceStackEntry::ResolvedRequirement(req) => format!("{} {req:?}", "resolved".blue()),
            TraceStackEntry::AddingTraitBounds(tvar, traits) => {
                format!("{} {traits:?} to {tvar}", "adding trait bound".yellow())
            }
        };
        if let TraceStackEntry::Exit = entry {
        } else {
            for _ in 0..indent_amount {
                result += "| ";
            }
            result += &message;
            result += "\n";
        }
        indent_amount = next_indent_amount;
    }
    result
}
