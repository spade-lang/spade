use std::{collections::HashMap, sync::RwLock};

use colored::*;
use itertools::Itertools;
use spade_common::name::NameID;
use spade_types::KnownType;

use crate::{
    constraints::ConstraintRhs,
    equation::{TraitList, TypeVar, TypedExpression},
    requirements::Requirement,
    TypeState,
};

pub struct TraceStack {
    entries: RwLock<Vec<TraceStackEntry>>,
}

impl Default for TraceStack {
    fn default() -> Self {
        Self::new()
    }
}

impl TraceStack {
    pub fn new() -> Self {
        Self {
            entries: RwLock::new(vec![]),
        }
    }
    pub fn push(&self, entry: TraceStackEntry) {
        self.entries.write().unwrap().push(entry)
    }
}

pub enum TraceStackEntry {
    /// Entering the specified visitor
    Enter(String),
    /// Exited the most recent visitor and the node had the specified type
    Exit,
    TryingUnify(TypeVar, TypeVar),
    /// Unified .0 with .1 producing .2. .3 were replaced
    Unified(TypeVar, TypeVar, TypeVar, Vec<TypeVar>),
    EnsuringImpls(TypeVar, TraitList, bool),
    AddingEquation(TypedExpression, TypeVar),
    AddingTraitBounds(TypeVar, TraitList),
    AddRequirement(Requirement),
    ResolvedRequirement(Requirement),
    NewGenericList(HashMap<NameID, TypeVar>),
    AddingConstraint(TypeVar, ConstraintRhs),
    /// Inferring more from constraints
    InferringFromConstraints(TypeVar, KnownType),
    AddingPipelineLabel(NameID, TypeVar),
    RecoveringPipelineLabel(NameID, TypeVar),
    PreAddingPipelineLabel(NameID, TypeVar),
    /// Arbitrary message
    Message(String),
}

pub fn format_trace_stack(type_state: &TypeState) -> String {
    let stack = &type_state.trace_stack;
    let mut result = String::new();
    let mut indent_amount = 0;

    // Prints a type var with some formatting if there is a type variable that
    // has not been replaced by a concrete type at the end of type inference
    let maybe_replaced = |t: &TypeVar| {
        let replacement = type_state.check_var_for_replacement(t.clone());
        if &replacement == t && matches!(replacement, TypeVar::Unknown(_, _, _, _)) {
            format!("{}", format!("{:?}", t).bright_yellow())
        } else {
            format!("{:?}", t)
        }
    };

    for entry in stack.entries.read().unwrap().iter() {
        let mut next_indent_amount = indent_amount;
        let message = match entry {
            TraceStackEntry::Enter(function) => {
                next_indent_amount += 1;
                format!("{} `{}`", "call".white(), function.blue())
            }
            TraceStackEntry::AddingEquation(expr, t) => {
                format!("{} {:?} <- {}", "eq".yellow(), expr, maybe_replaced(t))
            }
            TraceStackEntry::Unified(lhs, rhs, result, replaced) => {
                next_indent_amount -= 1;
                format!(
                    "{} {}, {} -> {} (replacing {})",
                    "unified".green(),
                    maybe_replaced(lhs),
                    maybe_replaced(rhs),
                    maybe_replaced(result),
                    replaced.iter().map(maybe_replaced).join(",")
                )
            }
            TraceStackEntry::TryingUnify(lhs, rhs) => {
                next_indent_amount += 1;
                format!(
                    "{} of {} with {}",
                    "trying unification".cyan(),
                    maybe_replaced(lhs),
                    maybe_replaced(rhs)
                )
            }
            TraceStackEntry::EnsuringImpls(ty, tr, trait_is_expected) => {
                format!(
                    "{} {ty} as {tr:?} (trait_is_expected: {trait_is_expected})",
                    "ensuring impls".yellow(),
                    ty = maybe_replaced(ty)
                )
            }
            TraceStackEntry::InferringFromConstraints(lhs, rhs) => {
                format!(
                    "{} {lhs} as {rhs:?} from constraints",
                    "inferring".purple(),
                    lhs = maybe_replaced(lhs),
                )
            }
            TraceStackEntry::AddingConstraint(lhs, rhs) => {
                format!("adding constraint {lhs} {rhs:?}", lhs = maybe_replaced(lhs))
            }
            TraceStackEntry::NewGenericList(mapping) => {
                format!(
                    "{}: {}",
                    "new generic list".bright_cyan(),
                    mapping
                        .iter()
                        .map(|(k, v)| format!("{k} -> {}", maybe_replaced(v)))
                        .join(", ")
                )
            }
            TraceStackEntry::AddingPipelineLabel(name, var) => {
                format!("{} {name:?} as {var:?}", "declaring label".bright_black())
            }
            TraceStackEntry::PreAddingPipelineLabel(name, var) => {
                format!(
                    "{} {name:?} as {var:?}",
                    "pre-declaring label".bright_black()
                )
            }
            TraceStackEntry::RecoveringPipelineLabel(name, var) => {
                format!(
                    "{} {name:?} as {var:?}",
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
                format!("{} {traits:?} to {tvar:?}", "adding trait bound".yellow())
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
