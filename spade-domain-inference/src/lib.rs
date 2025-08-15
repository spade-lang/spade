pub mod domain_var;
mod tracing;
mod visiting;

use std::{
    cell::RefCell,
    collections::{BTreeSet, HashMap},
    sync::{Arc, RwLock},
};

use domain_var::DomainVar;
use serde::{Deserialize, Serialize};
use spade_common::{id_tracker::ExprID, location_info::Loc, name::NameID};
use spade_diagnostics::{diag_list::DiagList, Diagnostic};
use spade_hir::{
    domains::DomainConstraint, Expression, Pattern
};
use spade_typeinference::{
    equation::TypeVarID, replacement::ReplacementStack,
    GenericListToken,
};
use tracing::TraceEntry;

type Result<T> = std::result::Result<T, Diagnostic>;

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
enum DomainedExpression {
    AnnonymousOuter(Loc<()>),
    AnnonymousInner(Loc<()>),
    Name(NameID),
    Id(ExprID),
}

type DomainEquations = HashMap<DomainedExpression, TypeVarID>;

/// State of the type inference algorithm
#[derive(Clone, Serialize, Deserialize)]
pub struct DomainState {
    /// All types are referred to by their index to allow type vars changing inside
    /// the type state while the types are "out in the wild". The TypeVarID is an index
    /// into this type_vars list which is used to look up the actual type as currently
    /// seen by the type state
    domain_vars: Vec<DomainVar>,
    replacements: ReplacementStack,
    /// This key is used to prevent bugs when multiple type states are mixed. Each TypeVarID
    /// holds the value of the key of the type state which created it, and this is checked
    /// to ensure that type vars are not mixed. The key is initialized randomly on type
    /// state creation
    key: u64,
    /// A type state can also support keys from other sources, this is tracked here
    keys: BTreeSet<u64>,

    equations: DomainEquations,

    next_typeid: RefCell<u64>,
    // List of the mapping between generic parameters and type vars.
    // The key is the index of the expression for which this generic list is associated. (if this
    // is a generic list for a call whose expression id is x to f<A, B>, then generic_lists[x] will
    // be {A: <type var>, b: <type var>}
    // Managed here because unification must update *all* TypeVars in existence.
    generic_lists: HashMap<GenericListToken, HashMap<NameID, DomainVar>>,

    /// An error type that can be accessed anywhere without mut access. This is an option
    /// to facilitate safe initialization, in practice it can never be None
    error_domain: Option<TypeVarID>,

    #[serde(skip)]
    pub traces: Arc<RwLock<Vec<TraceEntry>>>,

    #[serde(skip)]
    pub diags: DiagList,
}

impl DomainState {
    pub fn new() -> Self {
        let key = fastrand::u64(..);
        let mut result = Self {
            domain_vars: vec![],
            key,
            keys: [key].into_iter().collect(),
            equations: HashMap::new(),
            next_typeid: 0.into(),
            generic_lists: HashMap::new(),
            replacements: ReplacementStack::new(),
            error_domain: None,
            traces: Arc::new(RwLock::new(vec![])),
            diags: DiagList::new(),
        };

        result.error_domain = Some(result.add_domain_var(DomainVar::Error));
        result
    }

    fn add_domain_var(&mut self, var: DomainVar) -> TypeVarID {
        let idx = self.domain_vars.len();
        self.domain_vars.push(var);
        TypeVarID {
            inner: idx,
            type_state_key: self.key,
        }
    }

    fn maybe_domain_of(&self, of: &DomainedExpression) -> Option<&TypeVarID> {
        self.equations.get(&of)
    }

    fn new_any(&mut self) -> TypeVarID {
        self.add_domain_var(DomainVar::Unknown(vec![]))
    }

    fn new_with_constraints(&mut self, constraints: Vec<Loc<DomainConstraint>>) -> TypeVarID {
        self.add_domain_var(DomainVar::Unknown(constraints))
    }

    fn replace(&mut self, from: TypeVarID, to: TypeVarID) {
        self.trace(|| TraceEntry::Replacing(from, to));
        let from = from.get_domain(self);
        if from != to {
            self.replacements.insert(from, to)
        }
    }
}

trait TypeVarIDExt {
    fn resolve_domain<'a>(&'_ self, state: &'a DomainState) -> &'a DomainVar;

    fn insert_for_domained(self, f: DomainedExpression, state: &mut DomainState);
}
impl TypeVarIDExt for TypeVarID {
    fn resolve_domain<'a>(&'_ self, state: &'a DomainState) -> &'a DomainVar {
        &state.domain_vars[self.get_domain(state).inner]
    }

    fn insert_for_domained(self, f: DomainedExpression, state: &mut DomainState) {
        state.trace(|| {
            let binder = match &f {
                DomainedExpression::AnnonymousOuter(_) => "AnnonOuter".to_string(),
                DomainedExpression::AnnonymousInner(_) => "AnnonInner".to_string(),
                DomainedExpression::Name(name) => name.to_string(),
                DomainedExpression::Id(id) => format!("${}", id.0),
            };
            TraceEntry::Binding(binder, self)
        });
        state.equations.insert(f, self);
    }
}

pub trait HasDomain: std::fmt::Debug {
    fn get_domain(&self, state: &DomainState) -> TypeVarID {
        self.try_get_domain(state)
            .unwrap_or(state.error_domain.unwrap())
    }

    fn try_get_domain(&self, state: &DomainState) -> Option<TypeVarID> {
        let id = self.get_domain_impl(state);
        id.map(|id| state.replacements.get(id))
    }

    fn get_domain_impl(&self, state: &DomainState) -> Option<TypeVarID>;
}

impl HasDomain for TypeVarID {
    fn get_domain_impl(&self, _state: &DomainState) -> Option<TypeVarID> {
        Some(*self)
    }
}
impl HasDomain for Loc<TypeVarID> {
    fn get_domain_impl(&self, state: &DomainState) -> Option<TypeVarID> {
        self.inner.try_get_domain(state)
    }
}
impl HasDomain for DomainedExpression {
    fn get_domain_impl(&self, state: &DomainState) -> Option<TypeVarID> {
        state.maybe_domain_of(self).cloned()
    }
}
impl HasDomain for Expression {
    fn get_domain_impl(&self, state: &DomainState) -> Option<TypeVarID> {
        state
            .maybe_domain_of(&DomainedExpression::Id(self.id))
            .cloned()
    }
}
impl HasDomain for Loc<Expression> {
    fn get_domain_impl(&self, state: &DomainState) -> Option<TypeVarID> {
        state
            .maybe_domain_of(&DomainedExpression::Id(self.inner.id))
            .cloned()
    }
}
impl HasDomain for Pattern {
    fn get_domain_impl(&self, state: &DomainState) -> Option<TypeVarID> {
        state
            .maybe_domain_of(&DomainedExpression::Id(self.id))
            .cloned()
    }
}
impl HasDomain for Loc<Pattern> {
    fn get_domain_impl(&self, state: &DomainState) -> Option<TypeVarID> {
        state
            .maybe_domain_of(&DomainedExpression::Id(self.inner.id))
            .cloned()
    }
}
impl HasDomain for NameID {
    fn get_domain_impl(&self, state: &DomainState) -> Option<TypeVarID> {
        state
            .maybe_domain_of(&DomainedExpression::Name(self.clone()))
            .cloned()
    }
}
