mod visiting;

use std::{cell::RefCell, collections::{BTreeSet, HashMap}};

use serde::{Deserialize, Serialize};
use spade_common::{id_tracker::ExprID, location_info::Loc, name::NameID};
use spade_diagnostics::{diag_list::DiagList, Diagnostic};
use spade_hir::domains::Domain;
use spade_typeinference::{equation::TypeVarID, replacement::ReplacementStack, GenericListToken};

type Result<T> = std::result::Result<T, Diagnostic>;

#[derive(Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
enum DomainedExpression {
    AnnonymousOuter(Loc<()>),
    AnnonymousInner(Loc<()>),
    Name(Loc<NameID>),
    Expr(Loc<ExprID>)
}

#[derive(Clone, Serialize, Deserialize)]
enum DomainVar {
    Error,
    Unknown,
    Known(Domain)
}

pub type DomainEquations = HashMap<DomainedExpression, TypeVarID>;

/// State of the type inference algorithm
#[derive(Clone, Serialize, Deserialize)]
pub struct DomainState {
    /// All types are referred to by their index to allow type vars changing inside
    /// the type state while the types are "out in the wild". The TypeVarID is an index
    /// into this type_vars list which is used to look up the actual type as currently
    /// seen by the type state
    domain_vars: Vec<DomainVar>,
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

    replacements: ReplacementStack,

    #[serde(skip)]
    pub diags: DiagList,
}

impl DomainState {
    pub fn new() -> Self {
        let key = fastrand::u64(..);
        Self {
            domain_vars: vec![],
            key,
            keys: [key].into_iter().collect(),
            equations: HashMap::new(),
            next_typeid: 0.into(),
            generic_lists: HashMap::new(),
            replacements: ReplacementStack::new(),
            diags: DiagList::new(),
        }
    }

    fn add_domain_var(&mut self, var: DomainVar) -> TypeVarID {
        let idx = self.domain_vars.len();
        self.domain_vars.push(var);
        TypeVarID {
            inner: idx,
            type_state_key: self.key,
        }
    }

}

