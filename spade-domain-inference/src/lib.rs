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
use spade_hir::{domains::DomainConstraint, symbol_table::SymbolTable, Expression, Pattern};
use spade_typeinference::{
    equation::TypeVarID, replacement::ReplacementStack, GenericListToken, TypeState,
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

pub struct Context<'a> {
    pub types: &'a TypeState,
    pub symtab: &'a SymbolTable,
}

/// State of the type inference algorithm
#[derive(Clone, Serialize, Deserialize)]
pub struct DomainState {
    pub name_domains: HashMap<NameID, DomainVar>,
    pub expr_domains: HashMap<ExprID, DomainVar>,


    #[serde(skip)]
    pub traces: Arc<RwLock<Vec<TraceEntry>>>,

    #[serde(skip)]
    pub diags: DiagList,
}

impl DomainState {
    pub fn new() -> Self {
        let result = Self {
            name_domains: HashMap::new(),
            expr_domains: HashMap::new(),
            traces: Arc::new(RwLock::new(vec![])),
            diags: DiagList::new(),
        };

        result
    }
}

