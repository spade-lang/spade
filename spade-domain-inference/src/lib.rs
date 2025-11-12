// This implementation is based on
// https://www.cl.cam.ac.uk/~nk480/bidir.pdf
// which was made easier to understand by
// https://dl.acm.org/doi/pdf/10.1145/3450952

pub mod domain_var;
mod tracing;
mod visiting;

use std::{
    collections::HashMap,
    sync::{Arc, RwLock},
};

use domain_var::DomainVar;
use serde::{Deserialize, Serialize};
use spade_common::{id_tracker::ExprID, location_info::Loc, name::NameID};
use spade_diagnostics::{diag_list::DiagList, Diagnostic};
use spade_hir::symbol_table::SymbolTable;
use spade_typeinference::{
    equation::TypeVarID, TypeState,
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

/// Denoted `\hat{x}`` in the paper
#[derive(Clone, Serialize, Deserialize, Debug, PartialEq)]
pub struct FreeDomainVar(u64);

pub struct Context<'a> {
    pub types: &'a TypeState,
    pub symtab: &'a SymbolTable,
}

/// State of the type inference algorithm
#[derive(Clone, Serialize, Deserialize)]
pub struct DomainState {
    pub name_domains: HashMap<NameID, DomainVar>,
    pub expr_domains: HashMap<ExprID, DomainVar>,

    // Contexts as defined in the paper
    next_free_var: u64,
    pub contexts: Vec<Vec<FreeDomainVar>>,

    #[serde(skip)]
    pub traces: Arc<RwLock<Vec<TraceEntry>>>,

    #[serde(skip)]
    pub diags: DiagList,
}

impl DomainState {
    fn with_pushed_context(&mut self, f: impl Fn(&mut Self)) {
        self.contexts.push(vec![]);
        f(self);
        self.contexts.pop();
    }
}

impl DomainState {
    pub fn new() -> Self {
        let result = Self {
            name_domains: HashMap::new(),
            expr_domains: HashMap::new(),
            next_free_var: 0,
            contexts: vec![],
            traces: Arc::new(RwLock::new(vec![])),
            diags: DiagList::new(),
        };

        result
    }
}

