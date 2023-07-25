use itertools::Itertools;
use spade_mir::Statement;
use spade_mir::ValueName;

use crate::name_map::NameSource;
use crate::name_map::NameSourceMap;

pub struct StatementList {
    stmts: Vec<Statement>,
    name_map: NameSourceMap,
}

impl Default for StatementList {
    fn default() -> Self {
        Self::new()
    }
}

impl StatementList {
    pub fn new() -> StatementList {
        Self {
            stmts: vec![],
            name_map: NameSourceMap::new(),
        }
    }

    /// Pushes a statement which has no associated name or id. Currently used for asserts,
    /// wal_tracing, and pipeline enable signals
    pub fn push_anonymous(&mut self, stmt: Statement) {
        self.stmts.push(stmt)
    }

    /// Pushes a statement which is the primary statement associated with the specified expression
    pub fn push_primary(&mut self, stmt: Statement, source: impl Into<NameSource>) {
        let name = match &stmt {
            Statement::Binding(b) => Some(b.name.clone()),
            Statement::Register(r) => Some(r.name.clone()),
            Statement::Constant(id, _, _) => Some(ValueName::Expr(*id)),
            Statement::Assert(_) => None,
            Statement::Set { .. } => None,
            Statement::WalTrace { .. } => None,
        };
        self.stmts.push(stmt);
        if let Some(name) = name {
            self.name_map.insert_primary(&name, source.into())
        }
    }

    /// Pushes a statement which is used as a supporting statement for the generation
    /// of the specified source. The description should give a short description of what
    /// this value does. For example, being part of a condition, or being a pipeline register
    pub fn push_secondary(
        &mut self,
        stmt: Statement,
        source: impl Into<NameSource>,
        description: &str,
    ) {
        let name = match &stmt {
            Statement::Binding(b) => Some(b.name.clone()),
            Statement::Register(r) => Some(r.name.clone()),
            Statement::Constant(id, _, _) => Some(ValueName::Expr(*id)),
            Statement::Assert(_) => None,
            Statement::Set { .. } => None,
            Statement::WalTrace { .. } => None,
        };
        self.stmts.push(stmt);
        if let Some(name) = name {
            self.name_map
                .insert_secondary(&name, source.into(), description.to_string())
        }
    }

    pub fn append_secondary(
        &mut self,
        other: Vec<Statement>,
        source: impl Into<NameSource> + Clone,
        description: &str,
    ) {
        for statement in other {
            self.push_secondary(statement, source.clone(), description)
        }
    }

    pub fn append(&mut self, mut other: StatementList) {
        self.stmts.append(&mut other.stmts);
        self.name_map.merge(other.name_map)
    }

    pub fn to_vec(self, name_map: &mut NameSourceMap) -> Vec<Statement> {
        name_map.merge(self.name_map);
        self.stmts
    }
    pub fn to_vec_no_source_map(self) -> Vec<Statement> {
        self.stmts
    }
}

impl std::fmt::Display for StatementList {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "\n{}\n",
            self.stmts.iter().map(|s| s.to_string()).join("\n")
        )
    }
}
