use rustc_hash::FxHashMap as HashMap;
use serde::{Deserialize, Serialize};
use spade_common::{id_tracker::ExprID, location_info::Loc, name::NameID};
use spade_hir::{Expression, Pattern};
use spade_mir::ValueName;

#[derive(Clone, Serialize, Deserialize)]
pub enum NameSource {
    Name(Loc<NameID>),
    Expr(Loc<ExprID>),
}

impl std::fmt::Display for NameSource {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            NameSource::Name(n) => write!(f, "{n}"),
            NameSource::Expr(id) => write!(f, "e{}", id.0),
        }
    }
}

impl From<&Loc<NameID>> for NameSource {
    fn from(n: &Loc<NameID>) -> Self {
        NameSource::Name(n.clone())
    }
}

impl From<&Loc<ExprID>> for NameSource {
    fn from(e: &Loc<ExprID>) -> Self {
        NameSource::Expr(*e)
    }
}

impl From<&Loc<Expression>> for NameSource {
    fn from(e: &Loc<Expression>) -> Self {
        Self::from(&e.map_ref(|e| e.id))
    }
}

impl From<&Loc<Pattern>> for NameSource {
    fn from(e: &Loc<Pattern>) -> Self {
        Self::from(&e.map_ref(|e| e.id))
    }
}

#[derive(Clone, Serialize, Deserialize)]
pub enum NamedValue {
    /// This name corresponds to the primary expression of the specified name. I.e. the location
    /// where the value is actually stored
    Primary(NameSource),
    /// This value is a secondary expression used in the calculation of the primary name. For
    /// example, a boolean value or a pipelined version of a value. The associated string
    /// is a description of the use
    Secondary(NameSource, String),
}

impl std::fmt::Display for NamedValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            NamedValue::Primary(n) => write!(f, "{n}"),
            NamedValue::Secondary(n, descr) => write!(f, "{n}({descr})"),
        }
    }
}

#[derive(Serialize, Deserialize, Clone)]
pub struct NameSourceMap {
    pub inner: HashMap<ValueName, NamedValue>,
}

impl Default for NameSourceMap {
    fn default() -> Self {
        Self::new()
    }
}

impl NameSourceMap {
    pub fn new() -> Self {
        Self {
            inner: HashMap::default(),
        }
    }

    pub fn insert_primary(&mut self, name: &ValueName, unmangled: NameSource) {
        self.inner
            .insert(name.clone(), NamedValue::Primary(unmangled));
    }
    pub fn insert_secondary(
        &mut self,
        name: &ValueName,
        unmangled: NameSource,
        description: String,
    ) {
        self.inner
            .insert(name.clone(), NamedValue::Secondary(unmangled, description));
    }

    pub fn merge(&mut self, other: NameSourceMap) {
        for (k, v) in other.inner {
            // NOTE: we previously had a check here for duplication, but that failed
            // when monomorphising generic functions as we then had multiple
            // copies of the same name in the output verilog.
            //
            // For the purpose of name mapping however, it does not matter what
            // types were selected for the monomorphised item, so we can safely
            // ignore duplicates.
            self.inner.insert(k.clone(), v);
        }
    }
}
