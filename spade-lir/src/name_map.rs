use std::collections::HashMap;

use serde::{Deserialize, Serialize};

use crate::ValueName;

/// Mapping from verilog name back to the corresponding NameID
#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct VerilogNameMap {
    inner: HashMap<String, ValueName>,
}

impl Default for VerilogNameMap {
    fn default() -> Self {
        Self::new()
    }
}

impl VerilogNameMap {
    pub fn new() -> Self {
        Self {
            inner: HashMap::default(),
        }
    }

    /// Insert the specified string into the name map. If the string contains
    /// verilog escape characters (\\<name> ), those are removed
    pub fn insert(&mut self, from: &str, to: ValueName) {
        self.inner.insert(
            from.trim_start_matches('\\')
                .trim_end_matches(' ')
                .to_string(),
            to,
        );
    }

    pub fn lookup_name(&self, name: &str) -> Option<&ValueName> {
        self.inner.get(name)
    }
}

