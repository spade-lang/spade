use std::collections::HashMap;

use itertools::Itertools;

pub struct InstanceNameTracker {
    previous_names: HashMap<String, usize>,
}

impl InstanceNameTracker {
    pub fn new() -> Self {
        Self {
            previous_names: HashMap::new(),
        }
    }

    pub fn use_name(&mut self, name: &str) -> String {
        let e = self.previous_names.entry(name.to_string()).or_default();
        let result = format!("{name}_{e}");
        *e += 1;
        result
    }
}

#[derive(Clone, Debug, PartialEq, PartialOrd, Ord, Eq)]
/// The name of a verilog module
pub enum UnitName {
    /// A string that will be directly emitted in verilog. Must be a valid verilog
    /// identifier that does not clash with any keywords.
    /// The path is the underlying path which results in this entity. This is used when generating
    /// instance names to only emit the unit name and not the fully qualified path
    Unescaped(String),
    /// Any ASCII characters. Will be prepended with `\` and have ` ` appended at the
    /// end to give a valid verilog identifier
    Escaped { name: String, path: Vec<String> },
}

impl UnitName {
    /// Creates a UnitName::Escaped from a list of strings making up a path. Primarily
    /// to be used by tests
    pub fn from_strs(strs: &[&str]) -> Self {
        UnitName::Escaped {
            name: strs.iter().join("::"),
            path: strs.iter().map(|s| s.to_string()).collect(),
        }
    }
    pub fn as_verilog(&self) -> String {
        match self {
            UnitName::Unescaped(name) => name.clone(),
            UnitName::Escaped { name, path: _ } => format!("\\{name} "),
        }
    }

    pub fn instance_name(&self, names: &mut InstanceNameTracker) -> String {
        let name = match self {
            UnitName::Escaped { name, path } => path.last().unwrap_or(name),
            UnitName::Unescaped(name) => name,
        };
        names.use_name(name)
    }

    /// The \ and ' ' are not part of the actual identifier when escaping. So when we check
    /// for the top module, we don't want to include them
    pub fn without_escapes(&self) -> &str {
        match self {
            UnitName::Escaped { name, path: _ } => name,
            UnitName::Unescaped(s) => s,
        }
    }
}

impl std::fmt::Display for UnitName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_verilog())
    }
}

pub trait IntoUnitName {
    fn into_unit_name(&self) -> UnitName;
}

impl<'a, T> IntoUnitName for T
where
    T: AsRef<[&'a str]>,
{
    fn into_unit_name(&self) -> UnitName {
        UnitName::Escaped {
            name: self.as_ref().iter().join("::"),
            path: self.as_ref().iter().map(|s| s.to_string()).collect(),
        }
    }
}

impl IntoUnitName for str {
    fn into_unit_name(&self) -> UnitName {
        UnitName::Unescaped(self.to_string())
    }
}

impl IntoUnitName for UnitName {
    fn into_unit_name(&self) -> UnitName {
        self.clone()
    }
}
