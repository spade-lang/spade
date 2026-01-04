use std::collections::{BTreeMap, HashMap};

use derive_where::derive_where;
use itertools::Itertools;
use serde::{Deserialize, Serialize};
use spade_common::name::{NameID, Path};

/// Mapping between instances and the module it instantiates
/// Example:
/// ```rust
/// entity y() {} // NameID: y_n0
/// entity x() {inst y()} // NameID: x_n1
/// entity main() { // NameID: main_n2
///     inst y();
///     inst x()
/// }
/// ```
///
/// Results in the following pseudo verilog:
/// ```
/// module main();
///     x x_0();
///     y y_0();
/// endmodule
///
/// module x();
///     y y_0();
/// endmodule
/// module y();
/// endmodule
/// ```
///
/// Which would have the following name map
///
/// (y has no modules, so no mapping)
/// (x_n1, "x_0") -> y_n0
/// (main_n2, "x_0") -> x_n1
/// (main_n2, "y_0") -> y_n0
#[derive(Serialize, Deserialize, Debug)]
pub struct InstanceMap {
    pub inner: HashMap<NameID, BTreeMap<String, NameID>>,
}

impl InstanceMap {
    pub fn extend(&mut self, other: Self) {
        self.inner.extend(other.inner);
    }
}

impl Default for InstanceMap {
    fn default() -> Self {
        Self::new()
    }
}

impl InstanceMap {
    pub fn new() -> Self {
        Self {
            inner: HashMap::new(),
        }
    }
}

pub struct InstanceNameTracker {
    previous_names: HashMap<String, usize>,
}

impl Default for InstanceNameTracker {
    fn default() -> Self {
        Self::new()
    }
}

impl InstanceNameTracker {
    pub fn new() -> Self {
        Self {
            previous_names: HashMap::new(),
        }
    }

    pub fn use_name(
        &mut self,
        // The nameID of the monomorphized unit to be instantiated
        unit_name: NameID,
        // The requested human readable instance name, will be modified to
        // make unique in this module
        instance_name: &str,
        // The unit in which this instantiation takes place
        in_unit: NameID,
        map: &mut InstanceMap,
    ) -> String {
        let e = self
            .previous_names
            .entry(instance_name.to_string())
            .or_default();
        let result = format!("{instance_name}_{e}");
        *e += 1;

        map.inner
            .entry(in_unit)
            .or_default()
            .insert(result.clone(), unit_name);

        result
    }
}

#[derive(Clone, Debug, PartialEq, PartialOrd, Ord, Eq, Hash)]
/// The name of a verilog module
pub enum UnitNameKind {
    /// A string that will be directly emitted in verilog. Must be a valid verilog
    /// identifier that does not clash with any keywords.
    /// The path is the underlying path which results in this entity. This is used when generating
    /// instance names to only emit the unit name and not the fully qualified path
    Unescaped(String),
    /// Any ASCII characters. Will be prepended with `\` and have ` ` appended at the
    /// end to give a valid verilog identifier
    Escaped { name: String, path: Vec<String> },
}

#[derive_where(PartialOrd, Ord, PartialEq, Eq, Hash)]
#[derive(Clone, Debug)]
pub struct UnitName {
    pub kind: UnitNameKind,
    #[derive_where(skip)]
    pub source: NameID,
}

impl UnitName {
    /// Creates a UnitName::Escaped from a list of strings making up a path.
    /// Does not set `source` to a valid NameID
    pub fn _test_from_strs(strs: &[&str]) -> Self {
        UnitName {
            source: NameID(0, Path::from_strs(strs)),
            kind: UnitNameKind::Escaped {
                name: strs.iter().join("::"),
                path: strs.iter().map(|s| s.to_string()).collect(),
            },
        }
    }
    pub fn as_verilog(&self) -> String {
        match &self.kind {
            UnitNameKind::Unescaped(name) => name.clone(),
            UnitNameKind::Escaped { name, path: _ } => format!("\\{name} "),
        }
    }

    pub fn instance_name(
        &self,
        inside: NameID,
        instance_map: &mut InstanceMap,
        names: &mut InstanceNameTracker,
    ) -> String {
        let name = match &self.kind {
            UnitNameKind::Escaped { name, path } => path.last().unwrap_or(name),
            UnitNameKind::Unescaped(name) => name,
        };
        names.use_name(self.source.clone(), name, inside, instance_map)
    }

    /// The \ and ' ' are not part of the actual identifier when escaping. So when we check
    /// for the top module, we don't want to include them
    pub fn without_escapes(&self) -> &str {
        match &self.kind {
            UnitNameKind::Escaped { name, path: _ } => name,
            UnitNameKind::Unescaped(s) => s,
        }
    }
}

impl std::fmt::Display for UnitName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_verilog())
    }
}

pub trait IntoUnitName {
    fn _test_into_unit_name(&self) -> UnitName;
}

impl<'a, T> IntoUnitName for T
where
    T: AsRef<[&'a str]>,
{
    fn _test_into_unit_name(&self) -> UnitName {
        UnitName {
            kind: UnitNameKind::Escaped {
                name: self.as_ref().iter().join("::"),
                path: self.as_ref().iter().map(|s| s.to_string()).collect(),
            },
            source: NameID(0, Path::from_strs(self.as_ref())),
        }
    }
}

impl IntoUnitName for str {
    fn _test_into_unit_name(&self) -> UnitName {
        UnitName {
            kind: UnitNameKind::Unescaped(self.to_string()),
            source: NameID(0, Path::from_strs(&[self])),
        }
    }
}

impl IntoUnitName for UnitName {
    fn _test_into_unit_name(&self) -> UnitName {
        self.clone()
    }
}
