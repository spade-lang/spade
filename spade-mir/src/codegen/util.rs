use num::BigUint;

use crate::ValueName;

impl ValueName {
    pub fn var_name(&self) -> String {
        match self {
            ValueName::Named(_, _) => format!("{self}"),
            ValueName::Expr(id) => {
                format!("_e_{}", id)
            }
        }
    }

    pub fn backward_var_name(&self) -> String {
        match self {
            ValueName::Named(id, name) => {
                if *id == 0 {
                    format!("\\{}_mut ", name)
                } else {
                    format!("{}_n{}_mut", name, id)
                }
            }
            ValueName::Expr(id) => {
                format!("_e_{}_mut", id)
            }
        }
    }
}

pub fn escape_path(path: &str) -> String {
    path.replace("::", "_")
}

pub fn mangle_entity(module: &str) -> String {
    if module.starts_with('\\') {
        module.to_string()
    } else {
        format!("e_{}", escape_path(module))
    }
}

pub fn mangle_input(input: &str) -> String {
    format!("{}_i", input)
}

pub fn mangle_output(input: &str) -> String {
    format!("{}_o", input)
}

pub enum TupleIndex {
    /// The indexee is a 1 bit scalar, so no indexing should be performed.
    /// Codegens as empty string
    None,
    /// The index is a single bit, i.e. codegens as [val]
    Single(BigUint),
    /// The index is a range of bits, codegens as [left:right]
    Range { left: BigUint, right: BigUint },
}

impl TupleIndex {
    pub fn verilog_code(&self) -> String {
        match self {
            TupleIndex::None => String::new(),
            TupleIndex::Single(i) => format!("[{i}]"),
            TupleIndex::Range { left, right } => format!("[{left}:{right}]"),
        }
    }
}
