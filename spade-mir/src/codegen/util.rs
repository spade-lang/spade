use num::BigUint;
use spade_common::location_info::Loc;

use crate::ValueName;

impl ValueName {
    pub fn unescaped_var_name(&self) -> String {
        match self {
            ValueName::Named(_, _, _) => {
                format!("{self}")
            }
            ValueName::Expr(id) => format!("_e_{}", id.0),
        }
    }

    // Returns true if this name needs to be escaped using `\ `
    pub fn needs_escaping(&self) -> bool {
        match self {
            ValueName::Named(id, _, _) => *id == 0,
            ValueName::Expr(_) => false,
        }
    }

    pub fn var_name(&self) -> String {
        if self.needs_escaping() {
            format!("\\{} ", self.unescaped_var_name())
        } else {
            self.unescaped_var_name()
        }
    }

    pub fn backward_var_name(&self) -> String {
        match self {
            ValueName::Named(id, name, _) => {
                if *id == 0 {
                    format!("\\{}_mut ", name)
                } else {
                    format!("{}_n{}_mut", name, id)
                }
            }
            ValueName::Expr(id) => {
                format!("_e_{}_mut", id.0)
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

pub fn mangle_input(no_mangle: &Option<Loc<()>>, input: &str) -> String {
    if no_mangle.is_some() {
        input.to_string()
    } else {
        format!("{}_i", input)
    }
}

pub fn mangle_output(no_mangle: &Option<Loc<()>>, input: &str) -> String {
    if no_mangle.is_some() {
        input.to_string()
    } else {
        format!("{}_o", input)
    }
}

#[derive(PartialEq, Debug)]
pub enum TupleIndex {
    /// The indexee is a 1 bit scalar, so no indexing should be performed.
    /// Codegens as empty string
    None,
    /// The indexee is zero width, this is most likely caused by a a mir lowering bug
    /// where a 0 sized type is indexed
    ZeroWidth,
    /// The index is a single bit, i.e. codegens as [val]
    Single(BigUint),
    /// The index is a range of bits, codegens as [left:right]
    Range { left: BigUint, right: BigUint },
}

impl TupleIndex {
    pub fn verilog_code(&self) -> String {
        match self {
            TupleIndex::None => String::new(),
            TupleIndex::ZeroWidth => panic!("Computed a 0 width tuple index"),
            TupleIndex::Single(i) => format!("[{i}]"),
            TupleIndex::Range { left, right } => format!("[{left}:{right}]"),
        }
    }
}
