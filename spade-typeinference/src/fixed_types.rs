use spade_common::{
    location_info::{Loc, WithLocation},
    name::{Identifier, Path},
};
use spade_hir::symbol_table::SymbolTable;
use spade_types::KnownType;

use crate::{
    equation::{TypeVar, TypeVarID},
    TypeState,
};

fn lookup(symtab: &SymbolTable, name: &[&str]) -> KnownType {
    let path = Path(
        name.iter()
            .map(|s| Identifier::intern(s).nowhere())
            .collect(),
    );
    KnownType::Named(
        symtab
            .lookup_type_symbol(&path.clone().nowhere())
            .unwrap_or_else(|_| {
                panic!(
                    "{} not found. Was the symtab not populated with externs?",
                    path
                )
            })
            .0,
    )
}

impl TypeState {
    pub fn t_int(&mut self, loc: Loc<()>, symtab: &SymbolTable) -> TypeVarID {
        self.add_type_var(TypeVar::Known(loc, t_int(symtab), vec![]))
    }
    pub fn t_uint(&mut self, loc: Loc<()>, symtab: &SymbolTable) -> TypeVarID {
        self.add_type_var(TypeVar::Known(loc, t_uint(symtab), vec![]))
    }
    pub fn t_tri(&mut self, loc: Loc<()>, symtab: &SymbolTable) -> TypeVarID {
        self.add_type_var(TypeVar::Known(loc, t_tri(symtab), vec![]))
    }
    pub fn t_bool(&mut self, loc: Loc<()>, symtab: &SymbolTable) -> TypeVarID {
        self.add_type_var(TypeVar::Known(loc, t_bool(symtab), vec![]))
    }
    pub fn t_clock(&mut self, loc: Loc<()>, symtab: &SymbolTable) -> TypeVarID {
        self.add_type_var(TypeVar::Known(loc, t_clock(symtab), vec![]))
    }

    pub fn t_err(&mut self, loc: Loc<()>) -> TypeVarID {
        self.add_type_var(TypeVar::Known(loc, KnownType::Error, vec![]))
    }
}

pub fn t_int(symtab: &SymbolTable) -> KnownType {
    lookup(symtab, &["int"])
}
pub fn t_uint(symtab: &SymbolTable) -> KnownType {
    lookup(symtab, &["uint"])
}
pub fn t_tri(symtab: &SymbolTable) -> KnownType {
    lookup(symtab, &["tri"])
}
pub fn t_bool(symtab: &SymbolTable) -> KnownType {
    lookup(symtab, &["bool"])
}
pub fn t_clock(symtab: &SymbolTable) -> KnownType {
    lookup(symtab, &["clock"])
}
