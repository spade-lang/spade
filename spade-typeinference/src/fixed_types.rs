use spade_common::{
    location_info::WithLocation,
    name::{Identifier, Path},
};
use spade_hir::symbol_table::SymbolTable;
use spade_types::KnownType;

fn lookup(symtab: &SymbolTable, name: &[&str]) -> KnownType {
    let path = Path(
        name.iter()
            .map(|s| Identifier(s.to_string()).nowhere())
            .collect(),
    );
    KnownType::Named(
        symtab
            .lookup_type_symbol(&path.clone().nowhere())
            .unwrap_or_else(|_| {
                panic!(
                    "{} not found. Was the symtab not populated with builtins?",
                    path
                )
            })
            .0,
    )
}

pub fn t_int(symtab: &SymbolTable) -> KnownType {
    lookup(symtab, &["int"])
}
pub fn t_uint(symtab: &SymbolTable) -> KnownType {
    lookup(symtab, &["uint"])
}
pub fn t_bit(symtab: &SymbolTable) -> KnownType {
    lookup(symtab, &["bit"])
}
pub fn t_bool(symtab: &SymbolTable) -> KnownType {
    lookup(symtab, &["bool"])
}
pub fn t_clock(symtab: &SymbolTable) -> KnownType {
    lookup(symtab, &["clock"])
}
