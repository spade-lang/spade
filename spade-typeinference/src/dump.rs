use std::collections::HashMap;

use spade_hir::{symbol_table::SymbolTable, TypeList};
use spade_types::ConcreteType;

use crate::{equation::TypedExpression, TypeState};

// lifeguard spade#254
// FIXME: Remove this since we dump the whole type statem
pub fn dump_types(
    type_state: &TypeState,
    type_list: &TypeList,
    symtab: &SymbolTable,
) -> HashMap<TypedExpression, Option<ConcreteType>> {
    type_state
        .get_equations()
        .iter()
        .map(|(expr, t)| {
            (
                expr.clone(),
                type_state.ungenerify_type(t, symtab, type_list),
            )
        })
        .collect()
}
