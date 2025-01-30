use crate::code_compiles;
use crate::build_items;


code_compiles! {
    cache_cells_reproducer,
    "entity cache_cells() {
        let self_has_value = match 0 {
            addr => addr == 0u8,
        };
        gen if 0 != 0 {
        } else {
        }
    }
    "
}
