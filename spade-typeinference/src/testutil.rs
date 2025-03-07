use spade_common::location_info::WithLocation;
use spade_common::num_ext::InfallibleToBigInt;
use spade_hir::symbol_table::SymbolTable;
use spade_types::KnownType;

use crate::fixed_types::t_int;
use crate::TypeVar as TVar;

#[cfg(test)]
use crate::traits::TraitList;
use crate::TypeState;
#[cfg(test)]
use spade_types::meta_types::MetaType;

pub fn sized_int(size: u128, symtab: &SymbolTable, type_state: &mut TypeState) -> TVar {
    TVar::Known(
        ().nowhere(),
        t_int(symtab),
        vec![
            TVar::Known(().nowhere(), KnownType::Integer(size.to_bigint()), vec![])
                .insert(type_state),
        ],
    )
}

#[cfg(test)]
pub fn unsized_int(id: u64, symtab: &SymbolTable, type_state: &mut TypeState) -> TVar {
    TVar::Known(
        ().nowhere(),
        t_int(symtab),
        vec![
            TVar::Unknown(().nowhere(), id, TraitList::empty(), MetaType::Uint).insert(type_state),
        ],
    )
}

#[macro_export]
macro_rules! get_type {
    ($state:ident, $e:expr) => {
        if let Ok(t) = $state.type_of($e) {
            t
        } else {
            println!("{}", format_trace_stack(&$state));
            panic!("Failed to get type of {:?}", $e)
        }
    };
}

#[macro_export]
macro_rules! ensure_same_type {
    ($state:ident, $t1:expr, $t2:expr) => {
        // These let bindings are required for the values returned by
        // get_type to live long enough
        let t1 = $t1;
        let t2 = $t2;
        let _t1 = t1.get_type(&$state);
        let _t2 = t2.get_type(&$state);
        if _t1 != _t2 {
            println!("{}", format_trace_stack(&$state));
            $state.print_equations();

            if let (Ok(t1), Ok(t2)) = (&_t1, &_t2) {
                println!("Types were OK and have values {}, {}", t1, t2);
                println!("Raw: {:?}, {:?}", t1, t2);
            } else {
                println!("{:?}\n!=\n{:?}", _t1, _t2);
            }
            panic!("Types are not the same")
        }
    };
}

/// Shorthand macro for constructing TypeVar::Known
#[macro_export]
macro_rules! kvar {
    ($base:expr $(; ( $( $params:expr ),* ) )? ) => {
        TypeVar::Known(().nowhere(), $base, vec![ $( $($params),* )? ])
    }
}
