use spade_hir::symbol_table::SymbolTable;
use spade_types::KnownType;

use crate::fixed_types::t_int;
use crate::TypeVar as TVar;

pub fn sized_int(size: u128, symtab: &SymbolTable) -> TVar {
    TVar::Known(
        t_int(symtab),
        vec![TVar::Known(KnownType::Integer(size), vec![], None)],
        None,
    )
}

pub fn unsized_int(id: u64, symtab: &SymbolTable) -> TVar {
    TVar::Known(t_int(symtab), vec![TVar::Unknown(id)], None)
}

#[macro_export]
macro_rules! get_type {
    ($state:ident, $e:expr) => {
        if let Ok(t) = $state.type_of($e) {
            t
        } else {
            println!("{}", format_trace_stack(&$state.trace_stack));
            panic!("Failed to get type of {:?}", $e)
        }
    };
}

#[macro_export]
macro_rules! ensure_same_type {
    ($state:ident, $t1:expr, $t2:expr) => {
        let _t1 = $t1.get_type(&$state);
        let _t2 = $t2.get_type(&$state);
        if _t1 != _t2 {
            println!("{}", format_trace_stack(&$state.trace_stack));
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
        TypeVar::Known($base, vec![ $( $($params),* )? ], None)
    }
}