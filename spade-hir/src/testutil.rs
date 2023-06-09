use spade_common::{
    location_info::{Loc, WithLocation},
    num_ext::InfallibleToBigInt,
};

/// A declared type.
/// The type name is the name as declared in the symtab which must be in scope with
/// the name `symtab`
#[macro_export]
macro_rules! dtype {
    ($symtab:expr => $base:expr$(; ($($arg:expr),*) )?) => {
        hir::TypeSpec::Declared(
            $symtab.lookup_id(&ast_path($base)).unwrap().nowhere(),
            vec![ $( $( $arg ),* )? ]
        ).nowhere()
    }
}

/// A type level integer
pub fn t_num(size: u128) -> Loc<crate::TypeExpression> {
    crate::TypeExpression::Integer(size.to_bigint()).nowhere()
}

#[macro_export]
macro_rules! hparams {
    ($(($name:expr, $type:expr)),*$(,)?) => {
        hir::ParameterList(vec![$(hir::Parameter{name: ast_ident($name), ty: $type, no_mangle: None}),*])
    }
}
