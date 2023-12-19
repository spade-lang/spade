use spade_common::{
    location_info::{Loc, WithLocation},
    name::{Identifier, Path},
};
use spade_hir::{
    symbol_table::{GenericArg, SymbolTable, TypeDeclKind, TypeSymbol},
    TypeDeclaration,
};
use spade_hir::{ItemList, TypeParam};
use spade_types::PrimitiveType;

/// Add built in symbols like types to the symtab. The symbols are added with very high NameIDs to
/// not interfere with tests with hardcoded NameIDs
pub fn populate_symtab(symtab: &mut SymbolTable, item_list: &mut ItemList) {
    // Add primitive data types
    let mut id = std::u64::MAX;

    let mut add_type =
        |path: &[&str], args: Vec<Loc<GenericArg>>, primitive: PrimitiveType, is_port: bool| {
            let name = symtab
                .add_type_with_id(
                    id,
                    Path::from_strs(path),
                    TypeSymbol::Declared(args.clone(), TypeDeclKind::Primitive { is_port })
                        .nowhere(),
                )
                .nowhere();
            id -= 1;

            symtab.new_scope();
            let args = args
                .iter()
                .map(|arg| {
                    let result = match &arg.inner {
                        GenericArg::TypeName { name: a, traits: t } => {
                            assert!(
                                t.is_empty(),
                                "Constrained generics are not supported on primitives"
                            );
                            let id = symtab.add_type_with_id(
                                id,
                                Path(vec![a.clone().nowhere()]),
                                TypeSymbol::GenericArg { traits: vec![] }.nowhere(),
                            );
                            TypeParam::TypeName(a.clone(), id)
                        }
                        GenericArg::Number(a) => {
                            let id = symtab.add_type_with_id(
                                id,
                                Path(vec![a.clone().nowhere()]),
                                TypeSymbol::GenericInt.nowhere(),
                            );
                            TypeParam::Integer(a.clone(), id)
                        }
                    }
                    .nowhere();
                    id -= 1;
                    result
                })
                .collect();
            symtab.close_scope();

            item_list.types.insert(
                name.inner.clone(),
                TypeDeclaration {
                    name,
                    kind: spade_hir::TypeDeclKind::Primitive(primitive),
                    generic_args: args,
                }
                .nowhere(),
            );
        };
    add_type(
        &["uint"],
        vec![GenericArg::Number(Identifier("size".into())).nowhere()],
        PrimitiveType::Uint,
        false,
    );
    add_type(
        &["int"],
        vec![GenericArg::Number(Identifier("size".into())).nowhere()],
        PrimitiveType::Int,
        false,
    );
    add_type(
        &["Memory"],
        vec![
            GenericArg::TypeName {
                name: Identifier("D".into()),
                traits: vec![],
            }
            .nowhere(),
            GenericArg::Number(Identifier("AddrWidth".into())).nowhere(),
        ],
        PrimitiveType::Memory,
        true,
    );
    add_type(&["clock"], vec![], PrimitiveType::Clock, true);
    add_type(&["bool"], vec![], PrimitiveType::Bool, false);
    add_type(&["void"], vec![], PrimitiveType::Void, false);
    add_type(&["bit"], vec![], PrimitiveType::Bool, false);
}
