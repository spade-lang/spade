use spade_common::{
    location_info::{Loc, WithLocation},
    name::{Identifier, Visibility},
};
use spade_hir::{
    symbol_table::{GenericArg, SymbolTable, TypeDeclKind, TypeSymbol},
    Generic, TypeDeclaration,
};
use spade_hir::{ItemList, TypeParam};
use spade_types::{meta_types::MetaType, PrimitiveType};

/// Add built in symbols like types to the symtab. The symbols are added with very high NameIDs to
/// not interfere with tests with hardcoded NameIDs
pub fn populate_symtab(symtab: &mut SymbolTable, item_list: &mut ItemList) {
    // Add primitive data types
    let mut id = std::u64::MAX;

    let mut add_type = |name: &str,
                        args: Vec<Loc<GenericArg>>,
                        primitive: PrimitiveType,
                        is_port: bool,
                        is_inout: bool| {
        let name = symtab
            .add_type_with_id(
                id,
                Identifier::intern(name).nowhere(),
                TypeSymbol::Declared(args.clone(), TypeDeclKind::Primitive { is_port, is_inout })
                    .nowhere(),
                Visibility::Public.nowhere(),
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
                            a.clone().nowhere(),
                            TypeSymbol::GenericArg { traits: vec![] }.nowhere(),
                            Visibility::Implicit.nowhere(),
                        );
                        TypeParam {
                            name: Generic::Named(id.nowhere()),
                            trait_bounds: vec![],
                            meta: MetaType::Type,
                        }
                    }
                    GenericArg::TypeWithMeta { name, meta } => {
                        let id = symtab.add_type_with_id(
                            id,
                            name.clone().nowhere(),
                            TypeSymbol::GenericMeta(meta.clone()).nowhere(),
                            Visibility::Implicit.nowhere(),
                        );
                        TypeParam {
                            name: Generic::Named(id.nowhere()),
                            trait_bounds: vec![],
                            meta: meta.clone(),
                        }
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
        "uint",
        vec![GenericArg::uint(Identifier::intern("size")).nowhere()],
        PrimitiveType::Uint,
        false,
        false,
    );
    add_type(
        "int",
        vec![GenericArg::uint(Identifier::intern("size")).nowhere()],
        PrimitiveType::Int,
        false,
        false,
    );
    add_type(
        "Memory",
        vec![
            GenericArg::TypeName {
                name: Identifier::intern("D"),
                traits: vec![],
            }
            .nowhere(),
            GenericArg::uint(Identifier::intern("AddrWidth")).nowhere(),
        ],
        PrimitiveType::Memory,
        true,
        false,
    );
    add_type("clock", vec![], PrimitiveType::Clock, true, false);
    add_type("bool", vec![], PrimitiveType::Bool, false, false);
    add_type("tri", vec![], PrimitiveType::Bool, false, false);
    add_type(
        "inout",
        vec![GenericArg::uint(Identifier::intern("T")).nowhere()],
        PrimitiveType::InOut,
        false,
        true,
    );
}
