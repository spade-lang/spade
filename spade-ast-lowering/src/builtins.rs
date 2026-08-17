use spade_common::{
    location_info::{Loc, WithLocation},
    name::{Identifier, Path},
};
use spade_hir::{
    Generic, TypeDeclaration,
    symbol_table::{GenericArg, SymbolTable, TypeDeclKind, TypeSymbol},
};
use spade_hir::{ItemList, TypeParam};
use spade_types::{PrimitiveType, meta_types::MetaType};

/// Add built in symbols like types to the symtab. The symbols are added with very high NameIDs to
/// not interfere with tests with hardcoded NameIDs
pub fn populate_symtab(symtab: &mut SymbolTable, item_list: &mut ItemList) {
    // Add primitive data types
    let mut id = std::u64::MAX;

    let mut add_type =
        |name_str: &str, args: Vec<Loc<GenericArg>>, primitive: PrimitiveType, is_inout: bool| {
            let path = Path::from_strs(&[name_str]).nowhere();
            let name = symtab
                .add_type_with_id(
                    id,
                    path,
                    TypeSymbol::Declared(args.clone(), 0, TypeDeclKind::Primitive { is_inout })
                        .nowhere(),
                    None,
                    None,
                )
                .nowhere();
            id -= 1;

            symtab.new_scope();
            // Create a dummy namespace to put the parameters in to aid completion. Slight hack :)
            symtab.push_namespace(spade_common::name::PathSegment::Named(
                Identifier::intern(name_str).nowhere(),
            ));
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
                                Path::ident_with_loc(a.clone().nowhere()),
                                TypeSymbol::GenericArg { traits: vec![] }.nowhere(),
                                None,
                                None,
                            );
                            TypeParam {
                                name: Generic::Named(id.nowhere()),
                                trait_bounds: vec![],
                                meta: MetaType::Type,
                                default: None,
                            }
                        }
                        GenericArg::TypeWithMeta { name, meta } => {
                            let id = symtab.add_type_with_id(
                                id,
                                Path::ident_with_loc(name.clone().nowhere()),
                                TypeSymbol::GenericMeta(meta.clone()).nowhere(),
                                None,
                                None,
                            );
                            TypeParam {
                                name: Generic::Named(id.nowhere()),
                                trait_bounds: vec![],
                                meta: meta.clone(),
                                default: None,
                            }
                        }
                    }
                    .nowhere();
                    id -= 1;
                    result
                })
                .collect();
            symtab.pop_namespace();
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
    );
    add_type(
        "int",
        vec![GenericArg::uint(Identifier::intern("size")).nowhere()],
        PrimitiveType::Int,
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
        false,
    );
    add_type("clock", vec![], PrimitiveType::Clock, false);
    add_type("bool", vec![], PrimitiveType::Bool, false);
    add_type("tri", vec![], PrimitiveType::Bool, false);
    add_type(
        "inout",
        vec![GenericArg::uint(Identifier::intern("T")).nowhere()],
        PrimitiveType::InOut,
        true,
    );
}
