use crate::Result;
use spade_ast::{
    AttributeList, Item, Module, ModuleBody, ParameterList, Struct, TypeDeclKind, TypeDeclaration,
    TypeParam, TypeSpec, Unit,
};
use spade_common::{
    location_info::{Loc, WithLocation},
    name::Identifier,
    namespace::ModuleNamespace,
};
use spade_diagnostics::{diag_bail, Diagnostic};

/// Applies macros to the specified unit, returning any new items generated.
fn apply_unit_macros(_unit: &Loc<Unit>) -> Vec<Item> {
    todo!()
}

/// Applies macros to the specified type definition, returning any new items generated.
fn apply_type_decl_macros(decl: &Loc<TypeDeclaration>) -> Result<Vec<Item>> {
    match &decl.kind {
        // We support no macros on enums atm
        TypeDeclKind::Enum(_) => Ok(vec![]),
        TypeDeclKind::Struct(s) => {
            if s.is_port() {
                generate_aux_structs(s, &decl.generic_args)
            } else {
                // Non port structs have no macros
                Ok(vec![])
            }
        }
    }
}

/// Generates AST nodes for the auxillary structs for a struct port (`::Fwd`) and (`::Back`)
fn generate_aux_structs(
    t: &Loc<Struct>,
    generic_args: &Option<Loc<Vec<Loc<TypeParam>>>>,
) -> Result<Vec<Item>> {
    if !t.is_port() {
        diag_bail!(
            t,
            "The compiler called generate_aux_structs on a non-port struct"
        );
    }
    if let Some(self_) = t.members.self_ {
        diag_bail!(self_, "Found a self on a struct port");
    }
    let (fwd_members, back_members) = t
        .members
        .args
        .iter()
        .map(|(_attrs, name, ty)| {
            Ok((
                (AttributeList::empty(), name.clone(), forward_type(ty)),
                (AttributeList::empty(), name.clone(), backward_type(ty)),
            ))
        })
        .collect::<Result<Vec<_>>>()?
        .into_iter()
        .unzip();

    let fwd_members = ParameterList {
        self_: None,
        args: fwd_members,
    }
    .at_loc(&t.members);
    let back_members = ParameterList {
        self_: None,
        args: back_members,
    }
    .at_loc(&t.members);

    Ok(vec![Item::Module(
        Module {
            name: t.name.clone(),
            body: ModuleBody {
                members: vec![
                    Item::Type(
                        TypeDeclaration {
                            name: Identifier("Fwd".to_string()).at_loc(&t.name),
                            kind: TypeDeclKind::Struct(
                                Struct {
                                    attributes: AttributeList::empty(),
                                    name: Identifier("Fwd".to_string()).at_loc(&t.name),
                                    members: fwd_members,
                                    port_keyword: None,
                                }
                                .at_loc(t),
                            ),
                            generic_args: generic_args.clone(),
                        }
                        .at_loc(t),
                    ),
                    Item::Type(
                        TypeDeclaration {
                            name: Identifier("Back".to_string()).at_loc(&t.name),
                            kind: TypeDeclKind::Struct(
                                Struct {
                                    attributes: AttributeList::empty(),
                                    name: Identifier("Back".to_string()).at_loc(&t.name),
                                    members: back_members,
                                    port_keyword: None,
                                }
                                .at_loc(t),
                            ),
                            generic_args: generic_args.clone(),
                        }
                        .at_loc(t),
                    ),
                ],
            }
            .at_loc(t),
        }
        .at_loc(t),
    )])
}

/// Returns a new ast type with only the forward parts of the specified type. If there
/// are no forward parts, returns None.
/// Only valid for port types
fn forward_type(ty: &Loc<TypeSpec>) -> Option<Loc<TypeSpec>> {
    match &ty.inner {
        TypeSpec::Tuple(members) => {
            let members: Vec<Loc<TypeSpec>> = members.iter().filter_map(forward_type).collect();
            if members.is_empty() {
                None
            } else {
                Some(TypeSpec::Tuple(members).at_loc(&ty))
            }
        }
        TypeSpec::Array { inner, size } => {
            if let Some(inner) = forward_type(inner) {
                Some(
                    TypeSpec::Array {
                        inner: Box::new(inner),
                        size: size.clone(),
                    }
                    .at_loc(&ty),
                )
            } else {
                None
            }
        }
        // If we have a raw named type here, we know that it is a port type, so we will
        // have a ::Fwd available
        TypeSpec::Named(name, args) => {
            let new_name = name.push_ident(Identifier("Fwd".to_string()).at_loc(&name));

            Some(TypeSpec::Named(new_name.at_loc(name), args.clone()).at_loc(ty))
        }
        TypeSpec::Unit(_) => None,
        TypeSpec::Inverted(inner) => backward_type(inner),
        TypeSpec::Wire(w) => Some(TypeSpec::Wire(w.clone()).at_loc(&ty)),
        // NOTE: We're leaving this unhandled here. It is an error, but that error will
        // be reported later
        TypeSpec::Wildcard => None,
    }
}

/// Like forward_type, but backward
fn backward_type(ty: &Loc<TypeSpec>) -> Option<Loc<TypeSpec>> {
    match &ty.inner {
        TypeSpec::Tuple(members) => {
            let members: Vec<Loc<TypeSpec>> = members.iter().filter_map(backward_type).collect();
            if members.is_empty() {
                None
            } else {
                Some(TypeSpec::Tuple(members).at_loc(&ty))
            }
        }
        TypeSpec::Array { inner, size } => {
            if let Some(inner) = backward_type(inner) {
                Some(
                    TypeSpec::Array {
                        inner: Box::new(inner),
                        size: size.clone(),
                    }
                    .at_loc(&ty),
                )
            } else {
                None
            }
        }
        // If we have a raw named type here, we know that it is a port type, so we will
        // have a ::Fwd available
        TypeSpec::Named(name, args) => {
            let new_name = name.push_ident(Identifier("Back".to_string()).at_loc(&name));

            Some(TypeSpec::Named(new_name.at_loc(name), args.clone()).at_loc(ty))
        }
        TypeSpec::Unit(_) => None,
        TypeSpec::Inverted(inner) => forward_type(inner),
        TypeSpec::Wire(_) => None,
        // NOTE: We're leaving this unhandled here. It is an error, but that error will
        // be reported later
        TypeSpec::Wildcard => None,
    }
}

fn apply_macros(modules: &mut Vec<(ModuleNamespace, ModuleBody)>) -> Result<()> {
    for (_namespace, body) in modules {
        let mut new_items = body
            .members
            .iter()
            .map(|item| match item {
                Item::Unit(unit) => Ok(apply_unit_macros(&unit)),
                Item::TraitDef(_) => Ok(vec![]),
                Item::Type(type_decl) => apply_type_decl_macros(type_decl),
                Item::Module(_) => Ok(vec![]),
                Item::Use(_) => Ok(vec![]),
                Item::Config(_) => Ok(vec![]),
                Item::ImplBlock(_) => Ok(vec![]),
            })
            .collect::<Result<Vec<_>>>()?
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();

        body.members.append(&mut new_items)
    }

    Ok(())
}
