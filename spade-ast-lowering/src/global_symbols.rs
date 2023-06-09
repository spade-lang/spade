use std::collections::HashSet;

use hir::{
    symbol_table::{EnumVariant, StructCallable},
    ItemList, TypeExpression, WalSuffix,
};
use spade_ast as ast;
use spade_common::{
    location_info::{Loc, WithLocation},
    name::{Identifier, Path},
};
use spade_diagnostics::{diag_bail, Diagnostic};
use spade_hir as hir;

use crate::{
    attributes::{AttributeListExt, LocAttributeExt},
    types::IsPort,
    visit_parameter_list, Result, SelfContext,
};
use spade_hir::symbol_table::{GenericArg, SymbolTable, Thing, TypeSymbol};

#[tracing::instrument(skip_all)]
pub fn gather_types(module: &ast::ModuleBody, symtab: &mut SymbolTable) -> Result<()> {
    for item in &module.members {
        match item {
            ast::Item::Type(t) => {
                visit_type_declaration(t, symtab)?;
            }
            ast::Item::Module(m) => {
                symtab.push_namespace(m.name.clone());
                if let Err(e) = gather_types(&m.body, symtab) {
                    symtab.pop_namespace();
                    return Err(e);
                };
                symtab.pop_namespace();
            }
            ast::Item::ImplBlock(_) => {}
            ast::Item::Unit(_) => {}
            ast::Item::TraitDef(_) => {}
            ast::Item::Config(cfg) => {
                symtab.add_unique_thing(
                    Path::ident(cfg.name.clone()).at_loc(&cfg.name),
                    Thing::ComptimeConfig(cfg.val.clone()),
                )?;
            }
            ast::Item::Use(u) => {
                let new_name = match &u.alias {
                    Some(name) => name.clone(),
                    None => u.path.0.last().unwrap().clone(),
                };

                symtab.add_alias(
                    Path::ident(new_name.clone()).at_loc(&new_name.loc()),
                    u.path.clone(),
                )?;
            }
        }
    }
    Ok(())
}

/// Collect global symbols as a first pass before generating HIR
#[tracing::instrument(skip_all)]
pub fn gather_symbols(
    module: &ast::ModuleBody,
    symtab: &mut SymbolTable,
    item_list: &mut ItemList,
) -> Result<()> {
    for item in &module.members {
        visit_item(item, symtab, item_list)?;
    }

    Ok(())
}

#[tracing::instrument(skip_all)]
pub fn visit_item(
    item: &ast::Item,
    symtab: &mut SymbolTable,
    item_list: &mut ItemList,
) -> Result<()> {
    match item {
        ast::Item::Unit(e) => {
            visit_unit(&None, &e, symtab, &SelfContext::FreeStanding)?;
        }
        ast::Item::TraitDef(def) => {
            // FIXME
            diag_bail!(def, "Trait definition is currently unsupported");
        }
        ast::Item::ImplBlock(block) => {
            if let Some(r#trait) = &block.r#trait {
                // FIXME
                diag_bail!(r#trait, "Implementation of traits is currently unsupported");
            }
        }
        ast::Item::Type(t) => {
            re_visit_type_declaration(t, symtab, item_list)?;
        }
        ast::Item::Module(m) => {
            symtab.push_namespace(m.name.clone());
            if let Err(e) = gather_symbols(&m.body, symtab, item_list) {
                symtab.pop_namespace();
                return Err(e);
            }
            symtab.pop_namespace();
        }
        ast::Item::Use(_) => {}
        ast::Item::Config(_) => {}
    }
    Ok(())
}

#[tracing::instrument(skip_all)]
pub fn visit_unit(
    extra_path: &Option<Path>,
    e: &Loc<ast::Unit>,
    symtab: &mut SymbolTable,
    self_context: &SelfContext,
) -> Result<()> {
    let head = crate::entity_head(&e, symtab, self_context)?;

    let new_path = extra_path
        .as_ref()
        .unwrap_or(&Path(vec![]))
        .join(Path::ident(e.name.clone()))
        .at_loc(&e.name);

    symtab.add_unique_thing(new_path, Thing::Unit(head.at_loc(e)))?;

    Ok(())
}

pub fn visit_type_declaration(
    t: &Loc<ast::TypeDeclaration>,
    symtab: &mut SymbolTable,
) -> Result<()> {
    let args = t
        .generic_args
        .iter()
        .map(|arg| {
            match &arg.inner {
                ast::TypeParam::TypeName(n) => GenericArg::TypeName(n.inner.clone()),
                ast::TypeParam::Integer(n) => GenericArg::Number(n.inner.clone()),
            }
            .at_loc(&arg.loc())
        })
        .collect();

    let kind = match &t.kind {
        ast::TypeDeclKind::Enum(_) => hir::symbol_table::TypeDeclKind::Enum,
        ast::TypeDeclKind::Struct(s) => hir::symbol_table::TypeDeclKind::Struct {
            is_port: s.is_port(),
        },
    };

    let new_thing = Path::ident(t.name.clone()).at_loc(&t.name.loc());
    symtab.add_unique_type(new_thing, TypeSymbol::Declared(args, kind).at_loc(&t))?;

    Ok(())
}

/// Visit type declarations a second time, this time adding the type to the item list
/// as well as adding enum variants to the global scope.
/// This needs to happen as a separate pass since other types need to be in scope when
/// we check type declarations
pub fn re_visit_type_declaration(
    t: &Loc<ast::TypeDeclaration>,
    symtab: &mut SymbolTable,
    items: &mut ItemList,
) -> Result<()> {
    // Process right hand side of type declarations
    // The first visitor has already added the LHS to the symtab
    // Look up the ID
    let (declaration_id, _) = symtab
        .lookup_type_symbol(&Path(vec![t.name.clone()]).at_loc(&t.name))
        .expect("Expected type symbol to already be in symtab");
    let declaration_id = declaration_id.at_loc(&t.name);

    // Add the generic parameters to a new symtab scope
    symtab.new_scope();
    for param in &t.generic_args {
        let (name, symbol_type) = match &param.inner {
            ast::TypeParam::TypeName(n) => (n, TypeSymbol::GenericArg),
            ast::TypeParam::Integer(n) => (n, TypeSymbol::GenericInt),
        };
        symtab.add_type(Path::ident(name.clone()), symbol_type.at_loc(param));
    }

    // Generate TypeExprs and TypeParam vectors which are needed for building the
    // hir::TypeDeclaration and for enum constructors
    let mut output_type_exprs = vec![];
    let mut type_params = vec![];
    for arg in &t.generic_args {
        let (name_id, _) = symtab
            .lookup_type_symbol(&Path(vec![arg.name().clone()]).at_loc(arg))
            .expect("Expected generic param to be in symtab");
        let expr = TypeExpression::TypeSpec(hir::TypeSpec::Generic(name_id.clone().at_loc(arg)))
            .at_loc(arg);
        let param = match &arg.inner {
            ast::TypeParam::TypeName(n) => {
                hir::TypeParam::TypeName(n.inner.clone(), name_id.clone())
            }
            ast::TypeParam::Integer(n) => hir::TypeParam::Integer(n.inner.clone(), name_id.clone()),
        };
        output_type_exprs.push(expr);
        type_params.push(param.at_loc(arg))
    }

    let hir_kind = match &t.inner.kind {
        ast::TypeDeclKind::Enum(e) => {
            let mut member_names = HashSet::<Loc<Identifier>>::new();
            let mut hir_options = vec![];

            for (i, option) in e.options.iter().enumerate() {
                if let Some(prev) = member_names.get(&option.0) {
                    let new = &option.0;
                    return Err(
                        Diagnostic::error(new, format!("Multiple options called {}", new))
                            .primary_label(format!("{} occurs more than once", new))
                            .secondary_label(prev, "Previously occurred here")
                            .into(),
                    );
                }
                member_names.insert(option.0.clone());
                // Check the parameter list
                let parameter_list = option
                    .1
                    .clone()
                    .map(|l| visit_parameter_list(&l, symtab, &SelfContext::FreeStanding))
                    .unwrap_or_else(|| Ok(hir::ParameterList(vec![])))?;

                let args = option
                    .1
                    .clone()
                    .map(|l| {
                        if let Some(self_) = l.self_ {
                            Err(Diagnostic::bug(self_, "enum member contains self"))
                        } else {
                            Ok(l.args.clone())
                        }
                    })
                    .unwrap_or(Ok(vec![]))?;

                // Ensure that we don't have any port types in the enum variants
                for (_, _, ty) in args {
                    if ty.is_port(symtab)? {
                        return Err(Diagnostic::error(ty, "Port in enum")
                            .primary_label("This is a port")
                            .secondary_label(&e.name, "This is an enum")
                            .into());
                    }
                }

                let variant_thing = EnumVariant {
                    name: option.0.clone(),
                    output_type: hir::TypeSpec::Declared(
                        declaration_id.clone(),
                        output_type_exprs.clone(),
                    )
                    .at_loc(t),
                    type_params: type_params.clone(),
                    option: i,
                    params: parameter_list.clone(),
                };

                // Add option constructor to symtab at the outer scope
                let head_id = symtab.add_thing_at_offset(
                    1,
                    Path(vec![e.name.clone(), option.0.clone()]),
                    Thing::EnumVariant(variant_thing.at_loc(&option.0)),
                );
                // Add option constructor to item list
                items.executables.insert(
                    head_id.clone(),
                    hir::ExecutableItem::EnumInstance {
                        base_enum: declaration_id.inner.clone(),
                        variant: i,
                    },
                );

                // NOTE: it's kind of weird to push head_id here, since that's just
                // the constructor. In the future, if we move forward with enum members
                // being individual types, we should push that instead
                hir_options.push((head_id.clone().at_loc(&option.0), parameter_list))
            }

            hir::TypeDeclKind::Enum(
                hir::Enum {
                    options: hir_options,
                }
                .at_loc(e),
            )
        }
        ast::TypeDeclKind::Struct(s) => {
            if let Some(self_) = s.members.self_ {
                return Err(Diagnostic::bug(
                    self_,
                    "struct contains self member which was let through parser",
                )
                .into());
            }
            // Disallow normal arguments if the struct is a port, and port types
            // if it is not
            if s.is_port() {
                for (_, f, ty) in &s.members.args {
                    if !ty.is_port(symtab)? {
                        return Err(Diagnostic::error(ty, "Non-port in port struct")
                            .primary_label("This is not a port type")
                            .secondary_label(
                                s.port_keyword.unwrap(),
                                format!("{} is a port struct", s.name),
                            )
                            .note("All members of a port struct must be ports")
                            .span_suggest_insert_before(
                                format!("Consider making {f} a wire"),
                                ty,
                                "&",
                            )
                            .into());
                    }
                }
            } else {
                for (_, _, ty) in &s.members.args {
                    if ty.is_port(symtab)? {
                        return Err(Diagnostic::error(ty, "Port in non-port struct")
                            .primary_label("This is a port")
                            .secondary_label(&s.name, "This is not a port struct")
                            .span_suggest_insert_before(
                                format!("Consider making {} a port struct", s.name),
                                &s.name,
                                "port ",
                            )
                            .into());
                    }
                }
            }

            let members = visit_parameter_list(&s.members, symtab, &SelfContext::FreeStanding)?;

            let self_type =
                hir::TypeSpec::Declared(declaration_id.clone(), output_type_exprs.clone())
                    .at_loc(s);

            symtab.add_thing_with_name_id(
                declaration_id.inner.clone(),
                Thing::Struct(
                    StructCallable {
                        name: t.name.clone(),
                        self_type,
                        params: members.clone(),
                        type_params: type_params.clone(),
                    }
                    .at_loc(s),
                ),
            );

            items.executables.insert(
                declaration_id.inner.clone(),
                hir::ExecutableItem::StructInstance,
            );

            let mut wal_suffix = None;
            let attributes = s.attributes.lower(&mut |attr| match &attr.inner {
                ast::Attribute::WalSuffix {
                    suffix,
                    uses_rst,
                    uses_clk,
                } => {
                    wal_suffix = Some(
                        WalSuffix {
                            suffix: suffix.clone(),
                            uses_clk: uses_clk.clone(),
                            uses_rst: uses_rst.clone(),
                        }
                        .at_loc(attr),
                    );
                    Ok(None)
                }
                ast::Attribute::NoMangle
                | ast::Attribute::Fsm { .. }
                | ast::Attribute::WalTrace { .. } => Err(attr.report_unused("struct")),
            })?;

            // We don't do any special processing of structs here
            hir::TypeDeclKind::Struct(
                hir::Struct {
                    members,
                    is_port: s.is_port(),
                    attributes,
                    wal_suffix,
                }
                .at_loc(s),
            )
        }
    };
    // Close the symtab scope
    symtab.close_scope();

    // Add type to item list
    let decl = hir::TypeDeclaration {
        name: declaration_id.clone(),
        kind: hir_kind,
        generic_args: type_params,
    }
    .at_loc(t);
    items.types.insert(declaration_id.inner, decl);

    Ok(())
}

#[cfg(test)]
mod tests {
    use ast::{
        aparams,
        testutil::{ast_ident, ast_path},
        TypeParam,
    };
    use hir::{dtype, hparams, testutil::t_num, ItemList};
    use spade_common::{
        name::testutil::{name_id, name_id_p},
        num_ext::InfallibleToBigInt,
    };

    use super::*;

    #[test]
    fn type_declaration_visiting_works() {
        let input = ast::TypeDeclaration {
            name: ast_ident("test"),
            kind: ast::TypeDeclKind::Enum(
                ast::Enum {
                    name: ast_ident("test"),
                    options: vec![
                        // No arguments
                        (ast_ident("A"), None),
                        // Builtin type with no args
                        (
                            ast_ident("B"),
                            Some(
                                ast::ParameterList::without_self(vec![(
                                    ast_ident("x"),
                                    ast::TypeSpec::Named(ast_path("bool"), None).nowhere(),
                                )])
                                .nowhere(),
                            ),
                        ),
                        // Builtin type with no args
                        (
                            ast_ident("C"),
                            Some(
                                ast::ParameterList::without_self(vec![(
                                    ast_ident("x"),
                                    ast::TypeSpec::Named(
                                        ast_path("int"),
                                        Some(
                                            vec![ast::TypeExpression::Integer(10u32.to_bigint())
                                                .nowhere()]
                                            .nowhere(),
                                        ),
                                    )
                                    .nowhere(),
                                )])
                                .nowhere(),
                            ),
                        ),
                    ],
                }
                .nowhere(),
            ),
            generic_args: vec![],
        }
        .nowhere();

        // Populate the symtab with builtins
        let mut symtab = SymbolTable::new();

        let mut items = ItemList::new();

        crate::builtins::populate_symtab(&mut symtab, &mut ItemList::new());
        crate::global_symbols::visit_type_declaration(&input, &mut symtab)
            .expect("Failed to visit global symbol");
        crate::global_symbols::re_visit_type_declaration(&input, &mut symtab, &mut items)
            .expect("Failed to re-visit global symbol");

        let result = items.types.get(&name_id(0, "test").inner).unwrap();

        let expected = hir::TypeDeclaration {
            name: name_id(0, "test"),
            kind: hir::TypeDeclKind::Enum(
                hir::Enum {
                    options: vec![
                        (name_id_p(1, &["test", "A"]), hir::ParameterList(vec![])),
                        (
                            name_id_p(2, &["test", "B"]),
                            hparams![("x", dtype!(symtab => "bool"))],
                        ),
                        (
                            name_id_p(3, &["test", "C"]),
                            hparams![("x", dtype!(symtab => "int"; (t_num(10))))],
                        ),
                    ],
                }
                .nowhere(),
            ),
            generic_args: vec![],
        };

        assert_eq!(result.inner, expected);
    }

    #[test]
    fn type_declarations_with_generics_work() {
        let input = ast::TypeDeclaration {
            name: ast_ident("test"),
            kind: ast::TypeDeclKind::Enum(
                ast::Enum {
                    name: ast_ident("test"),
                    options: vec![
                        // Builtin type with no args
                        (ast_ident("B"), Some(aparams!(("a", ast::tspec!("T"))))),
                    ],
                }
                .nowhere(),
            ),
            generic_args: vec![TypeParam::TypeName(ast_ident("T")).nowhere()],
        }
        .nowhere();

        // Populate the symtab with builtins
        let mut symtab = SymbolTable::new();

        let mut items = ItemList::new();

        crate::builtins::populate_symtab(&mut symtab, &mut ItemList::new());
        crate::global_symbols::visit_type_declaration(&input, &mut symtab)
            .expect("Failed to visit global symbol");
        crate::global_symbols::re_visit_type_declaration(&input, &mut symtab, &mut items)
            .expect("Failed to visit global symbol");

        let result = items.types.get(&name_id(0, "test").inner).unwrap();

        let expected = hir::TypeDeclaration {
            name: name_id(0, "test"),
            kind: hir::TypeDeclKind::Enum(
                hir::Enum {
                    options: vec![(
                        name_id_p(2, &["test", "B"]),
                        hparams![("a", hir::TypeSpec::Generic(name_id(1, "T")).nowhere())],
                    )],
                }
                .nowhere(),
            ),
            generic_args: vec![hir::TypeParam::TypeName(
                ast_ident("T").inner,
                name_id(1, "T").inner,
            )
            .nowhere()],
        };

        assert_eq!(result.inner, expected);
    }
}
