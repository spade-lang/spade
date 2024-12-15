use std::collections::HashSet;

use hir::{
    symbol_table::{EnumVariant, StructCallable},
    TypeExpression, WalTraceable,
};
use spade_ast as ast;
use spade_common::{
    location_info::{Loc, WithLocation},
    name::{Identifier, Path},
};
use spade_diagnostics::Diagnostic;
use spade_hir as hir;
use spade_hir::WhereClause;
use spade_types::meta_types::MetaType;

use crate::{
    attributes::{AttributeListExt, LocAttributeExt},
    impls::create_trait_from_unit_heads,
    types::IsPort,
    visit_parameter_list, visit_trait_spec, visit_type_spec, Context, Result, TypeSpecKind,
};
use spade_hir::symbol_table::{GenericArg, Thing, TypeSymbol};

#[tracing::instrument(skip_all)]
pub fn gather_types(module: &ast::ModuleBody, ctx: &mut Context) -> Result<()> {
    for item in &module.members {
        match item {
            ast::Item::Type(t) => {
                visit_type_declaration(t, ctx)?;
            }
            ast::Item::Module(m) => {
                ctx.symtab.add_unique_thing(
                    Path::ident(m.name.clone()).at_loc(&m.name),
                    Thing::Module(m.name.clone()),
                )?;
                ctx.symtab.push_namespace(m.name.clone());
                if let Err(e) = gather_types(&m.body, ctx) {
                    ctx.symtab.pop_namespace();
                    return Err(e);
                };
                ctx.symtab.pop_namespace();
            }
            ast::Item::ImplBlock(_) => {}
            ast::Item::Unit(_) => {}
            ast::Item::TraitDef(_) => {
                // FIXME: When we end up needing to refer to traits, we should add them
                // to the symtab here
            }
            ast::Item::Config(cfg) => {
                ctx.symtab.add_unique_thing(
                    Path::ident(cfg.name.clone()).at_loc(&cfg.name),
                    Thing::ComptimeConfig(cfg.val.clone()),
                )?;
            }
            ast::Item::Use(u) => {
                let new_name = match &u.alias {
                    Some(name) => name.clone(),
                    None => u.path.0.last().unwrap().clone(),
                };

                ctx.symtab.add_alias(
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
pub fn gather_symbols(module: &ast::ModuleBody, ctx: &mut Context) -> Result<()> {
    for item in &module.members {
        visit_item(item, ctx)?;
    }
    Ok(())
}

#[tracing::instrument(skip_all)]
pub fn visit_item(item: &ast::Item, ctx: &mut Context) -> Result<()> {
    match item {
        ast::Item::Unit(e) => {
            visit_unit(&None, e, &None, &vec![], ctx)?;
        }
        ast::Item::TraitDef(def) => {
            let name = ctx.symtab.add_unique_thing(
                Path(vec![def.name.clone()]).at_loc(&def.name),
                Thing::Trait(def.name.clone()),
            )?;

            create_trait_from_unit_heads(
                hir::TraitName::Named(name.at_loc(&def.name)),
                &def.type_params,
                &def.where_clauses,
                &def.methods,
                ctx,
            )?;
        }
        ast::Item::ImplBlock(_) => {}
        ast::Item::Type(t) => {
            re_visit_type_declaration(t, ctx)?;
        }
        ast::Item::Module(m) => {
            ctx.symtab.push_namespace(m.name.clone());
            if let Err(e) = gather_symbols(&m.body, ctx) {
                ctx.symtab.pop_namespace();
                return Err(e);
            }
            ctx.symtab.pop_namespace();
        }
        ast::Item::Use(_) => {}
        ast::Item::Config(_) => {}
    }
    Ok(())
}

#[tracing::instrument(skip_all)]
pub fn visit_unit(
    extra_path: &Option<Path>,
    unit: &Loc<ast::Unit>,
    scope_type_params: &Option<Loc<Vec<Loc<ast::TypeParam>>>>,
    scope_where_clauses: &[Loc<WhereClause>],
    ctx: &mut Context,
) -> Result<()> {
    let head = crate::unit_head(&unit.head, scope_type_params, scope_where_clauses, ctx)?;

    let new_path = extra_path
        .as_ref()
        .unwrap_or(&Path(vec![]))
        .join(Path::ident(unit.head.name.clone()))
        .at_loc(&unit.head.name);

    ctx.symtab
        .add_unique_thing(new_path, Thing::Unit(head.at_loc(unit)))?;

    Ok(())
}

pub fn visit_meta_type(meta: &Loc<Identifier>) -> Result<MetaType> {
    let meta = match meta.inner.0.as_str() {
        "int" => MetaType::Int,
        "uint" => MetaType::Uint,
        "type" => MetaType::Type,
        _ => {
            return Err(Diagnostic::error(meta, "{meta} is not a valid meta-type")
                .primary_label("Invalid meta-type")
                .help("Expected #int, #uint or #type"))
        }
    };
    Ok(meta)
}

pub fn visit_type_declaration(t: &Loc<ast::TypeDeclaration>, ctx: &mut Context) -> Result<()> {
    let args = t
        .generic_args
        .as_ref()
        .map(|args| &args.inner)
        .unwrap_or(&vec![])
        .iter()
        .map(|arg| {
            let result = match &arg.inner {
                ast::TypeParam::TypeName { name, traits } => {
                    let traits = traits
                        .iter()
                        .map(|t| visit_trait_spec(t, &TypeSpecKind::TraitBound, ctx))
                        .collect::<Result<Vec<_>>>()?;

                    GenericArg::TypeName {
                        name: name.inner.clone(),
                        traits,
                    }
                }
                ast::TypeParam::TypeWithMeta { name, meta } => GenericArg::TypeWithMeta {
                    name: name.inner.clone(),
                    meta: visit_meta_type(meta)?,
                },
            }
            .at_loc(&arg.loc());
            Ok(result)
        })
        .collect::<Result<_>>()?;

    let kind = match &t.kind {
        ast::TypeDeclKind::Enum(_) => hir::symbol_table::TypeDeclKind::Enum,
        ast::TypeDeclKind::Struct(s) => hir::symbol_table::TypeDeclKind::Struct {
            is_port: s.is_port(),
        },
    };

    let new_thing = Path::ident(t.name.clone()).at_loc(&t.name.loc());
    ctx.symtab
        .add_unique_type(new_thing, TypeSymbol::Declared(args, kind).at_loc(t))?;

    Ok(())
}

/// Visit type declarations a second time, this time adding the type to the item list
/// as well as adding enum variants to the global scope.
/// This needs to happen as a separate pass since other types need to be in scope when
/// we check type declarations
pub fn re_visit_type_declaration(t: &Loc<ast::TypeDeclaration>, ctx: &mut Context) -> Result<()> {
    // Process right hand side of type declarations
    // The first visitor has already added the LHS to the symtab
    // Look up the ID
    let (declaration_id, _) = ctx
        .symtab
        .lookup_type_symbol(&Path(vec![t.name.clone()]).at_loc(&t.name))
        .expect("Expected type symbol to already be in symtab");
    let declaration_id = declaration_id.at_loc(&t.name);

    // Add the generic parameters to a new symtab scope
    ctx.symtab.new_scope();
    for param in t
        .generic_args
        .as_ref()
        .map(Loc::strip_ref)
        .unwrap_or(&vec![])
    {
        let (name, symbol_type) = match &param.inner {
            ast::TypeParam::TypeName { name: n, traits } => {
                let resolved_traits = traits
                    .iter()
                    .map(|t| visit_trait_spec(t, &TypeSpecKind::TraitBound, ctx))
                    .collect::<Result<Vec<_>>>()?;
                (
                    n,
                    TypeSymbol::GenericArg {
                        traits: resolved_traits,
                    },
                )
            }
            ast::TypeParam::TypeWithMeta { name, meta } => {
                (name, TypeSymbol::GenericMeta(visit_meta_type(meta)?))
            }
        };
        ctx.symtab
            .add_type(Path::ident(name.clone()), symbol_type.at_loc(param));
    }

    // Generate TypeExprs and TypeParam vectors which are needed for building the
    // hir::TypeDeclaration and for enum constructors
    let mut output_type_exprs = vec![];
    let mut type_params = vec![];
    for arg in t.generic_args.as_ref().map(|l| &l.inner).unwrap_or(&vec![]) {
        let (name_id, _) = ctx
            .symtab
            .lookup_type_symbol(&Path(vec![arg.name().clone()]).at_loc(arg))
            .expect("Expected generic param to be in symtab");
        let expr = TypeExpression::TypeSpec(hir::TypeSpec::Generic(name_id.clone().at_loc(arg)))
            .at_loc(arg);
        let param = match &arg.inner {
            ast::TypeParam::TypeName { name, traits } => {
                let trait_bounds = traits
                    .iter()
                    .map(|t| visit_trait_spec(t, &TypeSpecKind::TraitBound, ctx))
                    .collect::<Result<Vec<_>>>()?;

                hir::TypeParam {
                    ident: name.clone(),
                    name_id: name_id.clone(),
                    trait_bounds,
                    meta: MetaType::Type,
                }
            }
            ast::TypeParam::TypeWithMeta { meta, name } => hir::TypeParam {
                ident: name.clone(),
                name_id: name_id.clone(),
                trait_bounds: vec![],
                meta: visit_meta_type(&meta)?,
            },
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
                            .secondary_label(prev, "Previously occurred here"),
                    );
                }
                member_names.insert(option.0.clone());
                // Check the parameter list
                let parameter_list = option
                    .1
                    .clone()
                    .map(|l| visit_parameter_list(&l, ctx))
                    .unwrap_or_else(|| Ok(hir::ParameterList(vec![]).nowhere()))?;

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
                    let ty = visit_type_spec(&ty, &TypeSpecKind::EnumMember, ctx)?;
                    if ty.is_port(&ctx)? {
                        return Err(Diagnostic::error(ty, "Port in enum")
                            .primary_label("This is a port")
                            .secondary_label(&e.name, "This is an enum"));
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
                let head_id = ctx.symtab.add_thing_at_offset(
                    1,
                    Path(vec![e.name.clone(), option.0.clone()]),
                    Thing::EnumVariant(variant_thing.at_loc(&option.0)),
                );
                // Add option constructor to item list
                ctx.item_list.executables.insert(
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
                ));
            }
            // Disallow normal arguments if the struct is a port, and port types
            // if it is not
            if s.is_port() {
                for (_, f, ty) in &s.members.args {
                    let hir_ty = visit_type_spec(ty, &TypeSpecKind::StructMember, ctx)?;
                    if !hir_ty.is_port(ctx)? {
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
                            ));
                    }
                }
            } else {
                for (_, _, ty) in &s.members.args {
                    let hir_ty = visit_type_spec(ty, &TypeSpecKind::StructMember, ctx)?;
                    if hir_ty.is_port(ctx)? {
                        return Err(Diagnostic::error(ty, "Port in non-port struct")
                            .primary_label("This is a port")
                            .secondary_label(&s.name, "This is not a port struct")
                            .span_suggest_insert_before(
                                format!("Consider making {} a port struct", s.name),
                                &s.name,
                                "port ",
                            ));
                    }
                }
            }

            let members = visit_parameter_list(&s.members, ctx)?;

            let self_type =
                hir::TypeSpec::Declared(declaration_id.clone(), output_type_exprs.clone())
                    .at_loc(s);

            ctx.symtab.add_thing_with_name_id(
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

            ctx.item_list.executables.insert(
                declaration_id.inner.clone(),
                hir::ExecutableItem::StructInstance,
            );

            let mut wal_traceable = None;
            let attributes = s.attributes.lower(&mut |attr| match &attr.inner {
                ast::Attribute::WalTraceable {
                    suffix,
                    uses_rst,
                    uses_clk,
                } => {
                    let suffix = if let Some(suffix) = suffix {
                        Path(vec![suffix.clone()])
                    } else {
                        declaration_id.1.clone()
                    };
                    wal_traceable = Some(
                        WalTraceable {
                            suffix,
                            uses_clk: *uses_clk,
                            uses_rst: *uses_rst,
                        }
                        .at_loc(attr),
                    );
                    Ok(None)
                }
                ast::Attribute::Optimize { .. }
                | ast::Attribute::NoMangle
                | ast::Attribute::Fsm { .. }
                | ast::Attribute::WalSuffix { .. }
                | ast::Attribute::WalTrace { .. } => Err(attr.report_unused("struct")),
            })?;

            // We don't do any special processing of structs here
            hir::TypeDeclKind::Struct(
                hir::Struct {
                    members,
                    is_port: s.is_port(),
                    attributes,
                    wal_traceable,
                }
                .at_loc(s),
            )
        }
    };
    // Close the symtab scope
    ctx.symtab.close_scope();

    // Add type to item list
    let decl = hir::TypeDeclaration {
        name: declaration_id.clone(),
        kind: hir_kind,
        generic_args: type_params,
    }
    .at_loc(t);
    ctx.item_list.types.insert(declaration_id.inner, decl);

    Ok(())
}
