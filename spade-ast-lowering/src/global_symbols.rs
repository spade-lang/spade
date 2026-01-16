use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};

use hir::{
    symbol_table::{EnumVariant, StructCallable},
    TypeExpression, WalTraceable,
};
use spade_ast::{self as ast, Module, ModuleBody};
use spade_common::{
    location_info::{Loc, WithLocation},
    name::{Identifier, Path, Visibility},
    namespace::ModuleNamespace,
};
use spade_diagnostics::{diag_anyhow, Diagnostic};
use spade_hir::WhereClause;
use spade_hir::{self as hir, symbol_table::TraitMarker};
use spade_types::meta_types::MetaType;

use crate::{
    attributes::{AttributeListExt, LocAttributeExt},
    impls::create_trait_from_unit_heads,
    types::{IsInOut, IsPort},
    visit_parameter_list, visit_trait_spec, visit_type_spec, Context, Result, TypeSpecKind,
};
use spade_hir::symbol_table::{GenericArg, Thing, TypeSymbol};

pub fn handle_external_modules(
    this_file: &str,
    inner_module: Option<&Loc<Module>>,
    module: &ast::ModuleBody,
    namespaces: &mut HashMap<Path, String>,
    ctx: &mut Context,
) -> Result<()> {
    for item in &module.members {
        match item {
            ast::Item::ExternalMod(ref em) => {
                let name = &em.name;
                if let Some(inner) = inner_module {
                    return Err(Diagnostic::error(
                        name,
                        "Modules from different files cannot be defined inside inline modules",
                    )
                    .primary_label("Module defined in inline module")
                    .secondary_label(inner, "Inline module defined here"));
                } else {
                    // If we get an external module, we need to
                    // 1. check that there is an associated file
                    // 2. Replace the loc of that module with the source code
                    let path = ctx.symtab.current_namespace().push_ident(name.clone());

                    // We're going to eagerly add the `mod` first in order to detect duplicates.
                    let name_id = ctx.symtab.add_unique_thing(
                        Path::ident(name.clone()).at_loc(&name),
                        Thing::Module(em.loc(), name.clone()),
                        Some(em.visibility.clone()),
                    )?;

                    ctx.item_list.modules.insert(
                        name_id.clone(),
                        spade_hir::Module {
                            name: name_id.at_loc(&name),
                            documentation: String::new(),
                        },
                    );

                    if namespaces.remove(&path).is_none() {
                        let name_parts = this_file.split("/").collect::<Vec<_>>();
                        if name_parts.len() > 1 {
                            let base = name_parts[0..name_parts.len() - 1].join("/");
                            let expected_name = format!("{base}/{name}.spade");
                            let expected_mod = format!("{base}/{name}/main.spade");

                            return Err(Diagnostic::error(
                                name,
                                format!("Did not find {expected_name} or {expected_mod}"),
                            )
                            .primary_label(format!("Did not find file for {name}")));
                        } else {
                            return Err(Diagnostic::error(
                                    name,
                                    format!("Did not find file for {name}"),
                                )
                                .help("Are you running Spade without swim? If so, multiple files are unsupported"));
                        };
                    }
                }
            }
            ast::Item::Module(m) => ctx.in_named_namespace(m.name.clone(), |ctx| {
                handle_external_modules(this_file, Some(m), &m.body, namespaces, ctx)
            })?,
            ast::Item::Type(_) => {}
            ast::Item::ImplBlock(_) => {}
            ast::Item::Unit(_) => {}
            ast::Item::TraitDef(_) => {}
            ast::Item::Use(_) => {}
        }
    }
    Ok(())
}

pub fn report_missing_mod_declarations(
    module_asts: &[(ModuleNamespace, Loc<ModuleBody>)],
    missing_namespace_set: &HashMap<Path, String>,
) -> Vec<Diagnostic> {
    // If we have things left in the namespace_set, we are missing a few `mod`, let's report
    // those
    let missing_namespace_set = missing_namespace_set
        .iter()
        .filter(|ns| !ns.0 .0.is_empty() && !(ns.1.ends_with("main.spade")))
        .collect::<Vec<_>>();

    missing_namespace_set
        .iter()
        .map(|(path, file)| {
            if path.0.len() == 0 {
                return diag_anyhow!(
                    ().nowhere(),
                    "Internal error: Found no mod for empty path (in {file})"
                );
            }

            let ns = path.tail();
            let parent_path = path.prelude();
            let parent_loc = module_asts.iter().find_map(|(ns, ast)| {
                if ns.namespace == parent_path {
                    Some(ast.loc())
                } else {
                    None
                }
            });

            if let Some(parent_loc) = parent_loc {
                Diagnostic::error(parent_loc, format!("Missing `mod {ns};` for {file}"))
                    .primary_label(format!("Missing `mod {ns};`"))
                    .span_suggest_insert_before(
                        format!("Consider adding `mod {ns};`"),
                        parent_loc,
                        format!("mod {ns}; "),
                    )
            } else {
                diag_anyhow!(().nowhere(), "Found {file} which is missing `mod` but the file where `mod` should go was not found")
            }
        })
        .collect()
}

#[tracing::instrument(skip_all)]
pub fn gather_types(module: &ast::ModuleBody, ctx: &mut Context) -> Result<()> {
    for item in &module.members {
        match item {
            ast::Item::Type(ref t) => {
                visit_type_declaration(t, ctx)?;
            }
            ast::Item::ExternalMod(_) => {}
            ast::Item::Module(ref m) => {
                ctx.symtab.add_unique_thing(
                    Path::ident(m.name.clone()).at_loc(&m.name),
                    Thing::Module(m.loc(), m.name.clone()),
                    Some(m.visibility.clone()),
                )?;
                ctx.in_named_namespace(m.name.clone(), |ctx| gather_types(&m.body, ctx))?
            }
            ast::Item::ImplBlock(_) => {}
            ast::Item::Unit(_) => {}
            ast::Item::TraitDef(ref r#trait) => {
                ctx.symtab.add_unique_thing(
                    Path::ident(r#trait.name.clone()).at_loc(&r#trait.name.clone()),
                    Thing::Trait(
                        TraitMarker {
                            name: r#trait.name.clone(),
                            paren_sugar: r#trait
                                .inner
                                .attributes
                                .0
                                .iter()
                                .any(|attr| attr.inner == ast::Attribute::SpadecParenSugar),
                        }
                        .at_loc(&r#trait.name),
                    ),
                    Some(r#trait.visibility.clone()),
                )?;
            }
            ast::Item::Use(us) => {
                for u in &us.inner {
                    let new_name = match &u.alias {
                        Some(name) => name.clone(),
                        None => u.path.0.last().unwrap().unwrap_named().clone(),
                    };

                    ctx.symtab
                        .add_alias(new_name, u.path.clone(), u.visibility.clone())?;
                }
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
        ast::Item::Unit(ref e) => {
            visit_unit(&None, e, &None, &vec![], ctx)?;
        }
        ast::Item::TraitDef(ref def) => {
            let (name, _) = ctx.symtab.lookup_trait(&Path::ident(def.name.clone()).at_loc(&def.name)).map_err(|_| diag_anyhow!(def, "Did not find the trait in the trait list when looking it up during item visiting"))?;
            let mut paren_sugar = false;
            let documentation = def.attributes.merge_docs();
            let _ = def.attributes.lower(&mut |attr| match &attr.inner {
                ast::Attribute::Documentation { .. } => Ok(None),
                ast::Attribute::SpadecParenSugar => {
                    paren_sugar = true;
                    Ok(None)
                }
                ast::Attribute::VerilogAttrs { .. }
                | ast::Attribute::Optimize { .. }
                | ast::Attribute::SurferTranslator(_)
                | ast::Attribute::WalTraceable { .. }
                | ast::Attribute::NoMangle { .. }
                | ast::Attribute::Fsm { .. }
                | ast::Attribute::WalSuffix { .. }
                | ast::Attribute::WalTrace { .. } => Err(attr.report_unused("trait")),
            })?;
            create_trait_from_unit_heads(
                hir::TraitName::Named(name.at_loc(&def.name)),
                &def.type_params,
                &def.where_clauses,
                &def.methods,
                paren_sugar,
                documentation,
                ctx,
            )?;
        }
        ast::Item::ImplBlock(_) => {}
        ast::Item::Type(ref t) => {
            re_visit_type_declaration(t, ctx)?;
        }
        ast::Item::ExternalMod(_) => {}
        ast::Item::Module(m) => {
            ctx.in_named_namespace(m.name.clone(), |ctx| gather_symbols(&m.body, ctx))?
        }
        ast::Item::Use(_) => {}
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
    let head = crate::unit_head(
        &unit.head,
        scope_type_params,
        scope_where_clauses,
        ctx,
        unit.inner.body.as_ref(),
    )?;

    let new_path = extra_path
        .as_ref()
        .unwrap_or(&Path(vec![]))
        .join(Path::ident(unit.head.name.clone()))
        .at_loc(&unit.head.name);

    ctx.symtab.add_unique_thing(
        new_path,
        Thing::Unit(head.at_loc(unit)),
        Some(unit.head.visibility.clone()),
    )?;

    Ok(())
}

pub fn visit_meta_type(meta: &Loc<Identifier>) -> Result<MetaType> {
    let meta = match meta.inner.as_str() {
        "int" => MetaType::Int,
        "uint" => MetaType::Uint,
        "str" => MetaType::Str,
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

    let new_thing = t.name.clone();
    ctx.symtab.add_unique_type(
        new_thing,
        TypeSymbol::Declared(args, kind).at_loc(t),
        t.visibility.clone(),
    )?;

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
        .lookup_type_symbol(&Path::ident_with_loc(t.name.clone()))
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
        ctx.symtab.add_type(
            name.clone(),
            symbol_type.at_loc(param),
            t.visibility.clone(),
        );
    }

    // Generate TypeExprs and TypeParam vectors which are needed for building the
    // hir::TypeDeclaration and for enum constructors
    let mut output_type_exprs = vec![];
    let mut type_params = vec![];
    for arg in t.generic_args.as_ref().map(|l| &l.inner).unwrap_or(&vec![]) {
        let (name_id, _) = ctx
            .symtab
            .lookup_type_symbol(&Path::ident_with_loc(arg.name().clone()))
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
            let mut member_names = HashSet::<Loc<Identifier>>::default();
            let mut hir_options = vec![];

            // Set variant visibility based on enum visibility
            let variant_vis = match *t.visibility {
                // Implicit visibility (no visibility marker attached) is equivalent to `pub(self)`.
                // This means that an enum with implicit visibility must have enum variants with
                // `super` visibility.
                Visibility::Implicit => Visibility::AtSuper,
                Visibility::Public => Visibility::Public,
                Visibility::AtLib => Visibility::AtLib,
                Visibility::AtSelf => Visibility::AtSuper,
                Visibility::AtSuper => Visibility::AtSuperSuper,
                Visibility::AtSuperSuper => {
                    return Err(Diagnostic::bug(
                        t.loc(),
                        "Impossible visibility found while setting enum variant visibility",
                    ))
                }
            };

            for (i, variant) in e.variants.iter().enumerate() {
                if let Some(prev) = member_names.get(&variant.name) {
                    let new = &variant.name;
                    return Err(
                        Diagnostic::error(new, format!("Multiple options called {}", new))
                            .primary_label(format!("{} occurs more than once", new))
                            .secondary_label(prev, "Previously occurred here"),
                    );
                }
                member_names.insert(variant.name.clone());
                // Check the parameter list
                let parameter_list = variant
                    .args
                    .clone()
                    .map(|l| visit_parameter_list(&l, ctx, None))
                    .unwrap_or_else(|| Ok(hir::ParameterList(vec![]).nowhere()))?;

                let args = variant
                    .args
                    .clone()
                    .map(|l| {
                        if let Some(ref self_) = l.self_ {
                            Err(Diagnostic::bug(self_, "enum member contains self"))
                        } else {
                            Ok(l.args.clone())
                        }
                    })
                    .unwrap_or(Ok(vec![]))?;

                // Ensure that we don't have any port or inout types in the enum variants
                for (_, _, ty) in args {
                    let ty = visit_type_spec(&ty, &TypeSpecKind::EnumMember, ctx)?;
                    if ty.is_port(&ctx)? {
                        return Err(Diagnostic::error(ty, "Port in enum")
                            .primary_label("This is a port")
                            .secondary_label(&e.name, "This is an enum"));
                    }
                    if ty.is_inout(&ctx)? {
                        return Err(Diagnostic::error(ty, "Inout in enum")
                            .primary_label("This is an inout")
                            .secondary_label(&e.name, "This is an enum"));
                    }
                }

                let documentation = variant.attributes.merge_docs();
                let _ = variant.attributes.lower(&mut |attr| match &attr.inner {
                    ast::Attribute::Documentation { .. } => Ok(None),
                    ast::Attribute::Optimize { .. }
                    | ast::Attribute::VerilogAttrs { .. }
                    | ast::Attribute::SurferTranslator(_)
                    | ast::Attribute::SpadecParenSugar
                    | ast::Attribute::WalTraceable { .. }
                    | ast::Attribute::NoMangle { .. }
                    | ast::Attribute::Fsm { .. }
                    | ast::Attribute::WalSuffix { .. }
                    | ast::Attribute::WalTrace { .. } => Err(attr.report_unused("enum variant")),
                })?;

                let variant_thing = EnumVariant {
                    name: variant.name.clone(),
                    output_type: hir::TypeSpec::Declared(
                        declaration_id.clone(),
                        output_type_exprs.clone(),
                    )
                    .at_loc(t),
                    type_params: type_params.clone(),
                    option: i,
                    params: parameter_list.clone(),
                    documentation,
                };

                // Add option constructor to symtab at the outer scope
                let head_id = ctx.symtab.add_thing_at_offset(
                    1,
                    Path::from_idents(&[&e.name, &variant.name]),
                    Thing::EnumVariant(variant_thing.at_loc(&variant.name)),
                    Some(variant_vis.clone().at_loc(&t.visibility)),
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
                hir_options.push((head_id.clone().at_loc(&variant.name), parameter_list))
            }

            let documentation = e.attributes.merge_docs();
            let _ = e.attributes.lower(&mut |attr| match &attr.inner {
                ast::Attribute::Documentation { .. } => Ok(None),
                ast::Attribute::Optimize { .. }
                | ast::Attribute::VerilogAttrs { .. }
                | ast::Attribute::WalTraceable { .. }
                | ast::Attribute::SpadecParenSugar
                | ast::Attribute::NoMangle { .. }
                | ast::Attribute::Fsm { .. }
                | ast::Attribute::WalSuffix { .. }
                | ast::Attribute::SurferTranslator(_)
                | ast::Attribute::WalTrace { .. } => Err(attr.report_unused("enum")),
            })?;

            hir::TypeDeclKind::Enum(
                hir::Enum {
                    options: hir_options,
                    documentation,
                }
                .at_loc(e),
            )
        }
        ast::TypeDeclKind::Struct(s) => {
            if let Some(ref self_) = s.members.self_ {
                return Err(Diagnostic::bug(
                    self_,
                    "struct contains self member which was let through parser",
                ));
            }

            // Disallow normal arguments if the struct is a port, and port types
            // if it is not
            for (_, f, ty) in &s.members.args {
                let hir_ty = visit_type_spec(ty, &TypeSpecKind::StructMember, ctx)?;
                if hir_ty.is_inout(ctx)? {
                    return Err(Diagnostic::error(ty, "Inout in struct")
                        .primary_label("This is an inout")
                        .secondary_label(&s.name, "This is a struct"));
                }
                if s.is_port() {
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
                } else {
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

            let members = visit_parameter_list(&s.members, ctx, None)?;

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
                Some(t.visibility.clone()),
            );

            ctx.item_list.executables.insert(
                declaration_id.inner.clone(),
                hir::ExecutableItem::StructInstance,
            );

            let mut wal_traceable = None;
            let documentation = s.attributes.merge_docs();
            let attributes = s.attributes.lower(&mut |attr| match &attr.inner {
                ast::Attribute::WalTraceable {
                    suffix,
                    uses_rst,
                    uses_clk,
                } => {
                    let suffix = if let Some(suffix) = suffix {
                        Path::ident(suffix.clone())
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
                ast::Attribute::Documentation { .. } => Ok(None),
                ast::Attribute::Optimize { .. }
                | ast::Attribute::VerilogAttrs { .. }
                | ast::Attribute::NoMangle { .. }
                | ast::Attribute::Fsm { .. }
                | ast::Attribute::WalSuffix { .. }
                | ast::Attribute::SpadecParenSugar
                | ast::Attribute::SurferTranslator(_)
                | ast::Attribute::WalTrace { .. } => Err(attr.report_unused("struct")),
            })?;

            // We don't do any special processing of structs here
            hir::TypeDeclKind::Struct(
                hir::Struct {
                    members,
                    is_port: s.is_port(),
                    attributes,
                    wal_traceable,
                    documentation,
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
