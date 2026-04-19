use rustc_hash::FxHashMap as HashMap;
use spade_ast::{self as ast, AttributeList, TypeSpec};
use spade_common::{
    location_info::{Loc, WithLocation},
    name::{Identifier, NameID, Path, PathSegment},
};
use spade_diagnostics::Diagnostic;
use spade_hir::symbol_table::{SymbolTable, TypeSymbol};

#[derive(Clone, Hash, PartialEq, Eq)]
pub enum ImplTargetBase {
    Named(NameID),
    Tuple,
    Array,
    Inv,
    CopyView,
    Str,
}

impl ImplTargetBase {
    /// Calls `f` for the inner most specialized type specs and returns `false` if there were none.
    fn for_type_spec(
        spec: &TypeSpec,
        symtab: &SymbolTable,
        f: &mut impl FnMut(ImplTargetBase),
    ) -> bool {
        match spec {
            TypeSpec::Tuple(exprs) => {
                let not_specialized = !exprs.into_iter().any(|e| Self::for_type_expr(e, symtab, f));
                if not_specialized {
                    f(ImplTargetBase::Tuple);
                }
                true
            }
            TypeSpec::Array { inner, .. } => {
                let not_specialized = !Self::for_type_expr(inner, symtab, f);
                if not_specialized {
                    f(ImplTargetBase::Array);
                }
                true
            }
            TypeSpec::Named(name, _) => {
                if let Ok((target, ty)) = symtab.lookup_type_symbol(name, true) {
                    match ty.inner {
                        TypeSymbol::Declared(_, _, _) => {
                            f(ImplTargetBase::Named(target));
                            true
                        }
                        TypeSymbol::GenericArg { .. } | TypeSymbol::GenericMeta(_) => false,
                    }
                } else {
                    println!("Couldn't find {name}");
                    false
                }
            }
            TypeSpec::Inverted(inner) => {
                let not_specialized = !Self::for_type_expr(inner, symtab, f);
                if not_specialized {
                    f(ImplTargetBase::Inv);
                }
                true
            }
            TypeSpec::CopyView(inner) => {
                let not_specialized = !Self::for_type_expr(inner, symtab, f);
                if not_specialized {
                    f(ImplTargetBase::CopyView);
                }
                true
            }

            // These cannot occur on impl blocks
            TypeSpec::Impl(_) => unreachable!(),
            TypeSpec::Wildcard => unreachable!(),
        }
    }

    fn for_type_expr(
        expr: &ast::TypeExpression,
        symtab: &SymbolTable,
        f: &mut impl FnMut(ImplTargetBase),
    ) -> bool {
        match expr {
            ast::TypeExpression::TypeSpec(inner) => Self::for_type_spec(inner, symtab, f),
            // Those are all unreachable as for e.g. uint<8>, it would only go until uint and then stop, we don't iterate over any real exprs
            ast::TypeExpression::Bool(_) => unreachable!(),
            ast::TypeExpression::Integer(_big_int) => unreachable!(),
            ast::TypeExpression::String(_) => unreachable!(),
            ast::TypeExpression::ConstGeneric(_loc) => unreachable!(),
        }
    }
}

pub type ImplList = (Vec<DirectImpl>, Vec<TraitImpl>);
pub type ImplMap = HashMap<ImplTargetBase, ImplList>;

pub(crate) struct ImplsNDocs {
    pub(crate) for_type: ImplMap,
    pub(crate) docs: HashMap<NameID, String>,

    /// Impl blocks which appear in a module but which are not impl blocks for types
    /// defined in that module. These are rendered in the docs for the module in addition
    /// to on the type they impl for.
    pub(crate) wild_impls: HashMap<NameID, ImplList>,
}

#[derive(Clone)]
pub(crate) struct DirectImpl {
    pub(crate) type_params: Option<Loc<Vec<Loc<ast::TypeParam>>>>,
    pub(crate) where_clauses: Vec<ast::WhereClause>,
    pub(crate) target: ast::TypeSpec,
    pub(crate) units: Vec<Loc<ast::Unit>>,
}

#[derive(Clone)]
pub(crate) struct TraitImpl {
    pub(crate) r#trait: ast::TraitSpec,
    pub(crate) type_params: Option<Loc<Vec<Loc<ast::TypeParam>>>>,
    pub(crate) where_clauses: Vec<ast::WhereClause>,
    pub(crate) target: ast::TypeSpec,
    pub(crate) units: Vec<Loc<ast::Unit>>,
}

impl ImplsNDocs {
    fn add_outer_doc(
        &mut self,
        symtab: &SymbolTable,
        name: &Loc<Identifier>,
        attrs: &AttributeList,
    ) {
        let nameid = symtab
            .lookup_id(&Path::ident(*name).nowhere(), false)
            .expect("Couldn't lookup own type for documentation?");

        let merged = attrs.merge_docs();
        // Maybe append with double newline separator
        if let Some(pre) = self.docs.get_mut(&nameid) {
            pre.extend(["\n\n", &merged]);
        } else {
            self.docs.insert(nameid, merged);
        }
    }
    fn add_inner_doc(&mut self, symtab: &SymbolTable, docs: &[String]) {
        let nameid = symtab
            .lookup_id(&Path::from_idents(&[]).nowhere(), false)
            .expect("Couldn't lookup own type for documentation?");

        let mut merged = docs.join("\n");
        // Maybe prepend with double newline separator
        if let Some(post) = self.docs.get_mut(&nameid) {
            merged.extend(["\n\n", post]);
            *post = merged;
        } else {
            self.docs.insert(nameid, merged);
        }
    }
}

pub(crate) fn gather_impls_n_docs(
    module_ast: &Loc<ast::ModuleBody>,
    impls: &mut ImplsNDocs,
    ctx: &mut spade_ast_lowering::Context,
) -> Result<(), Diagnostic> {
    impls.add_inner_doc(&ctx.symtab, &module_ast.documentation);

    for item in &module_ast.members {
        match item {
            ast::Item::Unit(u) => {
                impls.add_outer_doc(&ctx.symtab, &u.head.name, &u.head.attributes);
            }
            ast::Item::MacroDef(_) => {
                // FIXME: Once macros become user-definable, we should handle them
            }
            ast::Item::TraitDef(t) => {
                impls.add_outer_doc(&ctx.symtab, &t.name, &t.attributes);
            }
            ast::Item::ImplBlock(block) => {
                // Parts of this are stolen from `spade_ast_lowering::visit_impl_inner`

                // This adds the generics to the symtab
                let _ = spade_ast_lowering::visit_type_params(&block.type_params, ctx)?;

                // FIXME: introducing `Self` makes problems down the symtab resolving
                // let self_name = Identifier::intern("Self").nowhere();
                // let alias_id = ctx.symtab.add_type(
                //     self_name,
                //     symtab::TypeSymbol::Declared(vec![], 0, symtab::TypeDeclKind::Alias)
                //         .at_loc(&block.target),
                //     spade_common::name::Visibility::Implicit.nowhere(),
                //     None,
                // );

                // if let ast::TypeSpec::Named(path, _) = &block.target.inner {
                //     ctx.symtab.add_thing_with_name_id(
                //         alias_id.clone(),
                //         symtab::Thing::Alias {
                //             loc: block.target.loc(),
                //             path: path.clone(),
                //             in_namespace: ctx.symtab.current_namespace().clone(),
                //         },
                //         None,
                //         None,
                //     );
                // }

                let is_wild_target = |target: &ImplTargetBase| {
                    match &target {
                        ImplTargetBase::Named(name_id) => {
                            !name_id.1.starts_with(ctx.symtab.current_namespace())
                        }
                        // Foreign types do not belong to any module, so they are always
                        // wild
                        ImplTargetBase::Tuple
                        | ImplTargetBase::Array
                        | ImplTargetBase::Inv
                        | ImplTargetBase::CopyView
                        | ImplTargetBase::Str => true,
                    }
                };

                if let Some(trt) = block.r#trait.clone() {
                    let timpl = TraitImpl {
                        r#trait: trt.inner,
                        type_params: block.type_params.clone(),
                        where_clauses: block.where_clauses.clone(),
                        target: block.target.inner.clone(),
                        units: block.units.clone(),
                    };

                    let mut is_wild = true;
                    ImplTargetBase::for_type_spec(&block.target, &ctx.symtab, &mut |target| {
                        impls
                            .for_type
                            .entry(target.clone())
                            .or_default()
                            .1
                            .push(timpl.clone());

                        if !is_wild_target(&target) {
                            // At least one of the most inner named targets are in this module,
                            // so no need to also document it in the wild in the module.
                            is_wild = false;
                        }
                    });
                    if is_wild {
                        if let Ok((module_name, _)) = ctx
                            .symtab
                            .lookup_thing(&ctx.symtab.current_namespace().clone().nowhere(), true)
                        {
                            impls
                                .wild_impls
                                .entry(module_name)
                                .or_default()
                                .1
                                .push(timpl.clone());
                        }
                    }
                } else {
                    let dimpl = DirectImpl {
                        type_params: block.type_params.clone(),
                        where_clauses: block.where_clauses.clone(),
                        target: block.target.inner.clone(),
                        units: block.units.clone(),
                    };

                    let mut is_wild = true;
                    ImplTargetBase::for_type_spec(&block.target, &ctx.symtab, &mut |target| {
                        impls
                            .for_type
                            .entry(target.clone())
                            .or_default()
                            .0
                            .push(dimpl.clone());

                        if !is_wild_target(&target) {
                            // At least one of the most inner named targets are in this module,
                            // so no need to also document it in the wild in the module.
                            is_wild = false;
                        }
                    });
                    if is_wild {
                        if let Ok((module_name, _)) = ctx
                            .symtab
                            .lookup_thing(&ctx.symtab.current_namespace().clone().nowhere(), true)
                        {
                            impls
                                .wild_impls
                                .entry(module_name)
                                .or_default()
                                .0
                                .push(dimpl.clone());
                        }
                    }
                }
            }
            ast::Item::Type(t) => {
                let attrs = match &t.kind {
                    spade_ast::TypeDeclKind::Enum(e) => &e.attributes,
                    spade_ast::TypeDeclKind::Struct(s) => &s.attributes,
                    spade_ast::TypeDeclKind::Alias(a) => &a.attributes,
                };
                impls.add_outer_doc(&ctx.symtab, &t.name, attrs);
            }
            ast::Item::ExternalMod(m) => {
                impls.add_outer_doc(&ctx.symtab, &m.name, &m.attributes);
            }
            ast::Item::Module(m) => {
                impls.add_outer_doc(&ctx.symtab, &m.name, &m.attributes);

                ctx.symtab
                    .push_namespace(PathSegment::Named(m.name.clone()));
                if let Err(e) = gather_impls_n_docs(&m.body, impls, ctx) {
                    ctx.symtab.pop_namespace();
                    return Err(e);
                }
                ctx.symtab.pop_namespace();
            }
            ast::Item::Use(_, _) => {}
        }
    }

    Ok(())
}
