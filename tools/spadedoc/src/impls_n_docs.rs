use rustc_hash::FxHashMap as HashMap;
use spade_ast::{self as ast, AttributeList};
use spade_common::{
    location_info::{Loc, WithLocation},
    name::{Identifier, NameID, Path, PathSegment},
};
use spade_diagnostics::Diagnostic;
use spade_hir::symbol_table::SymbolTable;

pub(crate) struct ImplsNDocs {
    pub(crate) for_type: HashMap<NameID, (Vec<DirectImpl>, Vec<TraitImpl>)>,
    pub(crate) docs: HashMap<NameID, String>,
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
        // Maybe append with double newline seperator
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
        // Maybe prepend with double newline seperator
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

                if let Some(trt) = block.r#trait.clone() {
                    let timpl = TraitImpl {
                        r#trait: trt.inner,
                        type_params: block.type_params.clone(),
                        where_clauses: block.where_clauses.clone(),
                        target: block.target.inner.clone(),
                        units: block.units.clone(),
                    };

                    for_all_targets(&block.target, &mut |t| {
                        let Ok(target) = ctx.symtab.lookup_id(t, true) else {
                            println!("Couldn't find {t}");
                            return; /* Generics */
                        };
                        impls
                            .for_type
                            .entry(target)
                            .or_default()
                            .1
                            .push(timpl.clone());
                    });
                } else {
                    let dimpl = DirectImpl {
                        type_params: block.type_params.clone(),
                        where_clauses: block.where_clauses.clone(),
                        target: block.target.inner.clone(),
                        units: block.units.clone(),
                    };

                    for_all_targets(&block.target, &mut |t| {
                        let Ok(target) = ctx.symtab.lookup_id(t, true) else {
                            println!("Couldn't find {t}");
                            return; /* Generics */
                        };
                        impls
                            .for_type
                            .entry(target)
                            .or_default()
                            .0
                            .push(dimpl.clone());
                    });
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

fn for_all_targets(target_spec: &ast::TypeSpec, f: &mut impl FnMut(&Loc<Path>)) {
    match target_spec {
        ast::TypeSpec::Tuple(exprs) => exprs.into_iter().for_each(|expr| for_all_expr(expr, f)),
        ast::TypeSpec::Array { inner, size: _ } => for_all_expr(&inner, f),
        ast::TypeSpec::Named(path, _params) => f(path),
        ast::TypeSpec::Inverted(inner) => for_all_expr(&inner, f),
        // Following `spade_ast_lowering::get_impl_target`, those are illegal in target position.
        ast::TypeSpec::Impl(_) => todo!(),
        ast::TypeSpec::Wildcard => todo!(),
    }
}

fn for_all_expr(expr: &ast::TypeExpression, f: &mut impl FnMut(&Loc<Path>)) {
    match expr {
        ast::TypeExpression::TypeSpec(inner) => for_all_targets(inner, f),
        ast::TypeExpression::Bool(_) => todo!(),
        ast::TypeExpression::Integer(_big_int) => todo!(),
        ast::TypeExpression::String(_) => todo!(),
        ast::TypeExpression::ConstGeneric(_loc) => todo!(),
    }
}
