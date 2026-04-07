use rustc_hash::FxHashMap as HashMap;
use spade_ast as ast;
use spade_common::{
    location_info::{Loc, WithLocation as _},
    name::{Identifier, NameID, Path, PathSegment},
};
use spade_diagnostics::Diagnostic;
use spade_hir::symbol_table as symtab;

pub(crate) struct Impls {
    pub(crate) for_type: HashMap<NameID, (Vec<DirectImpl>, Vec<TraitImpl>)>,
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

pub(crate) fn gather_impls(
    module_ast: &Loc<ast::ModuleBody>,
    impls: &mut Impls,
    ctx: &mut spade_ast_lowering::Context,
) -> Result<(), Diagnostic> {
    for item in &module_ast.members {
        match item {
            ast::Item::Unit(_) => {}
            ast::Item::TraitDef(_) => {}
            ast::Item::ImplBlock(block) => {
                // Parts of this are stolen from `spade_ast_lowering::visit_impl_inner`

                // This adds the generics to the symtab
                let _ = spade_ast_lowering::visit_type_params(&block.type_params, ctx)?;

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
            ast::Item::Type(_) => {}
            ast::Item::ExternalMod(_) => {}
            ast::Item::Module(m) => {
                ctx.symtab
                    .push_namespace(PathSegment::Named(m.name.clone()));
                if let Err(e) = gather_impls(&m.body, impls, ctx) {
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
