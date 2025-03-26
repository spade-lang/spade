use spade_ast as ast;
use spade_common::location_info::WithLocation;
use spade_common::name::Identifier;
use spade_common::name::Path;
use spade_hir as hir;

use crate::global_symbols::re_visit_type_declaration;
use crate::global_symbols::visit_type_declaration;
use crate::impls::visit_impl;
use crate::Context;
use crate::Result;

/*
```spade
fn (a, b, c) {}

struct Lambda {}

impl<A, B, C, O> Fn<(A, B, C), O> for Lambda {
    fn call(self, args: (A, B, C)) -> O {
        let (a, b, c) = args;
        // Pasted body
    }
}
```
*/

pub fn visit_lambda(e: &ast::Expression, ctx: &mut Context) -> Result<hir::ExprKind> {
    let ast::Expression::Lambda {
        unit_kind,
        args,
        body,
    } = &e
    else {
        panic!("visit_lambda called with non-lambda");
    };

    let loc = ().between_locs(unit_kind, body);

    let type_name = Identifier(format!("Lambda"));
    let type_decl = ast::TypeDeclaration {
        name: type_name.clone().at_loc(&loc),
        kind: spade_ast::TypeDeclKind::Struct(
            ast::Struct {
                attributes: ast::AttributeList::empty(),
                name: type_name.clone().at_loc(&loc),
                members: ast::ParameterList::without_self(vec![]).at_loc(&loc),
                port_keyword: None,
            }
            .at_loc(&loc),
        ),
        generic_args: None,
    }
    .at_loc(&loc);

    visit_type_declaration(&type_decl, ctx)?;
    re_visit_type_declaration(&type_decl, ctx)?;
    // TODO: Commented out code
    // let type_nameid = ctx.symtab.add_type(
    //     Path::ident(type_name.clone().at_loc(&loc)),
    //     TypeSymbol::Declared(
    //         vec![],
    //         spade_hir::symbol_table::TypeDeclKind::Struct { is_port: false },
    //     )
    //     .at_loc(&loc),
    // );
    // let type_callable_namid = ctx.symtab.add_thing(
    //     Path::ident(type_name.clone().at_loc(&loc)),
    //     spade_hir::symbol_table::Thing::Struct(
    //         StructCallable {
    //             name: type_name.clone().nowhere(),
    //             self_type: hir::TypeSpec::Declared(type_nameid.clone().at_loc(&loc), vec![])
    //                 .at_loc(&loc),
    //             params: hir::ParameterList(vec![]).at_loc(&loc),
    //             type_params: vec![],
    //         }
    //         .at_loc(&loc),
    //     ),
    // );

    let output_type_name = Identifier("Output".to_string());
    let type_params = args
        .iter()
        .map(|arg| {
            ast::TypeParam::TypeName {
                name: arg.clone(),
                traits: vec![],
            }
            .at_loc(arg)
        })
        .chain(
            [ast::TypeParam::TypeName {
                name: output_type_name.clone().nowhere(),
                traits: vec![],
            }
            .nowhere()]
            .into_iter(),
        )
        .collect::<Vec<_>>()
        .at_loc(&loc);

    let args_spec = ast::TypeSpec::Tuple(
        args.iter()
            .map(|arg| {
                ast::TypeExpression::TypeSpec(Box::new(
                    ast::TypeSpec::Named(Path::ident(arg.clone()).at_loc(arg), None).nowhere(),
                ))
                .at_loc(arg)
            })
            .collect::<Vec<_>>(),
    )
    .nowhere();

    let mut new_body = body.inner.clone();

    // TODO: Error if there is no output in the body, maybe

    new_body.statements = vec![ast::Statement::binding(
        ast::Pattern::Tuple(
            args.iter()
                .map(|arg| ast::Pattern::Path(Path::ident(arg.clone()).nowhere()).nowhere())
                .collect(),
        )
        .nowhere(),
        None,
        ast::Expression::Identifier(
            Path::ident(Identifier("args".to_string()).nowhere()).nowhere(),
        )
        .nowhere(),
    )
    .nowhere()];

    let impl_block = ast::ImplBlock {
        r#trait: Some(
            ast::TraitSpec {
                path: Path::from_strs(&["Fn"]).nowhere(),
                type_params: Some(
                    vec![
                        ast::TypeExpression::TypeSpec(Box::new(args_spec.clone())).nowhere(),
                        ast::TypeExpression::TypeSpec(Box::new(
                            ast::TypeSpec::Named(
                                Path::ident(output_type_name.clone().nowhere()).nowhere(),
                                None,
                            )
                            .nowhere(),
                        ))
                        .nowhere(),
                    ]
                    .nowhere(),
                ),
            }
            .at_loc(&loc),
        ),
        type_params: Some(type_params),
        where_clauses: vec![],
        target: ast::TypeSpec::Named(Path::ident(type_name.clone().nowhere()).nowhere(), None)
            .nowhere(),
        units: vec![ast::Unit {
            head: ast::UnitHead {
                extern_token: None,
                attributes: ast::AttributeList(vec![]),
                unit_kind: unit_kind.clone(),
                name: Identifier("call".to_string()).nowhere(),
                inputs: ast::ParameterList {
                    self_: Some(().nowhere()),
                    args: vec![(
                        ast::AttributeList(vec![]),
                        Identifier("args".to_string()).nowhere(),
                        args_spec,
                    )],
                }
                .nowhere(),
                output_type: Some((
                    ().nowhere(),
                    ast::TypeSpec::Named(Path::ident(output_type_name.nowhere()).nowhere(), None)
                        .nowhere(),
                )),
                type_params: None,
                where_clauses: vec![],
            },
            body: Some(ast::Expression::Block(Box::new(new_body)).at_loc(body)),
        }
        .at_loc(&loc)],
    };

    for item in visit_impl(&impl_block.at_loc(&loc), ctx)? {
        let u = item.assume_unit();
        ctx.item_list.add_executable(
            u.name.name_id().clone(),
            hir::ExecutableItem::Unit(u.clone().at_loc(&loc)),
        )?;
    }

    let (callee, _) = ctx
        .symtab
        .lookup_struct(&Path::ident(type_name.at_loc(&loc)).at_loc(&loc))?;
    Ok(hir::ExprKind::Call {
        kind: spade_hir::expression::CallKind::Function,
        callee: callee.at_loc(&loc),
        args: hir::ArgumentList::Positional(vec![]).at_loc(&loc),
        turbofish: None,
    })
}
