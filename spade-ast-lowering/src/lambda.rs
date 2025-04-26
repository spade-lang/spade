use spade_ast as ast;
use spade_common::location_info::WithLocation;
use spade_common::name::Identifier;
use spade_common::name::Path;
use spade_diagnostics::diag_bail;
use spade_hir as hir;

use crate::global_symbols::re_visit_type_declaration;
use crate::global_symbols::visit_type_declaration;
use crate::impls::visit_impl;
use crate::visit_block;
use crate::visit_pattern;
use crate::Context;
use crate::LocExt;
use crate::Result;

/*

ast lowering:
- Add a type for the lambda
    - Mono needs this type to be as generic as its context generic
        - Function generics
        - Impl block generics
    - Add an impl block for `Fn<...>`
        impl Fn<(Args), Output> for LambdaT {
            fn call(self, args: Args) -> Output {
                ... placeholder
            }
        }

- Typechecking
    - Typecheck the body as if it were inline

- Post mono
    - Replace lambda body placeholders

```spade
fn (a, b, c) {/* body */} =>  {LambdaDef<A, B, C, D>(), /* body */}

// These are added
struct Lambda<A, B, C, O> {}

impl<A, B, C, O> Fn<(A, B, C), O> for Lambda<A, B, C, O> {
    fn call(self, args: (A, B, C)) -> O {
        // placeholder
    }
}

// After typechecking we replace the placeholder body with the actual body

```
*/

// TODO: Prevent captures

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
    let output_type_name = Identifier("Output".to_string());

    let generic_param_names = args
        .iter()
        .enumerate()
        .map(|(i, arg)| Identifier(format!("A{i}")).at_loc(arg))
        .chain(vec![output_type_name.clone().nowhere()])
        .collect::<Vec<_>>();

    let type_params = generic_param_names
        .iter()
        .map(|name| {
            ast::TypeParam::TypeName {
                name: name.clone(),
                traits: vec![],
            }
            .at_loc(name)
        })
        .collect::<Vec<_>>()
        .at_loc(&loc);

    let args_spec = ast::TypeSpec::Tuple(
        args.iter()
            .enumerate()
            .map(|(i, arg)| {
                ast::TypeExpression::TypeSpec(Box::new(
                    ast::TypeSpec::Named(
                        Path::ident(Identifier(format!("A{i}")).at_loc(arg)).at_loc(arg),
                        None,
                    )
                    .nowhere(),
                ))
                .at_loc(arg)
            })
            .collect::<Vec<_>>(),
    )
    .nowhere();

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
        generic_args: Some(type_params.clone()),
    }
    .at_loc(&loc);

    visit_type_declaration(&type_decl, ctx)?;
    re_visit_type_declaration(&type_decl, ctx)?;

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
        target: ast::TypeSpec::Named(
            Path::ident(type_name.clone().nowhere()).nowhere(),
            Some(
                generic_param_names
                    .iter()
                    .map(|name| {
                        ast::TypeExpression::TypeSpec(Box::new(
                            ast::TypeSpec::Named(Path::ident(name.clone()).at_loc(name), None)
                                .at_loc(name),
                        ))
                        .at_loc(name)
                    })
                    .collect::<Vec<_>>()
                    .nowhere(),
            ),
        )
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
            body: Some(
                ast::Expression::Block(Box::new(ast::Block {
                    statements: vec![],
                    result: Some(
                        ast::Expression::StaticUnreachable(
                            "Compiler bug: Lambda body was not lowered during monomorphization"
                                .to_string()
                                .at_loc(body),
                        )
                        .at_loc(body),
                    ),
                }))
                .at_loc(body),
            ),
        }
        .at_loc(&loc)],
    };

    let lambda_unit = match visit_impl(&impl_block.at_loc(&loc), ctx)?.as_slice() {
        [item] => {
            let u = item.assume_unit();
            ctx.item_list.add_executable(
                u.name.name_id().clone(),
                hir::ExecutableItem::Unit(u.clone().at_loc(&loc)),
            )?;
            u.name.name_id().clone()
        }
        _ => diag_bail!(loc, "Lambda impl block produced more than one item"),
    };

    let (callee_name, callee_struct) = ctx
        .symtab
        .lookup_struct(&Path::ident(type_name.at_loc(&loc)).at_loc(&loc))?;

    ctx.symtab.new_scope();
    let arguments = args
        .iter()
        .map(|arg| arg.try_visit(visit_pattern, ctx))
        .collect::<Result<Vec<_>>>()?;
    let body = body.try_map_ref(|body| visit_block(body, ctx));
    ctx.symtab.close_scope();
    let body = Box::new(
        body?.map(|body| hir::ExprKind::Block(Box::new(body)).with_id(ctx.idtracker.next())),
    );

    Ok(hir::ExprKind::LambdaDef {
        lambda_type: callee_name,
        lambda_type_params: callee_struct.type_params.clone(),
        lambda_unit: lambda_unit.inner,
        arguments,
        body,
    })
}
