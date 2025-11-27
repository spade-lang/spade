use std::sync::Arc;
use std::sync::Mutex;

use spade_ast as ast;
use spade_ast::testutil::ast_ident;
use spade_ast::UnitKind;
use spade_common::location_info::Loc;
use spade_common::location_info::WithLocation;
use spade_common::name::Identifier;
use spade_common::name::Path;
use spade_common::name::Visibility;
use spade_diagnostics::diag_anyhow;
use spade_diagnostics::diag_bail;
use spade_diagnostics::Diagnostic;
use spade_hir as hir;
use spade_hir::expression::LambdaTypeParams;
use spade_hir::expression::OuterLambdaParam;
use spade_types::meta_types::MetaType;

use crate::global_symbols::re_visit_type_declaration;
use crate::global_symbols::visit_type_declaration;
use crate::impls::visit_impl;
use crate::visit_block;
use crate::visit_pattern;
use crate::visit_unit_kind;
use crate::Context;
use crate::LocExt;
use crate::Result;

/*

ast lowering:
- Add a type for the lambda
    - Mono needs this type to be as generic as its context generic
        - Function generics
        - Impl block generics
    - Add an impl block for `Fn(...)`
        impl Fn(Args) -> Output for LambdaT {
            fn call(self, args: Args) -> Output {
                ... placeholder
            }
        }

- Typechecking
    - Typecheck the body as if it were inline

- Post mono
    - Replace lambda body placeholders

```spade
fn |a, b, c| {/* body */} =>  {LambdaDef<A, B, C, D>(), /* body */}

// These are added
struct Lambda<A, B, C, O> {}

impl<A, B, C, O> Fn(A, B, C) -> O for Lambda<A, B, C, O> {
    fn call(self, args: (A, B, C)) -> O {
        // placeholder
    }
}

// After typechecking we replace the placeholder body with the actual body

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

    let debug_loc = unit_kind.loc();
    let loc = ().between_locs(unit_kind, body);

    let type_name = Identifier::intern("Lambda");
    let output_type_name = Identifier::intern("Output");

    let current_unit = ctx.current_unit.clone().ok_or_else(|| {
        diag_anyhow!(loc, "Did not have a current_unit when visiting this lambda")
    })?;

    let (clock_arg, actual_args) = handle_unit_kind(unit_kind, args)?;

    let shared_captures = Arc::new(Mutex::new(vec![]));
    {
        let captures = shared_captures.clone();
        ctx.symtab
            .new_scope_with_barrier(Box::new(move |_name: _, previous, thing| match thing {
                spade_hir::symbol_table::Thing::Variable(name) => {
                    captures
                        .lock()
                        .unwrap()
                        .push((name.clone(), previous.clone()));
                    Ok(())
                }
                spade_hir::symbol_table::Thing::Struct(_)
                | spade_hir::symbol_table::Thing::EnumVariant(_)
                | spade_hir::symbol_table::Thing::Unit(_)
                | spade_hir::symbol_table::Thing::Alias {
                    path: _,
                    in_namespace: _,
                }
                | spade_hir::symbol_table::Thing::ArrayLabel(_)
                | spade_hir::symbol_table::Thing::Module(_)
                | spade_hir::symbol_table::Thing::Dummy
                | spade_hir::symbol_table::Thing::Trait(_) => Ok(()),
            }))
    };

    let clock = clock_arg
        .as_ref()
        .map(|(_, clk, _)| ctx.symtab.add_local_variable(clk.clone()).at_loc(&clk));
    let arguments = actual_args
        .iter()
        .map(|arg| arg.try_visit(visit_pattern, ctx))
        .collect::<Result<Vec<_>>>()?;
    let hir_body = body.try_map_ref(|body| visit_block(body, ctx));
    ctx.symtab.close_scope();
    let hir_body = Box::new(
        hir_body?.map(|body| hir::ExprKind::Block(Box::new(body)).with_id(ctx.idtracker.next())),
    );

    // Get rid of the mutex for more reasable code
    let mut captures = vec![];
    std::mem::swap(&mut *shared_captures.lock().unwrap(), &mut captures);

    let arg_generic_param_names = actual_args
        .iter()
        .enumerate()
        .map(|(i, arg)| Identifier::intern(&format!("A{i}")).at_loc(arg))
        .collect::<Vec<_>>();

    let output_generic_param_name = output_type_name.clone().at_loc(body);

    // Generic params of the environment in which the lambda is defined
    let outer_generic_params = current_unit
        .unit_type_params
        .iter()
        .chain(current_unit.scope_type_params.iter())
        .cloned()
        .collect::<Vec<_>>();

    // Generic params for all the captured variables
    let captured_value_generic_param_names = captures
        .iter()
        .enumerate()
        .map(|(i, cap)| Identifier::intern(&format!("C{i}")).at_loc(&cap.1));

    let manufactured_generic_params = arg_generic_param_names
        .clone()
        .into_iter()
        .chain(Some(output_generic_param_name.clone()))
        .chain(captured_value_generic_param_names.clone())
        .collect::<Vec<_>>();

    let all_generic_param_names = manufactured_generic_params
        .iter()
        .cloned()
        .chain(
            outer_generic_params
                .iter()
                .map(|p| p.name_id().1.tail().unwrap_named().inner.clone().at_loc(&p)),
        )
        .collect::<Vec<_>>();

    let type_params = manufactured_generic_params
        .iter()
        .map(|name| {
            ast::TypeParam::TypeName {
                name: name.clone(),
                traits: vec![],
            }
            .at_loc(name)
        })
        .chain(
            outer_generic_params
                .iter()
                .map(|tp| {
                    Ok(ast::TypeParam::TypeWithMeta {
                        // NOTE: Recreating the meta-type like this is kind of strange, but works for now. If we add more meta-types in the future, recondsider this decision
                        meta: match tp.meta {
                            MetaType::Int => Identifier::intern("int").at_loc(tp),
                            MetaType::Uint => Identifier::intern("uint").at_loc(tp),
                            MetaType::Bool => Identifier::intern("bool").at_loc(tp),
                            MetaType::Str => Identifier::intern("str").at_loc(tp),
                            MetaType::Type => Identifier::intern("type").at_loc(tp),
                            MetaType::Any | MetaType::Number => {
                                diag_bail!(loc, "Found unexpected meta in captured type args")
                            }
                        },
                        name: tp
                            .name_id()
                            .1
                            .tail()
                            .unwrap_named()
                            .inner
                            .clone()
                            .at_loc(tp),
                    }
                    .at_loc(tp))
                })
                .collect::<Result<Vec<_>>>()?
                .into_iter(),
        )
        .collect::<Vec<_>>()
        .at_loc(&debug_loc);

    let args_spec = ast::TypeSpec::Tuple(
        actual_args
            .iter()
            .enumerate()
            .map(|(i, arg)| {
                ast::TypeExpression::TypeSpec(Box::new(
                    ast::TypeSpec::Named(
                        Path::ident(Identifier::intern(&format!("A{i}")).at_loc(arg)).at_loc(arg),
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
        visibility: Visibility::Implicit.nowhere(),
        name: type_name.clone().at_loc(&debug_loc),
        kind: spade_ast::TypeDeclKind::Struct(
            ast::Struct {
                attributes: ast::AttributeList::empty(),
                name: type_name.clone().at_loc(&debug_loc),
                members: ast::ParameterList::without_self(
                    captures
                        .iter()
                        .enumerate()
                        .map(|(i, (name_ident, name_id))| {
                            let ty = ast::TypeSpec::Named(
                                Path::ident(Identifier::intern(&format!("C{i}")).at_loc(name_id))
                                    .at_loc(name_ident),
                                None,
                            )
                            .at_loc(name_id);

                            (ast::AttributeList::empty(), name_ident.clone(), ty)
                        })
                        .collect(),
                )
                .at_loc(&debug_loc),
                port_keyword: None,
            }
            .at_loc(&debug_loc),
        ),
        generic_args: Some(type_params.clone()),
    }
    .at_loc(&debug_loc);

    ctx.in_fresh_unit(|ctx| visit_type_declaration(&type_decl, ctx))?;
    ctx.in_fresh_unit(|ctx| re_visit_type_declaration(&type_decl, ctx))?;

    let impl_block = ast::ImplBlock {
        r#trait: Some(
            ast::TraitSpec {
                path: match &unit_kind.inner {
                    UnitKind::Function => Path::from_strs(&["Fn"]).at_loc(unit_kind),
                    UnitKind::Entity => Path::from_strs(&["Entity"]).at_loc(unit_kind),
                    UnitKind::Pipeline(_) => Path::from_strs(&["Pipeline"]).at_loc(unit_kind),
                },
                type_params: Some(
                    match &unit_kind.inner {
                        UnitKind::Function => vec![],
                        UnitKind::Entity => vec![],
                        UnitKind::Pipeline(depth) => vec![depth.clone()],
                    }
                    .into_iter()
                    .chain([
                        ast::TypeExpression::TypeSpec(Box::new(args_spec.clone())).nowhere(),
                        ast::TypeExpression::TypeSpec(Box::new(
                            ast::TypeSpec::Named(
                                Path::ident(output_type_name.clone().nowhere()).nowhere(),
                                None,
                            )
                            .nowhere(),
                        ))
                        .nowhere(),
                    ])
                    .collect::<Vec<_>>()
                    .nowhere(),
                ),
                paren_syntax: true,
            }
            .at_loc(&debug_loc),
        ),
        type_params: Some(type_params),
        where_clauses: vec![],
        target: ast::TypeSpec::Named(
            Path::ident(type_name.clone().nowhere()).nowhere(),
            Some(
                all_generic_param_names
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
                visibility: Visibility::Implicit.nowhere(),
                unsafe_token: None,
                extern_token: None,
                attributes: ast::AttributeList(vec![]),
                unit_kind: unit_kind.clone(),
                name: ast_ident("call"),
                inputs: ast::ParameterList {
                    self_: Some(ast::AttributeList::empty().nowhere()),
                    args: clock_arg
                        .clone()
                        .into_iter()
                        .chain([(ast::AttributeList(vec![]), ast_ident("args"), args_spec)])
                        .collect::<Vec<_>>(),
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
                    statements: match &unit_kind.inner {
                        UnitKind::Function => vec![],
                        UnitKind::Entity => vec![],
                        UnitKind::Pipeline(depth) => {
                            vec![ast::Statement::PipelineRegMarker(Some(depth.clone()), None)
                                .at_loc(body)]
                        }
                    },
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
        .at_loc(&debug_loc)],
    };

    let lambda_unit = ctx.in_fresh_unit(|ctx| {
        match &unit_kind.inner {
            UnitKind::Function => {}
            UnitKind::Entity => {}
            UnitKind::Pipeline(_) => {
                ctx.pipeline_ctx = Some(crate::pipelines::PipelineContext {
                    scope: ctx.symtab.current_scope(),
                })
            }
        };
        match visit_impl(&impl_block.at_loc(&debug_loc), ctx)?.as_slice() {
            [item] => {
                let u = item.assume_unit();
                ctx.item_list.add_executable(
                    u.name.name_id().clone(),
                    hir::ExecutableItem::Unit(u.clone().at_loc(&loc)),
                )?;

                Ok::<_, Diagnostic>(u.clone())
            }
            _ => diag_bail!(loc, "Lambda impl block produced more than one item"),
        }
    })?;

    // For the rest of the process, we need the HIR type params which we have to extract
    // from the HIR struct that was created earlier
    let (callee_name, callee_struct) = ctx
        .symtab
        .lookup_struct(&Path::ident(type_name.at_loc(&debug_loc)).at_loc(&debug_loc))?;
    let struct_type_params = callee_struct.type_params.clone();
    if struct_type_params.len() != all_generic_param_names.len() {
        diag_bail!(
            debug_loc,
            "Did not find the right number of type params in the struct created by this lambda"
        )
    }
    let struct_type_params = &mut struct_type_params.iter();
    let type_params = LambdaTypeParams {
        arg: struct_type_params
            .take(arg_generic_param_names.len())
            .cloned()
            .collect(),
        output: struct_type_params.take(1).next().unwrap().clone(),
        captures: struct_type_params
            .take(captured_value_generic_param_names.len())
            .cloned()
            .collect(),
        outer: struct_type_params
            .take(outer_generic_params.len())
            .cloned()
            .collect(),
    };

    Ok(hir::ExprKind::LambdaDef {
        unit_kind: visit_unit_kind(unit_kind, ctx)?.at_loc(unit_kind),
        lambda_type: callee_name,
        lambda_unit: lambda_unit.name.name_id().inner.clone(),
        captures,
        outer_generic_params: outer_generic_params
            .iter()
            // Kind of cursed, but we need to figure out what name IDs we gave to
            // the outer type params while visiting the unit so we can replace them later
            .zip(
                lambda_unit
                    .head
                    .scope_type_params
                    .iter()
                    .skip(manufactured_generic_params.len()),
            )
            .map(|(in_body, in_lambda)| OuterLambdaParam {
                name_in_lambda: in_lambda.name_id(),
                name_in_body: in_body.name_id().at_loc(in_body),
            })
            .collect(),
        type_params,
        arguments,
        body: hir_body,
        clock,
    })
}

fn handle_unit_kind(
    unit_kind: &Loc<UnitKind>,
    args: &Loc<Vec<Loc<ast::Pattern>>>,
) -> Result<(
    Option<(ast::AttributeList, Loc<Identifier>, Loc<ast::TypeSpec>)>,
    Vec<Loc<ast::Pattern>>,
)> {
    let result = match &unit_kind.inner {
        UnitKind::Function => (None, args.inner.clone()),
        UnitKind::Entity | UnitKind::Pipeline(_) => match args.as_slice() {
            [] => {
                return Err(
                    Diagnostic::error(args, "Non-function lambdas must take a clock.")
                        .primary_label("Expected a clock")
                        .secondary_label(unit_kind, "Required because this is not a `fn`")
                        .span_suggest_replace("Consider adding a clock", args, "(clk)"),
                )
            }
            [clock, rest @ ..] => match &clock.inner {
                spade_ast::Pattern::Path(p) => match p.inner.to_named_strs().as_slice() {
                    [Some("clk")] => (
                        Some((
                            ast::AttributeList(vec![]),
                            p.0.last().unwrap().unwrap_named().clone(),
                            ast::TypeSpec::Named(Path::from_strs(&["clock"]).at_loc(clock), None)
                                .at_loc(clock),
                        )),
                        rest.to_vec(),
                    ),
                    [_] => {
                        return Err(Diagnostic::error(
                            clock,
                            "The first argument of a non-function lambda must be called `clk`",
                        )
                        .primary_label("Expected `clk`")
                        .span_suggest_replace("Consider renaming the first argument", clock, "clk")
                        .span_suggest_insert_before(
                            "Or adding a adding a clock",
                            clock,
                            "clk, ",
                        ))
                    }
                    _ => {
                        return Err(Diagnostic::error(
                            clock,
                            "The first argument of a non-function lambda must be a clock",
                        )
                        .primary_label("Expected clock")
                        .span_suggest_insert_before(
                            "Consider adding a clock",
                            clock,
                            "clk, ",
                        ))
                    }
                },
                _ => {
                    return Err(Diagnostic::error(
                        clock,
                        "The first argument of a non-function lambda must be a clock",
                    )
                    .primary_label("Expected clock")
                    .span_suggest_insert_before(
                        "Consider adding a clock",
                        clock,
                        "clk, ",
                    ))
                }
            },
        },
    };
    Ok(result)
}
