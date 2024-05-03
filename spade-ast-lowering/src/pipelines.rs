use num::ToPrimitive;
use spade_ast as ast;
use spade_common::{location_info::Loc, name::Identifier};
use spade_diagnostics::Diagnostic;
use spade_hir as hir;

use crate::{comptime::ComptimeCondExt, error::Result, Context};

pub fn int_literal_to_pipeline_stages(depth: &Loc<ast::IntLiteral>) -> Result<Loc<usize>> {
    depth
        .try_map_ref(|u| {
            u.clone().as_unsigned().ok_or_else(|| {
                Diagnostic::error(depth, "Negative depth")
                    .primary_label("Expected non-negative depth")
            })
        })?
        .try_map_ref(|u| {
            u.clone().to_usize().ok_or_else(|| {
                Diagnostic::bug(depth, "Too many pipeline stages").primary_label(format!(
                    "At most {} pipeline stages are supported",
                    usize::MAX
                ))
            })
        })
}

pub struct PipelineContext {
    /// All stages within the pipeline, possibly labelled
    pub stages: Vec<Option<Loc<Identifier>>>,
    /// The stage we are currently lowering
    pub current_stage: usize,
}

impl PipelineContext {
    pub fn get_stage(&self, name: &Identifier) -> Option<usize> {
        for (i, stage_name) in self.stages.iter().enumerate() {
            if stage_name.as_ref().map(|n| &n.inner) == Some(name) {
                return Some(i);
            }
        }
        None
    }

    /// Returns the location of the previous definition of stage `name` if such
    /// a definition exists
    pub fn previous_def(&self, name: &Identifier) -> Option<Loc<Identifier>> {
        for stage_name in &self.stages {
            if stage_name.as_ref().map(|n| &n.inner) == Some(name) {
                return stage_name.clone();
            }
        }
        None
    }
}

fn visit_pipeline_statement(
    statement: &ast::Statement,
    current_stage: &mut usize,
    ctx: &mut Context,
    pipeline_ctx: &mut PipelineContext,
) -> Result<()> {
    match &statement {
        ast::Statement::Label(name) => {
            if let Some(previous) = &pipeline_ctx.stages[*current_stage] {
                // FIXME: We might actually want to support multiple labels
                // for the same stage... If so we need to rewrite
                // some other parts
                return Err(
                    Diagnostic::error(name, "Multiple labels for the same stage")
                        .primary_label("This stage has already been labeled")
                        .secondary_label(previous, "Previously labeled here"),
                );
            }

            if let Some(prev) = pipeline_ctx.previous_def(name) {
                return Err(Diagnostic::error(name, "Stage was already defined")
                    .primary_label(format!("'{} has already been defined", name))
                    .secondary_label(prev, "Previously defined here"));
            }
            pipeline_ctx.stages[*current_stage] = Some(name.clone());
        }
        ast::Statement::Declaration(_) => {}
        ast::Statement::Binding(_) => {}
        ast::Statement::PipelineRegMarker(count, _) => {
            for _ in 0..count.map(|v| v.inner).unwrap_or(1) {
                *current_stage += 1;
                pipeline_ctx.stages.push(None)
            }
        }
        ast::Statement::Register(_) => {}
        ast::Statement::Assert(_) => {}
        ast::Statement::Comptime(inner) => {
            if let Some(inner_stmts) = inner.maybe_unpack(&ctx.symtab)? {
                for inner_stmt in inner_stmts {
                    visit_pipeline_statement(&inner_stmt, current_stage, ctx, pipeline_ctx)?;
                }
            }
        }
        ast::Statement::Set { .. } => {}
        ast::Statement::ForLoop { .. } => {}
        ast::Statement::Yield(_) => {}
    };
    Ok(())
}

pub fn maybe_perform_pipelining_tasks(
    unit: &Loc<ast::Unit>,
    head: &Loc<hir::UnitHead>,
    ctx: &mut Context,
) -> Result<Option<PipelineContext>> {
    let ast::Unit {
        head:
            ast::UnitHead {
                unit_kind,
                inputs: ast_inputs,
                ..
            },
        body,
    } = &unit.inner;

    match &unit_kind.inner {
        ast::UnitKind::Function => Ok(None),
        ast::UnitKind::Entity => Ok(None),
        ast::UnitKind::Pipeline(depth) => {
            let depth = depth.maybe_unpack(&ctx.symtab)?.ok_or_else(|| {
                Diagnostic::error(depth, "Missing depth")
                    .note("The current comptime branch does not specify a depth")
            })?;

            if head.inputs.0.is_empty() {
                return Err(Diagnostic::error(
                    ast_inputs.loc(),
                    "Missing clock argument for pipeline",
                )
                .note("All pipelines need to take at least a clock as an argument"));
            }

            let mut context = PipelineContext {
                stages: vec![None],
                current_stage: 0,
            };

            let body = body.as_ref().unwrap();

            let mut current_stage = 0;
            for statement in &body.assume_block().statements {
                visit_pipeline_statement(statement, &mut current_stage, ctx, &mut context)?;
            }

            let depth = int_literal_to_pipeline_stages(&depth)?;
            if current_stage != depth.inner {
                let stage_str = format!("{current_stage}");
                return Err(Diagnostic::error(body, "Wrong number of pipeline stages")
                    .primary_label(format!(
                        "Found {} stage{} here",
                        if current_stage == 0 { "no" } else { &stage_str },
                        if current_stage <= 1 { "" } else { "s" }
                    ))
                    .secondary_label(
                        depth,
                        format!(
                            "{} stage{} specified here",
                            depth,
                            if depth.inner == 1 { "" } else { "s" }
                        ),
                    ));
            }

            Ok(Some(context))
        }
    }
}

#[cfg(test)]
mod pipeline_visiting {
    use crate::{visit_unit, SelfContext};

    use super::*;

    use ast::comptime::MaybeComptime;
    use hir::symbol_table::SymbolTable;
    use spade_ast::testutil::ast_ident;
    use spade_common::{
        id_tracker::{ExprIdTracker, ImplIdTracker},
        location_info::WithLocation,
        name::testutil::name_id,
        num_ext::InfallibleToBigInt,
    };

    use pretty_assertions::assert_eq;

    #[test]
    fn relative_stage_references_work() {
        let input = ast::Unit {
            head: ast::UnitHead {
                name: ast_ident("pipe"),
                unit_kind: ast::UnitKind::Pipeline(
                    MaybeComptime::Raw(ast::IntLiteral::Signed(2.to_bigint()).nowhere()).nowhere(),
                )
                .nowhere(),
                inputs: ast::ParameterList::without_self(vec![(
                    ast_ident("clk"),
                    ast::TypeSpec::Unit(().nowhere()).nowhere(),
                )])
                .nowhere(),
                output_type: Some(ast::TypeSpec::Unit(().nowhere()).nowhere()),
                type_params: vec![],
                attributes: ast::AttributeList(vec![]),
            },
            body: Some(
                ast::Expression::Block(Box::new(ast::Block {
                    statements: vec![
                        ast::Statement::PipelineRegMarker(Some(1.nowhere()), None).nowhere(),
                        ast::Statement::binding(
                            ast::Pattern::name("a"),
                            None,
                            ast::Expression::int_literal_signed(0).nowhere(),
                        )
                        .nowhere(),
                        ast::Statement::PipelineRegMarker(Some(1.nowhere()), None).nowhere(),
                        ast::Statement::binding(
                            ast::Pattern::name("b"),
                            None,
                            ast::Expression::PipelineReference {
                                stage_kw_and_reference_loc: ().nowhere(),
                                stage: ast::PipelineStageReference::Relative(
                                    (-1).to_bigint().nowhere(),
                                ),
                                name: ast_ident("a"),
                            }
                            .nowhere(),
                        )
                        .nowhere(),
                    ],
                    result: Some(ast::Expression::int_literal_signed(0).nowhere()),
                }))
                .nowhere(),
            ),
        }
        .nowhere();

        let expected_statements = vec![
            hir::Statement::PipelineRegMarker(None).nowhere(),
            hir::Statement::named_let(
                2,
                name_id(2, "a"),
                hir::ExprKind::IntLiteral(0.to_bigint()).with_id(3),
            )
            .nowhere(),
            hir::Statement::PipelineRegMarker(None).nowhere(),
            hir::Statement::named_let(
                4,
                name_id(3, "b"),
                hir::ExprKind::PipelineRef {
                    stage: 1usize.nowhere(),
                    name: name_id(2, "a"),
                    declares_name: false,
                }
                .idless(),
            )
            .nowhere(),
        ];

        let mut symtab = SymbolTable::new();
        let idtracker = ExprIdTracker::new();

        crate::global_symbols::visit_unit(&None, &input, &mut symtab, &SelfContext::FreeStanding)
            .expect("Failed to add pipeline to symtab");

        let result = visit_unit(
            None,
            &input,
            &mut Context {
                symtab,
                idtracker,
                impl_idtracker: ImplIdTracker::new(),
                pipeline_ctx: None,
            },
        );

        assert_eq!(
            result.unwrap().assume_unit().body.assume_block().statements,
            expected_statements
        );
    }

    #[test]
    fn absolute_stage_references_work() {
        let input = ast::Unit {
            head: ast::UnitHead {
                name: ast_ident("pipe"),
                unit_kind: ast::UnitKind::Pipeline(
                    MaybeComptime::Raw(ast::IntLiteral::Signed(2.to_bigint()).nowhere()).nowhere(),
                )
                .nowhere(),
                inputs: ast::ParameterList::without_self(vec![(
                    ast_ident("clk"),
                    ast::TypeSpec::Unit(().nowhere()).nowhere(),
                )])
                .nowhere(),
                output_type: Some(ast::TypeSpec::Unit(().nowhere()).nowhere()),
                type_params: vec![],
                attributes: ast::AttributeList(vec![]),
            },
            body: Some(
                ast::Expression::Block(Box::new(ast::Block {
                    statements: vec![
                        ast::Statement::PipelineRegMarker(Some(1.nowhere()), None).nowhere(),
                        ast::Statement::Label(ast_ident("s")).nowhere(),
                        ast::Statement::binding(
                            ast::Pattern::name("a"),
                            None,
                            ast::Expression::int_literal_signed(0).nowhere(),
                        )
                        .nowhere(),
                        ast::Statement::PipelineRegMarker(Some(1.nowhere()), None).nowhere(),
                        ast::Statement::binding(
                            ast::Pattern::name("b"),
                            None,
                            ast::Expression::PipelineReference {
                                stage_kw_and_reference_loc: ().nowhere(),
                                stage: ast::PipelineStageReference::Absolute(ast_ident("s")),
                                name: ast_ident("a"),
                            }
                            .nowhere(),
                        )
                        .nowhere(),
                    ],
                    result: Some(ast::Expression::int_literal_signed(0).nowhere()),
                }))
                .nowhere(),
            ),
        }
        .nowhere();

        let expected_statements = vec![
            hir::Statement::PipelineRegMarker(None).nowhere(),
            hir::Statement::Label(ast_ident("s")).nowhere(),
            hir::Statement::named_let(
                2,
                name_id(2, "a"),
                hir::ExprKind::IntLiteral(0.to_bigint()).with_id(3),
            )
            .nowhere(),
            hir::Statement::PipelineRegMarker(None).nowhere(),
            hir::Statement::named_let(
                4,
                name_id(3, "b"),
                hir::ExprKind::PipelineRef {
                    stage: 1usize.nowhere(),
                    name: name_id(2, "a"),
                    declares_name: false,
                }
                .idless(),
            )
            .nowhere(),
        ];

        let mut symtab = SymbolTable::new();
        let idtracker = ExprIdTracker::new();

        crate::global_symbols::visit_unit(&None, &input, &mut symtab, &SelfContext::FreeStanding)
            .expect("Failed to add pipeline to symtab");

        let result = visit_unit(
            None,
            &input,
            &mut Context {
                symtab,
                idtracker,
                impl_idtracker: ImplIdTracker::new(),
                pipeline_ctx: None,
            },
        );

        assert_eq!(
            result.unwrap().assume_unit().body.assume_block().statements,
            expected_statements
        );
    }
}
