use spade_common::location_info::{Loc, WithLocation};
use spade_diagnostics::diag_bail;
use spade_hir::{
    domains::DomainName, pretty_debug::PrettyDebug, Binding, Expression, Parameter, Pattern,
    PatternArgument, Statement, Unit,
};
use spade_typeinference::equation::TypeVarID;

use crate::{
    domain_var::LocExt, tracing::TraceEntry, DomainState, DomainVar, DomainedExpression, HasDomain,
    Result, TypeVarIDExt,
};

impl DomainState {
    pub fn visit_unit(&mut self, unit: &Loc<Unit>) -> Result<()> {
        let _t = self.trace_scope(|| TraceEntry::VisitingUnit(unit.name.to_string()));

        for domain in &unit.head.domains {
            let var = self.add_domain_var(DomainVar::Known(
                domain.name.clone(),
                domain.constraints.clone(),
            ));
            let name = match &domain.name {
                DomainName::Annonymous => DomainedExpression::AnnonymousOuter(unit.head.name.loc()),
                DomainName::Named(name) => DomainedExpression::Name(name.inner.clone()),
            };
            self.equations.insert(name, var);
        }

        for (
            Parameter {
                no_mangle: _,
                name: _,
                ty: _,
                domain,
                field_translator: _,
            },
            (name_id, _),
        ) in unit.head.inputs.0.iter().zip(unit.inputs.iter())
        {
            let dexpr = match &domain {
                DomainName::Annonymous => DomainedExpression::AnnonymousOuter(unit.head.name.loc()),
                DomainName::Named(name) => DomainedExpression::Name(name.inner.clone()),
            };

            dexpr
                .get_domain(self)
                .insert_for_domained(DomainedExpression::Name(name_id.inner.clone()), self);
        }

        let output_domain = match &unit.head.output_type {
            Some((DomainName::Annonymous, _)) => {
                DomainedExpression::AnnonymousOuter(unit.head.name.loc())
            }
            Some((DomainName::Named(name), _)) => DomainedExpression::Name(name.inner.clone()),
            None => {
                // TODO: This is not right, but i'm also not sure how to handle the unit type
                // here
                DomainedExpression::AnnonymousOuter(unit.head.name.loc())
            }
        }
        .get_domain(self);

        // TODO: That Loc is all wrong
        self.check_expression(&unit.body, output_domain.at_loc(&unit.head.name.loc()))?;
        Ok(())
    }

    fn visit_statement(&mut self, stmt: &Loc<Statement>) -> Result<()> {
        let _t = self.trace_scope(|| TraceEntry::VisitingStatement(stmt.pretty_debug()));

        match &stmt.inner {
            Statement::Error => Ok(()),
            Statement::Binding(Binding {
                pattern,
                ty: _,
                value,
                wal_trace: _,
            }) => {
                let pattern_ty = self.synth_pattern(pattern)?;
                self.check_expression(value, pattern_ty.at_loc(pattern))?;

                Ok(())
            }
            Statement::Expression(expr) => {
                self.synth_expression(expr)?;
                Ok(())
            }
            Statement::Register(register) => todo!(),
            Statement::Declaration(locs) => todo!(),
            Statement::PipelineRegMarker(pipeline_reg_marker_extra) => todo!(),
            Statement::Label(loc) => todo!(),
            Statement::Assert(loc) => todo!(),
            Statement::Set { target, value } => todo!(),
            Statement::WalSuffixed { suffix, target } => todo!(),
        }
    }

    fn synth_pattern(&mut self, pattern: &Loc<Pattern>) -> Result<TypeVarID> {
        let _t = self.trace_scope(|| TraceEntry::SynthPattern(pattern.pretty_debug()));

        let result = match &pattern.inner.kind {
            spade_hir::PatternKind::Integer(_) | spade_hir::PatternKind::Bool(_) => self.new_any(),
            spade_hir::PatternKind::Name { name, pre_declared } => {
                if *pre_declared {
                    // We don't place additional constraints on this with a pattern, but we do
                    // need to lookup the name
                    name.get_domain(self)
                } else {
                    let var_id = self.new_any();
                    var_id.insert_for_domained(DomainedExpression::Name(name.inner.clone()), self);
                    var_id
                }
            }
            spade_hir::PatternKind::Tuple(members) | spade_hir::PatternKind::Array(members) => {
                if members.is_empty() {
                    self.new_any()
                } else {
                    let first_domain = self.synth_pattern(&members[0])?;
                    for member in &members[1..] {
                        self.check_pattern(member, first_domain.at_loc(&members[0]))?;
                    }
                    first_domain
                }
            }
            spade_hir::PatternKind::Type(_, args) => {
                if args.is_empty() {
                    self.new_any()
                } else {
                    let first_domain = self.synth_pattern(&args[0].value)?;
                    for PatternArgument {
                        target: _,
                        value,
                        kind: _,
                    } in &args[1..]
                    {
                        self.check_pattern(value, first_domain.at_loc(&args[0].value))?;
                    }
                    first_domain
                }
            }
        };

        result.insert_for_domained(DomainedExpression::Id(pattern.id), self);
        Ok(result)
    }

    fn check_pattern(&mut self, pattern: &Loc<Pattern>, expected: Loc<TypeVarID>) -> Result<()> {
        let _t = self.trace_scope(|| TraceEntry::CheckPattern(pattern.pretty_debug()));
        // All patterns have a synthesizeable type if we look hard enough
        let inner = self.synth_pattern(pattern)?;

        // NOTE: There is a potential for optimization here if we don't merge vars that are
        // the same
        let merged = inner
            .resolve_domain(self)
            .at_loc(pattern)
            .merge_domains(&expected.map(|d| d.resolve_domain(self)))?;

        let merged_id = self.add_domain_var(merged);

        self.replace(expected.inner, merged_id);
        self.replace(inner, merged_id);

        Ok(())
    }

    fn synth_expression(&mut self, expr: &Loc<Expression>) -> Result<TypeVarID> {
        let _t = self.trace_scope(|| TraceEntry::SynthExpr(expr.pretty_debug()));
        let result = match &expr.inner.kind {
            spade_hir::ExprKind::Error => Ok(self.error_domain.unwrap()),
            spade_hir::ExprKind::Identifier(name) => Ok(name.get_domain(self)),
            spade_hir::ExprKind::PipelineRef {
                stage: _,
                name,
                declares_name: _,
                depth_typeexpr_id: _,
            } => Ok(name.get_domain(self)),
            spade_hir::ExprKind::TupleLiteral(members) => {
                // If there are no members, we can be in any domain
                if members.is_empty() {
                    Ok(self.new_any())
                } else {
                    let inner_domain = self.synth_expression(&members[0])?;
                    for member in &members[1..] {
                        self.check_expression(member, inner_domain.at_loc(&members[0]))
                            .map_err(|e| e.help("All tuple members must be in the same domain"))?;
                    }

                    Ok(inner_domain)
                }
            }
            spade_hir::ExprKind::ArrayLiteral(members) => {
                // If there are no members, we can be in any domain
                if members.is_empty() {
                    Ok(self.new_any())
                } else {
                    let inner_domain = self.synth_expression(&members[0])?;
                    for member in &members[1..] {
                        self.check_expression(member, inner_domain.at_loc(&members[0]))
                            .map_err(|e| e.help("All array members must be in the same domain"))?;
                    }

                    Ok(inner_domain)
                }
            }
            spade_hir::ExprKind::ArrayShorthandLiteral(inner, _) => self.synth_expression(inner),
            spade_hir::ExprKind::IntLiteral(_, _)
            | spade_hir::ExprKind::BoolLiteral(_)
            | spade_hir::ExprKind::BitLiteral(_)
            | spade_hir::ExprKind::TypeLevelInteger(_)
            | spade_hir::ExprKind::CreatePorts => Ok(self.new_any()),

            // For items whose domain depends on sub-expressions, we can synthesize those
            spade_hir::ExprKind::Index(op, _)
            | spade_hir::ExprKind::RangeIndex { target: op, .. }
            | spade_hir::ExprKind::TupleIndex(op, _)
            | spade_hir::ExprKind::UnaryOperator(_, op)
            | spade_hir::ExprKind::FieldAccess(op, _) => self.synth_expression(op),

            spade_hir::ExprKind::BinaryOperator(opa, _, opb) => {
                let expected = self.synth_expression(opa)?;
                self.check_expression(opb, expected.at_loc(opb))?;
                Ok(expected)
            }

            // If we're in synthesis mode and find expressions which need checking,
            // we can return any since we can always fall back on the annonymous domain
            spade_hir::ExprKind::Call {
                kind,
                callee,
                args,
                turbofish,
                safety,
            } => todo!(),

            spade_hir::ExprKind::Match(loc, items) => todo!(),
            spade_hir::ExprKind::Block(block) => todo!(),
            spade_hir::ExprKind::If(loc, loc1, loc2) => todo!(),
            spade_hir::ExprKind::TypeLevelIf(loc, loc1, loc2) => todo!(),
            spade_hir::ExprKind::StageValid => todo!(),
            spade_hir::ExprKind::StageReady => todo!(),
            spade_hir::ExprKind::StaticUnreachable(loc) => todo!(),
            spade_hir::ExprKind::Null => todo!(),

            spade_hir::ExprKind::MethodCall { .. } => {
                diag_bail!(expr, "Method should be lowered already")
            }
            spade_hir::ExprKind::LambdaDef { .. } => {
                diag_bail!(expr, "Lambda should be lowered already")
            }
        }?;
        result.insert_for_domained(DomainedExpression::Id(expr.id), self);
        Ok(result)
    }

    fn check_expression(&mut self, expr: &Loc<Expression>, expected: Loc<TypeVarID>) -> Result<()> {
        let _t = self.trace_scope(|| TraceEntry::CheckExpr {
            expr: expr.inner.clone(),
            expected: expected.resolve_domain(self).clone(),
        });
        let self_domain = match &expr.inner.kind {
            // TODO: Verify that this is correrct
            spade_hir::ExprKind::Error => Ok(self.error_domain.unwrap()),
            // TODO: This smells a whole lot like synthesis in the check function hmmmm
            spade_hir::ExprKind::Identifier(_) |
            // Pipeline refs are just spicy identifiers
            // NOTE: This only holds until pipelines get upgraded to domains
            spade_hir::ExprKind::PipelineRef {
                stage: _,
                name: _,
                declares_name: _,
                depth_typeexpr_id: _,
            } => self.synth_expression(expr),

            // Literals can be in any domain, so check cannot fail
            spade_hir::ExprKind::IntLiteral(_, _)
            | spade_hir::ExprKind::BoolLiteral(_)
            | spade_hir::ExprKind::BitLiteral(_)
            | spade_hir::ExprKind::TypeLevelInteger(_)
            | spade_hir::ExprKind::CreatePorts |

            // Constructors of stuff end up in the same domain as their constituent parts,
            // if they match, otherwise there is an error
            spade_hir::ExprKind::TupleLiteral(_) |
            spade_hir::ExprKind::ArrayLiteral(_) |
            spade_hir::ExprKind::ArrayShorthandLiteral(_, _) => self.synth_expression(expr),

            // TLif diverges depending on the branch taken in this function call. We need
            // a type state to be available for this
            spade_hir::ExprKind::TypeLevelIf(loc, loc1, loc2) => todo!(),

            // Operators and friends have to have the same domain on all branches. We'll group
            // these based on their arity
            spade_hir::ExprKind::Index(opa, opb) |
            spade_hir::ExprKind::BinaryOperator(opa, _, opb) => {
                self.synth_expression(expr)
            },

            spade_hir::ExprKind::UnaryOperator(_, op) |
            spade_hir::ExprKind::FieldAccess(op, _) |
            spade_hir::ExprKind::TupleIndex(op, _) |
            spade_hir::ExprKind::RangeIndex { target: op, start: _, end: _ } => {
                self.synth_expression(op)
            },

            spade_hir::ExprKind::Match(loc, items) => todo!(),
            spade_hir::ExprKind::If(loc, loc1, loc2) => todo!(),

            // Functions are special and will need special treatment
            spade_hir::ExprKind::Call {
                kind,
                callee,
                args,
                turbofish,
                safety,
            } => todo!(),
            // Visit the statements, then ensure that the result has the same type as the result
            spade_hir::ExprKind::Block(block) => {
                for statement in &block.statements {
                    self.visit_statement(&statement)?;
                }
                if let Some(result) = &block.result {
                    self.check_expression(&result, expected)?;
                }
                // TODO: This feels weird, am I sure we should re-check checked results?
                Ok(expected.inner)
            },

            // These have teh same domain as the pipeline
            spade_hir::ExprKind::StageValid => todo!(),
            spade_hir::ExprKind::StageReady => todo!(),

            // Weird expressions
            spade_hir::ExprKind::StaticUnreachable(loc) => todo!(),
            spade_hir::ExprKind::Null => todo!(),

            spade_hir::ExprKind::MethodCall { .. } => {
                diag_bail!(expr, "Method should be lowered already")
            }
            spade_hir::ExprKind::LambdaDef { .. } => {
                diag_bail!(expr, "Lambda should be lowered already")
            }
        };

        let self_domain = self_domain?;

        // NOTE: There is a potential for optimization here if we don't merge vars that are
        // the same
        let merged = self_domain
            .resolve_domain(self)
            .at_loc(expr)
            .merge_domains(&expected.map(|d| d.resolve_domain(self)))?;

        let merged_id = self.add_domain_var(merged);

        self.replace(expected.inner, merged_id);
        self.replace(self_domain, merged_id);

        Ok(())
    }
}
