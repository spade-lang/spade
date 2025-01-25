use spade_common::location_info::Loc;
use spade_hir::{Binding, ExprKind, Expression, PipelineRegMarkerExtra, Register, Statement, Unit};

use crate::Result;

pub trait Pass {
    fn visit_expression(&mut self, expression: &mut Loc<Expression>) -> Result<()>;
    /// Visit a statement, transforming it into a list of new statements which replace it. If the
    /// statement should be replaced Ok(Some(new...)) should be returned, if it should be kept,
    /// Ok(None) should be returned
    fn visit_statement(
        &mut self,
        _statement: &Loc<Statement>,
    ) -> Result<Option<Vec<Loc<Statement>>>> {
        Ok(None)
    }
    /// Perform transformations on the unit. This should not transform the body of the unit, that
    /// is handled by `visit_expression`
    fn visit_unit(&mut self, unit: &mut Unit) -> Result<()>;
}

pub trait Passable {
    /// Applies the pass to this HIR node. Children are visited before
    /// parents. Statements are visited in the order that they are defined
    fn apply(&mut self, pass: &mut dyn Pass) -> Result<()>;
}

impl Passable for Loc<Expression> {
    fn apply(&mut self, pass: &mut dyn Pass) -> Result<()> {
        macro_rules! subnodes {
            ($($node:expr),*) => {
                {$($node.apply(pass)?;)*}
            };
        }

        match &mut self.inner.kind {
            ExprKind::Identifier(_) => {}
            ExprKind::IntLiteral(_, _) => {}
            ExprKind::TypeLevelInteger(_) => {}
            ExprKind::BoolLiteral(_) => {}
            ExprKind::BitLiteral(_) => {}
            ExprKind::CreatePorts => {}
            ExprKind::StageReady | ExprKind::StageValid => {}
            ExprKind::TupleLiteral(inner) => {
                for i in inner {
                    i.apply(pass)?
                }
            }
            ExprKind::ArrayLiteral(inner) => {
                for i in inner {
                    i.apply(pass)?
                }
            }
            ExprKind::ArrayShorthandLiteral(inner, _) => {
                inner.apply(pass)?;
            }
            ExprKind::Index(lhs, rhs) => {
                subnodes!(lhs, rhs)
            }
            ExprKind::RangeIndex {
                target,
                start: _,
                end: _,
            } => {
                subnodes!(target)
            }
            ExprKind::TupleIndex(lhs, _) => subnodes!(lhs),
            ExprKind::FieldAccess(lhs, _) => subnodes!(lhs),
            ExprKind::MethodCall {
                target: self_,
                name: _,
                args,
                call_kind: _,
                turbofish: _,
            } => {
                subnodes!(self_);
                for arg in args.expressions_mut() {
                    arg.apply(pass)?;
                }
            }
            ExprKind::Call {
                kind: _,
                callee: _,
                args,
                turbofish: _,
            } => {
                for arg in args.expressions_mut() {
                    arg.apply(pass)?;
                }
            }
            ExprKind::BinaryOperator(lhs, _, rhs) => subnodes!(lhs, rhs),
            ExprKind::UnaryOperator(_, operand) => subnodes!(operand),
            ExprKind::Match(cond, branches) => {
                cond.apply(pass)?;
                for (_, branch) in branches {
                    branch.apply(pass)?;
                }
            }
            ExprKind::Block(block) => {
                block.statements = block
                    .statements
                    .iter()
                    .map(|stmt| match pass.visit_statement(stmt)? {
                        Some(new) => Ok(new),
                        None => Ok(vec![stmt.clone()]),
                    })
                    .collect::<Result<Vec<_>>>()?
                    .into_iter()
                    .flatten()
                    .collect();

                for statement in &mut block.statements {
                    match &mut statement.inner {
                        Statement::Binding(Binding {
                            pattern: _,
                            ty: _,
                            value,
                            wal_trace: _,
                        }) => value.apply(pass)?,
                        Statement::Expression(expr) => expr.apply(pass)?,
                        Statement::Register(reg) => {
                            let Register {
                                pattern: _,
                                clock,
                                reset,
                                initial,
                                value,
                                value_type: _,
                                attributes: _,
                            } = reg;

                            match reset {
                                Some((trig, val)) => subnodes!(trig, val),
                                None => {}
                            }

                            match initial {
                                Some(initial) => subnodes!(initial),
                                None => {}
                            }

                            subnodes!(clock, value);
                        }
                        Statement::Declaration(_) => {}
                        Statement::PipelineRegMarker(extra) => match extra {
                            Some(PipelineRegMarkerExtra::Condition(cond)) => {
                                cond.apply(pass)?;
                            }
                            Some(PipelineRegMarkerExtra::Count {
                                count: _,
                                count_typeexpr_id: _,
                            }) => {}
                            None => {}
                        },
                        Statement::Label(_) => {}
                        Statement::WalSuffixed {
                            suffix: _,
                            target: _,
                        } => {}
                        Statement::Assert(expr) => expr.apply(pass)?,
                        Statement::Set { target, value } => subnodes!(target, value),
                    }
                }

                if let Some(result) = &mut block.result {
                    result.apply(pass)?;
                }
            }
            ExprKind::If(cond, on_true, on_false) => subnodes!(cond, on_true, on_false),
            ExprKind::TypeLevelIf(_cond, on_true, on_false) => subnodes!(on_true, on_false),
            ExprKind::PipelineRef {
                stage: _,
                name: _,
                declares_name: _,
                depth_typeexpr_id: _,
            } => {}
            ExprKind::Null => {}
        };

        pass.visit_expression(self)
    }
}

impl Passable for Unit {
    fn apply(&mut self, pass: &mut dyn Pass) -> Result<()> {
        pass.visit_unit(self)?;
        self.body.apply(pass)?;
        Ok(())
    }
}
