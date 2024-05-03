use spade_common::location_info::Loc;
use spade_hir::{Binding, ExprKind, Expression, Register, Statement, Unit};

use crate::Result;

pub trait Pass {
    fn visit_expression(&mut self, expression: &mut Loc<Expression>) -> Result<()>;
}

pub trait Passable {
    /// Applies the pass to this HIR node. Children are visited before
    /// parents. Statements are visited in the order that they are defined
    fn apply(&mut self, pass: &mut impl Pass) -> Result<()>;
}

impl Passable for Loc<Expression> {
    fn apply(&mut self, pass: &mut impl Pass) -> Result<()> {
        macro_rules! subnodes {
            ($($node:expr),*) => {
                {$($node.apply(pass)?;)*}
            };
        }

        match &mut self.inner.kind {
            ExprKind::Identifier(_) => {}
            ExprKind::IntLiteral(_) => {}
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
                for statement in &mut block.statements {
                    statement.apply(pass)?;
                }

                if let Some(result) = &mut block.result {
                    result.apply(pass)?;
                }
            }
            ExprKind::If(cond, on_true, on_false) => subnodes!(cond, on_true, on_false),
            ExprKind::PipelineRef {
                stage: _,
                name: _,
                declares_name: _,
            } => {}
            ExprKind::Fsm(stmts) => {
                for stmt in stmts {
                    stmt.apply(pass)?
                }
            }
            ExprKind::Null => {}
        };

        pass.visit_expression(self)
    }
}

impl Passable for Statement {
    fn apply(&mut self, pass: &mut impl Pass) -> Result<()> {
        macro_rules! subnodes {
            ($($node:expr),*) => {
                {$($node.apply(pass)?;)*}
            };
        }
        match self {
            Statement::Binding(Binding {
                pattern: _,
                ty: _,
                value,
                wal_trace: _,
            }) => value.apply(pass)?,
            Statement::Register(reg) => {
                let Register {
                    pattern: _,
                    clock,
                    reset,
                    initial,
                    value,
                    value_type: _,
                    attributes: _,
                } = &mut reg.inner;

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
            Statement::PipelineRegMarker(cond) => {
                if let Some(cond) = cond {
                    cond.apply(pass)?;
                }
            }
            Statement::Label(_) => {}
            Statement::WalSuffixed {
                suffix: _,
                target: _,
            } => {}
            Statement::Assert(expr) => expr.apply(pass)?,
            Statement::Set { target, value } => subnodes!(target, value),
            Statement::Yield(value) => subnodes!(value),
            Statement::ForLoop(stmts) => {
                for stmt in &mut stmts.body {
                    stmt.apply(pass)?;
                }
            }
        }

        Ok(())
    }
}

impl Passable for Unit {
    fn apply(&mut self, pass: &mut impl Pass) -> Result<()> {
        self.body.apply(pass)
    }
}
