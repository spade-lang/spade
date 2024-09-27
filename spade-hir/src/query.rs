use std::collections::BTreeMap;

use spade_common::{id_tracker::ExprID, loc_map::LocMap, location_info::Loc};

use crate::{
    expression::NamedArgument, ArgumentList, Binding, ExecutableItem, Expression, ItemList,
    Register, Statement,
};

pub enum Thing {
    Expr(Expression),
    Statement(Statement),
    Executable(ExecutableItem),
}

pub struct QueryCache {
    things: LocMap<Thing>,
    // FIXME: To support patterns, this needs to not be just Loc<Expression> anymore
    ids: BTreeMap<ExprID, Loc<Expression>>,
}

// Public functions
impl QueryCache {
    pub fn from_item_list(items: &ItemList) -> Self {
        let mut result = QueryCache {
            things: LocMap::new(),
            ids: BTreeMap::new(),
        };

        for (_, item) in items.executables.iter() {
            result.visit_executable(item.clone());
        }

        result
    }

    pub fn id_to_expression(&self, id: ExprID) -> Option<&Loc<Expression>> {
        self.ids.get(&id).map(|x| x)
    }
}

// Visitors
impl<'a> QueryCache {
    fn visit_executable(&mut self, item: ExecutableItem) {
        match &item {
            ExecutableItem::EnumInstance {
                base_enum: _,
                variant: _,
            } => {
                // FIXME: Map this loc
            }
            // Structs are stored as types rather than struct instances
            ExecutableItem::StructInstance => {}
            ExecutableItem::Unit(unit) => {
                self.things
                    .insert(unit.loc().map(|_| Thing::Executable(item.clone())));

                self.visit_expression(&unit.body)
            }
            ExecutableItem::ExternUnit(_, unit) => {
                self.things
                    .insert(unit.loc().map(|_| Thing::Executable(item.clone())));
            }
        }
    }

    fn visit_expression(&mut self, expr: &'a Loc<Expression>) {
        self.things
            .insert(expr.loc().map(|_| Thing::Expr(expr.inner.clone())));
        self.ids.insert(expr.id, expr.clone());

        match &expr.kind {
            crate::ExprKind::Identifier(_) => {}
            crate::ExprKind::IntLiteral(_, _) => {}
            crate::ExprKind::BoolLiteral(_) => {}
            crate::ExprKind::BitLiteral(_) => {}
            // FIXME Visit types
            crate::ExprKind::TypeLevelInteger(_) => {}
            crate::ExprKind::CreatePorts => {}
            crate::ExprKind::TupleLiteral(inner) | crate::ExprKind::ArrayLiteral(inner) => {
                for expr in inner {
                    self.visit_expression(expr)
                }
            }
            crate::ExprKind::ArrayShorthandLiteral(expr, _) => self.visit_expression(expr),
            crate::ExprKind::Index(lhs, rhs) => {
                self.visit_expression(lhs);
                self.visit_expression(rhs);
            }
            crate::ExprKind::RangeIndex {
                target,
                start: _,
                end: _,
            } => self.visit_expression(target),
            crate::ExprKind::TupleIndex(target, _) => self.visit_expression(target),
            crate::ExprKind::FieldAccess(target, _) => self.visit_expression(target),
            crate::ExprKind::MethodCall {
                target,
                name: _,
                args,
                call_kind: _,
                turbofish: _,
            } => {
                // FIXME: handle name and turbofish
                self.visit_expression(target);
                self.visit_arg_list(args)
            }
            crate::ExprKind::Call {
                kind: _,
                callee: _callee,
                args,
                turbofish: _turbofish,
            } => {
                // FIXME: handle callee and turbofish
                self.visit_arg_list(args)
            }
            crate::ExprKind::BinaryOperator(lhs, _, rhs) => {
                self.visit_expression(lhs);
                self.visit_expression(rhs);
            }
            crate::ExprKind::UnaryOperator(_, operand) => self.visit_expression(operand),
            crate::ExprKind::Match(cond, branches) => {
                self.visit_expression(cond);

                for (_pattern, expr) in branches {
                    // FIXME: Handle pattern
                    self.visit_expression(expr)
                }
            }
            crate::ExprKind::Block(b) => {
                for stmt in &b.statements {
                    self.visit_statements(&stmt)
                }
                if let Some(result) = &b.result {
                    self.visit_expression(result)
                }
            }
            crate::ExprKind::If(cond, lhs, rhs) => {
                self.visit_expression(cond);
                self.visit_expression(lhs);
                self.visit_expression(rhs);
            }
            crate::ExprKind::TypeLevelIf(_cond, lhs, rhs) => {
                // FIXME: Visit cond
                self.visit_expression(lhs);
                self.visit_expression(rhs);
            }
            crate::ExprKind::PipelineRef {
                stage: _,
                name: _,
                declares_name: _,
                depth_typeexpr_id: _,
            } => {}
            crate::ExprKind::StageValid => {}
            crate::ExprKind::StageReady => {}
            crate::ExprKind::Null => {}
        }
    }

    fn visit_statements(&mut self, stmt: &'a Loc<Statement>) {
        match &stmt.inner {
            Statement::Binding(Binding {
                pattern: _,
                ty: _,
                value,
                wal_trace: _,
            }) => {
                // FIXME: Handle pattern, ty
                self.visit_expression(value)
            }
            Statement::Register(Register {
                pattern: _pattern,
                clock,
                reset,
                initial,
                value,
                value_type: _value_type,
                attributes: _,
            }) => {
                // FIXME: Handle pattern, value_type
                self.visit_expression(clock);
                if let Some((trig, val)) = reset {
                    self.visit_expression(trig);
                    self.visit_expression(val);
                }
                if let Some(initial) = initial {
                    self.visit_expression(initial)
                }
                self.visit_expression(value);
            }
            Statement::Expression(e) => {
                self.visit_expression(e);
            }
            Statement::Declaration(_) => {
                // FIXME: Handle declaration
            }
            Statement::PipelineRegMarker(_) => {}
            Statement::Label(_) => {
                // FIXME: Handle labels
            }
            Statement::Assert(expr) => self.visit_expression(expr),
            Statement::Set { target, value } => {
                self.visit_expression(target);
                self.visit_expression(value);
            }
            Statement::WalSuffixed {
                suffix: _,
                target: _,
            } => {}
        }
    }

    fn visit_arg_list(&mut self, args: &'a ArgumentList<Expression>) {
        match args {
            ArgumentList::Named(l) => {
                for arg in l {
                    match arg {
                        NamedArgument::Full(_name, expr) => {
                            // FIXME: Handle name

                            self.visit_expression(expr)
                        }
                        NamedArgument::Short(_, expr) => self.visit_expression(expr),
                    }
                }
            }
            ArgumentList::Positional(args) => {
                for arg in args {
                    self.visit_expression(arg)
                }
            }
        }
    }
}
