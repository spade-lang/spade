use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};
use spade_common::{
    id_tracker::ExprID,
    loc_map::LocMap,
    location_info::{Loc, WithLocation},
    name::NameID,
};

use crate::{
    expression::NamedArgument, ArgumentList, Binding, ConstGeneric, Enum, ExecutableItem, ExprKind,
    Expression, ItemList, Pattern, PatternArgument, PatternKind, Register, Statement, Struct,
    TypeDeclKind, TypeDeclaration, TypeExpression, TypeSpec,
};

#[derive(Debug, Serialize, Deserialize)]
pub enum Thing {
    Pattern(Pattern),
    Expr(Expression),
    Statement(Statement),
    Executable(ExecutableItem),
}

#[derive(Serialize, Deserialize)]
pub struct QueryCache {
    things: LocMap<Thing>,
    names: LocMap<NameID>,
    // FIXME: To support patterns, this needs to not be just Loc<Expression> anymore
    ids: BTreeMap<ExprID, Loc<Expression>>,
}

// Public functions
impl QueryCache {
    pub fn empty() -> Self {
        QueryCache {
            things: LocMap::new(),
            names: LocMap::new(),
            ids: BTreeMap::new(),
        }
    }

    pub fn from_item_list(items: &ItemList) -> Self {
        let mut result = QueryCache::empty();

        for (_, item) in items.executables.iter() {
            result.visit_executable(item.clone());
        }

        for (_, ty) in items.types.iter() {
            result.visit_type_decl(ty)
        }

        result
    }

    pub fn things_around(&self, loc: &Loc<()>) -> Vec<Loc<&Thing>> {
        self.things.around(loc)
    }

    pub fn names_around(&self, loc: &Loc<()>) -> Vec<Loc<&NameID>> {
        self.names.around(loc)
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

    fn visit_expr_kind(&mut self, kind: &Loc<&ExprKind>) {
        match &kind.inner {
            crate::ExprKind::Error => {}
            crate::ExprKind::Identifier(ident) => self.names.insert(ident.clone().at_loc(kind)),
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
                callee,
                args,
                turbofish: _turbofish,
            } => {
                self.names.insert(callee.clone());
                // FIXME: handle callee and turbofish
                self.visit_arg_list(args)
            }
            crate::ExprKind::LambdaDef {
                lambda_type: _,
                lambda_type_params: _,
                lambda_unit: _,
                arguments: _,
                captured_generic_params: _,
                body,
            } => {
                // FIXME: Handle arguments
                self.visit_expression(body);
            }
            crate::ExprKind::BinaryOperator(lhs, _, rhs) => {
                self.visit_expression(lhs);
                self.visit_expression(rhs);
            }
            crate::ExprKind::UnaryOperator(_, operand) => self.visit_expression(operand),
            crate::ExprKind::Match(cond, branches) => {
                self.visit_expression(cond);

                for (pattern, expr) in branches {
                    self.visit_pattern(pattern);
                    self.visit_expression(expr);
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
            crate::ExprKind::StaticUnreachable(_) | crate::ExprKind::Null => {}
        }
    }

    fn visit_expression(&mut self, expr: &'a Loc<Expression>) {
        self.things
            .insert(expr.loc().map(|_| Thing::Expr(expr.inner.clone())));
        self.ids.insert(expr.id, expr.clone());

        self.visit_expr_kind(&Loc::new(&expr.kind, expr.span, expr.file_id));
    }

    fn visit_pattern(&mut self, pat: &'a Loc<Pattern>) {
        self.things
            .insert(pat.loc().map(|_| Thing::Pattern(pat.inner.clone())));
        match &pat.inner.kind {
            PatternKind::Integer(_) => {}
            PatternKind::Bool(_) => {}
            PatternKind::Name {
                name,
                pre_declared: _,
            } => {
                self.names.insert(name.clone());
            }
            PatternKind::Tuple(inner) => {
                for pat in inner {
                    self.visit_pattern(&pat);
                }
            }
            PatternKind::Array(inner) => {
                for pat in inner {
                    self.visit_pattern(&pat);
                }
            }
            PatternKind::Type(base, args) => {
                self.names.insert(base.clone());
                for PatternArgument {
                    target: _,
                    value,
                    kind: _,
                } in args
                {
                    self.visit_pattern(value);
                }
            }
        }
    }

    fn visit_statements(&mut self, stmt: &'a Loc<Statement>) {
        match &stmt.inner {
            Statement::Error => {}
            Statement::Binding(Binding {
                pattern,
                ty: _,
                value,
                wal_trace: _,
            }) => {
                self.visit_pattern(pattern);
                // FIXME: Handle ty
                self.visit_expression(value)
            }
            Statement::Register(Register {
                pattern,
                clock,
                reset,
                initial,
                value,
                value_type: _value_type,
                attributes: _,
            }) => {
                self.visit_pattern(pattern);
                // FIXME: Handle value_type
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
            Statement::Declaration(names) => {
                for name in names {
                    self.names.insert(name.clone());
                }
            }
            Statement::PipelineRegMarker(_) => {}
            Statement::Label(l) => {
                self.names.insert(l.clone());
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

    fn visit_type_decl(&mut self, ty: &TypeDeclaration) {
        self.names.insert(ty.name.clone());
        match &ty.kind {
            TypeDeclKind::Enum(e) => self.visit_enum_decl(e),
            TypeDeclKind::Primitive(_) => {}
            TypeDeclKind::Struct(s) => self.visit_struct(s),
        }
    }

    fn visit_enum_decl(&mut self, e: &Loc<Enum>) {
        for (_, params) in &e.options {
            for param in &params.0 {
                self.visit_type_spec(&param.ty);
            }
        }
    }

    fn visit_struct(&mut self, s: &Loc<Struct>) {
        for member in &s.members.0 {
            self.visit_type_spec(&member.ty);
        }
    }

    fn visit_type_spec(&mut self, ts: &Loc<TypeSpec>) {
        match &ts.inner {
            TypeSpec::Declared(n, params) => {
                self.names.insert(n.clone());
                for param in params {
                    self.visit_type_expr(param);
                }
            }
            TypeSpec::Generic(n) => self.names.insert(n.clone()),
            TypeSpec::Tuple(inner) => {
                for i in inner {
                    self.visit_type_spec(i);
                }
            }
            TypeSpec::Array { inner, size } => {
                self.visit_type_spec(inner);
                self.visit_type_expr(size);
            }
            TypeSpec::Inverted(inner) => self.visit_type_spec(inner),
            TypeSpec::Wire(inner) => self.visit_type_spec(inner),
            TypeSpec::TraitSelf(_) => {}
            TypeSpec::Wildcard(_) => {}
        }
    }

    fn visit_type_expr(&mut self, te: &Loc<TypeExpression>) {
        match &te.inner {
            TypeExpression::Integer(_) => {}
            TypeExpression::TypeSpec(ts) => self.visit_type_spec(&ts.clone().at_loc(te)),
            TypeExpression::ConstGeneric(cg) => {
                self.visit_const_generic(cg);
            }
        }
    }

    fn visit_const_generic(&mut self, cg: &Loc<ConstGeneric>) {
        match &cg.inner {
            ConstGeneric::Name(n) => self.names.insert(n.clone()),
            ConstGeneric::Const(_) => {}
            ConstGeneric::Add(lhs, rhs) => {
                self.visit_const_generic(lhs);
                self.visit_const_generic(rhs);
            }
            ConstGeneric::Sub(lhs, rhs) => {
                self.visit_const_generic(lhs);
                self.visit_const_generic(rhs);
            }
            ConstGeneric::Mul(lhs, rhs) => {
                self.visit_const_generic(lhs);
                self.visit_const_generic(rhs);
            }
            ConstGeneric::Div(lhs, rhs) => {
                self.visit_const_generic(lhs);
                self.visit_const_generic(rhs);
            }
            ConstGeneric::Mod(lhs, rhs) => {
                self.visit_const_generic(lhs);
                self.visit_const_generic(rhs);
            }
            ConstGeneric::Eq(lhs, rhs) => {
                self.visit_const_generic(lhs);
                self.visit_const_generic(rhs);
            }
            ConstGeneric::NotEq(lhs, rhs) => {
                self.visit_const_generic(lhs);
                self.visit_const_generic(rhs);
            }
            ConstGeneric::UintBitsToFit(inner) => self.visit_const_generic(inner),
        }
    }
}
