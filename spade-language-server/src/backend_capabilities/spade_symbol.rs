use spade_common::location_info::{Loc, WithLocation};
use spade_common::name::NameID;
use spade_hir::expression::{CallKind, NamedArgument};
use spade_hir::{
    ArgumentList, ExecutableItem, ExprKind, Expression, Pattern, PatternKind,
    PipelineRegMarkerExtra, Register, Statement, TypeDeclKind, TypeDeclaration, TypeExpression,
    TypeSpec, Unit,
};
use spade_typeinference::equation::TypeVar;
use spade_typeinference::{HasType, TypeState};
use spade_types::KnownType;
use tower_lsp::lsp_types::{Position, Url};

use crate::backend::ServerBackend;

/*
    A small (mostly)flat enum describing a heavily simplified
    subset of the available Spade language constructs.
*/
#[derive(Debug, Clone)]
pub enum SpadeSymbol {
    // Symbol is a datatype: contains id of type.
    Type(NameID),
    Unit {
        kind: SUnitKind,
        name: NameID,
        out_type: NameID,
    },
    Variable {
        name: NameID,
        var_type: NameID,
    },
    Member {
        kind: SMemberKind,
        name: String,
        member_type: NameID,
        parent_type: NameID,
    },
    // Type of symbol could not be deduced because parser bailed to early.
    NotInferred(NameID),
}

#[derive(Debug, Clone)]
pub enum SUnitKind {
    Function,
    Entity,
    Pipeline,
}

#[derive(Debug, Clone)]
pub enum SMemberKind {
    Field,
    Method,
}

impl SpadeSymbol {
    /*
        Deduces if an id is a variable binding or a datat type based on
        if it's name and type are the same.
    */
    fn from_id(name_id: &NameID, type_state: Option<&TypeState>) -> SpadeSymbol {
        type S = SpadeSymbol;
        let type_id = if let Some(type_state) = type_state {
            match name_id.get_type(type_state).resolve(type_state) {
                TypeVar::Known(_, KnownType::Named(type_id), _) => Some(type_id),
                _ => None,
            }
        } else {
            None
        };

        if let Some(type_id) = type_id {
            if name_id == type_id {
                S::Type(name_id.clone())
            } else {
                S::Variable {
                    name: name_id.clone(),
                    var_type: type_id.clone(),
                }
            }
        } else {
            S::NotInferred(name_id.clone())
        }
    }
}

fn get_expr_type(expr: &dyn HasType, type_state: Option<&TypeState>) -> Option<NameID> {
    if let Some(type_state) = type_state {
        match expr.get_type(type_state).resolve(type_state) {
            TypeVar::Known(_, KnownType::Named(type_id), _) => {
                return Some(type_id.clone());
            }
            _ => {}
        }
    }
    None
}

impl ServerBackend {
    pub(crate) fn find_symbol(&self, pos: &Position, _uri: &Url) -> Option<SpadeSymbol> {
        // Search typedeclarations
        let td_search = self
            .item_list
            .lock()
            .unwrap()
            .types
            .iter()
            .find_map(|(_, td)| self.search_sym_tdef(td, pos));

        if td_search.is_some() {
            return td_search;
        }

        let type_states = &self.type_states.lock().unwrap().clone();
        // Search units
        type E = ExecutableItem;
        self.item_list
            .lock()
            .unwrap()
            .executables
            .iter()
            .find_map(|(id, item)| {
                let ts = type_states.get(id);
                match item {
                    E::Unit(u) => self.search_sym_unit(&u, pos, ts),
                    E::ExternUnit(_, _) => None,    // FIXME
                    E::EnumInstance { .. } => None, // FIXME
                    E::StructInstance => None,      // FIXME
                }
            })
    }

    fn search_sym_tdef(
        &self,
        type_decl: &Loc<TypeDeclaration>,
        pos: &Position,
    ) -> Option<SpadeSymbol> {
        if !self.pos_in_loc(&type_decl.loc(), pos) {
            return None;
        }

        type T = TypeDeclKind;
        match &type_decl.kind {
            T::Enum(e) => e
                .options
                .iter()
                .find_map(|(_, pl)| pl.0.iter().find_map(|p| self.search_sym_tspec(&p.ty, pos))),
            T::Struct(s) => s
                .members
                .0
                .iter()
                .find_map(|p| self.search_sym_tspec(&p.ty, pos)),
            T::Primitive(_) => None, // Ignore
        }
    }

    pub(crate) fn search_sym_unit(
        &self,
        unit: &Loc<Unit>,
        pos: &Position,
        type_state: Option<&TypeState>,
    ) -> Option<SpadeSymbol> {
        if !self.pos_in_loc(&unit.loc(), pos) {
            return None;
        }

        let Unit {
            name: _name,
            inputs,
            head,
            body,
            ..
        } = &unit.inner;

        // Search inputs
        let inp_search = inputs
            .iter()
            .find_map(|(_, ts)| self.search_sym_tspec(&ts, pos));

        if inp_search.is_some() {
            return inp_search;
        }

        // Search output
        if let Some(ty) = &head.output_type {
            let ts_search = self.search_sym_tspec(&ty, pos);
            if ts_search.is_some() {
                return ts_search;
            }
        }

        // Search unit body
        self.search_sym_expr(&body, pos, type_state)
    }

    fn search_sym_expr(
        &self,
        expression: &Loc<Expression>,
        pos: &Position,
        ts: Option<&TypeState>,
    ) -> Option<SpadeSymbol> {
        if !self.pos_in_loc(&expression.loc(), pos) {
            return None;
        }

        type E = ExprKind;
        match &expression.kind {
            E::Identifier(id) | E::TypeLevelInteger(id) => {
                return Some(SpadeSymbol::from_id(id, ts));
            }
            E::TupleLiteral(list) | E::ArrayLiteral(list) => {
                return list
                    .iter()
                    .find_map(|expr| self.search_sym_expr(expr, pos, ts));
            }
            E::ArrayShorthandLiteral(expr, _length) => return self.search_sym_expr(expr, pos, ts),
            E::Index(lhs, rhs) => {
                return [lhs, rhs]
                    .iter()
                    .find_map(|expr| self.search_sym_expr(expr, pos, ts));
            }
            E::RangeIndex { target, .. } => {
                return self.search_sym_expr(target, pos, ts);
            }
            E::TupleIndex(lhs, _) => {
                return self.search_sym_expr(lhs, pos, ts);
            }
            E::FieldAccess(expr, ident) => {
                // Search lhs expression
                if let Some(id) = self.search_sym_expr(expr, pos, ts) {
                    return Some(id);
                }
                // Search rhs member
                if self.pos_in_loc(&ident.loc(), pos) {
                    let parent_type = get_expr_type(&expr.inner, ts);
                    let member_type = get_expr_type(&expression.inner, ts);
                    match (parent_type, member_type) {
                        (Some(parent_type), Some(member_type)) => {
                            return Some(SpadeSymbol::Member {
                                kind: SMemberKind::Field,
                                parent_type,
                                name: ident.to_string(),
                                member_type,
                            });
                        }
                        _ => {}
                    }
                }
            }
            E::Call {
                kind,
                callee,
                args,
                turbofish: _turbofish,
            } => {
                // Search name
                if self.pos_in_loc(&callee.loc(), pos) {
                    let unit_kind = match kind {
                        CallKind::Function => SUnitKind::Function,
                        CallKind::Entity(_) => SUnitKind::Entity,
                        CallKind::Pipeline { .. } => SUnitKind::Pipeline,
                    };
                    let unit_type_id = get_expr_type(expression, ts);
                    if let Some(unit_type_id) = unit_type_id {
                        if unit_type_id == **callee {
                            return Some(SpadeSymbol::Type(callee.inner.clone()));
                        } else {
                            return Some(SpadeSymbol::Unit {
                                kind: unit_kind,
                                name: callee.inner.clone(),
                                out_type: unit_type_id,
                            });
                        }
                    }
                    return Some(SpadeSymbol::NotInferred(callee.inner.clone()));
                }
                // Search args
                return self.search_sym_args(args, pos, ts);
            }
            E::MethodCall {
                target,
                name,
                args,
                call_kind: _kind,
                turbofish: _turbofish,
            } => {
                // Search target
                if let Some(id) = self.search_sym_expr(target, pos, ts) {
                    return Some(id);
                }
                // Search args
                if let Some(id) = self.search_sym_args(args, pos, ts) {
                    return Some(id);
                }
                // Search name
                if self.pos_in_loc(&name.loc(), pos) {
                    let parent_type = get_expr_type(&target.inner, ts);
                    let member_type = get_expr_type(&expression.inner, ts);
                    match (parent_type, member_type) {
                        (Some(parent_type), Some(member_type)) => {
                            return Some(SpadeSymbol::Member {
                                kind: SMemberKind::Method,
                                parent_type,
                                name: name.to_string(),
                                member_type,
                            });
                        }
                        _ => {}
                    }
                }
            }
            E::BinaryOperator(lhs, _, rhs) => {
                for expr in [lhs, rhs] {
                    if let Some(id) = self.search_sym_expr(expr, pos, ts) {
                        return Some(id);
                    }
                }
            }
            E::UnaryOperator(_, operand) => {
                return self.search_sym_expr(operand, pos, ts);
            }
            E::Match(expr, arms) => {
                // Search arms
                for (p, e) in arms {
                    // Search arm pattern
                    if let Some(id) = self.search_sym_pat(p, pos, ts) {
                        return Some(id);
                    }
                    // Search arm expression
                    if let Some(id) = self.search_sym_expr(e, pos, ts) {
                        return Some(id);
                    }
                }
                // Search expr
                return self.search_sym_expr(expr, pos, ts);
            }
            E::If(expr1, expr2, expr3) => {
                for expr in [expr1, expr2, expr3] {
                    if let Some(id) = self.search_sym_expr(expr, pos, ts) {
                        return Some(id);
                    }
                }
            }
            E::TypeLevelIf(_expr1, expr2, expr3) => {
                // FIXME: Search for symbols i nconst generics
                for expr in [expr2, expr3] {
                    if let Some(id) = self.search_sym_expr(expr, pos, ts) {
                        return Some(id);
                    }
                }
            }
            E::Block(block) => {
                for s in &block.statements {
                    if let Some(id) = self.find_sym_stat(s, pos, ts) {
                        return Some(id);
                    }
                }
                if let Some(expr) = &block.result {
                    if let Some(id) = self.search_sym_expr(expr, pos, ts) {
                        return Some(id);
                    }
                }
            }
            E::PipelineRef { name, .. } => {
                if self.pos_in_loc(&name.loc(), pos) {
                    //return Ok(Some(SpadeSymbol::NameID(name.inner.clone(), self.get_type_id(name, type_state)))); //
                }
            }
            E::LambdaDef {
                arguments: _,
                body,
                lambda_type: _,
                lambda_unit: _,
                lambda_type_params: _,
            } => return self.search_sym_expr(body, pos, ts),
            E::IntLiteral(_, _)
            | E::BitLiteral(_)
            | E::BoolLiteral(_)
            | E::CreatePorts
            | E::StageValid
            | E::StageReady
            | E::Null
            | E::StaticUnreachable(_) => {} // Ignore all of these
        }
        None
    }

    fn search_sym_args(
        &self,
        arg_list: &Loc<ArgumentList<Expression>>,
        pos: &Position,
        ts: Option<&TypeState>,
    ) -> Option<SpadeSymbol> {
        if !self.pos_in_loc(&arg_list.loc(), pos) {
            return None;
        }

        type A = ArgumentList<Expression>;
        type N = NamedArgument<Expression>;
        match &arg_list.inner {
            A::Named(list) => list.iter().find_map(|arg| match arg {
                N::Full(_, expr) | N::Short(_, expr) => self.search_sym_expr(&expr, pos, ts),
            }),

            A::Positional(list) => list
                .iter()
                .find_map(|expr| self.search_sym_expr(&expr, pos, ts)),
        }
    }

    fn find_sym_stat(
        &self,
        statement: &Loc<Statement>,
        pos: &Position,
        type_state: Option<&TypeState>,
    ) -> Option<SpadeSymbol> {
        if !self.pos_in_loc(&statement.loc(), pos) {
            return None;
        }

        match &statement.inner {
            Statement::Binding(binding) => {
                // Search lhs pattern
                let lhs_search = self.search_sym_pat(&binding.pattern, pos, type_state);
                if lhs_search.is_some() {
                    lhs_search
                } else {
                    // Search rhs value
                    self.search_sym_expr(&binding.value, pos, type_state)
                }
            }
            Statement::Register(register) => {
                //FIXME deal with attributes?
                let Register {
                    clock,
                    reset,
                    initial,
                    value,
                    value_type,
                    ..
                } = register;

                // Search clock
                let clock_search = self.search_sym_expr(clock, pos, type_state);
                if clock_search.is_some() {
                    return clock_search;
                }
                // Search reset
                if let Some(reset) = reset {
                    return [&reset.0, &reset.1]
                        .iter()
                        .find_map(|expr| self.search_sym_expr(expr, pos, type_state));
                }
                // Search initial
                if let Some(init) = &initial {
                    let init_search = self.search_sym_expr(init, pos, type_state);
                    if init_search.is_some() {
                        return init_search;
                    }
                }
                // Search value
                let value_search = self.search_sym_expr(value, pos, type_state);
                if value_search.is_some() {
                    return value_search;
                }
                // Search value type
                if let Some(type_spec) = &value_type {
                    self.search_sym_tspec(&type_spec, pos)
                } else {
                    None
                }
            }
            Statement::Set { target, value } => [target, value]
                .iter()
                .find_map(|expr| self.search_sym_expr(expr, pos, type_state)),
            Statement::PipelineRegMarker(extra) => {
                if let Some(expr) = &extra {
                    match expr {
                        PipelineRegMarkerExtra::Condition(expr) => {
                            self.search_sym_expr(expr, pos, type_state)
                        }
                        PipelineRegMarkerExtra::Count {
                            count,
                            count_typeexpr_id: _,
                        } => {
                            // FIXME: Allow lookup in type expressions
                            self.search_sym_texpr(count, pos)
                        }
                    }
                } else {
                    None
                }
            }
            Statement::Expression(expr) => self.search_sym_expr(expr, pos, type_state),
            Statement::Assert(expr) => self.search_sym_expr(expr, pos, type_state),
            Statement::Declaration(_) => None,     // FIXME
            Statement::WalSuffixed { .. } => None, // FIXME
            Statement::Label { .. } => None,       // FIXME
        }
    }

    fn search_sym_pat(
        &self,
        pattern: &Loc<Pattern>,
        pos: &Position,
        type_state: Option<&TypeState>,
    ) -> Option<SpadeSymbol> {
        if !self.pos_in_loc(&pattern.loc(), pos) {
            return None;
        }

        match &pattern.kind {
            PatternKind::Name { name, .. } => {
                if self.pos_in_loc(&name.loc(), pos) {
                    Some(SpadeSymbol::from_id(name, type_state))
                } else {
                    None
                }
            }
            PatternKind::Tuple(list) | PatternKind::Array(list) => list
                .iter()
                .find_map(|p| self.search_sym_pat(p, pos, type_state)),
            PatternKind::Type(name, args) => {
                // Search name
                if self.pos_in_loc(&name.loc(), pos) {
                    return Some(SpadeSymbol::Type(name.inner.clone()));
                }
                // Search args
                args.iter()
                    .find_map(|arg| self.search_sym_pat(&arg.value, pos, type_state))
            }
            PatternKind::Bool(_) | PatternKind::Integer(_) => None, // Ignore
        }
    }

    fn search_sym_tspec(&self, type_spec: &Loc<TypeSpec>, pos: &Position) -> Option<SpadeSymbol> {
        if !self.pos_in_loc(&type_spec.loc(), pos) {
            return None;
        }

        match &type_spec.inner {
            TypeSpec::Declared(name, args) => {
                // Search name
                if self.pos_in_loc(&name.loc(), pos) {
                    Some(SpadeSymbol::Type(name.inner.clone()))
                } else {
                    // Search args
                    args.iter().find_map(|arg| self.search_sym_texpr(arg, pos))
                }
            }
            TypeSpec::Generic(name) => {
                if self.pos_in_loc(&name.loc(), pos) {
                    Some(SpadeSymbol::Type(name.inner.clone())) //FIXME THIS MIGHT BE VERY WRONG :)
                } else {
                    None
                }
            }
            TypeSpec::Tuple(tuple) => tuple.iter().find_map(|ts| self.search_sym_tspec(&ts, pos)),
            TypeSpec::Array { inner, size } => {
                // Search inner
                let inner_search = self.search_sym_tspec(&inner, pos);
                if inner_search.is_some() {
                    inner_search
                } else {
                    // Search size
                    self.search_sym_texpr(&size, pos)
                }
            }
            TypeSpec::Wire(ts) | TypeSpec::Inverted(ts) => {
                if self.pos_in_loc(&ts.loc(), pos) {
                    self.search_sym_tspec(&ts, pos)
                } else {
                    None
                }
            }
            TypeSpec::Wildcard(_) | TypeSpec::TraitSelf(_) => None,
        }
    }

    fn search_sym_texpr(
        &self,
        type_expr: &Loc<TypeExpression>,
        pos: &Position,
    ) -> Option<SpadeSymbol> {
        if !self.pos_in_loc(&type_expr.loc(), pos) {
            return None;
        }
        match &type_expr.inner {
            TypeExpression::TypeSpec(ts) => {
                self.search_sym_tspec(&ts.clone().at_loc(&type_expr.loc()), pos)
            }
            //Note: If it's not a typespec then it's just a number
            _ => None,
        }
    }
}

impl ServerBackend {
    pub(crate) fn find_symbol_named(
        &self,
        pos: &Position,
        _uri: &Url,
        name: &str,
    ) -> Option<SpadeSymbol> {
        let type_states = &self.type_states.lock().unwrap().clone();
        // Search units
        type E = ExecutableItem;
        self.item_list
            .lock()
            .unwrap()
            .executables
            .iter()
            .find_map(|(id, item)| {
                let ts = type_states.get(id);
                match item {
                    E::Unit(u) => self.search_sym_unit_named(&u, pos, ts, name),
                    E::ExternUnit(_, _) => None,    // FIXME
                    E::EnumInstance { .. } => None, // FIXME
                    E::StructInstance => None,      // FIXME
                }
            })
    }

    pub(crate) fn search_sym_unit_named(
        &self,
        unit: &Loc<Unit>,
        pos: &Position,
        type_state: Option<&TypeState>,
        name: &str,
    ) -> Option<SpadeSymbol> {
        if !self.pos_in_loc(&unit.loc(), pos) {
            return None;
        }

        let Unit {
            name: _name,
            inputs: _inputs,
            head: _head,
            body,
            ..
        } = &unit.inner;

        /*
        // Search inputs
        let inp_search = inputs
            .iter()
            .find_map(|(_, ts)| self.search_sym_tspec(&ts, pos));

        if inp_search.is_some() {
            return inp_search;
        }
        */

        // Search unit body
        self.search_sym_expr_named(&body, pos, type_state, name)
    }

    fn search_sym_expr_named(
        &self,
        expression: &Loc<Expression>,
        pos: &Position,
        ts: Option<&TypeState>,
        name: &str,
    ) -> Option<SpadeSymbol> {
        type E = ExprKind;
        match &expression.kind {
            E::Identifier(_id) | E::TypeLevelInteger(_id) => {}
            E::TupleLiteral(_) | E::ArrayLiteral(_) | E::ArrayShorthandLiteral(_, _) => {}
            E::Index(_lhs, _rhs) => {}
            E::RangeIndex { .. } => {}
            E::TupleIndex(_lhs, _) => {}
            E::FieldAccess(_expr, _ident) => {}
            E::Call { .. } => {}
            E::MethodCall { .. } => {}
            E::BinaryOperator(_lhs, _, _rhs) => {}
            E::UnaryOperator(_, _operand) => {}
            E::Match(_expr, _arms) => {}
            E::If(_expr1, _expr2, _expr3) => {}
            E::TypeLevelIf(_expr1, _expr2, _expr3) => {}
            E::Block(block) => {
                let mut syms = vec![];
                for s in &block.statements {
                    let stat_search = self.find_sym_stat_name(s, pos, ts, name);
                    if let Some(sym) = stat_search {
                        syms.push(sym);
                    }
                }
                return syms.last().cloned();
            }
            E::LambdaDef {
                arguments: _,
                body,
                lambda_type: _,
                lambda_unit: _,
                lambda_type_params: _,
            } => return self.search_sym_expr_named(body, pos, ts, name),
            E::PipelineRef { .. } => {}
            E::IntLiteral(_, _)
            | E::BitLiteral(_)
            | E::BoolLiteral(_)
            | E::CreatePorts
            | E::StageValid
            | E::StageReady
            | E::Null
            | E::StaticUnreachable(_) => {} // Ignore all of these
        }
        None
    }

    fn same_name(&self, id: &NameID, name: &str) -> bool {
        name == id.1.tail().0
    }

    fn find_sym_stat_name(
        &self,
        statement: &Loc<Statement>,
        pos: &Position,
        type_state: Option<&TypeState>,
        name: &str,
    ) -> Option<SpadeSymbol> {
        match &statement.inner {
            Statement::Binding(binding) => {
                if !self.pos_after_loc(&statement.loc(), pos).unwrap_or(false) {
                    return None;
                }
                self.search_sym_pat_name(&binding.pattern, pos, type_state, name)
            }
            Statement::Expression(_) => None,
            Statement::Register(_) => None,
            Statement::Set { .. } => None,
            Statement::PipelineRegMarker(_) => None,
            Statement::Assert(_) => None,
            Statement::Declaration(_) => None,     // FIXME
            Statement::WalSuffixed { .. } => None, // FIXME
            Statement::Label { .. } => None,       // FIXME
        }
    }

    fn search_sym_pat_name(
        &self,
        pattern: &Loc<Pattern>,
        pos: &Position,
        type_state: Option<&TypeState>,
        name: &str,
    ) -> Option<SpadeSymbol> {
        match &pattern.kind {
            PatternKind::Name { name: name_id, .. } => {
                if self.same_name(name_id, name) {
                    Some(SpadeSymbol::from_id(name_id, type_state))
                } else {
                    None
                }
            }
            PatternKind::Tuple(list) | PatternKind::Array(list) => list
                .iter()
                .find_map(|p| self.search_sym_pat_name(p, pos, type_state, name)),
            PatternKind::Type(_, _) => None,
            PatternKind::Bool(_) | PatternKind::Integer(_) => None, // Ignore
        }
    }
}
