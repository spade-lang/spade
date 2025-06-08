use crate::backend_capabilities::spade_symbol::SpadeSymbol;
use spade_common::name::NameID;
use spade_hir::{
    ExecutableItem, ExprKind, Expression, Pattern, PatternKind, Statement, TypeDeclKind,
};
use tower_lsp::lsp_types::{Location, Position, Url};

use crate::backend::ServerBackend;

pub trait GotoDefinition {
    fn find_definition(&self, pos: &Position, uri: &Url) -> Option<Location>;
}

impl GotoDefinition for ServerBackend {
    fn find_definition(&self, pos: &Position, uri: &Url) -> Option<Location> {
        if let Some(symbol) = self.find_symbol(pos, uri) {
            match symbol {
                SpadeSymbol::Type(id)
                | SpadeSymbol::Unit { name: id, .. }
                | SpadeSymbol::Variable { name: id, .. }
                | SpadeSymbol::NotInferred(id) => {
                    return self.find_id_definition(&id);
                }
                SpadeSymbol::Member {
                    parent_type, name, ..
                } => {
                    return self.find_member_definition(&parent_type, &name);
                }
            }
        }

        None
    }
}

impl ServerBackend {
    pub(crate) fn find_id_definition(&self, query_id: &NameID) -> Option<Location> {
        let types = &self.item_list.lock().unwrap().types.clone();
        for (_, ty) in types {
            if *ty.inner.name == *query_id {
                if let Ok(location) = self.loc_to_location(ty.loc()) {
                    return Some(location);
                }
            }
            match &ty.kind {
                TypeDeclKind::Enum(e) => {
                    for option in &e.options {
                        if *option.0 == *query_id {
                            if let Ok(location) = self.loc_to_location(option.0.loc()) {
                                return Some(location);
                            }
                        }
                    }
                }
                TypeDeclKind::Struct(_) => {}
                TypeDeclKind::Primitive(_) => {}
            }
        }

        let executables = &self.item_list.lock().unwrap().executables.clone();
        for (_, item) in executables {
            match item {
                ExecutableItem::Unit(unit) => {
                    let uni_id = unit.name.name_id();
                    if **uni_id == *query_id {
                        if let Ok(location) = self.loc_to_location(unit.loc()) {
                            return Some(location);
                        }
                    }
                    for (name, _) in &unit.inputs {
                        if name.inner == *query_id {
                            if let Ok(location) = self.loc_to_location(name.loc()) {
                                return Some(location);
                            }
                        }
                    }

                    if let Some(location) = self.find_def_in_expression(&unit.body, query_id) {
                        return Some(location);
                    }
                }
                ExecutableItem::StructInstance => {}   // FIXME
                ExecutableItem::ExternUnit(_, _) => {} // FIXME
                ExecutableItem::EnumInstance { .. } => {} // FIXME
            }
        }
        None
    }

    fn find_def_in_expression(
        &self,
        expression: &Expression,
        query_id: &NameID,
    ) -> Option<Location> {
        match &expression.kind {
            ExprKind::Error => {}
            ExprKind::Block(block) => {
                for statement in &block.statements {
                    if let Some(location) = self.find_def_in_statement(statement, query_id) {
                        return Some(location);
                    }
                }
                if let Some(result) = &block.result {
                    if let Some(location) = self.find_def_in_expression(&result, query_id) {
                        return Some(location);
                    }
                }
            }
            ExprKind::If(expr1, expr2, expr3) => {
                for expr in [expr1, expr2, expr3] {
                    if let Some(location) = self.find_def_in_expression(expr, query_id) {
                        return Some(location);
                    }
                }
            }
            ExprKind::TypeLevelIf(_, expr2, expr3) => {
                for expr in [expr2, expr3] {
                    if let Some(location) = self.find_def_in_expression(expr, query_id) {
                        return Some(location);
                    }
                }
            }
            ExprKind::Match(_, arms) => {
                for arm in arms {
                    if let Some(location) = self.find_def_in_pattern(&arm.0, query_id) {
                        return Some(location);
                    }
                    if let Some(location) = self.find_def_in_expression(&arm.1, query_id) {
                        return Some(location);
                    }
                }
            }
            ExprKind::LambdaDef {
                arguments: _,
                body,
                lambda_type: _,
                lambda_unit: _,
                lambda_type_params: _,
                captured_generic_params: _,
            } => {
                return self.find_def_in_expression(body, query_id);
            }
            ExprKind::TupleLiteral(_) => {}             //  FIXME
            ExprKind::ArrayLiteral(_) => {}             //  FIXME
            ExprKind::ArrayShorthandLiteral(_, _) => {} //  FIXME
            ExprKind::RangeIndex { .. } => {}           //  FIXME
            ExprKind::Identifier(_) => {}               //  FIXME
            ExprKind::Call { .. } => {}                 //  FIXME
            ExprKind::MethodCall { .. } => {}           //  FIXME
            ExprKind::TypeLevelInteger(_) => {}         //  FIXME
            ExprKind::FieldAccess(_, _) => {}           //  FIXME
            ExprKind::UnaryOperator(_, _) => {}         //  FIXME
            ExprKind::BinaryOperator(_, _, _) => {}     //  FIXME
            ExprKind::Index(_, _) => {}                 //  FIXME
            ExprKind::TupleIndex(_, _) => {}            //  FIXME
            ExprKind::BitLiteral(_) => {}               //  FIXME
            ExprKind::BoolLiteral(_) => {}              //  FIXME
            ExprKind::IntLiteral(_, _) => {}            //  FIXME
            ExprKind::PipelineRef { .. } => {}          //  FIXME
            ExprKind::CreatePorts => {}                 //  FIXME
            ExprKind::StageReady => {}                  //  FIXME
            ExprKind::StageValid => {}                  //  FIXME
            ExprKind::StaticUnreachable(_) => {}
            ExprKind::Null => {}
        }
        None
    }

    fn find_def_in_statement(&self, statement: &Statement, query_id: &NameID) -> Option<Location> {
        match statement {
            Statement::Error => {}
            Statement::Binding(binding) => {
                let pat = &binding.pattern;
                if let Some(location) = self.find_def_in_pattern(&pat, query_id) {
                    return Some(location);
                }
            }
            Statement::Register(register) => {
                let pat = &register.pattern;
                if let Some(location) = self.find_def_in_pattern(&pat, query_id) {
                    return Some(location);
                }
                return self.find_def_in_expression(&register.value, query_id);
            }
            Statement::Expression(expression) => {
                return self.find_def_in_expression(expression, query_id)
            }
            Statement::WalSuffixed { .. } => {}   //  FIXME
            Statement::Declaration(_) => {}       //  FIXME
            Statement::Label(_) => {}             //  FIXME
            Statement::Set { .. } => {}           //  FIXME
            Statement::Assert(_) => {}            //  FIXME
            Statement::PipelineRegMarker(_) => {} //  FIXME
        }
        None
    }

    fn find_def_in_pattern(&self, pattern: &Pattern, query_id: &NameID) -> Option<Location> {
        match &pattern.kind {
            PatternKind::Name { name, .. } => {
                if name.inner == *query_id {
                    if let Ok(location) = self.loc_to_location(name.loc()) {
                        return Some(location);
                    } else {
                        return None;
                    }
                }
            }
            PatternKind::Tuple(patterns) | PatternKind::Array(patterns) => {
                for pat in patterns {
                    if let Some(location) = self.find_def_in_pattern(&pat, query_id) {
                        return Some(location);
                    }
                }
            }
            PatternKind::Type(_, args) => {
                for arg in args {
                    if let Some(location) = self.find_def_in_pattern(&arg.value, query_id) {
                        return Some(location);
                    }
                }
            }
            PatternKind::Integer(_) | PatternKind::Bool(_) => {}
        }
        None
    }

    pub(self) fn find_member_definition(
        &self,
        type_id: &NameID,
        member_name: &str,
    ) -> Option<Location> {
        let types = &self.item_list.lock().unwrap().types.clone();
        for (_, ty) in types {
            if *ty.inner.name == *type_id {
                match &ty.kind {
                    TypeDeclKind::Struct(s) => {
                        for param in &s.members.0 {
                            if param.name.0 == member_name {
                                if let Ok(location) = self.loc_to_location(param.name.loc()) {
                                    return Some(location);
                                }
                            }
                        }
                    }
                    TypeDeclKind::Enum(_) => {}      // Ignore
                    TypeDeclKind::Primitive(_) => {} // Ignore
                }
            }
        }
        None
    }
}
