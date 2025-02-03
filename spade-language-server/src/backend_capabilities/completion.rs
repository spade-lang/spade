use async_recursion::async_recursion;
use camino::Utf8PathBuf;
use spade_common::location_info::Loc;
use spade_hir::{
    ExecutableItem, ExprKind, Expression, ImplTarget, Pattern, PatternKind, Statement,
    TypeDeclKind, TypeDeclaration, Unit,
};
use tower_lsp::lsp_types::{CompletionContext, CompletionItem, CompletionItemKind, Position, Url};

use crate::backend::ServerBackend;

use super::spade_symbol::SpadeSymbol;

fn new_comp(label: &str, detail: &str, kind: CompletionItemKind) -> CompletionItem {
    let mut comp = CompletionItem::new_simple(label.to_string(), detail.to_string());
    comp.kind = Some(kind);

    comp
}

pub trait Completion {
    async fn get_completions(
        &self,
        pos: &Position,
        uri: &Url,
        context: Option<CompletionContext>,
    ) -> Vec<CompletionItem>;
}

fn parse_lhs(line: &str, character: u32) -> &str {
    line[..(character as usize - 1)]
        .split(" ")
        .last()
        .unwrap_or("")
        .split(".")
        .last()
        .unwrap_or("")
}

fn is_member_completion(line: &str, character: u32) -> bool {
    for (i, c) in line.chars().enumerate() {
        if i >= character as usize {
            break;
        }

        if c == '.' {
            return true;
        }
    }

    false
}

impl Completion for ServerBackend {
    async fn get_completions(
        &self,
        pos: &Position,
        uri: &Url,
        context: Option<CompletionContext>,
    ) -> Vec<CompletionItem> {
        let path = Utf8PathBuf::from(uri.path().to_string())
            .canonicalize_utf8()
            .unwrap();

        self.try_compile(&path, None).await;

        let trigger_char = if let Some(context) = context {
            context.trigger_character.unwrap_or("".to_string())
        } else {
            "".to_string()
        };

        let code = self.code.lock().unwrap().clone();
        let current_file = code
            .dump_files()
            .into_iter()
            .find_map(|(file_name, contents)| {
                if file_name == uri.path() {
                    Some(contents)
                } else {
                    None
                }
            });

        let current_line = current_file
            .unwrap()
            .lines()
            .nth(pos.line as usize)
            .unwrap()
            .to_owned();

        if trigger_char == "." || is_member_completion(&current_line, pos.character) {
            let lhs = parse_lhs(&current_line, pos.character);
            self.get_member_completions(&pos, &uri, &lhs).await
        } else {
            [
                self.fold_comps(&pos, &uri).await,
                self.keyword_completions.to_vec(),
            ]
            .concat()
        }
    }
}

impl ServerBackend {
    async fn get_member_completions(
        &self,
        pos: &Position,
        uri: &Url,
        parent: &str,
    ) -> Vec<CompletionItem> {
        self.fold_memb_comps(pos, uri, parent).await
    }

    async fn trim_name(&self, name: &str, loc: &Loc<()>, uri: &Url) -> String {
        if !self.in_same_file(uri, loc).unwrap_or(false) {
            name.to_string()
        } else {
            name.to_string()
                .split("::")
                .last()
                .unwrap_or("")
                .to_string()
        }
    }

    pub(self) async fn fold_comps(&self, pos: &Position, uri: &Url) -> Vec<CompletionItem> {
        let mut comps: Vec<CompletionItem> = vec![];

        let types = &self.item_list.lock().unwrap().types.clone();
        for (_, td) in types {
            comps.append(&mut self.fold_comps_td(td, pos, uri).await);
        }

        let executables = &self.item_list.lock().unwrap().executables.clone();
        for (_, item) in executables {
            match item {
                ExecutableItem::Unit(u) => {
                    comps.append(&mut self.fold_comps_unit(u, pos, uri).await);
                }
                ExecutableItem::BuiltinUnit(_, _) => {} // FIXME
                ExecutableItem::EnumInstance { .. } => {} // FIXME
                ExecutableItem::StructInstance => {}    // FIXME
            }
        }

        comps
    }

    async fn fold_comps_td(
        &self,
        td: &Loc<TypeDeclaration>,
        _pos: &Position,
        uri: &Url,
    ) -> Vec<CompletionItem> {
        let kind = match td.kind {
            TypeDeclKind::Enum(_) => CompletionItemKind::ENUM,
            TypeDeclKind::Struct(_) => CompletionItemKind::STRUCT,
            TypeDeclKind::Primitive(_) => CompletionItemKind::STRUCT,
        };
        vec![new_comp(
            &self.trim_name(&td.name.to_string(), &td.loc(), uri).await,
            "type",
            kind,
        )]
    }

    #[async_recursion]
    async fn fold_comps_unit(
        &self,
        unit: &Loc<Unit>,
        pos: &Position,
        uri: &Url,
    ) -> Vec<CompletionItem> {
        let Unit {
            name,
            inputs,
            head,
            body,
            ..
        } = &unit.inner;

        let mut comps = vec![];

        // Add non method unit names to the completion
        if !name.to_string().contains("impl_") {
            comps.push(new_comp(
                &self
                    .trim_name(&head.name.to_string(), &head.name.loc(), uri)
                    .await,
                "unit",
                CompletionItemKind::FUNCTION,
            ));
        }

        // If were in the unit add unit inputs to the completion
        if self.pos_in_loc(&unit.loc(), pos) {
            for (name, _ts) in inputs {
                comps.push(new_comp(
                    &self.trim_name(&name.to_string(), &name.loc(), uri).await,
                    "variable",
                    CompletionItemKind::VARIABLE,
                ));
            }
        }

        // Fold in unit body completions
        comps.append(&mut self.fold_comps_expr(body, pos, uri).await);

        comps
    }
    #[async_recursion]
    async fn fold_comps_expr(
        &self,
        expr: &Loc<Expression>,
        pos: &Position,
        uri: &Url,
    ) -> Vec<CompletionItem> {
        let mut comps = vec![];
        if !self.pos_in_loc(&expr.loc(), pos) {
            return comps;
        }

        match &expr.kind {
            ExprKind::Identifier(_name_id) | ExprKind::TypeLevelInteger(_name_id) => {}
            ExprKind::TupleLiteral(_list) | ExprKind::ArrayLiteral(_list) => {}
            ExprKind::ArrayShorthandLiteral(_, _) => {}
            ExprKind::Index(_lhs, _rhs) => {}
            ExprKind::RangeIndex {
                target: _target, ..
            } => {}
            ExprKind::TupleIndex(_lhs, _) => {}
            ExprKind::FieldAccess(_expr, _ident) => {}
            ExprKind::Call {
                kind: _kind,
                callee: _callee,
                args: _args,
                turbofish: _turbofish,
            } => {}
            ExprKind::MethodCall {
                target: _target,
                name: _name,
                args: _args,
                call_kind: _kind,
                turbofish: _turbofish,
            } => {}
            ExprKind::BinaryOperator(_lhs, _, _rhs) => {}
            ExprKind::UnaryOperator(_, _operand) => {}
            ExprKind::Match(_expr, _arms) => {}
            ExprKind::If(_expr1, _expr2, _expr3) => {}
            ExprKind::TypeLevelIf(_expr1, _expr2, _expr3) => {}
            ExprKind::Block(block) => {
                for s in &block.statements {
                    comps.append(&mut self.fold_comps_stat(s, pos, uri).await);
                }
            }
            ExprKind::PipelineRef { name: _name, .. } => {}
            ExprKind::IntLiteral(_, _)
            | ExprKind::BitLiteral(_)
            | ExprKind::BoolLiteral(_)
            | ExprKind::CreatePorts
            | ExprKind::StageValid
            | ExprKind::StageReady
            | ExprKind::Null => {} // Ignore all of these
        }

        comps
    }
    #[async_recursion]
    async fn fold_comps_stat(
        &self,
        stat: &Loc<Statement>,
        pos: &Position,
        uri: &Url,
    ) -> Vec<CompletionItem> {
        let mut comps = vec![];
        if !self.pos_after_loc(&stat.loc(), pos).unwrap_or(false) {
            return comps;
        }
        match &stat.inner {
            Statement::Binding(binding) => {
                comps.append(&mut self.fold_comps_pat(&binding.pattern, pos, uri).await);
            }
            Statement::Register(_register) => {}
            Statement::Set {
                target: _target,
                value: _value,
            } => {}
            Statement::Assert(_expr) => {}
            Statement::PipelineRegMarker(_expr) => {}
            Statement::Declaration(_) => {}     // FIXME
            Statement::WalSuffixed { .. } => {} // FIXME
            Statement::Label { .. } => {}       // FIXME
        }
        comps
    }
    #[async_recursion]
    async fn fold_comps_pat(
        &self,
        pat: &Loc<Pattern>,
        pos: &Position,
        uri: &Url,
    ) -> Vec<CompletionItem> {
        let mut comps = vec![];
        match &pat.inner.kind {
            PatternKind::Integer(_) | PatternKind::Bool(_) => {}
            PatternKind::Name {
                name,
                pre_declared: _pre_declared,
            } => {
                comps.push(CompletionItem::new_simple(
                    name.to_string()
                        .split("::")
                        .last()
                        .unwrap_or("")
                        .to_string(),
                    "local var".to_string(),
                ));
            }
            PatternKind::Tuple(patterns) | PatternKind::Array(patterns) => {
                for pat in patterns {
                    comps.append(&mut self.fold_comps_pat(pat, pos, uri).await);
                }
            }
            PatternKind::Type(_, _) => {}
        }
        comps
    }
}

impl ServerBackend {
    pub(self) async fn fold_memb_comps(
        &self,
        pos: &Position,
        uri: &Url,
        parent: &str,
    ) -> Vec<CompletionItem> {
        let mut comps = vec![];

        let pos_before_dot = Position::new(pos.line, pos.character - 1);

        let parent_symbol = self.find_symbol_named(pos, uri, parent);

        match parent_symbol {
            Some(SpadeSymbol::Variable { var_type, .. }) | Some(SpadeSymbol::Type(var_type)) => {
                let td = self
                    .item_list
                    .lock()
                    .unwrap()
                    .types
                    .iter()
                    .find_map(|(_, td)| {
                        if td.name.inner == var_type {
                            Some(td.clone())
                        } else {
                            None
                        }
                    });

                if let Some(td) = td {
                    comps.append(&mut self.fold_td_members(&td, &pos_before_dot, uri).await);
                }
            }
            _ => {}
        }

        comps
    }

    async fn fold_td_members(
        &self,
        td: &Loc<TypeDeclaration>,
        _pos: &Position,
        _uri: &Url,
    ) -> Vec<CompletionItem> {
        let mut comps = vec![];
        match &td.kind {
            TypeDeclKind::Struct(s) => {
                for member in &s.members.0 {
                    comps.push(new_comp(
                        &member.name.0,
                        "member",
                        CompletionItemKind::FIELD,
                    ));
                }
            }
            TypeDeclKind::Enum(_) => {}
            TypeDeclKind::Primitive(_) => {}
        };

        for (id, impls_map) in self.item_list.lock().unwrap().impls.clone() {
            if ImplTarget::Named(td.name.inner.clone()) == id {
                for (_, imp_block) in impls_map {
                    for (ident, _) in &imp_block.fns {
                        comps.push(new_comp(&ident.0, "method", CompletionItemKind::METHOD));
                    }
                }
            }
        }

        comps
    }
}
