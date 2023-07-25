use spade_common::{
    location_info::{Loc, WithLocation},
    name::Identifier,
};
use spade_diagnostics::Diagnostic;
use spade_hir::{
    expression::NamedArgument, symbol_table::FrozenSymtab, ArgumentList, Expression, ItemList,
};
use spade_typeinference::{method_resolution::select_method, HasType, TypeState};

use crate::passes::pass::Pass;

pub struct LowerMethods<'a> {
    pub type_state: &'a TypeState,
    pub items: &'a ItemList,
    pub symtab: &'a FrozenSymtab,
}

impl<'a> Pass for LowerMethods<'a> {
    fn visit_expression(&mut self, expression: &mut Loc<Expression>) -> crate::error::Result<()> {
        let replacement_kind = match &mut expression.kind {
            spade_hir::ExprKind::MethodCall {
                target: self_,
                name,
                args,
                call_kind,
            } => {
                let self_type = self_.get_type(self.type_state).map_err(|e| {
                    Diagnostic::bug(self_.as_ref(), format!("did not find a type ({e})"))
                })?;

                let type_name = self_type.expect_named(
                    |name, _params| Ok(name.clone()),
                    || Err(Diagnostic::bug(self_.as_ref(), "Generic type")),
                    |other| {
                        Err(Diagnostic::bug(
                            self_.as_ref(),
                            format!("{other} cannot have methods"),
                        ))
                    },
                )?;

                let method = select_method(self_.loc(), &type_name, name, self.items)?;

                // Insert self as the first arg
                let args = args.map_ref(|args| {
                    let mut new = args.clone();
                    match &mut new {
                        ArgumentList::Named(list) => list.push(NamedArgument::Full(
                            Identifier(String::from("self")).nowhere(),
                            self_.as_ref().clone(),
                        )),
                        ArgumentList::Positional(list) => list.insert(0, self_.as_ref().clone()),
                    }
                    new
                });

                Some(spade_hir::ExprKind::Call {
                    kind: call_kind.clone(),
                    callee: method.inner.at_loc(name),
                    args: args.clone(),
                    turbofish: None,
                })
            }
            _ => None,
        };

        match replacement_kind {
            Some(new) => expression.kind = new,
            None => {}
        }
        Ok(())
    }

    fn visit_unit(&mut self, _unit: &mut spade_hir::Unit) -> crate::error::Result<()> {
        Ok(())
    }
}
