use crate::passes::pass::Pass;
use spade_common::{
    location_info::{Loc, WithLocation},
    name::Identifier,
};
use spade_diagnostics::Diagnostic;
use spade_hir::{
    expression::NamedArgument, symbol_table::FrozenSymtab, ArgumentList, Expression, ItemList,
};
use spade_typeinference::{
    method_resolution::select_method, traits::TraitImplList, HasType, TypeState,
};

pub struct LowerMethods<'a> {
    pub type_state: &'a TypeState,
    pub items: &'a ItemList,
    pub symtab: &'a FrozenSymtab,
    pub impls: &'a TraitImplList,
}

impl<'a> Pass for LowerMethods<'a> {
    fn visit_expression(&mut self, expression: &mut Loc<Expression>) -> crate::error::Result<()> {
        let replacement_kind = match &mut expression.kind {
            spade_hir::ExprKind::MethodCall {
                target: self_,
                target_trait: _,
                name,
                args,
                call_kind,
                // Turbofishes are only important during type inference
                turbofish: _,
                safety,
            } => {
                let self_type = self_.get_type(self.type_state);

                // Method resolution requires fully known types, so we'll do a throwaway MIR
                // conversion here
                self.type_state.concrete_type_of(
                    &self_,
                    self.symtab.symtab(),
                    &self.items.types,
                )?;

                let Some(method) =
                    select_method(self_.loc(), &self_type, name, &self.impls, &self.type_state)?
                else {
                    return Err(Diagnostic::bug(
                        expression.loc(),
                        format!("Incorrect method call. None or Multiple candidates exist for {self_type}", self_type=self_type.display(&self.type_state)),
                    ));
                };

                // Insert self as the first arg
                let args = args.map_ref(|args| {
                    let mut new = args.clone();
                    match &mut new {
                        ArgumentList::Named(list) => list.push(NamedArgument::Full(
                            Identifier::intern("self").nowhere(),
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
                    safety: *safety,
                    verilog_attr_groups: vec![],
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
