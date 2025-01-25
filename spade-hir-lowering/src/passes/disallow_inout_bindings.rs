use spade_common::location_info::Loc;
use spade_diagnostics::Diagnostic;
use spade_hir::{symbol_table::FrozenSymtab, Binding, ItemList, Parameter, Register};
use spade_typeinference::TypeState;
use spade_types::PrimitiveType;

use super::pass::Pass;

pub struct InOutChecks<'a> {
    pub type_state: &'a TypeState,
    pub items: &'a ItemList,
    pub symtab: &'a FrozenSymtab,
}

impl<'a> Pass for InOutChecks<'a> {
    fn visit_unit(&mut self, unit: &mut spade_hir::Unit) -> crate::error::Result<()> {
        // NOTE: the check for complete types is done after this pass is run
        // but if an incomplete type is present at this point, we can skip
        // this check for now and just let the next step fail.
        // FIXME: A better option may be to have a pass that checks
        // for incomplete types, in the monomorphization stage
        let ty =
            self.type_state
                .concrete_type_of(&unit.body, self.symtab.symtab(), &self.items.types);
        match ty {
            Ok(spade_types::ConcreteType::Single {
                base: PrimitiveType::InOut,
                params: _,
            }) => {
                return Err(Diagnostic::error(
                    &unit.body,
                    "Values of inout type cannot be returned",
                )
                .primary_label("returning inout value")
                .help("inout values can only be passed along to other modules as inputs"))
            }
            _ => {}
        }

        for (
            Parameter {
                no_mangle,
                name: _,
                ty: _,
            },
            (name, _ty),
        ) in unit.head.inputs.inner.0.iter().zip(&unit.inputs)
        {
            let ty =
                self.type_state
                    .concrete_type_of(name, self.symtab.symtab(), &self.items.types);

            match (no_mangle, ty) {
                (
                    None,
                    Ok(spade_types::ConcreteType::Single {
                        base: PrimitiveType::InOut,
                        params: _,
                    }),
                ) => {
                    return Err(Diagnostic::error(
                        name,
                        "inout parameters must be marked #[no_mangle]",
                    )
                    .primary_label("inout parameter must be #[no_mangle]")
                    .span_suggest_insert_before(
                        "Consider making the input #[no_mangle]",
                        name,
                        "#[no_mangle] ",
                    ))
                }
                _ => {}
            }
        }

        Ok(())
    }

    fn visit_expression(
        &mut self,
        expression: &mut Loc<spade_hir::Expression>,
    ) -> crate::error::Result<()> {
        match &expression.kind {
            spade_hir::ExprKind::Block(b) => {
                for stmt in &b.statements {
                    match &stmt.inner {
                        spade_hir::Statement::Binding(Binding { pattern, .. })
                        | spade_hir::Statement::Register(Register { pattern, .. }) => {
                            // NOTE: the check for complete types is done after this pass is run
                            // but if an incomplete type is present at this point, we can skip
                            // this check for now and just let the next step fail.
                            // FIXME: A better option may be to have a pass that checks
                            // for incomplete types, in the monomorphization stage
                            let ty = self.type_state.concrete_type_of(
                                pattern,
                                self.symtab.symtab(),
                                &self.items.types,
                            );
                            match ty {
                                Ok(spade_types::ConcreteType::Single {
                                    base: PrimitiveType::InOut,
                                    params: _,
                                }) => {
                                    return Err(Diagnostic::error(
                                        pattern,
                                        "Values of inout type cannot be bound to names",
                                    )
                                    .primary_label("inout type bound to name")
                                    .help(
                                        "inout values can only be passed along to other modules",
                                    ))
                                }
                                _ => {}
                            }
                        }
                        spade_hir::Statement::Declaration(_)
                        | spade_hir::Statement::PipelineRegMarker(_)
                        | spade_hir::Statement::Label(_)
                        | spade_hir::Statement::Assert(_)
                        | spade_hir::Statement::Expression(_)
                        | spade_hir::Statement::Set { .. }
                        | spade_hir::Statement::WalSuffixed { .. } => {}
                    }
                }
            }
            _ => {}
        }

        Ok(())
    }
}
