use parse_tree_macros::trace_typechecker;
use spade_common::location_info::WithLocation;
use spade_hir::symbol_table::SymbolTable;
use spade_hir::Pipeline;

use crate::result::UnificationErrorExt;
use crate::GenericListSource;
use crate::{equation::TypedExpression, fixed_types::t_clock, result::Error};

use super::{Result, TraceStackEntry, TypeState};

impl TypeState {
    #[trace_typechecker]
    pub fn visit_pipeline(&mut self, pipeline: &Pipeline, symtab: &SymbolTable) -> Result<()> {
        let Pipeline {
            head,
            name: _,
            inputs,
            body,
        } = pipeline;
        let generic_list = self.create_generic_list(
            GenericListSource::Definition(&pipeline.name.name_id().inner),
            &pipeline.head.type_params,
        );

        // Add an equation for the clock
        let input_tvar = self.type_var_from_hir(&inputs[0].1.inner, &generic_list);
        self.add_equation(TypedExpression::Name(inputs[0].0.clone().inner), input_tvar);
        self.unify(
            &TypedExpression::Name(inputs[0].0.clone().inner),
            &t_clock(symtab),
            symtab,
        )
        .map_normal_err(|(got, expected)| Error::FirstPipelineArgNotClock {
            expected,
            spec: got.at_loc(&inputs[0].1.loc()),
        })?;

        // Add equations for the inputs
        for (name, t) in inputs.iter().skip(1) {
            let tvar = self.type_var_from_hir(t, &generic_list);
            self.add_equation(TypedExpression::Name(name.clone().inner), tvar);
        }

        self.visit_expression(&body, symtab, &generic_list)?;

        // Ensure that the output type matches what the user specified, and unit otherwise
        if let Some(output_type) = &head.output_type {
            let tvar = self.type_var_from_hir(&output_type, &generic_list);
            self.unify(&TypedExpression::Id(body.inner.id), &tvar, symtab)
                .map_normal_err(|(got, expected)| Error::EntityOutputTypeMismatch {
                    expected,
                    got,
                    type_spec: output_type.loc(),
                    output_expr: body.loc(),
                })?;
        } else {
            todo!("Support unit types")
            // self.unify_types(
            //     &TypedExpression::Id(entity.body.inner.id),
            //     &TypeVar::Known(KnownType::Type(BaseType::Unit), vec![], None),
            // )
            // .map_err(|(got, expected)| Error::UnspecedEntityOutputTypeMismatch {
            //     expected,
            //     got,
            //     output_expr: entity.body.loc(),
            // })?;
        }

        self.check_requirements(symtab)?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::{format_trace_stack, hir};
    use hir::Block;
    use hir::ItemList;
    use hir::{dtype, testutil::t_num, ExprKind};
    use spade_ast::testutil::ast_ident;
    use spade_ast::testutil::ast_path;
    use spade_common::location_info::WithLocation;
    use spade_common::name::testutil::name_id;
    use spade_hir::symbol_table::SymbolTable;

    #[test]
    fn pipeline_first_argument_is_clock() {
        // Add the head to the symtab
        let mut symtab = SymbolTable::new();
        spade_ast_lowering::builtins::populate_symtab(&mut symtab, &mut ItemList::new());

        // Add the entity to the symtab
        let pipeline = Pipeline {
            name: hir::UnitName::WithID(name_id(0, "pipe")),
            head: hir::PipelineHead {
                depth: 3.nowhere(),
                inputs: hir::ParameterList(vec![(ast_ident("clk"), dtype!(symtab => "bool"))]),
                output_type: Some(dtype!(symtab => "int"; (t_num(5)))),
                type_params: vec![],
            },
            body: ExprKind::Block(Box::new(Block {
                statements: vec![],
                result: ExprKind::IntLiteral(0).idless().nowhere(),
            }))
            .idless()
            .nowhere(),
            inputs: vec![(name_id(0, "clk"), dtype!(symtab => "bool"))],
        };

        let mut state = TypeState::new();

        match state.visit_pipeline(&pipeline, &symtab) {
            Err(Error::FirstPipelineArgNotClock { .. }) => {}
            other => {
                println!("{}", format_trace_stack(&state.trace_stack));
                panic!("Expected FirstPipelineArgNotClock, got {:?}", other)
            }
        }
    }
}
