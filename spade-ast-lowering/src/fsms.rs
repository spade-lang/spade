use spade_ast as ast;
use spade_common::location_info::Loc;
use spade_diagnostics::Diagnostic;
use spade_hir as hir;

use crate::{comptime::ComptimeCondExt, error::Result, Context};

pub fn maybe_check_fsm_requirements(
    unit: &Loc<ast::Unit>,
    head: &Loc<hir::UnitHead>,
    _ctx: &mut Context,
) -> Result<()> {
    let ast::Unit {
        head:
            ast::UnitHead {
                unit_kind,
                inputs: ast_inputs,
                ..
            },
        body: _,
    } = &unit.inner;

    match &unit_kind.inner {
        ast::UnitKind::Function => {}
        ast::UnitKind::Entity => {}
        ast::UnitKind::Pipeline(_) => {}
        ast::UnitKind::Fsm => {
            if head.inputs.0.len() == 1 {
                return Err(Diagnostic::error(ast_inputs.loc(), "Missing reset for fsm")
                    .note("All FSMs need to take a reset as the second argument")
                    .span_suggest_insert_after(
                        "Consider adding the reset",
                        &ast_inputs.inner.args[0].2,
                        ", rst: bool",
                    ));
            }
            if head.inputs.0.len() == 0 {
                return Err(
                    Diagnostic::error(ast_inputs.loc(), "Missing clock and reset for fsm")
                        .note("All FSMs need to take a clock and a reset")
                        .span_suggest_replace(
                            "Consider adding the clock and reset",
                            ast_inputs,
                            "(clock: clk, rst: bool)",
                        ),
                );
            }
        }
    };

    Ok(())
}
