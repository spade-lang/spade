use local_impl::local_impl;
use spade_ast::UnitKind;
use spade_common::location_info::Loc;
use spade_diagnostics::Diagnostic;

fn not_allowed_in_function(message: &str, at: Loc<()>, what: &str, kw_loc: Loc<()>) -> Diagnostic {
    Diagnostic::error(at, message)
        .primary_label(format!("{what} not allowed here"))
        .secondary_label(kw_loc, "this is a function")
        .note("functions can only contain combinatorial logic")
        .span_suggest_replace("consider making the function an entity", kw_loc, "entity")
}

fn not_allowed_in_fsm(message: &str, at: Loc<()>, what: &str, kw_loc: Loc<()>) -> Diagnostic {
    Diagnostic::error(at, message)
        .primary_label(format!("{what} not allowed here"))
        .secondary_label(kw_loc, "this is an FSM")
        .note("describe control flow, not structural hardware")
}

fn bug_no_item_context(at: Loc<()>) -> Diagnostic {
    Diagnostic::bug(
        at,
        "attempted to parse something which requires an item context, but no item context exists",
    )
}

fn stage_ref_in(what: &str, at: Loc<()>, kw_loc: Loc<()>) -> Diagnostic {
    Diagnostic::error(at, format!("pipeline stage reference in {what}"))
        .primary_label("pipeline stage reference not allowed here")
        .secondary_label(kw_loc, format!("this is a {what}"))
        .note("only pipelines can contain pipeline stage references")
        .span_suggest_replace(
            format!("consider making the {} a pipeline", what),
            kw_loc,
            "pipeline(/* depth */)",
        )
}

#[local_impl]
impl UnitKindLocal for Option<Loc<UnitKind>> {
    fn allows_reg(&self, at: Loc<()>) -> Result<(), Diagnostic> {
        match self.as_ref().map(|x| x.split_loc_ref()) {
            Some((UnitKind::Function, kw_loc)) => Err(not_allowed_in_function(
                "register declared in function",
                at,
                "register",
                kw_loc,
            )),
            Some((UnitKind::Fsm, kw_loc)) => Err(not_allowed_in_fsm(
                "register declared in fsm",
                at,
                "register",
                kw_loc,
            )),
            Some((UnitKind::Entity | UnitKind::Pipeline(_), _)) => Ok(()),
            None => Err(bug_no_item_context(at)),
        }
    }

    fn allows_inst(&self, at: Loc<()>) -> Result<(), Diagnostic> {
        match self.as_ref().map(|x| x.split_loc_ref()) {
            // FIXME: Choose "entities" or "pipelines" depending on what we try to instantiate
            Some((UnitKind::Function, kw_loc)) => Err(not_allowed_in_function(
                "cannot instantiate entities and pipelines in functions",
                at,
                "inst",
                kw_loc,
            )),
            Some((UnitKind::Fsm, kw_loc)) => Err(not_allowed_in_fsm(
                "cannot instantiate entities and pipelines in FSMs",
                at,
                "inst",
                kw_loc,
            )),
            Some((UnitKind::Entity | UnitKind::Pipeline(_), _)) => Ok(()),
            None => Err(bug_no_item_context(at)),
        }
    }

    fn allows_pipeline_ref(&self, at: Loc<()>) -> Result<(), Diagnostic> {
        match self.as_ref().map(|x| x.split_loc_ref()) {
            Some((UnitKind::Function, kw_loc)) => Err(stage_ref_in("function", at, kw_loc)),
            Some((UnitKind::Entity, kw_loc)) => Err(stage_ref_in("entity", at, kw_loc)),
            Some((UnitKind::Fsm, kw_loc)) => Err(stage_ref_in("fsm", at, kw_loc)),
            Some((UnitKind::Pipeline(_), _)) => Ok(()),
            None => Err(bug_no_item_context(at)),
        }
    }
}
