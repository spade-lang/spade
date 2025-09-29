use spade_common::location_info::Loc;
use spade_common::name::Identifier;
use spade_hir as hir;
use spade_hir::expression::Safety;
use spade_hir::{ArgumentList, ExprKind, Expression, TypeExpression};

use crate::Context;

pub trait ExprExt {
    fn call_method(
        self,
        method: Loc<&str>,
        turbofish: Option<Loc<ArgumentList<TypeExpression>>>,
        args: Loc<ArgumentList<Expression>>,
        ctx: &mut Context,
    ) -> ExprKind;
}

impl ExprExt for Loc<Expression> {
    fn call_method(
        self,
        method: Loc<&str>,
        turbofish: Option<Loc<ArgumentList<TypeExpression>>>,
        args: Loc<ArgumentList<Expression>>,
        _ctx: &mut Context,
    ) -> ExprKind {
        ExprKind::MethodCall {
            target: Box::new(self),
            name: method.map(|name| Identifier(name.to_string())),
            args,
            call_kind: hir::expression::CallKind::Function,
            turbofish,
            safety: Safety::Default,
        }
    }
}

impl ExprExt for Loc<ExprKind> {
    fn call_method(
        self,
        method: Loc<&str>,
        turbofish: Option<Loc<ArgumentList<TypeExpression>>>,
        args: Loc<ArgumentList<Expression>>,
        ctx: &mut Context,
    ) -> ExprKind {
        self.map_ref(|e| e.clone().with_id(ctx.idtracker.next()))
            .call_method(method, turbofish, args, ctx)
    }
}
