use hir::symbol_table::{TypeDeclKind, TypeSymbol};
use local_impl::local_impl;
use spade_ast as ast;
use spade_diagnostics::diag_bail;
use spade_hir as hir;

use crate::{Context, Result, SelfContext};

pub trait IsPort {
    fn is_port(&self, symtab: &Context) -> Result<bool>;
}

impl IsPort for hir::TypeExpression {
    fn is_port(&self, ctx: &Context) -> Result<bool> {
        match self {
            spade_hir::TypeExpression::Integer(_) => Ok(false),
            spade_hir::TypeExpression::String(_) => Ok(false),
            spade_hir::TypeExpression::TypeSpec(s) => s.is_port(ctx),
            spade_hir::TypeExpression::ConstGeneric(_) => Ok(false),
        }
    }
}

impl IsPort for hir::TypeSpec {
    fn is_port(&self, ctx: &Context) -> Result<bool> {
        let result = match self {
            spade_hir::TypeSpec::Declared(name, _) => {
                let symbol = ctx.symtab.type_symbol_by_id(name);

                match &symbol.inner {
                    TypeSymbol::Declared(_, kind) => match kind {
                        TypeDeclKind::Struct { ref is_port } => *is_port,
                        TypeDeclKind::Enum => false,
                        TypeDeclKind::Primitive { ref is_port, .. } => *is_port,
                    },
                    TypeSymbol::GenericArg { traits: _ } => false,
                    TypeSymbol::GenericMeta(_) => false,
                    TypeSymbol::Alias(expr) => expr.is_port(ctx)?,
                }
            }
            spade_hir::TypeSpec::Generic(_) => false,
            spade_hir::TypeSpec::Tuple(unit) if unit.is_empty() => false,
            spade_hir::TypeSpec::Tuple(specs) => specs
                .iter()
                .map(|s| s.is_port(ctx))
                .collect::<Result<Vec<_>>>()?
                .into_iter()
                .all(|x| x),
            spade_hir::TypeSpec::Array { inner, size: _ } => inner.is_port(ctx)?,
            spade_hir::TypeSpec::Inverted(_) => true,
            spade_hir::TypeSpec::Wire(_) => true,
            spade_hir::TypeSpec::TraitSelf(s) => match &ctx.self_ctx {
                SelfContext::FreeStanding => diag_bail!(
                    s,
                    "Called is_port on self type but no self type was present"
                ),
                SelfContext::ImplBlock(target) => target.is_port(ctx)?,
                SelfContext::TraitDefinition(_) => {
                    diag_bail!(s, "Called is_port on self type while in a trait definition")
                }
            },
            spade_hir::TypeSpec::Wildcard(s) => diag_bail!(s, "Calling is_port on wildcard type"),
        };
        Ok(result)
    }
}

pub trait IsInOut {
    fn is_inout(&self, symtab: &Context) -> Result<bool>;
}

impl IsInOut for hir::TypeExpression {
    fn is_inout(&self, ctx: &Context) -> Result<bool> {
        match self {
            spade_hir::TypeExpression::String(_) => Ok(false),
            spade_hir::TypeExpression::Integer(_) => Ok(false),
            spade_hir::TypeExpression::TypeSpec(s) => s.is_inout(ctx),
            spade_hir::TypeExpression::ConstGeneric(_) => Ok(false),
        }
    }
}

impl IsInOut for hir::TypeSpec {
    fn is_inout(&self, ctx: &Context) -> Result<bool> {
        let result = match self {
            spade_hir::TypeSpec::Declared(name, _) => {
                let symbol = ctx.symtab.type_symbol_by_id(name);

                match &symbol.inner {
                    TypeSymbol::Declared(_, kind) => match kind {
                        TypeDeclKind::Struct { .. } => false,
                        TypeDeclKind::Enum => false,
                        TypeDeclKind::Primitive { ref is_inout, .. } => *is_inout,
                    },
                    TypeSymbol::GenericArg { .. } => false,
                    TypeSymbol::GenericMeta(_) => false,
                    TypeSymbol::Alias(expr) => expr.is_inout(ctx)?,
                }
            }
            spade_hir::TypeSpec::Generic(_) => false,
            spade_hir::TypeSpec::Tuple(_) => false,
            spade_hir::TypeSpec::Array { .. } => false,
            spade_hir::TypeSpec::Inverted(_) => false,
            spade_hir::TypeSpec::Wire(_) => false,
            spade_hir::TypeSpec::TraitSelf(s) => match &ctx.self_ctx {
                SelfContext::FreeStanding => diag_bail!(
                    s,
                    "Called is_inout on self type but no self type was present"
                ),
                SelfContext::ImplBlock(target) => target.is_inout(ctx)?,
                SelfContext::TraitDefinition(_) => {
                    diag_bail!(
                        s,
                        "Called is_inout on self type while in a trait definition"
                    )
                }
            },
            spade_hir::TypeSpec::Wildcard(s) => diag_bail!(s, "Calling is_inout on wildcard type"),
        };
        Ok(result)
    }
}

#[local_impl]
impl IsSelf for ast::TypeSpec {
    fn is_self(&self) -> Result<bool> {
        match self {
            ast::TypeSpec::Named(path, _) => {
                let path = &path.inner.0;
                Ok(path.len() == 1 && path.first().is_some_and(|ident| ident.inner.0 == "Self"))
            }
            _ => Ok(false),
        }
    }
}
