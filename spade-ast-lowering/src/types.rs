use hir::symbol_table::{SymbolTable, TypeDeclKind, TypeSymbol};
use local_impl::local_impl;
use spade_ast::{self as ast, TypeExpression};
use spade_hir as hir;

use crate::Result;

pub trait IsPort {
    fn is_port(&self, symtab: &SymbolTable) -> Result<bool>;
}
impl IsPort for TypeExpression {
    fn is_port(&self, symtab: &SymbolTable) -> Result<bool> {
        match self {
            TypeExpression::TypeSpec(s) => s.is_port(symtab),
            TypeExpression::Integer(_) => Ok(false),
            TypeExpression::ConstGeneric(_) => Ok(false),
        }
    }
}

impl IsPort for ast::TypeSpec {
    #[tracing::instrument(skip(symtab))]
    fn is_port(&self, symtab: &SymbolTable) -> Result<bool> {
        match self {
            ast::TypeSpec::Tuple(inner) => {
                for t in inner {
                    if t.is_port(symtab)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            ast::TypeSpec::Array { inner, size: _ } => inner.is_port(symtab),
            ast::TypeSpec::Named(name, _) => {
                let (_, symbol) = symtab.lookup_type_symbol(name)?;

                match &symbol.inner {
                    TypeSymbol::Declared(_, kind) => match kind {
                        TypeDeclKind::Struct { is_port } => Ok(*is_port),
                        TypeDeclKind::Enum => Ok(false),
                        TypeDeclKind::Primitive { is_port } => Ok(*is_port),
                    },
                    TypeSymbol::GenericArg { traits: _ } => Ok(false),
                    TypeSymbol::GenericMeta(_) => Ok(false),
                }
            }
            ast::TypeSpec::Unit(_) => Ok(false),
            ast::TypeSpec::Inverted(_) => Ok(true),
            ast::TypeSpec::Wire(_) => Ok(true),
            ast::TypeSpec::Wildcard => unreachable!("Checking if wildcard type is port"),
        }
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
