use std::collections::HashMap;

use crate::types::KnownType;
use crate::{hir::NameID, location_info::Loc};

pub type TypeEquations = HashMap<TypedExpression, TypeVar>;

#[derive(Debug, Clone)]
pub enum TypeVar {
    /// The type is known. If the type is known through a type signature specified by
    /// the user, that signature is the second argument, otherwise None
    Known(KnownType, Vec<TypeVar>, Option<Loc<()>>),
    /// The type is completely unknown
    Generic(u64),
}

impl std::fmt::Display for TypeVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeVar::Known(t, params, _) => {
                let generics = if params.is_empty() {
                    format!("")
                } else {
                    format!(
                        "<{}>",
                        params
                            .iter()
                            .map(|p| format!("{}", p))
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                };
                write!(f, "{}{}", t, generics)
            }
            TypeVar::Generic(id) => write!(f, "t{}", id),
        }
    }
}

impl PartialEq for TypeVar {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (TypeVar::Known(t1, p1, _), TypeVar::Known(t2, p2, _)) => t1 == t2 && p1 == p2,
            (TypeVar::Known(_, _, _), TypeVar::Generic(_)) => false,
            (TypeVar::Generic(_), TypeVar::Known(_, _, _)) => false,
            (TypeVar::Generic(t1), TypeVar::Generic(t2)) => t1 == t2,
        }
    }
}

#[derive(Eq, PartialEq, Hash, Debug, Clone)]
pub enum TypedExpression {
    Id(u64),
    Name(NameID),
}

impl std::fmt::Display for TypedExpression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypedExpression::Id(i) => {
                write!(f, "%{}", i)
            }
            TypedExpression::Name(p) => {
                write!(f, "{}", p)
            }
        }
    }
}
