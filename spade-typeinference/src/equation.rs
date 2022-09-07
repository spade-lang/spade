use std::collections::HashMap;

use serde::{Deserialize, Serialize};
use spade_common::{location_info::WithLocation, name::NameID};
use spade_types::KnownType;

pub type TypeEquations = HashMap<TypedExpression, TypeVar>;

/// A type variable represents the type of something in the program. It is mapped
/// to expressions by type equations in the TypeState.
///
/// When TypeVars are passed externally into TypeState, they must be checked for replacement,
/// as the type inference process might have refined them.
#[derive(Debug, Clone, PartialEq, Hash, Eq)]
pub enum TypeVar {
    /// The base type is known and has a list of parameters
    Known(KnownType, Vec<TypeVar>),
    Tuple(Vec<TypeVar>),
    Array {
        inner: Box<TypeVar>,
        size: Box<TypeVar>,
    },
    /// The type is completely unknown
    Unknown(u64),
    Backward(Box<TypeVar>),
    Wire(Box<TypeVar>),
}

impl WithLocation for TypeVar {}

impl std::fmt::Display for TypeVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeVar::Known(t, params) => {
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
            TypeVar::Tuple(inner) => {
                write!(
                    f,
                    "({})",
                    inner
                        .iter()
                        .map(|t| format!("{}", t))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            TypeVar::Array { inner, size } => {
                write!(f, "[{}; {}]", inner, size)
            }
            TypeVar::Unknown(_) => write!(f, "_"),
            TypeVar::Backward(inner) => write!(f, "&mut {inner}"),
            TypeVar::Wire(inner) => write!(f, "&{inner}"),
        }
    }
}

#[derive(Eq, PartialEq, Hash, Debug, Clone, Serialize, Deserialize)]
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
                write!(f, "{}#{}", p, p.0)
            }
        }
    }
}
