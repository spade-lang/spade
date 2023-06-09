use std::collections::HashMap;

use num::BigInt;
use serde::{Deserialize, Serialize};
use spade_common::{location_info::WithLocation, name::NameID};
use spade_types::KnownType;

pub type TypeEquations = HashMap<TypedExpression, TypeVar>;

/// A type variable represents the type of something in the program. It is mapped
/// to expressions by type equations in the TypeState.
///
/// When TypeVars are passed externally into TypeState, they must be checked for replacement,
/// as the type inference process might have refined them.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
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
    Inverted(Box<TypeVar>),
}

impl WithLocation for TypeVar {}

impl TypeVar {
    pub fn expect_known<T, U, K, O>(&self, on_known: K, on_unknown: U, on_other: O) -> T
    where
        U: FnOnce() -> T,
        K: FnOnce(&KnownType, &[TypeVar]) -> T,
        O: FnOnce(&TypeVar) -> T,
    {
        match self {
            TypeVar::Unknown(_) => on_unknown(),
            TypeVar::Known(k, v) => on_known(k, v),
            other => on_other(other),
        }
    }

    pub fn expect_named<T, U, K, O>(&self, on_named: K, on_unknown: U, on_other: O) -> T
    where
        U: FnOnce() -> T,
        K: FnOnce(&NameID, &[TypeVar]) -> T,
        O: FnOnce(&TypeVar) -> T,
    {
        match self {
            TypeVar::Unknown(_) => on_unknown(),
            TypeVar::Known(KnownType::Type(name), params) => on_named(name, params),
            other => on_other(other),
        }
    }

    /// Expect a named type, or TypeVar::Inverted(named), or a recursive inversion.
    /// inverted_now is stateful and used to track if we are currently in an
    /// inverted context.
    /// The first argument of the on_named function specifies whether or not
    /// the final named type we found was inverted or not. I.e. if we ran it on
    /// `~T`, it would be called with (true, T), and if we ran it on `T` it would
    /// be called with `(false, T)`
    pub fn expect_named_or_inverted<T, U, K, O>(
        &self,
        inverted_now: bool,
        on_named: K,
        on_unknown: U,
        on_other: O,
    ) -> T
    where
        U: FnOnce() -> T,
        K: FnOnce(bool, &NameID, &[TypeVar]) -> T,
        O: FnOnce(&TypeVar) -> T,
    {
        match self {
            TypeVar::Unknown(_) => on_unknown(),
            TypeVar::Known(KnownType::Type(name), params) => on_named(inverted_now, name, params),
            TypeVar::Inverted(inner) => {
                inner.expect_named_or_inverted(!inverted_now, on_named, on_unknown, on_other)
            }
            other => on_other(other),
        }
    }

    pub fn expect_specific_named<T, U, K, O>(
        &self,
        name: NameID,
        on_correct: K,
        on_unknown: U,
        on_other: O,
    ) -> T
    where
        U: FnOnce() -> T,
        K: FnOnce(&[TypeVar]) -> T,
        O: FnOnce(&TypeVar) -> T,
    {
        match self {
            TypeVar::Unknown(_) => on_unknown(),
            TypeVar::Known(k, v) if k == &KnownType::Type(name) => on_correct(v),
            other => on_other(other),
        }
    }

    /// Assumes that this type is KnownType::Integer(size) and calls on_integer then. Otherwise
    /// calls on_unknown or on_other depending on the type. If the integer is given type params,
    /// panics
    pub fn expect_integer<T, U, K, O>(&self, on_integer: K, on_unknown: U, on_other: O) -> T
    where
        U: FnOnce() -> T,
        K: FnOnce(BigInt) -> T,
        O: FnOnce(&TypeVar) -> T,
    {
        match self {
            TypeVar::Known(KnownType::Integer(size), params) => {
                assert!(params.is_empty());
                on_integer(size.clone())
            }
            TypeVar::Unknown(_) => on_unknown(),
            other => on_other(other),
        }
    }
}

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
            TypeVar::Inverted(inner) => write!(f, "~{inner}"),
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
