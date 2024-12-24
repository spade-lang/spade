use itertools::Itertools;
use std::collections::HashMap;

use num::BigInt;
use serde::{Deserialize, Serialize};
use spade_common::{
    id_tracker::ExprID,
    location_info::{Loc, WithLocation},
    name::NameID,
};
use spade_types::{meta_types::MetaType, KnownType};

use crate::traits::TraitList;

pub type TypeEquations = HashMap<TypedExpression, TypeVar>;

/// A type variable represents the type of something in the program. It is mapped
/// to expressions by type equations in the TypeState.
///
/// When TypeVars are passed externally into TypeState, they must be checked for replacement,
/// as the type inference process might have refined them.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum TypeVar {
    /// The base type is known and has a list of parameters
    Known(Loc<()>, KnownType, Vec<TypeVar>),
    /// The type is unknown, but must satisfy the specified traits. When the generic substitution
    /// is done, the TypeVars will be carried over to the KnownType type vars
    Unknown(Loc<()>, u64, TraitList, MetaType),
}

impl WithLocation for TypeVar {}

impl TypeVar {
    pub fn array(loc: Loc<()>, inner: TypeVar, size: TypeVar) -> Self {
        TypeVar::Known(loc, KnownType::Array, vec![inner, size])
    }

    pub fn tuple(loc: Loc<()>, inner: Vec<TypeVar>) -> Self {
        TypeVar::Known(loc, KnownType::Tuple, inner)
    }

    pub fn unit(loc: Loc<()>) -> Self {
        TypeVar::Known(loc, KnownType::Tuple, Vec::new())
    }

    pub fn wire(loc: Loc<()>, inner: TypeVar) -> Self {
        TypeVar::Known(loc, KnownType::Wire, vec![inner])
    }

    pub fn backward(loc: Loc<()>, inner: TypeVar) -> Self {
        TypeVar::Known(
            loc,
            KnownType::Inverted,
            vec![TypeVar::Known(loc, KnownType::Wire, vec![inner])],
        )
    }

    pub fn inverted(loc: Loc<()>, inner: TypeVar) -> Self {
        TypeVar::Known(loc, KnownType::Inverted, vec![inner])
    }

    pub fn expect_known<T, U, K, O>(&self, on_known: K, on_unknown: U) -> T
    where
        U: FnOnce() -> T,
        K: FnOnce(&KnownType, &[TypeVar]) -> T,
    {
        match self {
            TypeVar::Unknown(_, _, _, _) => on_unknown(),
            TypeVar::Known(_, k, v) => on_known(k, v),
        }
    }

    pub fn expect_named<T, U, K, O>(&self, on_named: K, on_unknown: U, on_other: O) -> T
    where
        U: FnOnce() -> T,
        K: FnOnce(&NameID, &[TypeVar]) -> T,
        O: FnOnce(&TypeVar) -> T,
    {
        match self {
            TypeVar::Unknown(_, _, _, _) => on_unknown(),
            TypeVar::Known(_, KnownType::Named(name), params) => on_named(name, params),
            other => on_other(other),
        }
    }

    /// Expect a named type, or TypeVar::Inverted(named), or a recursive inversion.
    /// inverted_now is stateful and used to track if we are currently in an
    /// inverted context.
    /// The first argument of the on_named function specifies whether or not
    /// the final named type we found was inverted or not. I.e. if we ran it on
    /// `inv T`, it would be called with (true, T), and if we ran it on `T` it would
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
            TypeVar::Unknown(_, _, _, _) => on_unknown(),
            TypeVar::Known(_, KnownType::Inverted, params) => {
                if params.len() != 1 {
                    panic!("Found wire with {} params", params.len())
                }
                params[0].expect_named_or_inverted(!inverted_now, on_named, on_unknown, on_other)
            }
            TypeVar::Known(_, KnownType::Named(name), params) => {
                on_named(inverted_now, name, params)
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
            TypeVar::Unknown(_, _, _, _) => on_unknown(),
            TypeVar::Known(_, k, v) if k == &KnownType::Named(name) => on_correct(v),
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
            TypeVar::Known(_, KnownType::Integer(size), params) => {
                assert!(params.is_empty());
                on_integer(size.clone())
            }
            TypeVar::Unknown(_, _, _, _) => on_unknown(),
            other => on_other(other),
        }
    }

    pub fn display_with_meta(&self, display_meta: bool) -> String {
        match self {
            TypeVar::Known(_, KnownType::Named(t), params) => {
                let generics = if params.is_empty() {
                    String::new()
                } else {
                    format!(
                        "<{}>",
                        params
                            .iter()
                            .map(|p| format!("{}", p.display_with_meta(display_meta)))
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                };
                format!("{}{}", t, generics)
            }
            TypeVar::Known(_, KnownType::Integer(inner), _) => {
                format!("{inner}")
            }
            TypeVar::Known(_, KnownType::Bool(inner), _) => {
                format!("{inner}")
            }
            TypeVar::Known(_, KnownType::Tuple, params) => {
                format!(
                    "({})",
                    params
                        .iter()
                        .map(|t| format!("{}", t.display_with_meta(display_meta)))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            TypeVar::Known(_, KnownType::Array, params) => {
                format!(
                    "[{}; {}]",
                    params[0].display_with_meta(display_meta),
                    params[1].display_with_meta(display_meta)
                )
            }
            TypeVar::Known(_, KnownType::Wire, params) => {
                format!("&{}", params[0].display_with_meta(display_meta))
            }
            TypeVar::Known(_, KnownType::Inverted, params) => {
                format!("inv {}", params[0].display_with_meta(display_meta))
            }
            TypeVar::Unknown(_, _, traits, meta) if traits.inner.is_empty() => {
                if display_meta {
                    format!("{meta}")
                } else {
                    "_".to_string()
                }
            }
            // If we have traits, we know this is a type
            TypeVar::Unknown(_, _, traits, _meta) => {
                format!(
                    "{}",
                    traits
                        .inner
                        .iter()
                        .map(|t| format!("{}", t.display_with_meta(display_meta)))
                        .join("+"),
                )
            }
        }
    }
}

impl std::fmt::Debug for TypeVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeVar::Known(_, KnownType::Named(t), params) => {
                let generics = if params.is_empty() {
                    String::new()
                } else {
                    format!(
                        "<{}>",
                        params
                            .iter()
                            .map(|p| format!("{:?}", p))
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                };
                write!(f, "{}{}", t, generics)
            }
            TypeVar::Known(_, KnownType::Integer(inner), _) => {
                write!(f, "{inner}")
            }
            TypeVar::Known(_, KnownType::Bool(inner), _) => {
                write!(f, "{inner}")
            }
            TypeVar::Known(_, KnownType::Tuple, params) => {
                write!(
                    f,
                    "({})",
                    params
                        .iter()
                        .map(|t| format!("{:?}", t))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            TypeVar::Known(_, KnownType::Array, params) => {
                write!(f, "[{:?}; {:?}]", params[0], params[1])
            }
            TypeVar::Known(_, KnownType::Wire, params) => write!(f, "&{:?}", params[0]),
            TypeVar::Known(_, KnownType::Inverted, params) => write!(f, "inv {:?}", params[0]),
            TypeVar::Unknown(_, id, traits, meta_type) => write!(
                f,
                "t{id}({}, {meta_type})",
                traits.inner.iter().map(|t| format!("{t}")).join("+")
            ),
        }
    }
}

impl std::fmt::Display for TypeVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.display_with_meta(false))
    }
}

#[derive(Eq, PartialEq, Hash, Debug, Clone, Serialize, Deserialize)]
pub enum TypedExpression {
    Id(ExprID),
    Name(NameID),
}

impl WithLocation for TypedExpression {}

impl std::fmt::Display for TypedExpression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypedExpression::Id(i) => {
                write!(f, "%{}", i.0)
            }
            TypedExpression::Name(p) => {
                write!(f, "{}#{}", p, p.0)
            }
        }
    }
}
