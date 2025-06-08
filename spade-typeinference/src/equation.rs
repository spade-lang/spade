use itertools::Itertools;
use std::collections::{BTreeMap, HashMap};

use num::BigInt;
use serde::{Deserialize, Serialize};
use spade_common::{
    id_tracker::ExprID,
    location_info::{Loc, WithLocation},
    name::NameID,
};
use spade_types::{meta_types::MetaType, KnownType};

use crate::{
    traits::{TraitList, TraitReq},
    HasType, TypeState,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct TypeVarID {
    pub inner: usize,
    /// Key from the TypeState from which this var originates. See the `key` field
    /// of the type state for details
    pub type_state_key: u64,
}
impl WithLocation for TypeVarID {}

impl TypeVarID {
    pub fn resolve(self, state: &TypeState) -> &TypeVar {
        assert!(
            state.keys.contains(&self.type_state_key),
            "Type var key mismatch. Type states are being mixed incorrectly. Type state has {:?}, var has {}", state.keys, self.type_state_key
        );
        // In case our ID is stale, we'll need to look up the final ID
        let final_id = self.get_type(state);
        state.type_vars.get(final_id.inner).unwrap()
    }

    pub fn replace_inside(
        self,
        from: TypeVarID,
        to: TypeVarID,
        state: &mut TypeState,
    ) -> TypeVarID {
        if self.get_type(state) == from.get_type(state) {
            to
        } else {
            let mut new = self.resolve(state).clone();
            match &mut new {
                TypeVar::Known(_, _known_type, params) => {
                    params
                        .iter_mut()
                        .for_each(|var| *var = var.replace_inside(from, to, state));
                }
                TypeVar::Unknown(_, _, trait_list, _) => {
                    trait_list.inner.iter_mut().for_each(|var| {
                        let TraitReq {
                            name: _,
                            type_params,
                        } = &mut var.inner;

                        type_params
                            .iter_mut()
                            .for_each(|t| *t = t.replace_inside(from, to, state));
                    })
                }
            };

            // NOTE: For performance we could consider not doing replacement if none
            // of the inner types changed. For now, we only use this in diagnostics,
            // so even for performance, it won't make a difference
            new.insert(state)
        }
    }

    pub fn display(self, type_state: &TypeState) -> String {
        self.display_with_meta(false, type_state)
    }

    pub fn display_with_meta(self, meta: bool, type_state: &TypeState) -> String {
        match self.resolve(type_state) {
            TypeVar::Known(_, KnownType::Error, _) => "{unknown}".to_string(),
            TypeVar::Known(_, KnownType::Named(t), params) => {
                let generics = if params.is_empty() {
                    String::new()
                } else {
                    format!(
                        "<{}>",
                        params
                            .iter()
                            .map(|p| format!("{}", p.display_with_meta(meta, type_state)))
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
                        .map(|t| format!("{}", t.display_with_meta(meta, type_state)))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            TypeVar::Known(_, KnownType::Array, params) => {
                format!(
                    "[{}; {}]",
                    params[0].display_with_meta(meta, type_state),
                    params[1].display_with_meta(meta, type_state)
                )
            }
            TypeVar::Known(_, KnownType::Wire, params) => {
                format!("&{}", params[0].display_with_meta(meta, type_state))
            }
            TypeVar::Known(_, KnownType::Inverted, params) => {
                format!("inv {}", params[0].display_with_meta(meta, type_state))
            }
            TypeVar::Unknown(_, _, traits, meta_type) => match meta_type {
                MetaType::Type => {
                    if !traits.inner.is_empty() {
                        traits
                            .inner
                            .iter()
                            .map(|t| t.display_with_meta(meta, type_state))
                            .join(" + ")
                    } else {
                        "_".to_string()
                    }
                }
                _ => {
                    if meta {
                        format!("{}", meta_type)
                    } else {
                        format!("_")
                    }
                }
            },
        }
    }

    pub fn debug_resolve(self, state: &TypeState) -> TypeVarString {
        match self.resolve(state) {
            TypeVar::Known(_, base, params) => {
                let params = if params.is_empty() {
                    "".to_string()
                } else {
                    format!(
                        "<{}>",
                        params.iter().map(|t| t.debug_resolve(state).0).join(", ")
                    )
                };
                let base = match base {
                    KnownType::Named(name_id) => format!("{name_id}"),
                    KnownType::Integer(big_int) => format!("{big_int}"),
                    KnownType::Bool(val) => format!("{val}"),
                    KnownType::Tuple => format!("Tuple"),
                    KnownType::Array => format!("Array"),
                    KnownType::Wire => format!("&"),
                    KnownType::Inverted => format!("inv &"),
                    KnownType::Error => format!("{{error}}"),
                };
                TypeVarString(format!("{base}{params}"), self)
            }
            TypeVar::Unknown(_, id, traits, _meta_type) => {
                let traits = if traits.inner.is_empty() {
                    "".to_string()
                } else {
                    format!(
                        "({})",
                        traits
                            .inner
                            .iter()
                            .map(|t| t.debug_display(state))
                            .join(" + ")
                    )
                };
                TypeVarString(format!("t{id}{traits}"), self)
            }
        }
    }
}

/// A type which which should not be resolved directly but can be used to create new
/// copies with unique type var ids
#[derive(Clone, Copy, Serialize, Deserialize, Eq, PartialEq, PartialOrd, Ord)]
pub struct TemplateTypeVarID {
    inner: TypeVarID,
}

impl TemplateTypeVarID {
    pub fn new(inner: TypeVarID) -> Self {
        Self { inner }
    }

    pub fn make_copy(&self, state: &mut TypeState) -> TypeVarID {
        self.make_copy_with_mapping(state, &mut BTreeMap::new())
    }

    pub fn make_copy_with_mapping(
        &self,
        state: &mut TypeState,
        mapped: &mut BTreeMap<TemplateTypeVarID, TypeVarID>,
    ) -> TypeVarID {
        if let Some(prev) = mapped.get(self) {
            return *prev;
        }

        let new = match self.inner.resolve(state).clone() {
            TypeVar::Known(loc, base, params) => TypeVar::Known(
                loc,
                base,
                params
                    .into_iter()
                    .map(|p| TemplateTypeVarID { inner: p }.make_copy_with_mapping(state, mapped))
                    .collect(),
            ),
            TypeVar::Unknown(loc, id, TraitList { inner: tl }, meta_type) => TypeVar::Unknown(
                loc,
                id,
                TraitList {
                    inner: tl
                        .into_iter()
                        .map(|loc| {
                            loc.map(|req| TraitReq {
                                name: req.name,
                                type_params: req
                                    .type_params
                                    .into_iter()
                                    .map(|p| {
                                        TemplateTypeVarID { inner: p }
                                            .make_copy_with_mapping(state, mapped)
                                    })
                                    .collect(),
                            })
                        })
                        .collect(),
                },
                meta_type,
            ),
        };
        let result = state.add_type_var(new);
        mapped.insert(*self, result);
        result
    }
}

pub type TypeEquations = HashMap<TypedExpression, TypeVarID>;

/// A frozen TypeVar that can be printed for debugging purposes
#[derive(Debug, Clone)]
pub struct TypeVarString(pub String, pub TypeVarID);

impl std::fmt::Display for TypeVarString {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// A type variable represents the type of something in the program. It is mapped
/// to expressions by type equations in the TypeState.
///
/// When TypeVars are passed externally into TypeState, they must be checked for replacement,
/// as the type inference process might have refined them.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize, Debug)]
pub enum TypeVar {
    /// The base type is known and has a list of parameters
    Known(Loc<()>, KnownType, Vec<TypeVarID>),
    /// The type is unknown, but must satisfy the specified traits. When the generic substitution
    /// is done, the TypeVars will be carried over to the KnownType type vars
    Unknown(Loc<()>, u64, TraitList, MetaType),
}

impl WithLocation for TypeVar {}

impl TypeVar {
    pub fn into_known(&self, type_state: &TypeState) -> Option<KnownTypeVar> {
        match self {
            TypeVar::Known(loc, base, params) => Some(KnownTypeVar(
                loc.clone(),
                base.clone(),
                params
                    .iter()
                    .map(|t| t.resolve(type_state).into_known(type_state))
                    .collect::<Option<_>>()?,
            )),
            TypeVar::Unknown(_, _, _, _) => None,
        }
    }

    pub fn insert(self, into: &mut TypeState) -> TypeVarID {
        into.add_type_var(self)
    }

    pub fn array(loc: Loc<()>, inner: TypeVarID, size: TypeVarID) -> Self {
        TypeVar::Known(loc, KnownType::Array, vec![inner, size])
    }

    pub fn tuple(loc: Loc<()>, inner: Vec<TypeVarID>) -> Self {
        TypeVar::Known(loc, KnownType::Tuple, inner)
    }

    pub fn unit(loc: Loc<()>) -> Self {
        TypeVar::Known(loc, KnownType::Tuple, Vec::new())
    }

    pub fn wire(loc: Loc<()>, inner: TypeVarID) -> Self {
        TypeVar::Known(loc, KnownType::Wire, vec![inner])
    }

    pub fn backward(loc: Loc<()>, inner: TypeVarID, type_state: &mut TypeState) -> Self {
        TypeVar::Known(
            loc,
            KnownType::Inverted,
            vec![type_state.add_type_var(TypeVar::Known(loc, KnownType::Wire, vec![inner]))],
        )
    }

    pub fn inverted(loc: Loc<()>, inner: TypeVarID) -> Self {
        TypeVar::Known(loc, KnownType::Inverted, vec![inner])
    }

    pub fn expect_known<T, U, K, O>(&self, on_known: K, on_unknown: U) -> T
    where
        U: FnOnce() -> T,
        K: FnOnce(&KnownType, &[TypeVarID]) -> T,
    {
        match self {
            TypeVar::Unknown(_, _, _, _) => on_unknown(),
            TypeVar::Known(_, k, v) => on_known(k, v),
        }
    }

    pub fn expect_named<T, E, U, K, O>(
        &self,
        on_named: K,
        on_unknown: U,
        on_other: O,
        on_error: E,
    ) -> T
    where
        U: FnOnce() -> T,
        K: FnOnce(&NameID, &[TypeVarID]) -> T,
        E: FnOnce() -> T,
        O: FnOnce(&TypeVar) -> T,
    {
        match self {
            TypeVar::Unknown(_, _, _, _) => on_unknown(),
            TypeVar::Known(_, KnownType::Named(name), params) => on_named(name, params),
            TypeVar::Known(_, KnownType::Error, _) => on_error(),
            other => on_other(other),
        }
    }

    /// Expect a named type, or TypeVar::Inverted(named), or a recursive inversion.
    /// inverted_now is stateful and used to track if we are currently in an
    /// inverted context.
    pub fn resolve_named_or_inverted(
        &self,
        inverted_now: bool,
        type_state: &TypeState,
    ) -> ResolvedNamedOrInverted {
        match self {
            TypeVar::Unknown(_, _, _, _) => ResolvedNamedOrInverted::Unknown,
            TypeVar::Known(_, KnownType::Inverted, params) => {
                if params.len() != 1 {
                    panic!("Found wire with {} params", params.len())
                }
                params[0]
                    .resolve(type_state)
                    .resolve_named_or_inverted(!inverted_now, type_state)
            }
            TypeVar::Known(_, KnownType::Named(name), params) => {
                ResolvedNamedOrInverted::Named(inverted_now, name.clone(), params.clone())
            }
            _ => ResolvedNamedOrInverted::Other,
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
        K: FnOnce(&[TypeVarID]) -> T,
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
    pub fn expect_integer<T, E, U, K, O>(
        &self,
        on_integer: K,
        on_unknown: U,
        on_other: O,
        on_error: E,
    ) -> T
    where
        U: FnOnce() -> T,
        E: FnOnce() -> T,
        K: FnOnce(BigInt) -> T,
        O: FnOnce(&TypeVar) -> T,
    {
        match self {
            TypeVar::Known(_, KnownType::Integer(size), params) => {
                assert!(params.is_empty());
                on_integer(size.clone())
            }
            TypeVar::Known(_, KnownType::Error, _) => on_error(),
            TypeVar::Unknown(_, _, _, _) => on_unknown(),
            other => on_other(other),
        }
    }

    pub fn display(&self, type_state: &TypeState) -> String {
        self.display_with_meta(false, type_state)
    }

    pub fn display_with_meta(&self, display_meta: bool, type_state: &TypeState) -> String {
        match self {
            TypeVar::Known(_, KnownType::Error, _) => "{unknown}".to_string(),
            TypeVar::Known(_, KnownType::Named(t), params) => {
                let generics = if params.is_empty() {
                    String::new()
                } else {
                    format!(
                        "<{}>",
                        params
                            .iter()
                            .map(|p| format!("{}", p.display_with_meta(display_meta, type_state)))
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
                        .map(|t| format!("{}", t.display_with_meta(display_meta, type_state)))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            TypeVar::Known(_, KnownType::Array, params) => {
                format!(
                    "[{}; {}]",
                    params[0].display_with_meta(display_meta, type_state),
                    params[1].display_with_meta(display_meta, type_state)
                )
            }
            TypeVar::Known(_, KnownType::Wire, params) => {
                format!("&{}", params[0].display_with_meta(display_meta, type_state))
            }
            TypeVar::Known(_, KnownType::Inverted, params) => {
                format!(
                    "inv {}",
                    params[0].display_with_meta(display_meta, type_state)
                )
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
                        .map(|t| format!("{}", t.display_with_meta(display_meta, type_state)))
                        .join("+"),
                )
            }
        }
    }
}

#[derive(Clone, Hash, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct KnownTypeVar(pub Loc<()>, pub KnownType, pub Vec<KnownTypeVar>);

impl KnownTypeVar {
    pub fn insert(&self, type_state: &mut TypeState) -> TypeVarID {
        let KnownTypeVar(loc, base, params) = self;
        TypeVar::Known(
            loc.clone(),
            base.clone(),
            params.into_iter().map(|p| p.insert(type_state)).collect(),
        )
        .insert(type_state)
    }
}

impl std::fmt::Display for KnownTypeVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let KnownTypeVar(_, base, params) = self;

        match base {
            KnownType::Error => {
                write!(f, "{{unknown}}")
            }
            KnownType::Named(name_id) => {
                write!(f, "{name_id}")?;
                if !params.is_empty() {
                    write!(f, "<{}>", params.iter().map(|t| format!("{t}")).join(", "))?;
                }
                Ok(())
            }
            KnownType::Integer(val) => write!(f, "{val}"),
            KnownType::Bool(val) => write!(f, "{val}"),
            KnownType::Tuple => {
                write!(f, "({})", params.iter().map(|t| format!("{t}")).join(", "))
            }
            KnownType::Array => write!(f, "[{}; {}]", params[0], params[1]),
            KnownType::Wire => write!(f, "&{}", params[0]),
            KnownType::Inverted => write!(f, "inv {}", params[0]),
        }
    }
}

pub enum ResolvedNamedOrInverted {
    Unknown,
    Named(bool, NameID, Vec<TypeVarID>),
    Other,
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
