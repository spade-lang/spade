use crate::{equation::TypeVar, TypeState};
use itertools::Itertools;
use serde::{Deserialize, Serialize};
use spade_common::location_info::{Loc, WithLocation};
use spade_hir::{ImplBlock, ImplTarget, TraitName};
use std::collections::{BTreeSet, HashMap};

#[derive(Clone)]
pub struct TraitImpl {
    pub name: TraitName,
    pub type_params: Vec<TypeVar>,
    pub impl_block: ImplBlock,
}

#[derive(Clone)]
pub struct TraitImplList {
    pub inner: HashMap<ImplTarget, Vec<TraitImpl>>,
}

impl TraitImplList {
    pub fn new() -> Self {
        Self {
            inner: HashMap::new(),
        }
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct TraitReq {
    pub name: TraitName,
    pub type_params: Vec<TypeVar>,
}

impl WithLocation for TraitReq {}

impl TraitReq {
    pub fn display_with_meta(&self, display_meta: bool) -> String {
        if self.type_params.is_empty() {
            format!("{}", self.name)
        } else {
            format!(
                "{}<{}>",
                self.name,
                self.type_params
                    .iter()
                    .map(|t| format!("{}", t.display_with_meta(display_meta)))
                    .join(", ")
            )
        }
    }

    fn replace_type_vars(&mut self, from: &TypeVar, to: &TypeVar) {
        let  Self { name: _, type_params } = self;
        for param in type_params {
            TypeState::replace_type_var(param, from, to)
        }
    }
}

impl std::fmt::Display for TraitReq {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.display_with_meta(false))
    }
}
impl std::fmt::Debug for TraitReq {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.type_params.is_empty() {
            write!(f, "{}", self.name)
        } else {
            write!(
                f,
                "{}<{}>",
                self.name,
                self.type_params.iter().map(|t| format!("{t:?}")).join(", ")
            )
        }
    }
}

#[derive(Clone, Serialize, Deserialize)]
pub struct TraitList {
    pub inner: Vec<Loc<TraitReq>>,
}

impl TraitList {
    pub fn empty() -> Self {
        Self { inner: vec![] }
    }

    pub fn from_vec(inner: Vec<Loc<TraitReq>>) -> Self {
        Self { inner }
    }

    pub fn replace_type_vars(&mut self, from: &TypeVar, to: &TypeVar) {
        let Self { inner } = self;
        for req in inner {
            req.replace_type_vars(from, to);
        }
    }

    pub fn get_trait(&self, name: &TraitName) -> Option<&Loc<TraitReq>> {
        self.inner.iter().find(|t| &t.name == name)
    }

    pub fn get_trait_with_type_params(
        &self,
        name: &TraitName,
        type_params: &[TypeVar],
    ) -> Option<&Loc<TraitReq>> {
        self.inner
            .iter()
            .find(|t| &t.name == name && &t.type_params.as_slice() == &type_params)
    }

    pub fn extend(self, other: Self) -> Self {
        let merged = self
            .inner
            .into_iter()
            .chain(other.inner.into_iter())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect_vec();

        TraitList { inner: merged }
    }

    pub fn display_with_meta(&self, display_meta: bool) -> String {
        self.inner
            .iter()
            .map(|t| t.inner.display_with_meta(display_meta))
            .join(" + ")
    }
}

// NOTE: The trait information is currently carried along with the type vars, but
// the trait information should not be involved in comparisons
impl PartialEq for TraitList {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}
impl Eq for TraitList {}
impl std::hash::Hash for TraitList {
    fn hash<H: std::hash::Hasher>(&self, _state: &mut H) {}
}
impl PartialOrd for TraitList {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for TraitList {
    fn cmp(&self, _other: &Self) -> std::cmp::Ordering {
        std::cmp::Ordering::Equal
    }
}

impl std::fmt::Display for TraitList {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.display_with_meta(false))
    }
}
impl std::fmt::Debug for TraitList {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.display_with_meta(true))
    }
}
