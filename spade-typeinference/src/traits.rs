use crate::{
    equation::{TemplateTypeVarID, TypeVarID},
    TypeState,
};
use itertools::Itertools;
use serde::{Deserialize, Serialize};
use spade_common::location_info::Loc;
use spade_hir::{ImplBlock, ImplTarget, TraitName};
use std::collections::{BTreeSet, HashMap};

#[derive(Clone, Serialize, Deserialize)]
pub struct TraitImpl {
    pub name: TraitName,
    pub target_type_params: Vec<TemplateTypeVarID>,
    pub trait_type_params: Vec<TemplateTypeVarID>,
    pub impl_block: ImplBlock,
}

#[derive(Clone, Serialize, Deserialize)]
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
    pub type_params: Vec<TypeVarID>,
}

impl TraitReq {
    pub fn display(&self, type_state: &TypeState) -> String {
        self.display_with_meta(false, type_state)
    }

    pub fn display_with_meta(&self, display_meta: bool, type_state: &TypeState) -> String {
        if self.type_params.is_empty() {
            format!("{}", self.name)
        } else {
            format!(
                "{}<{}>",
                self.name,
                self.type_params
                    .iter()
                    .map(|t| format!("{}", t.display_with_meta(display_meta, type_state)))
                    .join(", ")
            )
        }
    }

    pub fn debug_display(&self, type_state: &TypeState) -> String {
        if self.type_params.is_empty() {
            format!("{}", self.name)
        } else {
            format!(
                "{}<{}>",
                self.name,
                self.type_params
                    .iter()
                    .map(|t| format!("{}", t.debug_resolve(type_state).0))
                    .join(", ")
            )
        }
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

#[derive(Clone, Debug, Serialize, Deserialize)]
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

    pub fn get_trait(&self, name: &TraitName) -> Option<&Loc<TraitReq>> {
        self.inner.iter().find(|t| &t.name == name)
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

    pub fn display_with_meta(&self, display_meta: bool, type_state: &TypeState) -> String {
        self.inner
            .iter()
            .map(|t| t.inner.display_with_meta(display_meta, type_state))
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
