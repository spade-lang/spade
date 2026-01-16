use std::hash::Hash;

use serde::{de::Visitor, Deserialize, Serialize};

use crate::{
    interning::INTERNER,
    location_info::{Loc, WithLocation},
};

#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub enum Visibility {
    Implicit,
    Public,
    AtLib,
    AtSelf,
    AtSuper,
    // Super-super visibility is an implementation detail, not accessible through Spade syntax.
    // It arises when enum variants inherit their parent enum's visibility. Because the enum
    // introduces a new namespace, relative visibility needs to be shifted (`AtSelf` becomes
    // `AtSuper` and `AtSuper` becomes `AtSuperSuper`).
    AtSuperSuper,
}

#[derive(Debug, Clone, Copy, Eq)]
#[repr(transparent)]
pub struct Identifier(&'static str);

impl Identifier {
    pub fn intern(ident: &str) -> Self {
        Self(INTERNER.intern(ident))
    }

    pub fn as_str(&self) -> &'static str {
        self.0
    }
}

impl std::fmt::Display for Identifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl PartialEq for Identifier {
    fn eq(&self, other: &Self) -> bool {
        ::core::ptr::eq(self.0, other.0)
    }
}

impl std::hash::Hash for Identifier {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.as_ptr().hash(state);
    }
}

impl Serialize for Identifier {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_str(self.0)
    }
}

impl<'de> Deserialize<'de> for Identifier {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        struct IdentVisitor;
        impl<'de> Visitor<'de> for IdentVisitor {
            type Value = Identifier;

            fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
                formatter.write_str("Identifier")
            }

            fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                Ok(Identifier::intern(v))
            }
        }

        deserializer.deserialize_str(IdentVisitor)
    }
}

#[derive(Debug)]
pub enum PathPrefix {
    FromLib,
    FromSelf,
    FromSuper(usize),
    None,
}

#[derive(PartialEq, Debug, Clone, Eq, Hash, Serialize, Deserialize)]
pub enum PathSegment {
    Named(Loc<Identifier>),
    Impl(u64),
    IfT,
    IfF,
}

impl PathSegment {
    pub fn is_named(&self) -> bool {
        match self {
            PathSegment::Named(_) => true,
            PathSegment::Impl(_) | PathSegment::IfT | PathSegment::IfF => false,
        }
    }

    pub fn to_named_str(&self) -> Option<&str> {
        match self {
            PathSegment::Named(s) => Some(s.0),
            PathSegment::Impl(_) | PathSegment::IfT | PathSegment::IfF => None,
        }
    }

    pub fn loc(&self) -> Loc<()> {
        match self {
            PathSegment::Named(ident) => ident.loc(),
            PathSegment::Impl(_) | PathSegment::IfT | PathSegment::IfF => ().nowhere(),
        }
    }

    pub fn unwrap_named(&self) -> &Loc<Identifier> {
        match self {
            PathSegment::Named(ident) => ident,
            PathSegment::Impl(_) | PathSegment::IfT | PathSegment::IfF => {
                panic!("called `PathSegment::unwrap_named()` on a generated path segment")
            }
        }
    }
}

impl std::fmt::Display for PathSegment {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PathSegment::Named(ident) => write!(f, "{}", ident),
            PathSegment::Impl(n) => write!(f, "impl#{n}"),
            PathSegment::IfT => write!(f, "if#true"),
            PathSegment::IfF => write!(f, "if#false"),
        }
    }
}

#[derive(PartialEq, Debug, Clone, Eq, Hash, Serialize, Deserialize)]
pub struct Path(pub Vec<PathSegment>);

impl Path {
    pub fn to_strings(&self) -> Vec<String> {
        self.0.iter().map(PathSegment::to_string).collect()
    }

    pub fn to_named_strs(&self) -> Vec<Option<&str>> {
        self.0.iter().map(PathSegment::to_named_str).collect()
    }

    /// Generate a path from a list of strings
    pub fn from_strs(elems: &[&str]) -> Self {
        Path(
            elems
                .iter()
                .map(|x| PathSegment::Named(Identifier::intern(x).nowhere()))
                .collect(),
        )
    }

    /// Generate a path from a list of Loc<Identifier>
    pub fn from_idents(elems: &[&Loc<Identifier>]) -> Self {
        Path(
            elems
                .iter()
                .map(|x| PathSegment::Named((*x).clone()))
                .collect(),
        )
    }

    pub fn ident(ident: Loc<Identifier>) -> Self {
        Self(vec![PathSegment::Named(ident)])
    }

    pub fn ident_with_loc(ident: Loc<Identifier>) -> Loc<Self> {
        let loc = ident.loc();
        Self::ident(ident).at_loc(&loc)
    }

    pub fn push_segment(&self, segment: PathSegment) -> Path {
        let mut result = self.clone();
        result.0.push(segment);
        result
    }

    pub fn push_ident(&self, ident: Loc<Identifier>) -> Path {
        let mut result = self.clone();
        result.0.push(PathSegment::Named(ident));
        result
    }

    pub fn pop(&self) -> Self {
        let mut result = self.clone();
        result.0.pop().expect("Failed to pop identifier from path");
        result
    }

    pub fn join(&self, other: Path) -> Path {
        let mut result = self.clone();
        for segment in other.0 {
            result.0.push(segment);
        }
        result
    }

    pub fn extract_prefix(&self) -> (PathPrefix, Path) {
        let Some(segment) = self.0.first() else {
            return (PathPrefix::None, self.clone());
        };

        let (prefix, count) = match segment.to_named_str() {
            Some("lib") => (PathPrefix::FromLib, 1),
            Some("self") => (PathPrefix::FromSelf, 1),
            Some("super") => {
                let levels = self
                    .0
                    .iter()
                    .take_while(|s| s.to_named_str() == Some("super"))
                    .count();
                (PathPrefix::FromSuper(levels), levels)
            }
            _ => (PathPrefix::None, 0),
        };

        let path_without_prefix = Path(Vec::from(&self.0[count..]));
        (prefix, path_without_prefix)
    }

    /// The last element of the path. Panics if the path is empty
    pub fn tail(&self) -> PathSegment {
        self.0
            .last()
            .expect("Tried getting tail of empty path")
            .clone()
    }

    /// Returns the whole path apart from the tail. Panics if the path is empty
    pub fn prelude(&self) -> Path {
        Self(self.0[0..self.0.len() - 1].to_owned())
    }

    pub fn starts_with(&self, other: &Path) -> bool {
        self.0.iter().zip(&other.0).all(|(l, r)| l == r)
    }
}

impl std::fmt::Display for Path {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_strings().join("::"))
    }
}

/// Anything named will get assigned a unique name ID during AST lowering in order to avoid caring
/// about scopes once HIR has been generated. This is the type of those IDs
///
/// The associated string is only used for formatting when printing. The hash and eq methods do not
/// use it
#[derive(Clone, Serialize, Deserialize)]
pub struct NameID(pub u64, pub Path);

impl std::cmp::PartialEq for NameID {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl std::cmp::Eq for NameID {}

impl std::cmp::PartialOrd for NameID {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.0.cmp(&other.0))
    }
}

impl std::cmp::Ord for NameID {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.cmp(&other.0)
    }
}

impl std::hash::Hash for NameID {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl std::fmt::Debug for NameID {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}#{}", self.1, self.0)
    }
}
impl std::fmt::Display for NameID {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.1)
    }
}

pub mod testutil {
    use super::*;
    pub fn name_id(id: u64, name: &str) -> Loc<NameID> {
        NameID(id, Path::from_strs(&[name])).nowhere()
    }

    /// Shorthand for creating a name_id with static strs as name
    pub fn name_id_p(id: u64, name: &[&str]) -> Loc<NameID> {
        NameID(id, Path::from_strs(name)).nowhere()
    }
}
