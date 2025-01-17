use serde::{Deserialize, Serialize};

/*
  The meta-types form a a lattice with the following hierarchy

         any
        /    \
     number type
       / \
    uint int
*/

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize, Debug)]
pub enum MetaType {
    Any,

    Type,
    Number,

    Int,
    Uint,

    Bool,
}

// Attempts to unify l and r, returning the resulting MetaType if they are compatible,
// or an error if they are not
pub fn unify_meta(l: &MetaType, r: &MetaType) -> Option<MetaType> {
    match (l, r) {
        (MetaType::Any, other) => Some(other.clone()),
        (other, MetaType::Any) => Some(other.clone()),
        (MetaType::Number, other @ (MetaType::Int | MetaType::Uint))
        | (other @ (MetaType::Int | MetaType::Uint), MetaType::Number) => Some(other.clone()),
        (MetaType::Type, MetaType::Type)
        | (MetaType::Int, MetaType::Int)
        | (MetaType::Number, MetaType::Number)
        | (MetaType::Bool, MetaType::Bool)
        | (MetaType::Uint, MetaType::Uint) => Some(l.clone()),

        (MetaType::Bool, _) => None,
        (_, MetaType::Bool) => None,
        (MetaType::Type, MetaType::Int)
        | (MetaType::Type, MetaType::Uint)
        | (MetaType::Int, MetaType::Type)
        | (MetaType::Int, MetaType::Uint)
        | (MetaType::Uint, MetaType::Type)
        | (MetaType::Uint, MetaType::Int)
        | (MetaType::Type, MetaType::Number)
        | (MetaType::Number, MetaType::Type) => None,
    }
}

impl MetaType {
    /// Returns the type which is the most concrete of self and another type.
    /// A type which can be converted into another type is less concrete than the
    /// other type. Ordering of nnn-unifiable types is undefined
    pub fn is_more_concrete_than(&self, other: &Self) -> bool {
        if self > other {
            false
        } else {
            true
        }
    }
}

impl std::fmt::Display for MetaType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MetaType::Any => write!(f, "#any"),
            MetaType::Type => write!(f, "#type"),
            MetaType::Int => write!(f, "#int"),
            MetaType::Uint => write!(f, "#uint"),
            MetaType::Bool => write!(f, "#bool"),
            MetaType::Number => write!(f, "#number"),
        }
    }
}
