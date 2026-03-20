pub mod meta_types;

use num::BigInt;
use rustc_hash::FxHashMap as HashMap;
use serde::{Deserialize, Serialize};
use spade_common::{
    name::{Identifier, NameID},
    num_ext::InfallibleToBigInt,
};

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum PrimitiveType {
    Int,
    Uint,
    Clock,
    Bool,
    Tri,
    Memory,
    InOut,
}

impl std::fmt::Display for PrimitiveType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let str = match self {
            PrimitiveType::Int => "int",
            PrimitiveType::Uint => "uint",
            PrimitiveType::Clock => "clock",
            PrimitiveType::Bool => "bool",
            PrimitiveType::Tri => "tri",
            PrimitiveType::Memory => "Memory",
            PrimitiveType::InOut => "inout",
        };
        write!(f, "{str}")
    }
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ConcreteType {
    Error,
    Tuple(Vec<ConcreteType>),
    Struct {
        name: NameID,
        members: Vec<(Identifier, ConcreteType)>,
        field_translators: HashMap<Identifier, String>,
    },
    Array {
        inner: Box<ConcreteType>,
        size: BigInt,
    },
    Enum {
        options: Vec<(NameID, Vec<(Identifier, ConcreteType)>)>,
    },
    Single {
        base: PrimitiveType,
        params: Vec<ConcreteType>,
    },
    Integer(BigInt),
    Bool(bool),
    String(String),
    Backward(Box<ConcreteType>),
}

impl ConcreteType {
    pub fn assume_struct(&self) -> (&NameID, &Vec<(Identifier, ConcreteType)>) {
        match self {
            ConcreteType::Struct {
                name,
                members,
                field_translators: _,
            } => (name, members),
            t => unreachable!("Assumed {} was a struct", t),
        }
    }

    pub fn assume_array(&self) -> (&Box<ConcreteType>, &BigInt) {
        match self {
            ConcreteType::Array { inner, size } => (inner, size),
            t => unreachable!("Assumed {} was an array", t),
        }
    }

    pub fn is_error_recursively(&self) -> bool {
        match self {
            ConcreteType::Error => true,
            ConcreteType::Tuple(inner) => inner.iter().any(|ty| ty.is_error_recursively()),
            ConcreteType::Struct {
                name: _,
                members,
                field_translators: _,
            } => members.iter().any(|(_, ty)| ty.is_error_recursively()),
            ConcreteType::Array { inner, size: _ } => inner.is_error_recursively(),
            ConcreteType::Enum { options } => options.iter().any(|option| {
                option
                    .1
                    .iter()
                    .any(|(_, member)| member.is_error_recursively())
            }),
            ConcreteType::Single { base: _, params } => {
                params.iter().any(|p| p.is_error_recursively())
            }
            ConcreteType::Integer(_) => false,
            ConcreteType::Bool(_) => false,
            ConcreteType::String(_) => false,
            ConcreteType::Backward(inner) => inner.is_error_recursively(),
        }
    }

    pub fn resolve_recursive_inversions(self, invert: bool) -> Self {
        match self {
            ConcreteType::Error => ConcreteType::Error,
            ConcreteType::Tuple(inner) => ConcreteType::Tuple(
                inner
                    .into_iter()
                    .map(|ty| ty.resolve_recursive_inversions(invert))
                    .collect(),
            ),
            ConcreteType::Struct {
                name,
                members,
                field_translators,
            } => Self::Struct {
                name,
                members: members
                    .into_iter()
                    .map(|(ident, ty)| (ident, ty.resolve_recursive_inversions(invert)))
                    .collect(),
                field_translators,
            },
            ConcreteType::Array { inner, size } => ConcreteType::Array {
                inner: Box::new(inner.resolve_recursive_inversions(invert)),
                size: size,
            },
            s @ ConcreteType::Enum { .. } | s @ ConcreteType::Single { .. } => {
                if invert {
                    ConcreteType::Backward(Box::new(s))
                } else {
                    s
                }
            }
            s @ ConcreteType::Bool(_)
            | s @ ConcreteType::String(_)
            | s @ ConcreteType::Integer(_) => {
                if invert {
                    panic!("Cannot invert type level value")
                } else {
                    s
                }
            }
            ConcreteType::Backward(inner) => inner.resolve_recursive_inversions(!invert),
        }
    }
}

impl std::fmt::Display for ConcreteType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let str = match self {
            ConcreteType::Error => "{error}".to_string(),
            ConcreteType::Tuple(inner) => {
                format!(
                    "({})",
                    inner
                        .iter()
                        .map(|p| format!("{}", p))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            ConcreteType::Struct {
                name,
                members,
                field_translators: _,
            } => {
                format!(
                    "struct {name} {{{}}}",
                    members
                        .iter()
                        .map(|(name, t)| format!("{}: {}", name, t))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            ConcreteType::Array { inner, size } => {
                format!("[{}; {}]", inner, size)
            }
            ConcreteType::Enum { options } => {
                let inner = options
                    .iter()
                    .map(|o| {
                        let param_list =
                            o.1.iter()
                                .map(|t| format!("{}", t.1))
                                .collect::<Vec<_>>()
                                .join(",");
                        format!("{} ( {} )", o.0 .0, param_list)
                    })
                    .collect::<Vec<_>>()
                    .join(",");
                format!("enum {{{}}}", inner)
            }
            ConcreteType::Single { base, params } => {
                let params_str = if params.is_empty() {
                    String::new()
                } else {
                    params
                        .iter()
                        .map(|p| format!("{}", p))
                        .collect::<Vec<_>>()
                        .join(", ")
                };

                format!("{}{}", base, params_str)
            }
            ConcreteType::Integer(size) => {
                format!("{}", size)
            }
            ConcreteType::Bool(val) => {
                format!("{}", val)
            }
            ConcreteType::String(val) => {
                format!("{:?}", val)
            }
            ConcreteType::Backward(inner) => {
                format!("inv &{}", inner)
            }
        };

        write!(f, "{str}")
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum KnownType {
    Named(NameID),
    Integer(BigInt),
    Bool(bool),
    String(String),
    Tuple,
    Array,
    Inverted,
    // A special type that unifies with anything to produce another error. Doing code generation
    // on this type will produce invalid code.
    Error,
}

impl KnownType {
    pub fn integer(val: u64) -> Self {
        Self::Integer(val.to_bigint())
    }
}
