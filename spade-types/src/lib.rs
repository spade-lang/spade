pub mod meta_types;

use std::collections::HashMap;

use num::BigInt;
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
        is_port: bool,
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
    Wire(Box<ConcreteType>),
}

impl ConcreteType {
    pub fn assume_struct(&self) -> (&NameID, &Vec<(Identifier, ConcreteType)>) {
        match self {
            ConcreteType::Struct {
                name,
                is_port: _,
                members,
                field_translators: _,
            } => (name, members),
            t => unreachable!("Assumed {} was a struct", t),
        }
    }

    pub fn is_error_recursively(&self) -> bool {
        match self {
            ConcreteType::Error => true,
            ConcreteType::Tuple(inner) => inner.iter().any(|ty| ty.is_error_recursively()),
            ConcreteType::Struct {
                name: _,
                is_port: _,
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
            ConcreteType::Wire(inner) => inner.is_error_recursively(),
        }
    }

    pub fn is_port(&self) -> bool {
        match self {
            ConcreteType::Error => false,
            ConcreteType::Tuple(inner) => inner.iter().any(Self::is_port),
            ConcreteType::Struct {
                name: _,
                is_port,
                members: _,
                field_translators: _,
            } => *is_port,
            ConcreteType::Array { inner, size: _ } => inner.is_port(),
            // Enums cannot be ports
            ConcreteType::Enum { .. } => false,
            ConcreteType::Single {
                base: PrimitiveType::Memory,
                ..
            } => true,
            ConcreteType::Single {
                base: PrimitiveType::Clock,
                ..
            } => true,
            ConcreteType::Single { .. } => false,
            ConcreteType::Integer(_) | ConcreteType::Bool(_) | ConcreteType::String(_) => false,
            ConcreteType::Backward(_) => true,
            ConcreteType::Wire(_) => true,
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
                is_port,
                members,
                field_translators: _,
            } => {
                let port = if *is_port { "port " } else { "" };
                format!(
                    "struct {port}{name} {{{}}}",
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
            ConcreteType::Wire(inner) => {
                format!("&{}", inner)
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
    Wire,
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
