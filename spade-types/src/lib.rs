pub mod meta_types;

use num::BigInt;
use serde::{Deserialize, Serialize};
use spade_common::{
    location_info::WithLocation,
    name::{Identifier, NameID},
    num_ext::InfallibleToBigInt,
};

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum PrimitiveType {
    Int,
    Uint,
    Clock,
    Bool,
    Bit,
    Memory,
    Void,
    InOut,
}

impl std::fmt::Display for PrimitiveType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let str = match self {
            PrimitiveType::Int => "int",
            PrimitiveType::Uint => "uint",
            PrimitiveType::Clock => "clk",
            PrimitiveType::Bool => "bool",
            PrimitiveType::Bit => "bit",
            PrimitiveType::Memory => "Memory",
            PrimitiveType::Void => "()",
            PrimitiveType::InOut => "inout",
        };
        write!(f, "{str}")
    }
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ConcreteType {
    Tuple(Vec<ConcreteType>),
    Struct {
        name: NameID,
        members: Vec<(Identifier, ConcreteType)>,
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
    Backward(Box<ConcreteType>),
    Wire(Box<ConcreteType>),
}

impl ConcreteType {
    pub fn assume_struct(&self) -> (&NameID, &Vec<(Identifier, ConcreteType)>) {
        match self {
            ConcreteType::Struct { name, members } => (name, members),
            t => unreachable!("Assumed {} was a struct", t),
        }
    }

    pub fn is_port(&self) -> bool {
        match self {
            ConcreteType::Tuple(inner) => inner.iter().any(Self::is_port),
            ConcreteType::Struct { name: _, members } => members.iter().any(|(_, t)| t.is_port()),
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
            ConcreteType::Integer(_) | ConcreteType::Bool(_) => false,
            ConcreteType::Backward(_) => true,
            ConcreteType::Wire(_) => true,
        }
    }
}

impl std::fmt::Display for ConcreteType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let str = match self {
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
            ConcreteType::Struct { name, members } => {
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
    Tuple,
    Array,
    Wire,
    Inverted,
}

impl WithLocation for KnownType {}

impl KnownType {
    pub fn integer(val: u64) -> Self {
        Self::Integer(val.to_bigint())
    }
}
