use serde::{Deserialize, Serialize};
use spade_common::name::{Identifier, NameID};

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum PrimitiveType {
    Int,
    Uint,
    Clock,
    Bool,
    Memory,
}

impl std::fmt::Display for PrimitiveType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PrimitiveType::Int => write!(f, "int"),
            PrimitiveType::Uint => write!(f, "uint"),
            PrimitiveType::Clock => write!(f, "clk"),
            PrimitiveType::Bool => write!(f, "bool"),
            PrimitiveType::Memory => write!(f, "Memory"),
        }
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
        size: u128,
    },
    Enum {
        options: Vec<(NameID, Vec<(Identifier, ConcreteType)>)>,
    },
    Single {
        base: PrimitiveType,
        params: Vec<ConcreteType>,
    },
    Integer(u128),
    Backward(Box<ConcreteType>),
}

impl ConcreteType {
    pub fn assume_struct(&self) -> (&NameID, &Vec<(Identifier, ConcreteType)>) {
        match self {
            ConcreteType::Struct { name, members } => (name, members),
            t => unreachable!("Assumed {} was a struct", t),
        }
    }

    /// Transforms a backward type of a compound type into a compound type of backward types
    ///
    /// ~(a, b) => (~a, ~b)
    /// ~[a, N] => [~a, N]
    /// etc.
    pub fn internalize_backward(self) -> Self {
        match self {
            ConcreteType::Backward(inner) => match *inner {
                ConcreteType::Tuple(inner) => ConcreteType::Tuple(
                    inner
                        .into_iter()
                        .map(|t| ConcreteType::Backward(Box::new(t)))
                        .collect(),
                ),
                ConcreteType::Struct { name, members } => ConcreteType::Struct {
                    name,
                    members: members
                        .into_iter()
                        .map(|(f, t)| (f, ConcreteType::Backward(Box::new(t))))
                        .collect(),
                },
                ConcreteType::Array { inner, size } => ConcreteType::Array {
                    inner: Box::new(ConcreteType::Backward(inner)),
                    size,
                },
                ConcreteType::Enum { .. } => panic!("Backward enum"),
                s @ ConcreteType::Single { .. } => s,
                s @ ConcreteType::Integer(_) => s,
                ConcreteType::Backward(_) => panic!("Recursicve backward type"),
            },
            other => other,
        }
    }

    pub fn is_port(&self) -> bool {
        match self {
            ConcreteType::Tuple(inner) => inner.iter().any(Self::is_port),
            ConcreteType::Struct { name: _, members } => members.iter().any(|(_, t)| t.is_port()),
            ConcreteType::Array { inner, size: _ } => inner.is_port(),
            // Enums can not be ports
            ConcreteType::Enum { .. } => false,
            ConcreteType::Single {
                base: PrimitiveType::Memory,
                ..
            } => true,
            ConcreteType::Single { .. } => false,
            ConcreteType::Integer(_) => false,
            ConcreteType::Backward(_) => true,
        }
    }
}

impl std::fmt::Display for ConcreteType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConcreteType::Tuple(inner) => {
                write!(
                    f,
                    "({})",
                    inner
                        .iter()
                        .map(|p| format!("{}", p))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            ConcreteType::Struct { name, members } => {
                write!(
                    f,
                    "struct {name} {{{}}}",
                    members
                        .iter()
                        .map(|(name, t)| format!("{}: {}", name, t))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            ConcreteType::Array { inner, size } => {
                write!(f, "[{}; {}]", inner, size)
            }
            ConcreteType::Enum { options } => {
                write!(f, "enum {{",)?;
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
                write!(f, "{}", inner)?;
                write!(f, "}}")
            }
            ConcreteType::Single { base, params } => {
                let params_str = if params.is_empty() {
                    format!("")
                } else {
                    format!(
                        "{}",
                        params
                            .iter()
                            .map(|p| format!("{}", p))
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                };

                write!(f, "{}{}", base, params_str)
            }
            ConcreteType::Integer(size) => {
                write!(f, "#{}", size)
            }
            ConcreteType::Backward(inner) => {
                write!(f, "~{}", inner)
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Hash, Eq)]
pub enum KnownType {
    Type(NameID),
    Integer(u128),
}

impl std::fmt::Display for KnownType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            KnownType::Type(t) => {
                write!(f, "{}", t)
            }
            KnownType::Integer(v) => {
                write!(f, "{}", v)
            }
        }
    }
}
