use num::{BigUint, Zero};
use spade_common::num_ext::InfallibleToBigUint;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Type {
    Int(BigUint),
    UInt(BigUint),
    Bool,
    /// An "empty" type.
    Void,
    Tuple(Vec<Type>),
    Struct(Vec<(String, Type)>),
    Array {
        inner: Box<Type>,
        length: BigUint,
    },
    Memory {
        inner: Box<Type>,
        length: BigUint,
    },
    Enum(Vec<Vec<Type>>),
    /// A type in which values flow the opposite way compared to normal types. When a type
    /// containing a Backward<T> is returned, the module 'returning' it has an additional *input*
    /// for the wire, and if it takes an input with, n additional *output* port is created.
    Backward(Box<Type>),
    InOut(Box<Type>),
}

impl Type {
    pub fn int(val: u32) -> Self {
        Self::Int(val.to_biguint())
    }
    pub fn uint(val: u32) -> Self {
        Self::UInt(val.to_biguint())
    }
    pub fn backward(inner: Type) -> Self {
        Self::Backward(Box::new(inner))
    }

    pub fn size(&self) -> BigUint {
        match self {
            Type::Int(len) => len.clone(),
            Type::UInt(len) => len.clone(),
            Type::Bool => 1u32.to_biguint(),
            Type::Void => BigUint::zero(),
            Type::Tuple(inner) => inner.iter().map(Type::size).sum::<BigUint>(),
            Type::Struct(inner) => inner.iter().map(|(_, t)| t.size()).sum::<BigUint>(),
            Type::Enum(inner) => {
                let discriminant_size = (inner.len() as f32).log2().ceil() as u64;

                let members_size = inner
                    .iter()
                    .map(|m| m.iter().map(|t| t.size()).sum())
                    .max()
                    .unwrap_or(BigUint::zero());

                discriminant_size + members_size
            }
            Type::Array { inner, length } => inner.size() * length,
            Type::Memory { inner, length } => inner.size() * length,
            Type::Backward(_) => BigUint::zero(),
            Type::InOut(inner) => inner.size(),
        }
    }

    pub fn backward_size(&self) -> BigUint {
        match self {
            Type::Backward(inner) => inner.size(),
            Type::Int(_) | Type::UInt(_) | Type::Bool | Type::Void => BigUint::zero(),
            Type::Array { inner, length } => inner.backward_size() * length,
            Type::Enum(inner) => {
                for v in inner {
                    for i in v {
                        if i.backward_size() != BigUint::zero() {
                            unreachable!("Enums cannot have output wires as payload")
                        }
                    }
                }
                BigUint::zero()
            }
            Type::Memory { inner, .. } => {
                if inner.backward_size() != BigUint::zero() {
                    unreachable!("Memory cannot contain output wires")
                };
                BigUint::zero()
            }
            Type::Tuple(inner) => inner.iter().map(Type::backward_size).sum::<BigUint>(),
            Type::Struct(inner) => inner
                .iter()
                .map(|(_, t)| t.backward_size())
                .sum::<BigUint>(),
            Type::InOut(_) => BigUint::zero(),
        }
    }

    pub fn assume_enum(&self) -> &Vec<Vec<Type>> {
        if let Type::Enum(inner) = self {
            inner
        } else {
            panic!("Assumed enum for a type which was not")
        }
    }
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Int(val) => write!(f, "int<{}>", val),
            Type::UInt(val) => write!(f, "uint<{}>", val),
            Type::Bool => write!(f, "bool"),
            Type::Void => write!(f, "void"),
            Type::Tuple(inner) => {
                let inner = inner
                    .iter()
                    .map(|p| format!("{}", p))
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "({})", inner)
            }
            Type::Struct(inner) => {
                let inner = inner
                    .iter()
                    .map(|(n, t)| format!("{n}: {t}"))
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "{{{}}}", inner)
            }
            Type::Array { inner, length } => {
                write!(f, "[{}; {}]", inner, length)
            }
            Type::Memory { inner, length } => {
                write!(f, "Memory[{}; {}]", inner, length)
            }
            Type::Enum(inner) => {
                let inner = inner
                    .iter()
                    .map(|variant| {
                        let members = variant
                            .iter()
                            .map(|t| format!("{}", t))
                            .collect::<Vec<_>>()
                            .join(", ");
                        format!("option [{}]", members)
                    })
                    .collect::<Vec<_>>()
                    .join(", ");

                write!(f, "enum {}", inner)
            }
            Type::Backward(inner) => {
                write!(f, "&mut ({inner})")
            }
            Type::InOut(inner) => {
                write!(f, "inout<{inner}>")
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pure_enum_size_is_correct() {
        // 2 variant enum
        assert_eq!(Type::Enum(vec![vec![], vec![]]).size(), 1u32.to_biguint());
    }

    #[test]
    fn enum_with_payload_size_is_correct() {
        // 2 variant enum
        assert_eq!(
            Type::Enum(vec![vec![Type::Int(5u32.to_biguint())], vec![Type::Bool]]).size(),
            6u32.to_biguint()
        );
    }

    #[test]
    fn single_variant_enum_is_0_bits() {
        assert_eq!(Type::Enum(vec![vec![]]).size(), BigUint::zero());
    }
}
