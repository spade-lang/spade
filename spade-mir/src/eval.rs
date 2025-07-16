use std::collections::HashMap;

use itertools::Itertools;
use num::range;
use num::BigInt;
use num::BigUint;
use num::ToPrimitive;
use num::Zero;
use spade_common::num_ext::InfallibleToBigUint;

use crate::{enum_util, types::Type, Binding, Operator, Statement, ValueName};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Value {
    Bit(bool),
    Int {
        size: BigUint,
        val: BigInt,
    },
    UInt {
        size: BigUint,
        val: BigUint,
    },
    // Concatenated values are placed left-to-right, i.e. `Concat(vec![0b11,0b00])` is
    // 0b1100
    Concat(Vec<Value>),
    /// A number of undefined bits
    Undef(BigUint),
}

impl Value {
    pub fn assume_int(&self) -> BigInt {
        match self {
            Value::Int { val, .. } => val.clone(),
            other => panic!("Assumed value to be int, was {other:?}"),
        }
    }
    pub fn assume_uint(&self) -> BigUint {
        match self {
            Value::UInt { val, .. } => val.clone(),
            other => panic!("Assumed value to be int, was {other:?}"),
        }
    }

    pub fn as_string(&self) -> String {
        match self {
            Value::Bit(val) => format!("{}", if *val { 1 } else { 0 }),
            Value::Int { size, val } => {
                if *val >= 0i64.into() {
                    let val_str = format!("{val:b}");
                    let needed_0s: BigUint = size - val_str.len();
                    let extra_0 = range(0u64.into(), needed_0s).map(|_| "0").join("");
                    assert!(*size >= val_str.len().into());
                    format!("{extra_0}{val_str}")
                } else {
                    // Negative numbers in 2's complement are represented by all leadingdigits
                    // being 1. That is a bit difficult to achieve when our numbers have infinite
                    // bits (as is the case for BigInt). To fix that, we mask out the bits we do
                    // want which gives a positive number with the correct binary representation.
                    // https://stackoverflow.com/questions/12946116/twos-complement-binary-in-python
                    let size_usize = size.to_usize().unwrap_or_else(|| {
                        panic!("Variable size {size} is too large to fit a 'usize'")
                    });
                    let mask = (BigInt::from(1) << size_usize) - 1;
                    format!("{:b}", val & mask)
                }
            }
            Value::UInt { size, val } => {
                let val_str = format!("{val:b}");
                let needed_0s: BigUint = size - val_str.len();
                let extra_0 = range(0u64.into(), needed_0s).map(|_| "0").join("");

                assert!(*size >= val_str.len().into());

                format!("{extra_0}{val_str}")
            }
            Value::Concat(inner) => inner.iter().map(|i| i.as_string()).join(""),
            Value::Undef(size) => range(0u64.into(), size.clone()).map(|_| "X").join(""),
        }
    }

    pub fn width(&self) -> BigUint {
        match self {
            Value::Bit(_) => 1u32.to_biguint(),
            Value::Int { size, val: _ } => size.clone(),
            Value::UInt { size, val: _ } => size.clone(),
            Value::Concat(inner) => inner.iter().map(|i| i.width()).sum(),
            Value::Undef(size) => size.clone(),
        }
    }

    /// Computes the value as a 64. If the type this value represents is wider than 64 bits,
    /// the behaviour is undefined. If the value is value::Undef, 0 is returned
    pub fn as_u64(&self) -> u64 {
        match self {
            Value::Bit(val) => {
                if *val {
                    1
                } else {
                    0
                }
            }
            Value::Int { size, val } => {
                if *val >= 0i64.into() {
                    val.to_u64().unwrap()
                } else {
                    // Negative numbers in 2's complement are represented by all leadingdigits
                    // being 1. That is a bit difficult to achieve when our numbers have infinite
                    // bits (as is the case for BigInt). To fix that, we mask out the bits we do
                    // want which gives a positive number with the correct binary representation.
                    // https://stackoverflow.com/questions/12946116/twos-complement-binary-in-python
                    let size_usize = size.to_usize().unwrap_or_else(|| {
                        panic!("Variable size {size} is too large to fit in a 'usize'")
                    });
                    let mask: BigInt = (BigInt::from(1) << size_usize) - 1;
                    (val & mask).to_u64().unwrap()
                }
            }
            Value::UInt { size: _, val } => val.to_u64().unwrap(),
            Value::Concat(inner) => {
                let mut current = 0;

                for next in inner {
                    current = (current << next.width().to_u64().unwrap()) + next.as_u64()
                }
                current
            }
            Value::Undef(_) => 0,
        }
    }

    pub fn as_u32_chunks(&self) -> BigUint {
        match self {
            Value::Bit(val) => {
                if *val {
                    1u32.to_biguint()
                } else {
                    0u32.to_biguint()
                }
            }
            Value::Int { size, val } => {
                if *val >= 0i64.into() {
                    val.to_biguint().unwrap()
                } else {
                    // Negative numbers in 2's complement are represented by all leadingdigits
                    // being 1. That is a bit difficult to achieve when our numbers have infinite
                    // bits (as is the case for BigInt). To fix that, we mask out the bits we do
                    // want which gives a positive number with the correct binary representation.
                    // https://stackoverflow.com/questions/12946116/twos-complement-binary-in-python
                    let size_usize = size.to_usize().unwrap_or_else(|| {
                        panic!("Variable size {size} is too large to fit in a usize")
                    });
                    let mask: BigInt = (BigInt::from(1) << size_usize) - 1;
                    (val & mask).to_biguint().unwrap()
                }
            }
            Value::UInt { size: _, val } => val.clone(),
            Value::Concat(inner) => {
                let mut current = 0u32.to_biguint();

                for next in inner {
                    current = (current << next.width().to_u64().unwrap()) + next.as_u64()
                }
                current
            }
            Value::Undef(_) => 0u32.to_biguint(),
        }
    }
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Bit(val) => write!(f, "bit({})", if *val { "1" } else { "0" }),
            Value::Int { size, val } => write!(f, "int<{size}>({val})"),
            Value::UInt { size, val } => write!(f, "uint<{size}>({val})"),
            Value::Concat(inner) => write!(
                f,
                "concat([{}])",
                inner.iter().map(|v| format!("{v}")).join(", ")
            ),
            Value::Undef(_) => write!(f, "X"),
        }
    }
}

#[cfg(test)]
impl Value {
    fn uint(size: u64, val: u64) -> Self {
        Self::UInt {
            size: size.into(),
            val: val.into(),
        }
    }

    fn int(size: u64, val: i64) -> Self {
        Self::Int {
            size: size.into(),
            val: val.into(),
        }
    }

    fn undef(size: u64) -> Self {
        Self::Undef(size.into())
    }
}

/// Evaluates a list of statements, returning the value of the final statement in the
/// list. Panics if the list of statements is empty
pub fn eval_statements(statements: &[Statement]) -> Value {
    let mut name_vals: HashMap<ValueName, Value> = HashMap::new();
    let mut name_types: HashMap<ValueName, Type> = HashMap::new();

    let mut last_value = None;
    for stmt in statements {
        let (n, v) = match stmt {
            Statement::Binding(b) => {
                let Binding {
                    name,
                    operator,
                    operands: ops,
                    ty,
                    loc: _,
                } = b;

                name_types.insert(name.clone(), ty.clone());

                let val = match operator {
                    Operator::Add => Value::Int {
                        size: ty.size(),
                        val: name_vals[&ops[0]].assume_int() + name_vals[&ops[1]].assume_int(),
                    },
                    Operator::UnsignedAdd => Value::UInt {
                        size: ty.size(),
                        val: name_vals[&ops[0]].assume_uint() + name_vals[&ops[1]].assume_uint(),
                    },
                    Operator::Sub => Value::Int {
                        size: ty.size(),
                        val: name_vals[&ops[0]].assume_int() - name_vals[&ops[1]].assume_int(),
                    },
                    Operator::UnsignedSub => Value::UInt {
                        size: ty.size(),
                        val: name_vals[&ops[0]].assume_uint() - name_vals[&ops[1]].assume_uint(),
                    },
                    Operator::Mul => todo!(),
                    Operator::UnsignedMul => todo!(),
                    Operator::Div => todo!(),
                    Operator::UnsignedDiv => todo!(),
                    Operator::Mod => todo!(),
                    Operator::UnsignedMod => todo!(),
                    Operator::Eq => todo!(),
                    Operator::NotEq => todo!(),
                    Operator::Gt => todo!(),
                    Operator::Lt => todo!(),
                    Operator::Ge => todo!(),
                    Operator::Le => todo!(),
                    Operator::UnsignedGt => todo!(),
                    Operator::UnsignedLt => todo!(),
                    Operator::UnsignedGe => todo!(),
                    Operator::UnsignedLe => todo!(),
                    Operator::LeftShift => todo!(),
                    Operator::RightShift => todo!(),
                    Operator::ArithmeticRightShift => todo!(),
                    Operator::LogicalAnd => todo!(),
                    Operator::LogicalOr => todo!(),
                    Operator::LogicalXor => todo!(),
                    Operator::LogicalNot => todo!(),
                    Operator::BitwiseAnd => todo!(),
                    Operator::BitwiseOr => todo!(),
                    Operator::BitwiseXor => todo!(),
                    Operator::USub => Value::Int {
                        size: ty.size(),
                        val: -name_vals[&ops[0]].assume_int(),
                    },
                    Operator::Not => todo!(),
                    Operator::BitwiseNot => todo!(),
                    Operator::DivPow2 => todo!(),
                    Operator::ReduceAnd { .. } => todo!(),
                    Operator::ReduceOr { .. } => todo!(),
                    Operator::ReduceXor { .. } => todo!(),
                    Operator::SignExtend { .. } => todo!(),
                    Operator::ZeroExtend { .. } => todo!(),
                    Operator::Truncate => todo!(),
                    Operator::Concat => todo!(),
                    Operator::Select => todo!(),
                    Operator::Match => todo!(),
                    Operator::ConstructArray => {
                        Value::Concat(ops.iter().rev().map(|op| name_vals[op].clone()).collect())
                    }
                    Operator::DeclClockedMemory { .. } => todo!(),
                    Operator::IndexArray { .. } => todo!(),
                    Operator::IndexMemory => todo!(),
                    Operator::RangeIndexArray { .. } => todo!(),
                    Operator::RangeIndexBits { .. } => todo!(),
                    Operator::ConstructTuple => {
                        Value::Concat(ops.iter().map(|op| name_vals[op].clone()).collect())
                    }
                    Operator::ConstructEnum {
                        variant,
                        variant_count,
                    } => {
                        let tag_size = BigUint::from(enum_util::tag_size(*variant_count));

                        let mut to_concat = if *variant_count == 1 {
                            vec![]
                        } else {
                            vec![Value::UInt {
                                size: tag_size.clone(),
                                val: (*variant).into(),
                            }]
                        };
                        to_concat.append(
                            &mut ops
                                .iter()
                                .map(|op| {
                                    let val = &name_vals[op];

                                    val.clone()
                                })
                                .collect(),
                        );
                        let variant_member_size =
                            ops.iter().map(|op| name_types[op].size()).sum::<BigUint>();
                        let padding_size = ty.size() - tag_size - variant_member_size;
                        if padding_size != BigUint::zero() {
                            to_concat.push(Value::Undef(padding_size))
                        }

                        Value::Concat(to_concat)
                    }
                    Operator::IsEnumVariant { .. } => todo!(),
                    Operator::EnumMember { .. } => todo!(),
                    Operator::IndexTuple(_, _) => todo!(),
                    Operator::ReadPort => todo!(),
                    Operator::ReadWriteInOut => todo!(),
                    Operator::FlipPort => todo!(),
                    Operator::ReadMutWires => todo!(),
                    Operator::Instance { .. } => todo!(),
                    Operator::Alias => name_vals[&ops[0]].clone(),
                    Operator::Nop => todo!(),
                };

                (name.clone(), val)
            }
            Statement::Register(_) => panic!("trying to evaluate a register"),
            Statement::Constant(id, ty, val) => {
                let val = match val {
                    crate::ConstantValue::Int(i) => Value::Int {
                        size: ty.size(),
                        val: i.clone(),
                    },
                    crate::ConstantValue::Bool(v) => Value::Bit(*v),
                    crate::ConstantValue::HighImp => todo!(),
                };
                let name = ValueName::Expr(*id);
                name_types.insert(name.clone(), ty.clone());
                (name, val)
            }
            Statement::Assert(_) => panic!("trying to evaluate an assert statement"),
            Statement::Set { .. } => panic!("trying to evaluate a `set` statement"),
            Statement::WalTrace { .. } => panic!("trying to evaluate a `wal_trace`"),
        };

        name_vals.insert(n, v.clone());
        last_value = Some(v);
    }
    last_value.expect("Trying to evaluate empty statement list")
}

#[cfg(test)]
mod string_value_tests {
    use super::*;

    #[test]
    fn positive_integer_works() {
        let value = Value::int(8, 8);

        let expected = "00001000";

        assert_eq!(value.as_string(), expected)
    }

    #[test]
    fn negative_integer_works() {
        let value = Value::int(8, -8);

        let expected = "11111000";

        assert_eq!(value.as_string(), expected)
    }

    #[test]
    fn minus_10_works() {
        let value = Value::int(8, -10);

        let expected = "11110110";

        assert_eq!(value.as_string(), expected)
    }

    #[test]
    fn zero_integer_works() {
        let value = Value::int(8, 0);

        let expected = "00000000";

        assert_eq!(value.as_string(), expected)
    }

    #[test]
    fn positive_uinteger_works() {
        let value = Value::uint(8, 8);

        let expected = "00001000";

        assert_eq!(value.as_string(), expected)
    }

    #[test]
    fn zero_uinteger_works() {
        let value = Value::uint(8, 0);

        let expected = "00000000";

        assert_eq!(value.as_string(), expected)
    }
}

#[cfg(test)]
mod test {
    use crate as spade_mir;
    use crate::{statement, types::Type, ConstantValue};
    use pretty_assertions::assert_eq;
    use spade_common::num_ext::InfallibleToBigInt;

    use super::*;

    #[test]
    fn addition_works() {
        let mir = vec![
            statement!(const 0; Type::int(16); ConstantValue::int(5)),
            statement!(const 1; Type::int(16); ConstantValue::int(10)),
            statement!(e(2); Type::int(16); Add; e(0), e(1)),
        ];

        let result = eval_statements(&mir);

        assert_eq!(result, Value::int(16, 15));
    }

    #[test]
    fn enum_construction_works() {
        let enum_t = Type::Enum(vec![vec![], vec![Type::int(16)], vec![]]);

        let mir = vec![
            statement!(const 0; Type::int(16); ConstantValue::int(5)),
            statement!(e(1); enum_t; ConstructEnum({variant: 1, variant_count: 3}); e(0)),
        ];

        let result = eval_statements(&mir);

        assert_eq!(
            result,
            Value::Concat(vec![Value::uint(2, 1), Value::int(16, 5),])
        )
    }

    #[test]
    fn enum_construction_with_padding_works() {
        let enum_t = Type::Enum(vec![vec![Type::int(2)], vec![Type::int(16)], vec![]]);

        let mir = vec![
            statement!(const 0; Type::int(3); ConstantValue::int(5)),
            statement!(e(1); enum_t; ConstructEnum({variant: 1, variant_count: 3}); e(0)),
        ];

        let result = eval_statements(&mir);

        assert_eq!(
            result,
            Value::Concat(vec![Value::uint(2, 1), Value::int(3, 5), Value::undef(13)])
        )
    }

    #[test]
    fn enum_construction_to_string_works() {
        let enum_t = Type::Enum(vec![vec![Type::int(8)], vec![]]);

        let mir = vec![
            statement!(const 0; Type::int(8); ConstantValue::int(0b1010)),
            statement!(e(1); enum_t; ConstructEnum({variant: 0, variant_count: 2}); e(0)),
        ];

        assert_eq!("000001010", eval_statements(&mir).as_string())
    }

    #[test]
    fn as_u64_works_for_bits() {
        assert_eq!(Value::Bit(false).as_u64(), 0);
        assert_eq!(Value::Bit(true).as_u64(), 1);
    }

    #[test]
    fn as_u32_chunks_works_for_bits() {
        assert_eq!(Value::Bit(false).as_u32_chunks(), 0u32.to_biguint());
        assert_eq!(Value::Bit(true).as_u32_chunks(), 1u32.to_biguint());
    }

    #[test]
    fn as_u64_works_for_ints() {
        assert_eq!(
            Value::Int {
                size: 64u64.to_biguint(),
                val: i64::MAX.to_bigint()
            }
            .as_u64(),
            i64::MAX as u64
        );
        assert_eq!(
            Value::Int {
                size: 64u64.to_biguint(),
                val: i64::MIN.to_bigint()
            }
            .as_u64(),
            0x8000_0000_0000_0000u64
        );
        assert_eq!(
            Value::Int {
                size: 64u64.to_biguint(),
                val: -1.to_bigint()
            }
            .as_u64(),
            0xffff_ffff_ffff_ffffu64
        );

        assert_eq!(
            Value::Int {
                size: 8u64.to_biguint(),
                val: -1.to_bigint()
            }
            .as_u64(),
            0xffu64
        );
        assert_eq!(
            Value::Int {
                size: 8u64.to_biguint(),
                val: -128.to_bigint()
            }
            .as_u64(),
            0x80u64
        )
    }

    #[test]
    fn as_u32_chunks_works_for_ints() {
        assert_eq!(
            Value::Int {
                size: 64u64.to_biguint(),
                val: i64::MAX.to_bigint()
            }
            .as_u32_chunks(),
            num::bigint::ToBigUint::to_biguint(&i64::MAX).unwrap()
        );
        assert_eq!(
            Value::Int {
                size: 64u64.to_biguint(),
                val: i64::MIN.to_bigint()
            }
            .as_u32_chunks(),
            0x8000_0000_0000_0000u64.to_biguint()
        );
        assert_eq!(
            Value::Int {
                size: 64u64.to_biguint(),
                val: -1.to_bigint()
            }
            .as_u32_chunks(),
            0xffff_ffff_ffff_ffffu64.to_biguint()
        );
        assert_eq!(
            Value::Int {
                size: 8u64.to_biguint(),
                val: -1.to_bigint()
            }
            .as_u32_chunks(),
            0xffu64.to_biguint()
        );
        assert_eq!(
            Value::Int {
                size: 8u64.to_biguint(),
                val: -128.to_bigint()
            }
            .as_u32_chunks(),
            0x80u64.to_biguint()
        )
    }

    macro_rules! test_conversion {
        ($name:ident, $value:expr, $expected_u64:expr) => {
            #[test]
            fn $name() {
                assert_eq!($value.as_u64(), $expected_u64);
                assert_eq!($value.as_u32_chunks(), $expected_u64.to_biguint());
            }
        };
    }

    test_conversion! {
        concat_works,
        Value::Concat (
            vec![
                Value::Int {
                    size: 8u64.to_biguint(),
                    val: -1.to_bigint(),
                },
                Value::Bit(true),
                Value::Undef(7u64.to_biguint()),
                Value::UInt {
                    size: 8u64.to_biguint(),
                    val: 3u32.to_biguint()
                },
                Value::Bit(true),
            ]
        ),
        0b1111_1111_1000_0000_0000_0011_1u64
    }
}
