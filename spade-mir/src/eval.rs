use std::collections::HashMap;

use itertools::Itertools;
use num::range;
use num::BigInt;
use num::BigUint;
use num::ToPrimitive;
use num::Zero;

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
    /// usize is the width of the concatenated value
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
                    let size_usize = size.to_usize().expect(&format!(
                        "Variable size {size} is too large to fit a 'usize'"
                    ));
                    let mask = BigInt::from((BigInt::from(1) << size_usize) - 1);
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
                        size: ty.size().into(),
                        val: name_vals[&ops[0]].assume_int() + name_vals[&ops[1]].assume_int(),
                    },
                    Operator::Sub => Value::Int {
                        size: ty.size().into(),
                        val: name_vals[&ops[0]].assume_int() - name_vals[&ops[1]].assume_int(),
                    },
                    Operator::Mul => todo!(),
                    Operator::Eq => todo!(),
                    Operator::Gt => todo!(),
                    Operator::Lt => todo!(),
                    Operator::Ge => todo!(),
                    Operator::Le => todo!(),
                    Operator::LeftShift => todo!(),
                    Operator::RightShift => todo!(),
                    Operator::LogicalAnd => todo!(),
                    Operator::LogicalOr => todo!(),
                    Operator::LogicalXor => todo!(),
                    Operator::LogicalNot => todo!(),
                    Operator::BitwiseAnd => todo!(),
                    Operator::BitwiseOr => todo!(),
                    Operator::BitwiseXor => todo!(),
                    Operator::USub => Value::Int {
                        size: ty.size().into(),
                        val: -name_vals[&ops[0]].assume_int(),
                    },
                    Operator::Not => todo!(),
                    Operator::BitwiseNot => todo!(),
                    Operator::DivPow2 => todo!(),
                    Operator::SignExtend { .. } => todo!(),
                    Operator::ZeroExtend { .. } => todo!(),
                    Operator::Truncate => todo!(),
                    Operator::Concat => todo!(),
                    Operator::Select => todo!(),
                    Operator::Match => todo!(),
                    Operator::ConstructArray => todo!(),
                    Operator::DeclClockedMemory { .. } => todo!(),
                    Operator::IndexArray => todo!(),
                    Operator::IndexMemory => todo!(),
                    Operator::ConstructTuple => {
                        Value::Concat(ops.iter().map(|op| name_vals[op].clone()).collect())
                    }
                    Operator::ConstructEnum {
                        variant,
                        variant_count,
                    } => {
                        let tag_size = BigUint::from(enum_util::tag_size(*variant_count));

                        let mut to_concat = vec![Value::UInt {
                            size: tag_size.clone(),
                            val: (*variant).into(),
                        }];
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
                            BigUint::from(ops.iter().map(|op| name_types[op].size()).sum::<u64>());
                        let padding_size =
                            BigUint::from(ty.size()) - tag_size - variant_member_size;
                        if padding_size != BigUint::zero() {
                            to_concat.push(Value::Undef(padding_size))
                        }

                        Value::Concat(to_concat)
                    }
                    Operator::IsEnumVariant { .. } => todo!(),
                    Operator::EnumMember { .. } => todo!(),
                    Operator::IndexTuple(_, _) => todo!(),
                    Operator::Instance(_, _) => todo!(),
                    Operator::Alias => todo!(),
                };

                (name.clone(), val)
            }
            Statement::Register(_) => panic!("trying to evaluate a register"),
            Statement::Constant(id, ty, val) => {
                let val = match val {
                    crate::ConstantValue::Int(i) => Value::Int {
                        size: ty.size().into(),
                        val: (*i).into(),
                    },
                    crate::ConstantValue::Bool(v) => Value::Bit(*v),
                };
                let name = ValueName::Expr(*id);
                name_types.insert(name.clone(), ty.clone());
                (name, val)
            }
            Statement::Assert(_) => panic!("trying to evaluate an assert statemnet"),
            Statement::Set { .. } => panic!("trying to evaluate a `set` statement"),
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

    use super::*;

    #[test]
    fn addition_works() {
        let mir = vec![
            statement!(const 0; Type::Int(16); ConstantValue::Int(5)),
            statement!(const 1; Type::Int(16); ConstantValue::Int(10)),
            statement!(e(2); Type::Int(16); Add; e(0), e(1)),
        ];

        let result = eval_statements(&mir);

        assert_eq!(result, Value::int(16, 15));
    }

    #[test]
    fn enum_construction_works() {
        let enum_t = Type::Enum(vec![vec![], vec![Type::Int(16)], vec![]]);

        let mir = vec![
            statement!(const 0; Type::Int(16); ConstantValue::Int(5)),
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
        let enum_t = Type::Enum(vec![vec![Type::Int(2)], vec![Type::Int(16)], vec![]]);

        let mir = vec![
            statement!(const 0; Type::Int(3); ConstantValue::Int(5)),
            statement!(e(1); enum_t; ConstructEnum({variant: 1, variant_count: 3}); e(0)),
        ];

        let result = eval_statements(&mir);

        assert_eq!(
            result,
            Value::Concat(vec![Value::uint(2, 1), Value::int(3, 5), Value::undef(13)])
        )
    }
}
