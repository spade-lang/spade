use num::{bigint::Sign, BigInt, BigUint, ToPrimitive, Zero};
use spade_common::num_ext::InfallibleToBigUint;
use spade_hir_lowering::MirLowerable;
use spade_types::{ConcreteType, PrimitiveType};
use vcd::Value;

trait ToBitCountExt {
    /// Converts a uint to a usize, panicking if it does not fit, with a message
    /// about not supporting more than usize::MAX bytes
    fn to_bit_count(&self) -> usize;
}
impl ToBitCountExt for BigUint {
    fn to_bit_count(&self) -> usize {
        self.to_usize()
            .unwrap_or_else(|| panic!("Bit counts > {} are unsupported", usize::MAX))
    }
}
impl ToBitCountExt for BigInt {
    fn to_bit_count(&self) -> usize {
        self.to_usize()
            .unwrap_or_else(|| panic!("Bit counts < 0 and > {} are unsupported", usize::MAX))
    }
}

#[derive(Debug, PartialEq, Hash, Eq)]
enum MaybeValue<T> {
    Value(T),
    Undef,
    HighImpedance,
}

impl<T> MaybeValue<T> {
    fn map<F, U>(self, f: F) -> MaybeValue<U>
    where
        F: Fn(T) -> U,
    {
        match self {
            MaybeValue::Value(t) => MaybeValue::Value(f(t)),
            MaybeValue::Undef => MaybeValue::Undef,
            MaybeValue::HighImpedance => MaybeValue::HighImpedance,
        }
    }
}

impl<T> std::fmt::Display for MaybeValue<T>
where
    T: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MaybeValue::Value(v) => write!(f, "{v}"),
            MaybeValue::Undef => write!(f, "UNDEF"),
            MaybeValue::HighImpedance => write!(f, "HIGHIMP"),
        }
    }
}

impl MaybeValue<BigInt> {
    fn write_to(&self, s: &mut String) {
        match self {
            MaybeValue::Value(val) => *s += &val.to_str_radix(10),
            MaybeValue::Undef => *s += "UNDEF",
            MaybeValue::HighImpedance => *s += "HIGHIMP",
        }
    }
}

impl MaybeValue<BigUint> {
    fn write_to(&self, s: &mut String) {
        match self {
            MaybeValue::Value(val) => *s += &val.to_str_radix(10),
            MaybeValue::Undef => *s += "UNDEF",
            MaybeValue::HighImpedance => *s += "HIGHIMP",
        }
    }
}

fn translate_uint(value: &[Value], flip: bool) -> MaybeValue<BigUint> {
    let mut result = BigUint::new(vec![]);
    let mut accumulated_bits = 0;
    let mut intermediate = 0u64;
    for v in value {
        if accumulated_bits == 64 {
            result = (result << accumulated_bits) + BigUint::from(intermediate);
            accumulated_bits = 0;
            intermediate = 0;
        }
        if v == &Value::X {
            return MaybeValue::Undef;
        } else if v == &Value::Z {
            return MaybeValue::HighImpedance;
        }
        if !flip {
            if v == &Value::V1 {
                intermediate = (intermediate << 1i32) + 1;
            } else {
                intermediate <<= 1i32
            }
        } else if v == &Value::V0 {
            intermediate = (intermediate << 1i32) + 1;
        } else {
            intermediate <<= 1i32
        }
        accumulated_bits += 1;
    }
    MaybeValue::Value((result << accumulated_bits) + BigUint::from(intermediate))
}

/// Translate a signed integer into a BigInt if all the elements are defined
/// if not returns Undef
///
/// The values must be in two's complement form and of the intended width of the
/// integer. That is, the leftmost bit is interpreted as the sign bit
fn translate_signed_int(value: &[Value]) -> MaybeValue<BigInt> {
    if value.contains(&Value::X) {
        MaybeValue::Undef
    } else if value.contains(&Value::Z) {
        MaybeValue::HighImpedance
    } else {
        let negative = value[0] == Value::V1;
        let uint_val = translate_uint(&value[1..], negative);
        if negative {
            uint_val.map(|uint| BigInt::from_biguint(Sign::Minus, uint + BigUint::from(true)))
        } else {
            uint_val.map(|uint| BigInt::from_biguint(Sign::Plus, uint))
        }
    }
}

fn translate_unsigned_int(value: &[Value]) -> MaybeValue<BigUint> {
    if value.contains(&Value::X) {
        MaybeValue::Undef
    } else if value.contains(&Value::Z) {
        MaybeValue::HighImpedance
    } else {
        translate_uint(value, false)
    }
}

pub fn inner_translate_value(result: &mut String, in_value: &[Value], t: &ConcreteType) {
    let value_len = in_value.len();
    let type_size = t.to_mir_type().size();
    let missing_values = type_size
        .to_usize()
        .unwrap_or_else(|| panic!("Value is wider than {} bits", usize::MAX))
        - value_len;

    // FIXME: This is a temporary hack to work around
    // lifeguard spade#214
    if type_size < value_len.to_biguint() {
        return;
    }

    if type_size == BigUint::zero() {
        return;
    }

    // Extend according to verilog specification section 18.2.2
    let extend_value = match in_value[0] {
        Value::V0 => Value::V0,
        Value::V1 => Value::V0,
        Value::X => Value::X,
        Value::Z => Value::Z,
    };

    let value = [&vec![extend_value; missing_values], in_value].concat();

    match t {
        ConcreteType::Error => {}
        ConcreteType::Tuple(inner) => {
            result.push('(');

            let mut offset = 0;
            for (i, t) in inner.iter().enumerate() {
                let end = offset
                    + t.to_mir_type()
                        .size()
                        .to_usize()
                        .unwrap_or_else(|| panic!("Value is wider than {} bits", usize::MAX));
                inner_translate_value(result, &value[offset..end], t);
                offset = end;
                if i != inner.len() - 1 {
                    result.push(',');
                }
            }
            result.push(')')
        }
        ConcreteType::Struct {
            name: _,
            is_port: _,
            members,
            field_translators: _,
        } => {
            let mut offset = 0;

            result.push('{');
            for (i, (name, t)) in members.iter().enumerate() {
                let end = offset + t.to_mir_type().size().to_bit_count();
                *result += &format!("{name}:");
                inner_translate_value(result, &value[offset..end], t);
                offset = end;
                if i != members.len() - 1 {
                    result.push(',');
                }
            }
            result.push('}');
        }
        ConcreteType::Array { inner, size } => {
            let mut offset = 0;
            result.push('[');
            for i in 0..size.to_bit_count() {
                let end = offset + inner.to_mir_type().size().to_bit_count();
                inner_translate_value(result, &value[offset..end], inner);
                offset = end;
                if i != size.to_bit_count() - 1 {
                    result.push(',')
                }
            }
            result.push(']');
        }
        ConcreteType::Enum { options } => {
            let tag_size = (options.len() as f32).log2().ceil() as usize;
            let tag = translate_uint(&value[0..tag_size], false);
            match tag {
                MaybeValue::Value(val) => {
                    let tag_digits = val.to_u64_digits();
                    if tag_digits.len() > 1 {
                        panic!("Tag digit count must be 1, was {}", tag_digits.len());
                    } else {
                        let tag = tag_digits.first().cloned().unwrap_or(0);
                        if tag >= options.len() as u64 {
                            *result += "?TAG?";
                        } else {
                            let variant_idx = tag as usize;
                            let (variant_name, inner_types) = &options[variant_idx];
                            *result += &format!("{}", variant_name.1.tail());

                            result.push('(');
                            let mut offset = tag_size;
                            for (i, t) in inner_types.iter().enumerate() {
                                let end = offset + t.1.to_mir_type().size().to_bit_count();
                                inner_translate_value(result, &value[offset..end], &t.1);
                                offset = end;

                                if i != inner_types.len() - 1 {
                                    result.push(',')
                                }
                            }

                            result.push(')');
                        }
                    }
                }
                MaybeValue::Undef => {
                    *result += "UNDEF";
                }
                MaybeValue::HighImpedance => {
                    *result += "HIGHIMP";
                }
            }
        }
        ConcreteType::Single {
            base: PrimitiveType::Bool | PrimitiveType::Bit | PrimitiveType::Clock,
            params: _,
        } => {
            *result += match value[0] {
                Value::V0 => "false",
                Value::V1 => "true",
                Value::X => "UNDEF",
                Value::Z => "HIGHIMP",
            }
        }
        ConcreteType::Single {
            base: PrimitiveType::Int,
            params: _,
        } => {
            translate_signed_int(&value).write_to(result);
        }
        ConcreteType::Single {
            base: PrimitiveType::Uint,
            params: _,
        } => {
            translate_unsigned_int(&value).write_to(result);
        }
        ConcreteType::Single {
            base: PrimitiveType::Memory,
            params: _,
        } => *result += "memory",
        ConcreteType::Single {
            base: PrimitiveType::InOut,
            params,
        } => match params.as_slice() {
            [inner] => inner_translate_value(result, in_value, inner),
            t => panic!("Found an inout<{t:?}> but inout only supports one type parameter"),
        },
        ConcreteType::Integer(_) => {
            panic!("Found a variable with type level integer in the vcd file")
        }
        ConcreteType::Bool(_) => {
            panic!("Found a variable with type level bool in the vcd file")
        }
        ConcreteType::String(_) => {
            panic!("Found a variable with type level string in the vcd file")
        }
        ConcreteType::Backward(inner) => inner_translate_value(result, in_value, inner),
        ConcreteType::Wire(inner) => inner_translate_value(result, in_value, inner),
    }
}

pub fn translate_value(ty: &ConcreteType, value: &[Value]) -> String {
    let mut result = String::new();
    // Try to translate the name back into a name_id
    inner_translate_value(&mut result, value, ty);
    result
}

// Translates a string of `01XZ` characters into the corresponding
// VCD values
// NOTE: This function is incorrectly reported as unused when vcd-translate
// is compiled as a library
#[allow(dead_code)]
pub fn value_from_str(s: &str) -> Vec<Value> {
    s.to_lowercase()
        .chars()
        .map(|c| match c {
            'x' => Value::X,
            'z' => Value::Z,
            '0' => Value::V0,
            '1' => Value::V1,
            other => panic!("Found '{other}' in value string '{s}'"),
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use spade_common::{name::testutil::name_id, num_ext::InfallibleToBigInt};

    use super::*;

    use spade_ast::testutil::ast_ident;

    use Value::{V0, V1, X, Z};

    #[test]
    fn positive_integers_parse_correctly() {
        let values = vec![V0, V1, V0, V1, V1];

        let translated = translate_signed_int(&values);

        assert_eq!(
            translated,
            MaybeValue::Value(BigInt::new(Sign::Plus, vec![0b1011]))
        );
    }

    #[test]
    fn uint_65_works() {
        let mut values = vec![V1];
        values.append(&mut vec![V0; 64]);

        let translated = translate_uint(&values, false);

        assert_eq!(translated, MaybeValue::Value(BigUint::new(vec![0, 0, 1])));
    }

    #[test]
    fn uint_130_works() {
        let mut values = vec![V1, V0, V1];
        values.append(&mut vec![V0; 128]);

        let translated = translate_uint(&values, false);

        assert_eq!(
            translated,
            MaybeValue::Value(BigUint::new(vec![0, 0, 0, 0, 0b101]))
        );
    }

    #[test]
    fn uint_80_works() {
        let mut values = vec![V1; 16];
        values.append(&mut vec![V0; 64]);

        let translated = translate_uint(&values, false);

        assert_eq!(
            translated,
            MaybeValue::Value(BigUint::new(vec![0, 0, 0xffff]))
        );
    }

    #[test]
    fn negative_integers_parse_correctly() {
        let values = vec![V1, V1, V0, V1, V1];
        // -16 + 8 + 0  + 2 + 1 = -5

        let translated = translate_signed_int(&values);

        assert_eq!(translated, MaybeValue::Value(BigInt::from(-5)));
    }

    #[test]
    fn large_positive_unsigned_integers_parse_correctly() {
        let mut values = vec![Value::V1];
        values.append(&mut vec![Value::V0; 32]);

        let translated = translate_uint(&values, false);

        assert_eq!(
            translated,
            MaybeValue::Value(BigUint::from(0x10000_0000u64))
        )
    }

    #[test]
    fn struct_translation_works() {
        let ty = ConcreteType::Struct {
            name: name_id(0, "X").inner,
            is_port: false,
            field_translators: HashMap::new(),
            members: vec![
                (
                    ast_ident("a").inner,
                    ConcreteType::Single {
                        base: PrimitiveType::Int,
                        params: vec![ConcreteType::Integer(5u32.to_bigint())],
                    },
                ),
                (
                    ast_ident("b").inner,
                    ConcreteType::Single {
                        base: PrimitiveType::Int,
                        params: vec![ConcreteType::Integer(3u32.to_bigint())],
                    },
                ),
            ],
        };

        let value = vec![/*a*/ V0, V1, V0, V0, V0, /*b*/ V1, V0, V0];
        let mut translated = String::new();
        inner_translate_value(&mut translated, &value, &ty);

        assert_eq!(translated, "{a:8,b:-4}");
    }

    #[test]
    fn tuple_translation_works() {
        let ty = ConcreteType::Tuple(vec![
            ConcreteType::Single {
                base: PrimitiveType::Int,
                params: vec![ConcreteType::Integer(5u32.to_bigint())],
            },
            ConcreteType::Single {
                base: PrimitiveType::Int,
                params: vec![ConcreteType::Integer(3u32.to_bigint())],
            },
        ]);

        let value = vec![/*a*/ V0, V1, V0, V0, V1, /*b*/ V1, V0, V1];
        let mut translated = String::new();
        inner_translate_value(&mut translated, &value, &ty);

        assert_eq!(translated, "(9,-3)");
    }

    #[test]
    fn tuple_translation_of_undef_works() {
        let ty = ConcreteType::Tuple(vec![
            ConcreteType::Single {
                base: PrimitiveType::Int,
                params: vec![ConcreteType::Integer(5u32.to_bigint())],
            },
            ConcreteType::Single {
                base: PrimitiveType::Int,
                params: vec![ConcreteType::Integer(3u32.to_bigint())],
            },
        ]);

        let value = vec![/*a*/ X, X, X, X, /*b*/ X, X, X];
        let mut translated = String::new();
        inner_translate_value(&mut translated, &value, &ty);

        assert_eq!(translated, "(UNDEF,UNDEF)");
    }

    fn enum_ty() -> ConcreteType {
        let ty0 = vec![
            (
                ast_ident("a").inner,
                ConcreteType::Single {
                    base: PrimitiveType::Int,
                    params: vec![ConcreteType::Integer(5u32.to_bigint())],
                },
            ),
            (
                ast_ident("b").inner,
                ConcreteType::Single {
                    base: PrimitiveType::Int,
                    params: vec![ConcreteType::Integer(3u32.to_bigint())],
                },
            ),
        ];
        let ty1 = vec![(
            ast_ident("a").inner,
            ConcreteType::Single {
                base: PrimitiveType::Int,
                params: vec![ConcreteType::Integer(3u32.to_bigint())],
            },
        )];

        ConcreteType::Enum {
            options: vec![
                (name_id(0, "A").inner, ty0),
                (name_id(0, "B").inner, ty1),
                (name_id(0, "C").inner, vec![]),
            ],
        }
    }

    #[test]
    fn enum_translation_works_full_width() {
        let ty = enum_ty();

        let value = vec![
            /*tag*/ V0, V0, /*a*/ V0, V1, V0, V0, V1, /*b*/ V1, V0, V1,
        ];
        let mut translated = String::new();
        inner_translate_value(&mut translated, &value, &ty);

        assert_eq!(translated, "A(9,-3)");
    }

    #[test]
    fn enum_translation_works_half_width() {
        let ty = enum_ty();

        let value = vec![
            /*tag*/ V0, V1, /*payload*/ V0, V1, V0, /*padding*/ X, X, X, X, X,
        ];
        let mut translated = String::new();
        inner_translate_value(&mut translated, &value, &ty);

        assert_eq!(translated, "B(2)");
    }

    #[test]
    fn enum_translation_works_zero_width() {
        let ty = enum_ty();

        let value = vec![/*tag*/ V1, V0, /*payload*/ X, X, X, X, X, X, X, X];
        let mut translated = String::new();
        inner_translate_value(&mut translated, &value, &ty);

        assert_eq!(translated, "C()");
    }

    #[test]
    fn enum_translation_of_undef_is_undef() {
        let ty = enum_ty();

        let value = vec![/*tag*/ X, X, /*payload*/ X, X, X, X, X, X, X, X];
        let mut translated = String::new();
        inner_translate_value(&mut translated, &value, &ty);

        assert_eq!(translated, "UNDEF");
    }

    #[test]
    fn enum_translation_works_unknown_tag() {
        let ty = enum_ty();

        let value = vec![
            /*tag*/ V1, V1, /*a*/ X, X, X, X, X, /*b*/ X, X, X,
        ];
        let mut translated = String::new();
        inner_translate_value(&mut translated, &value, &ty);

        assert_eq!(translated, "?TAG?");
    }

    #[test]
    fn array_translation_works() {
        let ty = ConcreteType::Array {
            inner: Box::new(ConcreteType::Single {
                base: PrimitiveType::Int,
                params: vec![ConcreteType::Integer(3u32.to_bigint())],
            }),
            size: 2u32.to_bigint(),
        };

        let value = vec![V0, V0, V1, V0, V1, V0];
        let mut translated = String::new();
        inner_translate_value(&mut translated, &value, &ty);

        assert_eq!(translated, "[1,2]");
    }

    #[test]
    fn extending_x_extends_with_more_undef() {
        let ty = ConcreteType::Tuple(vec![
            ConcreteType::Single {
                base: PrimitiveType::Int,
                params: vec![ConcreteType::Integer(5u32.to_bigint())],
            },
            ConcreteType::Single {
                base: PrimitiveType::Int,
                params: vec![ConcreteType::Integer(3u32.to_bigint())],
            },
        ]);

        let value = vec![X];
        let mut translated = String::new();
        inner_translate_value(&mut translated, &value, &ty);

        assert_eq!(translated, "(UNDEF,UNDEF)");
    }

    #[test]
    fn extending_z_extends_with_more_undef() {
        let ty = ConcreteType::Tuple(vec![
            ConcreteType::Single {
                base: PrimitiveType::Int,
                params: vec![ConcreteType::Integer(5u32.to_bigint())],
            },
            ConcreteType::Single {
                base: PrimitiveType::Int,
                params: vec![ConcreteType::Integer(3u32.to_bigint())],
            },
        ]);

        let value = vec![Z];
        let mut translated = String::new();
        inner_translate_value(&mut translated, &value, &ty);

        assert_eq!(translated, "(HIGHIMP,HIGHIMP)");
    }
}
