use std::collections::HashMap;

use color_eyre::eyre::bail;
use spade_common::name::{Identifier, NameID};
use spade_hir_lowering::MirLowerable;
use spade_types::{ConcreteType, PrimitiveType};
use vcd::Value;

use crate::translation::{translate_uint, MaybeValue};

pub enum StructuralValue {
    HighImp,
    Undef,
    /// An enum value with a tag that is not valid for that enum
    InvalidTag(u64),
    Bits(String),
    Tuple(Vec<StructuralValue>),
    Array(Vec<StructuralValue>),
    Struct(Vec<(Identifier, StructuralValue)>),
    Enum(NameID, Vec<(Identifier, StructuralValue)>),
    Memory,
    Unsized,
}

pub fn translate_structural_value(
    in_value: &[Value],
    value_str: &str,
    t: &ConcreteType,
) -> StructuralValue {
    let value_len = in_value.len();
    let type_size = t.to_mir_type().size();
    let missing_values = type_size as usize - value_len;

    if type_size == 0 {
        return StructuralValue::Unsized;
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
        ConcreteType::Tuple(inner) => {
            let mut inner_result = vec![];
            let mut offset = 0;
            for t in inner.iter() {
                let end = offset + t.to_mir_type().size() as usize;
                inner_result.push(translate_structural_value(
                    &value[offset..end],
                    &value_str[offset..end],
                    t,
                ));
                offset = end;
            }

            StructuralValue::Tuple(inner_result)
        }
        ConcreteType::Struct { name: _, members } => {
            let mut offset = 0;

            let mut inner_result = vec![];

            for (name, t) in members.iter() {
                let end = offset + t.to_mir_type().size() as usize;
                inner_result.push((
                    name.clone(),
                    translate_structural_value(&value[offset..end], &value_str[offset..end], t),
                ));
                offset = end;
            }
            StructuralValue::Struct(inner_result)
        }
        ConcreteType::Array { inner, size } => {
            let mut offset = 0;
            let mut inner_result = vec![];
            for _ in 0..*size {
                let end = offset + inner.to_mir_type().size() as usize;
                inner_result.push(translate_structural_value(
                    &value[offset..end],
                    &value_str[offset..end],
                    inner,
                ));
                offset = end;
            }
            StructuralValue::Array(inner_result)
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
                            StructuralValue::InvalidTag(tag)
                        } else {
                            let variant_idx = tag as usize;
                            let (variant_name, inner_types) = &options[variant_idx];

                            let mut members = vec![];
                            let mut offset = tag_size;
                            for (name, t) in inner_types.iter() {
                                let end = offset + t.to_mir_type().size() as usize;
                                members.push((
                                    name.clone(),
                                    translate_structural_value(
                                        &value[offset..end],
                                        &value_str[offset..end],
                                        &t,
                                    ),
                                ));
                                offset = end;
                            }

                            StructuralValue::Enum(variant_name.clone(), members)
                        }
                    }
                }
                MaybeValue::Undef => StructuralValue::Undef,
                MaybeValue::HighImpedance => StructuralValue::HighImp,
            }
        }
        ConcreteType::Single {
            base: PrimitiveType::Bool | PrimitiveType::Clock,
            params: _,
        } => StructuralValue::Bits(value_str.to_string()),
        ConcreteType::Single {
            base: PrimitiveType::Int | PrimitiveType::Uint,
            params: _,
        } => StructuralValue::Bits(value_str.to_string()),
        ConcreteType::Single {
            base: PrimitiveType::Memory,
            params: _,
        } => StructuralValue::Memory,
        ConcreteType::Integer(_) => {
            panic!("Found a variable with type level integer in the vcd file")
        }
        ConcreteType::Backward(inner) => translate_structural_value(in_value, value_str, inner),
        ConcreteType::Wire(inner) => translate_structural_value(in_value, value_str, inner),
    }
}

pub fn translate_string(
    name: &str,
    value: &str,
    types: &HashMap<String, Option<ConcreteType>>,
) -> color_eyre::Result<Option<StructuralValue>> {
    let mut value_vcd = Vec::with_capacity(value.len());
    for c in value.chars() {
        value_vcd.push(match c.to_ascii_lowercase() {
            '0' => Value::V0,
            '1' => Value::V1,
            'x' => Value::X,
            'z' => Value::Z,
            other => bail!("Invalid vcd character: {other}"),
        })
    }

    if let Some(Some(t)) = types.get(name) {
        Ok(Some(translate_structural_value(&value_vcd, value, &t)))
    } else {
        Ok(None)
    }
}
