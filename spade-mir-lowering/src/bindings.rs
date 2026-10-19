use num::{BigInt, BigUint, CheckedSub, One, ToPrimitive, Zero};
use spade_common::{
    location_info::{Loc, WithLocation},
    num_ext::{InfallibleToBigInt, InfallibleToBigUint},
};
use spade_diagnostics::{diag_anyhow, diag_bail};
use spade_lir::{self as lir, BackOperator};
use spade_mir::{self as mir, type_list::MirTypeList};

use crate::{Context, Result, ValueNameExt, enum_util, types::TypeExt};

// NOTE: We may want to consider getting rid of this clone derive
// eventually
#[derive(Clone)]
pub(crate) struct BindingLoweringContext {
    pub fwd: lir::Type,
    pub back: lir::Type,

    pub lowered_fwd: Vec<Loc<lir::ValueName>>,
    pub lowered_back: Vec<Loc<lir::ValueName>>,
}

// An operator which takes no backward components and produces no backward values
fn fwd_only_operator(
    binding: &Loc<&mir::Binding>,
    bc: BindingLoweringContext,
    inner: &dyn Fn(&lir::Type) -> (lir::Operator, Vec<Loc<lir::ValueName>>),
) -> Result<Vec<Loc<lir::Statement>>> {
    if bc.back.size() != BigUint::ZERO {
        diag_bail!(
            binding,
            "{} was applied to a type with a backward component ({})",
            binding.operator,
            binding.ty
        );
    }

    let (operator, operands) = inner(&bc.fwd);

    Ok(vec![
        lir::Statement::Binding(lir::Binding {
            name: binding.name.lower_fwd(),
            operator: operator,
            operands: operands,
            ty: bc.fwd.clone(),
            loc: binding.loc.clone(),
        })
        .at_loc(binding),
    ])
}

pub(crate) fn trivial_fwd_operator(
    binding: &Loc<&mir::Binding>,
    bc: BindingLoweringContext,
    new_operator: lir::Operator,
) -> Result<Vec<Loc<lir::Statement>>> {
    fwd_only_operator(binding, bc.clone(), &|_| {
        (new_operator.clone(), bc.lowered_fwd.clone())
    })
}

pub(crate) fn maybe_fwd_operator(
    binding: &Loc<&mir::Binding>,
    bc: BindingLoweringContext,
    inner: &dyn Fn(&lir::Type) -> (lir::Operator, Vec<Loc<lir::ValueName>>),
) -> Result<Vec<Loc<lir::Statement>>> {
    let (operator, operands) = inner(&bc.fwd);

    Ok(vec![
        lir::Statement::Binding(lir::Binding {
            name: binding.name.lower_fwd(),
            operator: operator,
            operands: operands,
            ty: bc.fwd.clone(),
            loc: binding.loc.clone(),
        })
        .at_loc(binding),
    ])
}

pub(crate) fn maybe_back_operator(
    binding: &Loc<&mir::Binding>,
    bc: BindingLoweringContext,
    inner: &dyn Fn(&lir::Type) -> (lir::Operator, Vec<Loc<lir::ValueName>>),
) -> Result<Vec<Loc<lir::Statement>>> {
    let (operator, operands) = inner(&bc.back);

    Ok(vec![
        lir::Statement::Binding(lir::Binding {
            name: binding.name.lower_back(),
            operator: operator,
            operands: operands,
            // Safe unwrap, the assert above guards
            ty: bc.back.clone(),
            loc: binding.loc.clone(),
        })
        .at_loc(binding),
    ])
}

pub(crate) fn lower_match(
    binding: &Loc<&mir::Binding>,
    types: &MirTypeList,
    bc: BindingLoweringContext,
) -> Result<Vec<Loc<lir::Statement>>> {
    let fwd_operands = binding.operands.iter().skip(1).cloned().collect::<Vec<_>>();

    let (fwd_copies, fwd_operands): (Vec<_>, Vec<_>) = fwd_operands
        .chunks(3)
        .map(|chunk| {
            let [alias, cond, val] = chunk else {
                diag_bail!(binding, "Found non-mod 3 operands to match")
            };
            Ok((
                // TODO: There will now be `Nop` copies of these bindings since the MIR
                // introduces them but does not make use of them
                lir::Statement::Binding(lir::Binding {
                    name: alias.lower_fwd(),
                    operator: lir::Operator::Alias,
                    operands: vec![binding.operands[0].lower_fwd().at_loc(&binding.operands[0])],
                    ty: types[&binding.operands[0]].lower().0,
                    loc: None,
                })
                .near_loc(binding),
                [cond.lower_fwd().at_loc(&cond), val.lower_fwd().at_loc(&val)],
            ))
        })
        .collect::<Result<Vec<_>>>()?
        .into_iter()
        .unzip();

    Ok(fwd_copies
        .into_iter()
        .chain([lir::Statement::Binding(lir::Binding {
            name: binding.name.lower_fwd(),
            operator: spade_lir::Operator::Match,
            operands: fwd_operands.into_iter().flatten().collect(),
            ty: bc.fwd,
            loc: binding.loc,
        })
        .at_loc(&binding)])
        .collect())
}

pub(crate) fn lower_sign_extend(
    binding: &Loc<&mir::Binding>,
    types: &MirTypeList,
    bc: BindingLoweringContext,
    ctx: &Context,
) -> Result<Vec<Loc<lir::Statement>>> {
    debug_assert!(matches!(binding.operator, mir::Operator::SignExtend));

    let msb_name = lir::ValueName::Forward(mir::ValueName::Expr(ctx.idtracker.next()));
    let replicated_name = lir::ValueName::new_fwd(ctx.idtracker);
    let in_ty = &types[&binding.operands[0]]; // TODO Don't index, use .get and bail on error
    if in_ty.size() == BigUint::ZERO {
        diag_bail!(binding, "Sign extend called on zero sized type");
    };

    let replicated_size = binding.ty.size() - in_ty.size();

    Ok(vec![
        lir::Statement::Binding(lir::Binding {
            name: msb_name.clone(),
            operator: lir::Operator::RangeSlice {
                start: in_ty.size(),
                end_exclusive: in_ty.size(),
            },
            operands: vec![binding.operands[0].map_ref(|op| op.lower_fwd())],
            ty: lir::Type::BitVector(BigUint::one()),
            loc: None,
        })
        .near_loc(binding),
        lir::Statement::Binding(lir::Binding {
            name: replicated_name.clone(),
            operator: lir::Operator::Replicate {
                copies: replicated_size.clone(),
            },
            operands: vec![msb_name.near_loc(binding)],
            ty: lir::Type::BitVector(replicated_size),
            loc: None,
        })
        .near_loc(binding),
        lir::Statement::Binding(lir::Binding {
            name: binding.name.lower_fwd(),
            operator: lir::Operator::Concat,
            operands: vec![
                replicated_name.near_loc(binding),
                binding.operands[0].map_ref(|op| op.lower_fwd()),
            ],
            ty: bc.fwd,
            loc: binding.loc,
        })
        .at_loc(binding),
    ])
}

pub(crate) fn lower_zero_extend(
    binding: &Loc<&mir::Binding>,
    types: &MirTypeList,
    bc: BindingLoweringContext,
    ctx: &Context,
) -> Result<Vec<Loc<lir::Statement>>> {
    debug_assert!(matches!(binding.operator, mir::Operator::ZeroExtend));

    let in_ty = &types[&binding.operands[0]]; // TODO Don't index, use .get and bail on error
    if in_ty.size() == BigUint::ZERO {
        diag_bail!(binding, "Sign extend called on zero sized type");
    };

    let zeros_name = lir::ValueName::new_fwd(ctx.idtracker);

    let replicated_size = binding.ty.size() - in_ty.size();

    Ok(vec![
        lir::Statement::Constant(
            zeros_name.clone(),
            lir::Type::BitVector(replicated_size),
            spade_mir::ConstantValue::Int(BigInt::zero()),
        )
        .near_loc(binding),
        lir::Statement::Binding(lir::Binding {
            name: binding.name.lower_fwd(),
            operator: lir::Operator::Concat,
            operands: vec![
                zeros_name.near_loc(binding),
                binding.operands[0].map_ref(|op| op.lower_fwd()),
            ],
            ty: bc.fwd,
            loc: binding.loc,
        })
        .at_loc(binding),
    ])
}

pub(crate) fn lower_index_array(
    binding: &Loc<&mir::Binding>,
    types: &MirTypeList,
    bc: BindingLoweringContext,
) -> Result<Vec<Loc<lir::Statement>>> {
    debug_assert!(matches!(binding.operator, mir::Operator::IndexArray));

    let target_ty = &types[&binding.operands[0]].strip_copy_view_layers();
    let mir::types::Type::Array { inner, length: _ } = target_ty else {
        diag_bail!(binding, "IndexArray invoked on non-array ({})", target_ty);
    };

    Ok([
        maybe_fwd_operator(binding, bc.clone(), &|_binding_ty| {
            (
                lir::Operator::Slice {
                    elem_size: inner.size(),
                    direction: lir::SliceDirection::ZerothRight,
                },
                bc.lowered_fwd.clone(),
            )
        })?,
        // TODO: Ensure that this the result doesn't have a backward component
    ]
    .into_iter()
    .flatten()
    .collect())
}

pub(crate) fn lower_truncate(
    binding: &Loc<&mir::Binding>,
    bc: BindingLoweringContext,
) -> Result<Vec<Loc<lir::Statement>>> {
    debug_assert!(matches!(binding.operator, mir::Operator::Truncate));

    fwd_only_operator(binding, bc.clone(), &|ty| {
        (
            lir::Operator::RangeSlice {
                start: 0u32.to_biguint(),
                end_exclusive: ty.size(),
            },
            bc.lowered_fwd.clone(),
        )
    })
}

pub(crate) fn lower_concat(
    binding: &Loc<&mir::Binding>,
    bc: BindingLoweringContext,
) -> Result<Vec<Loc<lir::Statement>>> {
    debug_assert!(matches!(binding.operator, mir::Operator::Concat));
    Ok([
        maybe_fwd_operator(binding, bc.clone(), &|_| {
            (lir::Operator::Concat, bc.lowered_fwd.clone())
        })?,
        maybe_back_operator(binding, bc.clone(), &|_| {
            (
                lir::Operator::Back(BackOperator::Concat),
                bc.lowered_back.clone(),
            )
        })?,
    ]
    .into_iter()
    .flatten()
    .collect())
}

pub(crate) fn lower_construct_array(
    binding: &Loc<&mir::Binding>,
    bc: BindingLoweringContext,
) -> Result<Vec<Loc<lir::Statement>>> {
    debug_assert!(matches!(binding.operator, mir::Operator::ConstructArray));
    Ok([
        maybe_fwd_operator(binding, bc.clone(), &|_| {
            (
                lir::Operator::Concat,
                bc.lowered_fwd.clone().into_iter().rev().collect(),
            )
        })?,
        maybe_back_operator(binding, bc.clone(), &|_| {
            (
                lir::Operator::Back(BackOperator::Concat),
                bc.lowered_back.clone().into_iter().rev().collect(),
            )
        })?,
    ]
    .into_iter()
    .flatten()
    .collect())
}

pub(crate) fn lower_range_index_array(
    binding: &Loc<&mir::Binding>,
    bc: BindingLoweringContext,
) -> Result<Vec<Loc<lir::Statement>>> {
    let mir::Operator::RangeIndexArray {
        start,
        end_exclusive: end,
    } = &binding.inner.operator
    else {
        panic!("Expected RangeIndexArray")
    };

    let mir::types::Type::Array { inner, length: _ } = &binding.ty else {
        diag_bail!(binding, "IndexArray invoked on non-array ({})", binding.ty);
    };

    Ok([
        maybe_fwd_operator(binding, bc.clone(), &|_ty| {
            let member_size = inner.size();

            (
                lir::Operator::RangeSlice {
                    start: start.clone() * &member_size,
                    end_exclusive: end.clone() * member_size,
                },
                bc.lowered_fwd.clone(),
            )
        })?,
        maybe_fwd_operator(binding, bc.clone(), &|_ty| {
            let member_size = inner.backward_size();

            (
                lir::Operator::Back(BackOperator::RangeSlice {
                    start: start.clone() * &member_size,
                    end_exclusive: end.clone() * member_size,
                }),
                bc.lowered_back.clone(),
            )
        })?,
    ]
    .into_iter()
    .flatten()
    .collect())
}

pub(crate) fn lower_construct_tuple(
    binding: &Loc<&mir::Binding>,
    bc: BindingLoweringContext,
) -> Result<Vec<Loc<lir::Statement>>> {
    debug_assert!(matches!(binding.operator, mir::Operator::ConstructTuple));
    Ok([
        maybe_fwd_operator(binding, bc.clone(), &|_ty| {
            (lir::Operator::Concat, bc.lowered_fwd.clone())
        })?,
        maybe_back_operator(binding, bc.clone(), &|_ty| {
            (
                lir::Operator::Back(BackOperator::Concat),
                bc.lowered_back.clone(),
            )
        })?,
    ]
    .into_iter()
    .flatten()
    .collect())
}

pub(crate) fn lower_construct_enum(
    binding: &Loc<&mir::Binding>,
    bc: BindingLoweringContext,
    ctx: &Context,
) -> Result<Vec<Loc<lir::Statement>>> {
    let mir::Operator::ConstructEnum { variant } = &binding.inner.operator else {
        panic!("Expected ConstructEnum")
    };

    let mir::types::Type::Enum(options) = &binding.ty else {
        diag_bail!(
            binding,
            "Attempted enum construction of non-enum ({})",
            binding.ty
        );
    };

    if bc.back.size() != BigUint::ZERO {
        diag_bail!(
            binding,
            "Enum lir type has backward component ({})",
            binding.ty
        )
    }

    let tag_const = lir::ValueName::Forward(mir::ValueName::Expr(ctx.idtracker.next()));
    let tag_size = enum_util::tag_size(options.len());

    let mut operands = vec![tag_const.clone().near_loc(binding)];
    operands.extend(bc.lowered_fwd);

    Ok(vec![
        lir::Statement::Constant(
            tag_const.clone(),
            lir::Type::BitVector(tag_size.to_biguint()),
            mir::ConstantValue::Int(variant.to_bigint()),
        )
        .near_loc(binding),
        lir::Statement::Binding(lir::Binding {
            name: binding.name.lower_fwd(),
            operator: lir::Operator::Concat,
            operands,
            ty: bc.fwd,
            loc: binding.loc,
        })
        .at_loc(binding),
    ])
}

pub(crate) fn lower_construct_copy_view(
    binding: &Loc<&mir::Binding>,
    bc: BindingLoweringContext,
) -> Result<Vec<Loc<lir::Statement>>> {
    debug_assert!(matches!(binding.operator, mir::Operator::ConstructCopyView));

    if binding.operands.len() != 1 {
        diag_bail!(binding, "Expected exactly one operand for Inspect");
    }
    // Safe index, we check the length above
    let op = &binding.operands[0];

    Ok(vec![
        lir::Statement::Binding(spade_lir::Binding {
            name: binding.name.lower_fwd(),
            operator: spade_lir::Operator::Concat,
            operands: vec![op.lower_fwd().at_loc(&op), op.lower_back().at_loc(&op)],
            ty: spade_lir::Type::BitVector(bc.fwd.size() + bc.back.size()),
            loc: binding.loc,
        })
        .at_loc(binding),
    ])
}

pub(crate) fn lower_inspect(
    binding: &Loc<&mir::Binding>,
    bc: BindingLoweringContext,
    ctx: &Context,
) -> Result<Vec<Loc<lir::Statement>>> {
    debug_assert!(matches!(binding.operator, mir::Operator::Inspect));

    if binding.operands.len() != 1 {
        diag_bail!(binding, "Expected exactly one operand for Inspect");
    }
    // Safe index, we check the length above
    let op = &binding.operands[0];

    let ty = binding.ty.strip_copy_view_layers();

    let size = ty.size();
    let backward_size = ty.backward_size();

    // TODO: A function for these creations would be nice to have
    let new_left_name = lir::ValueName::Forward(mir::ValueName::Expr(ctx.idtracker.next()));
    let new_right_name = lir::ValueName::Forward(mir::ValueName::Expr(ctx.idtracker.next()));

    Ok(vec![
        lir::Statement::Binding(lir::Binding {
            name: new_left_name.clone(),
            operator: lir::Operator::RangeSlice {
                start: BigUint::zero(),
                end_exclusive: backward_size.clone(),
            },
            operands: vec![op.lower_fwd().at_loc(&op)],
            ty: spade_lir::Type::BitVector(backward_size.clone()),
            loc: None,
        })
        .near_loc(binding),
        lir::Statement::Binding(lir::Binding {
            name: new_right_name.clone(),
            operator: lir::Operator::RangeSlice {
                start: backward_size.clone(),
                end_exclusive: size.clone() + backward_size.clone(),
            },
            operands: vec![op.lower_fwd().at_loc(&op)],
            ty: spade_lir::Type::BitVector(size),
            loc: None,
        })
        .near_loc(binding),
        lir::Statement::Binding(lir::Binding {
            name: binding.name.lower_fwd(),
            operator: spade_lir::Operator::Concat,
            operands: vec![
                new_left_name.near_loc(binding),
                new_right_name.near_loc(binding),
            ],
            ty: spade_lir::Type::BitVector(bc.fwd.size() + bc.back.size()),
            loc: binding.loc,
        })
        .at_loc(binding),
    ])
}

pub(crate) fn lower_is_enum_variant(
    binding: &Loc<&mir::Binding>,
    bc: BindingLoweringContext,
    types: &MirTypeList,
    ctx: &Context,
) -> Result<Vec<Loc<lir::Statement>>> {
    let mir::Operator::IsEnumVariant { variant } = &binding.inner.operator else {
        panic!("Expected IsEnumVariant")
    };

    let enum_type = &types[&binding.operands[0]];

    // Special case for enum without members and payload
    if enum_type.size() == BigUint::ZERO {
        Ok(vec![
            lir::Statement::Constant(
                binding.name.lower_fwd(),
                lir::Type::BitVector(BigUint::one()),
                mir::ConstantValue::Bool(true),
            )
            .at_loc(binding),
        ])
    } else {
        let tag_size = enum_util::tag_size(enum_type.assume_enum().len());
        let total_size = enum_type.size();

        let tag_end = &total_size - 1u32.to_biguint();
        let tag_start = &total_size - tag_size as u64;

        let expected_tag = lir::ValueName::Forward(mir::ValueName::Expr(ctx.idtracker.next()));
        let extracted_tag = lir::ValueName::Forward(mir::ValueName::Expr(ctx.idtracker.next()));

        Ok(vec![
            lir::Statement::Constant(
                expected_tag.clone(),
                lir::Type::BitVector(tag_size.to_biguint()),
                mir::ConstantValue::Int(variant.to_bigint()),
            )
            .near_loc(binding),
            lir::Statement::Binding(lir::Binding {
                name: extracted_tag.clone(),
                operator: lir::Operator::RangeSlice {
                    start: tag_start,
                    end_exclusive: tag_end + BigUint::one(),
                },
                operands: bc.lowered_fwd,
                ty: lir::Type::BitVector(tag_size.to_biguint()),
                loc: binding.loc,
            })
            .near_loc(binding),
            lir::Statement::Binding(spade_lir::Binding {
                name: binding.name.lower_fwd(),
                operator: lir::Operator::Eq,
                operands: vec![
                    extracted_tag.near_loc(binding),
                    expected_tag.near_loc(binding),
                ],
                ty: lir::Type::BitVector(BigUint::one()),
                loc: binding.loc,
            })
            .at_loc(binding),
        ])
    }
}

pub(crate) fn lower_enum_member(
    binding: &Loc<&mir::Binding>,
    bc: BindingLoweringContext,
    types: &MirTypeList,
) -> Result<Vec<Loc<lir::Statement>>> {
    let mir::Operator::EnumMember {
        variant,
        member_index,
    } = &binding.inner.operator
    else {
        panic!("Expected EnumMember")
    };

    let enum_type = &types[&binding.operands[0]];

    let variant_list = enum_type.assume_enum();
    let tag_size = enum_util::tag_size(variant_list.len());
    let full_size = enum_type.size();

    if variant_list.len() == 0 {
        Ok(vec![
            lir::Statement::Constant(
                binding.name.lower_fwd(),
                lir::Type::BitVector(BigUint::zero()),
                spade_mir::ConstantValue::Undef(BigUint::zero()),
            )
            .at_loc(binding),
        ])
    } else {
        let member_start = (tag_size as u64)
            + variant_list[*variant][0..*member_index]
                .iter()
                .map(|t| t.size())
                .sum::<BigUint>();

        let member_end = &member_start + variant_list[*variant][*member_index].size();

        let upper_idx = &full_size
            .checked_sub(&member_start)
            .ok_or_else(|| diag_anyhow!(binding, "Checked sub failed"))?;
        let lower_idx = full_size
            .checked_sub(&member_end)
            .ok_or_else(|| diag_anyhow!(binding, "Checked sub failed"))?;

        // TODO: No longer a fwd_only_operator I think
        fwd_only_operator(binding, bc.clone(), &|_| {
            (
                lir::Operator::RangeSlice {
                    start: lower_idx.clone(),
                    end_exclusive: upper_idx.clone(),
                },
                bc.lowered_fwd.clone(),
            )
        })
    }
}

pub(crate) fn lower_index_tuple(
    binding: &Loc<&mir::Binding>,
    bc: BindingLoweringContext,
    types: &MirTypeList,
) -> Result<Vec<Loc<lir::Statement>>> {
    let mir::Operator::IndexTuple(idx) = &binding.inner.operator else {
        panic!("Expected IndexTuple")
    };

    let outer_type = &types[&binding.operands[0]];
    let inner_types = match &outer_type.strip_copy_view_layers() {
        mir::types::Type::Tuple(fields) => fields.clone(),
        mir::types::Type::Struct(fields) => fields.iter().map(|(_name, ty)| ty.clone()).collect(),
        mir::types::Type::Array { inner, length } => {
            vec![(**inner).clone(); length.to_usize().unwrap()]
        }
        _ => diag_bail!(binding, "Tuple index on unsupported type ({})", binding.ty),
    };

    let is_copy_view = matches!(outer_type, mir::types::Type::CopyView(_));

    // TODO: Also handle backward tuple indexinng
    // TODO: If this TODO is still valid, why do no tests fail
    maybe_fwd_operator(binding, bc.clone(), &|_| {
        let sizes = inner_types.iter().map(|t| t.size()).collect::<Vec<_>>();

        // Compute the start index of the element we're looking for
        let mut start_bit = BigUint::zero();
        for i in 0..*idx {
            start_bit += &sizes[i as usize];
        }

        let target_width = &sizes[*idx as usize];
        let end_bit = &start_bit + target_width;
        let total_width: BigUint = sizes.iter().sum();

        (
            lir::Operator::RangeSlice {
                start: &total_width - end_bit,
                end_exclusive: &total_width - start_bit,
            },
            bc.lowered_fwd.clone(),
        )
    })
}

pub(crate) fn lower_instance(
    binding: &Loc<&mir::Binding>,
    bc: BindingLoweringContext,
    types: &MirTypeList,
) -> Result<Vec<Loc<lir::Statement>>> {
    let mir::Operator::Instance {
        name,
        params,
        argument_names,
        loc: _,
        verilog_attr_groups,
    } = &binding.inner.operator
    else {
        panic!("Expected Instance")
    };

    let (mut inputs, mut outputs): (Vec<_>, Vec<_>) = argument_names
        .iter()
        .zip(&binding.operands)
        .map(|(arg_name, value)| {
            let (fwd, back) = types[value].lower();
            (
                (
                    arg_name.mangle_input(),
                    fwd,
                    value.map_ref(|v| v.lower_fwd()),
                ),
                (
                    arg_name.mangle_output(),
                    back,
                    value.map_ref(|v| v.lower_back()),
                ),
            )
        })
        .unzip();

    inputs.push((
        "input__".to_string(),
        bc.back,
        binding.name.map_ref(|n| n.lower_back()).clone(),
    ));
    outputs.push((
        "output__".to_string(),
        bc.fwd,
        binding.name.map_ref(|n| n.lower_fwd()).clone(),
    ));

    let output_declarations = outputs
        .iter()
        .map(|(_, ty, value_name)| {
            lir::Statement::Binding(lir::Binding {
                name: value_name.inner.clone(),
                operator: lir::Operator::DeclareInstantiationOutput,
                operands: vec![],
                ty: ty.clone(),
                loc: None,
            })
            .near_loc(value_name)
        })
        .collect::<Vec<_>>();

    Ok(output_declarations
        .into_iter()
        .chain([lir::Statement::Instance {
            name: name.clone(),
            params: params.clone(),
            inputs: inputs.into_iter().collect(),
            outputs: outputs.into_iter().collect(),
            verilog_attr_groups: verilog_attr_groups.clone(),
        }
        .at_loc(binding)])
        .collect())
}

pub(crate) fn lower_create_port(
    binding: &Loc<&mir::Binding>,
    ctx: &Context,
) -> Result<Vec<Loc<lir::Statement>>> {
    let mir::Operator::CreatePort = &binding.inner.operator else {
        panic!("Expected CreatePort")
    };

    let (left_ty, right_ty) = match &binding.ty {
        mir::types::Type::Tuple(inner) => {
            let [left, right] = inner.as_slice() else {
                diag_bail!(binding, "CreatePort did not create a tuple of two elements")
            };
            (left, right)
        }
        _ => diag_bail!(binding, "CreatePort did not create a tuple of two elements"),
    };

    let left_fwd = lir::ValueName::new_fwd(ctx.idtracker);
    let left_back = lir::ValueName::new_back(ctx.idtracker);
    let right_fwd = lir::ValueName::new_fwd(ctx.idtracker);
    let right_back = lir::ValueName::new_back(ctx.idtracker);

    let new_stmts = [
        // Declare the backward wires
        lir::Statement::Binding(spade_lir::Binding {
            name: left_back.clone(),
            operator: spade_lir::Operator::Nop,
            operands: vec![],
            ty: lir::Type::BitVector(left_ty.backward_size()),
            loc: binding.loc.clone(),
        })
        .near_loc(binding),
        lir::Statement::Binding(spade_lir::Binding {
            name: right_back.clone(),
            operator: spade_lir::Operator::Nop,
            operands: vec![],
            ty: lir::Type::BitVector(right_ty.backward_size()),
            loc: binding.loc.clone(),
        })
        .near_loc(binding),
        // Connect the backward wires to the forward wires
        lir::Statement::Binding(spade_lir::Binding {
            name: left_fwd.clone(),
            operator: spade_lir::Operator::Alias,
            operands: vec![right_back.clone().near_loc(binding)],
            ty: lir::Type::BitVector(left_ty.size()),
            loc: binding.loc.clone(),
        })
        .near_loc(binding),
        lir::Statement::Binding(spade_lir::Binding {
            name: right_fwd.clone(),
            operator: spade_lir::Operator::Alias,
            operands: vec![left_back.clone().near_loc(binding)],
            ty: lir::Type::BitVector(right_ty.size()),
            loc: binding.loc.clone(),
        })
        .near_loc(binding),
        // Create the final result
        lir::Statement::Binding(lir::Binding {
            name: binding.name.lower_fwd(),
            operator: spade_lir::Operator::Concat,
            operands: vec![left_fwd.near_loc(binding), right_fwd.near_loc(binding)],
            ty: lir::Type::BitVector(binding.ty.size()),
            loc: binding.loc.clone(),
        })
        .at_loc(binding),
        lir::Statement::Binding(lir::Binding {
            name: binding.name.lower_back(),
            operator: spade_lir::Operator::Back(BackOperator::Concat),
            operands: vec![left_back.near_loc(binding), right_back.near_loc(binding)],
            ty: lir::Type::BitVector(binding.ty.backward_size()),
            loc: binding.loc.clone(),
        })
        .at_loc(binding),
    ];

    Ok(new_stmts.into_iter().collect())
}

pub(crate) fn lower_alias(
    binding: &Loc<&mir::Binding>,
    bc: BindingLoweringContext,
) -> Result<Vec<Loc<lir::Statement>>> {
    let mir::Operator::Alias = &binding.inner.operator else {
        panic!("Expected Alias")
    };

    Ok([
        maybe_fwd_operator(binding, bc.clone(), &|_| {
            (
                lir::Operator::Alias,
                bc.lowered_fwd.clone().into_iter().collect(),
            )
        })?,
        maybe_back_operator(binding, bc.clone(), &|_| {
            (
                lir::Operator::Alias,
                bc.lowered_back.clone().into_iter().collect(),
            )
        })?,
    ]
    .into_iter()
    .flatten()
    .collect())
}

pub(crate) fn lower_black_box_alias(
    binding: &Loc<&mir::Binding>,
    bc: BindingLoweringContext,
) -> Result<Vec<Loc<lir::Statement>>> {
    let mir::Operator::BlackBoxAlias = &binding.inner.operator else {
        panic!("Expected BlackBoxAlias")
    };

    Ok([
        maybe_fwd_operator(binding, bc.clone(), &|_| {
            (
                lir::Operator::BlackBoxAlias,
                bc.clone().lowered_fwd.into_iter().rev().collect(),
            )
        })?,
        maybe_back_operator(binding, bc.clone(), &|_| {
            (
                lir::Operator::Back(BackOperator::BlackBoxAlias),
                bc.lowered_back.clone().into_iter().rev().collect(),
            )
        })?,
    ]
    .into_iter()
    .flatten()
    .collect())
}

pub(crate) fn lower_nop(
    binding: &Loc<&mir::Binding>,
    bc: BindingLoweringContext,
) -> Result<Vec<Loc<lir::Statement>>> {
    let mir::Operator::Nop = &binding.inner.operator else {
        panic!("Expected Nop")
    };

    // TODO: Try to figure out if we can do this pattern with fewer clones
    Ok([
        maybe_fwd_operator(binding, bc.clone(), &|_| {
            (
                lir::Operator::Nop,
                bc.lowered_fwd.clone().into_iter().rev().collect(),
            )
        })?,
        maybe_back_operator(binding, bc.clone(), &|_| {
            (
                lir::Operator::Nop,
                bc.lowered_back.clone().into_iter().rev().collect(),
            )
        })?,
    ]
    .into_iter()
    .flatten()
    .collect())
}

fn compute_forward_tuple_index(
    tuple_type: &mir::types::Type,
    idx: u64,
) -> std::ops::Range<BigUint> {
    let inner_types = tuple_type.strip_copy_view_layers().assume_tuple_like();
    let sizes = inner_types.iter().map(|t| t.size()).collect::<Vec<_>>();
    compute_tuple_index(idx, &sizes, BigUint::zero())
}

fn compute_backward_tuple_index(
    tuple_type: &mir::types::Type,
    idx: u64,
) -> std::ops::Range<BigUint> {
    let inner_types = tuple_type.strip_copy_view_layers().assume_tuple_like();
    let sizes = inner_types
        .iter()
        .map(|t| t.backward_size())
        .collect::<Vec<_>>();
    compute_tuple_index(idx, &sizes, BigUint::zero())
}

fn compute_copied_backward_tuple_index(
    tuple_type: &mir::types::Type,
    idx: u64,
) -> std::ops::Range<BigUint> {
    let stripped_type = tuple_type.strip_copy_view_layers();
    let inner_types = stripped_type.assume_tuple_like();
    let sizes = inner_types
        .iter()
        .map(|t| t.backward_size())
        .collect::<Vec<_>>();
    let offset = stripped_type.size();
    compute_tuple_index(idx, &sizes, offset)
}

fn compute_tuple_index(idx: u64, sizes: &[BigUint], offset: BigUint) -> std::ops::Range<BigUint> {
    // Compute the start index of the element we're looking for
    let mut start_bit = BigUint::zero();
    for i in 0..idx {
        start_bit += &sizes[i as usize];
    }

    let target_width = &sizes[idx as usize];

    let end_bit = &start_bit + target_width;

    let total_width: BigUint = sizes.iter().sum::<BigUint>() + offset;

    total_width.clone() - start_bit - 1u32.to_biguint()..total_width.clone() - end_bit
}
