mod enum_util;
mod types;

use spade_common::{
    id_tracker::ExprIdTracker,
    location_info::{Loc, WithLocation},
    num_ext::{InfallibleToBigInt, InfallibleToBigUint},
};
use spade_diagnostics::{Diagnostic, diag_anyhow, diag_bail};
use spade_lir::{self as lir, BackOperator, LirArg, ValueName};
use spade_mir::{self as mir, MirInput, type_list::MirTypeList};

use num::{BigInt, BigUint, CheckedSub, One, ToPrimitive, Zero};

use crate::types::TypeExt;

pub type Result<T> = std::result::Result<T, Diagnostic>;

pub struct Context<'a> {
    pub idtracker: &'a ExprIdTracker,
}

trait ValueNameExt {
    fn lower_fwd(&self) -> lir::ValueName;
    fn lower_back(&self) -> lir::ValueName;
}
impl ValueNameExt for mir::ValueName {
    fn lower_fwd(&self) -> lir::ValueName {
        lir::ValueName::Forward(self.clone())
    }
    fn lower_back(&self) -> lir::ValueName {
        lir::ValueName::Backward(self.clone())
    }
}

pub fn lower_entity(entity: &mir::Entity, ctx: &Context) -> Result<lir::Entity> {
    entity.lower(ctx)
}

pub(crate) trait EntityExt {
    fn lower(&self, ctx: &Context) -> Result<lir::Entity>;
}

impl EntityExt for mir::Entity {
    fn lower(&self, ctx: &Context) -> Result<lir::Entity> {
        let mir::Entity {
            name,
            inputs,
            output,
            output_type,
            verilog_attr_groups,
            statements,
            inline,
        } = self;

        let types = MirTypeList::from_entity(self);

        // These are in inverted order because we change the output to be an input
        let (output_fwd, output_back) = output_type.lower();

        let (mut inputs, mut outputs): (Vec<_>, Vec<_>) = inputs
            .iter()
            .map(|input| {
                let MirInput {
                    name,
                    val_name,
                    ty,
                    no_mangle,
                } = input;

                let (fwd, back) = ty.lower();

                (
                    LirArg {
                        name: name.clone(),
                        val_name: lir::ValueName::Forward(val_name.clone().inner).at_loc(val_name),
                        ty: fwd.clone(),
                        no_mangle: *no_mangle,
                    },
                    LirArg {
                        name: name.clone(),
                        val_name: lir::ValueName::Forward(val_name.clone().inner).at_loc(val_name),
                        ty: back.clone(),
                        no_mangle: *no_mangle,
                    },
                )
            })
            .unzip();

        inputs.push(LirArg {
            name: "__input".to_string(),
            val_name: lir::ValueName::OutputBack.at_loc(output),
            ty: output_back.clone(),
            no_mangle: None,
        });
        outputs.push(LirArg {
            name: "__output".to_string(),
            val_name: lir::ValueName::OutputFwd.at_loc(output),
            ty: output_fwd.clone(),
            no_mangle: None,
        });

        let mut statements = statements
            .iter()
            .map(|stmt| stmt.lower(&types, ctx))
            .collect::<Result<Vec<_>>>()?
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();

        // TODO
        statements.push(
            lir::Statement::Binding(lir::Binding {
                name: spade_lir::ValueName::OutputFwd,
                operator: spade_lir::Operator::BlackBoxAlias,
                operands: vec![output.map_ref(|v| v.lower_fwd())],
                ty: output_fwd,
                loc: None,
            })
            .at_loc(&self.output),
        );

        Ok(lir::Entity {
            name: name.clone(),
            inputs,
            outputs,
            verilog_attr_groups: verilog_attr_groups.clone(),
            statements,
            inline: *inline,
        })
    }
}

trait StatementExt {
    fn lower(&self, types: &MirTypeList, ctx: &Context) -> Result<Vec<Loc<lir::Statement>>>;
}

impl StatementExt for Loc<mir::Statement> {
    fn lower(&self, types: &MirTypeList, ctx: &Context) -> Result<Vec<Loc<lir::Statement>>> {
        match &self.inner {
            mir::Statement::Binding(binding) => binding.at_loc(self).lower(types, ctx),
            mir::Statement::Register(mir::Register {
                name,
                ty,
                clock,
                reset,
                initial,
                value,
                loc,
            }) => {
                if let Some(_intial) = initial {
                    // TODO
                    diag_bail!(self, "Register intial is unsupported in LIR")
                }
                let (fwd, back) = ty.lower();
                if back.size() != BigUint::ZERO {
                    diag_bail!(self, "Found a register with non-zero backward size")
                }
                Ok(vec![
                    lir::Statement::Register(lir::Register {
                        name: name.lower_fwd(),
                        ty: fwd,
                        clock: clock.lower_fwd(),
                        reset: reset
                            .as_ref()
                            .map(|(trig, val)| (trig.lower_fwd(), val.lower_fwd())),
                        // TODO
                        initial: None,
                        value: value.lower_fwd(),
                        loc: loc.clone(),
                    })
                    .at_loc(self),
                ])
            }
            mir::Statement::Constant(value_name, ty, val) => Ok(vec![
                lir::Statement::Constant(value_name.lower_fwd(), ty.lower().0, val.clone())
                    .at_loc(self),
            ]),
            mir::Statement::Assert(value_name) => Ok(vec![
                lir::Statement::Assert(value_name.map_ref(|v| v.lower_fwd())).at_loc(self),
            ]),
            mir::Statement::Set { target, value } => Ok(vec![
                lir::Statement::Binding(lir::Binding {
                    name: target.lower_back(),
                    operator: spade_lir::Operator::Alias,
                    operands: vec![value.map_ref(|v| v.lower_fwd())],
                    ty: lir::Type::BitVector(types[target].backward_size()),
                    // TODO: If we don't remove this field, set it to the statement loc
                    loc: None,
                })
                .at_loc(self),
                lir::Statement::Binding(lir::Binding {
                    name: value.lower_fwd(),
                    operator: spade_lir::Operator::Alias,
                    operands: vec![target.map_ref(|v| v.lower_back())],
                    ty: lir::Type::BitVector(types[target].backward_size()),
                    // TODO: If we don't remove this field, set it to the statement loc
                    loc: None,
                })
                .at_loc(self),
            ]),
            mir::Statement::Error => Ok(vec![lir::Statement::Error.at_loc(self)]),
        }
    }
}

trait BindingExt {
    fn lower(&self, types: &MirTypeList, ctx: &Context) -> Result<Vec<Loc<lir::Statement>>>;
}

impl BindingExt for Loc<&mir::Binding> {
    fn lower(&self, types: &MirTypeList, ctx: &Context) -> Result<Vec<Loc<lir::Statement>>> {
        let (fwd, back) = self.ty.lower();

        let fwd_only_operator =
            |inner: &dyn Fn(&lir::Type) -> (lir::Operator, Vec<Loc<lir::ValueName>>)| {
                if back.size() != BigUint::ZERO {
                    diag_bail!(
                        self,
                        "{} was applied to a type with a backward component ({})",
                        self.operator,
                        self.ty
                    );
                }

                let (operator, operands) = inner(&fwd);

                Ok(vec![
                    lir::Statement::Binding(lir::Binding {
                        name: self.name.lower_fwd(),
                        operator: operator,
                        operands: operands,
                        ty: fwd.clone(),
                        loc: self.loc.clone(),
                    })
                    .at_loc(self),
                ])
            };

        let lowered_fwd = || {
            self.operands
                .iter()
                .map(|op| op.map_ref(|op| op.lower_fwd()))
                .collect()
        };
        let lowered_back = || {
            self.operands
                .iter()
                .map(|op| op.map_ref(|op| op.lower_back()))
                .collect::<Vec<_>>()
        };

        let trivial_fwd_operator =
            |new_operator: lir::Operator| -> Result<Vec<Loc<lir::Statement>>> {
                fwd_only_operator(&|_| (new_operator.clone(), lowered_fwd()))
            };

        let maybe_fwd_operator =
            |inner: &dyn Fn(&lir::Type) -> (lir::Operator, Vec<Loc<lir::ValueName>>)| {
                let (operator, operands) = inner(&fwd);

                Ok(vec![
                    lir::Statement::Binding(lir::Binding {
                        name: self.name.lower_fwd(),
                        operator: operator,
                        operands: operands,
                        ty: fwd.clone(),
                        loc: self.loc.clone(),
                    })
                    .at_loc(self),
                ])
            };

        let maybe_back_operator =
            |inner: &dyn Fn(&lir::Type) -> (lir::Operator, Vec<Loc<lir::ValueName>>)| {
                let (operator, operands) = inner(&back);

                Ok(vec![
                    lir::Statement::Binding(lir::Binding {
                        name: self.name.lower_back(),
                        operator: operator,
                        operands: operands,
                        // Safe unwrap, the assert above guards
                        ty: back.clone(),
                        loc: self.loc.clone(),
                    })
                    .at_loc(self),
                ])
            };

        match &self.operator {
            mir::Operator::Add => trivial_fwd_operator(lir::Operator::Add),
            mir::Operator::UnsignedAdd => trivial_fwd_operator(lir::Operator::UnsignedAdd),
            mir::Operator::Sub => trivial_fwd_operator(lir::Operator::Sub),
            mir::Operator::UnsignedSub => trivial_fwd_operator(lir::Operator::UnsignedSub),
            mir::Operator::Mul => trivial_fwd_operator(lir::Operator::Mul),
            mir::Operator::UnsignedMul => trivial_fwd_operator(lir::Operator::UnsignedMul),
            mir::Operator::Div => trivial_fwd_operator(lir::Operator::Div),
            mir::Operator::UnsignedDiv => trivial_fwd_operator(lir::Operator::UnsignedDiv),
            mir::Operator::Mod => trivial_fwd_operator(lir::Operator::Mod),
            mir::Operator::UnsignedMod => trivial_fwd_operator(lir::Operator::UnsignedMod),
            mir::Operator::Eq => trivial_fwd_operator(lir::Operator::Eq),
            mir::Operator::NotEq => trivial_fwd_operator(lir::Operator::NotEq),
            mir::Operator::Gt => trivial_fwd_operator(lir::Operator::Gt),
            mir::Operator::UnsignedGt => trivial_fwd_operator(lir::Operator::UnsignedGt),
            mir::Operator::Lt => trivial_fwd_operator(lir::Operator::Lt),
            mir::Operator::UnsignedLt => trivial_fwd_operator(lir::Operator::UnsignedLt),
            mir::Operator::Ge => trivial_fwd_operator(lir::Operator::Ge),
            mir::Operator::UnsignedGe => trivial_fwd_operator(lir::Operator::UnsignedGe),
            mir::Operator::Le => trivial_fwd_operator(lir::Operator::Le),
            mir::Operator::UnsignedLe => trivial_fwd_operator(lir::Operator::UnsignedLe),
            mir::Operator::LeftShift => trivial_fwd_operator(lir::Operator::LeftShift),
            mir::Operator::RightShift => trivial_fwd_operator(lir::Operator::RightShift),
            mir::Operator::ArithmeticRightShift => {
                trivial_fwd_operator(lir::Operator::ArithmeticRightShift)
            }
            mir::Operator::LogicalAnd => trivial_fwd_operator(lir::Operator::LogicalAnd),
            mir::Operator::LogicalOr => trivial_fwd_operator(lir::Operator::LogicalOr),
            mir::Operator::LogicalXor => trivial_fwd_operator(lir::Operator::LogicalXor),
            mir::Operator::LogicalNot => trivial_fwd_operator(lir::Operator::LogicalNot),
            mir::Operator::BitwiseAnd => trivial_fwd_operator(lir::Operator::BitwiseAnd),
            mir::Operator::BitwiseOr => trivial_fwd_operator(lir::Operator::BitwiseOr),
            mir::Operator::BitwiseXor => trivial_fwd_operator(lir::Operator::BitwiseXor),
            mir::Operator::ReduceAnd => trivial_fwd_operator(lir::Operator::ReduceAnd),
            mir::Operator::ReduceOr => trivial_fwd_operator(lir::Operator::ReduceOr),
            mir::Operator::ReduceXor => trivial_fwd_operator(lir::Operator::ReduceXor),
            mir::Operator::USub => trivial_fwd_operator(lir::Operator::USub),
            mir::Operator::Not => trivial_fwd_operator(lir::Operator::Not),
            mir::Operator::ReadWriteItemsInOut(val) => {
                trivial_fwd_operator(lir::Operator::ReadWriteItemsInOut(val.clone()))
            }
            mir::Operator::DivPow2 => trivial_fwd_operator(lir::Operator::DivPow2),

            mir::Operator::Select => trivial_fwd_operator(lir::Operator::Select),
            mir::Operator::Match => trivial_fwd_operator(lir::Operator::Match),
            mir::Operator::BitwiseNot => trivial_fwd_operator(lir::Operator::BitwiseNot),

            mir::Operator::ReadPort => Ok(vec![
                lir::Statement::Binding(lir::Binding {
                    name: self.name.lower_fwd(),
                    operator: lir::Operator::Alias,
                    operands: vec![self.operands[0].map_ref(|op| op.lower_back())],
                    ty: fwd,
                    loc: self.loc,
                })
                .at_loc(self),
            ]),

            mir::Operator::SignExtend => {
                let msb_name = lir::ValueName::Forward(mir::ValueName::Expr(ctx.idtracker.next()));
                let replicated_name = lir::ValueName::new_fwd(ctx.idtracker);
                let in_ty = &types[&self.operands[0]]; // TODO Don't index, use .get and bail on error
                if in_ty.size() == BigUint::ZERO {
                    diag_bail!(self, "Sign extend called on zero sized type");
                };

                let replicated_size = self.ty.size() - in_ty.size();

                Ok(vec![
                    lir::Statement::Binding(lir::Binding {
                        name: msb_name.clone(),
                        operator: lir::Operator::RangeSlice {
                            start: in_ty.size(),
                            end_exclusive: in_ty.size(),
                        },
                        operands: vec![self.operands[0].map_ref(|op| op.lower_fwd())],
                        ty: lir::Type::BitVector(BigUint::one()),
                        loc: None,
                    })
                    .near_loc(self),
                    lir::Statement::Binding(lir::Binding {
                        name: replicated_name.clone(),
                        operator: lir::Operator::Replicate {
                            copies: replicated_size.clone(),
                        },
                        operands: vec![msb_name.near_loc(self)],
                        ty: lir::Type::BitVector(replicated_size),
                        loc: None,
                    })
                    .near_loc(self),
                    lir::Statement::Binding(lir::Binding {
                        name: self.name.lower_fwd(),
                        operator: lir::Operator::Concat,
                        operands: vec![
                            replicated_name.near_loc(self),
                            self.operands[0].map_ref(|op| op.lower_fwd()),
                        ],
                        ty: fwd,
                        loc: self.loc,
                    })
                    .at_loc(self),
                ])
            }
            mir::Operator::ZeroExtend => {
                let in_ty = &types[&self.operands[0]]; // TODO Don't index, use .get and bail on error
                if in_ty.size() == BigUint::ZERO {
                    diag_bail!(self, "Sign extend called on zero sized type");
                };

                let zeros_name = lir::ValueName::new_fwd(ctx.idtracker);

                let replicated_size = self.ty.size() - in_ty.size();

                Ok(vec![
                    lir::Statement::Constant(
                        zeros_name.clone(),
                        lir::Type::BitVector(replicated_size),
                        spade_mir::ConstantValue::Int(BigInt::zero()),
                    )
                    .near_loc(self),
                    lir::Statement::Binding(lir::Binding {
                        name: self.name.lower_fwd(),
                        operator: lir::Operator::Concat,
                        operands: vec![
                            zeros_name.near_loc(self),
                            self.operands[0].map_ref(|op| op.lower_fwd()),
                        ],
                        ty: fwd,
                        loc: self.loc,
                    })
                    .at_loc(self),
                ])
            }
            mir::Operator::Truncate => fwd_only_operator(&|ty| {
                (
                    lir::Operator::RangeSlice {
                        start: 0u32.to_biguint(),
                        end_exclusive: ty.size(),
                    },
                    lowered_fwd(),
                )
            }),

            mir::Operator::Concat => Ok([
                maybe_fwd_operator(&|_| (lir::Operator::Concat, lowered_fwd()))?,
                maybe_back_operator(&|_| {
                    (lir::Operator::Back(BackOperator::Concat), lowered_back())
                })?,
            ]
            .into_iter()
            .flatten()
            .collect()),

            mir::Operator::ConstructArray => Ok([
                maybe_fwd_operator(&|_| {
                    (
                        lir::Operator::Concat,
                        lowered_fwd().into_iter().rev().collect(),
                    )
                })?,
                maybe_back_operator(&|_| {
                    (
                        lir::Operator::Back(BackOperator::Concat),
                        lowered_back().into_iter().rev().collect(),
                    )
                })?,
            ]
            .into_iter()
            .flatten()
            .collect()),

            mir::Operator::DeclClockedMemory { initial } => {
                // TODO
                Ok(vec![])
            }
            mir::Operator::IndexMemory => {
                // TODO
                Ok(vec![])
            }

            mir::Operator::IndexArray => {
                let target_ty = &types[&self.operands[0]];
                let mir::types::Type::Array { inner, length: _ } = target_ty else {
                    diag_bail!(self, "IndexArray invoked on non-array ({})", target_ty);
                };

                Ok([
                    maybe_fwd_operator(&|_self_ty| {
                        (
                            lir::Operator::Slice {
                                elem_size: inner.size(),
                                reversed: true,
                            },
                            lowered_fwd(),
                        )
                    })?,
                    // TODO: Ensure that this the result doesn't have a backward component
                ]
                .into_iter()
                .flatten()
                .collect())
            }

            mir::Operator::RangeIndexArray {
                start,
                end_exclusive: end,
            } => {
                let mir::types::Type::Array { inner, length: _ } = &self.ty else {
                    diag_bail!(self, "IndexArray invoked on non-array ({})", self.ty);
                };

                Ok([
                    maybe_fwd_operator(&|_ty| {
                        let member_size = inner.size();
                        let num_elems = end - start;
                        let end_index = end * &member_size;
                        let offset = member_size * num_elems;

                        (
                            lir::Operator::RangeSlice {
                                start: &end_index * offset,
                                end_exclusive: end_index,
                            },
                            lowered_fwd(),
                        )
                    })?,
                    maybe_fwd_operator(&|_ty| {
                        let member_size = inner.backward_size();
                        let num_elems = end - start;
                        let end_index = end * &member_size;
                        let offset = member_size * num_elems;

                        (
                            lir::Operator::Back(BackOperator::RangeSlice {
                                start: &end_index * offset,
                                end_exclusive: end_index,
                            }),
                            lowered_back(),
                        )
                    })?,
                ]
                .into_iter()
                .flatten()
                .collect())
            }
            mir::Operator::RangeIndexBits {
                start,
                end_exclusive,
            } => fwd_only_operator(&|_| {
                (
                    lir::Operator::RangeSlice {
                        start: start.clone(),
                        end_exclusive: end_exclusive.clone(),
                    },
                    lowered_fwd(),
                )
            }),
            mir::Operator::ConstructTuple => Ok([
                maybe_fwd_operator(&|_ty| (lir::Operator::Concat, lowered_fwd()))?,
                maybe_back_operator(&|_ty| {
                    (lir::Operator::Back(BackOperator::Concat), lowered_back())
                })?,
            ]
            .into_iter()
            .flatten()
            .collect()),
            mir::Operator::ConstructEnum { variant } => {
                let mir::types::Type::Enum(options) = &self.ty else {
                    diag_bail!(
                        self,
                        "Attempted enum construction of non-enum ({})",
                        self.ty
                    );
                };

                if back.size() != BigUint::ZERO {
                    diag_bail!(self, "Enum lir type has backward component ({})", self.ty)
                }

                let tag_const = lir::ValueName::Forward(mir::ValueName::Expr(ctx.idtracker.next()));
                let tag_size = enum_util::tag_size(options.len());

                let mut operands = vec![tag_const.clone().near_loc(self)];
                operands.extend(lowered_fwd());

                Ok(vec![
                    lir::Statement::Constant(
                        tag_const.clone(),
                        lir::Type::BitVector(tag_size.to_biguint()),
                        mir::ConstantValue::Int(variant.to_bigint()),
                    )
                    .near_loc(self),
                    lir::Statement::Binding(lir::Binding {
                        name: self.name.lower_fwd(),
                        operator: lir::Operator::Concat,
                        operands,
                        ty: fwd,
                        loc: self.loc,
                    })
                    .at_loc(self),
                ])
            }
            mir::Operator::ConstructCopyView => {
                maybe_fwd_operator(&|_ty| (lir::Operator::Alias, lowered_fwd()))
            }
            mir::Operator::IsEnumVariant { variant } => {
                let enum_type = &types[&self.operands[0]];

                // Special case for enum without members and payload
                if enum_type.size() == BigUint::ZERO {
                    Ok(vec![
                        lir::Statement::Constant(
                            self.name.lower_fwd(),
                            lir::Type::BitVector(BigUint::one()),
                            mir::ConstantValue::Bool(true),
                        )
                        .at_loc(self),
                    ])
                } else {
                    let tag_size = enum_util::tag_size(enum_type.assume_enum().len());
                    let total_size = enum_type.size();

                    let tag_end = &total_size - 1u32.to_biguint();
                    let tag_start = &total_size - tag_size as u64;

                    let expected_tag =
                        lir::ValueName::Forward(mir::ValueName::Expr(ctx.idtracker.next()));
                    let extracted_tag =
                        lir::ValueName::Forward(mir::ValueName::Expr(ctx.idtracker.next()));

                    Ok(vec![
                        lir::Statement::Constant(
                            expected_tag.clone(),
                            lir::Type::BitVector(tag_size.to_biguint()),
                            mir::ConstantValue::Int(variant.to_bigint()),
                        )
                        .near_loc(self),
                        lir::Statement::Binding(lir::Binding {
                            name: extracted_tag.clone(),
                            operator: lir::Operator::RangeSlice {
                                start: tag_start,
                                end_exclusive: tag_end,
                            },
                            operands: lowered_fwd(),
                            ty: lir::Type::BitVector(tag_size.to_biguint()),
                            loc: self.loc,
                        })
                        .near_loc(self),
                        lir::Statement::Binding(spade_lir::Binding {
                            name: self.name.lower_fwd(),
                            operator: lir::Operator::Eq,
                            operands: vec![
                                extracted_tag.near_loc(self),
                                expected_tag.near_loc(self),
                            ],
                            ty: lir::Type::BitVector(BigUint::one()),
                            loc: self.loc,
                        })
                        .at_loc(self),
                    ])
                }
            }
            mir::Operator::EnumMember {
                variant,
                member_index,
            } => {
                let enum_type = &types[&self.operands[0]];

                let variant_list = enum_type.assume_enum();
                let tag_size = enum_util::tag_size(variant_list.len());
                let full_size = enum_type.size();

                let member_start = (tag_size as u64)
                    + variant_list[*variant][0..*member_index]
                        .iter()
                        .map(|t| t.size())
                        .sum::<BigUint>();

                let member_end = &member_start + variant_list[*variant][*member_index].size();

                let upper_idx = &full_size
                    .checked_sub(&member_start)
                    .and_then(|val| val.checked_sub(&1u32.to_biguint()))
                    .ok_or_else(|| diag_anyhow!(self, "Checked sub failed"))?;
                let lower_idx = full_size
                    .checked_sub(&member_end)
                    .ok_or_else(|| diag_anyhow!(self, "Checked sub failed"))?;

                fwd_only_operator(&|_| {
                    (
                        lir::Operator::RangeSlice {
                            start: lower_idx.clone(),
                            end_exclusive: upper_idx.clone(),
                        },
                        lowered_fwd(),
                    )
                })
            }
            mir::Operator::IndexTuple(idx) => {
                let inner_types = match &types[&self.operands[0]].strip_copy_view_layers() {
                    mir::types::Type::Tuple(fields) => fields.clone(),
                    mir::types::Type::Struct(fields) => {
                        fields.iter().map(|(_name, ty)| ty.clone()).collect()
                    }
                    mir::types::Type::Array { inner, length } => {
                        vec![(**inner).clone(); length.to_usize().unwrap()]
                    }
                    _ => diag_bail!(self, "Tuple index on unsupported type ({})", self.ty),
                };
                // TODO: Also handle backward tuple indexinng
                maybe_fwd_operator(&|_| {
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
                        lowered_fwd(),
                    )
                })
            }
            mir::Operator::ReadMutWires => {
                // TODO
                Ok(vec![])
            }
            mir::Operator::Instance {
                name,
                params,
                argument_names,
                loc: _,
                verilog_attr_groups,
            } => {
                let (mut inputs, mut outputs): (Vec<_>, Vec<_>) = argument_names
                    .iter()
                    .zip(&self.operands)
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
                    "__input".to_string(),
                    back,
                    self.name.map_ref(|n| n.lower_back()).clone(),
                ));
                outputs.push((
                    "__output".to_string(),
                    fwd,
                    self.name.map_ref(|n| n.lower_fwd()).clone(),
                ));

                Ok(vec![
                    lir::Statement::Instance {
                        name: name.clone(),
                        params: params.clone(),
                        inputs: inputs.into_iter().collect(),
                        outputs: outputs.into_iter().collect(),
                        verilog_attr_groups: verilog_attr_groups.clone(),
                    }
                    .at_loc(self),
                ])
            }

            mir::Operator::CreatePort => {
                let (left_ty, right_ty) = match &self.ty {
                    mir::types::Type::Tuple(inner) => {
                        let [left, right] = inner.as_slice() else {
                            diag_bail!(self, "CreatePort did not create a tuple of two elements")
                        };
                        (left, right)
                    }
                    _ => diag_bail!(self, "CreatePort did not create a tuple of two elements"),
                };

                let left_fwd = ValueName::new_fwd(ctx.idtracker);
                let left_back = ValueName::new_back(ctx.idtracker);
                let right_fwd = ValueName::new_fwd(ctx.idtracker);
                let right_back = ValueName::new_back(ctx.idtracker);

                let new_stmts = [
                    // Declare the backward wires
                    lir::Statement::Binding(spade_lir::Binding {
                        name: left_back.clone(),
                        operator: spade_lir::Operator::Nop,
                        operands: vec![],
                        ty: lir::Type::BitVector(left_ty.backward_size()),
                        loc: self.loc.clone(),
                    })
                    .near_loc(self),
                    lir::Statement::Binding(spade_lir::Binding {
                        name: right_back.clone(),
                        operator: spade_lir::Operator::Nop,
                        operands: vec![],
                        ty: lir::Type::BitVector(right_ty.backward_size()),
                        loc: self.loc.clone(),
                    })
                    .near_loc(self),
                    // Connect the backward wires to the forward wires
                    lir::Statement::Binding(spade_lir::Binding {
                        name: left_fwd.clone(),
                        operator: spade_lir::Operator::Alias,
                        operands: vec![right_back.clone().near_loc(self)],
                        ty: lir::Type::BitVector(left_ty.size()),
                        loc: self.loc.clone(),
                    })
                    .near_loc(self),
                    lir::Statement::Binding(spade_lir::Binding {
                        name: right_fwd.clone(),
                        operator: spade_lir::Operator::Alias,
                        operands: vec![left_back.clone().near_loc(self)],
                        ty: lir::Type::BitVector(right_ty.size()),
                        loc: self.loc.clone(),
                    })
                    .near_loc(self),
                    // Create the final result
                    lir::Statement::Binding(lir::Binding {
                        name: self.name.lower_fwd(),
                        operator: spade_lir::Operator::Concat,
                        operands: vec![left_fwd.near_loc(self), right_fwd.near_loc(self)],
                        ty: lir::Type::BitVector(self.ty.size()),
                        loc: self.loc.clone(),
                    })
                    .at_loc(self),
                    lir::Statement::Binding(lir::Binding {
                        name: self.name.lower_back(),
                        operator: spade_lir::Operator::Back(BackOperator::Concat),
                        operands: vec![left_back.near_loc(self), right_back.near_loc(self)],
                        ty: lir::Type::BitVector(self.ty.backward_size()),
                        loc: self.loc.clone(),
                    })
                    .at_loc(self),
                ];

                Ok(new_stmts.into_iter().collect())
            }

            mir::Operator::Alias => Ok([
                maybe_fwd_operator(&|_| {
                    (lir::Operator::Alias, lowered_fwd().into_iter().collect())
                })?,
                maybe_back_operator(&|_| {
                    (lir::Operator::Alias, lowered_back().into_iter().collect())
                })?,
            ]
            .into_iter()
            .flatten()
            .collect()),
            mir::Operator::BlackBoxAlias => Ok([
                maybe_fwd_operator(&|_| {
                    (
                        lir::Operator::BlackBoxAlias,
                        lowered_fwd().into_iter().rev().collect(),
                    )
                })?,
                maybe_back_operator(&|_| {
                    (
                        lir::Operator::Back(BackOperator::BlackBoxAlias),
                        lowered_back().into_iter().rev().collect(),
                    )
                })?,
            ]
            .into_iter()
            .flatten()
            .collect()),
            mir::Operator::Nop => Ok([
                maybe_fwd_operator(&|_| {
                    (
                        lir::Operator::Nop,
                        lowered_fwd().into_iter().rev().collect(),
                    )
                })?,
                maybe_back_operator(&|_| {
                    (
                        lir::Operator::Nop,
                        lowered_back().into_iter().rev().collect(),
                    )
                })?,
            ]
            .into_iter()
            .flatten()
            .collect()),
        }
    }
}
