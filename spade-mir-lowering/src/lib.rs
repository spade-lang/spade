mod enum_util;
mod types;

use spade_common::{
    id_tracker::ExprIdTracker,
    location_info::Loc,
    num_ext::{InfallibleToBigInt, InfallibleToBigUint},
};
use spade_diagnostics::{Diagnostic, diag_bail};
use spade_lir::{self as lir, LirArg};
use spade_mir::{self as mir, MirInput, type_list::MirTypeList};

use num::{BigUint, One, ToPrimitive, Zero};

use crate::types::TypeExt;

pub type Result<T> = std::result::Result<T, Diagnostic>;

struct Context<'a> {
    idtracker: &'a ExprIdTracker,
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

pub(crate) trait EntityExt {
    fn lower(&self) -> lir::Entity;
}

impl EntityExt for mir::Entity {
    fn lower(&self) -> lir::Entity {
        let mir::Entity {
            name,
            inputs,
            output,
            output_type,
            verilog_attr_groups,
            statements,
            inline,
        } = self;

        // These are in inverted order because we change the output to be an input
        let (output_back, output_fwd) = output_type.lower();

        let output_args = [
            output_back.map(|ty| LirArg {
                name: "__output".to_string(),
                val_name: lir::ValueName::OutputBack,
                ty,
                no_mangle: None,
            }),
            output_fwd.map(|ty| LirArg {
                name: "__input".to_string(),
                val_name: lir::ValueName::OutputFwd,
                ty,
                no_mangle: None,
            }),
        ];

        let arguments: Vec<_> = inputs
            .iter()
            .map(|input| {
                let MirInput {
                    name,
                    val_name,
                    ty,
                    no_mangle,
                } = input;

                let (fwd, back) = ty.lower();

                fwd.map(|ty| LirArg {
                    name: name.clone(),
                    val_name: lir::ValueName::Forward(val_name.clone().inner),
                    ty: ty.clone(),
                    no_mangle: *no_mangle,
                })
                .into_iter()
                .chain(back.map(|ty| LirArg {
                    name: name.clone(),
                    val_name: lir::ValueName::Forward(val_name.clone().inner),
                    ty: ty.clone(),
                    no_mangle: *no_mangle,
                }))
            })
            .flatten()
            .chain(output_args.into_iter().flatten())
            .collect::<Vec<_>>();

        let statements = statements.iter().flat_map(|stmt| stmt.lower()).collect();

        lir::Entity {
            name: name.clone(),
            arguments: arguments,
            verilog_attr_groups: verilog_attr_groups.clone(),
            statements,
            inline: *inline,
        }
    }
}

trait StatementExt {
    fn lower(&self) -> Vec<lir::Statement>;
}

impl StatementExt for mir::Statement {
    fn lower(&self) -> Vec<lir::Statement> {
        match self {
            spade_mir::Statement::Binding(binding) => todo!(),
            spade_mir::Statement::Register(register) => todo!(),
            spade_mir::Statement::Constant(value_name, ty, val) => {
                vec![lir::Statement::Constant(
                    value_name.lower_fwd(),
                    ty.lower().0.expect("Constant did not have a forward type"),
                    val.clone(),
                )]
            }
            spade_mir::Statement::Assert(value_name) => {
                vec![lir::Statement::Assert(
                    value_name.map_ref(|v| v.lower_fwd()),
                )]
            }
            spade_mir::Statement::Set { target, value } => {
                vec![lir::Statement::Set {
                    target: target.map_ref(|v| v.lower_back()),
                    value: value.map_ref(|v| v.lower_fwd()),
                }]
            }
            spade_mir::Statement::Error => {
                vec![spade_lir::Statement::Error]
            }
        }
    }
}

trait BindingExt {
    fn lower(&self, types: &MirTypeList, ctx: &Context) -> Result<Vec<lir::Statement>>;
}

impl BindingExt for Loc<&mir::Binding> {
    fn lower(&self, types: &MirTypeList, ctx: &Context) -> Result<Vec<lir::Statement>> {
        let (fwd, back) = self.ty.lower();

        let fwd_only_operator =
            |inner: &dyn Fn(&lir::Type) -> (lir::Operator, Vec<lir::ValueName>)| {
                let Some(fwd) = &fwd else {
                    diag_bail!(
                        self,
                        "{} was applied to a type without forward component ({})",
                        self.operator,
                        self.ty
                    );
                };
                if back.is_some() {
                    diag_bail!(
                        self,
                        "{} was applied to a type with a backward component ({})",
                        self.operator,
                        self.ty
                    );
                }

                let (operator, operands) = inner(fwd);

                Ok(vec![lir::Statement::Binding(lir::Binding {
                    name: self.name.lower_fwd(),
                    operator: operator,
                    operands: operands,
                    ty: fwd.clone(),
                    loc: self.loc.clone(),
                })])
            };

        let lowered_fwd = || self.operands.iter().map(|op| op.lower_fwd()).collect();
        let lowered_back = || {
            self.operands
                .iter()
                .map(|op| op.lower_back())
                .collect::<Vec<_>>()
        };

        let trivial_fwd_operator = |new_operator: lir::Operator| -> Result<Vec<lir::Statement>> {
            fwd_only_operator(&|_| (new_operator.clone(), lowered_fwd()))
        };

        let maybe_fwd_operator =
            |inner: &dyn Fn(&lir::Type) -> (lir::Operator, Vec<lir::ValueName>)| {
                if let Some(fwd) = &fwd {
                    let (operator, operands) = inner(fwd);

                    Ok(vec![lir::Statement::Binding(lir::Binding {
                        name: self.name.lower_fwd(),
                        operator: operator,
                        operands: operands,
                        ty: fwd.clone(),
                        loc: self.loc.clone(),
                    })])
                } else {
                    Ok(vec![])
                }
            };

        let maybe_back_operator =
            |inner: &dyn Fn(&lir::Type) -> (lir::Operator, Vec<lir::ValueName>)| {
                if let Some(back) = &back {
                    let (operator, operands) = inner(back);

                    Ok(vec![lir::Statement::Binding(lir::Binding {
                        name: self.name.lower_back(),
                        operator: operator,
                        operands: operands,
                        // Safe unwrap, the assert above guards
                        ty: back.clone(),
                        loc: self.loc.clone(),
                    })])
                } else {
                    Ok(vec![])
                }
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

            mir::Operator::ReadPort => todo!(),

            mir::Operator::SignExtend => todo!(),
            mir::Operator::ZeroExtend => todo!(),
            mir::Operator::Truncate => fwd_only_operator(&|ty| {
                (
                    lir::Operator::RangeSlice {
                        start: 0u32.to_biguint(),
                        end_exclusive: ty.size(),
                    },
                    lowered_fwd(),
                )
            }),

            mir::Operator::Concat => trivial_fwd_operator(lir::Operator::Concat),

            mir::Operator::ConstructArray => Ok([
                maybe_fwd_operator(&|_| {
                    (
                        lir::Operator::Concat,
                        lowered_fwd().into_iter().rev().collect(),
                    )
                })?,
                maybe_back_operator(&|_| {
                    (
                        lir::Operator::BackConcat,
                        lowered_back().into_iter().rev().collect(),
                    )
                })?,
            ]
            .into_iter()
            .flatten()
            .collect()),

            mir::Operator::DeclClockedMemory { initial } => todo!(),
            mir::Operator::IndexMemory => todo!(),

            mir::Operator::IndexArray => {
                let mir::types::Type::Array { inner, length: _ } = &self.ty else {
                    diag_bail!(self, "IndexArray invoked on non-array ({})", self.ty);
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
                    maybe_back_operator(&|_self_ty| {
                        (
                            lir::Operator::BackSlice {
                                elem_size: inner.backward_size(),
                                reversed: true,
                            },
                            lowered_back(),
                        )
                    })?,
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
                        let end_index = (end * &member_size) - BigUint::one();
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
                        let end_index = (end * &member_size) - BigUint::one();
                        let offset = member_size * num_elems;

                        (
                            lir::Operator::BackRangeSlice(&end_index * offset, end_index),
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
                maybe_back_operator(&|_ty| (lir::Operator::BackConcat, lowered_back()))?,
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
                let (Some(fwd), None) = (fwd, back) else {
                    diag_bail!(self, "Enum lir type was suspicious ({})", self.ty)
                };

                let tag_const = lir::ValueName::Forward(mir::ValueName::Expr(ctx.idtracker.next()));
                let tag_size = enum_util::tag_size(options.len());

                let mut operands = vec![tag_const.clone()];
                operands.extend(lowered_fwd());

                Ok(vec![
                    lir::Statement::Constant(
                        tag_const.clone(),
                        lir::Type::BitVector(tag_size.to_biguint()),
                        mir::ConstantValue::Int(variant.to_bigint()),
                    ),
                    lir::Statement::Binding(lir::Binding {
                        name: self.name.lower_fwd(),
                        operator: lir::Operator::Concat,
                        operands,
                        ty: fwd,
                        loc: self.loc,
                    }),
                ])
            }
            mir::Operator::ConstructCopyView => {
                maybe_fwd_operator(&|_ty| (lir::Operator::Alias, lowered_fwd()))
            }
            mir::Operator::IsEnumVariant { variant } => {
                let enum_type = &types[&self.operands[0]];

                // Special case for enum without members and payload
                if enum_type.size() == BigUint::ZERO {
                    Ok(vec![lir::Statement::Constant(
                        self.name.lower_fwd(),
                        lir::Type::BitVector(BigUint::one()),
                        mir::ConstantValue::Bool(true),
                    )])
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
                        ),
                        lir::Statement::Binding(lir::Binding {
                            name: extracted_tag.clone(),
                            operator: lir::Operator::RangeSlice {
                                start: tag_start,
                                end_exclusive: tag_end,
                            },
                            operands: lowered_fwd(),
                            ty: lir::Type::BitVector(tag_size.to_biguint()),
                            loc: self.loc,
                        }),
                        lir::Statement::Binding(spade_lir::Binding {
                            name: self.name.lower_fwd(),
                            operator: lir::Operator::Eq,
                            operands: vec![extracted_tag, expected_tag],
                            ty: lir::Type::BitVector(BigUint::one()),
                            loc: self.loc,
                        }),
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

                let upper_idx = &full_size - &member_start - 1u32.to_biguint();
                let lower_idx = full_size - &member_end;

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

                    let sizes = inner_types
                        .iter()
                        .map(|t| t.backward_size())
                        .collect::<Vec<_>>();

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
                            end_exclusive: &total_width - start_bit - 1u32.to_biguint(),
                        },
                        lowered_fwd(),
                    )
                })
            }
            mir::Operator::ReadMutWires => todo!(),
            mir::Operator::Instance {
                name,
                params,
                argument_names,
                loc,
                verilog_attr_groups,
            } => todo!(),

            mir::Operator::FlipPort => todo!(),

            mir::Operator::Alias => todo!(),
            mir::Operator::BlackBoxAlias => todo!(),
            mir::Operator::Nop => todo!(),
        }
    }
}
