mod types;

use spade_common::{location_info::Loc, num_ext::InfallibleToBigUint};
use spade_diagnostics::{Diagnostic, diag_anyhow, diag_bail};
use spade_lir::{self as lir, LirArg};
use spade_mir::{self as mir, MirInput};

use crate::types::TypeExt;

pub type Result<T> = std::result::Result<T, Diagnostic>;

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
                    val_name: lir::ValueName::Forward(val_name.clone()),
                    ty: ty.clone(),
                    no_mangle: *no_mangle,
                })
                .into_iter()
                .chain(back.map(|ty| LirArg {
                    name: name.clone(),
                    val_name: lir::ValueName::Forward(val_name.clone()),
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
    fn lower(&self) -> Vec<lir::Statement>;
}

impl BindingExt for mir::Binding {
    fn lower(&self) -> Vec<lir::Statement> {
        let fwd_only_type = || {
            
        };

        let simple_fwd_operator = |new_operator: lir::Operator, operands: &dyn Fn(lir::Type) -> Vec<lir::ValueName>| {
            let (fwd, back) = self.ty.lower();
            assert!(
                back.is_some(),
                "Found {new_operator} of type without forward component"
            );
            assert!(
                back.is_none(),
                "Found {new_operator} of type with backward component"
            );

            vec![lir::Statement::Binding(lir::Binding {
                name: self.name.lower_fwd(),
                operator: new_operator,
                operands: operands(fwd.unwrap()),
                // Safe unwrap, the assert above guards
                ty: fwd.unwrap(),
                loc: self.loc.clone(),
            })]
        };

        let map_fwd_operator = |new_operator: lir::Operator| -> Vec<lir::Statement> {
            simple_fwd_operator(
                new_operator,
                &|_| self.operands.iter().map(|op| op.lower_fwd()).collect(),
            )
        };

        match &self.operator {
            mir::Operator::Add => map_fwd_operator(lir::Operator::Add),
            mir::Operator::UnsignedAdd => map_fwd_operator(lir::Operator::UnsignedAdd),
            mir::Operator::Sub => map_fwd_operator(lir::Operator::Sub),
            mir::Operator::UnsignedSub => map_fwd_operator(lir::Operator::UnsignedSub),
            mir::Operator::Mul => map_fwd_operator(lir::Operator::Mul),
            mir::Operator::UnsignedMul => map_fwd_operator(lir::Operator::UnsignedMul),
            mir::Operator::Div => map_fwd_operator(lir::Operator::Div),
            mir::Operator::UnsignedDiv => map_fwd_operator(lir::Operator::UnsignedDiv),
            mir::Operator::Mod => map_fwd_operator(lir::Operator::Mod),
            mir::Operator::UnsignedMod => map_fwd_operator(lir::Operator::UnsignedMod),
            mir::Operator::Eq => map_fwd_operator(lir::Operator::Eq),
            mir::Operator::NotEq => map_fwd_operator(lir::Operator::NotEq),
            mir::Operator::Gt => map_fwd_operator(lir::Operator::Gt),
            mir::Operator::UnsignedGt => map_fwd_operator(lir::Operator::UnsignedGt),
            mir::Operator::Lt => map_fwd_operator(lir::Operator::Lt),
            mir::Operator::UnsignedLt => map_fwd_operator(lir::Operator::UnsignedLt),
            mir::Operator::Ge => map_fwd_operator(lir::Operator::Ge),
            mir::Operator::UnsignedGe => map_fwd_operator(lir::Operator::UnsignedGe),
            mir::Operator::Le => map_fwd_operator(lir::Operator::Le),
            mir::Operator::UnsignedLe => map_fwd_operator(lir::Operator::UnsignedLe),
            mir::Operator::LeftShift => map_fwd_operator(lir::Operator::LeftShift),
            mir::Operator::RightShift => map_fwd_operator(lir::Operator::RightShift),
            mir::Operator::ArithmeticRightShift => {
                map_fwd_operator(lir::Operator::ArithmeticRightShift)
            }
            mir::Operator::LogicalAnd => map_fwd_operator(lir::Operator::LogicalAnd),
            mir::Operator::LogicalOr => map_fwd_operator(lir::Operator::LogicalOr),
            mir::Operator::LogicalXor => map_fwd_operator(lir::Operator::LogicalXor),
            mir::Operator::LogicalNot => map_fwd_operator(lir::Operator::LogicalNot),
            mir::Operator::BitwiseAnd => map_fwd_operator(lir::Operator::BitwiseAnd),
            mir::Operator::BitwiseOr => map_fwd_operator(lir::Operator::BitwiseOr),
            mir::Operator::BitwiseXor => map_fwd_operator(lir::Operator::BitwiseXor),
            mir::Operator::ReduceAnd => map_fwd_operator(lir::Operator::ReduceAnd),
            mir::Operator::ReduceOr => map_fwd_operator(lir::Operator::ReduceOr),
            mir::Operator::ReduceXor => map_fwd_operator(lir::Operator::ReduceXor),
            mir::Operator::USub => map_fwd_operator(lir::Operator::USub),
            mir::Operator::Not => map_fwd_operator(lir::Operator::Not),
            mir::Operator::ReadWriteItemsInOut(val) => {
                map_fwd_operator(lir::Operator::ReadWriteItemsInOut(val.clone()))
            }
            mir::Operator::DivPow2 => map_fwd_operator(lir::Operator::DivPow2),

            mir::Operator::Select => map_fwd_operator(lir::Operator::Select),
            mir::Operator::Match => map_fwd_operator(lir::Operator::Match),
            mir::Operator::BitwiseNot => map_fwd_operator(lir::Operator::BitwiseNot),

            mir::Operator::ReadPort => todo!(),

            mir::Operator::SignExtend => todo!(),
            mir::Operator::ZeroExtend => todo!(),
            mir::Operator::Truncate => {
                simple_fwd_operator(&|ty| lir::Operator::RangeSlice(0u32.to_biguint(), ty.size()))
            }

            mir::Operator::Concat => map_fwd_operator(lir::Operator::Concat),

            mir::Operator::ConstructArray => {
                let (fwd, back) = self.ty.lower();

                [
                    fwd.map(|ty| {
                        lir::Statement::Binding(lir::Binding {
                            name: self.name.lower_fwd(),
                            ty: ty,
                            operator: lir::Operator::Concat,
                            operands: self
                                .operands
                                .iter()
                                .rev()
                                .map(|op| op.lower_fwd())
                                .collect(),
                            loc: self.loc.clone(),
                        })
                    }),
                    back.map(|ty| {
                        lir::Statement::Binding(lir::Binding {
                            name: self.name.lower_fwd(),
                            ty: ty,
                            operator: lir::Operator::Concat,
                            operands: self
                                .operands
                                .iter()
                                .rev()
                                .map(|op| op.lower_back())
                                .collect(),
                            loc: self.loc.clone(),
                        })
                    }),
                ]
                .into_iter()
                .flatten()
                .collect()
            }

            mir::Operator::DeclClockedMemory { initial } => todo!(),

            mir::Operator::IndexArray => todo!(),
            mir::Operator::IndexMemory => todo!(),
            mir::Operator::RangeIndexArray {
                start,
                end_exclusive,
            } => todo!(),
            mir::Operator::RangeIndexBits {
                start,
                end_exclusive,
            } => todo!(),
            mir::Operator::ConstructTuple => todo!(),
            mir::Operator::ConstructEnum { variant } => todo!(),
            mir::Operator::ConstructCopyView => todo!(),
            mir::Operator::IsEnumVariant { variant } => todo!(),
            mir::Operator::EnumMember {
                variant,
                member_index,
            } => todo!(),
            mir::Operator::IndexTuple(_) => todo!(),
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
