//! Legalization walks a LIR entity to prepare it for codegen. This includes
//!
//! - Dropping zero sized inputs and outputs from instances
//! - Dropping zero sized signals
//! - Replacing operations on zero sized values with static results where applicable
//!
//! This should be a failure-free process, so any error is a `Diagnostic::bug`, and after
//! legalization, codegen should generate syntactically correct verilog in all cases
//!
//! For performance reasons, legalization mutates in place where possible

use crate::Statement;
use itertools::Itertools;
use num::{BigInt, BigUint, One};
use spade_common::location_info::{Loc, WithLocation};
use spade_diagnostics::diag_bail;

use crate::{Binding, Entity, LirArg, Result, Type, type_list::LirTypeList};

impl Entity {
    pub fn legalize(&mut self) -> Result<()> {
        let types = LirTypeList::from_entity(self);

        let Entity {
            name: _,
            inputs,
            outputs,
            verilog_attr_groups: _,
            statements,
            // TODO: Do we need to keep `inline` around?
            inline: _,
        } = self;

        inputs.retain(
            |LirArg {
                 name: _,
                 val_name: _,
                 ty,
                 no_mangle: _,
             }| { ty.size() != BigUint::ZERO },
        );

        outputs.retain(
            |LirArg {
                 name: _,
                 val_name: _,
                 ty,
                 no_mangle: _,
             }| { ty.size() != BigUint::ZERO },
        );

        // Drop any statements that produce zero size types
        statements.retain(|statement| {
            match &statement.inner {
                crate::Statement::Binding(binding) => binding.ty.size() != BigUint::ZERO,
                crate::Statement::Register(register) => register.ty.size() != BigUint::ZERO,
                crate::Statement::Constant(_, ty, _) => ty.size() != BigUint::ZERO,
                crate::Statement::Assert(_) => {
                    // Asserts are always bool. We check this during statement modification later
                    true
                }
                crate::Statement::Set { target, value: _ } => {
                    if types.lookup(target).unwrap().size() == BigUint::ZERO {
                        false
                    } else {
                        true
                    }
                }
                // We keep instances even if the were to create only zero sized values. We will drop
                // their zero size values during statement modification
                crate::Statement::Instance { .. } => true,
                crate::Statement::Error => true,
            }
        });

        for statement in statements {
            statement.legalize(&types)?;
        }

        Ok(())
    }
}

trait StatementExt {
    fn legalize(&mut self, types: &LirTypeList) -> Result<()>;
}

impl StatementExt for Loc<Statement> {
    /// Legalize the inner parts of statements. We have already droppped statements which _produce_ zero size
    /// types, but some statements need modifications to account for their inputs being zero sized
    fn legalize(&mut self, types: &LirTypeList) -> Result<()> {
        let loc = &self.loc();
        let replacement = match &mut self.inner {
            Statement::Binding(binding) => binding.replacement_binding(types, &loc)?,
            Statement::Register(register) => {
                // TODO: Legalize clock and reset
                None
            }
            Statement::Constant(_, _, _) => None,
            Statement::Assert(val) => {
                if types.lookup(val)?.size() == BigUint::ZERO {
                    diag_bail!(loc, "Asserting a zero sized value");
                }
                None
            }
            Statement::Set { target, value } => {
                if types.lookup(value)?.size() == types.lookup(target)?.size() {
                    diag_bail!(loc, "Found `set` with mixed target/value size")
                }
                None
            }
            Statement::Error => None,
            Statement::Instance {
                name,
                params,
                inputs,
                outputs,
                verilog_attr_groups,
            } => {
                inputs.retain(|(_, ty, _)| ty.size() != BigUint::ZERO);
                outputs.retain(|(_, ty, _)| ty.size() != BigUint::ZERO);
                None
            }
        };

        if let Some(replacement) = replacement {
            *self = replacement.at_loc(&self)
        }

        Ok(())
    }
}

impl Binding {
    fn replacement_binding(
        &mut self,
        types: &LirTypeList,
        loc: &Loc<()>,
    ) -> Result<Option<Statement>> {
        let produce_constant =
            |value, size| Statement::Constant(self.name.clone(), Type::BitVector(size), value);

        let normal_binop = |value| -> Result<_> {
            if self.operands.len() != 2 {
                diag_bail!(
                    loc,
                    "Expected a binary operator but found {} operands",
                    self.operands.len()
                );
            }
            let operand_size = types.lookup(&self.operands[0])?.size();
            if operand_size != types.lookup(&self.operands[1])?.size() {
                diag_bail!(
                    loc,
                    "Expected both operands for a binary operator to be of equal size"
                );
            }

            if operand_size == BigUint::ZERO {
                Ok(Some(produce_constant(value, BigUint::one())))
            } else {
                Ok(None)
            }
        };

        let binop_should_have_dropped = || -> Result<Option<Statement>> {
            if self.operands.len() != 2 {
                diag_bail!(
                    loc,
                    "Expected a binary operator but found {} operands",
                    self.operands.len()
                );
            }
            if types.lookup(&self.operands[0])?.size() == BigUint::ZERO {
                diag_bail!(
                    loc,
                    "Found a zero sized operand for {} which as not been dropped",
                    self.operator
                )
            } else {
                Ok(None)
            }
        };

        match &self.operator {
            // Add/Sub-like grow one bit, therefore the output of 0u0 + 0u0 is 0u1
            crate::Operator::Add
            | crate::Operator::UnsignedAdd
            | crate::Operator::Sub
            | crate::Operator::UnsignedSub => {
                normal_binop(spade_mir::ConstantValue::Int(BigInt::ZERO))
            }

            crate::Operator::Mul => todo!(),
            crate::Operator::UnsignedMul => todo!(),

            // Equality is always true for 0 bit values
            crate::Operator::Eq
            | crate::Operator::Ge
            | crate::Operator::UnsignedGe
            | crate::Operator::Le
            | crate::Operator::UnsignedLe => {
                normal_binop(spade_mir::ConstantValue::Int(BigInt::one()))
            }

            // Non-equality is always false for 0 bit values
            crate::Operator::NotEq
            | crate::Operator::Gt
            | crate::Operator::UnsignedGt
            | crate::Operator::Lt
            | crate::Operator::UnsignedLt => {
                normal_binop(spade_mir::ConstantValue::Int(BigInt::ZERO))
            }

            // Operators which do not grow should already have been dropped
            crate::Operator::Div
            | crate::Operator::UnsignedDiv
            | crate::Operator::Mod
            | crate::Operator::UnsignedMod
            | crate::Operator::LeftShift
            | crate::Operator::RightShift
            | crate::Operator::ArithmeticRightShift
            | crate::Operator::LogicalAnd
            | crate::Operator::LogicalOr
            | crate::Operator::LogicalXor
            | crate::Operator::BitwiseAnd
            | crate::Operator::BitwiseOr
            | crate::Operator::BitwiseXor
            | crate::Operator::ReduceAnd
            | crate::Operator::ReduceOr
            | crate::Operator::ReduceXor
            | crate::Operator::DivPow2 => binop_should_have_dropped(),

            crate::Operator::LogicalNot
            | crate::Operator::USub
            | crate::Operator::Not
            | crate::Operator::BitwiseNot => {
                // TODO: Sanity checks
                Ok(None)
            }

            crate::Operator::ReadWriteItemsInOut(big_uint) => todo!(),

            crate::Operator::Concat => {
                let new_operands = self
                    .operands
                    .iter()
                    .map(|op| Ok((op, types.lookup(op)?)))
                    .collect::<Result<Vec<_>>>()?
                    .into_iter()
                    .filter_map(|(op, ty)| {
                        if ty.size() != BigUint::ZERO {
                            Some(op)
                        } else {
                            None
                        }
                    })
                    .collect::<Vec<_>>();

                if new_operands.len() != self.operands.len() {
                    Ok(Some(Statement::Binding(Binding {
                        name: self.name.clone(),
                        operator: self.operator.clone(),
                        operands: new_operands.into_iter().cloned().collect(),
                        ty: self.ty.clone(),
                        loc: self.loc.clone(),
                    })))
                } else {
                    Ok(None)
                }
            }
            // TODO
            crate::Operator::BackConcat => todo!(),
            crate::Operator::Slice {
                elem_size,
                reversed,
            } => {
                if types.lookup(&self.operands[0])?.size() == BigUint::ZERO {
                    diag_bail!(
                        loc,
                        "Slicing a zero size operand to produce a non-zero size result"
                    );
                }

                // Indexing with a zero size index happens if the indexee is 1 bit wide. In that case,
                // indexing just becomes an alias
                if types.lookup(&self.operands[1])?.size() == BigUint::ZERO {
                    Ok(Some(Statement::Binding(Binding {
                        name: self.name.clone(),
                        operator: crate::Operator::Alias,
                        operands: self.operands.clone(),
                        ty: self.ty.clone(),
                        loc: Some(loc.clone()),
                    })))
                } else {
                    Ok(None)
                }
            }
            crate::Operator::BackSlice {
                elem_size: _,
                reversed: _,
            }
            | crate::Operator::RangeSlice {
                start: _,
                end_exclusive: _,
            } => {
                if types.lookup(&self.operands[0])?.size() == BigUint::ZERO {
                    diag_bail!(
                        loc,
                        "Slicing a zero size operand to produce a non-zero size result"
                    );
                }

                Ok(None)
            }
            // TODO
            crate::Operator::BackRangeSlice(_, _) => todo!(),
            crate::Operator::Replicate { copies: _ } => {
                if types.lookup(&self.operands[0])?.size() == BigUint::ZERO {
                    diag_bail!(
                        loc,
                        "Replicating a zero size operand to produce a non-zero size result"
                    );
                }

                Ok(None)
            }
            crate::Operator::Select => {
                if types.lookup(&self.operands[0])?.size() != BigUint::one() {
                    diag_bail!(loc, "Found a select operation with a non-1 size condition")
                }
                if types.lookup(&self.operands[1])?.size() == BigUint::ZERO {
                    diag_bail!(
                        loc,
                        "Found a non-dropped select which produces a zero size vale"
                    )
                }
                if types.lookup(&self.operands[2])?.size() == BigUint::ZERO {
                    diag_bail!(
                        loc,
                        "Found a non-dropped select which produces a zero size vale"
                    )
                }

                Ok(None)
            }
            crate::Operator::Match => {
                for chunk in &self.operands.iter().chunks(2) {
                    let chunks = chunk.collect::<Vec<_>>();
                    let [cond, val] = chunks.as_slice() else {
                        diag_bail!(loc, "Found a non-even number of opreands in a match");
                    };
                    if types.lookup(cond)?.size() != BigUint::one() {
                        diag_bail!(loc, "Found a match operation with a non-1 size condition")
                    }
                    if types.lookup(val)?.size() == BigUint::ZERO {
                        diag_bail!(
                            loc,
                            "Found zero sized match result which produced non-zero size value"
                        )
                    }
                }
                Ok(None)
            }
            // TODO
            crate::Operator::DeclClockedMemory { initial } => todo!(),
            crate::Operator::Alias
            | crate::Operator::BlackBoxAlias
            | crate::Operator::BackAlias
            | crate::Operator::BackBlackBoxAlias => {
                let in_ty = types.lookup(&self.operands[0])?;
                if in_ty.size() == BigUint::ZERO {
                    diag_bail!(
                        loc,
                        "Found {} of zero size value. It would produce {}: {} from {}: {}",
                        self.operator,
                        self.name,
                        self.ty,
                        self.operands[0],
                        in_ty
                    )
                }
                Ok(None)
            }
            crate::Operator::Nop => Ok(None),
        }
    }
}
