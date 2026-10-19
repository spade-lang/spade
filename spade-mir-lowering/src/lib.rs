pub mod bindings;
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

use crate::{
    bindings::{
        BindingLoweringContext as Bc, lower_alias, lower_black_box_alias, lower_concat, lower_construct_array, lower_construct_copy_view, lower_construct_enum, lower_construct_tuple, lower_create_port, lower_enum_member, lower_index_array, lower_index_tuple, lower_inspect, lower_instance, lower_is_enum_variant, lower_match, lower_nop, lower_range_index_array, lower_sign_extend, lower_truncate, lower_zero_extend
    },
    types::TypeExt,
};

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
                        val_name: val_name.lower_fwd().at_loc(val_name),
                        ty: fwd.clone(),
                        no_mangle: *no_mangle,
                    },
                    LirArg {
                        name: name.clone(),
                        val_name: val_name.lower_back().at_loc(val_name),
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
        statements.push(
            lir::Statement::Binding(lir::Binding {
                name: output.lower_back(),
                operator: spade_lir::Operator::BlackBoxAlias,
                operands: vec![lir::ValueName::OutputBack.at_loc(output)],
                ty: output_back,
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

    fn lower_inner(&self, types: &MirTypeList, ctx: &Context) -> Result<Vec<Loc<lir::Statement>>>;
}

impl StatementExt for Loc<mir::Statement> {
    fn lower(&self, types: &MirTypeList, ctx: &Context) -> Result<Vec<Loc<lir::Statement>>> {
        let mut initial_lowering = self.lower_inner(types, ctx)?;

        // When we lower MIR operations to LIR, we only lower them into operations in the
        // relevant direction for that operator. For example, `a + b` only lowers into a forward
        // binding, not a backwards binding, since there is no backward `+`.
        //
        // However, in the initial phases of LIR passes, we need both forward and backward defintions
        // for all variables since the `Legalize` will need to check the type of bindings to,
        // for example, `BackConcat` in order to drop relevant components.
        //
        // I.e. `a = b.concat(c)` would lower to
        //
        // a = Concat(b, c);
        // back(a) = BackConcat(back(b), back(c));
        //
        // But if `b` or `c` came out of a forward operator, there would be no binding for `back(b)`
        // or `back(c)`.
        //
        // To avoid polluting the lowering step with a bunch of extra useless expressions, we'll insert
        // them here, after checking if there are other bindings. As a bonus, we will also sanity
        // check the sizes of the resulting bindings against the binding sizes in the MIR
        let generated_vars = initial_lowering
            .iter()
            .filter_map(|statement| {
                match &statement.inner {
                    // This is a hack, since instantiations are weird and create some bindings
                    // for their inv wires, it is needed to avoid creating a few duplicate
                    // bindings, bindings which in the case of unit inputs and outputs are
                    // defined elsewhere.
                    //
                    // TODO: Consider if we can do this in a better way
                    spade_lir::Statement::Binding(lir::Binding {
                        operator: spade_lir::Operator::DeclareInstantiationOutput,
                        ..
                    }) => None,
                    spade_lir::Statement::Binding(binding) => Some(binding.name.clone()),
                    spade_lir::Statement::Register(register) => Some(register.name.clone()),
                    spade_lir::Statement::Constant(value_name, _, _) => Some(value_name.clone()),
                    spade_lir::Statement::Assert(_) => None,
                    spade_lir::Statement::Set(_, _) => None,
                    spade_lir::Statement::Instance { .. } => {
                        // Instance outputs are handled elsewhere
                        None
                    }
                    spade_lir::Statement::Error => None,
                }
            })
            .collect::<Vec<_>>();

        let expected_vars = match &self.inner {
            spade_mir::Statement::Binding(binding) => Some((&binding.name, &binding.ty)),
            spade_mir::Statement::Register(register) => Some((&register.name, &register.ty)),
            spade_mir::Statement::Constant(name, ty, _) => Some((name, ty)),
            spade_mir::Statement::Assert(_) => None,
            spade_mir::Statement::Set { .. } => None,
            spade_mir::Statement::Error => None,
        };

        // NOTE(Performance): If this structure were larger, this would be an O(n) in the
        // number of names created, but for all operations, `n` will be very small, so we
        // will use a `Vec` here for predictability
        let new_vars = expected_vars
            .iter()
            .map(|(var, ty)| {
                [
                    (var.lower_fwd(), ty.backward_size()),
                    (var.lower_back(), ty.size()),
                ]
            })
            .flatten()
            .filter_map(|(var, size)| {
                match var {
                    ValueName::Forward(value_name) => {
                        let friend = ValueName::Backward(value_name.clone());
                        if !generated_vars.contains(&&friend) {
                            Some((friend, size))
                        } else {
                            None
                        }
                    }
                    ValueName::Backward(value_name) => {
                        let friend = ValueName::Forward(value_name.clone());
                        if !generated_vars.contains(&&friend) {
                            Some((friend, size))
                        } else {
                            None
                        }
                    }
                    // Output variables are not handled here
                    // TODO: Where are they handled?
                    ValueName::OutputFwd => None,
                    ValueName::OutputBack => None,
                }
            });

        initial_lowering.extend(new_vars.into_iter().map(|(name, size)| {
            lir::Statement::Binding(lir::Binding {
                name,
                operator: spade_lir::Operator::Nop,
                operands: vec![],
                // TODO: Ensure that the variable actually is 0 sized if it isn't
                // an annonymous variable
                ty: spade_lir::Type::BitVector(size),
                loc: None,
            })
            .near_loc(&self.loc())
        }));

        Ok(initial_lowering)
    }

    fn lower_inner(
        &self,
        types: &MirTypeList,
        ctx: &Context,
    ) -> Result<Vec<Loc<spade_lir::Statement>>> {
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
                    // TODO: To support initial, we have to support LIR eval. For continuing with testing,
                    // we'll warn instead of bailing here, but this naturally means that tests requiring
                    // initial will fail
                    let err = diag_anyhow!(self, "Register intial is unsupported in LIR");
                    return Err(err.level(spade_diagnostics::diagnostic::DiagnosticLevel::Warning));
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
                lir::Statement::Set(
                    target.lower_back().at_loc(target),
                    value.lower_fwd().at_loc(value),
                )
                .at_loc(self),
                lir::Statement::Set(
                    target.lower_fwd().at_loc(target),
                    value.lower_back().at_loc(value),
                )
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

        let lowered_fwd = self
            .operands
            .iter()
            .map(|op| op.map_ref(|op| op.lower_fwd()))
            .collect();
        let lowered_back = self
            .operands
            .iter()
            .map(|op| op.map_ref(|op| op.lower_back()))
            .collect::<Vec<_>>();

        let bc = Bc {
            fwd,
            back,
            lowered_fwd,
            lowered_back,
        };

        // TODO: get rid of these aliases
        let trivial_fwd_operator = {
            let bc = bc.clone();
            |new_operator| bindings::trivial_fwd_operator(self, bc, new_operator)
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
            mir::Operator::BitwiseNot => trivial_fwd_operator(lir::Operator::BitwiseNot),

            // TODO: This does not handle our new fancy bidirectional match statements
            mir::Operator::Match => lower_match(self, types, bc),

            mir::Operator::SignExtend => lower_sign_extend(self, types, bc, ctx),
            mir::Operator::ZeroExtend => lower_zero_extend(self, types, bc, ctx),
            mir::Operator::Truncate => lower_truncate(self, bc),

            mir::Operator::Concat => lower_concat(self, bc),

            mir::Operator::ConstructArray => lower_construct_array(self, bc),

            mir::Operator::DeclClockedMemory { .. } => {
                // TODO
                Ok(vec![])
            }
            mir::Operator::IndexMemory => {
                // TODO Placeholder to make it compile
                Ok(vec![
                    lir::Statement::Binding(lir::Binding {
                        name: self.name.lower_fwd(),
                        operator: spade_lir::Operator::Nop,
                        operands: vec![],
                        ty: bc.fwd.clone(),
                        loc: self.loc.clone(),
                    })
                    .at_loc(self),
                ])
            }

            mir::Operator::IndexArray => lower_index_array(self, types, bc),

            mir::Operator::RangeIndexArray { .. } => lower_range_index_array(self, bc),
            mir::Operator::RangeIndexBits { .. } => lower_range_index_array(self, bc),
            mir::Operator::ConstructTuple => lower_construct_tuple(self, bc),
            mir::Operator::ConstructEnum { .. } => lower_construct_enum(self, bc, ctx),
            mir::Operator::ConstructCopyView => lower_construct_copy_view(self, bc),
            mir::Operator::Inspect => lower_inspect(self, bc, ctx),
            mir::Operator::IsEnumVariant { .. } => lower_is_enum_variant(self, bc, types, ctx),
            mir::Operator::EnumMember { .. } => lower_enum_member(self, bc, types),
            mir::Operator::IndexTuple(_) => lower_index_tuple(self, bc, types),
            mir::Operator::Instance { .. } => lower_instance(self, bc, types),

            mir::Operator::CreatePort => lower_create_port(self, ctx),

            mir::Operator::Alias => lower_alias(self, bc),
            mir::Operator::BlackBoxAlias => lower_black_box_alias(self, bc),
            mir::Operator::Nop => lower_nop(self, bc),
        }
    }
}


