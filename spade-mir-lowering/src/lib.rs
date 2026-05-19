mod types;

use spade_lir::{self as lir, LirArg};
use spade_mir::{self as mir, MirInput};

use crate::types::TypeExt;

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
            output_back.map(|ty| {
                LirArg {
                    name: "__output".to_string(),
                    val_name: lir::ValueName::OutputBack,
                    ty,
                    no_mangle: None,
                }
            }),
            output_fwd.map(|ty| {
                LirArg {
                    name: "__input".to_string(),
                    val_name: lir::ValueName::OutputFwd,
                    ty,
                    no_mangle: None,
                }
            })
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

        lir::Entity {
            name: name.clone(),
            arguments: arguments,
            verilog_attr_groups: verilog_attr_groups.clone(),
            statements: todo!(),
            inline: *inline,
        }
    }
}

trait StatementExt {
    fn lower(&self) -> lir::Statement;
}

impl StatementExt for mir::Statement {
    fn lower(&self) -> spade_lir::Statement {
        match self {
            spade_mir::Statement::Binding(binding) => todo!(),
            spade_mir::Statement::Register(register) => todo!(),
            spade_mir::Statement::Constant(value_name, _, constant_value) => todo!(),
            spade_mir::Statement::Assert(loc) => todo!(),
            spade_mir::Statement::Set { target, value } => todo!(),
            spade_mir::Statement::WalTrace { name, val, suffix, ty } => todo!(),
            spade_mir::Statement::Error => todo!(),
        }
    }
}
