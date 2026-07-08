use itertools::Itertools;
use nesty::{Code, code};

use crate::{Binding, Entity, LirArg, Register, Statement};

impl std::fmt::Display for Entity {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            code! {
                [0] format!("entity {}(", self.name);
                [1] self.inputs.iter().map(|i| format!("input {i}")).join(",\n");
                [1] self.outputs.iter().map(|i| format!("output {i}")).join(",\n");
                [0] ") {";
                [1] self.statements.iter().map(|s| format!("{s}")).join(";\n");
                [0] "}"
            }
            .to_string()
        )
    }
}

impl std::fmt::Display for LirArg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self {
            name,
            val_name,
            ty,
            no_mangle,
        } = self;

        write!(
            f,
            "{}{name}/{val_name}: {ty}",
            if no_mangle.is_some() {
                "#[no_mangle]"
            } else {
                ""
            }
        )
    }
}

impl std::fmt::Display for Statement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Statement::Binding(Binding {
                name,
                operator,
                operands,
                ty,
                loc: _,
            }) => {
                write!(
                    f,
                    "let {name}: {ty} = {operator}({})",
                    operands.iter().map(|op| format!("{op}")).join(", ")
                )
            }
            Statement::Register(Register {
                name,
                ty,
                clock,
                reset,
                initial,
                value,
                loc: _,
            }) => {
                write!(
                    f,
                    "reg({clock}) {name}: {ty}{}{} = {value}",
                    reset
                        .as_ref()
                        .map(|(trig, val)| format!(" reset({trig}: {val})"))
                        .unwrap_or_default(),
                    initial
                        .as_ref()
                        .map(|_val| format!(" initial(..)"))
                        .unwrap_or_default()
                )
            }
            Statement::Constant(value_name, ty, constant_value) => {
                write!(f, "const {value_name}: {ty} = {constant_value}")
            }
            Statement::Assert(val) => write!(f, "assert {val}"),
            Statement::Instance {
                name,
                params,
                inputs,
                outputs,
                verilog_attr_groups,
            } => {
                write!(
                    f,
                    "{verilog_attr_groups}{name}<{params}>({inputs}, {outputs})",
                    verilog_attr_groups = verilog_attr_groups
                        .iter()
                        .map(|group| group
                            .iter()
                            .map(|(attr, value)| {
                                format!(
                                    "{attr}{}",
                                    value.as_ref().map(|v| format!(" {v}")).unwrap_or_default()
                                )
                            })
                            .join("\n"))
                        .join("\n"),
                    params = params
                        .iter()
                        .map(|(name, value)| format!(".{name}: {value}"))
                        .join(", "),
                    inputs = inputs
                        .iter()
                        .map(|(name, ty, value)| format!(".{name}: {ty} = {value}"))
                        .join(", "),
                    outputs = outputs
                        .iter()
                        .map(|(name, ty, value)| format!(".{name}: {ty} = {value}"))
                        .join(", "),
                )
            }
            Statement::Error => write!(f, "<error>"),
        }
    }
}
