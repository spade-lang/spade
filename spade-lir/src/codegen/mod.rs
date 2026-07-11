use itertools::Itertools;
use nesty::{Code, code};
use spade_codespan_reporting::term::termcolor;

use num::{BigInt, BigUint, CheckedSub, One, Signed, Zero};
use spade_common::location_info::{Loc, WithLocation};
use spade_common::name::NameID;
use spade_common::num_ext::InfallibleToBigUint;
use spade_diagnostics::emitter::CodespanEmitter;
use spade_diagnostics::{CodeBundle, CompilationError, DiagHandler, diag_anyhow, diag_bail};
use spade_mir::unit_name::{InstanceMap, InstanceNameTracker};

use crate::codegen::assertion::AssertedExpression;
use crate::name_map::VerilogNameMap;
use crate::type_list::LirTypeList;
use crate::verilog::{self, assign, localparam_size_spec, logic, size_spec};
use crate::{Binding, ConstantValue, Entity, LirArg, Operator, Statement, Type, ValueName};

mod assertion;
pub mod util;

use crate::Result;

struct Context<'a> {
    source_code: &'a Option<CodeBundle>,
    instance_names: &'a mut InstanceNameTracker,
    instance_map: &'a mut InstanceMap,
    // The NameID of the unit being generated
    unit_nameid: &'a NameID,
}

/// Produces a source location verilog attribute if the loc and code bundle are defined
fn source_attribute(loc: &Option<Loc<()>>, code: &Option<CodeBundle>) -> Option<String> {
    match (loc, code) {
        (Some(l), Some(c)) => Some(format!(r#"(* src = "{}" *)"#, c.source_loc(l))),
        _ => None,
    }
}

fn add_to_name_map(name_map: &mut VerilogNameMap, name: &ValueName, ty: &Type) {
    name_map.insert(&name.var_name(), name.clone())
}

fn statement_declaration(
    statement: &Loc<Statement>,
    code: &Option<CodeBundle>,
    name_map: &mut VerilogNameMap, // TODO
) -> Result<Code> {
    let result = match &statement.inner {
        Statement::Binding(binding) => {
            // add_to_name_map(name_map, &binding.name, &binding.ty); // TODO
            let name = binding.name.var_name();

            if !binding.name.is_output() {
                let forward_declaration = {
                    // let inner = vec![match &binding.ty {
                    //     // TODO: Deal with memories in the LIR. Separate statement?
                    //     crate::types::Type::Memory { inner, length } => {
                    //         let inner_w = inner.size();
                    //         if inner_w > 1u32.to_biguint() {
                    //             format!("logic[{inner_w}-1:0] {name}[{length}-1:0];")
                    //         } else {
                    //             format!("logic {name}[{length}-1:0];")
                    //         }
                    //     }
                    //     _ => logic(&name, &binding.ty.size()),
                    // }];

                    let inner = logic(&name, &binding.ty.size().near_loc(statement))?;
                    code![
                        [0] source_attribute(&binding.loc, code);
                        [0] inner
                    ]
                };

                // TODO: Deal with memories
                // Aliases of memories have to be treated differently because we can't
                // assign them
                // let assignment = match &binding.operator {
                //     Operator::Alias => match binding.ty {
                //         crate::types::Type::Memory { .. } => {
                //             vec![format!("`define {} {}", name, ops[0])]
                //         }
                //         _ => vec![],
                //     },
                //     _ => vec![],
                // };

                code! {
                    [0] &forward_declaration;
                }
            } else {
                // IO is declared in the input 
                code! {}
            }
        }
        Statement::Register(reg) => {
            // TODO: Legalization should check if reg or constants declare ValueName::Input/Output
            add_to_name_map(name_map, &reg.name, &reg.ty);
            let name = reg.name.var_name();
            let declaration = verilog::reg(&name, &reg.ty.size().near_loc(&statement))?;
            code! {
                [0] source_attribute(&reg.loc, code);
                [0] &declaration;
            }
        }
        Statement::Constant(name, ty, value) => {
            add_to_name_map(name_map, name, ty);

            let name = name.var_name();

            let expression = match value {
                ConstantValue::Int(val) => {
                    let size = ty.size();

                    let val_abs = val.abs();
                    let sign = if val < &BigInt::zero() { "-" } else { "" };

                    // Verilog literals are 32 bits by default
                    let size_spec = if size >= 32u32.to_biguint() {
                        format!("{size}'d")
                    } else {
                        String::new()
                    };
                    format!("{sign}{size_spec}{val_abs}")
                }
                ConstantValue::Bool(val) => format!("{}", if *val { 1 } else { 0 }),
                ConstantValue::String(val) => format!("{:?}", val),
                ConstantValue::Undef(w) => format!("{w}'bx"),
                ConstantValue::HighImp => "'bz".to_string(),
            };

            if ty.size() == BigUint::ZERO {
                diag_bail!(statement, "Found a zero sized constant");
            }

            let size = localparam_size_spec(&ty.size());

            let assignment = format!("localparam{size} {name} = {expression};");

            code! {
                [0] &assignment
            }
        }
        Statement::Assert(_) => {
            code! {}
        }
        Statement::Instance {
            name: _,
            params: _,
            inputs: _,
            outputs,
            // TODO: We now drop the attribute on the output variable, which is non-ideal
            verilog_attr_groups: _,
        } => {
            code! {
                [0] outputs.iter().map(|(_name, ty, val)| {
                    // TODO: What if we have `inout` here, can we even return inout currently?
                    logic(&val.var_name(), &ty.size().near_loc(val)).map_err(|e| e.note(format!("When generating the logic for output {val}")))
                }).collect::<Result<Vec<_>>>()?
            }
        }
        Statement::Error => {
            println!("WARNING: Running codegen on a Statement::Error");
            code! {
                [0] "// Codegen ran for an Error statement"
            }
        }
    };
    Ok(result)
}

fn forward_expression_code(
    binding: Loc<&Binding>,
    types: &LirTypeList,
    ops: &[Loc<ValueName>],
) -> Result<String> {
    let self_type = &binding.ty;
    let op_names = ops.iter().map(|op| op.var_name()).collect::<Vec<_>>();

    let name = binding.name.var_name();

    macro_rules! binop {
        ($verilog:expr) => {{
            assert!(
                binding.operands.len() == 2,
                "expected 2 operands to binary operator"
            );
            #[allow(unused_mut)]
            let mut result = format!("{} {} {}", op_names[0], $verilog, op_names[1]);

            result
        }};
    }

    macro_rules! signed_binop {
        ($verilog:expr $(; zst => $on_zero:expr)?) => {{
            assert!(
                binding.operands.len() == 2,
                "expected 2 operands to binary operator"
            );
            #[allow(unused_mut)]
            let mut result = format!(
                "$signed({}) {} $signed({})",
                op_names[0], $verilog, op_names[1]
            );

            $(
                if types[&ops[0]].size() == BigUint::ZERO {
                    result = $on_zero.to_string();
                }
            )?
            result
        }};
    }

    macro_rules! unop {
        ($verilog:expr) => {{
            assert!(
                binding.operands.len() == 1,
                "expected 1 operands to binary operator"
            );
            format!("{}{}", $verilog, op_names[0])
        }};
    }

    let result = match &binding.operator {
        Operator::Add => signed_binop!("+"),
        Operator::UnsignedAdd => binop!("+"),
        Operator::Sub => signed_binop!("-"),
        Operator::UnsignedSub => binop!("-"),
        Operator::Mul => signed_binop!("*"),
        Operator::UnsignedMul => binop!("*"),
        Operator::Div => signed_binop!("/"),
        Operator::UnsignedDiv => binop!("/"),
        Operator::Mod => signed_binop!("%"),
        Operator::UnsignedMod => binop!("%"),
        Operator::Eq => binop!("=="),
        Operator::NotEq => binop!("!="),
        Operator::Gt => signed_binop!(">"),
        Operator::UnsignedGt => binop!(">"),
        Operator::Lt => signed_binop!("<"),
        Operator::UnsignedLt => binop!("<"),
        Operator::Ge => signed_binop!(">="),
        Operator::UnsignedGe => binop!(">="),
        Operator::Le => signed_binop!("<="),
        Operator::UnsignedLe => binop!("<="),
        Operator::LeftShift => binop!("<<"),
        Operator::RightShift => binop!(">>"),
        Operator::ArithmeticRightShift => signed_binop!(">>>"),
        Operator::LogicalAnd => binop!("&&"),
        Operator::LogicalOr => binop!("||"),
        Operator::LogicalXor => binop!("^"),
        Operator::LogicalNot => {
            assert!(
                op_names.len() == 1,
                "Expected exactly 1 operand to not operator"
            );
            format!("!{}", op_names[0])
        }
        Operator::BitwiseNot => {
            assert!(
                op_names.len() == 1,
                "Expected exactly 1 operand to bitwise not operator"
            );
            format!("~{}", op_names[0])
        }
        Operator::BitwiseAnd => binop!("&"),
        Operator::BitwiseOr => binop!("|"),
        Operator::BitwiseXor => binop!("^"),
        Operator::USub => unop!("-"),
        Operator::Not => unop!("!"),
        Operator::ReduceAnd => unop!("&"),
        Operator::ReduceOr => unop!("|"),
        Operator::ReduceXor => unop!("^"),
        Operator::DivPow2 => {
            // Split into 3 cases: if the division amount is 2^0, nothing should
            // be done. Must be handled as a special case of the rest of the computation
            //
            // If the dividend is negative, we want to round the result towards 0, rather
            // than towards -inf. To do so, we add a 1 in the most significant bit
            // which is shifted away

            let dividend = &op_names[0];
            let divisor = &op_names[1];
            code! {
                [0] "always_comb begin";
                [1]     format!("if ({divisor} == 0) begin");
                [2]         format!("{name} = {dividend};");
                [1]     "end";
                [1]     format!("else begin");
                [2]         format!("{name} = $signed($signed({dividend}) + $signed(1 << ({divisor} - 1))) >>> $signed({divisor});");
                [1]     "end";
                [0] "end";
            }.to_string()
        }
        Operator::Concat => {
            format!("{{{}}}", ops.iter().map(|op| op.var_name()).join(", "))
        }
        Operator::Slice {
            elem_size,
            reversed,
        } => {
            let array_len = types.lookup(&binding.operands[0])?;
            if !*reversed {
                if elem_size == &BigUint::one() {
                    format!("{}[{}]", op_names[0], op_names[1])
                } else {
                    format!(
                        "{}[{} + {elem_size} - 1 : {}]",
                        op_names[0], op_names[1], op_names[1]
                    )
                }
            } else {
                if elem_size == &BigUint::one() {
                    format!(
                        "{}[{array_len} - {}]",
                        op_names[0], op_names[1]
                    )
                } else {
                    format!(
                        "{}[{array_len} - {} + {elem_size} - 1 : {array_len} - {}]",
                        op_names[0], op_names[1], op_names[1]
                    )
                }
            }
        }
        Operator::RangeSlice {
            start,
            end_exclusive,
        } => {
            let array_len = types.lookup(&binding.operands[0])?;

            if array_len.size() == BigUint::one() {
                op_names[0].clone()
            } else {
                // Strange indexing explained here https://stackoverflow.com/questions/18067571/indexing-vectors-and-arrays-with#18068296
                format!(
                    "{}[{}-:{}]",
                    op_names[0],
                    end_exclusive.checked_sub(&BigUint::one()).ok_or_else(|| {
                        diag_anyhow!(
                            binding,
                            "Range slice requested sub of {end_exclusive} - 1 which underflowed"
                        )
                    })?,
                    start
                )
            }
        }
        Operator::Replicate { copies } => format!("{{{}{{{}}}}}", copies, binding.operands[0]),

        Operator::Match => {
            assert!(
                op_names.len() % 2 == 0,
                "Match statements must have an even number of operands"
            );

            let num_branches = op_names.len() / 2;

            let mut conditions = vec![];
            let mut cases = vec![];
            for i in 0..num_branches {
                let cond = &op_names[i * 2];
                let result = &op_names[i * 2 + 1];

                conditions.push(cond.clone());

                let zeros = (0..i).map(|_| '0').collect::<String>();
                let unknowns = (0..(num_branches - i - 1)).map(|_| '?').collect::<String>();
                cases.push(format!(
                    "{}'b{}1{}: {} = {};",
                    num_branches, zeros, unknowns, name, result
                ))
            }

            let fallback = format!("{}'dx", self_type.size());

            code! (
                [0] "always_comb begin";
                [1]     format!("priority casez ({{{}}})", conditions.join(", "));
                [2]         cases;
                [2]         format!("{num_branches}'b?: {name} = {fallback};");
                [1]     "endcase";
                [0] "end";
            )
            .to_string()
        }
        Operator::Select => {
            assert!(
                binding.operands.len() == 3,
                "expected 3 operands to Select operator"
            );
            format!("{} ? {} : {}", op_names[0], op_names[1], op_names[2])
        }
        Operator::DeclClockedMemory { initial } => {
            // TODO: Handle DeclClockedMemory
            todo!()
            /*
            let (addr_w, inner_w, write_ports) = match &types[&ops[1]] {
                Type::Array { inner, length } => match &**inner {
                    Type::Tuple(fields) => match &fields[..] {
                        [_, Type::UInt(addr_w), inner] => Some((addr_w, inner.size(), length)),
                        _ => None,
                    },
                    _ => None,
                },
                _ => None,
            }
            .expect("the write ports have an incorrect type");

            let full_port_width = 1u32.to_biguint() + addr_w + &inner_w;

            let initial_block = if let Some(vals) = initial {
                let assignments = vals
                    .iter()
                    .enumerate()
                    .map(|(i, v)| {
                        let val = eval_statements(v).as_string();

                        format!("{}[{i}] = 'b{val};", name)
                    })
                    .collect::<Vec<_>>();
                code! {
                    [0] "initial begin";
                    [1]     assignments;
                    [0] "end";
                }
            } else {
                code! {}
            };

            let update_blocks = (0..write_ports.to_usize().expect("Too many write ports"))
                .map(|port| {
                    let we_index =
                        &full_port_width * (port + 1u32.to_biguint()) - 1u32.to_biguint();

                    let addr_start = &full_port_width * port + &inner_w;
                    let addr = if *addr_w == 1u32.to_biguint() {
                        format!("{}[{}]", op_names[1], addr_start)
                    } else {
                        format!(
                            "{}[{}:{}]",
                            op_names[1],
                            &addr_start + addr_w - 1u32.to_biguint(),
                            addr_start
                        )
                    };

                    let write_value_start = port * &full_port_width;
                    let (write_index, write_value) = if inner_w == 1u32.to_biguint() {
                        (
                            format!("{}[{addr}]", name),
                            format!("{}[{}]", op_names[1], &write_value_start),
                        )
                    } else {
                        (
                            format!("{}[{addr}]", name),
                            format!(
                                "{}[{end}:{write_value_start}]",
                                op_names[1],
                                end = &write_value_start + &inner_w - 1u32.to_biguint()
                            ),
                        )
                    };
                    let we_signal = format!("{}[{we_index}]", op_names[1]);

                    code! {
                        [0] format!("if ({we_signal}) begin");
                        [1]     format!("{write_index} <= {write_value};");
                        [0] "end"
                    }
                    .to_string()
                })
                .join("\n");

            code! {
                [0] initial_block;
                [0] format!("always @(posedge {clk}) begin", clk = op_names[0]);
                [1]     update_blocks;
                [0] "end";
            }
            .to_string()
            */
        }
        Operator::ReadWriteItemsInOut(_) => {
            // NOTE Dummy. Set in statement_code
            String::new()
        }
        Operator::Alias | Operator::BlackBoxAlias => {
            op_names[0].clone()
        }
        Operator::Nop => String::new(),

        Operator::Back(op) => {
            diag_bail!(
                binding,
                "Back operator ({op:?}) should already have been lowered during codegen."
            )
        }
    };

    Ok(result)
}

fn statement_code(
    statement: &Loc<Statement>,
    types: &LirTypeList,
    ctx: &mut Context,
) -> Result<Code> {
    let result = match &statement.inner {
        Statement::Binding(binding) => {
            let name = binding.name.var_name();

            let ops = &binding
                .operands
                .iter()
                .map(|n| n.var_name())
                .collect::<Vec<_>>();

            let forward_expression = if binding.ty.size() != BigUint::zero() {
                Some(forward_expression_code(
                    binding.at_loc(statement),
                    types,
                    &binding.operands,
                )?)
            } else {
                None
            };

            // Unless this is a special operator, we just use assign value = expression
            let assignment = match &binding.operator {
                Operator::Match => forward_expression.unwrap(),
                Operator::DivPow2 => forward_expression.unwrap(),
                Operator::Nop => String::new(),
                Operator::DeclClockedMemory { .. } => forward_expression.unwrap(),
                Operator::ReadWriteItemsInOut(num_items) => {
                    /*
                    // NOTE(repr): this code relies on the bit representation of `Option` to use the
                    // MSB as the discriminant, with 0 indicating a `None` value and 1 indicating a
                    // `Some(_)` value.
                    let item_size = binding.ty.size() / num_items;
                    let payload_size = binding.ty.size() / num_items - BigUint::one();
                    let mut snippets = vec![];

                    if num_items == &1u32.to_biguint() && payload_size == 1u32.to_biguint() {
                        snippets.push(code! {
                            [0] format!("assign {} = {}[1] ? {}[0] : {}'bZ;",
                                    ops[0],
                                    back_name,
                                    back_name,
                                    payload_size
                                );
                            [0] format!("assign {} = {}[1] ? {{ 1'b0, 1'bX }} : {{ 1'b1, {} }};",
                                    name,
                                    back_name,
                                    ops[0]
                                )
                        }
                        .to_string());
                    } else {
                        for i in 0..num_items.to_usize().unwrap() {
                            let item_offset = i * item_size.clone();
                            let payload_offset = i * payload_size.clone();
                            let discriminant_offset =
                                item_offset.clone() + item_size.clone() - BigUint::one();

                            snippets.push(code! {
                                [0] format!("assign {}[{}+:{}] = {}[{}] ? {}[{}+:{}] : {}'bZ;",
                                        ops[0], payload_offset, payload_size,
                                        back_name, discriminant_offset,
                                        back_name, item_offset, payload_size,
                                        payload_size);
                                [0] format!("assign {}[{}+:{}] = {}[{}] ? {{ 1'b0, {}'bX }} : {{ 1'b1, {}[{}+:{}] }};",
                                        name, item_offset, item_size,
                                        back_name, discriminant_offset,
                                        payload_size,
                                        ops[0], payload_offset, payload_size)
                            }
                            .to_string());
                        }
                    }
                    snippets.join("\n")
                    */
                    // TODO: Handle ReadWriteItemsInOut. Can we perhaps lower this during MIR lowering?
                    // todo!()
                    "".to_string()
                }
                // TODO: Handle memories
                // Operator::Alias | Operator::BlackBoxAlias => match binding.ty {
                //     crate::types::Type::Memory { .. } => {
                //         // Aliasing of memories happens at definition
                //         "".to_string()
                //     }
                //     _ => code! {
                //         [0] forward_expression.map(|_| format!("assign {} = {};", name, ops[0]));
                //     }.to_string()
                // },
                _ => code! {
                    [0] forward_expression.map(|f| format!("assign {} = {};", name, f));
                }
                .to_string(),
            };

            code! {
                [0] &assignment
            }
        }
        Statement::Register(reg) => {
            let name = reg.name.var_name();
            let main_body = if let Some((rst_trig, rst_val)) = &reg.reset {
                code! {
                    [0] &format!("always @(posedge {}) begin", reg.clock.var_name());
                    [1]     &format!("if ({}) begin", rst_trig.var_name());
                    [2]         &format!("{} <= {};", name, rst_val.var_name());
                    [1]     &"end";
                    [1]     &"else begin";
                    [2]         &format!("{} <= {};", name, reg.value.var_name());
                    [1]     &"end";
                    [0] &"end"
                }
            } else {
                code! {
                    [0] &format!("always @(posedge {}) begin", reg.clock.var_name());
                    [1]     &format!("{} <= {};", name, reg.value.var_name());
                    [0] &"end"
                }
            };

            // TODO: Initial blocks
            let initial_block = if let Some(initial) = reg.initial.as_ref() {
                diag_bail!(statement, "Intial blocks are not supported");
                // TODO
                todo!()
                // code! {
                //     [0] "initial begin";
                //     [1]     format!("{} = 'b{};", name, eval_statements(initial).as_string());
                //     [0] "end";
                // }
            } else {
                code![]
            };

            code! {
                [0] initial_block;
                [0] main_body
            }
        }
        Statement::Constant(_, _, _) => {
            // Constants are fully codegened at the definition
            code! {}
        }
        Statement::Assert(val) => {
            // NOTE: Source code unwrap is semi-safe. Non-tests are expected to pass an actual
            // source code

            let mut msg_buf = termcolor::Buffer::ansi();
            let mut diag_handler = DiagHandler::new(Box::new(CodespanEmitter));

            AssertedExpression(val.clone()).report(
                &mut msg_buf,
                ctx.source_code.as_ref().unwrap(),
                &mut diag_handler,
            );

            let msg = String::from_utf8(msg_buf.as_slice().into())
                .map_err(|e| {
                    println!("Internal error {e}: Failed to generate assert message, invalid utf-8 returned by codespan");
                })
                .unwrap_or_else(|_| String::new())
                .lines()
                .map(|line| {
                    format!(r#"$display("{line}");"#)
                })
                .join("\n");

            let val_var = val.var_name();
            code! {
                [0] format!("`ifndef SYNTHESIS");
                [0] format!("always @({val_var}) begin");
                    // This #0 is a bit unintiutive, but it seems to prevent assertions
                    // triggering too early. For example, in the case of !(x == 1 && y == 2)
                    // if x 1 and updated to 2 in the time step as y is updated to not be 2,
                    // an assertion might still trigger without #0 if the update of x triggers
                    // the always block before x is updated. See for more details
                    // https://electronics.stackexchange.com/questions/99223/relation-between-delta-cycle-and-event-scheduling-in-verilog-simulation
                    [1] "#0";
                    [1] format!("assert ({val_var})");
                    [1] "`ifndef NO_PRETTY_ASSERT";
                    [1] "else begin";
                        [2] msg;
                        [2] r#"$error("Assertion failed");"#;
                        [2] r#"$fatal(1);"#;
                    [1] "end";
                    [1] "`else";
                        [2] ";";
                    [1] "`endif";
                [0] "end";
                [0] format!("`endif")
            }
        }
        Statement::Error => {
            code! {
                [0] "// Codegen ran for an error node"
            }
        }
        Statement::Instance {
            name,
            params,
            inputs,
            outputs,
            verilog_attr_groups,
        } => {
            let param_string = if params.is_empty() {
                "".into()
            } else {
                let param_strings = params
                    .iter()
                    .map(|(name, value)| format!(".{}({})", name, value))
                    .collect::<Vec<_>>();
                format!("#({})", param_strings.join(", "))
            };

            // Input args
            let args = inputs
                .iter()
                .chain(outputs)
                .map(|(name, _ty, value)| format!(".{}({})", name, value.var_name()))
                .join(", ");

            let instance_name = name.instance_name(
                ctx.unit_nameid.clone(),
                ctx.instance_map,
                ctx.instance_names,
            );

            code! {
                [0] source_attribute(&Some(statement.loc()), ctx.source_code);
                [0] codegen_verilog_attr_groups(verilog_attr_groups);
                [0] format!(
                    "{}{} \\{} ({});",
                    &name.as_verilog(),
                    if param_string.is_empty() { "".into() } else { format!("{}", param_string)},
                    instance_name,
                    args
                )
            }
        }
    };
    Ok(result)
}

fn codegen_verilog_attr_groups(groups: &[Vec<(String, Option<String>)>]) -> Code {
    let lines = groups
        .iter()
        .map(|attrs| {
            let contents = attrs
                .iter()
                .map(|(key, value)| match value {
                    Some(v) => format!(r#"{key} = "{v}""#),
                    None => key.clone(),
                })
                .join(", ");

            format!("(* {contents} *)")
        })
        .join("\n");

    code! { [0] lines; }
}

pub fn cocotb_code() -> Code {
    code! {
        [0] "`ifdef COCOTB_SIM";
        [1]   "`define COCOTB_CODE(name) \\";
        [2]     "string __top_module; \\";
        [2]     "string __vcd_file; \\";
        [2]     "initial begin \\";
        [3]       r#"if ($value$plusargs("TOP_MODULE=%s", __top_module) && __top_module == `"name`" && $value$plusargs("VCD_FILENAME=%s", __vcd_file)) begin \"#;
        [4]         "$dumpfile (__vcd_file); \\";
        [4]         "$dumpvars (0, \\name ); \\";
        [3]       "end \\";
        [2]     "end";
        [0] "`else";
        [1]   "`define COCOTB_CODE(name)";
        [0] "`endif";
    }
}

/// Source code is used for two things: mapping expressions back to their original source code
/// location, and for assertions. If source_code is None, no (* src = *) attributes will be
/// emitted, however, assertions will cause a panic. This is convenient for tests where specifying
/// source location is annoying to specify.
/// In actual compilation this should be Some
///
/// Before prerforming codegen, `prepare_codegen` should be run
pub fn entity_code(
    entity: &Entity,
    instance_map: &mut InstanceMap,
    source_code: &Option<CodeBundle>,
) -> Result<(Code, VerilogNameMap)> {
    let mut name_map = VerilogNameMap::new();

    let verilog_attr_groups = codegen_verilog_attr_groups(&entity.verilog_attr_groups);

    let entity_name = entity.name.as_verilog();

    let (argument_heads, argument_bindings): (Vec<_>, Vec<_>) = entity
        .inputs
        .iter()
        .chain(&entity.outputs)
        .map(
            |LirArg {
                 name,
                 val_name,
                 ty,
                 no_mangle,
             }|
             -> Result<_> {
                enum Dir {
                    Input,
                    Output,
                }

                let direction = match &val_name.inner {
                    ValueName::Forward(_) => Dir::Input,
                    ValueName::Backward(_) => Dir::Output,
                    ValueName::OutputFwd => Dir::Output,
                    ValueName::OutputBack => Dir::Input,
                };

                let name = match (no_mangle.is_some(), &val_name.inner) {
                    (true, _) => name.clone(),
                    (_, ValueName::Forward(_)) => format!("{name}_i"),
                    (_, ValueName::Backward(_)) => format!("{name}_o"),
                    (_, ValueName::OutputFwd) => name.clone(),
                    (_, ValueName::OutputBack) => name.clone(),
                };

                // __input and __output don't need translation from the external
                // to the internal name, and neither does no_mangle params
                let assignment = if val_name.is_output() || no_mangle.is_some() {
                    vec![]
                } else {
                    vec![match direction {
                        Dir::Input => assign(&val_name.var_name(), &name),
                        Dir::Output => assign(&name, &val_name.var_name()),
                    }]
                };

                Ok((
                    format!(
                        "{}{} {}",
                        match (ty, direction) {
                            (Type::InOut(_), _) => "inout",
                            (Type::BitVector(_), Dir::Input) => "input",
                            (Type::BitVector(_), Dir::Output) => "output",
                        },
                        size_spec(&ty.size().near_loc(val_name))?,
                        name
                    ),
                    assignment,
                ))
            },
        )
        .collect::<Result<Vec<_>>>()?
        .into_iter()
        .unzip();

    let mut ctx = Context {
        source_code,
        instance_names: &mut InstanceNameTracker::new(),
        instance_map,
        unit_nameid: &entity.name.source,
    };

    let types = LirTypeList::from_entity(entity);

    let mut body = Code::new();

    for stmt in &entity.statements {
        body.join(&statement_declaration(stmt, source_code, &mut name_map)?)
    }
    for stmt in &entity.statements {
        body.join(&statement_code(stmt, &types, &mut ctx)?)
    }

    // Collect all port definitions into an already indented code snippet
    let port_definitions = argument_heads.join(",\n");

    let code = code! {
        [0] verilog_attr_groups;
        [0] &format!("module {} (", entity_name);
                [2] &port_definitions;
            [1] &");";
            [1] format!("`COCOTB_CODE( {top_name} )", top_name = entity.name.without_escapes());
            [1] argument_bindings.into_iter().flatten().collect::<Vec<_>>();
            [1] &body;
        [0] &"endmodule"
    };
    Ok((code, name_map))
}

#[macro_export]
macro_rules! assert_same_code {
    ($got:expr, $expected:expr) => {{
        let got = $got;
        let expected = $expected;
        if got != expected {
            println!("{}:\n{}", "got".red(), got);
            println!("{}", "==============================================".red());
            println!("{}:\n{}", "expected".green(), expected);
            println!(
                "{}",
                "==============================================".green()
            );
            println!("{}", prettydiff::diff_chars(got, expected));
            println!(
                "{}",
                "==============================================".yellow()
            );
            panic!("Code mismatch")
        }
    }};
}
