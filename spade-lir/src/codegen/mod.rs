use itertools::Itertools;
use nesty::{Code, code};
use spade_codespan_reporting::term::termcolor;

use num::{BigInt, BigUint, One, Signed, Zero};
use spade_common::location_info::{Loc, WithLocation};
use spade_common::name::NameID;
use spade_common::num_ext::InfallibleToBigUint;
use spade_diagnostics::emitter::CodespanEmitter;
use spade_diagnostics::{CodeBundle, CompilationError, DiagHandler, diag_bail};
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
        }
        Statement::Register(reg) => {
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
        Statement::Set { .. } => {
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
                    logic(&val.var_name(), &ty.size().near_loc(val))
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
                    format!("{}[{}]", binding.operands[0], binding.operands[1])
                } else {
                    format!(
                        "{}[{} + {elem_size} - 1 : {}]",
                        binding.operands[0], binding.operands[1], binding.operands[1]
                    )
                }
            } else {
                if elem_size == &BigUint::one() {
                    format!(
                        "{}[{array_len} - {}]",
                        binding.operands[0], binding.operands[1]
                    )
                } else {
                    format!(
                        "{}[{array_len} - {} + {elem_size} - 1 : {array_len} - {}]",
                        binding.operands[0], binding.operands[1], binding.operands[1]
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
                    end_exclusive - BigUint::one(),
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
            // NOTE Dummy. Set in the next match statement
            String::new()
        }
        Operator::Nop => String::new(),

        Operator::Back(_) => {
            diag_bail!(
                binding,
                "Back operator should already have been lowered during codegen."
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
                    // TODO: HAndle ReadWriteItemsInOut. Can we perhaps lower this during MIR lowering?
                    todo!()
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
        Statement::Set { target, value } => {
            let mut assignments = Vec::new();

            // TODO diag_bail on zst

            assignments.push(format!(
                "assign {} = {};",
                target.var_name(),
                value.var_name(),
            ));

            code! {
                [0] assignments;
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

#[cfg(test)]
fn statement_code_and_declaration(
    statement: &Loc<Statement>,
    types: &LirTypeList, // TODO: remove
    source_code: &CodeBundle,
) -> Result<Code> {
    use spade_common::name::Path;

    let mut ctx = Context {
        source_code: &Some(source_code.clone()),
        instance_names: &mut InstanceNameTracker::new(),
        instance_map: &mut InstanceMap::new(),
        unit_nameid: &NameID(0, Path::from_strs(&["dummy"])),
    };
    Ok(code! {
        [0] statement_declaration(statement, &Some(source_code.clone()), &mut VerilogNameMap::new())?;
        [0] statement_code(statement, &types, &mut ctx)?;
    })
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
                 // TODO: I think we can remove this since it is handled already during MIR lowering
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

                let assignment = match direction {
                    Dir::Input => assign(&val_name.var_name(), name),
                    Dir::Output => assign(name, &val_name.var_name()),
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
            [1] &argument_bindings;
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

// TODO: Decide if we should get rid of these, or rewrite them to be LIR tests
// #[cfg(test)]
// mod tests {
//     use super::*;
//     use colored::Colorize;
//     use spade_common::id_tracker::ExprID;
//     use spade_common::location_info::WithLocation;
//     use spade_common::name::Path;

//     use crate as spade_mir;
//     use crate::{entity, statement, types::Type};

//     use indoc::indoc;

//     #[test]
//     fn size_1_wires_have_no_size_spec() {
//         let binding = statement!(e(0); Type::Bool; Add; e(1), e(2));

//         let expected = indoc!(
//             r#"
//             logic _e_0;
//             assign _e_0 = $signed(_e_1) + $signed(_e_2);"#
//         );

//         assert_same_code!(
//             &statement_code_and_declaration(
//                 &binding,
//                 &MirTypeList::empty(),
//                 &CodeBundle::new("".to_string())
//             )
//             .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn binding_code_works() {
//         let binding = statement!(e(0); Type::int(5); Add; e(1), e(2));

//         let expected = indoc!(
//             r#"
//             logic[4:0] _e_0;
//             assign _e_0 = $signed(_e_1) + $signed(_e_2);"#
//         );

//         assert_same_code!(
//             &statement_code_and_declaration(
//                 &binding,
//                 &MirTypeList::empty(),
//                 &CodeBundle::new("".to_string())
//             )
//             .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn registers_without_reset_work() {
//         let reg = statement!(reg n(0, "r"); Type::int(7); clock (e(0)); e(1));

//         let expected = indoc!(
//             r#"
//                 reg[6:0] \r ;
//                 always @(posedge _e_0) begin
//                     \r  <= _e_1;
//                 end"#
//         );

//         assert_same_code!(
//             &statement_code_and_declaration(
//                 &reg,
//                 &MirTypeList::empty(),
//                 &CodeBundle::new("".to_string())
//             )
//             .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn registers_with_reset_work() {
//         let reg = statement!(reg n(0, "r"); Type::int(7); clock (e(0)); reset (e(2), e(3)); e(1));

//         let expected = indoc!(
//             r#"
//                 reg[6:0] \r ;
//                 always @(posedge _e_0) begin
//                     if (_e_2) begin
//                         \r  <= _e_3;
//                     end
//                     else begin
//                         \r  <= _e_1;
//                     end
//                 end"#
//         );

//         assert_same_code!(
//             &statement_code_and_declaration(
//                 &reg,
//                 &MirTypeList::empty(),
//                 &CodeBundle::new("".to_string())
//             )
//             .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn registers_with_initial_values_work() {
//         let initial_value = vec![
//             statement!(const 4; Type::int(7); ConstantValue::int(0b10_1100)),
//             statement!(e(5); Type::int(7); Alias; e(4)),
//         ];
//         let reg =
//             statement!(reg n(0, "r"); Type::int(7); clock (e(0)); initial (initial_value); e(1));

//         let expected = indoc!(
//             r#"
//                 reg[6:0] \r ;
//                 initial begin
//                     \r  = 'b0101100;
//                 end
//                 always @(posedge _e_0) begin
//                     \r  <= _e_1;
//                 end"#
//         );

//         assert_same_code!(
//             &statement_code_and_declaration(
//                 &reg,
//                 &MirTypeList::empty(),
//                 &CodeBundle::new("".to_string())
//             )
//             .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn entity_codegen_works() {
//         let input = entity!(&["pong"]; ("op", n(0, "op"), Type::int(6)) -> Type::int(6); {
//             (e(0); Type::int(6); Add; n(0, "op"), e(1))
//         } => e(0));

//         let expected = indoc!(
//             r#"

//             module \pong  (
//                     input[5:0] op_i,
//                     output[5:0] output__
//                 );
//                 `COCOTB_CODE( pong )
//                 logic[5:0] \op ;
//                 assign \op  = op_i;
//                 logic[5:0] _e_0;
//                 assign _e_0 = $signed(\op ) + $signed(_e_1);
//                 assign output__ = _e_0;
//             endmodule"#
//         );

//         assert_same_code!(
//             &entity_code(
//                 &prepare_codegen(input.clone()),
//                 &mut InstanceMap::new(),
//                 &None
//             )
//             .0
//             .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn verilog_attr_groups_work_on_entity_declarations() {
//         let mut input = entity!(&["pong"]; ("op", n(0, "op"), Type::int(6)) -> Type::int(6); {
//             (e(0); Type::int(6); Add; n(0, "op"), e(1))
//         } => e(0));

//         input.verilog_attr_groups = vec![
//             vec![("alone".into(), None)],
//             vec![
//                 ("standalone".into(), None),
//                 ("key".into(), Some("value".into())),
//             ],
//         ];

//         let expected = indoc!(
//             r#"
//             (* alone *)
//             (* standalone, key = "value" *)
//             module \pong  (
//                     input[5:0] op_i,
//                     output[5:0] output__
//                 );
//                 `COCOTB_CODE( pong )
//                 logic[5:0] \op ;
//                 assign \op  = op_i;
//                 logic[5:0] _e_0;
//                 assign _e_0 = $signed(\op ) + $signed(_e_1);
//                 assign output__ = _e_0;
//             endmodule"#
//         );

//         assert_same_code!(
//             &entity_code(
//                 &prepare_codegen(input.clone()),
//                 &mut InstanceMap::new(),
//                 &None
//             )
//             .0
//             .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn no_mangle_input_does_not_clash() {
//         let input = spade_mir::Entity {
//             name: spade_mir::unit_name::IntoUnitName::_test_into_unit_name("test"),
//             inline: false,
//             inputs: vec![spade_mir::MirInput {
//                 name: "a".to_string(),
//                 val_name: ValueName::_test_named(0, "a".to_string()).nowhere(),
//                 ty: Type::Bool,
//                 no_mangle: Some(().nowhere()),
//             }],
//             output: ValueName::Expr(ExprID(0)).nowhere(),
//             output_type: Type::Bool,
//             statements: vec![],
//             verilog_attr_groups: vec![],
//         };

//         let expected = indoc!(
//             r#"

//             module test (
//                     input a,
//                     output output__
//                 );
//                 `COCOTB_CODE( test )
//                 assign output__ = _e_0;
//             endmodule"#
//         );

//         assert_same_code!(
//             &entity_code(
//                 &prepare_codegen(input.clone()),
//                 &mut InstanceMap::new(),
//                 &None
//             )
//             .0
//             .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn no_mangle_output_does_not_clash() {
//         let input = spade_mir::Entity {
//             name: spade_mir::unit_name::IntoUnitName::_test_into_unit_name("test"),
//             inline: false,
//             inputs: vec![spade_mir::MirInput {
//                 name: "a".to_string(),
//                 val_name: ValueName::_test_named(0, "a".to_string()).nowhere(),
//                 ty: Type::Backward(Box::new(Type::Bool)),
//                 no_mangle: Some(().nowhere()),
//             }],
//             output: ValueName::Expr(ExprID(0)).nowhere(),
//             output_type: Type::Bool,
//             statements: vec![],
//             verilog_attr_groups: vec![],
//         };

//         let expected = indoc!(
//             r#"

//             module test (
//                     output a,
//                     output output__
//                 );
//                 `COCOTB_CODE( test )
//                 logic \a_mut ;
//                 assign a = \a_mut ;
//                 assign output__ = _e_0;
//             endmodule"#
//         );

//         assert_same_code!(
//             &entity_code(
//                 &prepare_codegen(input.clone()),
//                 &mut InstanceMap::new(),
//                 &None
//             )
//             .0
//             .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn pure_backward_input_produces_output_port() {
//         let ty = Type::Backward(Box::new(Type::int(3)));
//         let input = entity!(&["test"]; ("a", n(0, "a"), ty) -> Type::int(6); {
//             (const 0; Type::int(6); crate::ConstantValue::int(3))
//         } => e(0));

//         let expected = indoc!(
//             r#"

//             module \test  (
//                     output[2:0] a_o,
//                     output[5:0] output__
//                 );
//                 `COCOTB_CODE( test )
//                 logic[2:0] \a_mut ;
//                 assign a_o = \a_mut ;
//                 localparam[5:0] _e_0 = 3;
//                 assign output__ = _e_0;
//             endmodule"#
//         );

//         assert_same_code!(
//             &entity_code(
//                 &prepare_codegen(input.clone()),
//                 &mut InstanceMap::new(),
//                 &None
//             )
//             .0
//             .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn mixed_backward_input_works() {
//         let ty = Type::Tuple(vec![Type::int(4), Type::Backward(Box::new(Type::int(3)))]);
//         let input = entity!(&["test"]; ("a", n(0, "a"), ty) -> Type::int(6); {
//             (const 0; Type::int(6); crate::ConstantValue::int(3))
//         } => e(0));

//         let expected = indoc!(
//             r#"

//             module \test  (
//                     input[3:0] a_i, output[2:0] a_o,
//                     output[5:0] output__
//                 );
//                 `COCOTB_CODE( test )
//                 logic[3:0] \a ;
//                 assign \a  = a_i;
//                 logic[2:0] \a_mut ;
//                 assign a_o = \a_mut ;
//                 localparam[5:0] _e_0 = 3;
//                 assign output__ = _e_0;
//             endmodule"#
//         );

//         assert_same_code!(
//             &entity_code(
//                 &prepare_codegen(input.clone()),
//                 &mut InstanceMap::new(),
//                 &None
//             )
//             .0
//             .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn mixed_backward_output_works() {
//         let ty = Type::Tuple(vec![Type::int(4), Type::Backward(Box::new(Type::int(3)))]);
//         let input = entity!("test"; () -> ty; {
//         } => e(0));

//         let expected = indoc!(
//             r#"

//             module test (
//                     output[3:0] output__,
//                     input[2:0] input__
//                 );
//                 `COCOTB_CODE( test )
//                 assign output__ = _e_0;
//                 assign _e_0_mut = input__;
//             endmodule"#
//         );

//         assert_same_code!(
//             &entity_code(
//                 &prepare_codegen(input.clone()),
//                 &mut InstanceMap::new(),
//                 &None
//             )
//             .0
//             .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn constant_codegen_works() {
//         let input = statement!(const 0; Type::int(10); crate::ConstantValue::int(6));

//         let expected = indoc!(
//             r#"
//             localparam[9:0] _e_0 = 6;"#
//         );

//         assert_same_code!(
//             &statement_code_and_declaration(
//                 &input,
//                 &MirTypeList::empty(),
//                 &CodeBundle::new("".to_string())
//             )
//             .to_string(),
//             expected
//         )
//     }

//     #[test]
//     fn duplicate_names_adds_nx() {
//         let input = entity!(&["pl"]; (
//             ) -> Type::int(16); {
//                 (n(1, "x"); Type::int(16); Not; e(0));
//                 (n(2, "x"); Type::int(16); Not; e(1));
//             } => n(1, "x")
//         );

//         let expected = indoc!(
//             r#"

//             module \pl  (
//                     output[15:0] output__
//                 );
//                 `COCOTB_CODE( pl )
//                 logic[15:0] \x ;
//                 logic[15:0] x_n1;
//                 assign \x  = !_e_0;
//                 assign x_n1 = !_e_1;
//                 assign output__ = \x ;
//             endmodule"#
//         );

//         assert_same_code! {
//             &entity_code(&prepare_codegen(input.clone()), &mut InstanceMap::new(), &None).0.to_string(),
//             expected
//         }
//     }

//     #[test]
//     fn instance_map_is_populated() {
//         let inst1_name = NameID(10, Path::from_strs(&["test1"]));
//         let inst1_unit_name = spade_mir::UnitName {
//             kind: spade_mir::unit_name::UnitNameKind::Unescaped("test1".into()),
//             source: inst1_name.clone(),
//         };
//         let inst2_name = NameID(11, Path::from_strs(&["test1"]));
//         let inst2_unit_name = spade_mir::UnitName {
//             kind: spade_mir::unit_name::UnitNameKind::Unescaped("test1".into()),
//             source: inst2_name.clone(),
//         };

//         let top_name = NameID(1, Path::from_strs(&["top"]));
//         let top_unit_name = spade_mir::UnitName {
//             kind: spade_mir::unit_name::UnitNameKind::Unescaped("test1".into()),
//             source: top_name.clone(),
//         };
//         let input = entity!(&top_unit_name; (
//                 "clk", n(3, "clk"), Type::Bool,
//             ) -> Type::int(16); {
//                 (reg n(10, "x__s1"); Type::int(16); clock(n(3, "clk")); n(0, "x_"));
//                 // Stage 0
//                 (e(0); Type::int(16); Instance({
//                     name: inst1_unit_name,
//                     params: vec![],
//                     argument_names: vec![
//                         ParamName{name: "a".to_string(), no_mangle: None},
//                         ParamName{name: "b".to_string(), no_mangle: None},
//                     ],
//                     loc: None,
//                     verilog_attr_groups: vec![],
//                 }););
//                 (e(0); Type::int(16); Instance({
//                     name: inst2_unit_name,
//                     params: vec![],
//                     argument_names: vec![
//                         ParamName{name: "a".to_string(), no_mangle: None},
//                         ParamName{name: "b".to_string(), no_mangle: None},
//                     ],
//                     loc: None,
//                     verilog_attr_groups: vec![],
//                 }););
//                 (n(0, "x_"); Type::int(16); Alias; e(0));
//                 // Stage 1
//                 (n(1, "x"); Type::int(16); Alias; n(0, "x_"));
//             } => n(1, "x")
//         );

//         let mut instance_map = InstanceMap::new();
//         entity_code(&prepare_codegen(input), &mut instance_map, &None);

//         let top = instance_map
//             .inner
//             .get(&(top_name.clone()))
//             .expect("Failed to get top");

//         assert_eq!(
//             top.get(&"test1_0".to_string())
//                 .expect("failed to get test1_0"),
//             &inst1_name
//         );
//         assert_eq!(
//             top.get(&"test1_1".to_string())
//                 .expect("failed to get test1_0"),
//             &inst2_name
//         );
//     }
// }

// #[cfg(test)]
// mod backward_expression_tests {
//     use super::*;
//     use colored::Colorize;
//     use spade_common::id_tracker::ExprID;

//     use crate as spade_mir;
//     use crate::{statement, types::Type};

//     use indoc::indoc;

//     #[test]
//     fn backward_alias_works() {
//         let ty = Type::Backward(Box::new(Type::int(8)));
//         let stmt = statement!(e(0); ty; Alias; e(1));

//         let expected = indoc! {
//             r#"
//             logic[7:0] _e_0_mut;
//             assign _e_1_mut = _e_0_mut;"#
//         };

//         assert_same_code!(
//             &statement_code_and_declaration(
//                 &stmt,
//                 &MirTypeList::empty(),
//                 &CodeBundle::new("".to_string())
//             )
//             .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn backward_index_tuple_works() {
//         let tuple_members = vec![Type::backward(Type::int(8)), Type::backward(Type::int(4))];
//         let ty = Type::backward(Type::int(4));
//         let stmt = statement!(e(0); ty; IndexTuple((1)); e(1));

//         let expected = indoc! {
//             r#"
//             logic[3:0] _e_0_mut;
//             assign _e_1_mut[3:0] = _e_0_mut;"#
//         };

//         assert_same_code!(
//             &statement_code_and_declaration(
//                 &stmt,
//                 &MirTypeList::empty().with(ValueName::Expr(ExprID(1)), Type::Tuple(tuple_members)),
//                 &CodeBundle::new("".to_string())
//             )
//             .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn flip_port_works() {
//         let out_type = Type::Tuple(vec![Type::backward(Type::int(2)), Type::int(4)]);
//         let stmt = statement!(e(0); out_type; FlipPort; e(1));

//         let expected = indoc! {
//             r#"
//             logic[3:0] _e_0;
//             logic[1:0] _e_0_mut;
//             assign _e_0 = _e_1_mut;
//             assign _e_1 = _e_0_mut;"#
//         };

//         assert_same_code!(
//             &statement_code_and_declaration(
//                 &stmt,
//                 &MirTypeList::empty(),
//                 &CodeBundle::new("".to_string())
//             )
//             .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn construct_tuple_works() {
//         let tuple_members = vec![Type::backward(Type::int(8)), Type::backward(Type::int(4))];
//         let ty = Type::Tuple(tuple_members);
//         let stmt = statement!(e(0); ty; ConstructTuple; e(1), e(2));

//         let type_list = MirTypeList::empty()
//             .with(ValueName::Expr(ExprID(1)), Type::backward(Type::int(8)))
//             .with(ValueName::Expr(ExprID(2)), Type::backward(Type::int(4)));

//         let expected = indoc! {
//             r#"
//             logic[11:0] _e_0_mut;
//             assign {_e_1_mut, _e_2_mut} = _e_0_mut;"#
//         };

//         assert_same_code!(
//             &statement_code_and_declaration(&stmt, &type_list, &CodeBundle::new("".to_string()))
//                 .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn construct_tuple_works_on_mixed_direction_types() {
//         let tuple_members = vec![
//             Type::backward(Type::int(8)),
//             Type::Tuple(vec![Type::backward(Type::int(4)), Type::int(4)]),
//             Type::int(3),
//         ];
//         let ty = Type::Tuple(tuple_members);
//         let stmt = statement!(e(0); ty; ConstructTuple; e(1), e(2), e(3));

//         let expected = indoc! {
//             r#"
//             logic[6:0] _e_0;
//             logic[11:0] _e_0_mut;
//             assign _e_0 = {_e_2, _e_3};
//             assign {_e_1_mut, _e_2_mut} = _e_0_mut;"#
//         };

//         let type_list = MirTypeList::empty()
//             .with(ValueName::Expr(ExprID(1)), Type::backward(Type::int(8)))
//             .with(
//                 ValueName::Expr(ExprID(2)),
//                 Type::Tuple(vec![Type::backward(Type::int(4)), Type::int(4)]),
//             )
//             .with(ValueName::Expr(ExprID(3)), Type::int(3));

//         assert_same_code!(
//             &statement_code_and_declaration(&stmt, &type_list, &CodeBundle::new("".to_string()))
//                 .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn construct_array_works() {
//         let ty = Type::Array {
//             inner: Box::new(Type::backward(Type::int(5))),
//             length: 3u32.to_biguint(),
//         };
//         let stmt = statement!(e(0); ty; ConstructArray; e(1), e(2), e(3));

//         let expected = indoc! {
//             r#"
//             logic[14:0] _e_0_mut;
//             assign {_e_3_mut, _e_2_mut, _e_1_mut} = _e_0_mut;"#
//         };

//         assert_same_code!(
//             &statement_code_and_declaration(
//                 &stmt,
//                 &MirTypeList::empty(),
//                 &CodeBundle::new("".to_string())
//             )
//             .to_string(),
//             expected
//         );
//     }
// }

// #[cfg(test)]
// mod expression_tests {
//     use super::*;
//     use colored::Colorize;
//     use spade_codespan::Span;
//     use spade_common::id_tracker::ExprID;
//     use spade_common::location_info::WithLocation;
//     use spade_common::num_ext::InfallibleToBigInt;

//     use crate::{self as spade_mir, UnitName, value_name};
//     use crate::{statement, types::Type};

//     use indoc::{formatdoc, indoc};

//     macro_rules! binop_test {
//         ($name:ident, $ty:expr, $verilog_ty:expr, $op:ident, $verilog_op:expr) => {
//             #[test]
//             fn $name() {
//                 let stmt = statement!(e(0); $ty; $op; e(1), e(2));

//                 let expected = formatdoc!(
//                     r#"
//                     logic{} _e_0;
//                     assign _e_0 = _e_1 {} _e_2;"#, $verilog_ty, $verilog_op
//                 );

//                 let mut types = MirTypeList::empty();
//                 types.add_statements(&[
//                     statement!(e(1); Type::Int(8u8.to_biguint()); Alias; e(0)),
//                     statement!(e(2); Type::Int(8u8.to_biguint()); Alias; e(0))
//                 ]);

//                 assert_same_code!(&statement_code_and_declaration(&stmt, &types, &CodeBundle::new("".to_string())).to_string(), &expected)
//             }
//         }
//     }

//     macro_rules! signed_binop_test {
//         ($name:ident, $ty:expr, $verilog_ty:expr, $op:ident, $verilog_op:expr) => {
//             #[test]
//             fn $name() {
//                 let stmt = statement!(e(0); $ty; $op; e(1), e(2));

//                 let mut types = MirTypeList::empty();
//                 types.add_statements(&[
//                     statement!(e(1); Type::Int(8u8.to_biguint()); Alias; e(0)),
//                     statement!(e(2); Type::Int(8u8.to_biguint()); Alias; e(0))
//                 ]);

//                 let expected = formatdoc!(
//                     r#"
//                     logic{} _e_0;
//                     assign _e_0 = $signed(_e_1) {} $signed(_e_2);"#, $verilog_ty, $verilog_op
//                 );

//                 assert_same_code!(&statement_code_and_declaration(&stmt, &types, &CodeBundle::new("".to_string())).to_string(), &expected)
//             }
//         }
//     }

//     macro_rules! unop_test {
//         ($name:ident, $ty:expr, $verilog_ty:expr, $op:ident, $verilog_op:expr) => {
//             #[test]
//             fn $name() {
//                 let stmt = statement!(e(0); $ty; $op; e(1));

//                 let expected = formatdoc!(
//                     r#"
//                     logic{} _e_0;
//                     assign _e_0 = {}_e_1;"#, $verilog_ty, $verilog_op
//                 );

//                 assert_same_code!(&statement_code_and_declaration(&stmt, &MirTypeList::empty(), &CodeBundle::new("".to_string())).to_string(), &expected)
//             }
//         }
//     }

//     signed_binop_test!(binop_add_works, Type::int(2), "[1:0]", Add, "+");
//     signed_binop_test!(binop_sub_works, Type::int(2), "[1:0]", Sub, "-");
//     signed_binop_test!(binop_mul_works, Type::int(2), "[1:0]", Mul, "*");
//     binop_test!(
//         binop_left_shift_works,
//         Type::int(2),
//         "[1:0]",
//         LeftShift,
//         "<<"
//     );
//     binop_test!(
//         binop_right_shift_works,
//         Type::int(2),
//         "[1:0]",
//         RightShift,
//         ">>"
//     );
//     signed_binop_test!(
//         binop_arithmetic_right_shift_works,
//         Type::int(2),
//         "[1:0]",
//         ArithmeticRightShift,
//         ">>>"
//     );
//     binop_test!(binop_eq_works, Type::Bool, "", Eq, "==");
//     signed_binop_test!(binop_gt_works, Type::Bool, "", Gt, ">");
//     signed_binop_test!(binop_lt_works, Type::Bool, "", Lt, "<");
//     signed_binop_test!(binop_ge_works, Type::Bool, "", Ge, ">=");
//     signed_binop_test!(binop_le_works, Type::Bool, "", Le, "<=");
//     binop_test!(binop_logical_and_works, Type::Bool, "", LogicalAnd, "&&");
//     binop_test!(binop_logical_or_works, Type::Bool, "", LogicalOr, "||");
//     binop_test!(bitwise_xor_works, Type::int(32), "[31:0]", BitwiseXor, "^");
//     // NOTE: The resulting verilog uses `^` on a 1 bit value
//     binop_test!(logical_xor_works, Type::Bool, "", LogicalXor, "^");
//     unop_test!(not_works, Type::Bool, "", Not, "!");
//     unop_test!(usub_works, Type::int(2), "[1:0]", USub, "-");

//     #[test]
//     fn select_operator_works() {
//         let stmt = statement!(e(0); Type::int(2); Select; e(1), e(2), e(3));

//         let expected = indoc!(
//             r#"
//             logic[1:0] _e_0;
//             assign _e_0 = _e_1 ? _e_2 : _e_3;"#
//         );

//         assert_same_code!(
//             &statement_code_and_declaration(
//                 &stmt,
//                 &MirTypeList::empty(),
//                 &CodeBundle::new("".to_string())
//             )
//             .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn not_operator_works() {
//         let stmt = statement!(e(0); Type::Bool; LogicalNot; e(1));

//         let expected = indoc!(
//             r#"
//             logic _e_0;
//             assign _e_0 = !_e_1;"#
//         );

//         assert_same_code!(
//             &statement_code_and_declaration(
//                 &stmt,
//                 &MirTypeList::empty(),
//                 &CodeBundle::new("".to_string())
//             )
//             .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn match_operator_works() {
//         let stmt = statement!(e(0); Type::int(2); Match; e(1), e(2), e(3), e(4));

//         let expected = indoc!(
//             r#"
//             logic[1:0] _e_0;
//             always_comb begin
//                 priority casez ({_e_1, _e_3})
//                     2'b1?: _e_0 = _e_2;
//                     2'b01: _e_0 = _e_4;
//                     2'b?: _e_0 = 2'dx;
//                 endcase
//             end"#
//         );

//         assert_same_code!(
//             &statement_code_and_declaration(
//                 &stmt,
//                 &MirTypeList::empty(),
//                 &CodeBundle::new("".to_string())
//             )
//             .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn boolean_constants_are_1_and_0() {
//         let stmt = statement!(const 0; Type::Bool; ConstantValue::Bool(true));

//         let expected = indoc!(
//             r#"
//             localparam[0:0] _e_0 = 1;"#
//         );

//         assert_same_code!(
//             &statement_code_and_declaration(
//                 &stmt,
//                 &MirTypeList::empty(),
//                 &CodeBundle::new("".to_string())
//             )
//             .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn tuple_assembly_operator_works() {
//         let ty = Type::Tuple(vec![Type::int(6), Type::int(3)]);
//         let stmt = statement!(e(0); ty; ConstructTuple; e(1), e(2));

//         let expected = indoc!(
//             r#"
//             logic[8:0] _e_0;
//             assign _e_0 = {_e_1, _e_2};"#
//         );

//         assert_same_code!(
//             &statement_code_and_declaration(
//                 &stmt,
//                 &MirTypeList::empty()
//                     .with(ValueName::Expr(ExprID(1)), Type::int(6))
//                     .with(ValueName::Expr(ExprID(2)), Type::int(3)),
//                 &CodeBundle::new("".to_string())
//             )
//             .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn enum_construction_operator_works() {
//         let ty = Type::Enum(vec![vec![], vec![], vec![Type::int(10), Type::int(5)]]);
//         let stmt = statement!(e(0); ty; ConstructEnum({variant: 2}); e(1), e(2));

//         let expected = indoc!(
//             r#"
//             logic[16:0] _e_0;
//             assign _e_0 = {2'd2, _e_1, _e_2};"#
//         );

//         assert_same_code!(
//             &statement_code_and_declaration(
//                 &stmt,
//                 &MirTypeList::empty(),
//                 &CodeBundle::new("".to_string())
//             )
//             .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn is_enum_variant_operator_works() {
//         let ty = Type::Enum(vec![vec![], vec![], vec![Type::int(10), Type::int(5)]]);
//         let stmt = statement!(e(0); Type::Bool; IsEnumVariant({variant: 2}); e(1));

//         let expected = indoc!(
//             r#"
//             logic _e_0;
//             assign _e_0 = _e_1[16:15] == 2'd2;"#
//         );

//         assert_same_code!(
//             &statement_code_and_declaration(
//                 &stmt,
//                 &MirTypeList::empty().with(ValueName::Expr(ExprID(1)), ty),
//                 &CodeBundle::new("".to_string())
//             )
//             .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn is_enum_variant_operator_works_for_1_wide_tags() {
//         let ty = Type::Enum(vec![vec![], vec![Type::int(10), Type::int(5)]]);
//         let stmt = statement!(e(0); Type::Bool; IsEnumVariant({variant: 1}); e(1));

//         let expected = indoc!(
//             r#"
//             logic _e_0;
//             assign _e_0 = _e_1[15] == 1'd1;"#
//         );

//         assert_same_code!(
//             &statement_code_and_declaration(
//                 &stmt,
//                 &MirTypeList::empty().with(ValueName::Expr(ExprID(1)), ty),
//                 &CodeBundle::new("".to_string())
//             )
//             .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn enum_member_access_operator_works() {
//         let ty = Type::Enum(vec![vec![], vec![], vec![Type::int(10), Type::int(5)]]);
//         let stmt = statement!(e(0); Type::int(5); EnumMember({variant: 2, member_index: 1}); e(1));

//         let expected = indoc!(
//             r#"
//             logic[4:0] _e_0;
//             assign _e_0 = _e_1[4:0];"#
//         );

//         assert_same_code!(
//             &statement_code_and_declaration(
//                 &stmt,
//                 &MirTypeList::empty().with(ValueName::Expr(ExprID(1)), ty),
//                 &CodeBundle::new("".to_string())
//             )
//             .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn enum_construction_inserts_padding_undef_where_needed() {
//         let ty = Type::Enum(vec![
//             vec![],
//             vec![Type::int(5)],
//             vec![Type::int(10), Type::int(5)],
//         ]);
//         let stmt = statement!(e(0); ty; ConstructEnum({variant: 1}); e(1));

//         let expected = indoc!(
//             r#"
//             logic[16:0] _e_0;
//             assign _e_0 = {2'd1, _e_1, 10'bX};"#
//         );

//         assert_same_code!(
//             &statement_code_and_declaration(
//                 &stmt,
//                 &MirTypeList::empty(),
//                 &CodeBundle::new("".to_string())
//             )
//             .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn tuple_indexing_works_for_first_value() {
//         let ty = Type::Tuple(vec![Type::int(6), Type::int(3)]);
//         let stmt = statement!(e(0); Type::int(6); IndexTuple((0)); e(1));

//         let expected = indoc!(
//             r#"
//             logic[5:0] _e_0;
//             assign _e_0 = _e_1[8:3];"#
//         );

//         assert_same_code!(
//             &statement_code_and_declaration(
//                 &stmt,
//                 &MirTypeList::empty().with(ValueName::Expr(ExprID(1)), ty),
//                 &CodeBundle::new("".to_string())
//             )
//             .to_string(),
//             expected
//         );
//     }
//     #[test]
//     fn tuple_indexing_works() {
//         let ty = Type::Tuple(vec![Type::int(6), Type::int(3)]);
//         let stmt = statement!(e(0); Type::int(6); IndexTuple((1)); e(1));

//         let expected = indoc!(
//             r#"
//             logic[5:0] _e_0;
//             assign _e_0 = _e_1[2:0];"#
//         );

//         assert_same_code!(
//             &statement_code_and_declaration(
//                 &stmt,
//                 &MirTypeList::empty().with(ValueName::Expr(ExprID(1)), ty),
//                 &CodeBundle::new("".to_string())
//             )
//             .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn tuple_indexing_works_for_bools() {
//         let ty = Type::Tuple(vec![Type::Bool, Type::int(3)]);
//         let stmt = statement!(e(0); Type::Bool; IndexTuple((0)); e(1));

//         let expected = indoc!(
//             r#"
//             logic _e_0;
//             assign _e_0 = _e_1[3];"#
//         );

//         assert_same_code!(
//             &statement_code_and_declaration(
//                 &stmt,
//                 &MirTypeList::empty().with(ValueName::Expr(ExprID(1)), ty),
//                 &CodeBundle::new("".to_string())
//             )
//             .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn large_negative_literals_codegen_correctly() {
//         let statement = statement!(const 0; Type::int(64); ConstantValue::int(-1));

//         let expected = indoc!(
//             r#"
//             localparam[63:0] _e_0 = -64'd1;"#
//         );

//         assert_same_code!(
//             &statement_code_and_declaration(
//                 &statement,
//                 &MirTypeList::empty(),
//                 &CodeBundle::new("".to_string())
//             )
//             .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn array_literals_work() {
//         let ty = Type::Array {
//             inner: Box::new(Type::int(3)),
//             length: 3u32.to_biguint(),
//         };
//         let statement = statement!(e(0); ty; ConstructArray; e(1), e(2), e(3));

//         let expected = indoc!(
//             r#"
//             logic[8:0] _e_0;
//             assign _e_0 = {_e_3, _e_2, _e_1};"#
//         );

//         assert_same_code!(
//             &statement_code_and_declaration(
//                 &statement,
//                 &MirTypeList::empty(),
//                 &CodeBundle::new("".to_string())
//             )
//             .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn array_indexing_works() {
//         let statement = statement!(e(0); Type::int(3); IndexArray; e(1), e(2));

//         let expected = indoc!(
//             r#"
//             logic[2:0] _e_0;
//             assign _e_0 = _e_1[_e_2 * 3+:3];"#
//         );

//         assert_same_code!(
//             &statement_code_and_declaration(
//                 &statement,
//                 &MirTypeList::empty().with(
//                     ValueName::Expr(ExprID(1)),
//                     Type::Array {
//                         inner: Box::new(Type::int(3)),
//                         length: 3_u32.to_biguint(),
//                     }
//                 ),
//                 &CodeBundle::new("".to_string())
//             )
//             .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn array_indexing_works_for_1_bit_values() {
//         let statement = statement!(e(0); Type::Bool; IndexArray; e(1), e(2));

//         let expected = indoc!(
//             r#"
//             logic _e_0;
//             assign _e_0 = _e_1[_e_2];"#
//         );

//         assert_same_code!(
//             &statement_code_and_declaration(
//                 &statement,
//                 &MirTypeList::empty().with(
//                     ValueName::Expr(ExprID(1)),
//                     Type::Array {
//                         inner: Box::new(Type::Bool),
//                         length: 4_u32.to_biguint(),
//                     }
//                 ),
//                 &CodeBundle::new("".to_string())
//             )
//             .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn array_indexing_works_for_1_element_bool_arrays() {
//         let statement = statement!(e(0); Type::Bool; IndexArray; e(1), e(2));

//         let expected = indoc!(
//             r#"
//             logic _e_0;
//             assign _e_0 = _e_1;"#
//         );

//         assert_same_code!(
//             &statement_code_and_declaration(
//                 &statement,
//                 &MirTypeList::empty().with(
//                     ValueName::Expr(ExprID(1)),
//                     Type::Array {
//                         inner: Box::new(Type::Bool),
//                         length: 1_u32.to_biguint(),
//                     }
//                 ),
//                 &CodeBundle::new("".to_string())
//             )
//             .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn array_indexing_works_for_1_element_int_arrays() {
//         let statement = statement!(e(0); Type::int(10); IndexArray; e(1), e(2));

//         let expected = indoc!(
//             r#"
//             logic[9:0] _e_0;
//             assign _e_0 = _e_1;"#
//         );

//         assert_same_code!(
//             &statement_code_and_declaration(
//                 &statement,
//                 &MirTypeList::empty().with(
//                     ValueName::Expr(ExprID(1)),
//                     Type::Array {
//                         inner: Box::new(Type::int(10)),
//                         length: 1_u32.to_biguint(),
//                     }
//                 ),
//                 &CodeBundle::new("".to_string())
//             )
//             .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn range_array_indexing_works() {
//         let ty = Type::Array {
//             inner: Box::new(Type::int(10)),
//             length: 2u32.to_biguint(),
//         };
//         let statement = statement!(e(0); ty; RangeIndexArray({
//             start: 1u32.to_biguint(),
//             end_exclusive: 2u32.to_biguint(),
//         }); e(1), e(2));

//         let expected = indoc!(
//             r#"
//             logic[19:0] _e_0;
//             assign _e_0 = _e_1[19-:10];"#
//         );

//         assert_same_code!(
//             &statement_code_and_declaration(
//                 &statement,
//                 &MirTypeList::empty().with(
//                     ValueName::Expr(ExprID(1)),
//                     Type::Array {
//                         inner: Box::new(Type::int(10)),
//                         length: 4u32.to_biguint(),
//                     }
//                 ),
//                 &CodeBundle::new("".to_string())
//             )
//             .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn range_array_indexing_on_bool_array_works() {
//         let ty = Type::Array {
//             inner: Box::new(Type::Bool),
//             length: 2u32.to_biguint(),
//         };
//         let statement = statement!(e(0); ty; RangeIndexArray({
//             start: 1u32.to_biguint(),
//             end_exclusive: 2u32.to_biguint(),
//         }); e(1), e(2));

//         let expected = indoc!(
//             r#"
//             logic[1:0] _e_0;
//             assign _e_0 = _e_1[1];"#
//         );

//         assert_same_code!(
//             &statement_code_and_declaration(
//                 &statement,
//                 &MirTypeList::empty().with(
//                     ValueName::Expr(ExprID(1)),
//                     Type::Array {
//                         inner: Box::new(Type::Bool),
//                         length: 4u32.to_biguint(),
//                     }
//                 ),
//                 &CodeBundle::new("".to_string())
//             )
//             .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn range_array_indexing_on_single_element_array_works() {
//         let ty = Type::Array {
//             inner: Box::new(Type::int(10)),
//             length: 1u32.to_biguint(),
//         };
//         let statement = statement!(e(0); ty; RangeIndexArray({
//             start: 1u32.to_biguint(),
//             end_exclusive: 2u32.to_biguint(),
//         }); e(1), e(2));

//         let expected = indoc!(
//             r#"
//             logic[9:0] _e_0;
//             assign _e_0 = _e_1;"#
//         );

//         assert_same_code!(
//             &statement_code_and_declaration(
//                 &statement,
//                 &MirTypeList::empty().with(
//                     ValueName::Expr(ExprID(1)),
//                     Type::Array {
//                         inner: Box::new(Type::int(10)),
//                         length: 1u32.to_biguint(),
//                     }
//                 ),
//                 &CodeBundle::new("".to_string())
//             )
//             .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn entity_instantiation_works() {
//         let inst_name = UnitName::_test_from_strs(&["e_test"]);
//         let stmt = statement!(
//             e(0); Type::Bool; Instance({
//                 name: inst_name,
//                 params: vec![],
//                 argument_names: vec![
//                     ParamName{name: "a".to_string(), no_mangle: None},
//                     ParamName{name: "b".to_string(), no_mangle: None},
//                 ],
//                 loc: None,
//                 verilog_attr_groups: vec![],
//             });
//             e(1),
//             e(2)
//         );

//         let expected = indoc!(
//             r#"
//             logic _e_0;

//             \e_test  \e_test_0 (.a_i(_e_1), .b_i(_e_2), .output__(_e_0));"#
//         );

//         assert_same_code!(
//             &statement_code_and_declaration(
//                 &stmt,
//                 &MirTypeList::empty()
//                     .with(ValueName::Expr(ExprID(1)), Type::Bool)
//                     .with(ValueName::Expr(ExprID(2)), Type::Bool),
//                 &CodeBundle::new("".to_string())
//             )
//             .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn entity_instantiation_with_back_and_forward_ports_works() {
//         let inst_name = UnitName::_test_from_strs(&["e_test"]);
//         let ty = Type::Tuple(vec![Type::backward(Type::Bool), Type::Bool]);
//         let stmt = statement!(e(0); ty; Instance({
//             name: inst_name,
//             params: vec![],
//             argument_names: vec![
//                 ParamName{name: "a".to_string(), no_mangle: None},
//                 ParamName{name: "b".to_string(), no_mangle: None},
//             ],
//             loc: None,
//             verilog_attr_groups: vec![],
//         }); e(1), e(2));

//         let expected = indoc!(
//             r#"
//             logic _e_0;
//             logic _e_0_mut;

//             \e_test  \e_test_0 (.a_i(_e_1), .b_i(_e_2), .output__(_e_0), .input__(_e_0_mut));"#
//         );

//         assert_same_code!(
//             &statement_code_and_declaration(
//                 &stmt,
//                 &MirTypeList::empty()
//                     .with(ValueName::Expr(ExprID(1)), Type::Bool)
//                     .with(ValueName::Expr(ExprID(2)), Type::Bool),
//                 &CodeBundle::new("".to_string())
//             )
//             .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn entity_instantiation_with_back_ports_works() {
//         let ty = Type::backward(Type::Bool);
//         let stmt = statement!(e(0); ty; Instance({
//             name:UnitName::_test_from_strs(&["e_test"]),
//             params: vec![],
//             argument_names: vec![
//                 ParamName{name: "a".to_string(), no_mangle: None},
//                 ParamName{name: "b".to_string(), no_mangle: None},
//             ],
//             loc: None,
//             verilog_attr_groups: vec![],
//         }); e(1), e(2));

//         let expected = indoc!(
//             r#"
//             logic _e_0_mut;

//             \e_test  \e_test_0 (.a_i(_e_1), .b_i(_e_2), .input__(_e_0_mut));"#
//         );

//         assert_same_code!(
//             &statement_code_and_declaration(
//                 &stmt,
//                 &MirTypeList::empty()
//                     .with(ValueName::Expr(ExprID(1)), Type::Bool)
//                     .with(ValueName::Expr(ExprID(2)), Type::Bool),
//                 &CodeBundle::new("".to_string())
//             )
//             .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn entity_instantiation_with_back_inputs_works() {
//         let ty = Type::Bool;
//         let stmt = statement!(e(0); ty; Instance({
//             name:UnitName::_test_from_strs(&["test"]),
//             params: vec![],
//             argument_names: vec![
//                 ParamName{name: "a".to_string(), no_mangle: None},
//                 ParamName{name: "b".to_string(), no_mangle: None},
//             ],
//             loc: None,
//             verilog_attr_groups: vec![],
//         }); e(1), e(2));

//         let expected = indoc!(
//             r#"
//             logic _e_0;

//             \test  \test_0 (.a_i(_e_1), .a_o(_e_1_mut), .b_o(_e_2_mut), .output__(_e_0));"#
//         );

//         let type_list = MirTypeList::empty()
//             .with(
//                 ValueName::Expr(ExprID(1)),
//                 Type::Tuple(vec![Type::Bool, Type::backward(Type::Bool)]),
//             )
//             .with(ValueName::Expr(ExprID(2)), Type::backward(Type::Bool));

//         assert_same_code!(
//             &statement_code_and_declaration(&stmt, &type_list, &CodeBundle::new("".to_string()))
//                 .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn decl_clocked_array_works() {
//         let t = Type::Memory {
//             inner: Box::new(Type::int(6)),
//             length: 16u32.to_biguint(),
//         };
//         let stmt = statement!(e(0); t; DeclClockedMemory({initial: None}); e(1), e(2));

//         // Total write array length: 2 * (1 + 4 + 6)

//         let expected = indoc!(
//             r#"
//             logic[6-1:0] _e_0[16-1:0];
//             always @(posedge _e_1) begin
//                 if (_e_2[10]) begin
//                     _e_0[_e_2[9:6]] <= _e_2[5:0];
//                 end
//                 if (_e_2[21]) begin
//                     _e_0[_e_2[20:17]] <= _e_2[16:11];
//                 end
//             end"#
//         );

//         assert_same_code!(
//             &statement_code_and_declaration(
//                 &stmt,
//                 &MirTypeList::empty().with(
//                     ValueName::Expr(ExprID(2)),
//                     Type::Array {
//                         inner: Box::new(Type::Tuple(vec![Type::Bool, Type::uint(4), Type::int(6)])),
//                         length: 2u32.to_biguint(),
//                     }
//                 ),
//                 &CodeBundle::new("".to_string())
//             )
//             .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn decl_clocked_array_with_1_bit_address_works() {
//         let t = Type::Memory {
//             inner: Box::new(Type::int(6)),
//             length: 2u32.to_biguint(),
//         };
//         let stmt = statement!(e(0); t; DeclClockedMemory({initial: None}); e(1), e(2));

//         let expected = indoc!(
//             r#"
//             logic[6-1:0] _e_0[2-1:0];
//             always @(posedge _e_1) begin
//                 if (_e_2[7]) begin
//                     _e_0[_e_2[6]] <= _e_2[5:0];
//                 end
//             end"#
//         );

//         assert_same_code!(
//             &statement_code_and_declaration(
//                 &stmt,
//                 &MirTypeList::empty().with(
//                     ValueName::Expr(ExprID(2)),
//                     Type::Array {
//                         inner: Box::new(Type::Tuple(vec![Type::Bool, Type::uint(1), Type::int(6)])),
//                         length: 1u32.to_biguint(),
//                     }
//                 ),
//                 &CodeBundle::new("".to_string())
//             )
//             .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn decl_clocked_array_with_1_bit_data_works() {
//         let t = Type::Memory {
//             inner: Box::new(Type::Bool),
//             length: 16u32.to_biguint(),
//         };
//         let stmt = statement!(e(0); t; DeclClockedMemory({initial: None}); e(1), e(2));

//         // Total write array length: 2 * (1 + 4 + 6)

//         let expected = indoc!(
//             r#"
//             logic _e_0[16-1:0];
//             always @(posedge _e_1) begin
//                 if (_e_2[5]) begin
//                     _e_0[_e_2[4:1]] <= _e_2[0];
//                 end
//             end"#
//         );

//         assert_same_code!(
//             &statement_code_and_declaration(
//                 &stmt,
//                 &MirTypeList::empty().with(
//                     ValueName::Expr(ExprID(2)),
//                     Type::Array {
//                         inner: Box::new(Type::Tuple(vec![Type::Bool, Type::uint(4), Type::Bool])),
//                         length: 1u32.to_biguint(),
//                     }
//                 ),
//                 &CodeBundle::new("".to_string())
//             )
//             .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn decl_clocked_memory_with_initial_works() {
//         let t = Type::Memory {
//             inner: Box::new(Type::Int(6u32.to_biguint())),
//             length: 16u32.to_biguint(),
//         };
//         let stmt = statement!(e(0); t; DeclClockedMemory({
//             initial: Some(vec![
//                 vec![statement!(const 10; Type::Int(6u32.to_biguint()); ConstantValue::Int(10.to_bigint()))],
//                 vec![statement!(const 10; Type::Int(6u32.to_biguint()); ConstantValue::Int(5.to_bigint()))],
//             ])
//         }); e(1), e(2));

//         // Total write array length: 2 * (1 + 4 + 6)

//         let expected = indoc!(
//             r#"
//             logic[6-1:0] _e_0[16-1:0];
//             initial begin
//                 _e_0[0] = 'b001010;
//                 _e_0[1] = 'b000101;
//             end
//             always @(posedge _e_1) begin
//                 if (_e_2[10]) begin
//                     _e_0[_e_2[9:6]] <= _e_2[5:0];
//                 end
//                 if (_e_2[21]) begin
//                     _e_0[_e_2[20:17]] <= _e_2[16:11];
//                 end
//             end"#
//         );

//         assert_same_code!(
//             &statement_code_and_declaration(
//                 &stmt,
//                 &MirTypeList::empty().with(
//                     ValueName::Expr(ExprID(2)),
//                     Type::Array {
//                         inner: Box::new(Type::Tuple(vec![Type::Bool, Type::uint(4), Type::int(6)])),
//                         length: 2u32.to_biguint(),
//                     }
//                 ),
//                 &CodeBundle::new("".to_string())
//             )
//             .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn truncate_works() {
//         let stmt = statement!(e(0); Type::int(5); Truncate; e(1));

//         let expected = indoc! {
//             r#"
//             logic[4:0] _e_0;
//             assign _e_0 = _e_1[4:0];"#
//         };

//         assert_same_code!(
//             &statement_code_and_declaration(
//                 &stmt,
//                 &MirTypeList::empty(),
//                 &CodeBundle::new("".to_string())
//             )
//             .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn sext_works_for_many_bits() {
//         let stmt = statement!(e(0); Type::int(5); SignExtend; e(1));

//         let expected = indoc! {
//             r#"
//             logic[4:0] _e_0;
//             assign _e_0 = {{ 2 { _e_1[2] }}, _e_1};"#
//         };

//         assert_same_code!(
//             &statement_code_and_declaration(
//                 &stmt,
//                 &MirTypeList::empty()
//                     .with(ValueName::Expr(ExprID(0)), Type::Int(5_u32.to_biguint()))
//                     .with(ValueName::Expr(ExprID(1)), Type::Int(3_u32.to_biguint())),
//                 &CodeBundle::new("".to_string())
//             )
//             .to_string(),
//             expected
//         );
//     }
//     #[test]
//     fn sext_works_for_one_bits() {
//         let stmt = statement!(e(0); Type::int(4); SignExtend; e(1));

//         let expected = indoc! {
//             r#"
//             logic[3:0] _e_0;
//             assign _e_0 = {_e_1[2], _e_1};"#
//         };

//         assert_same_code!(
//             &statement_code_and_declaration(
//                 &stmt,
//                 &MirTypeList::empty()
//                     .with(ValueName::Expr(ExprID(0)), Type::Int(4_u32.to_biguint()))
//                     .with(ValueName::Expr(ExprID(1)), Type::Int(3_u32.to_biguint())),
//                 &CodeBundle::new("".to_string())
//             )
//             .to_string(),
//             expected
//         );
//     }
//     #[test]
//     fn sext_works_for_zero_bits() {
//         let stmt = statement!(e(0); Type::int(3); SignExtend; e(1));

//         let expected = indoc! {
//             r#"
//             logic[2:0] _e_0;
//             assign _e_0 = _e_1;"#
//         };

//         assert_same_code!(
//             &statement_code_and_declaration(
//                 &stmt,
//                 &MirTypeList::empty()
//                     .with(ValueName::Expr(ExprID(0)), Type::Int(3_u32.to_biguint()))
//                     .with(ValueName::Expr(ExprID(1)), Type::Int(3_u32.to_biguint())),
//                 &CodeBundle::new("".to_string())
//             )
//             .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn zext_works_for_many_bits() {
//         let stmt = statement!(e(0); Type::int(5); ZeroExtend; e(1));

//         let expected = indoc! {
//             r#"
//             logic[4:0] _e_0;
//             assign _e_0 = {2'b0, _e_1};"#
//         };

//         assert_same_code!(
//             &statement_code_and_declaration(
//                 &stmt,
//                 &MirTypeList::empty()
//                     .with(ValueName::Expr(ExprID(0)), Type::UInt(5_u32.to_biguint()))
//                     .with(ValueName::Expr(ExprID(1)), Type::UInt(3_u32.to_biguint())),
//                 &CodeBundle::new("".to_string())
//             )
//             .to_string(),
//             expected
//         );
//     }
//     #[test]
//     fn zext_works_for_one_bits() {
//         let stmt = statement!(e(0); Type::int(4); ZeroExtend; e(1));

//         let expected = indoc! {
//             r#"
//             logic[3:0] _e_0;
//             assign _e_0 = {1'b0, _e_1};"#
//         };

//         assert_same_code!(
//             &statement_code_and_declaration(
//                 &stmt,
//                 &MirTypeList::empty()
//                     .with(ValueName::Expr(ExprID(0)), Type::UInt(4_u32.to_biguint()))
//                     .with(ValueName::Expr(ExprID(1)), Type::UInt(3_u32.to_biguint())),
//                 &CodeBundle::new("".to_string())
//             )
//             .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn zext_works_for_zero_bits() {
//         let stmt = statement!(e(0); Type::int(3); ZeroExtend; e(1));

//         let expected = indoc! {
//             r#"
//             logic[2:0] _e_0;
//             assign _e_0 = _e_1;"#
//         };

//         assert_same_code!(
//             &statement_code_and_declaration(
//                 &stmt,
//                 &MirTypeList::empty()
//                     .with(ValueName::Expr(ExprID(0)), Type::UInt(3_u32.to_biguint()))
//                     .with(ValueName::Expr(ExprID(1)), Type::UInt(3_u32.to_biguint())),
//                 &CodeBundle::new("".to_string())
//             )
//             .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn div_pow2_works() {
//         let stmt = statement!(e(0); Type::int(3); DivPow2; e(1), e(2));

//         let expected = indoc! {
//             r#"
//             logic[2:0] _e_0;
//             always_comb begin
//                 if (_e_2 == 0) begin
//                     _e_0 = _e_1;
//                 end
//                 else begin
//                     _e_0 = $signed($signed(_e_1) + $signed(1 << (_e_2 - 1))) >>> $signed(_e_2);
//                 end
//             end"#
//         };

//         assert_same_code!(
//             &statement_code_and_declaration(
//                 &stmt,
//                 &MirTypeList::empty(),
//                 &CodeBundle::new("".to_string())
//             )
//             .to_string(),
//             expected
//         )
//     }

//     #[test]
//     fn concat_works() {
//         let stmt = statement!(e(0); Type::int(8); Concat; e(1), e(2));

//         let type_list = MirTypeList::empty()
//             .with(ValueName::Expr(ExprID(1)), Type::int(4))
//             .with(ValueName::Expr(ExprID(2)), Type::int(4));

//         let expected = indoc! {
//             r#"
//             logic[7:0] _e_0;
//             assign _e_0 = {_e_1, _e_2};"#
//         };

//         assert_same_code!(
//             &statement_code_and_declaration(&stmt, &type_list, &CodeBundle::new("".to_string()))
//                 .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn concat_works_with_one_zero_sized_arg() {
//         let stmt = statement!(e(0); Type::int(4); Concat; e(1), e(2));

//         let type_list = MirTypeList::empty()
//             .with(ValueName::Expr(ExprID(1)), Type::int(0))
//             .with(ValueName::Expr(ExprID(2)), Type::int(4));

//         let expected = indoc! {
//             r#"
//             logic[3:0] _e_0;
//             assign _e_0 = {_e_2};"#
//         };

//         assert_same_code!(
//             &statement_code_and_declaration(&stmt, &type_list, &CodeBundle::new("".to_string()))
//                 .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn assertion_codegen_works() {
//         let stmt = Statement::Assert(value_name!(e(0)).inner.at(0, &Span::new(1, 2))).nowhere();

//         // NOTE: The escape sequences here are a bit annoying when this test fails,
//         // but where to add an option to turn them off isn't obvious. To update this test
//         // verify that the output is correct, then run `cargo test | sed -e 's/\x1b/_x1b_/g'`
//         // and copy paste the output here. Escape the " characters and replace _x1b_ with \x1b
//         let expected = indoc! {
//             "
//             `ifndef SYNTHESIS
//             always @(_e_0) begin
//                 #0
//                 assert (_e_0)
//                 `ifndef NO_PRETTY_ASSERT
//                 else begin
//                     $display(\"\x1b[0m\x1b[1m\x1b[38;5;9merror\x1b[0m\x1b[1m: Assertion failed\x1b[0m\");
//                     $display(\"  \x1b[0m\x1b[34m┌─\x1b[0m <str>:1:2\");
//                     $display(\"  \x1b[0m\x1b[34m│\x1b[0m\");
//                     $display(\"\x1b[0m\x1b[34m1\x1b[0m \x1b[0m\x1b[34m│\x1b[0m a\x1b[0m\x1b[38;5;9mb\x1b[0mcd\");
//                     $display(\"  \x1b[0m\x1b[34m│\x1b[0m  \x1b[0m\x1b[38;5;9m^\x1b[0m \x1b[0m\x1b[38;5;9mThis expression is false\x1b[0m\");
//                     $display(\"\");
//                     $error(\"Assertion failed\");
//                     $fatal(1);
//                 end
//                 `else
//                     ;
//                 `endif
//             end
//             `endif"
//         };

//         let source_code = CodeBundle::new("abcd".to_string());

//         assert_same_code!(
//             &statement_code_and_declaration(&stmt, &MirTypeList::empty(), &source_code).to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn set_codegen_works() {
//         let stmt = Statement::Set {
//             target: value_name!(e(0)),
//             value: value_name!(e(1)),
//         };

//         let expected = indoc! {
//             r#"
//             assign _e_0_mut = _e_1;"#
//         };

//         assert_same_code!(
//             &statement_code_and_declaration(
//                 &stmt,
//                 &MirTypeList::empty()
//                     .with(ValueName::Expr(ExprID(0)), Type::backward(Type::Bool))
//                     .with(ValueName::Expr(ExprID(1)), Type::Bool),
//                 &CodeBundle::new("".to_string())
//             )
//             .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn read_mut_wire_codegen_works() {
//         let stmt = statement!(e(0); Type::int(8); ReadPort; e(1));

//         let expected = indoc! {
//             r#"
//             logic[7:0] _e_0;
//             assign _e_0 = _e_1_mut;"#
//         };

//         assert_same_code!(
//             &statement_code_and_declaration(
//                 &stmt,
//                 &MirTypeList::empty(),
//                 &CodeBundle::new("".to_string())
//             )
//             .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn const_codegen_large_bit_width_works() {
//         let stmt = statement!(const 0; Type::int(32); crate::ConstantValue::int(3));

//         let expected = indoc! {
//             r#"
//             localparam[31:0] _e_0 = 32'd3;"#
//         };

//         assert_same_code!(
//             &statement_code_and_declaration(
//                 &stmt,
//                 &MirTypeList::empty(),
//                 &CodeBundle::new("".to_string())
//             )
//             .to_string(),
//             expected
//         );
//     }

//     #[test]
//     #[should_panic]
//     fn compute_index_regression() {
//         let result = compute_tuple_index(
//             2,
//             &[
//                 24u32.to_biguint(),
//                 17u32.to_biguint(),
//                 0u32.to_biguint(),
//                 2u32.to_biguint(),
//                 1u32.to_biguint(),
//                 1u32.to_biguint(),
//             ],
//         );

//         result.verilog_code();
//     }

//     #[test]
//     fn inout_codegens_as_inout() {
//         let input = spade_mir::Entity {
//             name: spade_mir::unit_name::IntoUnitName::_test_into_unit_name("test"),
//             inline: false,
//             inputs: vec![spade_mir::MirInput {
//                 name: "a".to_string(),
//                 val_name: ValueName::_test_named(0, "a".to_string()).nowhere(),
//                 ty: Type::InOut(Box::new(Type::Bool)),
//                 no_mangle: Some(().nowhere()),
//             }],
//             output: ValueName::Expr(ExprID(0)).nowhere(),
//             output_type: Type::unit(),
//             statements: vec![],
//             verilog_attr_groups: vec![],
//         };

//         let expected = indoc!(
//             r#"

//             module test (
//                     inout a
//                 );
//                 `COCOTB_CODE( test )
//             endmodule"#
//         );

//         assert_same_code!(
//             &entity_code(
//                 &prepare_codegen(input.clone()),
//                 &mut InstanceMap::new(),
//                 &None
//             )
//             .0
//             .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn verilog_attrs_codegen_on_entity_declaration() {
//         let input = spade_mir::Entity {
//             name: spade_mir::unit_name::IntoUnitName::_test_into_unit_name("test"),
//             inputs: vec![spade_mir::MirInput {
//                 name: "a".to_string(),
//                 val_name: ValueName::_test_named(0, "a".to_string()).nowhere(),
//                 ty: Type::Bool,
//                 no_mangle: Some(().nowhere()),
//             }],
//             output: ValueName::Expr(ExprID(0)).nowhere(),
//             output_type: Type::unit(),
//             statements: vec![],
//             verilog_attr_groups: vec![
//                 vec![("single".into(), None)],
//                 vec![
//                     ("standalone".into(), None),
//                     ("key".into(), Some("val".into())),
//                 ],
//             ],
//             inline: false,
//         };

//         let expected = indoc!(
//             r#"
//             (* single *)
//             (* standalone, key = "val" *)
//             module test (
//                     input a
//                 );
//                 `COCOTB_CODE( test )
//             endmodule"#
//         );

//         assert_same_code!(
//             &entity_code(
//                 &prepare_codegen(input.clone()),
//                 &mut InstanceMap::new(),
//                 &None
//             )
//             .0
//             .to_string(),
//             expected
//         );
//     }

//     #[test]
//     fn verilog_attrs_codegen_on_entity_instantiation() {
//         let input = spade_mir::Entity {
//             name: spade_mir::unit_name::IntoUnitName::_test_into_unit_name("test"),
//             inputs: vec![spade_mir::MirInput {
//                 name: "a".to_string(),
//                 val_name: ValueName::_test_named(0, "a".to_string()).nowhere(),
//                 ty: Type::Bool,
//                 no_mangle: Some(().nowhere()),
//             }],
//             output: ValueName::Expr(ExprID(0)).nowhere(),
//             output_type: Type::unit(),
//             statements: vec![
//                 spade_mir::Statement::Binding(spade_mir::Binding {
//                     name: ValueName::_test_named(0, "x".to_string()).nowhere(),
//                     operator: spade_mir::Operator::Instance {
//                         name: UnitName::_test_from_strs(&["foo"]),
//                         params: vec![],
//                         argument_names: vec![],
//                         loc: None,
//                         verilog_attr_groups: vec![
//                             vec![("single".into(), None)],
//                             vec![
//                                 ("standalone".into(), None),
//                                 ("key".into(), Some("val".into())),
//                             ],
//                         ],
//                     },
//                     operands: vec![],
//                     ty: Type::unit(),
//                     loc: None,
//                 })
//                 .nowhere(),
//             ],
//             verilog_attr_groups: vec![],
//             inline: false,
//         };

//         let expected = indoc!(
//             r#"

//             module test (
//                     input a
//                 );
//                 `COCOTB_CODE( test )
//                 (* single *)
//                 (* standalone, key = "val" *)
//                 \foo  \foo_0 ();
//             endmodule"#
//         );

//         assert_same_code!(
//             &entity_code(
//                 &prepare_codegen(input.clone()),
//                 &mut InstanceMap::new(),
//                 &None
//             )
//             .0
//             .to_string(),
//             expected
//         );
//     }
// }
