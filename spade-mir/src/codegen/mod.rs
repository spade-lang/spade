use crate::{
    aliasing::flatten_aliases,
    assertion_codegen::AssertedExpression,
    enum_util,
    type_list::TypeList,
    verilog::{self, assign, logic, size_spec},
    Binding, ConstantValue, Entity, Operator, Statement, ValueName,
};
use codespan_reporting::term::termcolor;
use itertools::Itertools;
use nesty::{code, Code};
use spade_common::{
    error_reporting::{CodeBundle, CompilationError},
    location_info::Loc,
};

pub mod util;

pub use util::{escape_path, mangle_entity, mangle_input, mangle_output, TupleIndex};

/// Produces a source location verilog attribute if the loc and code bundle are defined
fn source_attribute(loc: &Option<Loc<()>>, code: &Option<CodeBundle>) -> Option<String> {
    match (loc, code) {
        (Some(l), Some(c)) => Some(format!(r#"(* src = "{}" *)"#, c.source_loc(&l))),
        _ => None,
    }
}

fn statement_declaration(statement: &Statement, code: &Option<CodeBundle>) -> Code {
    match statement {
        Statement::Binding(binding) => {
            let name = binding.name.var_name();

            let forward_declaration = if binding.ty.size() != 0 {
                vec![match &binding.ty {
                    crate::types::Type::Memory { inner, length } => {
                        let inner_w = inner.size();
                        if inner_w > 1 {
                            format!("logic[{inner_w}-1:0] {name}[{length}-1:0];")
                        } else {
                            logic(&name, binding.ty.size())
                        }
                    }
                    _ => logic(&name, binding.ty.size()),
                }]
            } else {
                vec![]
            };

            let backward_declaration = if binding.ty.backward_size() != 0 {
                vec![logic(
                    &binding.name.backward_var_name(),
                    binding.ty.backward_size(),
                )]
            } else {
                vec![]
            };

            let ops = &binding
                .operands
                .iter()
                .map(ValueName::var_name)
                .collect::<Vec<_>>();

            // Aliases of memories have to be treated differently because we can't
            // assign them
            let assignment = match &binding.operator {
                Operator::Alias => match binding.ty {
                    crate::types::Type::Memory { .. } => {
                        vec![format!("`define {} {}", name, ops[0])]
                    }
                    _ => vec![],
                },
                _ => vec![],
            };

            code! {
                [0] source_attribute(&binding.loc, code);
                [0] &forward_declaration;
                [0] &backward_declaration;
                [0] &assignment;
            }
        }
        Statement::Register(reg) => {
            if reg.ty.backward_size() != 0 {
                panic!("Attempting to put value with a backward_size != 0 in a register")
            }
            let name = reg.name.var_name();
            let declaration = verilog::reg(&name, reg.ty.size());
            code! {
                [0] source_attribute(&reg.loc, code);
                [0] &declaration;
            }
        }
        Statement::Constant(id, ty, _) => {
            let name = ValueName::Expr(*id).var_name();
            let declaration = logic(&name, ty.size());

            code! {
                [0] &declaration;
            }
        }
        Statement::Assert(_) => {
            code! {}
        }
        Statement::Set { .. } => {
            code! {}
        }
    }
}

fn compute_tuple_index(idx: u64, sizes: &[u64]) -> TupleIndex {
    // Compute the start index of the element we're looking for
    let mut start_bit = 0;
    for i in 0..idx {
        start_bit += sizes[i as usize];
    }

    let target_width = sizes[idx as usize];
    let end_bit = start_bit + target_width;

    let total_width: u64 = sizes.iter().sum();

    // Check if this is a single bit, if so, index using just it
    if target_width == 1 {
        TupleIndex::Single(total_width - start_bit - 1)
    } else {
        TupleIndex::Range {
            left: total_width - start_bit - 1,
            right: total_width - end_bit,
        }
    }
}

fn forward_expression_code(binding: &Binding, types: &TypeList, ops: &[ValueName]) -> String {
    let self_type = &binding.ty;
    let op_names = ops.iter().map(|op| op.var_name()).collect::<Vec<_>>();

    let name = binding.name.var_name();

    macro_rules! binop {
        ($verilog:expr) => {{
            assert!(
                binding.operands.len() == 2,
                "expected 2 operands to binary operator"
            );
            format!("{} {} {}", op_names[0], $verilog, op_names[1])
        }};
    }

    macro_rules! signed_binop {
        ($verilog:expr) => {{
            assert!(
                binding.operands.len() == 2,
                "expected 2 operands to binary operator"
            );
            format!(
                "$signed({}) {} $signed({})",
                op_names[0], $verilog, op_names[1]
            )
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

    match &binding.operator {
        Operator::Add => signed_binop!("+"),
        Operator::Sub => signed_binop!("-"),
        Operator::Mul => signed_binop!("*"),
        Operator::Eq => binop!("=="),
        Operator::Gt => signed_binop!(">"),
        Operator::Lt => signed_binop!("<"),
        Operator::Ge => signed_binop!(">="),
        Operator::Le => signed_binop!("<="),
        Operator::LeftShift => binop!("<<"),
        Operator::RightShift => binop!(">>"),
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
        Operator::Truncate => {
            format!("{}[{}:0]", op_names[0], binding.ty.size() - 1)
        }
        Operator::Concat => {
            format!(
                "{{{}}}",
                op_names.iter().map(|op| format!("{op}")).join(", ")
            )
        }
        Operator::SignExtend {
            extra_bits,
            operand_size,
        } => match extra_bits {
            0 => format!("{}", op_names[0]),
            1 => format!("{{{}[{}], {}}}", op_names[0], operand_size - 1, op_names[0]),
            2.. => format!(
                "#[#[ {extra_bits} #[ {op}[{last_index}] #]#], {op}#]",
                op = op_names[0],
                last_index = operand_size - 1,
            )
            // For readability with the huge amount of braces that both
            // rust and verilog want here, we'll insert them at the end
            // like this
            .replace("#[", "{")
            .replace("#]", "}"),
        },
        Operator::ZeroExtend { extra_bits } => match extra_bits {
            0 => format!("{}", op_names[0]),
            1.. => format!("{{{}'b0, {}}}", extra_bits, op_names[0]),
        },
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

            code! (
                [0] "always_comb begin";
                [1]     format!("priority casez ({{{}}})", conditions.join(", "));
                [2]         cases;
                [2]         format!("{num_branches}'b?: {name} = 'x;");
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
        Operator::IndexTuple(idx, ref types) => {
            let idx =
                compute_tuple_index(*idx, &types.iter().map(|t| t.size()).collect::<Vec<_>>());
            format!("{}{}", op_names[0], idx.verilog_code())
        }
        Operator::ConstructArray { .. } => {
            // NOTE: Reversing because we declare the array as logic[SIZE:0] and
            // we want the [x*width+:width] indexing to work
            format!(
                "{{{}}}",
                op_names
                    .iter()
                    .cloned()
                    .rev()
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        }
        Operator::IndexArray => {
            let member_size = self_type.size();
            if member_size == 1 {
                format!("{}[{}]", op_names[0], op_names[1])
            } else {
                let end_index = format!("{} * {}", op_names[1], member_size);
                let offset = member_size;

                // Strange indexing explained here https://stackoverflow.com/questions/18067571/indexing-vectors-and-arrays-with#18068296
                format!("{}[{}+:{}]", op_names[0], end_index, offset)
            }
        }
        Operator::IndexMemory => {
            format!("{}[{}]", op_names[0], op_names[1])
        }
        Operator::DeclClockedMemory {
            write_ports,
            addr_w,
            inner_w,
            elems: _,
        } => {
            let full_port_width = 1 + addr_w + inner_w;
            let update_blocks = (0..*write_ports)
                .map(|port| {
                    let we_index = full_port_width * (port + 1) - 1;

                    let addr_start = full_port_width * port + inner_w;
                    let addr = if *addr_w == 1 {
                        format!("{}[{}]", op_names[1], addr_start)
                    } else {
                        format!(
                            "{}[{}:{}]",
                            op_names[1],
                            addr_start + addr_w - 1,
                            addr_start
                        )
                    };

                    let write_value_start = port * full_port_width;
                    let (write_index, write_value) = if *inner_w == 1 {
                        (
                            format!("{}[{addr}]", name),
                            format!("{}[{write_value_start}]", op_names[1]),
                        )
                    } else {
                        (
                            format!("{}[{addr}]", name),
                            format!(
                                "{}[{end}:{write_value_start}]",
                                op_names[1],
                                end = write_value_start + inner_w - 1
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
                [0] format!("always @(posedge {clk}) begin", clk = op_names[0]);
                [1]     update_blocks;
                [0] "end";
            }
            .to_string()
        }
        Operator::ConstructEnum {
            variant,
            variant_count,
        } => {
            let tag_size = enum_util::tag_size(*variant_count);

            // Compute the amount of undefined bits to put at the end of the literal.
            // First compute the size of this variant
            let variant_member_size = match &binding.ty {
                crate::types::Type::Enum(options) => {
                    options[*variant].iter().map(|t| t.size()).sum::<u64>()
                }
                _ => panic!("Attempted enum construction of non-enum"),
            };

            let padding_size = binding.ty.size() as usize - tag_size - variant_member_size as usize;

            let padding_text = if padding_size != 0 {
                format!(", {}'bX", padding_size)
            } else {
                String::new()
            };

            let ops_text = if op_names.is_empty() {
                String::new()
            } else {
                format!(", {}", op_names.join(", "))
            };

            format!("{{{}'d{}{}{}}}", tag_size, variant, ops_text, padding_text)
        }
        Operator::IsEnumVariant { variant, enum_type } => {
            let tag_size = enum_util::tag_size(enum_type.assume_enum().len());
            let total_size = enum_type.size();

            let tag_end = total_size - 1;
            let tag_start = total_size - tag_size as u64;

            if tag_end == tag_start {
                format!("{}[{}] == {}'d{}", op_names[0], tag_end, tag_size, variant)
            } else {
                format!(
                    "{}[{}:{}] == {}'d{}",
                    op_names[0], tag_end, tag_start, tag_size, variant
                )
            }
        }
        Operator::EnumMember {
            variant,
            member_index,
            enum_type,
        } => {
            let variant_list = enum_type.assume_enum();
            let tag_size = enum_util::tag_size(variant_list.len());
            let full_size = enum_type.size();

            let member_start = (tag_size as u64)
                + variant_list[*variant][0..*member_index]
                    .iter()
                    .map(|t| t.size() as u64)
                    .sum::<u64>();

            let member_end = member_start + variant_list[*variant][*member_index].size();

            format!(
                "{}[{}:{}]",
                op_names[0],
                full_size - member_start - 1,
                full_size - member_end
            )
        }
        Operator::ReadPort => {
            format!("{}", ops[0].backward_var_name())
        }
        Operator::ConstructTuple => {
            let mut members = ops
                .iter()
                .filter(|op| types[op].size() != 0)
                .map(|op| op.var_name());
            // To make index calculations easier, we will store tuples in "inverse order".
            // i.e. the left-most element is stored to the right in the bit vector.
            format!("{{{}}}", members.join(", "))
        }
        Operator::Instance(_, _) => {
            // NOTE: dummy. Set in the next match statement
            format!("")
        }
        Operator::Alias => {
            // NOTE Dummy. Set in the next match statement
            format!("") //format!("{}", ops[0])
        }
        Operator::Nop => {
            format!("")
        }
    }
}

fn backward_expression_code(binding: &Binding, types: &TypeList, ops: &[ValueName]) -> String {
    let self_type = &binding.ty;
    let op_names = ops
        .iter()
        .map(ValueName::backward_var_name)
        .collect::<Vec<_>>();
    match &binding.operator {
        Operator::Add
        | Operator::Sub
        | Operator::Mul
        | Operator::Eq
        | Operator::Gt
        | Operator::Lt
        | Operator::Ge
        | Operator::Le
        | Operator::LeftShift
        | Operator::RightShift
        | Operator::LogicalAnd
        | Operator::LogicalOr
        | Operator::LogicalXor
        | Operator::LogicalNot
        | Operator::BitwiseAnd
        | Operator::BitwiseOr
        | Operator::BitwiseXor
        | Operator::USub
        | Operator::Not
        | Operator::BitwiseNot
        | Operator::DivPow2
        | Operator::SignExtend { .. }
        | Operator::ZeroExtend { .. }
        | Operator::Concat
        | Operator::DeclClockedMemory { .. }
        | Operator::ConstructEnum { .. }
        | Operator::IsEnumVariant { .. }
        | Operator::EnumMember { .. }
        | Operator::IndexMemory
        | Operator::Select
        | Operator::Match
        | Operator::ReadPort
        | Operator::Truncate => panic!(
            "{} can not be used on types with backward size",
            binding.operator
        ),
        Operator::ConstructArray => {
            // NOTE: Reversing because we declare the array as logic[SIZE:0] and
            // we want the [x*width+:width] indexing to work
            format!(
                "{{{}}}",
                op_names
                    .iter()
                    .cloned()
                    .rev()
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        }
        Operator::IndexArray => {
            let member_size = self_type.backward_size();
            if member_size == 1 {
                format!("{}[{}]", op_names[0], op_names[1])
            } else {
                let end_index = format!("{} * {}", op_names[1], member_size);
                let offset = member_size;

                // Strange indexing explained here https://stackoverflow.com/questions/18067571/indexing-vectors-and-arrays-with#18068296
                format!("{}[{}+:{}]", op_names[0], end_index, offset)
            }
        }
        Operator::ConstructTuple => {
            let mut members = ops
                .iter()
                .filter(|op| types[op].backward_size() != 0)
                .map(|op| op.backward_var_name());
            format!("{{{}}}", members.join(", "))
        }
        Operator::IndexTuple(index, inner_types) => {
            assert_eq!(&inner_types[*index as usize], self_type);
            let index = compute_tuple_index(
                *index,
                &inner_types
                    .iter()
                    .map(|t| t.backward_size())
                    .collect::<Vec<_>>(),
            );
            format!("{}{}", op_names[0], index.verilog_code())
        }
        Operator::Instance(_, _) => format!(""),
        Operator::Alias => {
            // NOTE: Set in statement_code
            format!("")
        }
        Operator::Nop => {
            format!("")
        }
    }
}

fn statement_code(
    statement: &Statement,
    types: &TypeList,
    source_code: &Option<CodeBundle>,
) -> Code {
    match statement {
        Statement::Binding(binding) => {
            let name = binding.name.var_name();
            let back_name = binding.name.backward_var_name();

            let ops = &binding
                .operands
                .iter()
                .map(ValueName::var_name)
                .collect::<Vec<_>>();

            let back_ops = &binding
                .operands
                .iter()
                .map(ValueName::backward_var_name)
                .collect::<Vec<_>>();

            let forward_expression = if binding.ty.size() != 0 {
                Some(forward_expression_code(binding, types, &binding.operands))
            } else {
                None
            };
            let backward_expression = if binding.ty.backward_size() != 0 {
                Some(backward_expression_code(binding, types, &binding.operands))
            } else {
                None
            };

            // Unless this is a special operator, we just use assign value = expression
            let assignment = match &binding.operator {
                Operator::Instance(module_name, loc) => {
                    // Input args
                    let mut args = binding
                        .operands
                        .iter()
                        .flat_map(|port| {
                            let ty = &types[port];

                            // Push the input and output into the result if they
                            // should be bound
                            let mut result = vec![];
                            if ty.size() != 0 {
                                result.push(port.var_name())
                            }
                            if ty.backward_size() != 0 {
                                result.push(port.backward_var_name())
                            }
                            result
                        })
                        .join(", ");

                    if !args.is_empty() {
                        args += ", "
                    }

                    let out_size = binding.ty.size();
                    let back_size = binding.ty.backward_size();
                    let io_comma = if out_size != 0 && back_size != 0 {
                        ", "
                    }
                    else {
                        ""
                    };
                    if out_size != 0 {
                        args += &name;
                    }
                    args += io_comma;
                    if back_size != 0 {
                        args += &back_name;
                    }

                    let module_name = escape_path(module_name.to_string());

                    let instance_name = format!("{}_{}", module_name, name);

                    code!{
                        [0] source_attribute(loc, source_code);
                        [0] format!(
                            "{} {}({});",
                            mangle_entity(&module_name),
                            instance_name,
                            args
                        )
                    }.to_string()
                }
                Operator::Alias => match binding.ty {
                    crate::types::Type::Memory { .. } => {
                        // Aliasing of memories happens at definition
                        "".to_string()
                    }
                    _ => code! {
                        [0] forward_expression.map(|_| format!("assign {} = {};", name, ops[0]));
                        [0] backward_expression.map(|_| format!("assign {} = {};", back_ops[0], back_name));
                    }.to_string()
                },
                Operator::Match => format!("{}", forward_expression.unwrap()),
                Operator::DivPow2 => format!("{}", forward_expression.unwrap()),
                Operator::Nop => format!(""),
                Operator::DeclClockedMemory { .. } => format!("{}", forward_expression.unwrap()),
                _ => code! {
                    [0] forward_expression.map(|f| format!("assign {} = {};", name, f));
                    [0] backward_expression.map(|b| format!("assign {} = {};", b, back_name));
                }
                .to_string(),
            };

            code! {
                [0] &assignment
            }
        }
        Statement::Register(reg) => {
            if let Some((rst_trig, rst_val)) = &reg.reset {
                let name = reg.name.var_name();

                code! {
                    [0] &format!("always @(posedge {}, posedge {}) begin", reg.clock.var_name(), rst_trig.var_name());
                    [1]     &format!("if ({}) begin", rst_trig.var_name());
                    [2]         &format!("{} <= {};", name, rst_val.var_name());
                    [1]     &"end";
                    [1]     &"else begin";
                    [2]         &format!("{} <= {};", name, reg.value.var_name());
                    [1]     &"end";
                    [0] &"end"
                }
            } else {
                let name = reg.name.var_name();

                code! {
                    [0] &format!("always @(posedge {}) begin", reg.clock.var_name());
                    [1]     &format!("{} <= {};", name, reg.value.var_name());
                    [0] &"end"
                }
            }
        }
        Statement::Constant(id, _, value) => {
            let name = ValueName::Expr(*id).var_name();

            let expression = match value {
                ConstantValue::Int(val) => format!("{}", val),
                ConstantValue::Bool(val) => format!("{}", if *val { 1 } else { 0 }),
            };

            let assignment = format!("assign {} = {};", name, expression);

            code! {
                [0] &assignment
            }
        }
        Statement::Assert(val) => {
            let mut msg_buf = termcolor::Buffer::ansi();

            // NOTE: Unwrap is semi-safe. Non-tests are expected to pass an actual
            // source code
            AssertedExpression(val.clone()).report(&mut msg_buf, &source_code.as_ref().unwrap());

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
                    [1] "else begin";
                        [2] msg;
                        [2] r#"$error("Assertion failed");"#;
                        [2] r#"$fatal(1);"#;
                    [1] "end";
                [0] "end";
                [0] format!("`endif")
            }
        }
        Statement::Set { target, value } => {
            let assignment = format!(
                "assign {} = {};",
                target.backward_var_name(),
                value.var_name()
            );

            code! {
                [0] assignment
            }
        }
    }
}

#[cfg(test)]
fn statement_code_and_declaration(
    statement: &Statement,
    types: &TypeList,
    source_code: &CodeBundle,
) -> Code {
    code! {
        [0] statement_declaration(statement, &Some(source_code.clone()));
        [0] statement_code(statement, types, &Some(source_code.clone()));
    }
}

/// Source code is used for two things: mapping expressions back to their original source code
/// location, and for assertions. If source_code is None, no (* src = *) attributes will be
/// emitted, however, assertions will cause a panic. This is convenient for tests where specifying
/// source location is annoying to specify.
/// In actual compilation this should be Some
pub fn entity_code(entity: &mut Entity, source_code: &Option<CodeBundle>) -> Code {
    flatten_aliases(entity);

    let types = &TypeList::from_entity(&entity);

    let entity_name = mangle_entity(&escape_path(entity.name.clone()));

    let inputs: Vec<_> = entity
        .inputs
        .iter()
        .map(|(name, value_name, ty)| (name, value_name, ty))
        .collect();

    let inputs = inputs.iter().map(|(name, value_name, ty)| {
        let size = ty.size();
        let (input_head, input_code) = if size != 0 {
            let name = mangle_input(name);
            (
                format!("input{} {},", size_spec(size), name),
                code! {
                    [0] &logic(&value_name.var_name(), size);
                    [0] &assign(&value_name.var_name(), &name)
                },
            )
        } else {
            (String::new(), code! {})
        };

        let backward_size = ty.backward_size();
        let (output_head, output_code) = if backward_size != 0 {
            let name = mangle_output(name);
            (
                format!("output{} {},", size_spec(backward_size), name),
                code! {
                    [0] &logic(&value_name.backward_var_name(), backward_size);
                    [0] &assign(&name, &value_name.backward_var_name())
                },
            )
        } else {
            (String::new(), code! {})
        };

        let spacing = if !input_head.is_empty() && !output_head.is_empty() {
            " "
        } else {
            ""
        };
        (
            format!("{input_head}{spacing}{output_head}"),
            code! {
                [0] input_code;
                [0] output_code;
            },
        )
    });

    let (inputs, input_assignments): (Vec<_>, Vec<_>) = inputs.unzip();

    let back_port_size = entity.output_type.backward_size();
    let (back_port_definition, back_port_assignment) = if back_port_size != 0 {
        let def = code! {
            [0] format!(
                "input{} input__",
                size_spec(entity.output_type.backward_size())
            );
        };
        let assignment = code! {
            [0] assign(&entity.output.backward_var_name(), "input__")
        };
        (Some(def), Some(assignment))
    } else {
        (None, None)
    };

    let output_size = entity.output_type.size();
    let (output_definition, output_assignment) = if output_size != 0 {
        let comma = if back_port_definition.is_some() {
            ","
        } else {
            ""
        };
        let def = code! {
            [0] format!("output{} output__{comma}", size_spec(output_size))
        };
        let assignment = code! {[0] assign("output__", &entity.output.var_name())};
        (Some(def), Some(assignment))
    } else {
        (None, None)
    };

    let mut body = Code::new();

    for stmt in &entity.statements {
        body.join(&statement_declaration(stmt, source_code))
    }
    for stmt in &entity.statements {
        body.join(&statement_code(stmt, types, source_code))
    }

    code! {
        [0] &format!("module {} (", entity_name);
                [2] &inputs;
                [2] &output_definition;
                [2] &back_port_definition;
            [1] &");";
            [1] "`ifdef COCOTB_SIM";
            [1] "string __top_module;";
            [1] "string __vcd_file;";
            [1] "initial begin";
            [2]   format!(r#"if ($value$plusargs("TOP_MODULE=%s", __top_module) && __top_module == "{entity_name}" && $value$plusargs("VCD_FILENAME=%s", __vcd_file)) begin"#);
            [3]     format!("$dumpfile (__vcd_file);");
            [3]     format!("$dumpvars (0, {entity_name});");
            [2]   "end";
            [2]  "#1;";
            [1] "end";
            [1] "`endif";
            [1] &input_assignments;
            [1] &body;
            [1] &output_assignment;
            [1] &back_port_assignment;
        [0] &"endmodule"
    }
}

#[macro_export]
macro_rules! assert_same_code {
    ($got:expr, $expected:expr) => {
        if $got != $expected {
            println!("{}:\n{}", "got".red(), $got);
            println!("{}", "==============================================".red());
            println!("{}:\n{}", "expected".green(), $expected);
            println!(
                "{}",
                "==============================================".green()
            );
            println!("{}", prettydiff::diff_chars($got, $expected));
            println!(
                "{}",
                "==============================================".yellow()
            );
            panic!("Code mismatch")
        }
    };
}

#[cfg(test)]
mod tests {
    use super::*;
    use colored::Colorize;

    use crate as spade_mir;
    use crate::{entity, statement, types::Type};

    use indoc::indoc;

    #[test]
    fn size_1_wires_have_no_size_spec() {
        let binding = statement!(e(0); Type::Bool; Add; e(1), e(2));

        let expected = indoc!(
            r#"
            logic _e_0;
            assign _e_0 = $signed(_e_1) + $signed(_e_2);"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &binding,
                &TypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn binding_code_works() {
        let binding = statement!(e(0); Type::Int(5); Add; e(1), e(2));

        let expected = indoc!(
            r#"
            logic[4:0] _e_0;
            assign _e_0 = $signed(_e_1) + $signed(_e_2);"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &binding,
                &TypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn registers_without_reset_work() {
        let reg = statement!(reg n(0, "r"); Type::Int(7); clock (e(0)); e(1));

        let expected = indoc!(
            r#"
                reg[6:0] r_n0;
                always @(posedge _e_0) begin
                    r_n0 <= _e_1;
                end"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &reg,
                &TypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn registers_with_reset_work() {
        let reg = statement!(reg n(0, "r"); Type::Int(7); clock (e(0)); reset (e(2), e(3)); e(1));

        let expected = indoc!(
            r#"
                reg[6:0] r_n0;
                always @(posedge _e_0, posedge _e_2) begin
                    if (_e_2) begin
                        r_n0 <= _e_3;
                    end
                    else begin
                        r_n0 <= _e_1;
                    end
                end"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &reg,
                &TypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn entity_codegen_works() {
        let input = entity!("pong"; ("op", n(0, "op"), Type::Int(6)) -> Type::Int(6); {
            (e(0); Type::Int(6); Add; n(0, "op"), e(1))
        } => e(0));

        let expected = indoc!(
            r#"
            module e_pong (
                    input[5:0] op_i,
                    output[5:0] output__
                );
                `ifdef COCOTB_SIM
                string __top_module;
                string __vcd_file;
                initial begin
                    if ($value$plusargs("TOP_MODULE=%s", __top_module) && __top_module == "e_pong" && $value$plusargs("VCD_FILENAME=%s", __vcd_file)) begin
                        $dumpfile (__vcd_file);
                        $dumpvars (0, e_pong);
                    end
                    #1;
                end
                `endif
                logic[5:0] op_n0;
                assign op_n0 = op_i;
                logic[5:0] _e_0;
                assign _e_0 = $signed(op_n0) + $signed(_e_1);
                assign output__ = _e_0;
            endmodule"#
        );

        assert_same_code!(
            &entity_code(&mut input.clone(), &None).to_string(),
            expected
        );
    }

    #[test]
    fn pure_backward_input_produces_output_port() {
        let ty = Type::Backward(Box::new(Type::Int(3)));
        let input = entity!("test"; ("a", n(0, "a"), ty) -> Type::Int(6); {
            (const 0; Type::Int(6); crate::ConstantValue::Int(3))
        } => e(0));

        let expected = indoc!(
            r#"module e_test (
                    output[2:0] a_o,
                    output[5:0] output__
                );
                `ifdef COCOTB_SIM
                string __top_module;
                string __vcd_file;
                initial begin
                    if ($value$plusargs("TOP_MODULE=%s", __top_module) && __top_module == "e_test" && $value$plusargs("VCD_FILENAME=%s", __vcd_file)) begin
                        $dumpfile (__vcd_file);
                        $dumpvars (0, e_test);
                    end
                    #1;
                end
                `endif
                logic[2:0] a_n0_o;
                assign a_o = a_n0_o;
                logic[5:0] _e_0;
                assign _e_0 = 3;
                assign output__ = _e_0;
            endmodule"#
        );

        assert_same_code!(
            &entity_code(&mut input.clone(), &None).to_string(),
            expected
        );
    }

    #[test]
    fn mixed_backward_input_works() {
        let ty = Type::Tuple(vec![Type::Int(4), Type::Backward(Box::new(Type::Int(3)))]);
        let input = entity!("test"; ("a", n(0, "a"), ty) -> Type::Int(6); {
            (const 0; Type::Int(6); crate::ConstantValue::Int(3))
        } => e(0));

        let expected = indoc!(
            r#"module e_test (
                    input[3:0] a_i, output[2:0] a_o,
                    output[5:0] output__
                );
                `ifdef COCOTB_SIM
                string __top_module;
                string __vcd_file;
                initial begin
                    if ($value$plusargs("TOP_MODULE=%s", __top_module) && __top_module == "e_test" && $value$plusargs("VCD_FILENAME=%s", __vcd_file)) begin
                        $dumpfile (__vcd_file);
                        $dumpvars (0, e_test);
                    end
                    #1;
                end
                `endif
                logic[3:0] a_n0;
                assign a_n0 = a_i;
                logic[2:0] a_n0_o;
                assign a_o = a_n0_o;
                logic[5:0] _e_0;
                assign _e_0 = 3;
                assign output__ = _e_0;
            endmodule"#
        );

        assert_same_code!(
            &entity_code(&mut input.clone(), &None).to_string(),
            expected
        );
    }

    #[test]
    fn mixed_backward_output_works() {
        let ty = Type::Tuple(vec![Type::Int(4), Type::Backward(Box::new(Type::Int(3)))]);
        let input = entity!("test"; () -> ty; {
        } => e(0));

        let expected = indoc!(
            r#"module e_test (
                    output[3:0] output__,
                    input[2:0] input__
                );
                `ifdef COCOTB_SIM
                string __top_module;
                string __vcd_file;
                initial begin
                    if ($value$plusargs("TOP_MODULE=%s", __top_module) && __top_module == "e_test" && $value$plusargs("VCD_FILENAME=%s", __vcd_file)) begin
                        $dumpfile (__vcd_file);
                        $dumpvars (0, e_test);
                    end
                    #1;
                end
                `endif
                assign output__ = _e_0;
                assign _e_0_o = input__;
            endmodule"#
        );

        assert_same_code!(
            &entity_code(&mut input.clone(), &None).to_string(),
            expected
        );
    }

    #[test]
    fn constant_codegen_works() {
        let input = statement!(const 0; Type::Int(10); crate::ConstantValue::Int(6));

        let expected = indoc!(
            r#"
            logic[9:0] _e_0;
            assign _e_0 = 6;"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &input,
                &TypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        )
    }

    #[test]
    fn pipeline_with_stage_references_codegens_correctly() {
        let input = entity!("pl"; (
                "clk", n(3, "clk"), Type::Bool,
            ) -> Type::Int(16); {
                (reg n(10, "x__s1"); Type::Int(16); clock(n(3, "clk")); n(0, "x_"));
                // Stage 0
                (e(0); Type::Int(16); Instance(("A".to_string(), None)););
                (n(0, "x_"); Type::Int(16); Alias; e(0));
                // Stage 1
                (n(1, "x"); Type::Int(16); Alias; n(0, "x_"));
            } => n(1, "x")
        );

        // This test removes a lot of variables through alias resolution
        let expected = indoc!(
            r#"
            module e_pl (
                    input clk_i,
                    output[15:0] output__
                );
                `ifdef COCOTB_SIM
                string __top_module;
                string __vcd_file;
                initial begin
                    if ($value$plusargs("TOP_MODULE=%s", __top_module) && __top_module == "e_pl" && $value$plusargs("VCD_FILENAME=%s", __vcd_file)) begin
                        $dumpfile (__vcd_file);
                        $dumpvars (0, e_pl);
                    end
                    #1;
                end
                `endif
                logic clk_n3;
                assign clk_n3 = clk_i;
                reg[15:0] x__s1_n10;
                logic[15:0] x_n1;
                always @(posedge clk_n3) begin
                    x__s1_n10 <= x_n1;
                end
                e_A A_x_n1(x_n1);
                assign output__ = x_n1;
            endmodule"#
        );

        assert_same_code!(
            &entity_code(&mut input.clone(), &None).to_string(),
            expected
        );
    }
}

#[cfg(test)]
mod backward_expression_tests {
    use super::*;
    use colored::Colorize;

    use crate as spade_mir;
    use crate::{statement, types::Type};

    use indoc::indoc;

    #[test]
    fn backward_alias_works() {
        let ty = Type::Backward(Box::new(Type::Int(8)));
        let stmt = statement!(e(0); ty; Alias; e(1));

        let expected = indoc! {
            r#"
            logic[7:0] _e_0_o;
            assign _e_1_o = _e_0_o;"#
        };

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &TypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn backward_index_tuple_works() {
        let tuple_members = vec![Type::backward(Type::Int(8)), Type::backward(Type::Int(4))];
        let ty = Type::backward(Type::Int(4));
        let stmt = statement!(e(0); ty; IndexTuple((1, tuple_members)); e(1));

        let expected = indoc! {
            r#"
            logic[3:0] _e_0_o;
            assign _e_1_o[3:0] = _e_0_o;"#
        };

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &TypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn construct_tuple_works() {
        let tuple_members = vec![Type::backward(Type::Int(8)), Type::backward(Type::Int(4))];
        let ty = Type::Tuple(tuple_members);
        let stmt = statement!(e(0); ty; ConstructTuple; e(1), e(2));

        let type_list = TypeList::empty()
            .with(ValueName::Expr(1), Type::backward(Type::Int(8)))
            .with(ValueName::Expr(2), Type::backward(Type::Int(4)));

        let expected = indoc! {
            r#"
            logic[11:0] _e_0_o;
            assign {_e_1_o, _e_2_o} = _e_0_o;"#
        };

        assert_same_code!(
            &statement_code_and_declaration(&stmt, &type_list, &CodeBundle::new("".to_string()))
                .to_string(),
            expected
        );
    }

    #[test]
    fn construct_tuple_works_on_mixed_direction_types() {
        let tuple_members = vec![
            Type::backward(Type::Int(8)),
            Type::Tuple(vec![Type::backward(Type::Int(4)), Type::Int(4)]),
            Type::Int(3),
        ];
        let ty = Type::Tuple(tuple_members);
        let stmt = statement!(e(0); ty; ConstructTuple; e(1), e(2), e(3));

        let expected = indoc! {
            r#"
            logic[6:0] _e_0;
            logic[11:0] _e_0_o;
            assign _e_0 = {_e_2, _e_3};
            assign {_e_1_o, _e_2_o} = _e_0_o;"#
        };

        let type_list = TypeList::empty()
            .with(ValueName::Expr(1), Type::backward(Type::Int(8)))
            .with(
                ValueName::Expr(2),
                Type::Tuple(vec![Type::backward(Type::Int(4)), Type::Int(4)]),
            )
            .with(ValueName::Expr(3), Type::Int(3));

        assert_same_code!(
            &statement_code_and_declaration(&stmt, &type_list, &CodeBundle::new("".to_string()))
                .to_string(),
            expected
        );
    }

    #[test]
    fn construct_array_works() {
        let ty = Type::Array {
            inner: Box::new(Type::backward(Type::Int(5))),
            length: 3,
        };
        let stmt = statement!(e(0); ty; ConstructArray; e(1), e(2), e(3));

        let expected = indoc! {
            r#"
            logic[14:0] _e_0_o;
            assign {_e_3_o, _e_2_o, _e_1_o} = _e_0_o;"#
        };

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &TypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }
}

#[cfg(test)]
mod expression_tests {
    use super::*;
    use codespan::Span;
    use colored::Colorize;
    use spade_common::location_info::WithLocation;

    use crate::{self as spade_mir, value_name};
    use crate::{statement, types::Type};

    use indoc::{formatdoc, indoc};

    macro_rules! binop_test {
        ($name:ident, $ty:expr, $verilog_ty:expr, $op:ident, $verilog_op:expr) => {
            #[test]
            fn $name() {
                let stmt = statement!(e(0); $ty; $op; e(1), e(2));

                let expected = formatdoc!(
                    r#"
                    logic{} _e_0;
                    assign _e_0 = _e_1 {} _e_2;"#, $verilog_ty, $verilog_op
                );

                assert_same_code!(&statement_code_and_declaration(&stmt, &TypeList::empty(), &CodeBundle::new("".to_string())).to_string(), &expected)
            }
        }
    }

    macro_rules! signed_binop_test {
        ($name:ident, $ty:expr, $verilog_ty:expr, $op:ident, $verilog_op:expr) => {
            #[test]
            fn $name() {
                let stmt = statement!(e(0); $ty; $op; e(1), e(2));

                let expected = formatdoc!(
                    r#"
                    logic{} _e_0;
                    assign _e_0 = $signed(_e_1) {} $signed(_e_2);"#, $verilog_ty, $verilog_op
                );

                assert_same_code!(&statement_code_and_declaration(&stmt, &TypeList::empty(), &CodeBundle::new("".to_string())).to_string(), &expected)
            }
        }
    }

    macro_rules! unop_test {
        ($name:ident, $ty:expr, $verilog_ty:expr, $op:ident, $verilog_op:expr) => {
            #[test]
            fn $name() {
                let stmt = statement!(e(0); $ty; $op; e(1));

                let expected = formatdoc!(
                    r#"
                    logic{} _e_0;
                    assign _e_0 = {}_e_1;"#, $verilog_ty, $verilog_op
                );

                assert_same_code!(&statement_code_and_declaration(&stmt, &TypeList::empty(), &CodeBundle::new("".to_string())).to_string(), &expected)
            }
        }
    }

    signed_binop_test!(binop_add_works, Type::Int(2), "[1:0]", Add, "+");
    signed_binop_test!(binop_sub_works, Type::Int(2), "[1:0]", Sub, "-");
    signed_binop_test!(binop_mul_works, Type::Int(2), "[1:0]", Mul, "*");
    binop_test!(
        binop_left_shift_works,
        Type::Int(2),
        "[1:0]",
        LeftShift,
        "<<"
    );
    binop_test!(
        binop_right_shift_works,
        Type::Int(2),
        "[1:0]",
        RightShift,
        ">>"
    );
    binop_test!(binop_eq_works, Type::Bool, "", Eq, "==");
    signed_binop_test!(binop_gt_works, Type::Bool, "", Gt, ">");
    signed_binop_test!(binop_lt_works, Type::Bool, "", Lt, "<");
    signed_binop_test!(binop_ge_works, Type::Bool, "", Ge, ">=");
    signed_binop_test!(binop_le_works, Type::Bool, "", Le, "<=");
    binop_test!(binop_logical_and_works, Type::Bool, "", LogicalAnd, "&&");
    binop_test!(binop_logical_or_works, Type::Bool, "", LogicalOr, "||");
    binop_test!(bitwise_xor_works, Type::Int(32), "[31:0]", BitwiseXor, "^");
    // NOTE: The resulting verilog uses `^` on a 1 bit value
    binop_test!(logical_xor_works, Type::Bool, "", LogicalXor, "^");
    unop_test!(not_works, Type::Bool, "", Not, "!");
    unop_test!(usub_works, Type::Int(2), "[1:0]", USub, "-");

    #[test]
    fn select_operator_works() {
        let stmt = statement!(e(0); Type::Int(2); Select; e(1), e(2), e(3));

        let expected = indoc!(
            r#"
            logic[1:0] _e_0;
            assign _e_0 = _e_1 ? _e_2 : _e_3;"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &TypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn not_operator_works() {
        let stmt = statement!(e(0); Type::Bool; LogicalNot; e(1));

        let expected = indoc!(
            r#"
            logic _e_0;
            assign _e_0 = !_e_1;"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &TypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn match_operator_works() {
        let stmt = statement!(e(0); Type::Int(2); Match; e(1), e(2), e(3), e(4));

        let expected = indoc!(
            r#"
            logic[1:0] _e_0;
            always_comb begin
                priority casez ({_e_1, _e_3})
                    2'b1?: _e_0 = _e_2;
                    2'b01: _e_0 = _e_4;
                    2'b?: _e_0 = 'x;
                endcase
            end"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &TypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn boolean_constants_are_1_and_0() {
        let stmt = statement!(const 0; Type::Bool; ConstantValue::Bool(true));

        let expected = indoc!(
            r#"
            logic _e_0;
            assign _e_0 = 1;"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &TypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn tuple_assembly_operator_works() {
        let ty = Type::Tuple(vec![Type::Int(6), Type::Int(3)]);
        let stmt = statement!(e(0); ty; ConstructTuple; e(1), e(2));

        let expected = indoc!(
            r#"
            logic[8:0] _e_0;
            assign _e_0 = {_e_1, _e_2};"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &TypeList::empty()
                    .with(ValueName::Expr(1), Type::Int(6))
                    .with(ValueName::Expr(2), Type::Int(3)),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn enum_construction_operator_works() {
        let ty = Type::Enum(vec![vec![], vec![], vec![Type::Int(10), Type::Int(5)]]);
        let stmt = statement!(e(0); ty; ConstructEnum({variant: 2, variant_count: 3}); e(1), e(2));

        let expected = indoc!(
            r#"
            logic[16:0] _e_0;
            assign _e_0 = {2'd2, _e_1, _e_2};"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &TypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn is_enum_variant_operator_works() {
        let ty = Type::Enum(vec![vec![], vec![], vec![Type::Int(10), Type::Int(5)]]);
        let stmt = statement!(e(0); Type::Bool; IsEnumVariant({variant: 2, enum_type: ty}); e(1));

        let expected = indoc!(
            r#"
            logic _e_0;
            assign _e_0 = _e_1[16:15] == 2'd2;"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &TypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn is_enum_variant_operator_works_for_1_wide_tags() {
        let ty = Type::Enum(vec![vec![], vec![Type::Int(10), Type::Int(5)]]);
        let stmt = statement!(e(0); Type::Bool; IsEnumVariant({variant: 1, enum_type: ty}); e(1));

        let expected = indoc!(
            r#"
            logic _e_0;
            assign _e_0 = _e_1[15] == 1'd1;"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &TypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn enum_member_access_operator_works() {
        let ty = Type::Enum(vec![vec![], vec![], vec![Type::Int(10), Type::Int(5)]]);
        let stmt = statement!(e(0); Type::Int(5); EnumMember({variant: 2, member_index: 1, enum_type: ty}); e(1));

        let expected = indoc!(
            r#"
            logic[4:0] _e_0;
            assign _e_0 = _e_1[4:0];"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &TypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn enum_construction_inserts_padding_undef_where_needed() {
        let ty = Type::Enum(vec![
            vec![],
            vec![Type::Int(5)],
            vec![Type::Int(10), Type::Int(5)],
        ]);
        let stmt = statement!(e(0); ty; ConstructEnum({variant: 1, variant_count: 3}); e(1));

        let expected = indoc!(
            r#"
            logic[16:0] _e_0;
            assign _e_0 = {2'd1, _e_1, 10'bX};"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &TypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn tuple_indexing_works_for_first_value() {
        let ty = vec![Type::Int(6), Type::Int(3)];
        let stmt = statement!(e(0); Type::Int(6); IndexTuple((0, ty)); e(1));

        let expected = indoc!(
            r#"
            logic[5:0] _e_0;
            assign _e_0 = _e_1[8:3];"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &TypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }
    #[test]
    fn tuple_indexing_works() {
        let ty = vec![Type::Int(6), Type::Int(3)];
        let stmt = statement!(e(0); Type::Int(6); IndexTuple((1, ty)); e(1));

        let expected = indoc!(
            r#"
            logic[5:0] _e_0;
            assign _e_0 = _e_1[2:0];"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &TypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn tuple_indexing_works_for_bools() {
        let ty = vec![Type::Bool, Type::Int(3)];
        let stmt = statement!(e(0); Type::Bool; IndexTuple((0, ty)); e(1));

        let expected = indoc!(
            r#"
            logic _e_0;
            assign _e_0 = _e_1[3];"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &TypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn array_literals_work() {
        let ty = Type::Array {
            inner: Box::new(Type::Int(3)),
            length: 3,
        };
        let statement = statement!(e(0); ty; ConstructArray; e(1), e(2), e(3));

        let expected = indoc!(
            r#"
            logic[8:0] _e_0;
            assign _e_0 = {_e_3, _e_2, _e_1};"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &statement,
                &TypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn array_indexing_works() {
        let statement = statement!(e(0); Type::Int(3); IndexArray; e(1), e(2));

        let expected = indoc!(
            r#"
            logic[2:0] _e_0;
            assign _e_0 = _e_1[_e_2 * 3+:3];"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &statement,
                &TypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn array_indexing_works_for_1_bit_values() {
        let statement = statement!(e(0); Type::Bool; IndexArray; e(1), e(2));

        let expected = indoc!(
            r#"
            logic _e_0;
            assign _e_0 = _e_1[_e_2];"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &statement,
                &TypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn entity_instantiation_works() {
        let stmt = statement!(e(0); Type::Bool; Instance(("test".to_string(), None)); e(1), e(2));

        let expected = indoc!(
            r#"
            logic _e_0;
            e_test test__e_0(_e_1, _e_2, _e_0);"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &TypeList::empty()
                    .with(ValueName::Expr(1), Type::Bool)
                    .with(ValueName::Expr(2), Type::Bool),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn entity_instantiation_with_back_and_forward_ports_works() {
        let ty = Type::Tuple(vec![Type::backward(Type::Bool), Type::Bool]);
        let stmt = statement!(e(0); ty; Instance(("test".to_string(), None)); e(1), e(2));

        let expected = indoc!(
            r#"
            logic _e_0;
            logic _e_0_o;
            e_test test__e_0(_e_1, _e_2, _e_0, _e_0_o);"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &TypeList::empty()
                    .with(ValueName::Expr(1), Type::Bool)
                    .with(ValueName::Expr(2), Type::Bool),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn entity_instantiation_with_back_ports_works() {
        let ty = Type::backward(Type::Bool);
        let stmt = statement!(e(0); ty; Instance(("test".to_string(), None)); e(1), e(2));

        let expected = indoc!(
            r#"
            logic _e_0_o;
            e_test test__e_0(_e_1, _e_2, _e_0_o);"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &TypeList::empty()
                    .with(ValueName::Expr(1), Type::Bool)
                    .with(ValueName::Expr(2), Type::Bool),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn entity_instantiation_with_back_inputs_works() {
        let ty = Type::Bool;
        let stmt = statement!(e(0); ty; Instance(("test".to_string(), None)); e(1), e(2));

        let expected = indoc!(
            r#"
            logic _e_0;
            e_test test__e_0(_e_1, _e_1_o, _e_2_o, _e_0);"#
        );

        let type_list = TypeList::empty()
            .with(
                ValueName::Expr(1),
                Type::Tuple(vec![Type::Bool, Type::backward(Type::Bool)]),
            )
            .with(ValueName::Expr(2), Type::backward(Type::Bool));

        assert_same_code!(
            &statement_code_and_declaration(&stmt, &type_list, &CodeBundle::new("".to_string()))
                .to_string(),
            expected
        );
    }

    #[test]
    fn decl_clocked_array_works() {
        let t = Type::Array {
            inner: Box::new(Type::Int(6)),
            length: 4,
        };
        let stmt = statement!(e(0); t; DeclClockedMemory({write_ports: 2, addr_w: 4, inner_w: 6, elems: 16}); e(1), e(2));

        // Total write array length: 2 * (1 + 4 + 6)

        let expected = indoc!(
            r#"
            logic[23:0] _e_0;
            always @(posedge _e_1) begin
                if (_e_2[10]) begin
                    _e_0[_e_2[9:6]] <= _e_2[5:0];
                end
                if (_e_2[21]) begin
                    _e_0[_e_2[20:17]] <= _e_2[16:11];
                end
            end"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &TypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn decl_clocked_array_with_1_bit_address_works() {
        let t = Type::Array {
            inner: Box::new(Type::Int(6)),
            length: 4,
        };
        let stmt = statement!(e(0); t; DeclClockedMemory({write_ports: 1, addr_w: 1, inner_w: 6, elems: 16}); e(1), e(2));

        let expected = indoc!(
            r#"
            logic[23:0] _e_0;
            always @(posedge _e_1) begin
                if (_e_2[7]) begin
                    _e_0[_e_2[6]] <= _e_2[5:0];
                end
            end"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &TypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn decl_clocked_array_with_1_bit_data_works() {
        let t = Type::Array {
            inner: Box::new(Type::Bool),
            length: 4,
        };
        let stmt = statement!(e(0); t; DeclClockedMemory({write_ports: 1, addr_w: 4, inner_w: 1, elems: 16}); e(1), e(2));

        // Total write array length: 2 * (1 + 4 + 6)

        let expected = indoc!(
            r#"
            logic[3:0] _e_0;
            always @(posedge _e_1) begin
                if (_e_2[5]) begin
                    _e_0[_e_2[4:1]] <= _e_2[0];
                end
            end"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &TypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn truncate_works() {
        let stmt = statement!(e(0); Type::Int(5); Truncate; e(1));

        let expected = indoc! {
            r#"
            logic[4:0] _e_0;
            assign _e_0 = _e_1[4:0];"#
        };

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &TypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn sext_works_for_many_bits() {
        let stmt =
            statement!(e(0); Type::Int(5); SignExtend({extra_bits: 2, operand_size: 3}); e(1));

        let expected = indoc! {
            r#"
            logic[4:0] _e_0;
            assign _e_0 = {{ 2 { _e_1[2] }}, _e_1};"#
        };

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &TypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }
    #[test]
    fn sext_works_for_one_bits() {
        let stmt =
            statement!(e(0); Type::Int(4); SignExtend({extra_bits: 1, operand_size: 3}); e(1));

        let expected = indoc! {
            r#"
            logic[3:0] _e_0;
            assign _e_0 = {_e_1[2], _e_1};"#
        };

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &TypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }
    #[test]
    fn sext_works_for_zero_bits() {
        let stmt =
            statement!(e(0); Type::Int(3); SignExtend({extra_bits: 0, operand_size: 3}); e(1));

        let expected = indoc! {
            r#"
            logic[2:0] _e_0;
            assign _e_0 = _e_1;"#
        };

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &TypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn zext_works_for_many_bits() {
        let stmt = statement!(e(0); Type::Int(5); ZeroExtend({extra_bits: 2}); e(1));

        let expected = indoc! {
            r#"
            logic[4:0] _e_0;
            assign _e_0 = {2'b0, _e_1};"#
        };

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &TypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }
    #[test]
    fn zext_works_for_one_bits() {
        let stmt = statement!(e(0); Type::Int(4); ZeroExtend({extra_bits: 1}); e(1));

        let expected = indoc! {
            r#"
            logic[3:0] _e_0;
            assign _e_0 = {1'b0, _e_1};"#
        };

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &TypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn zext_works_for_zero_bits() {
        let stmt = statement!(e(0); Type::Int(3); ZeroExtend({extra_bits: 0}); e(1));

        let expected = indoc! {
            r#"
            logic[2:0] _e_0;
            assign _e_0 = _e_1;"#
        };

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &TypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn div_pow2_works() {
        let stmt = statement!(e(0); Type::Int(3); DivPow2; e(1), e(2));

        let expected = indoc! {
            r#"
            logic[2:0] _e_0;
            always_comb begin
                if (_e_2 == 0) begin
                    _e_0 = _e_1;
                end
                else begin
                    _e_0 = $signed($signed(_e_1) + $signed(1 << (_e_2 - 1))) >>> $signed(_e_2);
                end
            end"#
        };

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &TypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        )
    }

    #[test]
    fn concat_works() {
        let stmt = statement!(e(0); Type::Int(8); Concat; e(1), e(2));

        let expected = indoc! {
            r#"
            logic[7:0] _e_0;
            assign _e_0 = {_e_1, _e_2};"#
        };

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &TypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn assertion_codegen_works() {
        let stmt = Statement::Assert(value_name!(e(0)).at(0, &Span::new(1, 2)));

        // NOTE: The escape sequences here are a bit annoying when this test fails,
        // but where to add an option to turn them off isn't obvious. To update this test
        // verify that the output is correct, then run `cargo test | sed -e 's/\x1b/_x1b_/g'`
        // and copy paste the output here. Escape the " characters and replace _x1b_ with \x1b
        let expected = indoc! {
            "
            `ifndef SYNTHESIS
            always @(_e_0) begin
                #0
                assert (_e_0)
                else begin
                    $display(\"\x1b[0m\x1b[1m\x1b[38;5;9merror\x1b[0m\x1b[1m: Assertion failed\x1b[0m\");
                    $display(\"  \x1b[0m\x1b[34m┌─\x1b[0m <str>:1:2\");
                    $display(\"  \x1b[0m\x1b[34m│\x1b[0m\");
                    $display(\"\x1b[0m\x1b[34m1\x1b[0m \x1b[0m\x1b[34m│\x1b[0m a\x1b[0m\x1b[38;5;9mb\x1b[0mcd\");
                    $display(\"  \x1b[0m\x1b[34m│\x1b[0m  \x1b[0m\x1b[38;5;9m^\x1b[0m \x1b[0m\x1b[38;5;9mThis expression is false\x1b[0m\");
                    $display(\"\");
                    $error(\"Assertion failed\");
                    $fatal(1);
                end
            end
            `endif"
        };

        let source_code = CodeBundle::new("abcd".to_string());

        assert_same_code!(
            &statement_code_and_declaration(&stmt, &TypeList::empty(), &source_code).to_string(),
            expected
        );
    }

    #[test]
    fn set_codegen_works() {
        let stmt = Statement::Set {
            target: value_name!(e(0)).nowhere(),
            value: value_name!(e(1)).nowhere(),
        };

        let expected = indoc! {
            r#"
            assign _e_0_o = _e_1;"#
        };

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &TypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn read_port_codegen_works() {
        let stmt = statement!(e(0); Type::Int(8); ReadPort; e(1));

        let expected = indoc! {
            r#"
            logic[7:0] _e_0;
            assign _e_0 = _e_1_o;"#
        };

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &TypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }
}
