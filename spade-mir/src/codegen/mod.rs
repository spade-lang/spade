use itertools::Itertools;
use nesty::{code, Code};
use spade_codespan_reporting::term::termcolor;

use num::{BigInt, BigUint, One, Signed, ToPrimitive, Zero};
use spade_common::id_tracker::ExprIdTracker;
use spade_common::location_info::Loc;
use spade_common::name::NameID;
use spade_common::num_ext::InfallibleToBigUint;
use spade_diagnostics::emitter::CodespanEmitter;
use spade_diagnostics::{CodeBundle, CompilationError, DiagHandler};

use crate::aliasing::flatten_aliases;
use crate::assertion_codegen::AssertedExpression;
use crate::eval::eval_statements;
use crate::renaming::{make_names_predictable, VerilogNameMap};
use crate::type_list::MirTypeList;
use crate::types::Type;
use crate::unit_name::{InstanceMap, InstanceNameTracker};
use crate::verilog::{self, assign, localparam_size_spec, logic, size_spec};
use crate::wal::insert_wal_signals;
use crate::{
    enum_util, Binding, ConstantValue, Entity, MirInput, Operator, ParamName, Statement, ValueName,
};

pub mod util;

pub use util::{escape_path, mangle_entity, mangle_input, mangle_output, TupleIndex};

struct Context<'a> {
    types: &'a MirTypeList,
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
    if ty.size() != BigUint::zero() {
        name_map.insert(&name.var_name(), name.verilog_name_source_fwd());
    }
    if ty.backward_size() != BigUint::zero() {
        name_map.insert(&name.backward_var_name(), name.verilog_name_source_back());
    }
}

fn statement_declaration(
    statement: &Statement,
    code: &Option<CodeBundle>,
    name_map: &mut VerilogNameMap,
) -> Code {
    match statement {
        Statement::Binding(binding) => {
            add_to_name_map(name_map, &binding.name, &binding.ty);
            let name = binding.name.var_name();

            let forward_declaration = if binding.ty.size() != BigUint::zero() {
                let inner = vec![match &binding.ty {
                    crate::types::Type::Memory { inner, length } => {
                        let inner_w = inner.size();
                        if inner_w > 1u32.to_biguint() {
                            format!("logic[{inner_w}-1:0] {name}[{length}-1:0];")
                        } else {
                            format!("logic {name}[{length}-1:0];")
                        }
                    }
                    _ => logic(&name, &binding.ty.size()),
                }];
                code![
                    [0] source_attribute(&binding.loc, code);
                    [0] inner
                ]
            } else {
                code![]
            };

            let backward_declaration = if binding.ty.backward_size() != BigUint::zero() {
                code![
                    [0] source_attribute(&binding.loc, code);
                    [0] logic(
                        &binding.name.backward_var_name(),
                        &binding.ty.backward_size(),
                    );
                ]
            } else {
                code![]
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
                [0] &forward_declaration;
                [0] &backward_declaration;
                [0] &assignment;
            }
        }
        Statement::Register(reg) => {
            if reg.ty.backward_size() != BigUint::zero() {
                panic!("Attempting to put value with a backward_size != 0 in a register")
            }
            if reg.ty.size() != BigUint::zero() {
                add_to_name_map(name_map, &reg.name, &reg.ty);
                let name = reg.name.var_name();
                let declaration = verilog::reg(&name, &reg.ty.size());
                code! {
                    [0] source_attribute(&reg.loc, code);
                    [0] &declaration;
                }
            } else {
                code! {}
            }
        }
        Statement::Constant(name, ty, value) => {
            add_to_name_map(name_map, name, ty);

            let name = name.var_name();

            let expression = match value {
                ConstantValue::Int(val) => {
                    let size = match ty {
                        crate::types::Type::Int(size) | crate::types::Type::UInt(size) => size,
                        _ => panic!("Const integer that is not const"),
                    };

                    let val_abs = val.abs();
                    let sign = if val < &BigInt::zero() { "-" } else { "" };

                    // Verilog literals are 32 bits by default
                    let size_spec = if *size >= 32u32.to_biguint() {
                        format!("{size}'d")
                    } else {
                        String::new()
                    };
                    format!("{sign}{size_spec}{val_abs}")
                }
                ConstantValue::Bool(val) => format!("{}", if *val { 1 } else { 0 }),
                ConstantValue::String(val) => format!("{:?}", val),
                ConstantValue::HighImp => "'bz".to_string(),
            };

            if ty.size() != BigUint::ZERO {
                let size = localparam_size_spec(&ty.size());

                let assignment = format!("localparam{size} {name} = {expression};");

                code! {
                    [0] &assignment
                }
            } else {
                code! {}
            }
        }
        Statement::Assert(_) => {
            code! {}
        }
        Statement::Set { .. } => {
            code! {}
        }
        Statement::WalTrace { .. } => {
            panic!("Encountered a WalTrace mir node during codegen");
        }
        Statement::Error => {
            println!("WARNING: Running codegen on a Statement::Error");
            code! {
                [0] "// Codegen ran for an Error statement"
            }
        }
    }
}

fn compute_tuple_index(idx: u64, sizes: &[BigUint]) -> TupleIndex {
    // Compute the start index of the element we're looking for
    let mut start_bit = BigUint::zero();
    for i in 0..idx {
        start_bit += &sizes[i as usize];
    }

    let target_width = &sizes[idx as usize];

    let end_bit = &start_bit + target_width;

    let total_width: BigUint = sizes.iter().sum();

    // Check if this is a single bit, if so, index using just it
    if target_width == &0u32.to_biguint() {
        TupleIndex::ZeroWidth
    } else if sizes.iter().sum::<BigUint>() == 1u32.to_biguint() {
        TupleIndex::None
    } else if target_width == &1u32.to_biguint() {
        TupleIndex::Single(total_width - start_bit - 1u32.to_biguint())
    } else {
        TupleIndex::Range {
            left: &total_width - start_bit - 1u32.to_biguint(),
            right: &total_width - end_bit,
        }
    }
}

fn forward_expression_code(binding: &Binding, types: &MirTypeList, ops: &[ValueName]) -> String {
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
        Operator::Truncate => {
            format!(
                "{}[{}:0]",
                op_names[0],
                binding.ty.size() - 1u32.to_biguint()
            )
        }
        Operator::Concat => {
            format!(
                "{{{}}}",
                op_names.iter().map(|op| op.to_string()).join(", ")
            )
        }
        Operator::SignExtend => {
            let operand_size = types[&ops[0]].size();
            let self_size = self_type.size();
            if self_size > operand_size {
                let extra_bits = self_size - &operand_size;
                match extra_bits.to_u32() {
                    Some(0) => unreachable!(),
                    Some(1) => format!(
                        "{{{}[{}], {}}}",
                        op_names[0],
                        operand_size - 1u32.to_biguint(),
                        op_names[0]
                    ),
                    _ => format!(
                        "#[#[ {extra_bits} #[ {op}[{last_index}] #]#], {op}#]",
                        op = op_names[0],
                        last_index = operand_size - 1u32.to_biguint(),
                    )
                    // For readability with the huge amount of braces that both
                    // rust and verilog want here, we'll insert them at the end
                    // like this
                    .replace("#[", "{")
                    .replace("#]", "}"),
                }
            } else {
                op_names[0].to_string()
            }
        }
        Operator::ZeroExtend => {
            let operand_size = types[&ops[0]].size();
            let self_size = self_type.size();
            if self_size > operand_size {
                let extra_bits = self_size - operand_size;
                format!("{{{}'b0, {}}}", extra_bits, op_names[0])
            } else {
                op_names[0].clone()
            }
        }
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
        Operator::IndexTuple(idx) => {
            let inner_types = match &types[&ops[0]] {
                Type::Tuple(fields) => fields.clone(),
                Type::Struct(fields) => fields.iter().map(|(_name, ty)| ty.clone()).collect(),
                Type::Array { inner, length } => {
                    vec![(**inner).clone(); length.to_usize().unwrap()]
                }
                _ => panic!("Tuple index with non-tuple input"),
            };
            let sizes = inner_types.iter().map(|t| t.size()).collect::<Vec<_>>();
            let idx = compute_tuple_index(*idx, &sizes);
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
            let Type::Array { length, .. } = &types[&ops[0]] else {
                panic!("Array index with non-array input");
            };
            let member_size = self_type.size();
            if length != &BigUint::one() {
                if member_size == 1u32.to_biguint() {
                    format!("{}[{}]", op_names[0], op_names[1])
                } else {
                    let end_index = format!("{} * {}", op_names[1], member_size);
                    let offset = member_size;

                    // Strange indexing explained here https://stackoverflow.com/questions/18067571/indexing-vectors-and-arrays-with#18068296
                    format!("{}[{}+:{}]", op_names[0], end_index, offset)
                }
            } else {
                format!("{}", op_names[0])
            }
        }
        Operator::RangeIndexArray {
            start,
            end_exclusive: end,
        } => {
            let (member_size, input_length) = match &types[&ops[0]] {
                Type::Array { inner, length } => (inner.size(), length),
                _ => panic!("Range index with non-array input"),
            };
            let num_elems = end - start;
            if input_length == &BigUint::one() {
                op_names[0].clone()
            } else if member_size == BigUint::one() && num_elems == BigUint::one() {
                format!("{}[{}]", op_names[0], start)
            } else {
                let end_index = (end * &member_size) - BigUint::one();
                let offset = member_size * num_elems;

                // Strange indexing explained here https://stackoverflow.com/questions/18067571/indexing-vectors-and-arrays-with#18068296
                format!("{}[{}-:{}]", op_names[0], end_index, offset)
            }
        }
        Operator::IndexMemory => {
            format!("{}[{}]", op_names[0], op_names[1])
        }
        Operator::RangeIndexBits {
            start,
            end_exclusive,
        } => {
            if end_exclusive - start == 1u32.to_biguint() {
                format!("{}[{start}]", op_names[0])
            } else {
                format!("{}[{end_exclusive}:{start}]", op_names[0])
            }
        }
        Operator::DeclClockedMemory { initial } => {
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
        }
        Operator::ConstructEnum { variant } => {
            let Type::Enum(options) = &binding.ty else {
                panic!("Attempted enum construction of non-enum");
            };

            let tag_size = enum_util::tag_size(options.len());

            let members = &options[*variant];

            let included_members = members
                .iter()
                .zip(op_names)
                .filter_map(|(ty, name)| {
                    if ty.size() != BigUint::ZERO {
                        Some(name)
                    } else {
                        None
                    }
                })
                .collect::<Vec<_>>();

            // Compute the amount of undefined bits to put at the end of the literal.
            // First compute the size of this variant
            let variant_member_size = members.iter().map(|t| t.size()).sum::<BigUint>();

            let padding_size = binding.ty.size() - tag_size - variant_member_size;

            let padding_text = if padding_size != BigUint::zero() {
                format!(", {}'bX", padding_size)
            } else {
                String::new()
            };

            let ops_text = if included_members.is_empty() {
                String::new()
            } else {
                format!(
                    "{}{}",
                    if tag_size != 0 { ", " } else { "" },
                    included_members.join(", ")
                )
            };

            let tag = if tag_size != 0 {
                format!("{tag_size}'d{variant}")
            } else {
                "".to_string()
            };

            format!("{{{tag}{ops_text}{padding_text}}}")
        }
        Operator::IsEnumVariant { variant } => {
            let enum_type = &types[&ops[0]];

            // Special case for fully zero sized enum
            if enum_type.size() == BigUint::ZERO {
                "1".to_string()
            } else {
                let tag_size = enum_util::tag_size(enum_type.assume_enum().len());
                let total_size = enum_type.size();

                let tag_end = &total_size - 1u32.to_biguint();
                let tag_start = &total_size - tag_size as u64;

                if tag_size == 0 {
                    "1".to_string()
                } else if total_size == 1u32.to_biguint() {
                    format!("{} == 1'd{}", op_names[0], variant)
                } else if tag_end == tag_start {
                    format!("{}[{}] == {}'d{}", op_names[0], tag_end, tag_size, variant)
                } else {
                    format!(
                        "{}[{}:{}] == {}'d{}",
                        op_names[0], tag_end, tag_start, tag_size, variant
                    )
                }
            }
        }
        Operator::EnumMember {
            variant,
            member_index,
        } => {
            let enum_type = &types[&ops[0]];

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
            if upper_idx == lower_idx && tag_size == 0 {
                op_names[0].clone()
            } else {
                format!("{}[{}:{}]", op_names[0], upper_idx, lower_idx)
            }
        }
        Operator::ReadPort => ops[0].backward_var_name(),
        Operator::ReadWriteInOut => {
            // NOTE Dummy. Set in statement_code
            String::new()
        }
        Operator::FlipPort => {
            // NOTE Dummy. Set in statement_code
            String::new()
        }
        Operator::ReadMutWires => {
            // NOTE Dummy. Set in statement_code
            String::new()
        }
        Operator::ConstructTuple => {
            let mut members = ops
                .iter()
                .filter(|op| types[op].size() != BigUint::zero())
                .map(|op| op.var_name());
            // To make index calculations easier, we will store tuples in "inverse order".
            // i.e. the left-most element is stored to the right in the bit vector.
            format!("{{{}}}", members.join(", "))
        }
        Operator::Instance { .. } => {
            // NOTE: dummy. Set in the next match statement
            String::new()
        }
        Operator::Alias => {
            // NOTE Dummy. Set in the next match statement
            String::new()
        }
        Operator::Nop => String::new(),
    }
}

fn backward_expression_code(binding: &Binding, types: &MirTypeList, ops: &[ValueName]) -> String {
    let self_type = &binding.ty;
    let op_names = ops
        .iter()
        .map(ValueName::backward_var_name)
        .collect::<Vec<_>>();
    let fwd_op_names = ops.iter().map(ValueName::var_name).collect::<Vec<_>>();
    match &binding.operator {
        Operator::Add
        | Operator::UnsignedAdd
        | Operator::Sub
        | Operator::UnsignedSub
        | Operator::Mul
        | Operator::UnsignedMul
        | Operator::Div
        | Operator::UnsignedDiv
        | Operator::Mod
        | Operator::UnsignedMod
        | Operator::Eq
        | Operator::NotEq
        | Operator::Gt
        | Operator::UnsignedGt
        | Operator::Lt
        | Operator::UnsignedLt
        | Operator::Ge
        | Operator::UnsignedGe
        | Operator::Le
        | Operator::UnsignedLe
        | Operator::LeftShift
        | Operator::RightShift
        | Operator::ArithmeticRightShift
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
        | Operator::ReduceAnd
        | Operator::ReduceOr
        | Operator::ReduceXor
        | Operator::SignExtend
        | Operator::ZeroExtend
        | Operator::Concat
        | Operator::DeclClockedMemory { .. }
        | Operator::ConstructEnum { .. }
        | Operator::IsEnumVariant { .. }
        | Operator::EnumMember { .. }
        | Operator::RangeIndexBits { .. }
        | Operator::IndexMemory
        | Operator::Select
        | Operator::Match
        | Operator::ReadPort
        | Operator::Truncate => panic!(
            "{} cannot be used on types with backward size",
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
            let Type::Array { length, .. } = &types[&ops[0]] else {
                panic!("Attempt to use array indexing on non-array type");
            };
            let member_size = self_type.backward_size();
            if length != &BigUint::one() {
                if member_size == 1u32.to_biguint() {
                    format!("{}[{}]", op_names[0], fwd_op_names[1])
                } else {
                    let end_index = format!("{} * {}", fwd_op_names[1], member_size);
                    let offset = member_size;

                    // Strange indexing explained here https://stackoverflow.com/questions/18067571/indexing-vectors-and-arrays-with#18068296
                    format!("{}[{}+:{}]", op_names[0], end_index, offset)
                }
            } else {
                op_names[0].clone()
            }
        }
        Operator::RangeIndexArray {
            start,
            end_exclusive: end,
        } => {
            let (member_size, input_length) = match &types[&ops[0]] {
                Type::Array { inner, length } => (inner.size(), length),
                _ => panic!("Range index with non-array input"),
            };
            let elems = end - start;
            if input_length == &BigUint::one() {
                op_names[0].clone()
            } else if member_size == BigUint::one() && elems == BigUint::one() {
                format!("{}[{}]", op_names[0], start)
            } else {
                let end_index = format!("{} * {}", start, member_size);
                let offset = member_size * elems;

                // Strange indexing explained here https://stackoverflow.com/questions/18067571/indexing-vectors-and-arrays-with#18068296
                format!("{}[{}+:{}]", op_names[0], end_index, offset)
            }
        }
        Operator::ConstructTuple => {
            let mut members = ops
                .iter()
                .filter(|op| types[op].backward_size() != BigUint::zero())
                .map(|op| op.backward_var_name());
            format!("{{{}}}", members.join(", "))
        }
        Operator::IndexTuple(index) => {
            let inner_types = match &types[&ops[0]] {
                Type::Tuple(fields) => fields.clone(),
                Type::Struct(fields) => fields.iter().map(|(_name, ty)| ty.clone()).collect(),
                Type::Array { inner, length } => {
                    vec![(**inner).clone(); length.to_usize().unwrap()]
                }
                _ => panic!("Tuple index with non-tuple input"),
            };

            // NOTE: Disabled assertion because it triggers issues in the LSP
            // assert_eq!(&inner_types[*index as usize], self_type);

            let sizes = inner_types
                .iter()
                .map(|t| t.backward_size())
                .collect::<Vec<_>>();
            let index = compute_tuple_index(*index, &sizes);
            format!("{}{}", op_names[0], index.verilog_code())
        }
        Operator::FlipPort => {
            // NOTE: Set in statement_code
            String::new()
        }
        Operator::ReadMutWires => {
            // NOTE Dummy. Set in statement_code
            String::new()
        }
        Operator::ReadWriteInOut => {
            // NOTE Dummy. Set in statement_code
            String::new()
        }
        Operator::Instance { .. } => String::new(),
        Operator::Alias => {
            // NOTE: Set in statement_code
            String::new()
        }
        Operator::Nop => String::new(),
    }
}

fn statement_code(statement: &Statement, ctx: &mut Context) -> Code {
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

            let forward_expression = if binding.ty.size() != BigUint::zero() {
                Some(forward_expression_code(
                    binding,
                    ctx.types,
                    &binding.operands,
                ))
            } else {
                None
            };
            let backward_expression = if binding.ty.backward_size() != BigUint::zero() {
                Some(backward_expression_code(
                    binding,
                    ctx.types,
                    &binding.operands,
                ))
            } else {
                None
            };

            // Unless this is a special operator, we just use assign value = expression
            let assignment = match &binding.operator {
                Operator::Instance{name: module_name, params, argument_names, loc, verilog_attr_groups} => {
                    let param_string = if params.is_empty() {
                        "".into()
                    } else {
                        let param_strings = params.iter().map(|(name, value)| format!(".{}({})", name, value)).collect::<Vec<_>>();
                        format!("#({})", param_strings.join(", "))
                    };
                    // Input args
                    let mut args = binding
                        .operands
                        .iter()
                        .zip(argument_names)
                        .flat_map(|(port, ParamName{name, no_mangle})| {
                            let ty = &ctx.types[port];

                            // Push the input and output into the result if they
                            // should be bound
                            let mut result = vec![];
                            if ty.size() != BigUint::zero()  {
                                result.push(format!(
                                    ".{}({})",
                                    mangle_input(no_mangle, name),
                                    port.var_name()
                                ))
                            }
                            if ty.backward_size() != BigUint::zero()  {
                                result.push(format!(
                                    ".{}({})",
                                    mangle_output(no_mangle, name),
                                    port.backward_var_name()
                                ))
                            }
                            result
                        }).collect::<Vec<_>>();

                    if binding.ty.size() != BigUint::zero()  {
                        args.push(format!(".output__({name})"));
                    }
                    if binding.ty.backward_size() != BigUint::zero()  {
                        args.push(format!(".input__({back_name})"));
                    }

                    let instance_name = module_name.instance_name(
                        ctx.unit_nameid.clone(),
                        ctx.instance_map,
                        ctx.instance_names
                    );

                    code!{
                        [0] source_attribute(loc, ctx.source_code);
                        [0] codegen_verilog_attr_groups(verilog_attr_groups);
                        [0] format!(
                            "{}{} \\{} ({});",
                            &module_name.as_verilog(),
                            if param_string.is_empty() { "".into() } else { format!("{}", param_string)},
                            instance_name,
                            args.join(", ")
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
                Operator::Match => forward_expression.unwrap(),
                Operator::DivPow2 => forward_expression.unwrap(),
                Operator::Nop => String::new(),
                Operator::FlipPort => {
                    let has_fwd = binding.ty.size() != BigUint::zero();
                    let has_back = binding.ty.backward_size() != BigUint::zero();
                    // The forward ports of the flipped port (op[0]) and and the original (self)
                    // should be mapped to the backward ports of the opposite port
                    code! {
                        [0] has_fwd.then(|| format!("assign {} = {};", name, back_ops[0]));
                        [0] has_back.then(|| format!("assign {} = {};", ops[0], back_name));
                    }
                    .to_string()
                }
                Operator::ReadMutWires => {
                    // The forward ports of the flipped port (op[0]) and and the original (self)
                    // should be mapped to the backward ports of the opposite port
                    code! {
                        [0] format!("assign {} = {};", name, back_ops[0]);
                    }
                    .to_string()
                }
                Operator::DeclClockedMemory { .. } => forward_expression.unwrap(),
                Operator::ReadWriteInOut => {
                    let total_size_minus_one = binding.ty.size() - BigUint::one();
                    let payload_size = binding.ty.size() - BigUint::one();
                    let payload_size_minus_one = &payload_size - BigUint::one();
                    code! {
                        [0] format!("assign {} = {}[{}] ? {}[{}:0] : {}'bZ;",
                                ops[0],
                                back_name, total_size_minus_one,
                                back_name, payload_size_minus_one,
                                payload_size);
                        [0] format!("assign {} = {}[{}] ? {{ 1'b0, {}'bX }} : {{ 1'b1, {} }};",
                                name,
                                back_name, total_size_minus_one,
                                payload_size,
                                ops[0])
                    }
                    .to_string()
                }
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

            let initial_block = if let Some(initial) = reg.initial.as_ref() {
                code! {
                    [0] "initial begin";
                    [1]     format!("{} = 'b{};", name, eval_statements(initial).as_string());
                    [0] "end";
                }
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
            let mut assignments = Vec::new();
            if ctx.types[&value.inner].size() != BigUint::ZERO {
                assignments.push(format!(
                    "assign {} = {};",
                    target.backward_var_name(),
                    value.var_name(),
                ));
            }
            if ctx.types[&value.inner].backward_size() != BigUint::ZERO {
                assignments.push(format!(
                    "assign {} = {};",
                    value.backward_var_name(),
                    target.var_name(),
                ))
            };

            code! {
                [0] assignments;
            }
        }
        Statement::WalTrace { .. } => {
            panic!("Encountered a WalTrace mir node during codegen");
        }
        Statement::Error => {
            code! {
                [0] "// Codegen ran for an error node"
            }
        }
    }
}

#[cfg(test)]
fn statement_code_and_declaration(
    statement: &Statement,
    types: &MirTypeList,
    source_code: &CodeBundle,
) -> Code {
    use spade_common::name::Path;

    let mut ctx = Context {
        types,
        source_code: &Some(source_code.clone()),
        instance_names: &mut InstanceNameTracker::new(),
        instance_map: &mut InstanceMap::new(),
        unit_nameid: &NameID(0, Path::from_strs(&["dummy"])),
    };
    code! {
        [0] statement_declaration(statement, &Some(source_code.clone()), &mut VerilogNameMap::new());
        [0] statement_code(statement, &mut ctx);
    }
}

/// A mir entity which has had passes required for codegen performed on it
#[derive(Clone)]
pub struct Codegenable(pub Entity);

pub fn prepare_codegen(mut entity: Entity, expr_idtracker: &ExprIdTracker) -> Codegenable {
    flatten_aliases(&mut entity);
    make_names_predictable(&mut entity);
    insert_wal_signals(&mut entity, expr_idtracker, &mut None);

    Codegenable(entity)
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
    entity: &Codegenable,
    instance_map: &mut InstanceMap,
    source_code: &Option<CodeBundle>,
) -> (Code, VerilogNameMap) {
    let mut name_map = VerilogNameMap::new();

    let Codegenable(entity) = entity;

    let verilog_attr_groups = codegen_verilog_attr_groups(&entity.verilog_attr_groups);

    let types = &MirTypeList::from_entity(entity);

    let entity_name = entity.name.as_verilog();

    let inputs = &entity.inputs;

    let inputs = inputs.iter().map(
        |MirInput {
             name,
             val_name,
             ty,
             no_mangle,
         }| {
            if ty.size() != BigUint::zero() {
                name_map.insert(name, val_name.verilog_name_source_fwd());
            }
            if ty.backward_size() != BigUint::zero() {
                name_map.insert(name, val_name.verilog_name_source_back());
            }

            let size = ty.size();
            let (input_head, input_code) = if size != BigUint::zero() {
                let name = mangle_input(no_mangle, name);

                name_map.insert(&name, val_name.verilog_name_source_fwd());

                let input_or_inout = match ty {
                    Type::InOut(_) => "inout",
                    _ => "input",
                };

                // If the no_mangle attribute is set, we need to avoid clashing between the port
                // name, and the value_name. Because the first value_name in a module has the same
                // name as the value_name, and because inputs are unique it is enough to just skip
                // alias assignment if no_mangle is set
                let alias_assignment = if no_mangle.is_none() {
                    code! {
                        [0] &logic(&val_name.var_name(), &size);
                        [0] &assign(&val_name.var_name(), &name)
                    }
                } else {
                    code! {}
                };
                (
                    format!("{input_or_inout}{} {}", size_spec(&size), name),
                    alias_assignment,
                )
            } else {
                (String::new(), code! {})
            };

            let backward_size = ty.backward_size();
            let (output_head, output_code) = if backward_size != BigUint::zero() {
                let name = mangle_output(no_mangle, name);
                name_map.insert(&name, val_name.verilog_name_source_back());
                (
                    format!("output{} {}", size_spec(&backward_size), name),
                    code! {
                        [0] &logic(&val_name.backward_var_name(), &backward_size);
                        [0] &assign(&name, &val_name.backward_var_name())
                    },
                )
            } else {
                (String::new(), code! {})
            };

            let spacing = if !input_head.is_empty() && !output_head.is_empty() {
                ", "
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
        },
    );

    let (inputs, input_assignments): (Vec<_>, Vec<_>) = inputs.unzip();

    let back_port_size = entity.output_type.backward_size();
    let (back_port_definition, back_port_assignment) = if back_port_size != BigUint::zero() {
        let def = code! {
            [0] format!(
                "input{} input__",
                size_spec(&entity.output_type.backward_size())
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
    let (output_definition, output_assignment) = if output_size != BigUint::zero() {
        let def = code! {
            [0] format!("output{} output__", size_spec(&output_size))
        };
        let assignment = code! {[0] assign("output__", &entity.output.var_name())};

        name_map.insert("output__", entity.output.verilog_name_source_fwd());

        (Some(def), Some(assignment))
    } else {
        (None, None)
    };

    let mut ctx = Context {
        types,
        source_code,
        instance_names: &mut InstanceNameTracker::new(),
        instance_map,
        unit_nameid: &entity.name.source,
    };

    let mut body = Code::new();

    for stmt in &entity.statements {
        body.join(&statement_declaration(stmt, source_code, &mut name_map))
    }
    for stmt in &entity.statements {
        body.join(&statement_code(stmt, &mut ctx))
    }

    // Collect all port definitions into an already indented code snippet
    let port_definitions = inputs
        .into_iter()
        .map(|s| code! { [0] s})
        .chain(output_definition)
        .chain(back_port_definition)
        .map(|code| code.to_string())
        .filter(|s| !s.is_empty())
        .join(",\n");

    let code = code! {
        [0] verilog_attr_groups;
        [0] &format!("module {} (", entity_name);
                [2] &port_definitions;
            [1] &");";
            [1] format!("`COCOTB_CODE( {top_name} )", top_name = entity.name.without_escapes());
            [1] &input_assignments;
            [1] &body;
            [1] &output_assignment;
            [1] &back_port_assignment;
        [0] &"endmodule"
    };
    (code, name_map)
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

#[cfg(test)]
mod tests {
    use super::*;
    use colored::Colorize;
    use spade_common::id_tracker::ExprID;
    use spade_common::location_info::WithLocation;
    use spade_common::name::Path;

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
                &MirTypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn binding_code_works() {
        let binding = statement!(e(0); Type::int(5); Add; e(1), e(2));

        let expected = indoc!(
            r#"
            logic[4:0] _e_0;
            assign _e_0 = $signed(_e_1) + $signed(_e_2);"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &binding,
                &MirTypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn registers_without_reset_work() {
        let reg = statement!(reg n(0, "r"); Type::int(7); clock (e(0)); e(1));

        let expected = indoc!(
            r#"
                reg[6:0] \r ;
                always @(posedge _e_0) begin
                    \r  <= _e_1;
                end"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &reg,
                &MirTypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn registers_with_reset_work() {
        let reg = statement!(reg n(0, "r"); Type::int(7); clock (e(0)); reset (e(2), e(3)); e(1));

        let expected = indoc!(
            r#"
                reg[6:0] \r ;
                always @(posedge _e_0) begin
                    if (_e_2) begin
                        \r  <= _e_3;
                    end
                    else begin
                        \r  <= _e_1;
                    end
                end"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &reg,
                &MirTypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn registers_with_initial_values_work() {
        let initial_value = vec![
            statement!(const 4; Type::int(7); ConstantValue::int(0b10_1100)),
            statement!(e(5); Type::int(7); Alias; e(4)),
        ];
        let reg =
            statement!(reg n(0, "r"); Type::int(7); clock (e(0)); initial (initial_value); e(1));

        let expected = indoc!(
            r#"
                reg[6:0] \r ;
                initial begin
                    \r  = 'b0101100;
                end
                always @(posedge _e_0) begin
                    \r  <= _e_1;
                end"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &reg,
                &MirTypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn entity_codegen_works() {
        let input = entity!(&["pong"]; ("op", n(0, "op"), Type::int(6)) -> Type::int(6); {
            (e(0); Type::int(6); Add; n(0, "op"), e(1))
        } => e(0));

        let expected = indoc!(
            r#"

            module \pong  (
                    input[5:0] op_i,
                    output[5:0] output__
                );
                `COCOTB_CODE( pong )
                logic[5:0] \op ;
                assign \op  = op_i;
                logic[5:0] _e_0;
                assign _e_0 = $signed(\op ) + $signed(_e_1);
                assign output__ = _e_0;
            endmodule"#
        );

        assert_same_code!(
            &entity_code(
                &prepare_codegen(input.clone(), &mut ExprIdTracker::new()),
                &mut InstanceMap::new(),
                &None
            )
            .0
            .to_string(),
            expected
        );
    }

    #[test]
    fn verilog_attr_groups_work_on_entity_declarations() {
        let mut input = entity!(&["pong"]; ("op", n(0, "op"), Type::int(6)) -> Type::int(6); {
            (e(0); Type::int(6); Add; n(0, "op"), e(1))
        } => e(0));

        input.verilog_attr_groups = vec![
            vec![("alone".into(), None)],
            vec![
                ("standalone".into(), None),
                ("key".into(), Some("value".into())),
            ],
        ];

        let expected = indoc!(
            r#"
            (* alone *)
            (* standalone, key = "value" *)
            module \pong  (
                    input[5:0] op_i,
                    output[5:0] output__
                );
                `COCOTB_CODE( pong )
                logic[5:0] \op ;
                assign \op  = op_i;
                logic[5:0] _e_0;
                assign _e_0 = $signed(\op ) + $signed(_e_1);
                assign output__ = _e_0;
            endmodule"#
        );

        assert_same_code!(
            &entity_code(
                &prepare_codegen(input.clone(), &mut ExprIdTracker::new()),
                &mut InstanceMap::new(),
                &None
            )
            .0
            .to_string(),
            expected
        );
    }

    #[test]
    fn no_mangle_input_does_not_clash() {
        let input = spade_mir::Entity {
            name: spade_mir::unit_name::IntoUnitName::_test_into_unit_name("test"),
            inline: false,
            inputs: vec![spade_mir::MirInput {
                name: "a".to_string(),
                val_name: ValueName::_test_named(0, "a".to_string()),
                ty: Type::Bool,
                no_mangle: Some(().nowhere()),
            }],
            output: ValueName::Expr(ExprID(0)),
            output_type: Type::Bool,
            statements: vec![],
            verilog_attr_groups: vec![],
        };

        let expected = indoc!(
            r#"

            module test (
                    input a,
                    output output__
                );
                `COCOTB_CODE( test )
                assign output__ = _e_0;
            endmodule"#
        );

        assert_same_code!(
            &entity_code(
                &prepare_codegen(input.clone(), &mut ExprIdTracker::new()),
                &mut InstanceMap::new(),
                &None
            )
            .0
            .to_string(),
            expected
        );
    }

    #[test]
    fn no_mangle_output_does_not_clash() {
        let input = spade_mir::Entity {
            name: spade_mir::unit_name::IntoUnitName::_test_into_unit_name("test"),
            inline: false,
            inputs: vec![spade_mir::MirInput {
                name: "a".to_string(),
                val_name: ValueName::_test_named(0, "a".to_string()),
                ty: Type::Backward(Box::new(Type::Bool)),
                no_mangle: Some(().nowhere()),
            }],
            output: ValueName::Expr(ExprID(0)),
            output_type: Type::Bool,
            statements: vec![],
            verilog_attr_groups: vec![],
        };

        let expected = indoc!(
            r#"

            module test (
                    output a,
                    output output__
                );
                `COCOTB_CODE( test )
                logic \a_mut ;
                assign a = \a_mut ;
                assign output__ = _e_0;
            endmodule"#
        );

        assert_same_code!(
            &entity_code(
                &prepare_codegen(input.clone(), &mut ExprIdTracker::new()),
                &mut InstanceMap::new(),
                &None
            )
            .0
            .to_string(),
            expected
        );
    }

    #[test]
    fn pure_backward_input_produces_output_port() {
        let ty = Type::Backward(Box::new(Type::int(3)));
        let input = entity!(&["test"]; ("a", n(0, "a"), ty) -> Type::int(6); {
            (const 0; Type::int(6); crate::ConstantValue::int(3))
        } => e(0));

        let expected = indoc!(
            r#"

            module \test  (
                    output[2:0] a_o,
                    output[5:0] output__
                );
                `COCOTB_CODE( test )
                logic[2:0] \a_mut ;
                assign a_o = \a_mut ;
                localparam[5:0] _e_0 = 3;
                assign output__ = _e_0;
            endmodule"#
        );

        assert_same_code!(
            &entity_code(
                &prepare_codegen(input.clone(), &mut ExprIdTracker::new()),
                &mut InstanceMap::new(),
                &None
            )
            .0
            .to_string(),
            expected
        );
    }

    #[test]
    fn mixed_backward_input_works() {
        let ty = Type::Tuple(vec![Type::int(4), Type::Backward(Box::new(Type::int(3)))]);
        let input = entity!(&["test"]; ("a", n(0, "a"), ty) -> Type::int(6); {
            (const 0; Type::int(6); crate::ConstantValue::int(3))
        } => e(0));

        let expected = indoc!(
            r#"

            module \test  (
                    input[3:0] a_i, output[2:0] a_o,
                    output[5:0] output__
                );
                `COCOTB_CODE( test )
                logic[3:0] \a ;
                assign \a  = a_i;
                logic[2:0] \a_mut ;
                assign a_o = \a_mut ;
                localparam[5:0] _e_0 = 3;
                assign output__ = _e_0;
            endmodule"#
        );

        assert_same_code!(
            &entity_code(
                &prepare_codegen(input.clone(), &mut ExprIdTracker::new()),
                &mut InstanceMap::new(),
                &None
            )
            .0
            .to_string(),
            expected
        );
    }

    #[test]
    fn mixed_backward_output_works() {
        let ty = Type::Tuple(vec![Type::int(4), Type::Backward(Box::new(Type::int(3)))]);
        let input = entity!("test"; () -> ty; {
        } => e(0));

        let expected = indoc!(
            r#"

            module test (
                    output[3:0] output__,
                    input[2:0] input__
                );
                `COCOTB_CODE( test )
                assign output__ = _e_0;
                assign _e_0_mut = input__;
            endmodule"#
        );

        assert_same_code!(
            &entity_code(
                &prepare_codegen(input.clone(), &mut ExprIdTracker::new()),
                &mut InstanceMap::new(),
                &None
            )
            .0
            .to_string(),
            expected
        );
    }

    #[test]
    fn constant_codegen_works() {
        let input = statement!(const 0; Type::int(10); crate::ConstantValue::int(6));

        let expected = indoc!(
            r#"
            localparam[9:0] _e_0 = 6;"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &input,
                &MirTypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        )
    }

    #[test]
    fn pipeline_with_stage_references_codegens_correctly() {
        let inst_name = spade_mir::UnitName::_test_from_strs(&["A"]);
        let input = entity!(&["pl"]; (
                "clk", n(3, "clk"), Type::Bool,
            ) -> Type::int(16); {
                (reg n(10, "x__s1"); Type::int(16); clock(n(3, "clk")); n(0, "x_"));
                // Stage 0
                (e(0); Type::int(16); simple_instance((inst_name, vec![])););
                (n(0, "x_"); Type::int(16); Alias; e(0));
                // Stage 1
                (n(1, "x"); Type::int(16); Alias; n(0, "x_"));
            } => n(1, "x")
        );

        // This test removes a lot of variables through alias resolution
        let expected = indoc!(
            r#"

            module \pl  (
                    input clk_i,
                    output[15:0] output__
                );
                `COCOTB_CODE( pl )
                logic \clk ;
                assign \clk  = clk_i;
                reg[15:0] \x__s1 ;
                logic[15:0] \x_ ;
                logic[15:0] \x ;
                always @(posedge \clk ) begin
                    \x__s1  <= \x_ ;
                end
                
                \A  \A_0 (.output__(\x_ ));
                assign \x  = \x_ ;
                assign output__ = \x ;
            endmodule"#
        );

        assert_same_code!(
            &entity_code(
                &prepare_codegen(input.clone(), &mut ExprIdTracker::new()),
                &mut InstanceMap::new(),
                &None
            )
            .0
            .to_string(),
            expected
        );
    }

    #[test]
    fn duplicate_names_adds_nx() {
        let input = entity!(&["pl"]; (
            ) -> Type::int(16); {
                (n(1, "x"); Type::int(16); Not; e(0));
                (n(2, "x"); Type::int(16); Not; e(1));
            } => n(1, "x")
        );

        let expected = indoc!(
            r#"

            module \pl  (
                    output[15:0] output__
                );
                `COCOTB_CODE( pl )
                logic[15:0] \x ;
                logic[15:0] x_n1;
                assign \x  = !_e_0;
                assign x_n1 = !_e_1;
                assign output__ = \x ;
            endmodule"#
        );

        assert_same_code! {
            &entity_code(&prepare_codegen(input.clone(), &mut ExprIdTracker::new()), &mut InstanceMap::new(), &None).0.to_string(),
            expected
        }
    }

    #[test]
    fn instance_map_is_populated() {
        let inst1_name = NameID(10, Path::from_strs(&["test1"]));
        let inst1_unit_name = spade_mir::UnitName {
            kind: spade_mir::unit_name::UnitNameKind::Unescaped("test1".into()),
            source: inst1_name.clone(),
        };
        let inst2_name = NameID(11, Path::from_strs(&["test1"]));
        let inst2_unit_name = spade_mir::UnitName {
            kind: spade_mir::unit_name::UnitNameKind::Unescaped("test1".into()),
            source: inst2_name.clone(),
        };

        let top_name = NameID(1, Path::from_strs(&["top"]));
        let top_unit_name = spade_mir::UnitName {
            kind: spade_mir::unit_name::UnitNameKind::Unescaped("test1".into()),
            source: top_name.clone(),
        };
        let input = entity!(&top_unit_name; (
                "clk", n(3, "clk"), Type::Bool,
            ) -> Type::int(16); {
                (reg n(10, "x__s1"); Type::int(16); clock(n(3, "clk")); n(0, "x_"));
                // Stage 0
                (e(0); Type::int(16); Instance({
                    name: inst1_unit_name,
                    params: vec![],
                    argument_names: vec![
                        ParamName{name: "a".to_string(), no_mangle: None},
                        ParamName{name: "b".to_string(), no_mangle: None},
                    ],
                    loc: None,
                    verilog_attr_groups: vec![],
                }););
                (e(0); Type::int(16); Instance({
                    name: inst2_unit_name,
                    params: vec![],
                    argument_names: vec![
                        ParamName{name: "a".to_string(), no_mangle: None},
                        ParamName{name: "b".to_string(), no_mangle: None},
                    ],
                    loc: None,
                    verilog_attr_groups: vec![],
                }););
                (n(0, "x_"); Type::int(16); Alias; e(0));
                // Stage 1
                (n(1, "x"); Type::int(16); Alias; n(0, "x_"));
            } => n(1, "x")
        );

        let mut instance_map = InstanceMap::new();
        entity_code(
            &prepare_codegen(input, &mut ExprIdTracker::new()),
            &mut instance_map,
            &None,
        );

        let top = instance_map
            .inner
            .get(&(top_name.clone()))
            .expect("Failed to get top");

        assert_eq!(
            top.get(&"test1_0".to_string())
                .expect("failed to get test1_0"),
            &inst1_name
        );
        assert_eq!(
            top.get(&"test1_1".to_string())
                .expect("failed to get test1_0"),
            &inst2_name
        );
    }
}

#[cfg(test)]
mod backward_expression_tests {
    use super::*;
    use colored::Colorize;
    use spade_common::id_tracker::ExprID;

    use crate as spade_mir;
    use crate::{statement, types::Type};

    use indoc::indoc;

    #[test]
    fn backward_alias_works() {
        let ty = Type::Backward(Box::new(Type::int(8)));
        let stmt = statement!(e(0); ty; Alias; e(1));

        let expected = indoc! {
            r#"
            logic[7:0] _e_0_mut;
            assign _e_1_mut = _e_0_mut;"#
        };

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &MirTypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn backward_index_tuple_works() {
        let tuple_members = vec![Type::backward(Type::int(8)), Type::backward(Type::int(4))];
        let ty = Type::backward(Type::int(4));
        let stmt = statement!(e(0); ty; IndexTuple((1)); e(1));

        let expected = indoc! {
            r#"
            logic[3:0] _e_0_mut;
            assign _e_1_mut[3:0] = _e_0_mut;"#
        };

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &MirTypeList::empty().with(ValueName::Expr(ExprID(1)), Type::Tuple(tuple_members)),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn flip_port_works() {
        let out_type = Type::Tuple(vec![Type::backward(Type::int(2)), Type::int(4)]);
        let stmt = statement!(e(0); out_type; FlipPort; e(1));

        let expected = indoc! {
            r#"
            logic[3:0] _e_0;
            logic[1:0] _e_0_mut;
            assign _e_0 = _e_1_mut;
            assign _e_1 = _e_0_mut;"#
        };

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &MirTypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn construct_tuple_works() {
        let tuple_members = vec![Type::backward(Type::int(8)), Type::backward(Type::int(4))];
        let ty = Type::Tuple(tuple_members);
        let stmt = statement!(e(0); ty; ConstructTuple; e(1), e(2));

        let type_list = MirTypeList::empty()
            .with(ValueName::Expr(ExprID(1)), Type::backward(Type::int(8)))
            .with(ValueName::Expr(ExprID(2)), Type::backward(Type::int(4)));

        let expected = indoc! {
            r#"
            logic[11:0] _e_0_mut;
            assign {_e_1_mut, _e_2_mut} = _e_0_mut;"#
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
            Type::backward(Type::int(8)),
            Type::Tuple(vec![Type::backward(Type::int(4)), Type::int(4)]),
            Type::int(3),
        ];
        let ty = Type::Tuple(tuple_members);
        let stmt = statement!(e(0); ty; ConstructTuple; e(1), e(2), e(3));

        let expected = indoc! {
            r#"
            logic[6:0] _e_0;
            logic[11:0] _e_0_mut;
            assign _e_0 = {_e_2, _e_3};
            assign {_e_1_mut, _e_2_mut} = _e_0_mut;"#
        };

        let type_list = MirTypeList::empty()
            .with(ValueName::Expr(ExprID(1)), Type::backward(Type::int(8)))
            .with(
                ValueName::Expr(ExprID(2)),
                Type::Tuple(vec![Type::backward(Type::int(4)), Type::int(4)]),
            )
            .with(ValueName::Expr(ExprID(3)), Type::int(3));

        assert_same_code!(
            &statement_code_and_declaration(&stmt, &type_list, &CodeBundle::new("".to_string()))
                .to_string(),
            expected
        );
    }

    #[test]
    fn construct_array_works() {
        let ty = Type::Array {
            inner: Box::new(Type::backward(Type::int(5))),
            length: 3u32.to_biguint(),
        };
        let stmt = statement!(e(0); ty; ConstructArray; e(1), e(2), e(3));

        let expected = indoc! {
            r#"
            logic[14:0] _e_0_mut;
            assign {_e_3_mut, _e_2_mut, _e_1_mut} = _e_0_mut;"#
        };

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &MirTypeList::empty(),
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
    use colored::Colorize;
    use spade_codespan::Span;
    use spade_common::id_tracker::ExprID;
    use spade_common::location_info::WithLocation;
    use spade_common::num_ext::InfallibleToBigInt;

    use crate::{self as spade_mir, value_name, UnitName};
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

                assert_same_code!(&statement_code_and_declaration(&stmt, &MirTypeList::empty(), &CodeBundle::new("".to_string())).to_string(), &expected)
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

                assert_same_code!(&statement_code_and_declaration(&stmt, &MirTypeList::empty(), &CodeBundle::new("".to_string())).to_string(), &expected)
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

                assert_same_code!(&statement_code_and_declaration(&stmt, &MirTypeList::empty(), &CodeBundle::new("".to_string())).to_string(), &expected)
            }
        }
    }

    signed_binop_test!(binop_add_works, Type::int(2), "[1:0]", Add, "+");
    signed_binop_test!(binop_sub_works, Type::int(2), "[1:0]", Sub, "-");
    signed_binop_test!(binop_mul_works, Type::int(2), "[1:0]", Mul, "*");
    binop_test!(
        binop_left_shift_works,
        Type::int(2),
        "[1:0]",
        LeftShift,
        "<<"
    );
    binop_test!(
        binop_right_shift_works,
        Type::int(2),
        "[1:0]",
        RightShift,
        ">>"
    );
    signed_binop_test!(
        binop_arithmetic_right_shift_works,
        Type::int(2),
        "[1:0]",
        ArithmeticRightShift,
        ">>>"
    );
    binop_test!(binop_eq_works, Type::Bool, "", Eq, "==");
    signed_binop_test!(binop_gt_works, Type::Bool, "", Gt, ">");
    signed_binop_test!(binop_lt_works, Type::Bool, "", Lt, "<");
    signed_binop_test!(binop_ge_works, Type::Bool, "", Ge, ">=");
    signed_binop_test!(binop_le_works, Type::Bool, "", Le, "<=");
    binop_test!(binop_logical_and_works, Type::Bool, "", LogicalAnd, "&&");
    binop_test!(binop_logical_or_works, Type::Bool, "", LogicalOr, "||");
    binop_test!(bitwise_xor_works, Type::int(32), "[31:0]", BitwiseXor, "^");
    // NOTE: The resulting verilog uses `^` on a 1 bit value
    binop_test!(logical_xor_works, Type::Bool, "", LogicalXor, "^");
    unop_test!(not_works, Type::Bool, "", Not, "!");
    unop_test!(usub_works, Type::int(2), "[1:0]", USub, "-");

    #[test]
    fn select_operator_works() {
        let stmt = statement!(e(0); Type::int(2); Select; e(1), e(2), e(3));

        let expected = indoc!(
            r#"
            logic[1:0] _e_0;
            assign _e_0 = _e_1 ? _e_2 : _e_3;"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &MirTypeList::empty(),
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
                &MirTypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn match_operator_works() {
        let stmt = statement!(e(0); Type::int(2); Match; e(1), e(2), e(3), e(4));

        let expected = indoc!(
            r#"
            logic[1:0] _e_0;
            always_comb begin
                priority casez ({_e_1, _e_3})
                    2'b1?: _e_0 = _e_2;
                    2'b01: _e_0 = _e_4;
                    2'b?: _e_0 = 2'dx;
                endcase
            end"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &MirTypeList::empty(),
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
            localparam[0:0] _e_0 = 1;"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &MirTypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn tuple_assembly_operator_works() {
        let ty = Type::Tuple(vec![Type::int(6), Type::int(3)]);
        let stmt = statement!(e(0); ty; ConstructTuple; e(1), e(2));

        let expected = indoc!(
            r#"
            logic[8:0] _e_0;
            assign _e_0 = {_e_1, _e_2};"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &MirTypeList::empty()
                    .with(ValueName::Expr(ExprID(1)), Type::int(6))
                    .with(ValueName::Expr(ExprID(2)), Type::int(3)),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn enum_construction_operator_works() {
        let ty = Type::Enum(vec![vec![], vec![], vec![Type::int(10), Type::int(5)]]);
        let stmt = statement!(e(0); ty; ConstructEnum({variant: 2}); e(1), e(2));

        let expected = indoc!(
            r#"
            logic[16:0] _e_0;
            assign _e_0 = {2'd2, _e_1, _e_2};"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &MirTypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn is_enum_variant_operator_works() {
        let ty = Type::Enum(vec![vec![], vec![], vec![Type::int(10), Type::int(5)]]);
        let stmt = statement!(e(0); Type::Bool; IsEnumVariant({variant: 2}); e(1));

        let expected = indoc!(
            r#"
            logic _e_0;
            assign _e_0 = _e_1[16:15] == 2'd2;"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &MirTypeList::empty().with(ValueName::Expr(ExprID(1)), ty),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn is_enum_variant_operator_works_for_1_wide_tags() {
        let ty = Type::Enum(vec![vec![], vec![Type::int(10), Type::int(5)]]);
        let stmt = statement!(e(0); Type::Bool; IsEnumVariant({variant: 1}); e(1));

        let expected = indoc!(
            r#"
            logic _e_0;
            assign _e_0 = _e_1[15] == 1'd1;"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &MirTypeList::empty().with(ValueName::Expr(ExprID(1)), ty),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn enum_member_access_operator_works() {
        let ty = Type::Enum(vec![vec![], vec![], vec![Type::int(10), Type::int(5)]]);
        let stmt = statement!(e(0); Type::int(5); EnumMember({variant: 2, member_index: 1}); e(1));

        let expected = indoc!(
            r#"
            logic[4:0] _e_0;
            assign _e_0 = _e_1[4:0];"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &MirTypeList::empty().with(ValueName::Expr(ExprID(1)), ty),
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
            vec![Type::int(5)],
            vec![Type::int(10), Type::int(5)],
        ]);
        let stmt = statement!(e(0); ty; ConstructEnum({variant: 1}); e(1));

        let expected = indoc!(
            r#"
            logic[16:0] _e_0;
            assign _e_0 = {2'd1, _e_1, 10'bX};"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &MirTypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn tuple_indexing_works_for_first_value() {
        let ty = Type::Tuple(vec![Type::int(6), Type::int(3)]);
        let stmt = statement!(e(0); Type::int(6); IndexTuple((0)); e(1));

        let expected = indoc!(
            r#"
            logic[5:0] _e_0;
            assign _e_0 = _e_1[8:3];"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &MirTypeList::empty().with(ValueName::Expr(ExprID(1)), ty),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }
    #[test]
    fn tuple_indexing_works() {
        let ty = Type::Tuple(vec![Type::int(6), Type::int(3)]);
        let stmt = statement!(e(0); Type::int(6); IndexTuple((1)); e(1));

        let expected = indoc!(
            r#"
            logic[5:0] _e_0;
            assign _e_0 = _e_1[2:0];"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &MirTypeList::empty().with(ValueName::Expr(ExprID(1)), ty),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn tuple_indexing_works_for_bools() {
        let ty = Type::Tuple(vec![Type::Bool, Type::int(3)]);
        let stmt = statement!(e(0); Type::Bool; IndexTuple((0)); e(1));

        let expected = indoc!(
            r#"
            logic _e_0;
            assign _e_0 = _e_1[3];"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &MirTypeList::empty().with(ValueName::Expr(ExprID(1)), ty),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn large_negative_literals_codegen_correctly() {
        let statement = statement!(const 0; Type::int(64); ConstantValue::int(-1));

        let expected = indoc!(
            r#"
            localparam[63:0] _e_0 = -64'd1;"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &statement,
                &MirTypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn array_literals_work() {
        let ty = Type::Array {
            inner: Box::new(Type::int(3)),
            length: 3u32.to_biguint(),
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
                &MirTypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn array_indexing_works() {
        let statement = statement!(e(0); Type::int(3); IndexArray; e(1), e(2));

        let expected = indoc!(
            r#"
            logic[2:0] _e_0;
            assign _e_0 = _e_1[_e_2 * 3+:3];"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &statement,
                &MirTypeList::empty().with(
                    ValueName::Expr(ExprID(1)),
                    Type::Array {
                        inner: Box::new(Type::int(3)),
                        length: 3_u32.to_biguint(),
                    }
                ),
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
                &MirTypeList::empty().with(
                    ValueName::Expr(ExprID(1)),
                    Type::Array {
                        inner: Box::new(Type::Bool),
                        length: 4_u32.to_biguint(),
                    }
                ),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn array_indexing_works_for_1_element_bool_arrays() {
        let statement = statement!(e(0); Type::Bool; IndexArray; e(1), e(2));

        let expected = indoc!(
            r#"
            logic _e_0;
            assign _e_0 = _e_1;"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &statement,
                &MirTypeList::empty().with(
                    ValueName::Expr(ExprID(1)),
                    Type::Array {
                        inner: Box::new(Type::Bool),
                        length: 1_u32.to_biguint(),
                    }
                ),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn array_indexing_works_for_1_element_int_arrays() {
        let statement = statement!(e(0); Type::int(10); IndexArray; e(1), e(2));

        let expected = indoc!(
            r#"
            logic[9:0] _e_0;
            assign _e_0 = _e_1;"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &statement,
                &MirTypeList::empty().with(
                    ValueName::Expr(ExprID(1)),
                    Type::Array {
                        inner: Box::new(Type::int(10)),
                        length: 1_u32.to_biguint(),
                    }
                ),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn range_array_indexing_works() {
        let ty = Type::Array {
            inner: Box::new(Type::int(10)),
            length: 2u32.to_biguint(),
        };
        let statement = statement!(e(0); ty; RangeIndexArray({
            start: 1u32.to_biguint(),
            end_exclusive: 2u32.to_biguint(),
        }); e(1), e(2));

        let expected = indoc!(
            r#"
            logic[19:0] _e_0;
            assign _e_0 = _e_1[19-:10];"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &statement,
                &MirTypeList::empty().with(
                    ValueName::Expr(ExprID(1)),
                    Type::Array {
                        inner: Box::new(Type::int(10)),
                        length: 4u32.to_biguint(),
                    }
                ),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn range_array_indexing_on_bool_array_works() {
        let ty = Type::Array {
            inner: Box::new(Type::Bool),
            length: 2u32.to_biguint(),
        };
        let statement = statement!(e(0); ty; RangeIndexArray({
            start: 1u32.to_biguint(),
            end_exclusive: 2u32.to_biguint(),
        }); e(1), e(2));

        let expected = indoc!(
            r#"
            logic[1:0] _e_0;
            assign _e_0 = _e_1[1];"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &statement,
                &MirTypeList::empty().with(
                    ValueName::Expr(ExprID(1)),
                    Type::Array {
                        inner: Box::new(Type::Bool),
                        length: 4u32.to_biguint(),
                    }
                ),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn range_array_indexing_on_single_element_array_works() {
        let ty = Type::Array {
            inner: Box::new(Type::int(10)),
            length: 1u32.to_biguint(),
        };
        let statement = statement!(e(0); ty; RangeIndexArray({
            start: 1u32.to_biguint(),
            end_exclusive: 2u32.to_biguint(),
        }); e(1), e(2));

        let expected = indoc!(
            r#"
            logic[9:0] _e_0;
            assign _e_0 = _e_1;"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &statement,
                &MirTypeList::empty().with(
                    ValueName::Expr(ExprID(1)),
                    Type::Array {
                        inner: Box::new(Type::int(10)),
                        length: 1u32.to_biguint(),
                    }
                ),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn entity_instantiation_works() {
        let inst_name = UnitName::_test_from_strs(&["e_test"]);
        let stmt = statement!(
            e(0); Type::Bool; Instance({
                name: inst_name,
                params: vec![],
                argument_names: vec![
                    ParamName{name: "a".to_string(), no_mangle: None},
                    ParamName{name: "b".to_string(), no_mangle: None},
                ],
                loc: None,
                verilog_attr_groups: vec![],
            });
            e(1),
            e(2)
        );

        let expected = indoc!(
            r#"
            logic _e_0;

            \e_test  \e_test_0 (.a_i(_e_1), .b_i(_e_2), .output__(_e_0));"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &MirTypeList::empty()
                    .with(ValueName::Expr(ExprID(1)), Type::Bool)
                    .with(ValueName::Expr(ExprID(2)), Type::Bool),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn entity_instantiation_with_back_and_forward_ports_works() {
        let inst_name = UnitName::_test_from_strs(&["e_test"]);
        let ty = Type::Tuple(vec![Type::backward(Type::Bool), Type::Bool]);
        let stmt = statement!(e(0); ty; Instance({
            name: inst_name,
            params: vec![],
            argument_names: vec![
                ParamName{name: "a".to_string(), no_mangle: None},
                ParamName{name: "b".to_string(), no_mangle: None},
            ],
            loc: None,
            verilog_attr_groups: vec![],
        }); e(1), e(2));

        let expected = indoc!(
            r#"
            logic _e_0;
            logic _e_0_mut;

            \e_test  \e_test_0 (.a_i(_e_1), .b_i(_e_2), .output__(_e_0), .input__(_e_0_mut));"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &MirTypeList::empty()
                    .with(ValueName::Expr(ExprID(1)), Type::Bool)
                    .with(ValueName::Expr(ExprID(2)), Type::Bool),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn entity_instantiation_with_back_ports_works() {
        let ty = Type::backward(Type::Bool);
        let stmt = statement!(e(0); ty; Instance({
            name:UnitName::_test_from_strs(&["e_test"]),
            params: vec![],
            argument_names: vec![
                ParamName{name: "a".to_string(), no_mangle: None},
                ParamName{name: "b".to_string(), no_mangle: None},
            ],
            loc: None,
            verilog_attr_groups: vec![],
        }); e(1), e(2));

        let expected = indoc!(
            r#"
            logic _e_0_mut;

            \e_test  \e_test_0 (.a_i(_e_1), .b_i(_e_2), .input__(_e_0_mut));"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &MirTypeList::empty()
                    .with(ValueName::Expr(ExprID(1)), Type::Bool)
                    .with(ValueName::Expr(ExprID(2)), Type::Bool),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn entity_instantiation_with_back_inputs_works() {
        let ty = Type::Bool;
        let stmt = statement!(e(0); ty; Instance({
            name:UnitName::_test_from_strs(&["test"]),
            params: vec![],
            argument_names: vec![
                ParamName{name: "a".to_string(), no_mangle: None},
                ParamName{name: "b".to_string(), no_mangle: None},
            ],
            loc: None,
            verilog_attr_groups: vec![],
        }); e(1), e(2));

        let expected = indoc!(
            r#"
            logic _e_0;

            \test  \test_0 (.a_i(_e_1), .a_o(_e_1_mut), .b_o(_e_2_mut), .output__(_e_0));"#
        );

        let type_list = MirTypeList::empty()
            .with(
                ValueName::Expr(ExprID(1)),
                Type::Tuple(vec![Type::Bool, Type::backward(Type::Bool)]),
            )
            .with(ValueName::Expr(ExprID(2)), Type::backward(Type::Bool));

        assert_same_code!(
            &statement_code_and_declaration(&stmt, &type_list, &CodeBundle::new("".to_string()))
                .to_string(),
            expected
        );
    }

    #[test]
    fn decl_clocked_array_works() {
        let t = Type::Memory {
            inner: Box::new(Type::int(6)),
            length: 16u32.to_biguint(),
        };
        let stmt = statement!(e(0); t; DeclClockedMemory({initial: None}); e(1), e(2));

        // Total write array length: 2 * (1 + 4 + 6)

        let expected = indoc!(
            r#"
            logic[6-1:0] _e_0[16-1:0];
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
                &MirTypeList::empty().with(
                    ValueName::Expr(ExprID(2)),
                    Type::Array {
                        inner: Box::new(Type::Tuple(vec![Type::Bool, Type::uint(4), Type::int(6)])),
                        length: 2u32.to_biguint(),
                    }
                ),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn decl_clocked_array_with_1_bit_address_works() {
        let t = Type::Memory {
            inner: Box::new(Type::int(6)),
            length: 2u32.to_biguint(),
        };
        let stmt = statement!(e(0); t; DeclClockedMemory({initial: None}); e(1), e(2));

        let expected = indoc!(
            r#"
            logic[6-1:0] _e_0[2-1:0];
            always @(posedge _e_1) begin
                if (_e_2[7]) begin
                    _e_0[_e_2[6]] <= _e_2[5:0];
                end
            end"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &MirTypeList::empty().with(
                    ValueName::Expr(ExprID(2)),
                    Type::Array {
                        inner: Box::new(Type::Tuple(vec![Type::Bool, Type::uint(1), Type::int(6)])),
                        length: 1u32.to_biguint(),
                    }
                ),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn decl_clocked_array_with_1_bit_data_works() {
        let t = Type::Memory {
            inner: Box::new(Type::Bool),
            length: 16u32.to_biguint(),
        };
        let stmt = statement!(e(0); t; DeclClockedMemory({initial: None}); e(1), e(2));

        // Total write array length: 2 * (1 + 4 + 6)

        let expected = indoc!(
            r#"
            logic _e_0[16-1:0];
            always @(posedge _e_1) begin
                if (_e_2[5]) begin
                    _e_0[_e_2[4:1]] <= _e_2[0];
                end
            end"#
        );

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &MirTypeList::empty().with(
                    ValueName::Expr(ExprID(2)),
                    Type::Array {
                        inner: Box::new(Type::Tuple(vec![Type::Bool, Type::uint(4), Type::Bool])),
                        length: 1u32.to_biguint(),
                    }
                ),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn decl_clocked_memory_with_initial_works() {
        let t = Type::Memory {
            inner: Box::new(Type::Int(6u32.to_biguint())),
            length: 16u32.to_biguint(),
        };
        let stmt = statement!(e(0); t; DeclClockedMemory({
            initial: Some(vec![
                vec![statement!(const 10; Type::Int(6u32.to_biguint()); ConstantValue::Int(10.to_bigint()))],
                vec![statement!(const 10; Type::Int(6u32.to_biguint()); ConstantValue::Int(5.to_bigint()))],
            ])
        }); e(1), e(2));

        // Total write array length: 2 * (1 + 4 + 6)

        let expected = indoc!(
            r#"
            logic[6-1:0] _e_0[16-1:0];
            initial begin
                _e_0[0] = 'b001010;
                _e_0[1] = 'b000101;
            end
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
                &MirTypeList::empty().with(
                    ValueName::Expr(ExprID(2)),
                    Type::Array {
                        inner: Box::new(Type::Tuple(vec![Type::Bool, Type::uint(4), Type::int(6)])),
                        length: 2u32.to_biguint(),
                    }
                ),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn truncate_works() {
        let stmt = statement!(e(0); Type::int(5); Truncate; e(1));

        let expected = indoc! {
            r#"
            logic[4:0] _e_0;
            assign _e_0 = _e_1[4:0];"#
        };

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &MirTypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn sext_works_for_many_bits() {
        let stmt = statement!(e(0); Type::int(5); SignExtend; e(1));

        let expected = indoc! {
            r#"
            logic[4:0] _e_0;
            assign _e_0 = {{ 2 { _e_1[2] }}, _e_1};"#
        };

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &MirTypeList::empty()
                    .with(ValueName::Expr(ExprID(0)), Type::Int(5_u32.to_biguint()))
                    .with(ValueName::Expr(ExprID(1)), Type::Int(3_u32.to_biguint())),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }
    #[test]
    fn sext_works_for_one_bits() {
        let stmt = statement!(e(0); Type::int(4); SignExtend; e(1));

        let expected = indoc! {
            r#"
            logic[3:0] _e_0;
            assign _e_0 = {_e_1[2], _e_1};"#
        };

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &MirTypeList::empty()
                    .with(ValueName::Expr(ExprID(0)), Type::Int(4_u32.to_biguint()))
                    .with(ValueName::Expr(ExprID(1)), Type::Int(3_u32.to_biguint())),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }
    #[test]
    fn sext_works_for_zero_bits() {
        let stmt = statement!(e(0); Type::int(3); SignExtend; e(1));

        let expected = indoc! {
            r#"
            logic[2:0] _e_0;
            assign _e_0 = _e_1;"#
        };

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &MirTypeList::empty()
                    .with(ValueName::Expr(ExprID(0)), Type::Int(3_u32.to_biguint()))
                    .with(ValueName::Expr(ExprID(1)), Type::Int(3_u32.to_biguint())),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn zext_works_for_many_bits() {
        let stmt = statement!(e(0); Type::int(5); ZeroExtend; e(1));

        let expected = indoc! {
            r#"
            logic[4:0] _e_0;
            assign _e_0 = {2'b0, _e_1};"#
        };

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &MirTypeList::empty()
                    .with(ValueName::Expr(ExprID(0)), Type::UInt(5_u32.to_biguint()))
                    .with(ValueName::Expr(ExprID(1)), Type::UInt(3_u32.to_biguint())),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }
    #[test]
    fn zext_works_for_one_bits() {
        let stmt = statement!(e(0); Type::int(4); ZeroExtend; e(1));

        let expected = indoc! {
            r#"
            logic[3:0] _e_0;
            assign _e_0 = {1'b0, _e_1};"#
        };

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &MirTypeList::empty()
                    .with(ValueName::Expr(ExprID(0)), Type::UInt(4_u32.to_biguint()))
                    .with(ValueName::Expr(ExprID(1)), Type::UInt(3_u32.to_biguint())),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn zext_works_for_zero_bits() {
        let stmt = statement!(e(0); Type::int(3); ZeroExtend; e(1));

        let expected = indoc! {
            r#"
            logic[2:0] _e_0;
            assign _e_0 = _e_1;"#
        };

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &MirTypeList::empty()
                    .with(ValueName::Expr(ExprID(0)), Type::UInt(3_u32.to_biguint()))
                    .with(ValueName::Expr(ExprID(1)), Type::UInt(3_u32.to_biguint())),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn div_pow2_works() {
        let stmt = statement!(e(0); Type::int(3); DivPow2; e(1), e(2));

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
                &MirTypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        )
    }

    #[test]
    fn concat_works() {
        let stmt = statement!(e(0); Type::int(8); Concat; e(1), e(2));

        let expected = indoc! {
            r#"
            logic[7:0] _e_0;
            assign _e_0 = {_e_1, _e_2};"#
        };

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &MirTypeList::empty(),
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
            &statement_code_and_declaration(&stmt, &MirTypeList::empty(), &source_code).to_string(),
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
            assign _e_0_mut = _e_1;"#
        };

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &MirTypeList::empty()
                    .with(ValueName::Expr(ExprID(0)), Type::backward(Type::Bool))
                    .with(ValueName::Expr(ExprID(1)), Type::Bool),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn read_mut_wire_codegen_works() {
        let stmt = statement!(e(0); Type::int(8); ReadPort; e(1));

        let expected = indoc! {
            r#"
            logic[7:0] _e_0;
            assign _e_0 = _e_1_mut;"#
        };

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &MirTypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    fn const_codegen_large_bit_width_works() {
        let stmt = statement!(const 0; Type::int(32); crate::ConstantValue::int(3));

        let expected = indoc! {
            r#"
            localparam[31:0] _e_0 = 32'd3;"#
        };

        assert_same_code!(
            &statement_code_and_declaration(
                &stmt,
                &MirTypeList::empty(),
                &CodeBundle::new("".to_string())
            )
            .to_string(),
            expected
        );
    }

    #[test]
    #[should_panic]
    fn compute_index_regression() {
        let result = compute_tuple_index(
            2,
            &[
                24u32.to_biguint(),
                17u32.to_biguint(),
                0u32.to_biguint(),
                2u32.to_biguint(),
                1u32.to_biguint(),
                1u32.to_biguint(),
            ],
        );

        result.verilog_code();
    }

    #[test]
    fn inout_codegens_as_inout() {
        let input = spade_mir::Entity {
            name: spade_mir::unit_name::IntoUnitName::_test_into_unit_name("test"),
            inline: false,
            inputs: vec![spade_mir::MirInput {
                name: "a".to_string(),
                val_name: ValueName::_test_named(0, "a".to_string()),
                ty: Type::InOut(Box::new(Type::Bool)),
                no_mangle: Some(().nowhere()),
            }],
            output: ValueName::Expr(ExprID(0)),
            output_type: Type::unit(),
            statements: vec![],
            verilog_attr_groups: vec![],
        };

        let expected = indoc!(
            r#"

            module test (
                    inout a
                );
                `COCOTB_CODE( test )
            endmodule"#
        );

        assert_same_code!(
            &entity_code(
                &prepare_codegen(input.clone(), &mut ExprIdTracker::new()),
                &mut InstanceMap::new(),
                &None
            )
            .0
            .to_string(),
            expected
        );
    }

    #[test]
    fn verilog_attrs_codegen_on_entity_declaration() {
        let input = spade_mir::Entity {
            name: spade_mir::unit_name::IntoUnitName::_test_into_unit_name("test"),
            inputs: vec![spade_mir::MirInput {
                name: "a".to_string(),
                val_name: ValueName::_test_named(0, "a".to_string()),
                ty: Type::Bool,
                no_mangle: Some(().nowhere()),
            }],
            output: ValueName::Expr(ExprID(0)),
            output_type: Type::unit(),
            statements: vec![],
            verilog_attr_groups: vec![
                vec![("single".into(), None)],
                vec![
                    ("standalone".into(), None),
                    ("key".into(), Some("val".into())),
                ],
            ],
            inline: false,
        };

        let expected = indoc!(
            r#"
            (* single *)
            (* standalone, key = "val" *)
            module test (
                    input a
                );
                `COCOTB_CODE( test )
            endmodule"#
        );

        assert_same_code!(
            &entity_code(
                &prepare_codegen(input.clone(), &mut ExprIdTracker::new()),
                &mut InstanceMap::new(),
                &None
            )
            .0
            .to_string(),
            expected
        );
    }

    #[test]
    fn verilog_attrs_codegen_on_entity_instantiation() {
        let input = spade_mir::Entity {
            name: spade_mir::unit_name::IntoUnitName::_test_into_unit_name("test"),
            inputs: vec![spade_mir::MirInput {
                name: "a".to_string(),
                val_name: ValueName::_test_named(0, "a".to_string()),
                ty: Type::Bool,
                no_mangle: Some(().nowhere()),
            }],
            output: ValueName::Expr(ExprID(0)),
            output_type: Type::unit(),
            statements: vec![spade_mir::Statement::Binding(spade_mir::Binding {
                name: ValueName::_test_named(0, "x".to_string()),
                operator: spade_mir::Operator::Instance {
                    name: UnitName::_test_from_strs(&["foo"]),
                    params: vec![],
                    argument_names: vec![],
                    loc: None,
                    verilog_attr_groups: vec![
                        vec![("single".into(), None)],
                        vec![
                            ("standalone".into(), None),
                            ("key".into(), Some("val".into())),
                        ],
                    ],
                },
                operands: vec![],
                ty: Type::unit(),
                loc: None,
            })],
            verilog_attr_groups: vec![],
            inline: false,
        };

        let expected = indoc!(
            r#"

            module test (
                    input a
                );
                `COCOTB_CODE( test )
                (* single *)
                (* standalone, key = "val" *)
                \foo  \foo_0 ();
            endmodule"#
        );

        assert_same_code!(
            &entity_code(
                &prepare_codegen(input.clone(), &mut ExprIdTracker::new()),
                &mut InstanceMap::new(),
                &None
            )
            .0
            .to_string(),
            expected
        );
    }
}
