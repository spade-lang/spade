mod aliasing;
mod assertion_codegen;
pub mod codegen;
pub mod diff;
pub mod diff_printing;
mod enum_util;
pub mod eval;
pub mod macros;
pub mod passes;
pub mod renaming;
mod type_list;
pub mod types;
pub mod unit_name;
pub mod verilator_wrapper;
mod verilog;
mod wal;

use derive_where::derive_where;
use itertools::Itertools;
use num::{BigInt, BigUint};
use renaming::VerilogNameSource;
use serde::{Deserialize, Serialize};
use types::Type;

use spade_common::location_info::{Loc, WithLocation};
use spade_common::name::NameID;
use spade_common::num_ext::InfallibleToBigInt;

pub use unit_name::UnitName;

#[derive(Clone, PartialEq, Debug)]
pub enum ConstantValue {
    Int(BigInt),
    Bool(bool),
    HighImp,
}

impl ConstantValue {
    pub fn int(val: i32) -> Self {
        Self::Int(val.to_bigint())
    }
}

impl std::fmt::Display for ConstantValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConstantValue::Int(val) => write!(f, "{val}"),
            ConstantValue::Bool(val) => write!(f, "{val}"),
            ConstantValue::HighImp => write!(f, "HIGHIMP"),
        }
    }
}

#[derive(Clone, PartialEq, Debug, Hash, Eq, serde::Serialize, serde::Deserialize)]
pub enum ValueNameSource {
    Name(NameID),
    Expr(u64),
}

impl From<NameID> for ValueNameSource {
    fn from(value: NameID) -> Self {
        (&value).into()
    }
}

impl From<&NameID> for ValueNameSource {
    fn from(value: &NameID) -> Self {
        Self::Name(value.clone())
    }
}

impl From<&ValueName> for ValueNameSource {
    fn from(value: &ValueName) -> Self {
        match value {
            ValueName::Named(_, _, source) => source.clone(),
            ValueName::Expr(id) => Self::Expr(*id),
        }
    }
}

/// A name of a value. Can either come from the NameID of the underlying
/// variable, or the id of the underlying expression
#[derive(Clone, Debug, Serialize, Deserialize)]
#[derive_where(Hash, Eq, PartialEq)]
pub enum ValueName {
    /// A named value in the code with with an index to make that name locally unique
    Named(
        // ID of the name in the generated verilog
        u64,
        // Human readable name in the generated verilog. If this is not unique
        // to the current module, the id will be appended
        String,
        // The original name ID from which this name originates
        // NOTE: Not checked by MIR diff because it is only a metadata field
        #[derive_where(skip)] ValueNameSource,
    ),
    // FIXME: Consider renaming this since it's now used for both patterns and expressions
    /// An un-named expression. In the resulting verilog, this is called _e_$id
    Expr(u64),
}

impl WithLocation for ValueName {}

impl ValueName {
    pub fn verilog_name_source_fwd(&self) -> VerilogNameSource {
        match self {
            ValueName::Named(_, _, ValueNameSource::Name(name_id)) => {
                VerilogNameSource::ForwardName(name_id.clone())
            }
            ValueName::Named(_, _, ValueNameSource::Expr(id)) | ValueName::Expr(id) => {
                VerilogNameSource::ForwardExpr(*id)
            }
        }
    }

    pub fn verilog_name_source_back(&self) -> VerilogNameSource {
        match self {
            ValueName::Named(_, _, ValueNameSource::Name(name_id)) => {
                VerilogNameSource::BackwardName(name_id.clone())
            }
            ValueName::Named(_, _, ValueNameSource::Expr(id)) | ValueName::Expr(id) => {
                VerilogNameSource::BackwardExpr(*id)
            }
        }
    }

    pub fn _test_named(id: u64, name: String) -> Self {
        use spade_common::name::Path;

        Self::Named(
            id,
            name.clone(),
            NameID(id, Path::from_strs(&[name.as_str()])).into(),
        )
    }
}

impl std::fmt::Display for ValueName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ValueName::Named(id, s, _) => {
                // The first identifier of each name has the exact same name as the underlying
                // spade variable.
                // However, Vivado has a bug where it treats an escaped `new` as the `new` keyword
                // from `SystemVerilog`, so we need to special case new here
                if *id == 0 && s != "new" {
                    write!(f, "{s}")
                } else {
                    write!(f, "{s}_n{id}")
                }
            }
            ValueName::Expr(id) => write!(f, "e{id}"),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct ParamName {
    pub name: String,
    pub no_mangle: Option<Loc<()>>,
}

#[derive_where(PartialEq)]
#[derive(Clone, Debug)]
pub enum Operator {
    // Binary arithmetic operators
    Add,
    UnsignedAdd,
    Sub,
    UnsignedSub,
    Mul,
    UnsignedMul,
    Div,
    UnsignedDiv,
    Mod,
    UnsignedMod,
    Eq,
    NotEq,
    Gt,
    UnsignedGt,
    Lt,
    UnsignedLt,
    Ge,
    UnsignedGe,
    Le,
    UnsignedLe,
    LeftShift,
    RightShift,
    ArithmeticRightShift,
    LogicalAnd,
    LogicalOr,
    LogicalXor,
    LogicalNot,
    BitwiseAnd,
    BitwiseOr,
    BitwiseXor,
    ReduceAnd,
    ReduceOr,
    ReduceXor,
    USub,
    Not,
    ReadPort,
    BitwiseNot,
    Bitreverse,
    // Divide op[0] by 2**op[1] rounding towards 0
    DivPow2,
    /// Convert the operand from gray code representation to binary
    Gray2Bin {
        num_bits: BigUint,
    },
    /// Sign extend the first operand with the provided amount of extra bits
    SignExtend {
        extra_bits: BigUint,
        operand_size: BigUint,
    },
    ZeroExtend {
        extra_bits: BigUint,
    },
    /// Truncate the first operand to fit the size of the target operand.
    /// Should not be used on operands which are smaller than the target
    Truncate,
    /// Concatenate the bits of all input operands
    Concat,
    /// Select [1] if [0] else [2]
    Select,
    /// Corresponds to a match statement. If value [0] is true, select [1], if [2] holds, select
    /// [3] and so on. Values are priorotized in order, i.e. if both [0] and [2] hold, [1] is
    /// selected
    // NOTE: We may want to add a MatchUnique for cases where we can guarantee uniqueness,
    // typically match statements with no wildcards
    Match,
    /// Construct an array from the operand expressions
    ConstructArray,
    /// Create a mutable array which is modified on the rising edge of the first argument.
    /// the second argument is an array of (write enable, write address, write data) tuples
    /// which update the array.
    DeclClockedMemory {
        write_ports: BigUint,
        /// Width of the write address
        addr_w: BigUint,
        /// Number of elements in the array
        inner_w: BigUint,
        /// Number of elements in the array
        elems: BigUint,
        /// Initial values for the memory. Must be const evaluatable
        initial: Option<Vec<Vec<Statement>>>,
    },
    /// Index an array with elements of the specified size
    IndexArray,
    IndexMemory,
    /// Indexes an array to extract a range of elements
    RangeIndexArray {
        start: BigUint,
        end_exclusive: BigUint,
    },
    /// Compiles to verilog [end_exclusive:start]. Supports single bit indexing, (when
    /// end_exclusive == start + 1, in which case it compiles to [start]
    RangeIndexBits {
        start: BigUint,
        end_exclusive: BigUint,
    },
    /// Construct a tuple from all the operand expressions
    ConstructTuple,
    /// Construct the nth enum variant with the operand expressions as the payload
    ConstructEnum {
        variant: usize,
        variant_count: usize,
    },
    /// 1 if the input is the specified enum variant
    IsEnumVariant {
        variant: usize,
        enum_type: Type,
    },
    /// Get the `member_index`th member of the `variant`th variant.
    EnumMember {
        enum_type: Type,
        variant: usize,
        member_index: usize,
    },
    /// Get the `.0`th element of a tuple or a type of the same representation as a tuple, for
    /// example a Struct. The types of the elements are specified
    /// in the second argument
    IndexTuple(u64, Vec<Type>),

    /// Inverts the direction of all bits of a port. I.e. the forward ports
    /// become backward ports. This is only valid when converting from T to ~T
    FlipPort,

    /// Given a struct or tuple consisting of mut and non-mut wires, create a new
    /// struct or tuple with the non-mut copies of the mut wires
    ///
    /// As an example `(&mut T1, T2, &mut T3)` becomes `(T1, T3)`
    // NOTE: For now this variant is a bit of a hack used during wal_trace_lowering
    // A saner implementation that also solves #252 would be nice
    // In particular, a dedicated `ReadMutTuple` might be useful
    // lifeguard spade#252
    ReadMutWires,

    /// Instantiation of another module with the specified name. The operands are passed
    /// by name to the entity. The operand name mapping is decided by the `argument_names` field of
    /// this variant. The first operand gets mapped to the first argument name, and so on.
    /// The target module can only have a single output which must be the last argument.
    /// The location of the instantiation is optional but can be passed to improve
    /// critical path report readability
    Instance {
        name: UnitName,
        params: Vec<(String, BigUint)>,
        /// The names of the arguments in the same order as the operands.
        /// For instance, if the `i`th argument name is "foo" and the `i`th [`Binding`] is
        /// `my_port`, the verilog module will be instantiated with `.foo(my_port)`.
        argument_names: Vec<ParamName>,
        #[derive_where(skip)]
        loc: Option<Loc<()>>,
    },
    /// Alias another named value
    Alias,
    /// Define a variable for the value but don't do anything with it. Useful for creating ports
    Nop,
}

impl Operator {
    pub fn simple_instance(name: UnitName, argument_names: Vec<&str>) -> Self {
        Self::Instance {
            name,
            params: Vec::default(),
            argument_names: argument_names
                .iter()
                .map(|p| ParamName {
                    name: p.to_string(),
                    no_mangle: None,
                })
                .collect(),
            loc: None,
        }
    }

    pub fn supports_zero_sized_operands(&self) -> bool {
        match self {
            Operator::Add => false,
            Operator::UnsignedAdd => false,
            Operator::Sub => false,
            Operator::UnsignedSub => false,
            Operator::Mul => false,
            Operator::UnsignedMul => false,
            Operator::Div => false,
            Operator::UnsignedDiv => false,
            Operator::Mod => false,
            Operator::UnsignedMod => false,
            Operator::Eq => false,
            Operator::NotEq => false,
            Operator::Gt => false,
            Operator::UnsignedGt => false,
            Operator::Lt => false,
            Operator::UnsignedLt => false,
            Operator::Ge => false,
            Operator::UnsignedGe => false,
            Operator::Le => false,
            Operator::UnsignedLe => false,
            Operator::LeftShift => false,
            Operator::RightShift => false,
            Operator::ArithmeticRightShift => false,
            Operator::LogicalAnd => false,
            Operator::LogicalOr => false,
            Operator::LogicalXor => false,
            Operator::LogicalNot => false,
            Operator::BitwiseAnd => false,
            Operator::BitwiseOr => false,
            Operator::BitwiseXor => false,
            Operator::ReduceAnd => false,
            Operator::ReduceOr => false,
            Operator::ReduceXor => false,
            Operator::USub => false,
            Operator::Not => false,
            Operator::ReadPort => true,
            Operator::BitwiseNot => false,
            Operator::Bitreverse => false,
            Operator::DivPow2 => false,
            Operator::Gray2Bin { .. } => false,
            Operator::SignExtend { .. } => false,
            Operator::ZeroExtend { .. } => false,
            Operator::Truncate => false,
            Operator::Concat => false,
            Operator::Select => false,
            Operator::Match => false,
            Operator::ConstructArray => false,
            Operator::DeclClockedMemory { .. } => false,
            Operator::IndexArray => false,
            Operator::IndexMemory => false,
            Operator::RangeIndexArray { .. } => false,
            Operator::RangeIndexBits { .. } => false,
            Operator::ConstructTuple => true,
            Operator::ConstructEnum { .. } => true,
            Operator::IsEnumVariant { .. } => true,
            Operator::EnumMember { .. } => true,
            Operator::IndexTuple(_, _) => true,
            Operator::FlipPort => true,
            Operator::ReadMutWires => true,
            Operator::Instance { .. } => true,
            Operator::Alias => true,
            Operator::Nop => true,
        }
    }
}

impl std::fmt::Display for Operator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Operator::Add => write!(f, "Add"),
            Operator::UnsignedAdd => write!(f, "UnsignedAdd"),
            Operator::Sub => write!(f, "Sub"),
            Operator::UnsignedSub => write!(f, "UnsignedSub"),
            Operator::Mul => write!(f, "Mul"),
            Operator::UnsignedMul => write!(f, "UnsignedMul"),
            Operator::Div => write!(f, "Div"),
            Operator::UnsignedDiv => write!(f, "UnsignedDiv"),
            Operator::Mod => write!(f, "Mod"),
            Operator::UnsignedMod => write!(f, "UnsignedMod"),
            Operator::Eq => write!(f, "Eq"),
            Operator::NotEq => write!(f, "NotEq"),
            Operator::Gt => write!(f, "Gt"),
            Operator::UnsignedGt => write!(f, "UnsignedGt"),
            Operator::Lt => write!(f, "Lt"),
            Operator::UnsignedLt => write!(f, "UnsignedLt"),
            Operator::Ge => write!(f, "Ge"),
            Operator::UnsignedGe => write!(f, "UnsignedGe"),
            Operator::Le => write!(f, "Le"),
            Operator::UnsignedLe => write!(f, "UnsignedLe"),
            Operator::RightShift => write!(f, "RightShift"),
            Operator::ArithmeticRightShift => write!(f, "ArithmeticRightShift"),
            Operator::LogicalAnd => write!(f, "LogicalAnd"),
            Operator::LogicalOr => write!(f, "LogicalOr"),
            Operator::LogicalXor => write!(f, "LogicalXor"),
            Operator::LogicalNot => write!(f, "LogicalNot"),
            Operator::BitwiseAnd => write!(f, "BitwiseAnd"),
            Operator::BitwiseOr => write!(f, "BitwiseOr"),
            Operator::BitwiseNot => write!(f, "BitwiseNot"),
            Operator::BitwiseXor => write!(f, "BitwiseXor"),
            Operator::ReduceAnd => write!(f, "ReduceAnd"),
            Operator::ReduceOr => write!(f, "ReduceOr"),
            Operator::ReduceXor => write!(f, "ReduceXor"),
            Operator::Bitreverse => write!(f, "Bitreverse"),
            Operator::USub => write!(f, "USub"),
            Operator::Not => write!(f, "Not"),
            Operator::Select => write!(f, "Select"),
            Operator::Match => write!(f, "Match"),
            Operator::LeftShift => write!(f, "LeftShift"),
            Operator::DivPow2 => write!(f, "DivPow2"),
            Operator::Gray2Bin { num_bits } => write!(f, "Gray2Bin({num_bits})"),
            Operator::SignExtend {
                extra_bits,
                operand_size,
            } => write!(f, "SignExtend({extra_bits}, {operand_size})"),
            Operator::ZeroExtend { extra_bits } => write!(f, "ZeroExtend({extra_bits})"),
            Operator::Truncate => write!(f, "Truncate"),
            Operator::Concat => write!(f, "Concat"),
            Operator::ConstructEnum {
                variant,
                variant_count,
            } => write!(f, "ConstructEnum({}, {})", variant, variant_count),
            Operator::IsEnumVariant {
                variant,
                enum_type: _,
            } => write!(f, "IsEnumVariant({})", variant),
            Operator::EnumMember {
                variant,
                member_index,
                enum_type: _,
            } => write!(f, "EnumMember({} {})", variant, member_index),
            Operator::ConstructTuple => write!(f, "ConstructTuple"),
            Operator::ConstructArray => write!(f, "ConstructArray"),
            Operator::DeclClockedMemory {
                write_ports,
                addr_w,
                inner_w,
                elems,
                initial,
            } => write!(
                f,
                "DeclClockedMemory({write_ports}, {addr_w}, {inner_w}, {elems}{})",
                if let Some(values) = initial {
                    format!(
                        ", [{}]",
                        values
                            .iter()
                            .map(|v| format!("[{}]", v.iter().map(|v| format!("{v}")).join(", ")))
                            .join(", ")
                    )
                } else {
                    String::new()
                }
            ),
            Operator::IndexArray => write!(f, "IndexArray"),
            Operator::IndexTuple(idx, ty) => write!(f, "IndexTuple({}, {ty:?})", idx),
            Operator::RangeIndexArray {
                start,
                end_exclusive: end,
            } => write!(f, "RangeIndexArray({start}, {end})"),
            Operator::RangeIndexBits {
                start,
                end_exclusive: end,
            } => write!(f, "RangeIndexBits({start}, {end})"),
            Operator::IndexMemory => write!(f, "IndexMemory"),
            Operator::Instance { name, .. } => write!(f, "Instance({})", name.as_verilog()),
            Operator::Alias => write!(f, "Alias"),
            Operator::FlipPort => write!(f, "FlipPort"),
            Operator::ReadMutWires => write!(f, "ReadMutWires"),
            Operator::Nop => write!(f, "Nop"),
            Operator::ReadPort => write!(f, "ReadPort"),
        }
    }
}

#[derive(Clone, PartialEq, Debug)]
pub struct Binding {
    pub name: ValueName,
    pub operator: Operator,
    pub operands: Vec<ValueName>,
    pub ty: Type,
    pub loc: Option<Loc<()>>,
}

impl std::fmt::Display for Binding {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Binding {
            name,
            operator,
            operands,
            ty,
            loc: _,
        } = self;
        write!(
            f,
            "let {name}: {ty} = {operator}({})",
            operands.iter().map(|op| format!("{op}")).join(", ")
        )
    }
}

#[derive(Clone, PartialEq, Debug)]
pub struct Register {
    pub name: ValueName,
    pub ty: Type,
    pub clock: ValueName,
    pub reset: Option<(ValueName, ValueName)>,
    pub initial: Option<Vec<Statement>>,
    pub value: ValueName,
    pub loc: Option<Loc<()>>,
    /// True if this register corresponds to an fsm with the specified ValueName
    /// as the actual state
    pub traced: Option<ValueName>,
}

impl std::fmt::Display for Register {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Register {
            name,
            ty,
            clock,
            reset,
            initial,
            value,
            loc: _,
            traced: _,
        } = self;

        let reset = reset
            .as_ref()
            .map(|(trig, val)| format!("({trig}, {val})"))
            .unwrap_or_else(String::new);

        let initial = initial
            .as_ref()
            .map(|i| format!("initial({})", i.iter().map(|s| format!("{s}")).join("; ")))
            .unwrap_or_else(String::new);

        write!(f, "reg({clock}) {name}: {ty}{reset}{initial} = {value}")
    }
}

#[derive(Clone, PartialEq, Debug)]
pub enum Statement {
    Binding(Binding),
    Register(Register),
    /// A constant expression with the specified ID and value
    Constant(u64, Type, ConstantValue),
    Assert(Loc<ValueName>),
    Set {
        target: Loc<ValueName>,
        value: Loc<ValueName>,
    },
    /// This is a tracing signal as part of the value `name`. It is used for
    /// both individual fields if `#[wal_traceable]` and `#[wal_trace]` is used,
    /// and whole signals if `#[wal_suffix]` is used
    /// I.e. the result of
    /// ```
    /// #[wal_traceable(suffix) struct T {a: A, b: B}
    ///
    /// let x: T = ...`
    /// ```
    ///
    /// Will be
    /// (e(0); IndexStruct(0); x)
    /// (wal_trace {name: x, val: e(0), suffix: _a_suffix, ty: A}
    /// (e(1); IndexStruct(1); x)
    /// (wal_trace {name: x, val: e(0), suffix: _a_suffix, ty: A}
    WalTrace {
        name: ValueName,
        val: ValueName,
        suffix: String,
        ty: Type,
    },
}

impl std::fmt::Display for Statement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Statement::Binding(b) => write!(f, "{b}"),
            Statement::Register(r) => write!(f, "{r}"),
            Statement::Constant(id, ty, val) => write!(f, "const e{id}: {ty} = {val}"),
            Statement::Assert(val) => write!(f, "assert {val}"),
            Statement::Set { target, value } => write!(f, "set {target} = {value}"),
            Statement::WalTrace {
                name,
                val,
                suffix,
                ty: _,
            } => write!(f, "wal_trace({name}, {val}, {suffix})"),
        }
    }
}

#[derive(Clone, PartialEq, Debug)]
pub struct MirInput {
    pub name: String,
    pub val_name: ValueName,
    pub ty: Type,
    pub no_mangle: Option<Loc<()>>,
}
#[derive(Clone, PartialEq, Debug)]
pub struct Entity {
    /// The name of the module
    pub name: UnitName,
    /// A module input which is called `.1` externally and `.2` internally in the module
    pub inputs: Vec<MirInput>,
    pub output: ValueName,
    pub output_type: Type,
    pub statements: Vec<Statement>,
}

impl std::fmt::Display for Entity {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Entity {
            name,
            inputs,
            output,
            output_type,
            statements,
        } = self;

        let inputs = inputs
            .iter()
            .map(
                |MirInput {
                     name,
                     val_name,
                     ty,
                     no_mangle,
                 }| {
                    format!(
                        "({}{name}, {val_name}, {ty})",
                        no_mangle.map(|_| "#[no_mangle]").unwrap_or("")
                    )
                },
            )
            .join(", ");

        let statements = statements.iter().map(|s| format!("\t{s}\n")).join("");

        writeln!(
            f,
            "entity {name}({inputs}) -> {output_type} {{",
            name = name.as_verilog()
        )?;
        write!(f, "{statements}")?;
        write!(f, "}} => {output}")
    }
}
