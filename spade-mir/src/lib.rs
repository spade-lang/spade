mod aliasing;
mod assertion_codegen;
pub mod codegen;
pub mod diff;
pub mod diff_printing;
mod enum_util;
pub mod eval;
pub mod macros;
mod type_list;
pub mod types;
mod verilog;

use derivative::Derivative;
use itertools::Itertools;

use spade_common::location_info::{Loc, WithLocation};
use types::Type;

#[derive(Clone, PartialEq, Debug)]
pub enum ConstantValue {
    Int(u64),
    Bool(bool),
}

impl std::fmt::Display for ConstantValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConstantValue::Int(val) => write!(f, "{val}"),
            ConstantValue::Bool(val) => write!(f, "{val}"),
        }
    }
}

/// A name of a value. Can either come from the NameID of the underlying
/// variable, or the id of the underlying expression
#[derive(Clone, PartialEq, Debug, Hash, Eq)]
pub enum ValueName {
    /// A named value in the code with with an index to make that name globally unique
    /// In the resulting verilog, this is translated as _n_$id_$name
    Named(u64, String),
    // FIXME: Consider renaming this since it's now used for both patterns and expressions
    /// An un-named expression. In the resulting verilog, this is called _e_$id
    Expr(u64),
}

impl WithLocation for ValueName {}

impl std::fmt::Display for ValueName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ValueName::Named(id, s) => write!(f, "{s}_n{id}"),
            ValueName::Expr(id) => write!(f, "e{id}"),
        }
    }
}

#[derive(Derivative)]
#[derivative(PartialEq)]
#[derive(Clone, Debug)]
pub enum Operator {
    /// Binary arithmetic operators
    Add,
    Sub,
    Mul,
    Eq,
    Gt,
    Lt,
    Ge,
    Le,
    LeftShift,
    RightShift,
    LogicalAnd,
    LogicalOr,
    LogicalXor,
    LogicalNot,
    BitwiseAnd,
    BitwiseOr,
    BitwiseXor,
    USub,
    Not,
    BitwiseNot,
    // Divide op[0] by 2**op[1] rounding towards 0
    DivPow2,
    /// Sign extend the first operand with the provided amount of extra bits
    SignExtend {
        extra_bits: u64,
        operand_size: u64,
    },
    ZeroExtend {
        extra_bits: u64,
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
        write_ports: u64,
        /// Width of the write address
        addr_w: u64,
        /// Number of elements in the array
        inner_w: u64,
        /// Number of elements in the array
        elems: u64,
    },
    /// Index an array with elements of the specified size
    IndexArray,
    IndexMemory,
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
    /// Get the `.0`th element of a tuple. The types of the elements are specified
    /// in the second argument
    IndexTuple(u64, Vec<Type>),
    /// Instantiation of another module with the specified name. The operands are passed
    /// positionally to the entity. The target module can only have a single output which
    /// must be the last argument.
    /// The location of the instantiation is optional but can be passed to improve
    /// critical path report readability
    Instance(String, #[derivative(PartialEq = "ignore")] Option<Loc<()>>),
    /// Alias another named value
    Alias,
}

impl std::fmt::Display for Operator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Operator::Add => write!(f, "Add"),
            Operator::Sub => write!(f, "Sub"),
            Operator::Mul => write!(f, "Mul"),
            Operator::Eq => write!(f, "Eq"),
            Operator::Gt => write!(f, "Gt"),
            Operator::Lt => write!(f, "Lt"),
            Operator::Ge => write!(f, "Ge"),
            Operator::Le => write!(f, "Le"),
            Operator::RightShift => write!(f, "RightShift"),
            Operator::LogicalAnd => write!(f, "LogicalAnd"),
            Operator::LogicalOr => write!(f, "LogicalOr"),
            Operator::LogicalXor => write!(f, "LogicalXor"),
            Operator::LogicalNot => write!(f, "LogicalNot"),
            Operator::BitwiseAnd => write!(f, "BitwiseAnd"),
            Operator::BitwiseOr => write!(f, "BitwiseOr"),
            Operator::BitwiseNot => write!(f, "BitwiseNot"),
            Operator::BitwiseXor => write!(f, "BitwiseXor"),
            Operator::USub => write!(f, "USub"),
            Operator::Not => write!(f, "Not"),
            Operator::Select => write!(f, "Select"),
            Operator::Match => write!(f, "Match"),
            Operator::LeftShift => write!(f, "LeftShift"),
            Operator::DivPow2 => write!(f, "DivPow2"),
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
            } => write!(
                f,
                "DeclClockedMemory({write_ports}, {addr_w}, {inner_w}, {elems})"
            ),
            Operator::IndexArray => write!(f, "IndexArray"),
            Operator::IndexTuple(idx, _) => write!(f, "IndexTuple({})", idx),
            Operator::IndexMemory => write!(f, "IndexMemory"),
            Operator::Instance(name, _) => write!(f, "Instance({})", name),
            Operator::Alias => write!(f, "Alias"),
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
    pub value: ValueName,
    pub loc: Option<Loc<()>>,
}

impl std::fmt::Display for Register {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Register {
            name,
            ty,
            clock,
            reset,
            value,
            loc: _,
        } = self;

        let reset = reset
            .as_ref()
            .map(|(trig, val)| format!("({trig}, {val})"))
            .unwrap_or_else(String::new);

        write!(f, "reg({clock}) {name}: {ty}{reset} = {value}")
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
}

impl std::fmt::Display for Statement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Statement::Binding(b) => write!(f, "{b}"),
            Statement::Register(r) => write!(f, "{r}"),
            Statement::Constant(id, ty, val) => write!(f, "const e{id}: {ty} = {val}"),
            Statement::Assert(val) => write!(f, "assert {val}"),
            Statement::Set { target, value } => write!(f, "set {target} = {value}"),
        }
    }
}

#[derive(Clone, PartialEq, Debug)]
pub struct Entity {
    /// The name of the module
    pub name: String,
    /// A module input which is called `.1` externally and `.2` internally in the module
    pub inputs: Vec<(String, ValueName, Type)>,
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
            .map(|(name, val, ty)| format!("({name}, {val}, {ty})"))
            .join(", ");

        let statements = statements.iter().map(|s| format!("\t{s}\n")).join("");

        writeln!(f, "entity {name}({inputs}) -> {output_type} {{")?;
        write!(f, "{statements}")?;
        write!(f, "}} => {output}")
    }
}
