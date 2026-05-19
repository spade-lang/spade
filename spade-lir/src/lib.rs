use derive_where::derive_where;
use itertools::Itertools;
use num::BigUint;

use serde::{Deserialize, Serialize};
use spade_common::location_info::Loc;

pub(crate) use spade_mir::ConstantValue;
use spade_mir as mir;

#[derive(Clone, Debug, Serialize, Deserialize, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum ValueName {
    Forward(mir::ValueName),
    Backward(mir::ValueName),
    OutputFwd,
    OutputBack,
}
impl std::fmt::Display for ValueName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ValueName::Forward(value_name) => write!(f, "{value_name}"),
            ValueName::Backward(value_name) => write!(f, "back({value_name})"),
            ValueName::OutputFwd => write!(f, "__output"),
            ValueName::OutputBack => write!(f, "__input"),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Type {
    BitVector(BigUint),
    InOut(Box<Type>),
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::BitVector(size) => {
                write!(f, "bits[{}]", size)
            }
            Type::InOut(inner) => {
                write!(f, "inout({})", inner)
            }
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct ParamName {
    pub name: String,
    pub no_mangle: Option<Loc<()>>,
}

#[derive_where(PartialEq, Eq, Hash)]
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
    ReadWriteItemsInOut(BigUint),
    BitwiseNot,
    // Divide op[0] by 2**op[1] rounding towards 0
    DivPow2,
    Concat,
    Slice,
    RangeSlice(BigUint, BigUint),

    /// Select [1] if [0] else [2]
    Select,
    /// Create a mutable array which is modified on the rising edge of the first argument.
    /// the second argument is an array of (write enable, write address, write data) tuples
    /// which update the array.
    DeclClockedMemory {
        /// Initial values for the memory. Must be const evaluatable
        initial: Option<Vec<Vec<Statement>>>,
    },

    /// Inverts the direction of all bits of a port. I.e. the forward ports
    /// become backward ports. This is only valid when converting from T to ~T
    FlipPort,

    /// Instantiation of another module with the specified name. The operands are passed
    /// by name to the entity. The operand name mapping is decided by the `argument_names` field of
    /// this variant. The first operand gets mapped to the first argument name, and so on.
    /// The target module can only have a single output which must be the last argument.
    /// The location of the instantiation is optional but can be passed to improve
    /// critical path report readability
    Instance {
        name: mir::UnitName,
        params: Vec<(String, ConstantValue)>,
        /// The names of the arguments in the same order as the operands.
        /// For instance, if the `i`th argument name is "foo" and the `i`th [`Binding`] is
        /// `my_port`, the verilog module will be instantiated with `.foo(my_port)`.
        argument_names: Vec<ParamName>,
        #[derive_where(skip)]
        loc: Option<Loc<()>>,
        verilog_attr_groups: Vec<Vec<(String, Option<String>)>>,
    },
    /// Alias another named value
    Alias,
    /// Like `Alias`, but don't attempt to replace the aliased name with another
    BlackBoxAlias,
    /// Define a variable for the value but don't do anything with it. Useful for creating ports
    Nop,
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
            Operator::USub => write!(f, "USub"),
            Operator::Not => write!(f, "Not"),
            Operator::Select => write!(f, "Select"),
            Operator::LeftShift => write!(f, "LeftShift"),
            Operator::DivPow2 => write!(f, "DivPow2"),
            Operator::Concat => write!(f, "Concat"),
            Operator::Slice => write!(f, "Slice"),
            Operator::RangeSlice(start, end) => write!(f, "RangeSlice({start}, {end})"),
            Operator::DeclClockedMemory { initial } => write!(
                f,
                "DeclClockedMemory({})",
                if let Some(values) = initial {
                    format!(
                        "[{}]",
                        values
                            .iter()
                            .map(|v| format!("[{}]", v.iter().map(|v| format!("{v}")).join(", ")))
                            .join(", ")
                    )
                } else {
                    "None".to_owned()
                }
            ),
            Operator::Instance { name, .. } => write!(f, "Instance({})", name.as_verilog()),
            Operator::Alias => write!(f, "Alias"),
            Operator::BlackBoxAlias => write!(f, "BlackBoxAlias"),
            Operator::FlipPort => write!(f, "FlipPort"),
            Operator::Nop => write!(f, "Nop"),
            Operator::ReadWriteItemsInOut(n) => write!(f, "ReadWriteInOut({})", n),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
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

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
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

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Statement {
    Binding(Binding),
    Register(Register),
    /// A constant expression with the specified ID and value
    Constant(ValueName, Type, ConstantValue),
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
    Error,
}

impl std::fmt::Display for Statement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Statement::Binding(b) => write!(f, "{b}"),
            Statement::Register(r) => write!(f, "{r}"),
            Statement::Constant(id, ty, val) => write!(f, "const {id}: {ty} = {val}"),
            Statement::Assert(val) => write!(f, "assert {val}"),
            Statement::Set { target, value } => write!(f, "set {target} = {value}"),
            Statement::WalTrace {
                name,
                val,
                suffix,
                ty: _,
            } => write!(f, "wal_trace({name}, {val}, {suffix})"),
            Statement::Error => write!(f, "Error"),
        }
    }
}

#[derive(Clone, PartialEq, Debug)]
pub struct LirArg {
    pub name: String,
    pub val_name: ValueName,
    pub ty: Type,
    pub no_mangle: Option<Loc<()>>,
}


#[derive(Clone, PartialEq, Debug)]
pub struct Entity {
    /// The name of the module
    pub name: mir::UnitName,
    /// A module input which is called `.1` externally and `.2` internally in the module
    pub arguments: Vec<LirArg>,
    pub verilog_attr_groups: Vec<Vec<(String, Option<String>)>>,
    pub statements: Vec<Statement>,
    pub inline: bool,
}

impl std::fmt::Display for Entity {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Entity {
            name,
            arguments,
            statements,
            verilog_attr_groups,
            inline,
        } = self;

        let inputs = arguments
            .iter()
            .map(
                |LirArg {
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

        for attrs in verilog_attr_groups {
            let contents = attrs
                .iter()
                .map(|(key, value)| match value {
                    Some(v) => format!("{key} = {v:?}"),
                    None => key.clone(),
                })
                .join(",");

            writeln!(f, "#[verilog_attrs({contents})]")?;
        }

        writeln!(
            f,
            "{inline}entity {name}({inputs}) {{",
            name = name.as_verilog(),
            inline = if *inline { "inline " } else { "" }
        )?;
        write!(f, "{statements}")?;
        write!(f, "}}")
    }
}
