pub mod codegen;
mod name_map;
pub mod pretty_print;
mod type_list;
mod verilog;
pub mod passes;

use itertools::Itertools;
use num::BigUint;

use serde::{Deserialize, Serialize};
use spade_common::{id_tracker::ExprIdTracker, location_info::Loc};

use spade_diagnostics::Diagnostic;
pub(crate) use spade_mir::ConstantValue;
use spade_mir::{self as mir, UnitName};

type Result<T> = std::result::Result<T, Diagnostic>;

#[derive(Clone, Debug, Serialize, Deserialize, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum ValueName {
    Forward(mir::ValueName),
    Backward(mir::ValueName),
    OutputFwd,
    OutputBack,
}

impl ValueName {
    pub fn new_fwd(idtracker: &ExprIdTracker) -> Self {
        Self::Forward(mir::ValueName::Expr(idtracker.next()))
    }
    pub fn new_back(idtracker: &ExprIdTracker) -> Self {
        Self::Backward(mir::ValueName::Expr(idtracker.next()))
    }
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

impl Type {
    pub fn unit() -> Self {
        Type::BitVector(BigUint::ZERO)
    }

    pub fn size(&self) -> BigUint {
        match self {
            Type::BitVector(s) => s.clone(),
            Type::InOut(inner) => inner.size(),
        }
    }
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::BitVector(size) => {
                write!(f, "bits<{}>", size)
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

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
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
    /// Slice `op[0]` at a runtime offset of `op[1]`, i.e. `op[0][op[0]..op[0] + elem_size]`
    /// If reversed is true, the 0th index is at the msb of the target rather than the lsb, i.e.
    /// `op[0](size - op[0] - elem_size .. size - op[0])
    Slice {
        elem_size: BigUint,
        reversed: bool,
    },
    RangeSlice {
        start: BigUint,
        end_exclusive: BigUint,
    },
    /// Replicate [0] `copies` times
    Replicate {
        copies: BigUint,
    },

    /// Select [1] if [0] else [2]
    Select,
    /// Corresponds to a match statement. If value [0] is true, select [1], if [2] holds, select
    /// [3] and so on. Values are priorotized in order, i.e. if both [0] and [2] hold, [1] is
    /// selected
    // NOTE: We may want to add a MatchUnique for cases where we can guarantee uniqueness,
    // typically match statements with no wildcards
    Match,

    /// Create a mutable array which is modified on the rising edge of the first argument.
    /// the second argument is an array of (write enable, write address, write data) tuples
    /// which update the array.
    DeclClockedMemory {
        /// Initial values for the memory. Must be const evaluatable
        initial: Option<Vec<Vec<Statement>>>,
    },

    /// Alias another named value
    Alias,
    /// Like `Alias`, but don't attempt to replace the aliased name with another
    BlackBoxAlias,

    Back(BackOperator),

    /// Define a variable for the value but don't do anything with it. Useful for creating ports
    Nop,
}

/// When compiling something like
///
/// ```spade
/// let x: (int<4>, inv bool);
/// let y: (int<4>, inv uint<8>);
/// let z = (x, y);
/// ```
///
/// the MIR for Z will be roughly
///
/// ```spade
/// let z = Concat(x, y);
/// ```
///
/// The LIR forward direction is easy, it will simply be
/// ```spade
/// let z = Concat(x, y);
/// ```
/// But the back direction is more tricky. It should be
/// ```spade
/// let back(x) = back(z)[0];
/// let back(y) = back(z)[1..9];
/// ```
/// However, dealing with this logic for each individual Spade construct is annoying. Therefore,
/// the LIR has a few backward operators called `BackX`, for example, `BackConcat`. Mir Lowering will
/// generate
///
/// ```spade
/// let z = Concat(x, y);
/// let back(z) = BackConcat(back(x), back(y));
/// ```
///
/// and the `backflip` pass will transform these operators into the underlying forward indexing
/// operators. This must be done before legalization and removes all `BackXYZ` operators.
#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub enum BackOperator {
    Concat,
    Alias,
    BlackBoxAlias,
    RangeSlice {
        start: BigUint,
        end_exclusive: BigUint,
    },
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
            Operator::Match => write!(f, "Match"),
            Operator::LeftShift => write!(f, "LeftShift"),
            Operator::DivPow2 => write!(f, "DivPow2"),
            Operator::Concat => write!(f, "Concat"),
            Operator::Slice {
                elem_size,
                reversed,
            } => write!(f, "Slice({elem_size}, {reversed})"),
            Operator::Replicate { copies } => write!(f, "Replicate({copies})"),
            Operator::RangeSlice {
                start,
                end_exclusive,
            } => write!(f, "RangeSlice({start}, {end_exclusive})"),
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
            Operator::Alias => write!(f, "Alias"),
            Operator::BlackBoxAlias => write!(f, "BlackBoxAlias"),
            Operator::Back(BackOperator::Concat) => write!(f, "BackConcat"),
            Operator::Back(BackOperator::RangeSlice { start, end_exclusive }) => {
                write!(f, "BackRangeSlice({start}, {end_exclusive})")
            }
            Operator::Back(BackOperator::BlackBoxAlias) => write!(f, "BackBlackBoxAlias"),
            Operator::Back(BackOperator::Alias) => write!(f, "Alias"),
            Operator::Nop => write!(f, "Nop"),
            Operator::ReadWriteItemsInOut(n) => write!(f, "ReadWriteInOut({})", n),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Binding {
    pub name: ValueName,
    pub operator: Operator,
    pub operands: Vec<Loc<ValueName>>,
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

    Instance {
        name: UnitName,
        params: Vec<(String, ConstantValue)>,

        inputs: Vec<(String, Type, Loc<ValueName>)>,
        outputs: Vec<(String, Type, Loc<ValueName>)>,

        verilog_attr_groups: Vec<Vec<(String, Option<String>)>>,
    },

    Error,
}

#[derive(Clone, PartialEq, Debug)]
pub struct LirArg {
    pub name: String,
    pub val_name: Loc<ValueName>,
    pub ty: Type,
    pub no_mangle: Option<Loc<()>>,
}

#[derive(Clone, PartialEq, Debug)]
pub struct Entity {
    /// The name of the module
    pub name: mir::UnitName,
    pub inputs: Vec<LirArg>,
    pub outputs: Vec<LirArg>,
    pub verilog_attr_groups: Vec<Vec<(String, Option<String>)>>,
    pub statements: Vec<Loc<Statement>>,
    pub inline: bool,
}
