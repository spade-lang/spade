use comptime::{ComptimeCondition, MaybeComptime};
use itertools::Itertools;
use num::{BigInt, BigUint, Zero};
use spade_common::{
    location_info::{Loc, WithLocation},
    name::{Identifier, Path},
    num_ext::InfallibleToBigInt,
};

pub mod comptime;
pub mod testutil;

#[derive(PartialEq, Debug, Clone)]
pub enum TypeExpression {
    TypeSpec(Box<Loc<TypeSpec>>),
    Integer(BigUint),
}
impl WithLocation for TypeExpression {}

impl std::fmt::Display for TypeExpression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeExpression::TypeSpec(s) => write!(f, "{s}"),
            TypeExpression::Integer(i) => write!(f, "{i}"),
        }
    }
}

#[derive(PartialEq, Debug, Clone)]
pub enum NamedTurbofish {
    Short(Loc<Identifier>),
    Full(Loc<Identifier>, Loc<TypeExpression>),
}
impl WithLocation for NamedTurbofish {}

#[derive(PartialEq, Debug, Clone)]
pub enum TurbofishInner {
    Named(Vec<Loc<NamedTurbofish>>),
    Positional(Vec<Loc<TypeExpression>>),
}
impl WithLocation for TurbofishInner {}

/// A specification of a type to be used. For example, the types of input/output arguments the type
/// of fields in a struct etc.
#[derive(PartialEq, Debug, Clone)]
pub enum TypeSpec {
    Tuple(Vec<Loc<TypeSpec>>),
    Array {
        inner: Box<Loc<TypeSpec>>,
        size: Box<Loc<TypeExpression>>,
    },
    Named(Loc<Path>, Option<Loc<Vec<Loc<TypeExpression>>>>),
    Unit(Loc<()>),
    /// A type in which signals travel in the opposite direction to normal. Any type containing a
    /// Backward type is considered a port, meaning it cannot be explicitly put in registers, and
    /// is not registered in pipelines
    Backward(Box<Loc<TypeSpec>>),
    /// An inverted port. Turns `&mut T` into `&T` and `&T` into `&mut T`
    Inverted(Box<Loc<TypeSpec>>),
    Wire(Box<Loc<TypeSpec>>),
}
impl WithLocation for TypeSpec {}

impl std::fmt::Display for TypeSpec {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeSpec::Tuple(inner) => {
                write!(f, "({})", inner.iter().map(|i| format!("{i}")).join(", "))
            }
            TypeSpec::Array { inner, size } => write!(f, "[{inner};{size}]"),
            TypeSpec::Named(name, params) => {
                if params.is_some() {
                    write!(
                        f,
                        "{name}<{}>",
                        params
                            .as_ref()
                            .map(|p| p.iter().map(|p| format!("{p}")).join(", "))
                            .unwrap_or_default()
                    )
                } else {
                    write!(f, "{name}")
                }
            }
            TypeSpec::Unit(_) => write!(f, "()"),
            TypeSpec::Backward(inner) => write!(f, "&mut {inner}"),
            TypeSpec::Inverted(inner) => write!(f, "~{inner}"),
            TypeSpec::Wire(inner) => write!(f, "&{inner}"),
        }
    }
}

#[derive(PartialEq, Debug, Clone)]
pub enum ArgumentPattern {
    Named(Vec<(Loc<Identifier>, Option<Loc<Pattern>>)>),
    Positional(Vec<Loc<Pattern>>),
}
impl WithLocation for ArgumentPattern {}

#[derive(PartialEq, Debug, Clone)]
pub enum Pattern {
    Integer(IntLiteral),
    Bool(bool),
    Path(Loc<Path>),
    Tuple(Vec<Loc<Pattern>>),
    Type(Loc<Path>, Loc<ArgumentPattern>),
}
impl WithLocation for Pattern {}

// Helper constructors for writing neater tests
impl Pattern {
    pub fn integer(val: i32) -> Self {
        Pattern::Integer(IntLiteral::Unsized(val.to_bigint()))
    }
    pub fn name(name: &str) -> Loc<Self> {
        Pattern::Path(Path(vec![Identifier(name.to_string()).nowhere()]).nowhere()).nowhere()
    }
}

#[derive(PartialEq, Debug, Clone)]
pub enum NamedArgument {
    Full(Loc<Identifier>, Loc<Expression>),
    /// Binds a local variable to an argument with the same name
    Short(Loc<Identifier>),
}
impl WithLocation for NamedArgument {}

#[derive(PartialEq, Debug, Clone)]
pub enum ArgumentList {
    Positional(Vec<Loc<Expression>>),
    Named(Vec<NamedArgument>),
}
impl WithLocation for ArgumentList {}

#[derive(PartialEq, Debug, Clone)]
pub enum BinaryOperator {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Equals,
    NotEquals,
    Lt,
    Gt,
    Le,
    Ge,
    LogicalAnd,
    LogicalOr,
    LogicalXor,
    LeftShift,
    RightShift,
    ArithmeticRightShift,
    BitwiseAnd,
    BitwiseOr,
    BitwiseXor,
}
impl WithLocation for BinaryOperator {}

impl std::fmt::Display for BinaryOperator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BinaryOperator::Add => write!(f, "+"),
            BinaryOperator::Sub => write!(f, "-"),
            BinaryOperator::Mul => write!(f, "*"),
            BinaryOperator::Div => write!(f, "/"),
            BinaryOperator::Mod => write!(f, "%"),
            BinaryOperator::Equals => write!(f, "=="),
            BinaryOperator::NotEquals => write!(f, "!="),
            BinaryOperator::Lt => write!(f, "<"),
            BinaryOperator::Gt => write!(f, ">"),
            BinaryOperator::Le => write!(f, "<="),
            BinaryOperator::Ge => write!(f, ">="),
            BinaryOperator::LogicalAnd => write!(f, "&"),
            BinaryOperator::LogicalOr => write!(f, "|"),
            BinaryOperator::LogicalXor => write!(f, "^"),
            BinaryOperator::LeftShift => write!(f, "<<"),
            BinaryOperator::RightShift => write!(f, ">>"),
            BinaryOperator::ArithmeticRightShift => write!(f, ">>>"),
            BinaryOperator::BitwiseAnd => write!(f, "&&"),
            BinaryOperator::BitwiseOr => write!(f, "||"),
            BinaryOperator::BitwiseXor => write!(f, "^^"),
        }
    }
}

#[derive(PartialEq, Debug, Clone)]
pub enum UnaryOperator {
    Sub,
    Not,
    BitwiseNot,
    Dereference,
    Reference,
}
impl WithLocation for UnaryOperator {}

#[derive(PartialEq, Debug, Clone)]
pub enum PipelineStageReference {
    Relative(Loc<BigInt>),
    Absolute(Loc<Identifier>),
}

#[derive(PartialEq, Debug, Clone)]
pub enum CallKind {
    Function,
    Entity(Loc<()>),
    Pipeline(Loc<()>, Loc<MaybeComptime<Loc<IntLiteral>>>),
}
impl WithLocation for CallKind {}

#[derive(PartialEq, Debug, Clone)]
pub enum BitLiteral {
    Low,
    High,
    HighImp,
}
impl WithLocation for BitLiteral {}

#[derive(PartialEq, Debug, Clone)]
pub enum Expression {
    Identifier(Loc<Path>),
    IntLiteral(IntLiteral),
    BoolLiteral(bool),
    BitLiteral(BitLiteral),
    ArrayLiteral(Vec<Loc<Expression>>),
    Index(Box<Loc<Expression>>, Box<Loc<Expression>>),
    RangeIndex {
        target: Box<Loc<Expression>>,
        start: Loc<BigUint>,
        end: Loc<BigUint>,
    },
    TupleLiteral(Vec<Loc<Expression>>),
    TupleIndex(Box<Loc<Expression>>, Loc<u128>),
    FieldAccess(Box<Loc<Expression>>, Loc<Identifier>),
    CreatePorts,
    Call {
        kind: CallKind,
        callee: Loc<Path>,
        args: Loc<ArgumentList>,
        turbofish: Option<Loc<TurbofishInner>>,
    },
    MethodCall {
        target: Box<Loc<Expression>>,
        name: Loc<Identifier>,
        args: Loc<ArgumentList>,
        kind: CallKind,
    },
    If(
        Box<Loc<Expression>>,
        Box<Loc<Expression>>,
        Box<Loc<Expression>>,
    ),
    Match(
        Box<Loc<Expression>>,
        Loc<Vec<(Loc<Pattern>, Loc<Expression>)>>,
    ),
    UnaryOperator(UnaryOperator, Box<Loc<Expression>>),
    BinaryOperator(
        Box<Loc<Expression>>,
        Loc<BinaryOperator>,
        Box<Loc<Expression>>,
    ),
    Block(Box<Block>),
    /// E.g. `stage(-5).x`, `stage('b).y`
    PipelineReference {
        /// ```text
        /// stage(-5).xyz
        /// ^^^^^^^^^
        /// ```
        stage_kw_and_reference_loc: Loc<()>,
        /// ```text
        /// stage(-5).xyz
        ///       ^^
        /// ```
        stage: PipelineStageReference,
        /// ```text
        /// stage(-5).xyz
        ///           ^^^
        /// ```
        name: Loc<Identifier>,
    },
    StageValid,
    StageReady,
    Comptime(Box<Loc<ComptimeCondition<Loc<Expression>>>>),
}
impl WithLocation for Expression {}

impl Expression {
    pub fn int_literal_signed(val: i32) -> Self {
        Self::IntLiteral(IntLiteral::unsized_(val))
    }

    pub fn as_int_literal(self) -> Option<IntLiteral> {
        match self {
            Expression::IntLiteral(lit) => Some(lit),
            _ => None,
        }
    }

    pub fn is_usub_int_literal(&self) -> bool {
        match self {
            Expression::UnaryOperator(UnaryOperator::Sub, e) => {
                matches!(e.inner, Expression::IntLiteral(_))
            }
            _ => false,
        }
    }

    pub fn assume_block(&self) -> &Block {
        if let Expression::Block(inner) = self {
            inner
        } else {
            panic!("Expected block")
        }
    }

    pub fn variant_str(&self) -> &'static str {
        match self {
            Expression::Identifier(_) => "identifier",
            Expression::IntLiteral(_) => "int literal",
            Expression::BoolLiteral(_) => "bool literal",
            Expression::BitLiteral(_) => "bit literal",
            Expression::ArrayLiteral(_) => "array literal",
            Expression::CreatePorts => "port",
            Expression::Index(_, _) => "index",
            Expression::RangeIndex { .. } => "range index",
            Expression::TupleLiteral(_) => "tuple literal",
            Expression::TupleIndex(_, _) => "tuple index",
            Expression::FieldAccess(_, _) => "field access",
            Expression::If(_, _, _) => "if",
            Expression::Match(_, _) => "match",
            Expression::Call { .. } => "call",
            Expression::MethodCall { .. } => "method call",
            Expression::UnaryOperator(_, _) => "unary operator",
            Expression::BinaryOperator(_, _, _) => "binary operator",
            Expression::Block(_) => "block",
            Expression::PipelineReference { .. } => "pipeline reference",
            Expression::StageValid => "stage.valid",
            Expression::StageReady => "stage.ready",
            Expression::Comptime { .. } => "comptime",
        }
    }
}

/// An integer literal, which may or may not have been suffixed with `U` to indicate
/// it being an unsigned literal.
#[derive(PartialEq, Debug, Clone)]
pub enum IntLiteral {
    Unsized(BigInt),
    Signed { val: BigInt, size: BigUint },
    Unsigned { val: BigUint, size: BigUint },
}
impl WithLocation for IntLiteral {}

impl IntLiteral {
    pub fn unsized_(val: i32) -> IntLiteral {
        IntLiteral::Unsized(val.to_bigint())
    }

    /// Returns this number as a signed number. Unsigned numbers are losslessly converted to
    /// signed
    pub fn as_signed(self) -> BigInt {
        match self {
            IntLiteral::Signed { val, size: _ } => val,
            IntLiteral::Unsigned { val, size: _ } => val.to_bigint(),
            IntLiteral::Unsized(val) => val,
        }
    }

    // Returns the signed, or unsigned number as a BigUint if it is positive, otherwise,
    // None
    pub fn as_unsigned(self) -> Option<BigUint> {
        match self {
            IntLiteral::Signed { val, size: _ } | IntLiteral::Unsized(val) => {
                if val >= BigInt::zero() {
                    Some(val.to_biguint().unwrap())
                } else {
                    None
                }
            }
            IntLiteral::Unsigned { val, size: _ } => Some(val),
        }
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct Block {
    pub statements: Vec<Loc<Statement>>,
    pub result: Option<Loc<Expression>>,
}
impl WithLocation for Block {}

#[derive(PartialEq, Debug, Clone)]
pub struct Binding {
    pub pattern: Loc<Pattern>,
    pub ty: Option<Loc<TypeSpec>>,
    pub value: Loc<Expression>,
    pub attrs: AttributeList,
}

#[derive(PartialEq, Debug, Clone)]
pub enum Statement {
    Label(Loc<Identifier>),
    Declaration(Vec<Loc<Identifier>>),
    Binding(Binding),
    PipelineRegMarker(Option<Loc<usize>>, Option<Loc<Expression>>),
    Register(Loc<Register>),
    /// Sets the value of the target expression, which must be a Backward port to
    /// the value of `value`
    Set {
        target: Loc<Expression>,
        value: Loc<Expression>,
    },
    Assert(Loc<Expression>),
    Comptime(ComptimeCondition<Vec<Loc<Statement>>>),
}
impl WithLocation for Statement {}

impl Statement {
    // Creates a binding from name, type and values without any attributes.
    pub fn binding(
        pattern: Loc<Pattern>,
        ty: Option<Loc<TypeSpec>>,
        value: Loc<Expression>,
    ) -> Self {
        Self::Binding(Binding {
            pattern,
            ty,
            value,
            attrs: AttributeList::empty(),
        })
    }
}

/// A generic type parameter
#[derive(PartialEq, Debug, Clone)]
pub enum TypeParam {
    TypeName {
        name: Loc<Identifier>,
        traits: Vec<Loc<Path>>,
    },
    Integer(Loc<Identifier>),
}
impl WithLocation for TypeParam {}
impl TypeParam {
    pub fn name(&self) -> &Loc<Identifier> {
        match self {
            TypeParam::TypeName { name, traits: _ } => name,
            TypeParam::Integer(n) => n,
        }
    }
}

#[derive(PartialEq, Debug, Clone)]
pub enum Attribute {
    Optimize {
        passes: Vec<Loc<String>>,
    },
    NoMangle,
    Fsm {
        state: Option<Loc<Identifier>>,
    },
    WalTraceable {
        suffix: Option<Loc<Identifier>>,
        uses_clk: bool,
        uses_rst: bool,
    },
    WalTrace {
        clk: Option<Loc<Expression>>,
        rst: Option<Loc<Expression>>,
    },
    /// Create a copy of the marked signal with the specified suffix applied
    WalSuffix {
        suffix: Loc<Identifier>,
    },
}

impl Attribute {
    pub fn name(&self) -> &str {
        match self {
            Attribute::Optimize { passes: _ } => "optimize",
            Attribute::NoMangle => "no_mangle",
            Attribute::Fsm { state: _ } => "fsm",
            Attribute::WalTraceable { .. } => "wal_traceable",
            Attribute::WalTrace { .. } => "wal_trace",
            Attribute::WalSuffix { .. } => "wal_suffix",
        }
    }
}

impl WithLocation for Attribute {}

#[derive(PartialEq, Debug, Clone)]
pub struct AttributeList(pub Vec<Loc<Attribute>>);
impl AttributeList {
    pub fn empty() -> Self {
        Self(vec![])
    }

    pub fn from_vec(attrs: Vec<Loc<Attribute>>) -> Self {
        Self(attrs)
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct ParameterList {
    pub self_: Option<Loc<()>>,
    pub args: Vec<(AttributeList, Loc<Identifier>, Loc<TypeSpec>)>,
}
impl WithLocation for ParameterList {}

impl ParameterList {
    pub fn without_self(args: Vec<(Loc<Identifier>, Loc<TypeSpec>)>) -> Self {
        Self {
            self_: None,
            args: args
                .into_iter()
                .map(|(n, t)| (AttributeList::empty(), n, t))
                .collect(),
        }
    }

    pub fn with_self(self_: Loc<()>, args: Vec<(Loc<Identifier>, Loc<TypeSpec>)>) -> Self {
        Self {
            self_: Some(self_),
            args: args
                .into_iter()
                .map(|(n, t)| (AttributeList::empty(), n, t))
                .collect(),
        }
    }
}

#[derive(PartialEq, Debug, Clone)]
pub enum UnitKind {
    Function,
    Entity,
    Pipeline(Loc<MaybeComptime<Loc<IntLiteral>>>),
}
impl WithLocation for UnitKind {}

impl UnitKind {
    pub fn is_pipeline(&self) -> bool {
        match self {
            UnitKind::Function => false,
            UnitKind::Entity => false,
            UnitKind::Pipeline(_) => true,
        }
    }
}

impl std::fmt::Display for UnitKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            UnitKind::Function => write!(f, "fn"),
            UnitKind::Entity => write!(f, "entity"),
            UnitKind::Pipeline(_) => write!(f, "pipeline"),
        }
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct UnitHead {
    pub attributes: AttributeList,
    pub unit_kind: Loc<UnitKind>,
    pub name: Loc<Identifier>,
    pub inputs: Loc<ParameterList>,
    pub output_type: Option<Loc<TypeSpec>>,
    pub type_params: Vec<Loc<TypeParam>>,
    pub where_clauses: Vec<(Loc<Path>, Loc<Expression>)>,
}
impl WithLocation for UnitHead {}

#[derive(PartialEq, Debug, Clone)]
pub struct Unit {
    pub head: UnitHead,
    /// The body is an expression for ID assignment purposes, but semantic analysis
    /// ensures that it is always a block. If body is `None`, the entity is __builtin__
    pub body: Option<Loc<Expression>>,
}
impl WithLocation for Unit {}

#[derive(PartialEq, Debug, Clone)]
pub struct Register {
    pub pattern: Loc<Pattern>,
    pub clock: Loc<Expression>,
    pub reset: Option<(Loc<Expression>, Loc<Expression>)>,
    pub initial: Option<Loc<Expression>>,
    pub value: Loc<Expression>,
    pub value_type: Option<Loc<TypeSpec>>,
    pub attributes: AttributeList,
}
impl WithLocation for Register {}

/// A definition of a trait
#[derive(PartialEq, Debug, Clone)]
pub struct TraitDef {
    pub name: Loc<Identifier>,
    pub methods: Vec<Loc<UnitHead>>,
}
impl WithLocation for TraitDef {}

#[derive(PartialEq, Debug, Clone)]
pub struct ImplBlock {
    pub type_params: Option<Vec<Loc<TypeParam>>>,
    pub r#trait: Option<Loc<TypeSpec>>,
    pub target: Loc<TypeSpec>,
    pub units: Vec<Loc<Unit>>,
}
impl WithLocation for ImplBlock {}

/// Declaration of an enum
#[derive(PartialEq, Debug, Clone)]
pub struct Enum {
    pub name: Loc<Identifier>,
    pub options: Vec<(Loc<Identifier>, Option<Loc<ParameterList>>)>,
}
impl WithLocation for Enum {}

#[derive(PartialEq, Debug, Clone)]
pub struct Struct {
    pub attributes: AttributeList,
    pub name: Loc<Identifier>,
    pub members: Loc<ParameterList>,
    pub port_keyword: Option<Loc<()>>,
}
impl WithLocation for Struct {}

impl Struct {
    pub fn is_port(&self) -> bool {
        self.port_keyword.is_some()
    }
}

#[derive(PartialEq, Debug, Clone)]
pub enum TypeDeclKind {
    Enum(Loc<Enum>),
    Struct(Loc<Struct>),
}

/// A declaration of a new type
#[derive(PartialEq, Debug, Clone)]
pub struct TypeDeclaration {
    pub name: Loc<Identifier>,
    pub kind: TypeDeclKind,
    pub generic_args: Vec<Loc<TypeParam>>,
}
impl WithLocation for TypeDeclaration {}

#[derive(PartialEq, Debug, Clone)]
pub struct UseStatement {
    pub path: Loc<Path>,
    pub alias: Option<Loc<Identifier>>,
}
impl WithLocation for UseStatement {}

#[derive(PartialEq, Debug, Clone)]
pub struct ComptimeConfig {
    pub name: Loc<Identifier>,
    pub val: Loc<BigInt>,
}
impl WithLocation for ComptimeConfig {}

/// Items are things typically present at the top level of a module such as
/// entities, pipelines, submodules etc.
#[derive(PartialEq, Debug, Clone)]
pub enum Item {
    Unit(Loc<Unit>),
    TraitDef(Loc<TraitDef>),
    Type(Loc<TypeDeclaration>),
    Module(Loc<Module>),
    Use(Loc<UseStatement>),
    Config(Loc<ComptimeConfig>),
    ImplBlock(Loc<ImplBlock>),
}
impl WithLocation for Item {}

impl Item {
    pub fn name(&self) -> Option<&Identifier> {
        match self {
            Item::Unit(u) => Some(&u.head.name.inner),
            Item::TraitDef(t) => Some(&t.name.inner),
            Item::Type(t) => Some(&t.name.inner),
            Item::Module(m) => Some(&m.name.inner),
            Item::Use(u) => u.alias.as_ref().map(|name| &name.inner),
            Item::Config(c) => Some(&c.name.inner),
            Item::ImplBlock(_) => None,
        }
    }

    pub fn variant_str(&self) -> &'static str {
        match self {
            Item::Unit(_) => "unit",
            Item::TraitDef(_) => "trait definition",
            Item::Type(_) => "type",
            Item::Module(_) => "module",
            Item::Use(_) => "use",
            Item::Config(_) => "config",
            Item::ImplBlock(_) => "impl",
        }
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct Module {
    pub name: Loc<Identifier>,
    pub body: Loc<ModuleBody>,
}
impl WithLocation for Module {}

#[derive(PartialEq, Debug, Clone)]
pub struct ModuleBody {
    pub members: Vec<Item>,
}
impl WithLocation for ModuleBody {}
