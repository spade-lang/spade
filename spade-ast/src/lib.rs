use spade_common::{
    location_info::{Loc, WithLocation},
    name::{Identifier, Path},
};

pub mod testutil;

#[derive(PartialEq, Debug, Clone)]
pub enum TypeExpression {
    TypeSpec(Box<Loc<TypeSpec>>),
    Integer(u128),
}
impl WithLocation for TypeExpression {}

/// A specification of a type to be used. For example, the types of input/output arguments the type
/// of fields in a struct etc.
#[derive(PartialEq, Debug, Clone)]
pub enum TypeSpec {
    Tuple(Vec<Loc<TypeSpec>>),
    Array {
        inner: Box<Loc<TypeSpec>>,
        size: Box<Loc<TypeExpression>>,
    },
    Named(Loc<Path>, Vec<Loc<TypeExpression>>),
    Unit(Loc<()>),
    /// A type in which signals travel in the opposite direction to normal. Any type containing a
    /// Backward type is considered a port, meaning it can not be explicitly put in registers, and
    /// is not registered in pipelines
    Backward(Box<Loc<TypeSpec>>),
}
impl WithLocation for TypeSpec {}

#[derive(PartialEq, Debug, Clone)]
pub enum ArgumentPattern {
    Named(Vec<(Loc<Identifier>, Option<Loc<Pattern>>)>),
    Positional(Vec<Loc<Pattern>>),
}
impl WithLocation for ArgumentPattern {}

#[derive(PartialEq, Debug, Clone)]
pub enum Pattern {
    Integer(u128),
    Bool(bool),
    Path(Loc<Path>),
    Tuple(Vec<Loc<Pattern>>),
    Type(Loc<Path>, Loc<ArgumentPattern>),
}
impl WithLocation for Pattern {}

// Helper constructors for writing neater tests
impl Pattern {
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
    Equals,
    Lt,
    Gt,
    Le,
    Ge,
    LogicalAnd,
    LogicalOr,
    LogicalXor,
    LeftShift,
    RightShift,
    BitwiseAnd,
    BitwiseOr,
    BitwiseXor,
}

#[derive(PartialEq, Debug, Clone)]
pub enum UnaryOperator {
    Sub,
    Not,
    BitwiseNot,
}
impl WithLocation for UnaryOperator {}

#[derive(PartialEq, Debug, Clone)]
pub enum PipelineReference {
    Relative(Loc<i64>),
    Absolute(Loc<Identifier>),
}

#[derive(PartialEq, Debug, Clone)]
pub enum Expression {
    Identifier(Loc<Path>),
    IntLiteral(u128),
    BoolLiteral(bool),
    ArrayLiteral(Vec<Loc<Expression>>),
    Index(Box<Loc<Expression>>, Box<Loc<Expression>>),
    TupleLiteral(Vec<Loc<Expression>>),
    TupleIndex(Box<Loc<Expression>>, Loc<u128>),
    FieldAccess(Box<Loc<Expression>>, Loc<Identifier>),
    If(
        Box<Loc<Expression>>,
        Box<Loc<Expression>>,
        Box<Loc<Expression>>,
    ),
    Match(
        Box<Loc<Expression>>,
        Loc<Vec<(Loc<Pattern>, Loc<Expression>)>>,
    ),
    FnCall(Loc<Path>, Loc<ArgumentList>),
    UnaryOperator(UnaryOperator, Box<Loc<Expression>>),
    BinaryOperator(Box<Loc<Expression>>, BinaryOperator, Box<Loc<Expression>>),
    Block(Box<Block>),
    EntityInstance(Loc<Path>, Loc<ArgumentList>),
    PipelineInstance(Loc<u128>, Loc<Path>, Loc<ArgumentList>),
    PipelineReference(PipelineReference, Loc<Identifier>),
}
impl WithLocation for Expression {}

impl Expression {
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
            Expression::ArrayLiteral(_) => "array literal",
            Expression::Index(_, _) => "index",
            Expression::TupleLiteral(_) => "tuple literal",
            Expression::TupleIndex(_, _) => "tuple index",
            Expression::FieldAccess(_, _) => "field access",
            Expression::If(_, _, _) => "if",
            Expression::Match(_, _) => "match",
            Expression::FnCall(_, _) => "fn call",
            Expression::UnaryOperator(_, _) => "unary operator",
            Expression::BinaryOperator(_, _, _) => "binary operator",
            Expression::Block(_) => "block",
            Expression::EntityInstance(_, _) => "entity instance",
            Expression::PipelineInstance(_, _, _) => "pipeline instance",
            Expression::PipelineReference(_, _) => "pipeline reference",
        }
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct Block {
    pub statements: Vec<Loc<Statement>>,
    pub result: Loc<Expression>,
}
impl WithLocation for Block {}

#[derive(PartialEq, Debug, Clone)]
pub enum Statement {
    Label(Loc<Identifier>),
    Declaration(Vec<Loc<Identifier>>),
    Binding(Loc<Pattern>, Option<Loc<TypeSpec>>, Loc<Expression>),
    PipelineRegMarker(usize),
    Register(Loc<Register>),
    /// Sets the value of the target expression, which must be a Backward port to
    /// the value of `value`
    Set {
        target: Loc<Expression>,
        value: Loc<Expression>,
    },
    Assert(Loc<Expression>),
}
impl WithLocation for Statement {}

/// A generic type parameter
#[derive(PartialEq, Debug, Clone)]
pub enum TypeParam {
    TypeName(Loc<Identifier>),
    Integer(Loc<Identifier>),
}
impl WithLocation for TypeParam {}
impl TypeParam {
    pub fn name(&self) -> &Loc<Identifier> {
        match self {
            TypeParam::TypeName(n) => n,
            TypeParam::Integer(n) => n,
        }
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct AttributeList(pub Vec<Loc<Identifier>>);
impl AttributeList {
    pub fn empty() -> Self {
        Self(vec![])
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct ParameterList(pub Vec<(Loc<Identifier>, Loc<TypeSpec>)>);

#[derive(PartialEq, Debug, Clone)]
pub struct Entity {
    pub attributes: AttributeList,
    /// Since functions and entities are so similar, we'll make them share everything
    /// and just have a bool here to indicate the type.
    pub is_function: bool,
    pub name: Loc<Identifier>,
    pub inputs: ParameterList,
    pub output_type: Option<Loc<TypeSpec>>,
    /// The body is an expression for ID assignment purposes, but semantic analysis
    /// ensures that it is always a block. If body is `None`, the entity is __builtin__
    pub body: Option<Loc<Expression>>,
    pub type_params: Vec<Loc<TypeParam>>,
}
impl WithLocation for Entity {}

#[derive(PartialEq, Debug, Clone)]
pub struct Pipeline {
    pub attributes: AttributeList,
    pub depth: Loc<u128>,
    pub name: Loc<Identifier>,
    pub inputs: ParameterList,
    pub output_type: Option<Loc<TypeSpec>>,
    /// The body is an expression for ID assignment purposes, but semantic analysis
    /// ensures that it is always a block. If body is `None`, the entity is __builtin__
    pub body: Option<Loc<Expression>>,
    pub type_params: Vec<Loc<TypeParam>>,
}
impl WithLocation for Pipeline {}

/// A definition of a function without a body.
#[derive(PartialEq, Debug, Clone)]
pub struct FunctionDecl {
    pub name: Loc<Identifier>,
    pub self_arg: Option<Loc<()>>,
    pub inputs: ParameterList,
    pub return_type: Option<Loc<TypeSpec>>,
    pub type_params: Vec<Loc<TypeParam>>,
}
impl WithLocation for FunctionDecl {}

#[derive(PartialEq, Debug, Clone)]
pub struct Register {
    pub pattern: Loc<Pattern>,
    pub clock: Loc<Expression>,
    pub reset: Option<(Loc<Expression>, Loc<Expression>)>,
    pub value: Loc<Expression>,
    pub value_type: Option<Loc<TypeSpec>>,
}
impl WithLocation for Register {}

/// A definition of a trait
#[derive(PartialEq, Debug, Clone)]
pub struct TraitDef {
    pub name: Loc<Identifier>,
    pub functions: Vec<Loc<FunctionDecl>>,
}
impl WithLocation for TraitDef {}

/// Declaration of an enum
#[derive(PartialEq, Debug, Clone)]
pub struct Enum {
    pub name: Loc<Identifier>,
    pub options: Vec<(Loc<Identifier>, Option<ParameterList>)>,
}
impl WithLocation for Enum {}

#[derive(PartialEq, Debug, Clone)]
pub struct Struct {
    pub name: Loc<Identifier>,
    pub members: ParameterList,
}
impl WithLocation for Struct {}

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

/// Items are things typically present at the top level of a module such as
/// entities, pipelines, submodules etc.
#[derive(PartialEq, Debug, Clone)]
pub enum Item {
    Entity(Loc<Entity>),
    Pipeline(Loc<Pipeline>),
    TraitDef(Loc<TraitDef>),
    Type(Loc<TypeDeclaration>),
    Module(Loc<Module>),
    Use(Loc<UseStatement>),
}
impl WithLocation for Item {}

impl Item {
    pub fn name(&self) -> Option<&Identifier> {
        match self {
            Item::Entity(e) => Some(&e.name.inner),
            Item::Pipeline(p) => Some(&p.name.inner),
            Item::TraitDef(t) => Some(&t.name.inner),
            Item::Type(t) => Some(&t.name.inner),
            Item::Module(m) => Some(&m.name.inner),
            Item::Use(u) => u.alias.as_ref().map(|name| &name.inner),
        }
    }

    pub fn variant_str(&self) -> &'static str {
        match self {
            Item::Entity(_) => "entity",
            Item::Pipeline(_) => "pipeline",
            Item::TraitDef(_) => "trait definition",
            Item::Type(_) => "type",
            Item::Module(_) => "module",
            Item::Use(_) => "use",
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
