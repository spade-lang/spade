pub mod expression;
pub mod symbol_table;
pub mod testutil;
pub mod util;

use std::collections::HashMap;

pub use expression::{Argument, ArgumentKind, ExprKind, Expression};
use spade_common::{
    location_info::{Loc, WithLocation},
    name::{Identifier, NameID},
};
use spade_types::PrimitiveType;

/**
  Representation of the language with most language constructs still present, with
  more correctness guaranatees than the AST, such as types actually existing.
*/

#[derive(PartialEq, Debug, Clone)]
pub struct Block {
    pub statements: Vec<Loc<Statement>>,
    pub result: Loc<Expression>,
}
impl WithLocation for Block {}

#[derive(PartialEq, Debug, Clone)]
pub struct PatternArgument {
    pub target: Loc<Identifier>,
    pub value: Loc<Pattern>,
    pub kind: ArgumentKind,
}
impl WithLocation for PatternArgument {}

#[derive(PartialEq, Debug, Clone)]
pub enum PatternKind {
    Integer(u128),
    Bool(bool),
    Name {
        name: Loc<NameID>,
        pre_declared: bool,
    },
    Tuple(Vec<Loc<Pattern>>),
    /// Instantiation of an entity. While the argument contains information about
    /// argument names, for codegen purposes, the arguments must be ordered in
    /// the target order. I.e. they should all act as positioanl arguments
    Type(Loc<NameID>, Vec<PatternArgument>),
}
impl PatternKind {
    pub fn name(name: Loc<NameID>) -> Self {
        PatternKind::Name {
            name,
            pre_declared: false,
        }
    }
}
impl PatternKind {
    pub fn with_id(self, id: u64) -> Pattern {
        Pattern { id, kind: self }
    }

    pub fn idless(self) -> Pattern {
        Pattern { id: 0, kind: self }
    }
}

#[derive(Debug, Clone)]
pub struct Pattern {
    // Unique ID of the pattern for use in type inference. Shared with expressions
    // meaning there are no expression/pattern id collisions
    pub id: u64,
    pub kind: PatternKind,
}
impl WithLocation for Pattern {}

impl Pattern {
    pub fn get_names(&self) -> Vec<NameID> {
        match &self.kind {
            PatternKind::Integer(_) => vec![],
            PatternKind::Bool(_) => vec![],
            PatternKind::Name {
                name,
                pre_declared: _,
            } => vec![name.inner.clone()],
            PatternKind::Tuple(inner) => inner.iter().map(|i| i.get_names()).flatten().collect(),
            PatternKind::Type(_, args) => args
                .iter()
                .map(|arg| arg.value.get_names())
                .flatten()
                .collect(),
        }
    }
}

impl PartialEq for Pattern {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind
    }
}

#[derive(PartialEq, Debug, Clone)]
pub enum Statement {
    Binding(Loc<Pattern>, Option<Loc<TypeSpec>>, Loc<Expression>),
    Register(Loc<Register>),
    Declaration(Vec<Loc<NameID>>),
    PipelineRegMarker,
    Label(Loc<Identifier>),
}
impl WithLocation for Statement {}

impl Statement {
    /// NOTE: For use in tests
    pub fn named_let(pattern_id: u64, name_id: Loc<NameID>, val: Expression) -> Self {
        Self::Binding(
            PatternKind::name(name_id).with_id(pattern_id).nowhere(),
            None,
            val.nowhere(),
        )
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct Register {
    pub pattern: Loc<Pattern>,
    pub clock: Loc<Expression>,
    pub reset: Option<(Loc<Expression>, Loc<Expression>)>,
    pub value: Loc<Expression>,
    pub value_type: Option<Loc<TypeSpec>>,
}
impl WithLocation for Register {}

/// Type params have both an identifier and a NameID since they go through the
/// ast lowering process in a few separate steps, and the identifier needs to be
/// re-added to the symtab multiple times
#[derive(PartialEq, Debug, Clone, Hash, Eq)]
pub enum TypeParam {
    TypeName(Identifier, NameID),
    Integer(Identifier, NameID),
}
impl WithLocation for TypeParam {}
impl TypeParam {
    pub fn name_id(&self) -> NameID {
        match self {
            TypeParam::TypeName(_, n) => n.clone(),
            TypeParam::Integer(_, n) => n.clone(),
        }
    }
}

#[derive(PartialEq, Debug, Clone)]
pub enum TypeExpression {
    /// An integer value
    Integer(u128),
    /// A type that fits all integer between two bounds (inclusive..exclusive).
    IntegerRange(u128, u128),
    /// Another type
    TypeSpec(TypeSpec),
}
impl WithLocation for TypeExpression {}

/// A specification of a type to be used. For example, the types of input/output arguments the type
/// of fields in a struct etc.
#[derive(PartialEq, Debug, Clone)]
pub enum TypeSpec {
    /// The type is a declared type (struct, enum, typedef etc.) with n arguments
    Declared(Loc<NameID>, Vec<Loc<TypeExpression>>),
    /// The type is a generic argument visible in the current scope
    Generic(Loc<NameID>),
    /// The type is a tuple of other variables
    Tuple(Vec<Loc<TypeSpec>>),
    Array {
        inner: Box<Loc<TypeSpec>>,
        size: Box<Loc<TypeExpression>>,
    },
    Unit(Loc<()>),
}
impl WithLocation for TypeSpec {}

// Quick functions for creating types wihtout typing so much
impl TypeSpec {
    pub fn unit() -> Self {
        TypeSpec::Unit(().nowhere())
    }
}

/// Declaration of an enum
#[derive(PartialEq, Debug, Clone)]
pub struct Enum {
    pub options: Vec<(Loc<NameID>, ParameterList)>,
}
impl WithLocation for Enum {}

#[derive(PartialEq, Debug, Clone)]
pub struct Struct {
    pub members: ParameterList,
}
impl WithLocation for Struct {}

#[derive(PartialEq, Debug, Clone)]
pub enum TypeDeclKind {
    Enum(Loc<Enum>),
    Primitive(PrimitiveType),
    Struct(Loc<Struct>),
}

/// A declaration of a new type
#[derive(PartialEq, Debug, Clone)]
pub struct TypeDeclaration {
    pub name: Loc<NameID>,
    pub kind: TypeDeclKind,
    pub generic_args: Vec<Loc<TypeParam>>,
}
impl WithLocation for TypeDeclaration {}

#[derive(PartialEq, Debug, Clone)]
pub struct Entity {
    pub name: Loc<NameID>,
    pub head: EntityHead,
    // This is needed here because the head does not have NameIDs
    pub inputs: Vec<(NameID, Loc<TypeSpec>)>,
    pub body: Loc<Expression>,
}
impl WithLocation for Entity {}

#[derive(PartialEq, Debug, Clone)]
pub struct ParameterList(pub Vec<(Loc<Identifier>, Loc<TypeSpec>)>);
impl WithLocation for ParameterList {}

impl ParameterList {
    pub fn argument_num(&self) -> usize {
        self.0.len()
    }

    /// Look up the type of an argument. Panics if no such argument exists
    pub fn arg_type(&self, name: &Identifier) -> TypeSpec {
        if let Some(result) = self.try_get_arg_type(name) {
            result
        } else {
            panic!(
                "Tried to get type of an argument which is not part of the parameter list. {}",
                name
            )
        }
    }

    /// Look up the type of an argument, returning None if no such argument exists
    pub fn try_get_arg_type(&self, name: &Identifier) -> Option<TypeSpec> {
        for (arg, ty) in &self.0 {
            if &arg.inner == name {
                return Some(ty.inner.clone());
            }
        }
        None
    }

    pub fn arg_index(&self, target: &Identifier) -> Option<usize> {
        let indices = self
            .0
            .iter()
            .enumerate()
            .filter_map(
                |(i, (name, _))| {
                    if &name.inner == target {
                        Some(i)
                    } else {
                        None
                    }
                },
            )
            .collect::<Vec<_>>();

        if indices.len() > 1 {
            panic!("Duplicate arguments with the same name")
        } else {
            indices.first().cloned()
        }
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct FunctionHead {
    pub inputs: ParameterList,
    pub output_type: Option<Loc<TypeSpec>>,
    pub type_params: Vec<Loc<TypeParam>>,
}
impl WithLocation for FunctionHead {}

#[derive(PartialEq, Debug, Clone)]
pub struct EntityHead {
    pub inputs: ParameterList,
    pub output_type: Option<Loc<TypeSpec>>,
    pub type_params: Vec<Loc<TypeParam>>,
}
impl WithLocation for EntityHead {}

#[derive(PartialEq, Debug, Clone)]
pub struct PipelineHead {
    pub depth: Loc<usize>,
    pub inputs: ParameterList,
    pub output_type: Option<Loc<TypeSpec>>,
    pub type_params: Vec<Loc<TypeParam>>,
}
impl WithLocation for PipelineHead {}

pub trait FunctionLike {
    fn inputs<'a>(&'a self) -> &'a ParameterList;
    fn output_type<'a>(&'a self) -> &'a Option<Loc<TypeSpec>>;
    fn type_params<'a>(&'a self) -> &'a [Loc<TypeParam>];
}

macro_rules! impl_function_like {
    ($($for:ident),*) => {
        $(
            impl FunctionLike for $for {
                fn inputs<'a>(&'a self) -> &'a ParameterList {
                    &self.inputs
                }
                fn output_type<'a>(&'a self) -> &'a Option<Loc<TypeSpec>> {
                    &self.output_type
                }
                fn type_params<'a>(&'a self) -> &'a [Loc<TypeParam>] {
                    &self.type_params
                }
            }
        )*
    }
}

impl_function_like!(EntityHead, FunctionHead, PipelineHead);

#[derive(PartialEq, Debug, Clone)]
pub struct Pipeline {
    pub head: PipelineHead,
    pub name: Loc<NameID>,
    // This is needed here because the head does not have NameIDs
    pub inputs: Vec<(NameID, Loc<TypeSpec>)>,
    pub body: Loc<Expression>,
}
impl WithLocation for Pipeline {}

#[derive(PartialEq, Debug, Clone)]
pub enum Item {
    Entity(Loc<Entity>),
    Pipeline(Loc<Pipeline>),
}

/// Items which have associated code that can be executed. This is different from
/// type declarations which are items, but which do not have code on their own
#[derive(PartialEq, Debug, Clone)]
pub enum ExecutableItem {
    EnumInstance { base_enum: NameID, variant: usize },
    StructInstance,
    Entity(Loc<Entity>),
    Pipeline(Loc<Pipeline>),
}
impl WithLocation for ExecutableItem {}

pub type TypeList = HashMap<NameID, Loc<TypeDeclaration>>;

/// A list of all the items present in the whole AST, flattened to remove module
/// hirearchies.
///
/// That is, `mod a { mod b{ entity X {} } } will result in members containing `a::b::X`, but the
/// modules will not be present
#[derive(PartialEq, Debug, Clone)]
pub struct ItemList {
    pub executables: HashMap<NameID, ExecutableItem>,
    pub types: TypeList,
}

impl ItemList {
    pub fn new() -> Self {
        Self {
            executables: HashMap::new(),
            types: TypeList::new(),
        }
    }
}
