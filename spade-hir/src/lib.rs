pub mod expression;

use spade_common::{
    location_info::{Loc, WithLocation},
    name::{Identifier, NameID},
};
use spade_types as types;

pub use expression::{Argument, ArgumentKind, ExprKind, Expression};

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
pub enum Statement {
    Binding(Loc<NameID>, Option<Loc<TypeSpec>>, Loc<Expression>),
    Register(Loc<Register>),
}
impl WithLocation for Statement {}

#[derive(PartialEq, Debug, Clone)]
pub struct Register {
    pub name: Loc<NameID>,
    pub clock: Loc<Expression>,
    pub reset: Option<(Loc<Expression>, Loc<Expression>)>,
    pub value: Loc<Expression>,
    pub value_type: Option<Loc<TypeSpec>>,
}
impl WithLocation for Register {}

#[derive(PartialEq, Debug, Clone)]
pub enum TypeParam {
    TypeName,
    Integer,
}
impl WithLocation for TypeParam {}

#[derive(PartialEq, Debug, Clone)]
pub enum TypeExpression {
    /// An integer value
    Integer(u128),
    /// Another type
    TypeSpec(TypeSpec),
}
impl WithLocation for TypeExpression {}

#[derive(PartialEq, Debug, Clone)]
/// The type is not unit with 0 or more type parameters. The amount of type parameters is
/// checked by the type checker.
pub enum TypeSpec {
    /// The type is a fixed known type with 0 or more type parameters
    Concrete(Loc<types::BaseType>, Vec<Loc<TypeExpression>>),
    /// The type is a generic type parameter visible in the current scope
    Generic(NameID),
    /// The type is a tuple of other variables
    Tuple(Vec<Loc<TypeSpec>>),
}
impl WithLocation for TypeSpec {}

// Quick functions for creating types wihtout typing so much
impl TypeSpec {
    pub fn unit() -> Self {
        TypeSpec::Concrete(types::BaseType::Unit.nowhere(), vec![])
    }

    pub fn int(size: u128) -> Self {
        TypeSpec::Concrete(
            types::BaseType::Int.nowhere(),
            vec![TypeExpression::Integer(size).nowhere()],
        )
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct Entity {
    pub name: Loc<NameID>,
    pub head: EntityHead,
    pub inputs: Vec<(NameID, Loc<TypeSpec>)>,
    pub body: Loc<Expression>,
}
impl WithLocation for Entity {}

#[derive(PartialEq, Debug, Clone)]
pub struct EntityHead {
    pub inputs: Vec<(Loc<Identifier>, Loc<TypeSpec>)>,
    pub output_type: Option<Loc<TypeSpec>>,
    pub type_params: Vec<Identifier>,
}
impl EntityHead {
    // Look up the type of an argument. Panics if no such argument exists
    pub fn arg_type(&self, name: &Identifier) -> TypeSpec {
        for (arg, ty) in &self.inputs {
            if &arg.inner == name {
                return ty.inner.clone();
            }
        }
        panic!(
            "Tried to get type of an argument which is not part of the entity. {}",
            name
        )
    }
}
impl WithLocation for EntityHead {}

/// Items are things typically present at the top level of a module such as
/// entities, pipelines, submodules etc.
#[derive(PartialEq, Debug, Clone)]
pub enum Item {
    Entity(Loc<Entity>),
}
impl WithLocation for Item {}

#[derive(PartialEq, Debug, Clone)]
pub struct ModuleBody {
    pub members: Vec<Item>,
}
