use std::borrow::BorrowMut;

use crate::{ConstGenericWithId, Pattern, TraitSpec, TypeExpression, TypeParam, UnitKind};

use super::{Block, NameID};
use num::{BigInt, BigUint};
use serde::{Deserialize, Serialize};
use spade_common::{
    id_tracker::ExprID,
    location_info::Loc,
    name::{Identifier, Path},
    num_ext::InfallibleToBigInt,
};

#[derive(Clone, Copy, PartialEq, Debug, Serialize, Deserialize)]
pub enum BinaryOperator {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    LeftShift,
    RightShift,
    ArithmeticRightShift,
}

impl std::fmt::Display for BinaryOperator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BinaryOperator::Add => write!(f, "+"),
            BinaryOperator::Sub => write!(f, "-"),
            BinaryOperator::Mul => write!(f, "*"),
            BinaryOperator::Div => write!(f, "/"),
            BinaryOperator::Mod => write!(f, "%"),
            BinaryOperator::LeftShift => write!(f, ">>"),
            BinaryOperator::RightShift => write!(f, "<<"),
            BinaryOperator::ArithmeticRightShift => write!(f, ">>>"),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Debug, Serialize, Deserialize)]
pub enum UnaryOperator {
    Sub,
    Not,
    BitwiseNot,
    Dereference,
    Reference,
}

impl std::fmt::Display for UnaryOperator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            UnaryOperator::Sub => write!(f, "-"),
            UnaryOperator::Not => write!(f, "!"),
            UnaryOperator::BitwiseNot => write!(f, "~"),
            UnaryOperator::Dereference => write!(f, "*"),
            UnaryOperator::Reference => write!(f, "&"),
        }
    }
}

// Named arguments are used for both type parameters in turbofishes and in argument lists. T is the
// right hand side of a binding, i.e. an expression in an argument list
#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub enum NamedArgument<T> {
    /// Binds the argument named LHS in the outer scope to the expression
    Full(Loc<Identifier>, Loc<T>),
    /// Binds a local variable to an argument with the same name
    Short(Loc<Identifier>, Loc<T>),
}

/// Specifies how an argument is bound. Mainly used for error reporting without
/// code duplication
#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub enum ArgumentKind {
    Positional,
    Named,
    ShortNamed,
}

#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub enum ArgumentList<T> {
    Named(Vec<NamedArgument<T>>),
    Positional(Vec<Loc<T>>),
}

impl<T> ArgumentList<T> {
    pub fn empty() -> Self {
        Self::Positional(vec![])
    }

    pub fn expressions(&self) -> Vec<&Loc<T>> {
        match self {
            ArgumentList::Named(n) => n
                .iter()
                .map(|arg| match &arg {
                    NamedArgument::Full(_, expr) => expr,
                    NamedArgument::Short(_, expr) => expr,
                })
                .collect(),
            ArgumentList::Positional(arg) => arg.iter().collect(),
        }
    }
    pub fn expressions_mut(&mut self) -> Vec<&mut Loc<T>> {
        match self {
            ArgumentList::Named(n) => n
                .iter_mut()
                .map(|arg| match arg {
                    NamedArgument::Full(_, expr) => expr,
                    NamedArgument::Short(_, expr) => expr,
                })
                .collect(),
            ArgumentList::Positional(arg) => arg.iter_mut().collect(),
        }
    }
}

#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub struct Argument<T> {
    pub target: Loc<Identifier>,
    pub value: Loc<T>,
    pub kind: ArgumentKind,
}

// FIXME: Migrate entity, pipeline and fn instantiation to this
#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub enum CallKind {
    Function,
    Entity(Loc<()>),
    Pipeline {
        inst_loc: Loc<()>,
        depth: Loc<TypeExpression>,
        /// An expression ID for which the type inferer will infer the depth of the instantiated
        /// pipeline, i.e. inst(<this>)
        depth_typeexpr_id: ExprID,
    },
}

#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub enum TriLiteral {
    Low,
    High,
    HighImp,
}

#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub enum IntLiteralKind {
    Unsized,
    Signed(BigUint),
    Unsigned(BigUint),
}

#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub enum PipelineRefKind {
    Absolute(Loc<NameID>),
    Relative(Loc<TypeExpression>),
}

#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub struct OuterLambdaParam {
    pub name_in_lambda: NameID,
    pub name_in_body: Loc<NameID>,
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, Serialize, Deserialize)]
pub enum Safety {
    Default,
    Unsafe,
}

#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub struct LambdaTypeParams {
    /// The parameters that will contain the types of each argument
    pub arg: Vec<Loc<TypeParam>>,
    pub output: Loc<TypeParam>,
    /// The parameters that will contain the types of the captured variables
    pub captures: Vec<Loc<TypeParam>>,
    /// The type parameters that are inherited from the unit in which the lambda is defined
    pub outer: Vec<Loc<TypeParam>>,
}

impl LambdaTypeParams {
    pub fn all(&self) -> impl Iterator<Item = &Loc<TypeParam>> {
        let Self {
            arg,
            output,
            captures,
            outer,
        } = self;
        arg.iter().chain(Some(output)).chain(captures).chain(outer)
    }
}

#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub enum ExprKind {
    Error,
    Identifier(NameID),
    IntLiteral(BigInt, IntLiteralKind),
    BoolLiteral(bool),
    TriLiteral(TriLiteral),
    TypeLevelBool(NameID),
    TypeLevelInteger(NameID),
    CreatePorts,
    TupleLiteral(Vec<Loc<Expression>>),
    ArrayLiteral(Vec<Loc<Expression>>),
    ArrayShorthandLiteral(Box<Loc<Expression>>, Loc<ConstGenericWithId>),
    Index(Box<Loc<Expression>>, Box<Loc<Expression>>),
    RangeIndex {
        target: Box<Loc<Expression>>,
        start: Loc<ConstGenericWithId>,
        end: Loc<ConstGenericWithId>,
    },
    TupleIndex(Box<Loc<Expression>>, Loc<u128>),
    FieldAccess(Box<Loc<Expression>>, Loc<Identifier>),
    MethodCall {
        target: Box<Loc<Expression>>,
        op_trait: Option<Loc<TraitSpec>>,
        name: Loc<Identifier>,
        args: Loc<ArgumentList<Expression>>,
        call_kind: CallKind,
        turbofish: Option<Loc<ArgumentList<TypeExpression>>>,
        safety: Safety,
    },
    Call {
        kind: CallKind,
        callee: Loc<NameID>,
        args: Loc<ArgumentList<Expression>>,
        turbofish: Option<Loc<ArgumentList<TypeExpression>>>,
        safety: Safety,
        verilog_attr_groups: Vec<Vec<(Loc<Identifier>, Option<Loc<String>>)>>,
    },
    BinaryOperator(
        Box<Loc<Expression>>,
        Loc<BinaryOperator>,
        Box<Loc<Expression>>,
    ),
    UnaryOperator(Loc<UnaryOperator>, Box<Loc<Expression>>),
    Match(
        Box<Loc<Expression>>,
        Vec<(Loc<Pattern>, Option<Loc<Expression>>, Loc<Expression>)>,
    ),
    Block(Box<Block>),
    If(
        Box<Loc<Expression>>,
        Box<Loc<Expression>>,
        Box<Loc<Expression>>,
    ),
    TypeLevelIf(
        // FIXME: Having a random u64 is not great, let's make TypeExpressions always have associated ids
        Loc<ConstGenericWithId>,
        Box<Loc<Expression>>,
        Box<Loc<Expression>>,
    ),
    PipelineRef {
        stage: Loc<PipelineRefKind>,
        name: Loc<NameID>,
        declares_name: bool,
        /// An expression ID which after typeinference will contain the absolute depth
        /// of this referenced value
        depth_typeexpr_id: ExprID,
    },
    LambdaDef {
        unit_kind: Loc<UnitKind>,
        /// The type that this lambda definition creates
        lambda_type: NameID,
        type_params: LambdaTypeParams,
        outer_generic_params: Vec<OuterLambdaParam>,
        /// The unit which is the `call` method on this lambda
        lambda_unit: NameID,
        arguments: Vec<Loc<Pattern>>,
        body: Box<Loc<Expression>>,
        clock: Option<Loc<NameID>>,
        captures: Vec<(Loc<Identifier>, Loc<NameID>)>,
    },
    StageValid,
    StageReady,
    StaticUnreachable(Loc<String>),
    // This is a special case expression which is never created in user code, but which can be used
    // in type inference to create virtual expressions with specific IDs
    Null,
}

impl ExprKind {
    pub fn with_id(self, id: ExprID) -> Expression {
        Expression { kind: self, id }
    }

    // FIXME: These really should be #[cfg(test)]'d away
    pub fn idless(self) -> Expression {
        Expression {
            kind: self,
            id: ExprID(0),
        }
    }

    pub fn int_literal(val: i32) -> Self {
        Self::IntLiteral(val.to_bigint(), IntLiteralKind::Unsized)
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Expression {
    pub kind: ExprKind,
    // This ID is used to associate types with the expression
    pub id: ExprID,
}

impl Expression {
    /// Create a new expression referencing an identifier with the specified
    /// id and name
    pub fn ident(expr_id: ExprID, name_id: u64, name: &str) -> Expression {
        ExprKind::Identifier(NameID(name_id, Path::from_strs(&[name]))).with_id(expr_id)
    }

    /// Returns the block that is this expression if it is a block, an error if it is an Error node, and panics if the expression is not a block or error
    pub fn assume_block(&self) -> std::result::Result<&Block, ()> {
        if let ExprKind::Block(ref block) = self.kind {
            Ok(block)
        } else if let ExprKind::Error = self.kind {
            Err(())
        } else {
            panic!("Expression is not a block")
        }
    }

    /// Returns the block that is this expression. Panics if the expression is not a block
    pub fn assume_block_mut(&mut self) -> &mut Block {
        if let ExprKind::Block(block) = &mut self.kind {
            block.borrow_mut()
        } else {
            panic!("Expression is not a block")
        }
    }
}

impl PartialEq for Expression {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind
    }
}
