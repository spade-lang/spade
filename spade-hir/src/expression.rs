use std::borrow::BorrowMut;

use crate::{ConstGenericWithId, Pattern, TypeExpression, TypeParam};

use super::{Block, NameID};
use num::{BigInt, BigUint};
use serde::{Deserialize, Serialize};
use spade_common::{
    id_tracker::ExprID,
    location_info::{Loc, WithLocation},
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
    Eq,
    NotEq,
    Gt,
    Lt,
    Ge,
    Le,
    LeftShift,
    RightShift,
    ArithmeticRightShift,
    LogicalAnd,
    LogicalOr,
    LogicalXor,
    BitwiseOr,
    BitwiseAnd,
    BitwiseXor,
}

impl std::fmt::Display for BinaryOperator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BinaryOperator::Add => write!(f, "+"),
            BinaryOperator::Sub => write!(f, "-"),
            BinaryOperator::Mul => write!(f, "*"),
            BinaryOperator::Div => write!(f, "/"),
            BinaryOperator::Mod => write!(f, "%"),
            BinaryOperator::Eq => write!(f, "=="),
            BinaryOperator::NotEq => write!(f, "!="),
            BinaryOperator::Gt => write!(f, ">"),
            BinaryOperator::Lt => write!(f, "<"),
            BinaryOperator::Ge => write!(f, ">="),
            BinaryOperator::Le => write!(f, "<="),
            BinaryOperator::LeftShift => write!(f, ">>"),
            BinaryOperator::RightShift => write!(f, "<<"),
            BinaryOperator::ArithmeticRightShift => write!(f, ">>>"),
            BinaryOperator::LogicalAnd => write!(f, "&&"),
            BinaryOperator::LogicalOr => write!(f, "||"),
            BinaryOperator::LogicalXor => write!(f, "^^"),
            BinaryOperator::BitwiseOr => write!(f, "|"),
            BinaryOperator::BitwiseAnd => write!(f, "&"),
            BinaryOperator::BitwiseXor => write!(f, "^"),
        }
    }
}
impl WithLocation for BinaryOperator {}

#[derive(Clone, Copy, PartialEq, Debug, Serialize, Deserialize)]
pub enum UnaryOperator {
    Sub,
    Not,
    BitwiseNot,
    Dereference,
    Reference,
}

impl WithLocation for UnaryOperator {}

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
    /// Binds the arguent named LHS in the outer scope to the expression
    Full(Loc<Identifier>, Loc<T>),
    /// Binds a local variable to an argument with the same name
    Short(Loc<Identifier>, Loc<T>),
}
impl<T> WithLocation for NamedArgument<T> {}

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
impl<T> WithLocation for ArgumentList<T> {}

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
impl WithLocation for CallKind {}

#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub enum BitLiteral {
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
impl WithLocation for PipelineRefKind {}

#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub struct CapturedLambdaParam {
    pub name_in_lambda: NameID,
    pub name_in_body: Loc<NameID>,
}

#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub enum ExprKind {
    Identifier(NameID),
    IntLiteral(BigInt, IntLiteralKind),
    BoolLiteral(bool),
    BitLiteral(BitLiteral),
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
        name: Loc<Identifier>,
        args: Loc<ArgumentList<Expression>>,
        call_kind: CallKind,
        turbofish: Option<Loc<ArgumentList<TypeExpression>>>,
    },
    Call {
        kind: CallKind,
        callee: Loc<NameID>,
        args: Loc<ArgumentList<Expression>>,
        turbofish: Option<Loc<ArgumentList<TypeExpression>>>,
    },
    BinaryOperator(
        Box<Loc<Expression>>,
        Loc<BinaryOperator>,
        Box<Loc<Expression>>,
    ),
    UnaryOperator(Loc<UnaryOperator>, Box<Loc<Expression>>),
    Match(Box<Loc<Expression>>, Vec<(Loc<Pattern>, Loc<Expression>)>),
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
        /// The type that this lambda definition creates
        lambda_type: NameID,
        lambda_type_params: Vec<Loc<TypeParam>>,
        captured_generic_params: Vec<CapturedLambdaParam>,
        /// The unit which is the `call` method on this lambda
        lambda_unit: NameID,
        arguments: Vec<Loc<Pattern>>,
        body: Box<Loc<Expression>>,
    },
    StageValid,
    StageReady,
    StaticUnreachable(Loc<String>),
    // This is a special case expression which is never created in user code, but which can be used
    // in type inference to create virtual expressions with specific IDs
    Null,
}
impl WithLocation for ExprKind {}

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
impl WithLocation for Expression {}

impl Expression {
    /// Create a new expression referencing an identifier with the specified
    /// id and name
    pub fn ident(expr_id: ExprID, name_id: u64, name: &str) -> Expression {
        ExprKind::Identifier(NameID(name_id, Path::from_strs(&[name]))).with_id(expr_id)
    }

    /// Returns the block that is this expression. Panics if the expression is not a block
    pub fn assume_block(&self) -> &Block {
        if let ExprKind::Block(ref block) = self.kind {
            block
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

pub trait LocExprExt {
    fn runtime_requirement_witness(&self) -> Option<Loc<Expression>>;
}

impl LocExprExt for Loc<Expression> {
    /// Checks if the expression is evaluable at compile time, returning a Loc of
    /// a (sub)-expression which requires runtime, and None if it is comptime evaluable.
    ///
    /// If this method returns None, `.eval()` on the resulting list of mir statements is
    /// guaranteed to work
    fn runtime_requirement_witness(&self) -> Option<Loc<Expression>> {
        match &self.kind {
            ExprKind::Identifier(_) => Some(self.clone()),
            ExprKind::TypeLevelInteger(_) => None,
            ExprKind::IntLiteral(_, _) => None,
            ExprKind::BoolLiteral(_) => None,
            ExprKind::BitLiteral(_) => Some(self.clone()),
            ExprKind::TupleLiteral(inner) => {
                inner.iter().find_map(Self::runtime_requirement_witness)
            }
            ExprKind::ArrayLiteral(inner) => {
                inner.iter().find_map(Self::runtime_requirement_witness)
            }
            ExprKind::ArrayShorthandLiteral(inner, _) => inner.runtime_requirement_witness(),
            ExprKind::CreatePorts => Some(self.clone()),
            ExprKind::Index(l, r) => l
                .runtime_requirement_witness()
                .or_else(|| r.runtime_requirement_witness()),
            ExprKind::RangeIndex { .. } => Some(self.clone()),
            ExprKind::TupleIndex(l, _) => l.runtime_requirement_witness(),
            ExprKind::FieldAccess(l, _) => l.runtime_requirement_witness(),
            // NOTE: We probably shouldn't see this here since we'll have lowered
            // methods at this point, but this function doesn't throw
            ExprKind::MethodCall { .. } | ExprKind::Call { .. } => Some(self.clone()),
            ExprKind::BinaryOperator(l, operator, r) => {
                if let Some(witness) = l
                    .runtime_requirement_witness()
                    .or_else(|| r.runtime_requirement_witness())
                {
                    Some(witness)
                } else {
                    match &operator.inner {
                        BinaryOperator::Add => None,
                        BinaryOperator::Sub => None,
                        BinaryOperator::Mul
                        | BinaryOperator::Div
                        | BinaryOperator::Mod
                        | BinaryOperator::Eq
                        | BinaryOperator::NotEq
                        | BinaryOperator::Gt
                        | BinaryOperator::Lt
                        | BinaryOperator::Ge
                        | BinaryOperator::Le
                        | BinaryOperator::LeftShift
                        | BinaryOperator::RightShift
                        | BinaryOperator::ArithmeticRightShift
                        | BinaryOperator::LogicalAnd
                        | BinaryOperator::LogicalOr
                        | BinaryOperator::LogicalXor
                        | BinaryOperator::BitwiseOr
                        | BinaryOperator::BitwiseAnd
                        | BinaryOperator::BitwiseXor => Some(self.clone()),
                    }
                }
            }
            ExprKind::UnaryOperator(op, operand) => {
                if let Some(witness) = operand.runtime_requirement_witness() {
                    Some(witness)
                } else {
                    match op.inner {
                        UnaryOperator::Sub => None,
                        UnaryOperator::Not
                        | UnaryOperator::BitwiseNot
                        | UnaryOperator::Dereference
                        | UnaryOperator::Reference => Some(self.clone()),
                    }
                }
            }
            ExprKind::Match(_, _) => Some(self.clone()),
            ExprKind::Block(_) => Some(self.clone()),
            ExprKind::If(_, _, _) => Some(self.clone()),
            ExprKind::TypeLevelIf(_, _, _) => Some(self.clone()),
            ExprKind::PipelineRef { .. } => Some(self.clone()),
            ExprKind::StageReady => Some(self.clone()),
            ExprKind::StageValid => Some(self.clone()),
            ExprKind::LambdaDef { .. } => Some(self.clone()),
            ExprKind::StaticUnreachable(_) => None,
            ExprKind::Null => None,
        }
    }
}
