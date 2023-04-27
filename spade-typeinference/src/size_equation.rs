use crate::equation::TypeVar;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SizeExpression {
    Range { lo: i128, hi: i128 },
    Var(TypeVar),
    Add(Box<SizeExpression>, Box<SizeExpression>),
    Neg(Box<SizeExpression>),
}

