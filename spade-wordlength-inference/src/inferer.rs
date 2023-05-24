use std::collections::btree_map::Entry;
use std::collections::BTreeMap;

use num::BigInt;
use spade_common::location_info::Loc;
use spade_hir::expression::NamedArgument;
use spade_hir::symbol_table::SymbolTable;
use spade_hir::{
    expression::{BinaryOperator, UnaryOperator},
    Block, ExprKind, Pattern, Statement,
};
use spade_hir::{ArgumentList, Expression};
use spade_typeinference::{equation::TypeVar, fixed_types::t_int, HasType, TypeState};

use crate::range::Range;
use crate::{error, InferMethod, Res};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Var(usize);

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Equation {
    V(Var),
    Constant(Range),
    Add(Box<Equation>, Box<Equation>),
    Sub(Box<Equation>, Box<Equation>),
    Mul(Box<Equation>, Box<Equation>),
    BitManpi(Box<Equation>),
    Neg(Box<Equation>),
    BitManipMax(Box<Equation>, Box<Equation>),
    Union(Box<Equation>, Box<Equation>),
}

pub struct Inferer<'a> {
    pub(crate) locs: BTreeMap<Var, Loc<()>>,
    pub(crate) mappings: BTreeMap<Loc<TypeVar>, Var>,
    // These are >= equations
    pub(crate) equations: Vec<(Var, Loc<Equation>)>,
    pub(crate) var_counter: usize,
    pub(crate) symtab: &'a SymbolTable,
    pub(crate) type_state: &'a mut TypeState,
}
impl<'a> Inferer<'a> {
    pub fn new(type_state: &'a mut TypeState, symtab: &'a SymbolTable) -> Self {
        Self {
            locs: BTreeMap::new(),
            mappings: BTreeMap::new(),
            equations: Vec::new(),
            var_counter: 0,
            symtab,
            type_state,
        }
    }

    fn new_var(&mut self, loc: Loc<()>) -> Var {
        let v = Var(self.var_counter);
        self.locs.insert(v, loc);
        self.var_counter += 1;
        v
    }

    fn find_or_create(&mut self, thing: &dyn HasType, loc: Loc<()>) -> Option<Var> {
        if let Ok(TypeVar::Known(t, v)) = thing.get_type(self.type_state) {
            match v.as_slice() {
                [size] if t == t_int(self.symtab) => {
                    // TODO[et]: Inject where the variable came from so we can put it back in
                    let p = if let Some(q) = self.mappings.get(&Loc::nowhere(size.clone())) {
                        *q
                    } else {
                        let q = self.new_var(loc);
                        self.mappings.insert(loc.map(|_| size.clone()), q);
                        q
                    };
                    Some(p)
                }
                _ => None,
            }
        } else {
            None
        }
    }

    fn maybe_add_equation(&mut self, thing: &dyn HasType, maybe_eq: Loc<Option<Equation>>) {
        if let (Some(var), Some(eq)) = (
            self.find_or_create(thing, maybe_eq.loc()),
            maybe_eq.inner.clone(),
        ) {
            self.equations.push((var, maybe_eq.give_loc(eq)))
        }
    }

    pub fn expression(&mut self, expr: &Loc<Expression>) -> Res {
        let maybe_eq = match &expr.inner.kind {
            ExprKind::Identifier(_) => self
                .find_or_create(&expr.inner, expr.loc())
                .map(|v| Equation::V(v)),
            ExprKind::IntLiteral(literal) => {
                let x = match literal {
                    spade_hir::expression::IntLiteral::Signed(x) => x.clone(),
                    spade_hir::expression::IntLiteral::Unsigned(x) => BigInt::from(x.clone()),
                };
                Some(Equation::Constant(Range {
                    lo: x.clone(),
                    hi: x.clone(),
                }))
            }

            ExprKind::BinaryOperator(lhs, op, rhs) => self.binary_operator(lhs, *op, rhs)?,
            ExprKind::UnaryOperator(op, v) => self.unary_operator(*op, v)?,
            ExprKind::Match(value, patterns) => self.match_(value, patterns)?,
            ExprKind::Block(block) => self.block(block)?,
            ExprKind::If(value, true_, false_) => self.if_(value, true_, false_)?,

            // These are all opaque types, they say nothing of the structure of integers (well,
            // they might but we don't have that kind of information). The inference will
            // replace these with the largest possible value and go from there. So, code like:
            // 1 + [0, 1000][0]
            //
            // Will realize we have a signed integer in the list with a max size of 1024, and give
            // us the estimate: 1 +- 1024, though a programmer could easily infer 1 + 0. This is
            // still better than what was before but not the best solution - extending this to
            // infer more complicated relationships might be a fun extension (but out of scope for
            // this thesis)
            ExprKind::TupleLiteral(exprs) | ExprKind::ArrayLiteral(exprs) => {
                self.tuple_or_array_literal(exprs)?;
                None
            }
            ExprKind::Index(target, index) => {
                self.expression(target)?;
                self.expression(index)?;
                None
            }
            ExprKind::TupleIndex(target, _) => {
                self.expression(target)?;
                None
            }

            ExprKind::FieldAccess(target, _) => {
                self.expression(target)?;
                None
            }
            ExprKind::Call { args, .. } => {
                self.visit_args(args)?;
                None
            }
            ExprKind::MethodCall { target, args, .. } => {
                self.expression(target)?;
                self.visit_args(args)?;
                None
            }

            // There's a case to be made for these being valuable to implement. Implementing these
            // is bound to be simple and give value to the language, but it requires figuring out
            // where their return types are stored - which is less interesting.
            ExprKind::BoolLiteral(_) | ExprKind::PipelineRef { .. } | ExprKind::CreatePorts => None,
        };

        self.maybe_add_equation(&expr.inner, expr.loc().give_loc(maybe_eq.clone()));
        Ok(maybe_eq)
    }

    fn block(&mut self, block: &Block) -> Res {
        for stmt in block.statements.iter() {
            match &stmt.inner {
                Statement::Binding(_, _, expr) | Statement::Assert(expr) => {
                    self.expression(&expr)?;
                }

                Statement::Set { target, value } => {
                    self.expression(&target)?;
                    self.expression(&value)?;
                }

                Statement::Register(register) => {
                    let register = &register.inner;
                    self.expression(&register.clock)?;
                    if let Some((left, right)) = &register.reset {
                        self.expression(&left)?;
                        self.expression(&right)?;
                    }
                    self.expression(&register.value)?;
                }

                // Nothing to be done for these since they contain no expressions and thus no
                // integer operations.
                Statement::Declaration(_) | Statement::PipelineRegMarker | Statement::Label(_) => {}
            }
        }
        self.expression(&block.result)
    }

    fn match_(
        &mut self,
        _value: &Loc<Expression>,
        patterns: &[(Loc<Pattern>, Loc<Expression>)],
    ) -> Res {
        // TODO: Is there a currectness bug here since I discard the pattern?
        // NOTE: This unification works if the range contains zero - which it kinda always does
        // here, but it can cause overestimations!
        let mut eq = Equation::Constant(Range::zero());
        for (_, body) in patterns {
            if let Some(b) = self.expression(body)? {
                eq = Equation::Union(Box::new(eq), Box::new(b));
            }
        }
        Ok(Some(eq))
    }

    fn if_(
        &mut self,
        _value: &Loc<Expression>,
        true_: &Loc<Expression>,
        false_: &Loc<Expression>,
    ) -> Res {
        Ok(match (self.expression(true_)?, self.expression(false_)?) {
            (Some(true_), Some(false_)) => Some(Equation::Union(Box::new(true_), Box::new(false_))),
            _ => None,
        })
    }

    fn binary_operator(
        &mut self,
        lhs: &Loc<Expression>,
        op: BinaryOperator,
        rhs: &Loc<Expression>,
    ) -> Res {
        // These would be None if we have something that is opaque to the wordlength inferer, they
        // might signal an error in the typechecker or in the wordlength inferer.
        let lhs_t = self.expression(lhs)?;
        let rhs_t = self.expression(rhs)?;
        Ok(match (op, lhs_t, rhs_t) {
            (BinaryOperator::Add, Some(lhs_t), Some(rhs_t)) => {
                Some(Equation::Add(Box::new(lhs_t), Box::new(rhs_t)))
            }
            (BinaryOperator::Add, _, _) => None,

            (BinaryOperator::Sub, Some(lhs_t), Some(rhs_t)) => {
                Some(Equation::Sub(Box::new(lhs_t), Box::new(rhs_t)))
            }
            (BinaryOperator::Sub, _, _) => None,

            (BinaryOperator::Mul, Some(lhs_t), Some(rhs_t)) => {
                Some(Equation::Mul(Box::new(lhs_t), Box::new(rhs_t)))
            }
            (BinaryOperator::Mul, _, _) => None,

            (
                BinaryOperator::LeftShift
                | BinaryOperator::RightShift
                | BinaryOperator::ArithmeticRightShift,
                Some(v),
                _,
            ) => {
                // The left value is the one being shifted
                Some(Equation::BitManpi(Box::new(v)))
            }

            (
                BinaryOperator::LeftShift
                | BinaryOperator::RightShift
                | BinaryOperator::ArithmeticRightShift,
                _,
                _,
            ) => None,

            (
                BinaryOperator::BitwiseOr
                | BinaryOperator::BitwiseAnd
                | BinaryOperator::BitwiseXor
                | BinaryOperator::LogicalAnd
                | BinaryOperator::LogicalOr
                | BinaryOperator::LogicalXor,
                Some(a),
                Some(b),
            ) => Some(Equation::BitManipMax(Box::new(a), Box::new(b))),
            (
                BinaryOperator::BitwiseOr
                | BinaryOperator::BitwiseAnd
                | BinaryOperator::BitwiseXor
                | BinaryOperator::LogicalAnd
                | BinaryOperator::LogicalOr
                | BinaryOperator::LogicalXor,
                _,
                _,
            ) => None,

            (
                BinaryOperator::Eq
                | BinaryOperator::NotEq
                | BinaryOperator::Gt
                | BinaryOperator::Lt
                | BinaryOperator::Ge
                | BinaryOperator::Le,
                _,
                _,
            ) => None,
        })
    }

    fn unary_operator(&mut self, op: UnaryOperator, v: &Loc<Expression>) -> Res {
        let v_t = self.expression(v)?;
        Ok(match (op, v_t) {
            (UnaryOperator::Sub, Some(v)) => Some(Equation::Neg(Box::new(v))),
            (UnaryOperator::Sub, _) => None,
            (UnaryOperator::BitwiseNot, Some(v)) => Some(Equation::BitManpi(Box::new(v))),
            (UnaryOperator::BitwiseNot, _) => None,

            (
                UnaryOperator::Not
                | UnaryOperator::Dereference
                | UnaryOperator::Reference
                | UnaryOperator::FlipPort,
                _,
            ) => None,
        })
    }

    pub fn infer(
        infer_method: InferMethod,
        equations: &Vec<(Var, Loc<Equation>)>,
        mut known: BTreeMap<Var, Range>,
        locs: &BTreeMap<Var, Loc<()>>,
    ) -> error::Result<BTreeMap<Var, Range>> {
        // worst-case: The equations are all in reverse order and we can solve one new
        // variable per run, but maybe this is untrue and we can grantee something like
        // finishes in a fixed number of cycles?
        for _ in 0..equations.len() {
            let known_at_start = known.clone();
            for (var, body) in equations.iter() {
                let loc = locs.get(var).cloned().unwrap_or(Loc::nowhere(()));
                if let Some(infer) = match infer_method {
                    InferMethod::IA => crate::range::evaluate_ia(body, &known),
                    InferMethod::AA => {
                        crate::affine::evaluate_aa_and_simplify_to_range(body, &known)
                    }
                } {
                    match known.entry(*var) {
                        Entry::Vacant(v) => {
                            v.insert(infer);
                        }
                        Entry::Occupied(v) => {
                            match (v.get().to_wordlength(), infer.to_wordlength()) {
                                // NOTE: I had to weaken this check to `<` (from `!=`) since it gave false
                                // positives for cases like: f(0) if the constant wasn't large
                                // enough. Maybe this is a signal of a special rule or something
                                // else, but it does signal potential optimization potential.
                                (Some(typecheck_wl), Some(infer_wl)) if typecheck_wl < infer_wl => {
                                    // I'm not sure this is the same kind of error as it's being
                                    // used as in both places - sure it's a contradiction, but here
                                    // we might have inferred an incorrect or contradicting conclusion.
                                    return Err(error::Error::WordlengthMismatch {
                                        typechecked: body.give_loc(typecheck_wl),
                                        infered: loc.give_loc(infer_wl),
                                    });
                                }
                                _ => {}
                            }
                        }
                    }
                }
            }

            // Break when we got new information - I think this is a decent speedup...
            if known_at_start == known {
                break;
            }
        }
        Ok(known)
    }

    fn tuple_or_array_literal(&mut self, exprs: &[Loc<Expression>]) -> Res {
        for expr in exprs.iter() {
            self.expression(expr)?;
        }
        // Tuples/Arrays aren't numbers!
        Ok(None)
    }

    fn visit_args(&mut self, args: &Loc<ArgumentList>) -> Res {
        let exprs = match &args.inner {
            ArgumentList::Named(named) => named
                .iter()
                .map(|x| match x {
                    NamedArgument::Full(_, expr) => expr.clone(),
                    NamedArgument::Short(_, expr) => expr.clone(),
                })
                .collect(),
            ArgumentList::Positional(expr) => expr.clone(),
        };
        for expr in exprs.iter() {
            self.expression(&expr)?;
        }
        Ok(None)
    }
}

#[cfg(test)]
mod test {
    use std::collections::{BTreeMap, BTreeSet};

    use num::BigInt;
    use spade_common::location_info::Loc;

    use super::Equation;
    use super::{Inferer, Var};

    use crate::{range::Range, InferMethod};

    fn check_infer(
        infer_method: InferMethod,
        equations: Vec<(Var, Equation)>,
        expected: Vec<(Var, Range)>,
    ) {
        let vars = equations
            .clone()
            .into_iter()
            .map(|(v, _)| (v, Loc::nowhere(())))
            .collect();
        let infered = Inferer::infer(
            infer_method,
            &equations
                .clone()
                .into_iter()
                .map(|(v, e)| (v, Loc::nowhere(e)))
                .collect(),
            BTreeMap::new(),
            &vars,
        )
        .map(|e| e.into_iter().collect::<BTreeSet<(Var, Range)>>());
        let expected = Ok(expected.into_iter().collect::<BTreeSet<(Var, Range)>>());
        assert_eq!(
            infered, expected,
            "The infered values don't match the given values, check the values carefully\nEQ: {:+?}", equations
        );
    }

    fn r(lo: i128, hi: i128) -> Range {
        Range {
            lo: BigInt::from(lo),
            hi: BigInt::from(hi),
        }
    }
    fn c(lo: i128, hi: i128) -> Equation {
        Equation::Constant(Range {
            lo: BigInt::from(lo),
            hi: BigInt::from(hi),
        })
    }
    fn v(x: usize) -> Equation {
        Equation::V(Var(x))
    }
    fn add(a: Equation, b: Equation) -> Equation {
        Equation::Add(Box::new(a), Box::new(b))
    }
    fn n(a: Equation) -> Equation {
        Equation::Neg(Box::new(a))
    }
    fn sub(a: Equation, b: Equation) -> Equation {
        Equation::Sub(Box::new(a), Box::new(b))
    }
    fn mul(a: Equation, b: Equation) -> Equation {
        Equation::Mul(Box::new(a), Box::new(b))
    }
    fn bit(a: Equation) -> Equation {
        Equation::BitManpi(Box::new(a))
    }
    fn u(a: Equation, b: Equation) -> Equation {
        Equation::Union(Box::new(a), Box::new(b))
    }

    // AA
    #[test]
    fn range_aa() {
        check_infer(
            InferMethod::AA,
            vec![(Var(0), c(10, 10))],
            vec![(Var(0), r(10, 10))],
        )
    }

    #[test]
    fn large_range_aa() {
        check_infer(
            InferMethod::AA,
            vec![(Var(0), c(-16, 15))],
            vec![(Var(0), r(-16, 15))],
        )
    }

    #[test]
    fn odd_range_aa() {
        check_infer(
            InferMethod::AA,
            vec![(Var(0), c(0, 1))],
            vec![(Var(0), r(0, 1))],
        )
    }

    #[test]
    fn add_aa() {
        check_infer(
            InferMethod::AA,
            vec![(Var(0), c(0, 10)), (Var(1), add(v(0), v(0)))],
            vec![(Var(0), r(0, 10)), (Var(1), r(0, 20))],
        )
    }

    #[test]
    fn sub_aa() {
        check_infer(
            InferMethod::AA,
            vec![(Var(0), c(0, 10)), (Var(1), sub(v(0), v(0)))],
            vec![(Var(0), r(0, 10)), (Var(1), r(0, 0))],
        )
    }

    #[test]
    fn mul_aa() {
        check_infer(
            InferMethod::AA,
            vec![
                (Var(0), c(0, 10)),
                (Var(1), c(-2, 2)),
                (Var(2), mul(v(0), v(1))),
                (Var(3), mul(v(1), v(0))),
            ],
            vec![
                (Var(0), r(0, 10)),
                (Var(1), r(-2, 2)),
                (Var(2), r(-20, 20)),
                (Var(3), r(-20, 20)),
            ],
        )
    }

    #[test]
    fn bit_manip_aa() {
        check_infer(
            InferMethod::AA,
            vec![(Var(0), c(0, 10)), (Var(1), bit(v(0)))],
            // AA can't handle odd-ranges due to how they're stored, this can
            // easily be solved by using a different structure but... Yeah...
            vec![(Var(0), r(0, 10)), (Var(1), r(-16, 15))],
        )
    }

    #[test]
    fn neg_aa() {
        check_infer(
            InferMethod::AA,
            vec![(Var(0), n(c(0, 10)))],
            vec![(Var(0), r(-10, 0))],
        )
    }

    #[test]
    fn union_aa() {
        check_infer(
            InferMethod::AA,
            vec![(Var(0), u(c(0, 10), c(-5, 5)))],
            // Union of AAF doesn't make a lot of sense, it's the biggest weakness of the form
            // since we have to either throw away information, or accumulate a lot of error.
            vec![(Var(0), r(-5, 15))],
        )
    }

    #[test]
    fn some_expression_aa() {
        check_infer(
            InferMethod::AA,
            vec![
                (Var(0), c(0, 10)),
                (
                    Var(1),
                    u(add(sub(v(0), c(10, 10)), mul(c(-1, 1), v(0))), c(-50, 0)),
                ),
            ],
            vec![(Var(0), r(0, 10)), (Var(1), r(-70, 10))],
        )
    }

    // IA
    #[test]
    fn range_ia() {
        check_infer(
            InferMethod::IA,
            vec![(Var(0), c(10, 10))],
            vec![(Var(0), r(10, 10))],
        )
    }

    #[test]
    fn add_ia() {
        check_infer(
            InferMethod::IA,
            vec![(Var(0), c(0, 10)), (Var(1), add(v(0), v(0)))],
            vec![(Var(0), r(0, 10)), (Var(1), r(0, 20))],
        )
    }

    #[test]
    fn sub_ia() {
        check_infer(
            InferMethod::IA,
            vec![(Var(0), c(0, 10)), (Var(1), sub(v(0), v(0)))],
            vec![(Var(0), r(0, 10)), (Var(1), r(-10, 10))],
        )
    }

    #[test]
    fn mul_ia() {
        check_infer(
            InferMethod::IA,
            vec![
                (Var(0), c(0, 10)),
                (Var(1), c(-2, 2)),
                (Var(2), mul(v(0), v(1))),
                (Var(3), mul(v(1), v(0))),
            ],
            vec![
                (Var(0), r(0, 10)),
                (Var(1), r(-2, 2)),
                (Var(2), r(-20, 20)),
                (Var(3), r(-20, 20)),
            ],
        )
    }

    #[test]
    fn bit_manip_ia() {
        check_infer(
            InferMethod::IA,
            vec![(Var(0), c(0, 10)), (Var(1), bit(v(0)))],
            vec![(Var(0), r(0, 10)), (Var(1), r(-16, 15))],
        )
    }

    #[test]
    fn neg_ia() {
        check_infer(
            InferMethod::IA,
            vec![(Var(0), n(c(0, 10)))],
            vec![(Var(0), r(-10, 0))],
        )
    }

    #[test]
    fn union_ia() {
        check_infer(
            InferMethod::IA,
            vec![(Var(0), u(c(0, 10), c(-5, 5)))],
            vec![(Var(0), r(-5, 10))],
        )
    }

    #[test]
    fn some_expression_ia() {
        let e = u(add(sub(v(0), c(10, 10)), mul(c(-1, 1), v(0))), c(-50, 0));
        check_infer(
            InferMethod::IA,
            vec![(Var(0), c(0, 10)), (Var(1), e)],
            vec![(Var(0), r(0, 10)), (Var(1), r(-50, 10))],
        )
    }
}
