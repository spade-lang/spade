use num::{BigInt, BigRational, Signed};
use spade_common::id_tracker::AAVarTracker;
use std::collections::{btree_map::Entry, BTreeMap, BTreeSet};

use crate::{
    inferer::{Equation, Var},
    range::Range,
};

#[derive(Eq, PartialEq, Clone, Copy, Debug, Ord, PartialOrd)]
enum AffineVar {
    /// A variable coming from the actual program source code.
    Var(Var),
    /// A generated variable when we need to add uncertainty to the calculations.
    Gen(u64),
    /// A constant which has no noise.
    Const,
}

// I've made the bold assumption that `x + EPSILON` is the same or equal to `^ x ^` (the larger floating point number).
// Another way of phrasing it is: `b > 0 => a + b > a` when using floating point arithmetic.
//
// AAForm or Affine Arithmetic Form is a way for computers to do Affine Arithmetic.
// The form is a sum of "noise" variables (variables holding a value between -1 and 1), here
// denoted as `x_i` where each `i` uniquely identifies a variable. This naturally gives you the
// AAForm:
// K + A_0 * x_0 + A_1 + x_1 ...
// where we can add any new kind of variable to the end. We also have a constant term K that
// offsets the potential values. In this program we store the constant as a variable which
// simplifies some parts of the implementation while making other parts more complex.
// A noise variable originate from one of 3 things:
//  - A constant, which is treated specially - `AffineVar::Const`
//  - An actual variable, in case we identify it using that variables ID - `AffineVar::Var(Var)`
//  - A generated variable which is used to make sure the AAForm is overestimating - `AffineVar::Gen(usize)`
//
// For more details see Self-Validated Numerical Methods and Applications
// by Jorge Stolfi and Luiz Henrique de Figueiredo
#[derive(PartialEq, Clone, Debug, PartialOrd)]
pub struct AAForm(BTreeMap<AffineVar, BigRational>);

#[derive(PartialEq, Clone, Debug, PartialOrd)]
struct RadAndMid {
    rad: BigRational,
    mid: BigRational,
}

fn range_helper(r: Range) -> RadAndMid {
    let mid = BigRational::from(r.hi().clone() + r.lo().clone()) / BigInt::from(2);
    let rad = (mid.clone() - r.lo().clone()).max(BigRational::from(r.hi().clone()) - mid.clone());
    RadAndMid { mid, rad }
}

impl AAForm {
    // Helpers

    fn from_range(tracker: &mut AAVarTracker, r: Range) -> AAForm {
        let h = range_helper(r);
        let new_var = AAForm::new_var(tracker);
        AAForm(
            [(AffineVar::Const, h.mid), (new_var, h.rad)]
                .into_iter()
                .collect(),
        )
    }

    fn new_var(tracker: &mut AAVarTracker) -> AffineVar {
        AffineVar::Gen(tracker.next())
    }

    fn from_var(var: Var, r: Range) -> AAForm {
        let h = range_helper(r);
        let new_var = AffineVar::Var(var);
        AAForm(
            [(AffineVar::Const, h.mid), (new_var, h.rad)]
                .into_iter()
                .collect(),
        )
    }

    fn rad(&self) -> BigRational {
        self.0
            .iter()
            .map(|(v, x)| {
                if v == &AffineVar::Const {
                    BigRational::from_integer(BigInt::from(0))
                } else {
                    x.abs()
                }
            })
            .sum()
    }

    fn mid(&self) -> BigRational {
        self.0
            .iter()
            .find_map(|(var, value)| {
                if var == &AffineVar::Const {
                    Some(value.clone())
                } else {
                    None
                }
            })
            .unwrap_or(BigRational::from_integer(BigInt::from(0)))
    }

    fn vars(&self) -> BTreeSet<AffineVar> {
        self.0.keys().cloned().collect()
    }

    fn bit_manip(&self, tracker: &mut AAVarTracker) -> AAForm {
        let mid = self.mid();
        let rad = self.rad();
        AAForm::from_range(
            tracker,
            Range::new(
                (mid.clone() - rad.clone()).to_integer(),
                (mid + rad).to_integer(),
            )
            .bit_manip()
            .unwrap(),
        )
    }

    // Operations

    fn mul(&self, tracker: &mut AAVarTracker, other: &Self) -> Self {
        // Shamelessly stolen from https://github.com/ogay/libaffa/blob/master/src/aa_aafapprox.cpp
        // since the old code had bugs
        let x = self;
        let y = other;
        let mut z = BTreeMap::new();
        for i in x.vars().union(&y.vars()) {
            if i == &AffineVar::Const { continue }
            z.insert(*i, match (x.0.get(i), y.0.get(i)) {
                (Some(xx), Some(yy)) => x.mid() * yy + y.mid() * xx,
                (Some(xx), None) => y.mid() * xx,
                (None, Some(yy)) => x.mid() * yy,
                (None, None) => unreachable!("Set union forces the keys to exist in one of the numbers"),
            });
            }
        let d = Self::new_var(tracker);
        z.insert(d, x.rad() * y.rad());
        AAForm(z)
    }


    fn old_mul(&self, tracker: &mut AAVarTracker, other: &Self) -> Self {
        // This code is quite complicated and I got a myriad of bugs here. The idea is to over
        // estimate using: |(a * b)| <= |(|b| * a + |a| * b + mid(a) * mid(b) + rad(a) * rad(b))|
        // It's a pretty correct way of estimating and it works decently well.
        let x0 = self.mid();
        let y0 = other.mid();

        let p = range_helper(
            Range::new(
                BigRational::to_integer(&BigRational::ceil(&x0)),
                BigRational::to_integer(&BigRational::ceil(&x0)),
            )
            .mul(&Range::new(
                BigRational::to_integer(&BigRational::ceil(&y0)),
                BigRational::to_integer(&BigRational::ceil(&y0)),
            )),
        );
        let gamma = -p.mid;
        let delta = (self.rad() * other.rad()) + p.rad;

        Self::affine(tracker, self, other, y0, x0, gamma, delta)
    }
    
    // Computes alpha * x + beta * y + gamma (where delta is extra noise)
    fn affine(
        tracker: &mut AAVarTracker,
        x: &AAForm,
        y: &AAForm,
        alpha: BigRational,
        beta: BigRational,
        gamma: BigRational,
        delta: BigRational,
    ) -> AAForm {
        let zero = BigRational::from_integer(BigInt::from(0));

        let mut z = BTreeMap::new();
        for i in x.vars().union(&y.vars()) {
            let xi = x.0.get(i).unwrap_or(&zero);
            let yi = y.0.get(i).unwrap_or(&zero);
            let zi = alpha.clone() * xi
                + beta.clone() * yi
                + if i == &AffineVar::Const {
                    gamma.clone()
                } else {
                    zero.clone()
                };
            z.insert(*i, zi);

            // We get no rounding errors when using BigRational
            // / Hope the compiler doesn't optimize this away...
            // delta += (a - zi).max(zi - b);
        }
        let d = Self::new_var(tracker);
        z.insert(d, delta);
        AAForm(z)
    }


    fn add(&self, other: &Self) -> Self {
        let mut out = self.0.clone();
        for (var, value) in other.0.iter() {
            match out.entry(*var) {
                Entry::Vacant(v) => {
                    v.insert(value.clone());
                }
                Entry::Occupied(mut v) => {
                    *v.get_mut() += value;
                }
            }
        }
        AAForm(out)
    }

    /// Takes two AAForms and tries to compute the smallest AAForm that is bigger than both of
    /// them. Think union for set, but for AAForm.
    fn union(&self, tracker: &mut AAVarTracker, other: &Self) -> Self {
        // Union of AAForm doesn't make a lot of sense, it's the biggest weakness of the form
        // since we have to either throw away information, or accumulate a lot of error.
        //
        // This approach accumulates error and might add unnecessary noise. This causes problems
        // pretty quickly and is probably why it's not defined. Consider `a & 1`, we would get an
        // potentially extra bit here. It's better to make it an opaque range and infer after it.
        // let mut out = self.0.clone();
        // for (var, value) in other.0.iter() {
        //     if var == &AffineVar::Const {
        //         out.insert(*var, self.mid() + other.mid());
        //     } else {
        //         match out.entry(*var) {
        //             Entry::Vacant(v) => {
        //                 v.insert(value.clone());
        //             }
        //             Entry::Occupied(mut v) => {
        //                 *v.get_mut() = v.get().max(value).clone();
        //             }
        //         }
        //     }
        // }
        // AAForm(out)

        let a = Range::new(
            (self.mid() - self.rad()).to_integer(),
            (self.mid() + self.rad()).to_integer(),
        );
        let b = Range::new(
            (other.mid() - other.rad()).to_integer(),
            (other.mid() + other.rad()).to_integer(),
        );
        AAForm::from_range(tracker, a.union(&b))
    }

    fn neg(&self) -> Self {
        AAForm(self.0.clone().into_iter().map(|(v, s)| (v, -s)).collect())
    }
}

fn evaluate_aa(
    tracker: &mut AAVarTracker,
    body: &Equation,
    known: &BTreeMap<Var, Range>,
) -> Option<AAForm> {
    match body {
        Equation::V(var) => known.get(var).map(|r| AAForm::from_var(*var, r.clone())),
        Equation::Constant(r) => Some(AAForm::from_range(tracker, r.clone())),
        Equation::Add(a, b) => match (
            evaluate_aa(tracker, a, known),
            evaluate_aa(tracker, b, known),
        ) {
            (Some(a), Some(b)) => Some(a.add(&b)),
            _ => None,
        },
        Equation::Sub(a, b) => match (
            evaluate_aa(tracker, a, known),
            evaluate_aa(tracker, b, known),
        ) {
            (Some(a), Some(b)) => Some(a.add(&b.neg())),
            _ => None,
        },

        Equation::Mul(a, b) => match (
            evaluate_aa(tracker, a, known),
            evaluate_aa(tracker, b, known),
        ) {
            (Some(a), Some(b)) => Some(a.mul(tracker, &b)),
            _ => None,
        },
        Equation::Neg(a) => evaluate_aa(tracker, a, known).map(|a| a.neg()),
        Equation::BitManpi(a) => evaluate_aa(tracker, a, known).map(|x| x.bit_manip(tracker)),
        Equation::BitManipMax(a, b) => match (
            evaluate_aa(tracker, a, known),
            evaluate_aa(tracker, b, known),
        ) {
            (Some(a), Some(b)) => {
                let b = b.bit_manip(tracker);
                Some(a.bit_manip(tracker).union(tracker, &b))
            }
            _ => None,
        },
        Equation::Union(a, b) => match (
            evaluate_aa(tracker, a, known),
            evaluate_aa(tracker, b, known),
        ) {
            (Some(a), Some(b)) => Some(a.union(tracker, &b)),
            _ => None,
        },
    }
}

pub fn evaluate_aa_and_simplify_to_range(
    body: &Equation,
    known: &BTreeMap<Var, Range>,
) -> Option<Range> {
    if let Some(aa_expr) = evaluate_aa(&mut AAVarTracker::new(), body, known) {
        let mid = aa_expr.mid();
        let rad = aa_expr.rad();
        Some(Range::new(
            BigRational::to_integer(&(mid.clone() - rad.clone()).floor()),
            BigRational::to_integer(&(mid + rad).ceil()),
        ))
    } else {
        None
    }
}
