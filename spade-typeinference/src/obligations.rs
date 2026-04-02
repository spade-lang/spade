use spade_common::location_info::Loc;

use crate::{Context, Result, TypeState, equation::TypeVarID, error::UnificationErrorExt};

#[must_use]
pub struct WithObligations<T> {
    val: T,
    obligations: Vec<Loc<(TypeVarID, TypeVarID)>>,
}

impl WithObligations<()> {
    pub fn empty() -> Self {
        Self {
            val: (),
            obligations: vec![],
        }
    }
}

impl<T> WithObligations<T> {
    pub fn new(val: T, obligations: Vec<Loc<(TypeVarID, TypeVarID)>>) -> Self {
        Self { val, obligations }
    }

    pub fn with_val<O>(self, val: O) -> WithObligations<O> {
        WithObligations {
            val,
            obligations: self.obligations,
        }
    }

    pub fn split(self) -> (T, WithObligations<()>) {
        (
            self.val,
            WithObligations {
                val: (),
                obligations: self.obligations,
            },
        )
    }

    pub fn push(&mut self, o: Loc<(TypeVarID, TypeVarID)>) {
        self.obligations.push(o);
    }

    pub fn resolve_obligations(self, ts: &mut TypeState, ctx: &Context) -> Result<T> {
        for obligation in self.obligations {
            let ((l, r), loc) = obligation.split_loc();
            ts.unify(&l, &r, ctx).into_default_diagnostic(loc, ts)?;
        }

        Ok(self.val)
    }

    pub fn absorb_obligations(self, other: &mut impl Extend<Loc<(TypeVarID, TypeVarID)>>) -> T {
        other.extend(self.obligations);
        self.val
    }
}

impl<T> Extend<Loc<(TypeVarID, TypeVarID)>> for WithObligations<T> {
    fn extend<I: IntoIterator<Item = Loc<(TypeVarID, TypeVarID)>>>(&mut self, iter: I) {
        self.obligations.extend(iter)
    }
}

pub trait WithoutObligations<T> {
    fn no_obligations(self) -> WithObligations<T>;
}

impl<T> WithoutObligations<T> for T {
    fn no_obligations(self) -> WithObligations<T> {
        WithObligations {
            val: self,
            obligations: vec![],
        }
    }
}
