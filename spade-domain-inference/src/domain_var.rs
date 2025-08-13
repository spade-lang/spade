use std::{borrow::Borrow, collections::HashSet};

use serde::{Deserialize, Serialize};
use spade_common::location_info::Loc;
use spade_diagnostics::Diagnostic;
use spade_hir::domains::{DomainConstraint, DomainName};

use crate::Result;

#[derive(Clone, Serialize, Deserialize)]
pub enum DomainVar {
    Error,
    Unknown(Vec<Loc<DomainConstraint>>),
    Known(DomainName, Vec<Loc<DomainConstraint>>),
}

pub(crate) trait LocExt<D> {
    fn merge_domains<D2: Borrow<DomainVar>>(&self, other: &Loc<D2>) -> Result<DomainVar>;
}

impl<D: Borrow<DomainVar>> LocExt<D> for Loc<D>
{
    fn merge_domains<D2: Borrow<DomainVar>>(&self, other: &Loc<D2>) -> Result<DomainVar> {
        match (self.inner.borrow(), other.inner.borrow()) {
            (DomainVar::Error, _) | (_, DomainVar::Error) => Ok(DomainVar::Error),
            (DomainVar::Unknown(e_constraints), DomainVar::Unknown(g_constraints))
            | (DomainVar::Unknown(e_constraints), DomainVar::Known(_, g_constraints))
            | (DomainVar::Known(_, e_constraints), DomainVar::Unknown(g_constraints)) => {
                for ec in e_constraints {
                    match ec.inner {
                        DomainConstraint::NoClock => {
                            if let Some(clk_req) = g_constraints
                                .iter()
                                .find(|c| c.inner == DomainConstraint::HasClock)
                            {
                                return Err(Diagnostic::error(
                                    self,
                                    "Mixing a domain without clocks with one that requires a clock",
                                )
                                .primary_label("This domain does not have a clock")
                                .secondary_label(other, "But this requires a clock to be present")
                                .secondary_label(clk_req, "The clock is required here")
                                .secondary_label(
                                    ec,
                                    "The requirement to not have a clock comes from here",
                                ));
                            }
                        }
                        DomainConstraint::HasClock => {
                            if let Some(clk_req) = g_constraints
                                .iter()
                                .find(|c| c.inner == DomainConstraint::NoClock)
                            {
                                return Err(Diagnostic::error(
                                    self,
                                    "Mixing a domain without clocks with one that requires a clock",
                                )
                                .primary_label("This domain requires a clock to be present")
                                .secondary_label(other, "But this does not have a clock")
                                .secondary_label(ec, "The clock is required here")
                                .secondary_label(
                                    clk_req,
                                    "The requirement to not have a clock comes from here",
                                ));
                            }
                        }
                    }
                }

                let mut new_constraints = vec![];
                let mut seen_constraints = HashSet::new();

                for constraint in e_constraints.iter().chain(g_constraints) {
                    if seen_constraints.contains(&constraint.inner) {
                        new_constraints.push(constraint.clone());
                        seen_constraints.insert(constraint.inner.clone());
                    }
                }
                
                Ok(DomainVar::Unknown(new_constraints))
            }
            // TODO: Will hwe need to check the requirements for named domains?
            (DomainVar::Known(n1, _), DomainVar::Known(n2, _)) => {
                if n1 == n2 {
                    Ok(self.inner.borrow().clone())
                } else {
                    let mut diag = Diagnostic::error(self, "Mixing signals in different domains")
                        .primary_label(match n1 {
                            DomainName::Annonymous(_) => {
                                format!("This has domain '{{de}}")
                            },
                            DomainName::Named(name) => {
                                format!("This has domain '{name}")
                            },
                        })
                        .secondary_label(other, match n2 {
                            DomainName::Annonymous(_) => {
                                format!("While this has domain '{{dg}}")
                            },
                            DomainName::Named(name) => {
                                format!("This has domain '{name}")
                            },
                        });

                    diag = match n1 {
                        DomainName::Annonymous(loc) => {
                            diag.secondary_label(loc, "'{{de}} is the annonymous domain of this unit")
                        },
                        DomainName::Named(_) => diag,
                    };
                    
                    diag = match n2 {
                        DomainName::Annonymous(loc) => {
                            diag.secondary_label(loc, "'{{dg}} is the annonymous domain of this unit")
                        },
                        DomainName::Named(_) => diag,
                    };

                    Err(diag)
                }
            }
        }
    }
}
