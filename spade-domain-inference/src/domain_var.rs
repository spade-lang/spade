use std::{borrow::Borrow, collections::HashSet};

use itertools::Itertools;
use serde::{Deserialize, Serialize};
use spade_common::location_info::Loc;
use spade_diagnostics::Diagnostic;
use spade_hir::{
    domains::{DomainConstraint, DomainName},
    pretty_debug::PrettyDebug,
};
use spade_typeinference::equation::TypeVarID;

use crate::Result;

#[derive(Clone, Serialize, Deserialize)]
pub enum DomainVar {
    Error,
    Unknown(Vec<Loc<DomainConstraint>>),
    Known(DomainName, Vec<Loc<DomainConstraint>>),
    Tuple(Vec<Loc<TypeVarID>>),
}
impl std::fmt::Debug for DomainVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DomainVar::Error => write!(f, "{{error}}"),
            DomainVar::Unknown(constraints) => write!(
                f,
                "{}",
                constraints
                    .iter()
                    .map(|constraint| constraint.pretty_debug())
                    .join(" + ")
            ),
            DomainVar::Known(domain_name, constraints) => {
                write!(
                    f,
                    "'{}: ({})",
                    domain_name.pretty_debug(),
                    constraints
                        .iter()
                        .map(|constraint| constraint.pretty_debug())
                        .join(" + ")
                )
            }
            DomainVar::Tuple(members) => {
                write!(
                    f,
                    "({})",
                    members
                        .iter()
                        .map(|domain| format!("{domain:?}"))
                        .join(", ")
                )
            }
        }
    }
}

pub(crate) trait LocExt<D> {
    fn merge_domains<D2: Borrow<DomainVar>>(&self, other: &Loc<D2>) -> Result<DomainVar>;
}

fn check_and_merge_constraints(
    e_loc: Loc<()>,
    e_constraints: &[Loc<DomainConstraint>],
    g_loc: Loc<()>,
    g_constraints: &[Loc<DomainConstraint>],
) -> Result<Vec<Loc<DomainConstraint>>> {
    for ec in e_constraints {
        match ec.inner {
            DomainConstraint::NoClock => {
                if let Some(clk_req) = g_constraints
                    .iter()
                    .find(|c| c.inner == DomainConstraint::HasClock)
                {
                    return Err(Diagnostic::error(
                        e_loc,
                        "Mixing a domain without clocks with one that requires a clock",
                    )
                    .primary_label("This domain does not have a clock")
                    .secondary_label(g_loc, "But this requires a clock to be present")
                    .secondary_label(clk_req, "The clock is required here")
                    .secondary_label(ec, "The requirement to not have a clock comes from here"));
                }
            }
            DomainConstraint::HasClock => {
                if let Some(clk_req) = g_constraints
                    .iter()
                    .find(|c| c.inner == DomainConstraint::NoClock)
                {
                    return Err(Diagnostic::error(
                        e_loc,
                        "Mixing a domain without clocks with one that requires a clock",
                    )
                    .primary_label("This domain requires a clock to be present")
                    .secondary_label(g_loc, "But this does not have a clock")
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

    for constraint in e_constraints.iter().chain(g_constraints.iter()) {
        if seen_constraints.contains(&constraint.inner) {
            new_constraints.push(constraint.clone());
            seen_constraints.insert(constraint.inner.clone());
        }
    }

    Ok(new_constraints)
}

impl<D: Borrow<DomainVar>> LocExt<D> for Loc<D> {
    fn merge_domains<D2: Borrow<DomainVar>>(&self, other: &Loc<D2>) -> Result<DomainVar> {
        match (self.inner.borrow(), other.inner.borrow()) {
            // Error merges with anything
            (DomainVar::Error, _) | (_, DomainVar::Error) => Ok(DomainVar::Error),
            (DomainVar::Unknown(e_constraints), DomainVar::Unknown(g_constraints)) => {
                let new_constraints = check_and_merge_constraints(
                    self.loc(),
                    e_constraints,
                    other.loc(),
                    g_constraints,
                )?;
                Ok(DomainVar::Unknown(new_constraints))
            }
            // Unknown <=> Known is ok as long as there are not conflicting constraints
            (DomainVar::Unknown(e_constraints), DomainVar::Known(kdomain, g_constraints))
            | (DomainVar::Known(kdomain, e_constraints), DomainVar::Unknown(g_constraints)) => {
                let new_constraints = check_and_merge_constraints(
                    self.loc(),
                    e_constraints,
                    other.loc(),
                    g_constraints,
                )?;
                // TODO: Disallow constraints that are more restricitve than than what is specified
                // on the domain
                Ok(DomainVar::Known(kdomain.clone(), new_constraints))
            }
            // Unknown with tuple is OK if the constraints on the unknown are satisfied
            // by _all_ tuple member domains, and Unkown is not Async since tuples cannot
            // be stored in registers
            (DomainVar::Unknown(u_constraints), DomainVar::Tuple(members))
            | (DomainVar::Tuple(members), DomainVar::Unknown(u_constraints)) => {
                if let Some(clock_constraint) = u_constraints
                    .iter()
                    .find(|c| c == DomainConstraint::HasClock)
                {
                    // If we have a clock constraint, we need to enforce the requirement that
                    // all tuple members can be in the same domain. To do so, we will pick the
                    // domain of the first member, replacing it with a placeholder Known domain
                    // if it is 
                    match members.as_slice() {
                        [] => Ok(DomainVar::Unknown(u_constraints.clone())),
                        [first, rest @ ..] => {
                            
                        }
                    }
                }
            }
            // TODO: Will we need to check the requirements for named domains?
            (DomainVar::Known(n1, _), DomainVar::Known(n2, _)) => {
                if n1 == n2 {
                    Ok(self.inner.borrow().clone())
                } else {
                    let diag = Diagnostic::error(self, "Mixing signals in different domains")
                        .primary_label(match n1 {
                            DomainName::Annonymous => {
                                format!("This has domain '{{de}}")
                            }
                            DomainName::Named(name) => {
                                format!("This has domain '{name}")
                            }
                        })
                        .secondary_label(
                            other,
                            match n2 {
                                DomainName::Annonymous => {
                                    format!("While this has domain '{{dg}}")
                                }
                                DomainName::Named(name) => {
                                    format!("This has domain '{name}")
                                }
                            },
                        );

                    // diag = match n1 {
                    //     DomainName::Annonymous(loc) => diag
                    //         .secondary_label(loc, "'{{de}} is the annonymous domain of this unit"),
                    //     DomainName::Named(_) => diag,
                    // };

                    // diag = match n2 {
                    //     DomainName::Annonymous(loc) => diag
                    //         .secondary_label(loc, "'{{dg}} is the annonymous domain of this unit"),
                    //     DomainName::Named(_) => diag,
                    // };

                    Err(diag)
                }
            }
        }
    }
}

/*

  {error} | anything else => {error}
  {unknown} | {unknown} => Check for constraint compatibility, merge constraint list
  {unknown} | {tuple} => Check for !Async, produce {tuple}
  {known} | {tuple} => Merge {known} with all domains in the tuple, produce if successful {known}
  {known} | {known} => Check for identical domains
*/
