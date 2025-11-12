use std::collections::HashMap;

use itertools::Itertools;
use serde::{Deserialize, Serialize};
use spade_common::{
    location_info::{Loc, WithLocation},
    name::NameID,
};
use spade_diagnostics::Diagnostic;
use spade_hir::{domains::DomainName, pretty_print::PrettyPrint, TypeSpec};

use crate::{DomainState, FreeDomainVar};
use crate::Result;

#[derive(Clone, Serialize, Deserialize, Debug, PartialEq, Eq, Hash)]
pub enum KnownDomain {
    Annonymous,
    Named(NameID),
}

impl std::fmt::Display for KnownDomain {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            KnownDomain::Annonymous => write!(f, "'_"),
            KnownDomain::Named(name_id) => write!(f, "'{name_id}"),
        }
    }
}

#[derive(Clone, Serialize, Deserialize, Debug, PartialEq)]
pub enum DomainVar {
    Free(FreeDomainVar),
    Error,
    Const,
    Async,
    Known(KnownDomain),
    Tuple(Vec<DomainVar>),
}

impl std::fmt::Display for DomainVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DomainVar::Free(idx) => write!(f, "^{}", idx.0),
            DomainVar::Error => write!(f, "{{error}}"),
            DomainVar::Const => write!(f, "'const"),
            DomainVar::Async => write!(f, "'async"),
            DomainVar::Known(name) => {
                write!(f, "{}", name)
            }
            DomainVar::Tuple(members) => {
                write!(
                    f,
                    "({})",
                    members.iter().map(|domain| format!("{domain}")).join(", ")
                )
            }
        }
    }
}

impl DomainVar {
    // pub fn least_upper_domain(&self, b: &DomainVar) -> DomainVar {
    //     match (self, b) {
    //        (DomainVar::Error, _) | (_, DomainVar::Error) => DomainVar::Error,
    //         (DomainVar::Const, DomainVar::Const) => self.clone(),
    //         (DomainVar::Async, _) | (_, DomainVar::Async) => DomainVar::Async,

    //         (DomainVar::Const, other) | (other, DomainVar::Const) => other.clone(),

    //         // I'm not so sure about this one, we could end up merging two free domains into one later
    //         // so this will be conservative
    //         (DomainVar::Free(d1), DomainVar::Free(d2)) => {
    //             if d1 == d2 {
    //                 self.clone()
    //             } else {
    //                 DomainVar::Async
    //             }
    //         }

    //         (DomainVar::Known(d1), DomainVar::Known(d2)) => {
    //             if d1 == d2 {
    //                 self.clone()
    //             } else {
    //                 DomainVar::Async
    //             }
    //         }

    //         (name @ DomainVar::Known(_), DomainVar::Tuple(inner))
    //         | (DomainVar::Tuple(inner), name @ DomainVar::Known(_)) => {
    //             let mut result = name.clone();
    //             for i in inner {
    //                 result = result.least_upper_domain(i)
    //             }
    //             result
    //         }

    //         (DomainVar::Tuple(l), DomainVar::Tuple(r)) => DomainVar::Tuple(
    //             l.iter()
    //                 .zip(r)
    //                 .map(|(l, r)| l.least_upper_domain(r))
    //                 .collect(),
    //         ),
    //     }
    // }

    // pub fn is_subdomain_of(&self, other: &DomainVar) -> bool {
    //     let lud = self.least_upper_domain(other);
    //     &lud == self
    // }

    /// Collapses the domains in a tuple into the least upper domain of all tuple elements.
    /// Primarily used for checking things like clock constraints
    pub fn collapse_tuple_domains(&self) -> DomainVar {
        match self {
            DomainVar::Tuple(inner) => match inner.as_slice() {
                [] => DomainVar::Const,
                [single] => single.clone(),
                [first, rest @ ..] => {
                    let mut result = first.collapse_tuple_domains();
                    for i in rest {
                        result = result.least_upper_domain(&i.collapse_tuple_domains())
                    }
                    result
                }
            },
            _ => self.clone(),
        }
    }
}

impl DomainState {
    pub fn is_subdomain(lhs: &DomainVar, rhs: &DomainVar) {
        match (lhs, rhs) {
            (DomainVar::Error, _) | (_, DomainVar::Error) => true,

            (DomainVar::Async, DomainVar::Async) => true,
            (_, DomainVar::Async) => true,
            (DomainVar::Const, _) => true,

            (DomainVar::Known(d1), DomainVar::Known(d2)) => d1 == d2, // Roughly <:Var

            (DomainVar::Free(free_domain_var), DomainVar::Free(free_domain_var)) => todo!(),
            (DomainVar::Free(free_domain_var), DomainVar::Const) => todo!(),
            (DomainVar::Free(free_domain_var), DomainVar::Async) => todo!(),
            (DomainVar::Free(free_domain_var), DomainVar::Known(known_domain)) => todo!(),
            (DomainVar::Free(free_domain_var), DomainVar::Tuple(domain_vars)) => todo!(),
            (DomainVar::Const, DomainVar::Free(free_domain_var)) => todo!(),
            (DomainVar::Const, DomainVar::Const) => todo!(),
            (DomainVar::Const, DomainVar::Async) => todo!(),
            (DomainVar::Const, DomainVar::Known(known_domain)) => todo!(),
            (DomainVar::Const, DomainVar::Tuple(domain_vars)) => todo!(),
            (DomainVar::Async, DomainVar::Free(free_domain_var)) => todo!(),
            (DomainVar::Async, DomainVar::Const) => todo!(),
            (DomainVar::Async, DomainVar::Async) => todo!(),
            (DomainVar::Async, DomainVar::Known(known_domain)) => todo!(),
            (DomainVar::Async, DomainVar::Tuple(domain_vars)) => todo!(),
            (DomainVar::Known(known_domain), DomainVar::Free(free_domain_var)) => todo!(),
            (DomainVar::Known(known_domain), DomainVar::Const) => todo!(),
            (DomainVar::Known(known_domain), DomainVar::Async) => todo!(),
            (DomainVar::Known(known_domain), DomainVar::Known(known_domain)) => todo!(),
            (DomainVar::Known(known_domain), DomainVar::Tuple(domain_vars)) => todo!(),
            (DomainVar::Tuple(domain_vars), DomainVar::Free(free_domain_var)) => todo!(),
            (DomainVar::Tuple(domain_vars), DomainVar::Const) => todo!(),
            (DomainVar::Tuple(domain_vars), DomainVar::Async) => todo!(),
            (DomainVar::Tuple(domain_vars), DomainVar::Known(known_domain)) => todo!(),
            (DomainVar::Tuple(domain_vars), DomainVar::Tuple(domain_vars)) => todo!(),
        }
    }

    pub fn domain_from_type_spec(&self, spec: &Loc<TypeSpec>) -> Loc<DomainVar> {
        match &spec.inner {
            TypeSpec::Generic(_)
            | TypeSpec::Array { inner: _, size: _ }
            | TypeSpec::Inverted(_)
            | TypeSpec::Wire(_)
            | TypeSpec::TraitSelf(_)
            | TypeSpec::Wildcard(_)
            | TypeSpec::Declared(_, _) => DomainVar::Known(KnownDomain::Annonymous),
            TypeSpec::Tuple(inner) => DomainVar::Tuple(
                inner
                    .iter()
                    .map(|domain| self.domain_from_type_spec(domain).inner)
                    .collect(),
            ),
            // TODO: properly handle things like 'a ('b, 'c)
            TypeSpec::WithDomain(domain, _) => match &domain.inner {
                DomainName::Annonymous => DomainVar::Known(KnownDomain::Annonymous),
                DomainName::Const => DomainVar::Const,
                DomainName::Async => DomainVar::Async,
                DomainName::Named(name) => DomainVar::Known(KnownDomain::Named(name.inner.clone())),
            },
        }
        .at_loc(spec)
    }
}

