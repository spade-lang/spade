use std::collections::HashMap;

use itertools::Itertools;
use serde::{Deserialize, Serialize};
use spade_common::{
    location_info::{Loc, WithLocation},
    name::NameID,
};
use spade_diagnostics::Diagnostic;
use spade_hir::{domains::DomainName, pretty_print::PrettyPrint, TypeSpec};

use crate::DomainState;
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
    Error,
    Const,
    Async,
    Known(KnownDomain),
    Tuple(Vec<DomainVar>),
}

impl std::fmt::Display for DomainVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
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
    pub fn least_upper_domain(&self, b: &DomainVar) -> DomainVar {
        match (self, b) {
            (DomainVar::Error, _) | (_, DomainVar::Error) => DomainVar::Error,
            (DomainVar::Const, DomainVar::Const) => self.clone(),
            (DomainVar::Async, _) | (_, DomainVar::Async) => DomainVar::Async,

            (DomainVar::Const, other) | (other, DomainVar::Const) => other.clone(),

            (DomainVar::Known(d1), DomainVar::Known(d2)) => {
                if d1 == d2 {
                    self.clone()
                } else {
                    DomainVar::Async
                }
            }

            (name @ DomainVar::Known(_), DomainVar::Tuple(inner))
            | (DomainVar::Tuple(inner), name @ DomainVar::Known(_)) => {
                let mut result = name.clone();
                for i in inner {
                    result = result.least_upper_domain(i)
                }
                result
            }

            (DomainVar::Tuple(l), DomainVar::Tuple(r)) => DomainVar::Tuple(
                l.iter()
                    .zip(r)
                    .map(|(l, r)| l.least_upper_domain(r))
                    .collect(),
            ),
        }
    }

    pub fn is_subdomain_of(&self, other: &DomainVar) -> bool {
        let lud = self.least_upper_domain(other);
        &lud == self
    }

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

    pub fn map_foreign_names(
        &self,
        foreign: &Loc<DomainVar>,
        foreign_to_local_map: &mut HashMap<KnownDomain, DomainVar>,
    ) -> Result<DomainVar> {
        match self {
            DomainVar::Error => Ok(DomainVar::Error),
            DomainVar::Const | DomainVar::Async => {
                
            }
            DomainVar::Known(k) => todo!(),
            DomainVar::Tuple(domain_vars) => todo!(),
        }
    }
}

impl DomainState {
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

