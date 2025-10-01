use itertools::Itertools;
use serde::{Deserialize, Serialize};
use spade_common::{location_info::{Loc, WithLocation}, name::NameID};
use spade_hir::{domains::DomainName, pretty_print::PrettyPrint, TypeSpec};

use crate::DomainState;

#[derive(Clone, Serialize, Deserialize, Debug, PartialEq)]
pub enum KnownDomain {
    Annonymous,
    Named(NameID)
}

impl std::fmt::Display for KnownDomain  {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            KnownDomain::Annonymous => write!(f, "'_"),
            KnownDomain::Named(name_id) => write!(f, "'{name_id}"),
        }
    }
}

#[derive(Clone, Serialize, Deserialize, Debug)]
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
                    members
                        .iter()
                        .map(|domain| format!("{domain}"))
                        .join(", ")
                )
            }
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
            TypeSpec::WithDomain(domain, _) => {
                match &domain.inner {
                    DomainName::Annonymous => DomainVar::Known(KnownDomain::Annonymous),
                    DomainName::Const => DomainVar::Const,
                    DomainName::Async => DomainVar::Async,
                    DomainName::Named(name) => DomainVar::Known(KnownDomain::Named(name.inner.clone())),
                }
            },
        }.at_loc(spec)
    }
}
