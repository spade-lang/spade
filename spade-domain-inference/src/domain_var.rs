use itertools::Itertools;
use serde::{Deserialize, Serialize};
use spade_common::location_info::{Loc, WithLocation};
use spade_hir::{domains::DomainName, pretty_debug::PrettyDebug, pretty_print::PrettyPrint, TypeSpec};

use crate::DomainState;

#[derive(Clone, Serialize, Deserialize)]
pub enum DomainVar {
    Error,
    Const,
    Async,
    Known(DomainName),
    Tuple(Vec<Loc<DomainVar>>),
}

impl std::fmt::Display for DomainVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DomainVar::Error => write!(f, "{{error}}"),
            DomainVar::Const => write!(f, "'const"),
            DomainVar::Async => write!(f, "'async"),
            DomainVar::Known(domain_name) => {
                write!(f, "{}", domain_name.pretty_print(),)
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

impl std::fmt::Debug for DomainVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DomainVar::Error => write!(f, "{{error}}"),
            DomainVar::Const => write!(f, "'const"),
            DomainVar::Async => write!(f, "'async"),
            DomainVar::Known(domain_name) => {
                write!(f, "'{}", domain_name.pretty_debug(),)
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

impl DomainState {
    pub fn domain_from_type_spec(&self, spec: &Loc<TypeSpec>) -> Loc<DomainVar> {
        match &spec.inner {
            TypeSpec::Generic(_)
            | TypeSpec::Array { inner: _, size: _ }
            | TypeSpec::Inverted(_)
            | TypeSpec::Wire(_)
            | TypeSpec::TraitSelf(_)
            | TypeSpec::Wildcard(_)
            | TypeSpec::Declared(_, _) => DomainVar::Known(DomainName::Annonymous),
            TypeSpec::Tuple(inner) => DomainVar::Tuple(
                inner
                    .iter()
                    .map(|domain| self.domain_from_type_spec(domain))
                    .collect(),
            ),
            TypeSpec::WithDomain(domain, _) => DomainVar::Known(domain.inner.clone()),
        }.at_loc(spec)
    }
}
