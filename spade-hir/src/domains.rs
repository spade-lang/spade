use serde::{Deserialize, Serialize};
use spade_common::{location_info::Loc, name::NameID};

#[derive(Hash, Eq, PartialEq, Debug, Clone, Serialize, Deserialize)]
pub enum DomainName {
    Annonymous,
    Const,
    Async,
    Named(Loc<NameID>),
}

impl std::fmt::Display for DomainName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DomainName::Annonymous => write!(f, "'_"),
            DomainName::Named(name) => write!(f, "'{name}"),
            DomainName::Const => write!(f, "'const"),
            DomainName::Async => write!(f, "'async"),
        }
    }
}
/**
  Constraints placed on a domain to make it more restrictive than the default domain
  which has:
  - A clock
  - An enable signal
  - Supports any reset kind, including `initial`
*/
#[derive(Eq, Hash, PartialEq, Debug, Clone, Serialize, Deserialize)]
pub enum DomainConstraint {
    /// Used in asynchronous domains which have no asociated clocks
    NoClock,
    /// Domains with registers which require a clock to be present
    HasClock,
}

#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub struct Domain {
    pub name: DomainName,
    pub constraints: Vec<Loc<DomainConstraint>>,
}

impl Domain {
    pub fn annonymous() -> Domain {
        Domain {
            name: DomainName::Annonymous,
            constraints: vec![],
        }
    }
}
