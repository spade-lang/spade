use serde::{Deserialize, Serialize};
use spade_common::{location_info::Loc, name::NameID};

#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub enum DomainName {
    Annonymous,
    Named(Loc<NameID>)
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
