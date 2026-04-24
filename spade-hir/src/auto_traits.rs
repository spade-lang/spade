use serde::{Deserialize, Serialize};
use spade_common::location_info::{Loc, WithLocation};

/// A witness for a type statically not being Copy
#[derive(Debug, Serialize, Deserialize)]
pub enum CopyWitness {
    Here(Loc<()>),
    Recursive(Box<Loc<CopyWitness>>),
}

impl CopyWitness {
    pub fn recurse(self, loc: &Loc<()>) -> Self {
        Self::Recursive(Box::new(self.at_loc(&loc)))
    }

    pub fn loc(&self) -> Loc<()> {
        match self {
            CopyWitness::Here(here) => here.clone(),
            CopyWitness::Recursive(inner) => inner.loc(),
        }
    }
}

/// A witness for a type statically not being Data
#[derive(Debug, Serialize, Deserialize)]
pub enum DataWitness {
    Here(Loc<()>),
    Recursive(Box<Loc<DataWitness>>),
}

impl DataWitness {
    pub fn recurse(self, loc: &Loc<()>) -> Self {
        Self::Recursive(Box::new(self.at_loc(&loc)))
    }

    pub fn loc(&self) -> Loc<()> {
        match self {
            DataWitness::Here(here) => here.clone(),
            DataWitness::Recursive(inner) => inner.loc(),
        }
    }
}
