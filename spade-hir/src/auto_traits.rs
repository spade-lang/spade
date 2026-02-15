use serde::{Deserialize, Serialize};
use spade_common::location_info::{Loc, WithLocation};

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
}


