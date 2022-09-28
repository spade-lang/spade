use spade_common::{location_info::Loc, name::NameID};

use super::affine_state::MutWireWitness;

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("Unused affine variable")]
    UnusedAffineItem{definition: Loc<()>, witness: MutWireWitness},
    #[error("Multiple use of affine type")]
    UseOfConsumedAffineName{new_use: Loc<()>, previous_use: Loc<()>, witness: MutWireWitness}
}

pub type Result<T> = std::result::Result<T, Error>;
