use num::{BigUint, CheckedSub};
use spade_common::{location_info::Loc, num_ext::InfallibleToBigUint};
use spade_diagnostics::{diag_anyhow, diag_bail};

use crate::Result;

pub fn assign(target: &str, value: &str) -> String {
    format!("assign {} = {};", target, value)
}

pub fn localparam_size_spec(size: &BigUint) -> String {
    format!("[{}:0]", size - 1u32.to_biguint())
}

pub fn size_spec(size: &Loc<BigUint>) -> Result<String> {
    if size.inner == 1u32.to_biguint() {
        Ok(String::new())
    } else {
        Ok(format!(
            "[{}:0]",
            size.checked_sub(&1u32.to_biguint())
                .ok_or_else(|| diag_anyhow!(size, "Sutraction with overflow while evaluating this. The size was {size}"))?
        ))
    }
}

pub fn logic(name: &str, size: &Loc<BigUint>) -> Result<String> {
    Ok(format!("logic{} {};", size_spec(size)?, name))
}
pub fn reg(name: &str, size: &Loc<BigUint>) -> Result<String> {
    Ok(format!("reg{} {};", size_spec(size)?, name))
}
