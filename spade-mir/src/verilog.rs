use num::BigUint;
use spade_common::num_ext::InfallibleToBigUint;

pub fn assign(target: &str, value: &str) -> String {
    format!("assign {} = {};", target, value)
}

pub fn localparam_size_spec(size: &BigUint) -> String {
    format!("[{}:0]", size - 1u32.to_biguint())
}

pub fn size_spec(size: &BigUint) -> String {
    if size == &1u32.to_biguint() {
        String::new()
    } else {
        format!("[{}:0]", size - 1u32.to_biguint())
    }
}

pub fn logic(name: &str, size: &BigUint) -> String {
    format!("logic{} {};", size_spec(size), name)
}
pub fn reg(name: &str, size: &BigUint) -> String {
    format!("reg{} {};", size_spec(size), name)
}

pub fn slice(full_size: BigUint, start: BigUint, end: BigUint) -> String {
    let upper_idx = &full_size - &start - 1u32.to_biguint();
    let lower_idx = &full_size - &end;

    if (&upper_idx, &lower_idx) == (&(&full_size - 1usize), &BigUint::ZERO) {
        String::new()
    } else if upper_idx == lower_idx {
        format!("[{}]", lower_idx)
    } else {
        format!("[{}:{}]", upper_idx, lower_idx)
    }
}
