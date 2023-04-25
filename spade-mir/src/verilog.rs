use num::BigUint;
use spade_common::num_ext::InfallibleToBigUint;

pub fn assign(target: &str, value: &str) -> String {
    format!("assign {} = {};", target, value)
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
