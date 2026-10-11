use num::{BigUint, One};
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

pub fn length_spec(length: &BigUint) -> String {
    format!("[0:{}]", length - 1u32.to_biguint())
}

pub fn logic(name: &str, size: &BigUint) -> String {
    format!("logic{} {};", size_spec(size), name)
}
pub fn logic_array(name: &str, size: &BigUint, length: &BigUint) -> String {
    format!("logic{} {}{};", size_spec(size), name, length_spec(length))
}
pub fn reg(name: &str, size: &BigUint) -> String {
    format!("reg{} {};", size_spec(size), name)
}

pub fn slice(full_size: &BigUint, start: &BigUint, end: &BigUint) -> String {
    if (start, end) == (&(full_size - 1usize), &BigUint::ZERO) {
        String::new()
    } else if start == end {
        format!("[{}]", end)
    } else {
        format!("[{}:{}]", start, end)
    }
}

pub fn index(full_size: &BigUint, idx: &BigUint) -> String {
    if full_size.is_one() {
        String::new()
    } else {
        format!("[{}]", idx)
    }
}
