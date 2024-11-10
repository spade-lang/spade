use std::ops::Deref;

use color_eyre::eyre::bail;
use color_eyre::eyre::Context;
use color_eyre::eyre::Result;
use color_eyre::owo_colors::OwoColorize;
use cxx::CxxString;
use num::ToPrimitive;

struct CompilerState(pub spade::compiler_state::CompilerState);

impl CompilerState {
    fn list_names(&self) {
        for (from, to) in &self.name_source_map.inner {
            println!("{from} -> {to}")
        }
    }

    fn demangle_name(&self, name: &str) -> String {
        self.0
            .demangle_string(name)
            .unwrap_or(format!("(not demangled) {name}"))
    }
}

fn read_state(path: &str) -> Result<Box<CompilerState>> {
    let file = std::fs::read_to_string(path)
        .with_context(|| "Failed to read compiler state from {path}")?;

    let ron = ron::Options::default().without_recursion_limit();

    Ok(Box::new(CompilerState(
        ron.from_str(&file)
            .context("Failed to decode compiler state in {path}")?,
    )))
}

impl Deref for CompilerState {
    type Target = spade::compiler_state::CompilerState;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

struct SignalValue(pub spade_mir::eval::Value);

impl SignalValue {
    fn as_u64(&self) -> u64 {
        self.0.as_u64()
    }

    fn as_u32_chunks(&self) -> Vec<u32> {
        let mut digits = self.0.as_u32_chunks().to_u32_digits();
        let expected_digit_count = ((self
            .0
            .width()
            .to_u64()
            .expect("Value size does not fit in u64") as f64)
            / 32.)
            .ceil() as u64;

        digits.extend_from_slice(&vec![0; expected_digit_count as usize - digits.len()]);
        digits
    }
}

struct SimulationExt(pub spade_simulation_ext::Spade);
struct BitString(spade_simulation_ext::BitString);

fn new_bit_string(s: &CxxString) -> Box<BitString> {
    Box::new(BitString(spade_simulation_ext::BitString(s.to_string())))
}

struct ComparisonResult(spade_simulation_ext::ComparisonResult);
impl ComparisonResult {
    fn matches(&self) -> bool {
        self.0.matches()
    }
}

struct FieldRef(spade_simulation_ext::field_ref::FieldRef);

fn setup_spade(uut_name: String, state_path: String) -> Result<Box<SimulationExt>> {
    Ok(Box::new(SimulationExt(spade_simulation_ext::Spade::new(
        uut_name, state_path,
    )?)))
}

impl SimulationExt {
    pub fn port_value(&mut self, port: &str, expr: &str) -> Result<Box<SignalValue>> {
        self.0
            .port_value_raw(port, expr)
            .map(|(_, value)| Box::new(SignalValue(value)))
    }

    pub fn compare_field(
        &mut self,
        // The field to compare
        field: &FieldRef,
        // The spade expression to compare against
        spade_expr: &str,
        // The bits of the whole output struct
        output_bits: &BitString,
    ) -> Result<Box<ComparisonResult>> {
        self.0
            .compare_field(field.0.clone(), spade_expr, &output_bits.0)
            .map(|o| Box::new(ComparisonResult(o)))
    }

    pub fn assert_eq(
        &mut self,
        // The field to compare
        field: &FieldRef,
        // The spade expression to compare against
        spade_expr: &str,
        // The bits of the whole output struct
        output_bits: &BitString,
        source_loc: &str,
    ) -> Result<()> {
        let cmp_result = self
            .0
            .compare_field(field.0.clone(), spade_expr, &output_bits.0)?;

        if !cmp_result.matches() {
            println!("{}", source_loc.to_string().red());
            println!("\texpected: {}", cmp_result.expected_spade);
            println!("\tgot:      {}", cmp_result.got_spade);
            println!();
            println!(
                "\tverilog (\n\t'{}' != \n\t'{}')",
                cmp_result.expected_bits.0.green(),
                cmp_result.got_bits.0.red()
            );
            bail!("{source_loc}: assertion failed");
        }
        Ok(())
    }

    pub fn output_field(&mut self, path: &Vec<String>) -> Result<Box<FieldRef>> {
        self.0.output_field(path.clone()).and_then(|o| match o {
            Some(field) => Ok(Box::new(FieldRef(field))),
            None => bail!("Trying to access output field on a unit returning void"),
        })
    }

    pub fn field_value(&mut self, field: &FieldRef, output_bits: &BitString) -> Result<String> {
        self.0.field_value(field.0.clone(), &output_bits.0)
    }
}

#[cxx::bridge(namespace = "spade")]
mod ffi {

    extern "Rust" {
        type FieldRef;
    }

    extern "Rust" {
        type BitString;
    }

    extern "Rust" {
        type ComparisonResult;

        fn matches(&self) -> bool;
    }

    extern "Rust" {
        fn new_bit_string(s: &CxxString) -> Box<BitString>;
    }

    extern "Rust" {
        type SignalValue;

        fn as_u64(&self) -> u64;
        fn as_u32_chunks(&self) -> Vec<u32>;
    }

    extern "Rust" {
        type CompilerState;

        fn read_state(path: &str) -> Result<Box<CompilerState>>;
        fn list_names(&self);
        fn demangle_name(&self, name: &str) -> String;
    }

    extern "Rust" {
        type SimulationExt;

        fn setup_spade(uut_name: String, state_path: String) -> Result<Box<SimulationExt>>;
        fn port_value(&mut self, port: &str, expr: &str) -> Result<Box<SignalValue>>;
        fn compare_field(
            &mut self,
            // The field to compare
            field: &FieldRef,
            // The spade expression to compare against
            spade_expr: &str,
            // The bits of the whole output struct
            output_bits: &BitString,
        ) -> Result<Box<ComparisonResult>>;
        fn assert_eq(
            &mut self,
            // The field to compare
            field: &FieldRef,
            // The spade expression to compare against
            spade_expr: &str,
            // The bits of the whole output struct
            output_bits: &BitString,
            source_loc: &str,
        ) -> Result<()>;

        fn output_field(&mut self, path: &Vec<String>) -> Result<Box<FieldRef>>;

        pub fn field_value(&mut self, field: &FieldRef, output_bits: &BitString) -> Result<String>;
    }
}
