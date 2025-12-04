mod translation;

use std::{fs::File, path::PathBuf};

use clap::Parser;
use color_eyre::{
    eyre::{anyhow, Context},
    Result,
};
use rustc_hash::FxHashMap as HashMap;
use spade::compiler_state::CompilerState;
use spade_common::{
    location_info::WithLocation,
    name::{NameID, Path},
};
use spade_types::ConcreteType;
use vcd::{IdCode, ScopeItem};

use std::io::{BufReader, BufWriter};

use crate::translation::translate_value;

#[derive(clap::Parser)]
struct CliArgs {
    infile: PathBuf,
    #[clap(short)]
    state_file: PathBuf,
    #[clap(short = 'o', default_value = "out.vcd")]
    outfile: PathBuf,
    #[clap(short = 't')]
    top: String,
}

#[derive(Debug, Clone)]
struct VarInfo {
    pub parsed: IdCode,
    pub ty: ConcreteType,
}

#[derive(Debug, Clone)]
struct MappedVar {
    pub raw: IdCode,
    pub info: Option<VarInfo>,
}

type NewVarMap = HashMap<IdCode, Vec<MappedVar>>;

fn add_new_vars(
    top_module: &NameID,
    mut result: NewVarMap,
    items: &[ScopeItem],
    writer: &mut vcd::Writer<impl std::io::Write>,
    hierarchy: &[String],
    state: &CompilerState,
) -> Result<NewVarMap> {
    for item in items {
        match item {
            ScopeItem::Scope(scope) => {
                writer.scope_def(scope.scope_type, &scope.identifier)?;
                let mut new_path = Vec::from(hierarchy);
                new_path.push(scope.identifier.clone());
                result = add_new_vars(
                    top_module,
                    result,
                    &scope.children,
                    writer,
                    &new_path,
                    state,
                )?;
                writer.upscope()?;
            }
            ScopeItem::Var(var) => {
                let raw = writer.add_var(var.var_type, var.size, &var.reference, var.index)?;
                let parsed = writer.add_var(
                    vcd::VarType::String,
                    1,
                    &format!("#{}", var.reference),
                    None,
                )?;

                // NOTE: The top module will be part of the hierarchy, but we want to
                // use the CLI specified top module instead
                let mut full_path = Vec::from(&hierarchy[1..]);
                full_path.push(var.reference.clone());

                // we know we won't be able to find types for some values, so we'll silently skip those
                let info = match state.type_of_hierarchical_value(top_module, &full_path) {
                    Ok(ty) => Some(VarInfo { parsed, ty }),
                    Err(_e) => None,
                };

                let new_map = MappedVar { raw, info };

                result.entry(var.code).or_default().push(new_map.clone());
            }
        }
    }
    Ok(result)
}

fn main() -> Result<()> {
    color_eyre::install()?;

    let args = CliArgs::parse();

    let reader = BufReader::new(
        File::open(&args.infile).with_context(|| format!("Failed to open {:?}", args.infile))?,
    );
    let mut parser = vcd::Parser::new(reader);

    let header = parser
        .parse_header()
        .context("Failed to parse vcd header")?;

    let mut outfile = BufWriter::new(
        File::create(&args.outfile)
            .with_context(|| format!("Failed to open outfile {:?}", args.outfile))?,
    );
    let mut writer = vcd::Writer::new(&mut outfile);

    if let Some((t, unit)) = header.timescale {
        writer.timescale(t, unit)?
    }

    let state_file = std::fs::read_to_string(&args.state_file)
        .with_context(|| format!("Failed to read state file {:?}", args.state_file))?;

    let compiler_state: CompilerState = ron::from_str(&state_file)
        .with_context(|| format!("failed to decode compiler state in {:?}", args.state_file))?;

    let top_path = Path::from_strs(&args.top.split("::").collect::<Vec<_>>()).nowhere();
    let (top, _) = compiler_state
        .symtab
        .symtab()
        .lookup_unit(&top_path)
        .map_err(|_e| anyhow!("Did not find a unit named {}", args.top))?;

    let var_map = add_new_vars(
        &top,
        HashMap::default(),
        &header.items,
        &mut writer,
        &[],
        &compiler_state,
    )?;
    writer.enddefinitions()?;

    for command_result in parser {
        use vcd::Command::*;
        let command = command_result?;
        match command {
            ChangeScalar(id, value) => {
                for mapped in &var_map[&id] {
                    writer.change_scalar(mapped.raw, value)?;
                    if let Some(info) = &mapped.info {
                        let val = translate_value(&info.ty, &[value]);
                        writer.change_string(info.parsed, &val)?;
                    }
                }
            }
            ChangeVector(id, value) => {
                for mapped in &var_map[&id] {
                    writer.change_vector(mapped.raw, &value)?;
                    if let Some(info) = &mapped.info {
                        let translated = translate_value(&info.ty, &value);
                        let with_color = if translated.contains("UNDEF") && translated != "UNDEF" {
                            format!("?DarkOrange4?{translated}")
                        } else if translated.contains("HIGHIMP") {
                            format!("?Goldenrod?{translated}")
                        } else if translated.starts_with("Option::None") {
                            format!("?DarkSeaGreen4?{translated}")
                        } else {
                            translated
                        };
                        writer.change_string(info.parsed, &with_color)?;
                    }
                }
            }
            ChangeReal(id, value) => {
                for mapped in &var_map[&id] {
                    writer.change_real(mapped.raw, value)?
                }
            }
            ChangeString(id, value) => {
                for mapped in &var_map[&id] {
                    writer.change_string(mapped.raw, &value)?
                }
            }
            other => writer.command(&other)?,
        }
    }

    Ok(())
}
