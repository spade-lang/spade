use std::{collections::HashMap, ops::Range};

use camino::{Utf8Path, Utf8PathBuf};
use ecolor::Color32;
use extism_pdk::{error, info, plugin_fn, FnResult, Json, WithReturnCode};

use itertools::Itertools;
use num::ToPrimitive;
use serde::{Deserialize, Serialize};
use spade::compiler_state::CompilerState;

use color_eyre::{
    eyre::{anyhow, bail, Context, ContextCompat},
    Result,
};
use spade_common::{
    location_info::{Loc, WithLocation},
    name::{Identifier, NameID, Path},
};
use spade_hir::{expression::CallKind, query::QueryCache, Expression};
use spade_hir_lowering::{name_map::NameSource, MirLowerable};
use spade_types::{ConcreteType, PrimitiveType};
use std::sync::Mutex;
use surfer_translation_types::{
    // translator::{TrueName, VariableNameInfo},
    plugin_types::TranslateParams,
    translator::TrueName,
    SubFieldTranslationResult,
    TranslationResult,
    ValueRepr,
    VariableMeta,
    VariableNameInfo,
    WaveSource,
};

use surfer_translation_types::{TranslationPreference, ValueKind, VariableInfo, VariableValue};

mod host {
    use extism_pdk::host_fn;

    #[host_fn]
    extern "ExtismHost" {
        pub fn read_file(filename: String) -> Vec<u8>;
        pub fn file_exists(filename: String) -> bool;
    }
}

fn read_file(filename: &Utf8Path) -> Result<Vec<u8>> {
    unsafe { host::read_file(filename.to_string()) }
        .map_err(|e| anyhow!("Failed to read {filename}. {e}"))
}

fn read_file_to_string(filename: &Utf8Path) -> Result<String> {
    String::from_utf8(read_file(filename)?).map_err(|_| anyhow!("{filename} was not valid utf8"))
}

fn file_exists(filename: &Utf8Path) -> Result<bool> {
    unsafe { host::file_exists(filename.to_string()) }
        .map_err(|e| anyhow!("Failed to check if {filename} exists {e}"))
}

trait ResultExt<T> {
    fn handle(self) -> FnResult<T>;
}
impl<T> ResultExt<T> for Result<T> {
    fn handle(self) -> FnResult<T> {
        match self {
            Ok(r) => Ok(r),
            Err(e) => Err(WithReturnCode::new(
                extism_pdk::Error::msg(format!("{e:#}")),
                1,
            )),
        }
    }
}

static STATE: Mutex<Option<SpadeTranslator>> = Mutex::new(None);

/// Same as the swim::SurferInfo struct
#[derive(Deserialize, Clone)]
pub struct SpadeTestInfo {
    pub state_file: Utf8PathBuf,
    pub top_names: HashMap<Utf8PathBuf, String>,
}

#[derive(Deserialize, Serialize)]
pub struct SpadeTranslator {
    // The compiler state is not thread safe so we have to throw it in a
    // mutex. A tokio mutex would be nice but causes blocking unwraps so since
    // we're in a blocking context anyway, we'll use a std mutex
    state: Mutex<CompilerState>,
    query_cache: QueryCache,
    top: NameID,
    top_name: String,
    state_file: Option<Utf8PathBuf>,
}

impl SpadeTranslator {
    pub fn new(wave_file: &Utf8Path) -> Result<Self> {
        let surfer_ron_file = Utf8PathBuf::from("build/surfer.ron");

        if !file_exists(&surfer_ron_file)? {
            bail!("Disabling Spade translator since {surfer_ron_file} does not exist");
        }
        let surfer_ron_content = read_file_to_string(&surfer_ron_file)
            .with_context(|| format!("Failed to read {surfer_ron_file}"))?;

        let (top_name, state_file) = ron::from_str::<SpadeTestInfo>(&surfer_ron_content)
            .map_err(|e| error!("Failed to decode {surfer_ron_file}. {e}"))
            .ok()
            .and_then(|info| {
                if let Some(top) = info.top_names.get(wave_file) {
                    Some((top.clone(), info.state_file.clone()))
                } else {
                    extism_pdk::warn!(
                        "Found no spade info for {wave_file}. Disabling spade translation"
                    );
                    None
                }
            })
            .ok_or_else(|| anyhow!("Failed to initialize Spade translator"))?;

        Self::new_from_state_bytes(
            &top_name,
            &read_file(&state_file)?,
            Some(state_file.to_path_buf()),
        )
        .context(format!("When loading Spade state from {state_file}"))
    }

    pub fn new_from_state_bytes(
        top_name: &str,
        state_content: &[u8],
        state_file: Option<Utf8PathBuf>,
    ) -> Result<Self> {
        let state = Mutex::new(
            bincode::serde::decode_from_slice::<CompilerState, _>(
                state_content,
                bincode::config::standard(),
            )
            .with_context(|| "Failed to decode Spade state")?
            .0,
        );

        let path = top_name
            .split("::")
            .map(|s| Identifier(s.to_string()).nowhere());
        let (top, _) = state
            .lock()
            .unwrap()
            .symtab
            .symtab()
            .lookup_unit(&Path(path.collect()).nowhere())
            .map_err(|_| anyhow!("Did not find a unit {top_name} in Spade state"))?;

        let query_cache = state.lock().unwrap().build_query_cache();

        Ok(Self {
            state,
            query_cache,
            top,
            top_name: top_name.to_string(),
            state_file,
        })
    }
}

#[plugin_fn]
pub fn new() -> FnResult<()> {
    Ok(())
}

#[plugin_fn]
pub fn name() -> FnResult<String> {
    Ok("Spade (WASM)".to_string())
}

#[plugin_fn]
pub fn set_wave_source(Json(wave_source): Json<Option<WaveSource>>) -> FnResult<()> {
    if let Some(wave_source) = wave_source {
        let file = match wave_source {
            WaveSource::File(f) => Some(f),
            WaveSource::Data => None,
            WaveSource::DragAndDrop(f) => f,
            WaveSource::Url(_) => None,
            WaveSource::Cxxrtl => None,
        };

        if let Some(file) = file {
            let ctx = SpadeTranslator::new(&Utf8PathBuf::from(file)).handle()?;
            // extism_pdk::var::set("state", ctx).unwrap();
            *STATE.lock().unwrap() = Some(ctx);
            Ok(())
        } else {
            extism_pdk::info!("Not loading Spade translator for non-files");
            Ok(())
        }
    } else {
        *STATE.lock().unwrap() = None;
        Ok(())
    }
}

#[plugin_fn]
pub fn translate(
    TranslateParams { variable, value }: TranslateParams,
) -> FnResult<TranslationResult> {
    let mutex = STATE.lock().unwrap();
    let Some(ctx) = mutex.as_ref() else {
        return Err(anyhow!(
            "Spade translator asked to translate before state was loaded."
        ))
        .handle();
    };

    let ty = ctx
        .state
        .lock()
        .unwrap()
        .type_of_hierarchical_value(&ctx.top, &variable.var.full_path()[1..])
        .handle()?;

    let val_vcd_raw = match value {
        VariableValue::BigUint(v) => format!("{v:b}"),
        VariableValue::String(v) => v.clone(),
    };
    let mir_ty = ty.to_mir_type();
    let ty_size = mir_ty
        .size()
        .to_usize()
        .context("Type size does not fit in usize")
        .handle()?;
    let extra_bits = if ty_size > val_vcd_raw.len() {
        let extra_count = ty_size - val_vcd_raw.len();
        let extra_value = match val_vcd_raw.chars().next() {
            Some('0') => "0",
            Some('1') => "0",
            Some('x') => "x",
            Some('z') => "z",
            // other => Err(anyhow!("Found non-bit value in vcd ({other:?})"),
            _ => "?",
        };
        extra_value.repeat(extra_count)
    } else {
        String::new()
    };
    let val_vcd = format!("{extra_bits}{val_vcd_raw}",);
    translate_concrete(&val_vcd, &ty, &mut false).handle()
}

#[plugin_fn]
pub fn variable_info(variable: VariableMeta<(), ()>) -> FnResult<VariableInfo> {
    let mutex = STATE.lock().unwrap();
    let Some(ctx) = mutex.as_ref() else {
        return Err(anyhow!(
            "Spade translator asked to translate before state was loaded."
        ))
        .handle();
    };
    let ty = ctx
        .state
        .lock()
        .unwrap()
        .type_of_hierarchical_value(&ctx.top, &variable.var.full_path()[1..])
        .handle()?;

    info_from_concrete(&ty).handle()
}

#[plugin_fn]
pub fn translates(variable: VariableMeta<(), ()>) -> FnResult<TranslationPreference> {
    let mutex = STATE.lock().unwrap();
    let Some(ctx) = mutex.as_ref() else {
        return Err(anyhow!(
            "Spade translator asked to translate before state was loaded."
        ))
        .handle();
    };
    let ty = ctx
        .state
        .lock()
        .unwrap()
        .type_of_hierarchical_value(&ctx.top, &variable.var.full_path()[1..])
        .handle()?;

    match ty {
        ConcreteType::Single {
            base: PrimitiveType::Clock,
            params: _,
        } => Ok(TranslationPreference::Prefer),
        ConcreteType::Single { base: _, params: _ } => Ok(TranslationPreference::No),
        _ => Ok(TranslationPreference::Prefer),
    }
}
#[plugin_fn]
pub fn variable_name_info(
    Json(variable): Json<surfer_translation_types::VariableMeta<(), ()>>,
) -> FnResult<Option<VariableNameInfo>> {
    let mutex = STATE.lock().unwrap();
    let Some(ctx) = mutex.as_ref() else {
        return Err(anyhow!(
            "Spade translator asked to translate before state was loaded."
        ))
        .handle();
    };
    let state = ctx.state.lock().unwrap();

    let Some(info) = state
        .name_source_of_hierarchical_value(
            &ctx.top,
            &variable.var.full_path()[1..],
            &ctx.query_cache,
        )
        .ok()
    else {
        return Ok(None);
    };

    let result = match info {
        Some(source) => {
            match source {
                NameSource::Name(_) => {
                    // FIXME: We could consider resolving names with multiple IDs
                    Some(VariableNameInfo {
                        true_name: None,
                        priority: Some(2),
                    })
                }
                NameSource::Expr(id) => {
                    let true_name = ctx
                        .query_cache
                        .id_to_expression(id.inner)
                        .and_then(|expr| descriptive_loc(expr))
                        .and_then(|loc| loc.resolve(&state.code))
                        .as_ref()
                        .map(ResolvedLoc::to_true_name);

                    let priority = match true_name {
                        Some(_) => Some(1),
                        None => Some(0),
                    };
                    Some(VariableNameInfo {
                        true_name,
                        priority,
                    })
                }
            }
        }
        None => None,
    };
    Ok(result)
}

#[plugin_fn]
pub fn reload() -> FnResult<()> {
    // At this point, we have already loaded the spade info on the first load, so can just
    // pass None as the wave source
    error!("Wasm spade translator does not implement reloading");
    Ok(())
}

struct ResolvedLoc<'a> {
    /// The line number that the Loc starts at
    pub line_index: usize,
    /// The full lines which contain the Loc, for example if a loc points to the `a`s here,
    /// the lines will be the middle 3 lines, but not the first or last line
    /// ```notest
    /// xxxxx
    /// xxxxaaa
    /// aaa
    /// axxxx
    /// xxxxx
    /// ```
    pub lines: &'a str,
    /// The span inside `lines` that this loc actually contains, as byte offsets
    pub relevant_span: Range<usize>,
}

impl<'a> ResolvedLoc<'a> {
    fn to_true_name(&self) -> TrueName {
        let before = &self.lines[0..self.relevant_span.start];
        let during_ = &self.lines[self.relevant_span.start..self.relevant_span.end];
        let (during, after) =
            if let Some((idx, _)) = during_.bytes().enumerate().find(|(_, c)| *c == b'\n') {
                let during = &during_[0..idx];
                (during, "")
            } else {
                (during_, &self.lines[self.relevant_span.end..])
            };

        TrueName::SourceCode {
            line_number: self.line_number(),
            before: before.trim_start().to_string(),
            this: during.to_string(),
            after: after.trim_end().to_string(),
        }
    }

    fn line_number(&self) -> usize {
        self.line_index + 1
    }
}

trait LocExt {
    fn resolve<'a>(self, files: &'a [(String, String)]) -> Option<ResolvedLoc<'a>>;
}

impl<T> LocExt for Loc<T> {
    fn resolve<'a>(self, files: &'a [(String, String)]) -> Option<ResolvedLoc<'a>> {
        let span = self.span;
        let (_, content) = files.get(self.file_id)?;

        let mut lines_before_start = 0;
        let mut chars_before_start = 0;
        for c in content.bytes().take(self.span.start().to_usize()) {
            if c == b'\n' {
                chars_before_start = 0;
                lines_before_start += 1;
            } else {
                chars_before_start += 1;
            }
        }

        let chars_past_end = content
            .bytes()
            .skip(self.span.end().to_usize())
            .enumerate()
            .find_or_last(|(_, c)| *c == b'\n')
            .map(|(i, _)| i)
            .unwrap_or(content.len() - span.end().to_usize());

        Some(ResolvedLoc {
            line_index: lines_before_start,
            lines: &content[span.start().to_usize() - chars_before_start
                ..chars_past_end + span.end().to_usize()],
            relevant_span: (chars_before_start
                ..(chars_before_start + (span.end().to_usize() - span.start().to_usize()))),
        })
    }
}

fn not_present_value(ty: &ConcreteType) -> TranslationResult {
    let subfields = match ty {
        ConcreteType::Tuple(inner) => inner
            .iter()
            .enumerate()
            .map(|(i, t)| SubFieldTranslationResult::new(i, not_present_value(t)))
            .collect(),
        ConcreteType::Struct {
            name: _,
            members,
            is_port: _,
            field_translators: _,
        } => members
            .iter()
            .map(|(n, t)| SubFieldTranslationResult::new(n, not_present_value(t)))
            .collect(),
        ConcreteType::Array { inner, size } => (0..(size.to_u64().unwrap()))
            .map(|i| SubFieldTranslationResult::new(i, not_present_value(inner)))
            .collect(),
        ConcreteType::Enum { options } => not_present_enum_options(options),
        ConcreteType::Single { .. } => vec![],
        ConcreteType::Integer(_) | ConcreteType::Bool(_) | ConcreteType::String(_) => vec![],
        ConcreteType::Backward(inner) | ConcreteType::Wire(inner) => {
            not_present_value(inner).subfields
        }
        ConcreteType::Error => {
            vec![]
        }
    };

    TranslationResult {
        val: ValueRepr::NotPresent,
        subfields,
        kind: ValueKind::Normal,
    }
}

fn not_present_enum_fields(
    fields: &[(Identifier, ConcreteType)],
) -> Vec<SubFieldTranslationResult> {
    fields
        .iter()
        .map(|(name, ty)| SubFieldTranslationResult::new(name.0.clone(), not_present_value(ty)))
        .collect()
}

fn not_present_enum_options(
    options: &[(NameID, Vec<(Identifier, ConcreteType)>)],
) -> Vec<SubFieldTranslationResult> {
    options
        .iter()
        .map(|(opt_name, opt_fields)| SubFieldTranslationResult {
            name: opt_name.1.tail().0.clone(),
            result: TranslationResult {
                val: ValueRepr::NotPresent,
                subfields: not_present_enum_fields(opt_fields),
                kind: ValueKind::Normal,
            },
        })
        .collect()
}

fn translate_concrete(
    val: &str,
    ty: &ConcreteType,
    problematic: &mut bool,
) -> Result<TranslationResult> {
    macro_rules! handle_problematic {
        ($kind:expr) => {
            if *problematic {
                ValueKind::Warn
            } else {
                $kind
            }
        };
        () => {
            handle_problematic!(ValueKind::Normal)
        };
    }
    let mir_ty = ty.to_mir_type();
    let result = match ty {
        ConcreteType::Tuple(inner) => {
            let mut subfields = vec![];
            let mut offset = 0;
            for (i, t) in inner.iter().enumerate() {
                let mut local_problematic = false;
                let end = offset
                    + t.to_mir_type()
                        .size()
                        .to_usize()
                        .context(format!("Value is wider than {} bits", usize::MAX))?;
                let new = translate_concrete(&val[offset..end], t, &mut local_problematic)?;
                offset = end;
                subfields.push(SubFieldTranslationResult::new(i, new));
                *problematic |= local_problematic;
            }

            TranslationResult {
                val: ValueRepr::Tuple,
                subfields,
                kind: handle_problematic!(),
            }
        }
        ConcreteType::Struct {
            name: _,
            members,
            is_port: _,
            field_translators: _,
        } => {
            let mut subfields = vec![];
            let mut offset = 0;
            for (n, t) in members.iter() {
                let mut local_problematic = false;
                let end = offset
                    + t.to_mir_type()
                        .size()
                        .to_usize()
                        .context(format!("Value is wider than {} bits", usize::MAX))?;
                let new = translate_concrete(&val[offset..end], t, &mut local_problematic)?;
                *problematic |= local_problematic;
                offset = end;
                subfields.push(SubFieldTranslationResult::new(n.0.clone(), new));
            }

            TranslationResult {
                val: ValueRepr::Tuple,
                subfields,
                kind: handle_problematic!(),
            }
        }
        ConcreteType::Array { inner, size } => {
            let mut subfields = vec![];
            let mut offset = 0;
            for n in 0..size
                .to_usize()
                .context(format!("Array size is greater than {}", usize::MAX))?
            {
                let mut local_problematic = false;
                let end = offset
                    + inner
                        .to_mir_type()
                        .size()
                        .to_usize()
                        .context(format!("Value is wider than {} bits", usize::MAX))?;
                let new = translate_concrete(&val[offset..end], inner, &mut local_problematic)?;
                *problematic |= local_problematic;
                offset = end;
                subfields.push(SubFieldTranslationResult::new(n, new));
            }

            TranslationResult {
                val: ValueRepr::Array,
                subfields,
                kind: handle_problematic!(),
            }
        }
        ConcreteType::Enum { options } => {
            let tag_size = (options.len() as f32).log2().ceil() as usize;
            let tag_section = &val[0..tag_size];
            if tag_section.contains('x') {
                *problematic = true;
                TranslationResult {
                    val: ValueRepr::String(format!("xTAG(0b{tag_section})")),
                    subfields: not_present_enum_options(options),
                    kind: ValueKind::Undef,
                }
            } else if tag_section.contains('z') {
                *problematic = true;
                TranslationResult {
                    val: ValueRepr::String(format!("zTAG(0b{tag_section})")),
                    subfields: not_present_enum_options(options),
                    kind: ValueKind::HighImp,
                }
            } else {
                let tag = usize::from_str_radix(tag_section, 2)
                    .with_context(|| format!("Unexpected characters in enum tag {tag_section}"))?;

                if tag > options.len() {
                    *problematic = true;
                    TranslationResult {
                        val: ValueRepr::String(format!("?TAG(0b{tag_section})")),
                        subfields: not_present_enum_options(options),
                        kind: ValueKind::Undef,
                    }
                } else {
                    let mut kind = ValueKind::Normal;
                    let subfields = options
                        .iter()
                        .enumerate()
                        .map(|(i, (name, fields))| {
                            let name = name.1.tail().0;
                            let mut offset = tag_size;

                            let subfields = fields
                                .iter()
                                .map(|(f_name, f_ty)| {
                                    let mut local_problematic = false;
                                    let end = offset
                                        + f_ty.to_mir_type().size().to_usize().context(format!(
                                            "Value is wider than {} bits",
                                            usize::MAX
                                        ))?;
                                    let new = translate_concrete(
                                        &val[offset..end],
                                        f_ty,
                                        &mut local_problematic,
                                    )?;
                                    offset = end;

                                    *problematic |= local_problematic;

                                    Ok(SubFieldTranslationResult::new(f_name.0.clone(), new))
                                })
                                .collect::<Result<_>>()?;

                            let result = if i == tag {
                                if name == "None" {
                                    kind = ValueKind::Custom(Color32::DARK_GRAY);
                                }

                                SubFieldTranslationResult {
                                    name,
                                    result: TranslationResult {
                                        val: if fields.len() == 1 {
                                            ValueRepr::Tuple
                                        } else {
                                            ValueRepr::Struct
                                        },
                                        subfields,
                                        kind: handle_problematic!(),
                                    },
                                }
                            } else {
                                SubFieldTranslationResult {
                                    name,
                                    result: TranslationResult {
                                        val: ValueRepr::NotPresent,
                                        subfields: not_present_enum_fields(fields),
                                        kind: handle_problematic!(),
                                    },
                                }
                            };
                            Ok(result)
                        })
                        .collect::<Result<_>>()?;

                    TranslationResult {
                        val: ValueRepr::Enum {
                            idx: tag,
                            name: options[tag].0 .1.tail().0.clone(),
                        },
                        kind,
                        subfields,
                    }
                }
            }
        }
        ConcreteType::Error
        | ConcreteType::Single {
            base: PrimitiveType::Bool | PrimitiveType::Clock,
            params: _,
        } => TranslationResult {
            val: ValueRepr::Bit(val.chars().next().unwrap()),
            kind: ValueKind::Normal,
            subfields: vec![],
        },
        ConcreteType::Single { base: _, params: _ }
        | ConcreteType::Integer(_)
        | ConcreteType::Bool(_) => TranslationResult {
            val: ValueRepr::Bits(
                mir_ty.size().to_u64().context("Size did not fit in u64")?,
                val.to_string(),
            ),
            kind: ValueKind::Normal,
            subfields: vec![],
        },
        ConcreteType::String(_) => TranslationResult {
            val: ValueRepr::String(format!("{val:?}")),
            kind: ValueKind::Normal,
            subfields: vec![],
        },
        ConcreteType::Backward(_) => TranslationResult {
            val: ValueRepr::String("*backward*".to_string()),
            kind: ValueKind::Custom(Color32::from_gray(128)),
            subfields: vec![],
        },
        ConcreteType::Wire(inner) => translate_concrete(val, inner, problematic)?,
    };
    Ok(result)
}

fn info_from_concrete(ty: &ConcreteType) -> Result<VariableInfo> {
    let result = match ty {
        ConcreteType::Tuple(inner) => VariableInfo::Compound {
            subfields: inner
                .iter()
                .enumerate()
                .map(|(i, inner)| Ok((format!("{i}"), info_from_concrete(inner)?)))
                .collect::<Result<_>>()?,
        },
        ConcreteType::Struct {
            name: _,
            members,
            is_port: _,
            field_translators
        } => VariableInfo::Compound {
            subfields: members
                .iter()
                .map(|(f, inner)| {
                    let inner = info_from_concrete(&inner)?;
                    let inner = if let Some(translator) = field_translators.get(f) {
                        match inner {
                            VariableInfo::Bits => {
                                VariableInfo::SuggestedSubtranslator(translator.clone())
                            },
                            VariableInfo::Compound { ..} |
                            VariableInfo::Bool |
                            VariableInfo::Clock |
                            VariableInfo::String |
                            VariableInfo::Real |
                            VariableInfo::SuggestedSubtranslator(_) => {
                                info!("Got a #[surfer_translator] attribute on a {f}, but it is not a primitive type, ignoring");
                                inner
                            }
                        }
                    } else {
                        inner
                    };

                    Ok((f.0.clone(), inner))
                })
                .collect::<Result<_>>()?,
        },
        ConcreteType::Array { inner, size } => VariableInfo::Compound {
            subfields: (0..size.to_u64().context("Array size did not fit in u64")?)
                .map(|i| Ok((format!("{i}"), info_from_concrete(inner)?)))
                .collect::<Result<_>>()?,
        },
        ConcreteType::Enum { options } => VariableInfo::Compound {
            subfields: options
                .iter()
                .map(|(name, fields)| {
                    Ok((
                        name.1.tail().0.clone(),
                        VariableInfo::Compound {
                            subfields: fields
                                .iter()
                                .map(|(f_name, f_ty)| {
                                    Ok((f_name.0.clone(), info_from_concrete(f_ty)?))
                                })
                                .collect::<Result<_>>()?,
                        },
                    ))
                })
                .collect::<Result<_>>()?,
        },
        ConcreteType::Single {
            base: PrimitiveType::Bool,
            params: _,
        } => VariableInfo::Bool,
        ConcreteType::Single {
            base: PrimitiveType::Clock,
            params: _,
        } => VariableInfo::Clock,
        ConcreteType::Single { .. } => VariableInfo::Bits,
        ConcreteType::Integer(_) | ConcreteType::Bool(_) => VariableInfo::Bits,
        ConcreteType::String(_) => VariableInfo::String,
        ConcreteType::Backward(inner) => info_from_concrete(inner)?,
        ConcreteType::Wire(inner) => info_from_concrete(inner)?,
        ConcreteType::Error => VariableInfo::Bool,
    };
    Ok(result)
}

fn descriptive_loc(expr: &Loc<Expression>) -> Option<Loc<()>> {
    match &expr.inner.kind {
        spade_hir::ExprKind::Error => None,
        spade_hir::ExprKind::Identifier(_) => None,
        spade_hir::ExprKind::IntLiteral(_, _) => None,
        spade_hir::ExprKind::BoolLiteral(_) => None,
        spade_hir::ExprKind::BitLiteral(_) => None,
        spade_hir::ExprKind::TypeLevelInteger(_) => None,
        spade_hir::ExprKind::CreatePorts => None,
        spade_hir::ExprKind::FieldAccess(_, field) => Some(field.loc()),
        spade_hir::ExprKind::MethodCall {
            name, call_kind, ..
        } => Some(match &call_kind {
            CallKind::Function => name.loc(),
            CallKind::Entity(kw) => ().between_locs(kw, name),
            CallKind::Pipeline { inst_loc, .. } => ().between_locs(inst_loc, name),
        }),
        spade_hir::ExprKind::Call { kind, callee, .. } => Some(match &kind {
            CallKind::Function => callee.loc(),
            CallKind::Entity(kw) => ().between_locs(kw, callee),
            CallKind::Pipeline { inst_loc, .. } => ().between_locs(inst_loc, callee),
        }),
        spade_hir::ExprKind::BinaryOperator(_, op, _) => Some(op.loc()),
        spade_hir::ExprKind::TupleLiteral(_)
        | spade_hir::ExprKind::LambdaDef { .. }
        | spade_hir::ExprKind::ArrayLiteral(_)
        | spade_hir::ExprKind::ArrayShorthandLiteral(_, _)
        | spade_hir::ExprKind::Index(_, _)
        | spade_hir::ExprKind::RangeIndex { .. }
        | spade_hir::ExprKind::TupleIndex(_, _)
        | spade_hir::ExprKind::UnaryOperator(_, _)
        | spade_hir::ExprKind::Match(_, _)
        | spade_hir::ExprKind::Block(_)
        | spade_hir::ExprKind::If(_, _, _)
        | spade_hir::ExprKind::TypeLevelIf(_, _, _)
        | spade_hir::ExprKind::PipelineRef { .. }
        | spade_hir::ExprKind::StageValid
        | spade_hir::ExprKind::StageReady
        | spade_hir::ExprKind::StaticUnreachable(_)
        | spade_hir::ExprKind::Null => Some(expr.loc()),
    }
}

// NOTE: We need codespan to be a non dev-dependency to make it optional. However,
// that makes it be reported as unused if it is only used in a `#[cfg(test)]`, so we'll
// use it here.
#[allow(unused)]
use spade_codespan::Span;

#[cfg(test)]
mod test {

    use super::*;

    #[test]
    fn resolve_loc_works_single_line() {
        let code = [("file".to_string(), "0123\n45678\n0123\n".to_string())];

        let loc = Loc::new((), Span::new(6, 8), 0);

        let resolved = loc.resolve(&code).unwrap();

        assert_eq!(resolved.line_number(), 2);
        assert_eq!(resolved.lines, "45678");
        assert_eq!(resolved.relevant_span, (1..3));
    }

    #[test]
    fn resolve_loc_works_multi_single_line() {
        let code = [("file".to_string(), "0123\n45678\n45678\n0123\n".to_string())];

        let loc = Loc::new((), Span::new(9, 13), 0);

        let resolved = loc.resolve(&code).unwrap();

        assert_eq!(resolved.line_number(), 2);
        assert_eq!(resolved.lines, "45678\n45678");
        assert_eq!(resolved.relevant_span, (4..8));
    }

    #[test]
    fn resolve_loc_works_span_at_end_of_line() {
        let code = [("file".to_string(), "0123\n".to_string())];

        let loc = Loc::new((), Span::new(0, 4), 0);

        let resolved = loc.resolve(&code).unwrap();

        assert_eq!(resolved.line_number(), 1);
        assert_eq!(resolved.lines, "0123");
        assert_eq!(resolved.relevant_span, (0..4));
    }

    #[test]
    fn resolve_loc_works_span_at_end_of_file() {
        let code = [("file".to_string(), "0123".to_string())];

        let loc = Loc::new((), Span::new(0, 4), 0);

        let resolved = loc.resolve(&code).unwrap();

        assert_eq!(resolved.line_number(), 1);
        assert_eq!(resolved.lines, "0123");
        assert_eq!(resolved.relevant_span, (0..4));
    }

    #[test]
    fn resolve_loc_to_true_name_works() {
        let rloc = ResolvedLoc {
            line_index: 3,
            lines: "abc123def",
            relevant_span: 3..6,
        };

        assert_eq!(
            rloc.to_true_name(),
            TrueName::SourceCode {
                line_number: 4,
                before: "abc".to_string(),
                this: "123".to_string(),
                after: "def".to_string()
            }
        );
    }

    #[test]
    fn resolve_loc_to_true_name_works_on_multi_line() {
        let rloc = ResolvedLoc {
            line_index: 3,
            lines: "abc12\n3def",
            relevant_span: 3..6,
        };

        assert_eq!(
            rloc.to_true_name(),
            TrueName::SourceCode {
                line_number: 4,
                before: "abc".to_string(),
                this: "12".to_string(),
                after: "".to_string()
            }
        );
    }

    #[test]
    fn resolve_loc_to_true_name_trims_whitespace() {
        let rloc = ResolvedLoc {
            line_index: 3,
            lines: " a b c 123 d e f    ",
            relevant_span: 7..10,
        };

        assert_eq!(
            rloc.to_true_name(),
            TrueName::SourceCode {
                line_number: 4,
                before: "a b c ".to_string(),
                this: "123".to_string(),
                after: " d e f".to_string()
            }
        );
    }

    #[test]
    fn true_name_works_span_at_end_of_line() {
        let code = [("file".to_string(), "0123\n".to_string())];

        let loc = Loc::new((), Span::new(0, 4), 0);

        let rloc = loc.resolve(&code).unwrap();

        assert_eq!(
            rloc.to_true_name(),
            TrueName::SourceCode {
                line_number: 1,
                before: "".to_string(),
                this: "0123".to_string(),
                after: "".to_string()
            }
        );
    }
}
