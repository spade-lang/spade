use std::collections::HashMap;
use std::rc::Rc;
use std::sync::RwLock;

use codespan_reporting::term::termcolor::Buffer;
use color_eyre::eyre::{anyhow, Context};
use color_eyre::Result;
use itertools::Itertools;
use logos::Logos;
use num::{BigUint, ToPrimitive, Zero};
#[cfg(feature = "python")]
use pyo3::prelude::*;

use ::spade::compiler_state::{type_of_hierarchical_value, CompilerState, MirContext};
use spade_ast_lowering::id_tracker::{ExprIdTracker, ImplIdTracker};
use spade_ast_lowering::SelfContext;
use spade_common::location_info::{Loc, WithLocation};
use spade_common::name::{Identifier, NameID, Path as SpadePath};
use spade_diagnostics::emitter::CodespanEmitter;
use spade_diagnostics::{CodeBundle, CompilationError, DiagHandler, Diagnostic};
use spade_hir::symbol_table::{LookupError, SymbolTable};
use spade_hir::{symbol_table::FrozenSymtab, ItemList};
use spade_hir::{Parameter, TypeSpec, UnitHead};
use spade_hir_lowering::monomorphisation::MonoState;
use spade_hir_lowering::pipelines::MaybePipelineContext;
use spade_hir_lowering::substitution::Substitutions;
use spade_hir_lowering::{expr_to_mir, MirLowerable};
use spade_mir::codegen::mangle_input;
use spade_mir::eval::{eval_statements, Value};
use spade_mir::unit_name::InstanceMap;
use spade_parser::lexer;
use spade_parser::Parser;
use spade_typeinference::equation::{TypeVar, TypedExpression};
use spade_typeinference::{GenericListSource, HasType, TypeState};
use spade_types::ConcreteType;
use vcd_translate::translation::{self, inner_translate_value};

trait Reportable {
    type Inner;
    fn report_and_convert(
        self,
        error_buffer: &mut Buffer,
        code: &CodeBundle,
        diag_handler: &mut DiagHandler,
    ) -> Result<Self::Inner>;
}

impl<T, E> Reportable for Result<T, E>
where
    E: CompilationError,
{
    type Inner = T;
    fn report_and_convert(
        self,
        error_buffer: &mut Buffer,
        code: &CodeBundle,
        diag_handler: &mut DiagHandler,
    ) -> Result<Self::Inner> {
        match self {
            Ok(val) => Ok(val),
            Err(e) => {
                e.report(error_buffer, code, diag_handler);
                if !error_buffer.is_empty() {
                    println!("{}", String::from_utf8_lossy(error_buffer.as_slice()));
                }
                Err(anyhow!("Failed to compile spade"))
            }
        }
    }
}

#[cfg_attr(feature = "python", pyclass)]
#[derive(Clone, Debug)]
pub struct BitString(pub String);

#[cfg_attr(feature = "python", pymethods)]
impl BitString {
    #[cfg(feature = "python")]
    #[new]
    pub fn new(bits: String) -> Self {
        Self(bits)
    }
    #[cfg(not(feature = "python"))]
    pub fn new(bits: String) -> Self {
        Self(bits)
    }

    fn inner(&self) -> &String {
        &self.0
    }
}

#[cfg_attr(feature = "python", pyclass)]
#[derive(Clone)]
pub struct SpadeType(pub ConcreteType);

/// State which we need to modify later. Stored in an Option so we can
/// take ownership of temporarily
pub struct OwnedState {
    symtab: FrozenSymtab,
    idtracker: ExprIdTracker,
    impl_idtracker: ImplIdTracker,
}

#[cfg_attr(feature = "python", pyclass)]
pub struct ComparisonResult {
    #[cfg(feature = "python")]
    #[pyo3(get)]
    pub expected_spade: String,
    #[cfg(feature = "python")]
    #[pyo3(get)]
    pub expected_bits: BitString,
    #[cfg(feature = "python")]
    #[pyo3(get)]
    pub got_spade: String,
    #[cfg(feature = "python")]
    #[pyo3(get)]
    pub got_bits: BitString,

    #[cfg(not(feature = "python"))]
    pub expected_spade: String,
    #[cfg(not(feature = "python"))]
    pub expected_bits: BitString,
    #[cfg(not(feature = "python"))]
    pub got_spade: String,
    #[cfg(not(feature = "python"))]
    pub got_bits: BitString,
}

#[cfg_attr(feature = "python", pymethods)]
impl ComparisonResult {
    /// Returns `true` if the values are the same Spade value. If the expected value has
    /// undefined bits, those are ignored
    pub fn matches(&self) -> bool {
        self.expected_bits
            .0
            .chars()
            .zip(self.got_bits.0.chars())
            .all(|(e, g)| e == 'X' || e == g)
    }
}

#[cfg_attr(feature = "python", pyclass)]
#[derive(Clone)]
pub struct FieldRef {
    #[cfg(feature = "python")]
    #[pyo3(get)]
    pub range: (u64, u64),
    #[cfg(not(feature = "python"))]
    pub range: (u64, u64),
    pub ty: TypeVar,
}

#[cfg_attr(feature = "python", pyclass(subclass))]
pub struct Spade {
    // state: CompilerState,
    code: CodeBundle,
    error_buffer: Buffer,
    diag_handler: DiagHandler,
    owned: Option<OwnedState>,
    item_list: ItemList,
    uut: Loc<SpadePath>,
    /// Type state used for new code written into the context of this struct.
    type_state: TypeState,
    uut_head: UnitHead,
    uut_nameid: NameID,
    instance_map: InstanceMap,
    mir_context: HashMap<NameID, MirContext>,

    compilation_cache: HashMap<(TypeVar, String), Value>,
    output_field_cache: HashMap<Vec<String>, Option<FieldRef>>,
}

impl Spade {
    pub fn new_impl(uut_name: String, state_path: String) -> color_eyre::Result<Self> {
        let state_str = std::fs::read_to_string(&state_path)
            .with_context(|| format!("Failed to read state file at {state_path}"))?;

        // FIXME: IF we start running into stackoverflows we should use serde_stacker
        let ron = ron::Options::default().without_recursion_limit();
        let state = ron
            .from_str::<CompilerState>(&state_str)
            .map_err(|e| anyhow!("Failed to deserialize compiler state {e}"))?;

        let code = Rc::new(RwLock::new(CodeBundle::from_files(&state.code)));
        let mut error_buffer = Buffer::ansi();
        let mut diag_handler = DiagHandler::new(Box::new(CodespanEmitter));

        let file_id = code
            .write()
            .unwrap()
            .add_file("dut".to_string(), uut_name.clone());
        let mut parser = Parser::new(lexer::TokenKind::lexer(&uut_name), file_id);
        let uut = parser.path().report_and_convert(
            &mut error_buffer,
            &code.read().unwrap(),
            &mut diag_handler,
        )?;

        let (uut_nameid, uut_head) = Self::lookup_function_like(&uut, state.symtab.symtab())
            .map_err(Diagnostic::from)
            .report_and_convert(&mut error_buffer, &code.read().unwrap(), &mut diag_handler)?;

        if !uut_head.type_params.is_empty() {
            return Err(anyhow!(
                "Testing units with generics is currently unsupported"
            ))?;
        }

        // Set the namespace of the module
        let namespace = uut.prelude();
        let mut symtab = state.symtab.unfreeze();
        for name in namespace.0 {
            symtab.push_namespace(name)
        }
        let symtab = symtab.freeze();

        let code = code.read().unwrap().clone();
        Ok(Self {
            uut,
            code,
            error_buffer,
            diag_handler,
            item_list: state.item_list,
            type_state: TypeState::new(),
            owned: Some(OwnedState {
                symtab,
                idtracker: state.idtracker,
                impl_idtracker: state.impl_idtracker,
            }),
            uut_head,
            uut_nameid,
            instance_map: state.instance_map,
            mir_context: state.mir_context,
            compilation_cache: HashMap::new(),
            output_field_cache: HashMap::new(),
        })
    }
}

#[cfg_attr(feature = "python", pymethods)]
impl Spade {
    #[cfg(feature = "python")]
    #[new]
    pub fn new(uut_name: String, state_path: String) -> color_eyre::Result<Self> {
        Self::new_impl(uut_name, state_path)
    }
    #[cfg(not(feature = "python"))]
    pub fn new(uut_name: String, state_path: String) -> color_eyre::Result<Self> {
        Self::new_impl(uut_name, state_path)
    }

    pub fn port_value(&mut self, port: &str, expr: &str) -> Result<(String, BitString)> {
        self.port_value_raw(port, expr)
            .map(|(name, v)| (name, BitString(v.as_string())))
    }

    #[tracing::instrument(level = "trace", skip(self, field))]
    pub fn compare_field(
        &mut self,
        // The field to compare
        field: FieldRef,
        // The spade expression to compare against
        spade_expr: &str,
        // The bits of the whole output struct
        output_bits: &BitString,
    ) -> Result<ComparisonResult> {
        let spade_bits = BitString(self.compile_expr(spade_expr, &field.ty)?.as_string());

        let concrete = TypeState::ungenerify_type(
            &field.ty,
            self.owned.as_ref().unwrap().symtab.symtab(),
            &self.item_list.types,
        )
        .unwrap();

        let relevant_bits = &BitString(
            output_bits.inner()[field.range.0 as usize..field.range.1 as usize].to_owned(),
        );

        Ok(ComparisonResult {
            expected_spade: spade_expr.to_string(),
            expected_bits: spade_bits,
            got_spade: val_to_spade(relevant_bits.inner(), concrete),
            got_bits: relevant_bits.clone(),
        })
    }

    pub fn field_value(
        &mut self,
        // The field to get the value of
        field: FieldRef,
        // The bits of the whole output struct
        output_bits: &BitString,
    ) -> Result<String> {
        let concrete = TypeState::ungenerify_type(
            &field.ty,
            self.owned.as_ref().unwrap().symtab.symtab(),
            &self.item_list.types,
        )
        .unwrap();

        let relevant_bits = &BitString(
            output_bits.inner()[field.range.0 as usize..field.range.1 as usize].to_owned(),
        );

        Ok(val_to_spade(relevant_bits.inner(), concrete))
    }

    #[tracing::instrument(level = "trace", skip(self))]
    pub fn output_as_field_ref(&mut self) -> Result<Option<FieldRef>> {
        let output_type = match self.output_type()? {
            Some(t) => t,
            None => return Ok(None),
        };
        let generic_list =
            self.type_state
                .create_generic_list(GenericListSource::Anonymous, &[], None)?;

        let ty = self
            .type_state
            .type_var_from_hir(output_type.loc(), &output_type, &generic_list);

        let concrete = TypeState::ungenerify_type(
            &ty,
            self.owned.as_ref().unwrap().symtab.symtab(),
            &self.item_list.types,
        )
        .unwrap();

        let size = concrete.to_mir_type().size();

        Ok(Some(FieldRef {
            range: (
                0,
                size.to_u64()
                    .ok_or(anyhow!("Field index exceeds {} bits", usize::MAX))?,
            ),
            ty,
        }))
    }

    /// Access a field of the DUT output or its subfields
    #[tracing::instrument(level = "trace", skip(self))]
    pub fn output_field(&mut self, path: Vec<String>) -> Result<Option<FieldRef>> {
        if let Some(cached) = self.output_field_cache.get(&path) {
            return Ok(cached.clone());
        }

        if path.is_empty() {
            return self.output_as_field_ref();
        }

        let output_type = match self.output_type()? {
            Some(t) => t,
            None => return Ok(None),
        };

        // Create a new variable which is guaranteed to have the output type
        let mut owned = self.take_owned();
        let mut symtab = owned.symtab.unfreeze();

        symtab.new_scope();
        let o_name = symtab.add_local_variable(Identifier("o".to_string()).nowhere());

        let generic_list =
            self.type_state
                .create_generic_list(GenericListSource::Anonymous, &[], None)?;
        let ty = self
            .type_state
            .type_var_from_hir(output_type.loc(), &output_type, &generic_list);

        // NOTE: safe unwrap, o_name is something we just created, so it can be any type
        let g = self.type_state.new_generic();
        self.type_state
            .add_equation(TypedExpression::Name(o_name.clone()), g);
        self.type_state
            .unify(
                &o_name,
                &ty,
                &spade_typeinference::Context {
                    symtab: &symtab,
                    items: &self.item_list,
                },
            )
            .unwrap();

        // Now that we have a type which we can work with, we can create a virtual expression
        // which accesses the field in order to learn the type of the field
        let expr = format!("o.{}", path.iter().join("."));
        let file_id = self.code.add_file("py".to_string(), expr.clone());
        let mut parser = Parser::new(lexer::TokenKind::lexer(&expr), file_id);

        // Parse the expression
        let ast = parser.expression().report_and_convert(
            &mut self.error_buffer,
            &self.code,
            &mut self.diag_handler,
        )?;

        let mut ast_ctx = spade_ast_lowering::Context {
            symtab: &mut symtab,
            idtracker: &mut owned.idtracker,
            impl_idtracker: &mut owned.impl_idtracker,
            pipeline_ctx: None,
            self_ctx: &mut SelfContext::FreeStanding,
        };
        let hir = spade_ast_lowering::visit_expression(&ast, &mut ast_ctx)
            .report_and_convert(&mut self.error_buffer, &self.code, &mut self.diag_handler)?
            .at_loc(&ast);

        let type_ctx = spade_typeinference::Context {
            symtab: &ast_ctx.symtab,
            items: &self.item_list,
        };
        let generic_list =
            self.type_state
                .create_generic_list(GenericListSource::Anonymous, &[], None)?;
        // NOTE: We need to actually have the type information about what we're assigning to here
        // available
        self.type_state
            .visit_expression(&hir, &type_ctx, &generic_list)
            .report_and_convert(&mut self.error_buffer, &self.code, &mut self.diag_handler)?;

        let g = self.type_state.new_generic();
        self.type_state
            .unify_expression_generic_error(
                &hir,
                &g,
                &spade_typeinference::Context {
                    symtab: &ast_ctx.symtab,
                    items: &self.item_list,
                },
            )
            .report_and_convert(&mut self.error_buffer, &self.code, &mut self.diag_handler)?;

        ast_ctx.symtab.close_scope();

        let result_type = hir.get_type(&self.type_state).unwrap();

        // Finally, we need to figure out the range of the field in in the
        // type. Since all previous steps passed, this can assume that
        // the types are good so we can do lots of unwrapping
        let mut concrete = &self
            .type_state
            .name_type(&o_name.nowhere(), &ast_ctx.symtab, &self.item_list.types)
            .unwrap();
        let (mut start, mut end) = (BigUint::zero(), concrete.to_mir_type().size());

        for field in &path {
            let mut current_offset = BigUint::zero();
            for (f, ty) in concrete.assume_struct().1 {
                let self_size = ty.to_mir_type().size();
                if f.0 == *field {
                    concrete = ty;
                    start = &start + current_offset;
                    end = &start + self_size;
                    break;
                }
                current_offset += self_size;
            }
        }

        self.return_owned(OwnedState {
            symtab: symtab.freeze(),
            idtracker: owned.idtracker,
            impl_idtracker: owned.impl_idtracker,
        });

        let result = Some(FieldRef {
            range: (
                start
                    .to_u64()
                    .ok_or(anyhow!("Field index exceeds {} bits", usize::MAX))?,
                end.to_u64()
                    .ok_or(anyhow!("Field index exceeds {} bits", usize::MAX))?,
            ),
            ty: result_type,
        });

        self.output_field_cache.insert(path, result.clone());
        Ok(result)
    }

    // Translate a value from a verilog instance path into a string value
    pub fn translate_value(&self, path: &str, value: &str) -> Result<String> {
        let hierarchy = path.split('.').map(str::to_string).collect::<Vec<_>>();
        if hierarchy.is_empty() {
            return Err(anyhow!("{path} is not a hierarchy path"));
        };

        let concrete = type_of_hierarchical_value(
            &self.uut_nameid,
            &hierarchy,
            &self.instance_map,
            &self.mir_context,
            self.owned
                .as_ref()
                .map(|state| state.symtab.symtab())
                .unwrap(),
            &self.item_list,
        )?;

        Ok(val_to_spade(value, concrete))
    }
}

impl Spade {
    /// Computes expr as a value for port. If the type of expr does not match the expected an error
    /// is returned. Likewise if uut does not have such a port.
    ///
    /// The returned value is the name of the port in the verilog, and the value
    #[tracing::instrument(level = "trace", skip(self))]
    pub fn port_value_raw(
        &mut self,
        port: &str,
        expr: &str,
    ) -> Result<(String, spade_mir::eval::Value)> {
        let (port_name, port_ty) = self.get_port(port.into())?;

        let mut type_state = TypeState::new();
        let generic_list =
            type_state.create_generic_list(GenericListSource::Anonymous, &[], None)?;
        let ty = type_state.type_var_from_hir(port_ty.loc(), &port_ty, &generic_list);

        let val = self.compile_expr(expr, &ty)?;
        Ok((port_name, val))
    }

    #[tracing::instrument(level = "trace", skip(symtab, name))]
    fn lookup_function_like(
        name: &Loc<SpadePath>,
        symtab: &SymbolTable,
    ) -> Result<(NameID, UnitHead), LookupError> {
        symtab
            .lookup_unit(name)
            .map(|(name, head)| (name, head.inner))
    }

    /// Tries to get the type and the name of the port in the generated verilog of the specified
    /// input port
    #[tracing::instrument(level = "trace", skip(self))]
    fn get_port(&mut self, port: String) -> Result<(String, Loc<TypeSpec>)> {
        let owned = self.owned.as_ref().unwrap();
        let symtab = owned.symtab.symtab();
        let head = Self::lookup_function_like(&self.uut, symtab)
            .map_err(Diagnostic::from)
            .report_and_convert(&mut self.error_buffer, &self.code, &mut self.diag_handler)?;

        for Parameter {
            name,
            ty,
            no_mangle,
        } in &head.1.inputs.0
        {
            if port == name.0 {
                let verilog_name = if no_mangle.is_some() {
                    mangle_input(no_mangle, &port)
                } else {
                    port
                };
                return Ok((verilog_name, ty.clone()));
            }
        }

        Err(anyhow!("{port} is not a port of {}", self.uut))
    }

    /// Evaluates the provided expression as the specified type and returns the result
    /// as a string of 01xz
    #[tracing::instrument(level = "trace", skip(self, ty))]
    pub fn compile_expr(
        &mut self,
        expr: &str,
        ty: &impl HasType,
    ) -> Result<spade_mir::eval::Value> {
        let cache_key = (ty.get_type(&self.type_state)?, expr.to_string());
        if let Some(cached) = self.compilation_cache.get(&cache_key) {
            return Ok(cached.clone());
        }

        let file_id = self.code.add_file("py".to_string(), expr.into());
        let mut parser = Parser::new(lexer::TokenKind::lexer(expr), file_id);

        // Parse the expression
        let ast = parser.expression().report_and_convert(
            &mut self.error_buffer,
            &self.code,
            &mut self.diag_handler,
        )?;

        let OwnedState {
            symtab,
            mut idtracker,
            mut impl_idtracker,
        } = self
            .owned
            .take()
            .expect("attempting to re-take owned state");

        let mut symtab = symtab.unfreeze();

        let mut ast_ctx = spade_ast_lowering::Context {
            symtab: &mut symtab,
            idtracker: &mut idtracker,
            impl_idtracker: &mut impl_idtracker,
            pipeline_ctx: None,
            self_ctx: &mut SelfContext::FreeStanding,
        };
        let hir = spade_ast_lowering::visit_expression(&ast, &mut ast_ctx)
            .report_and_convert(&mut self.error_buffer, &self.code, &mut self.diag_handler)?
            .at_loc(&ast);

        let mut symtab = symtab.freeze();

        let type_ctx = spade_typeinference::Context {
            symtab: symtab.symtab(),
            items: &self.item_list,
        };
        let generic_list = self
            .type_state
            .create_generic_list(GenericListSource::Anonymous, &[], None)
            .unwrap();

        self.type_state
            .visit_expression(&hir, &type_ctx, &generic_list)
            .report_and_convert(&mut self.error_buffer, &self.code, &mut self.diag_handler)?;

        self.type_state
            .unify_expression_generic_error(
                &hir,
                ty,
                &spade_typeinference::Context {
                    symtab: symtab.symtab(),
                    items: &self.item_list,
                },
            )
            .report_and_convert(&mut self.error_buffer, &self.code, &mut self.diag_handler)?;
        self.type_state
            .check_requirements(&spade_typeinference::Context {
                items: &self.item_list,
                symtab: symtab.symtab(),
            })
            .report_and_convert(&mut self.error_buffer, &self.code, &mut self.diag_handler)?;

        let mut hir_ctx = spade_hir_lowering::Context {
            symtab: &mut symtab,
            idtracker: &mut idtracker,
            types: &mut self.type_state,
            item_list: &self.item_list,
            unit_generic_list: &None,
            // NOTE: This requires changes if we end up wanting to write tests
            // for generic units
            mono_state: &mut MonoState::new(),
            subs: &mut Substitutions::new(),
            diag_handler: &mut self.diag_handler,
            pipeline_context: &mut MaybePipelineContext::NotPipeline,
            self_mono_item: None,
        };

        let mir = expr_to_mir(hir, &mut hir_ctx).report_and_convert(
            &mut self.error_buffer,
            &self.code,
            &mut self.diag_handler,
        )?;

        self.return_owned(OwnedState {
            symtab,
            idtracker,
            impl_idtracker,
        });

        let result = eval_statements(&mir.to_vec_no_source_map());
        self.compilation_cache.insert(cache_key, result.clone());
        Ok(result)
    }

    /// Return the output type of uut
    #[tracing::instrument(level = "trace", skip(self))]
    fn output_type(&mut self) -> Result<Option<Loc<TypeSpec>>> {
        Ok(self.uut_head.output_type.clone())
    }

    #[tracing::instrument(level = "trace", skip(self))]
    fn take_owned(&mut self) -> OwnedState {
        self.owned.take().expect("Failed to take owned state")
    }

    #[tracing::instrument(level = "trace", skip(self, o))]
    fn return_owned(&mut self, o: OwnedState) {
        self.owned = Some(o)
    }
}

fn val_to_spade(val: &str, ty: ConcreteType) -> String {
    let val_vcd = translation::value_from_str(val);
    let mut result = String::new();
    inner_translate_value(&mut result, &val_vcd, &ty);
    result
}
