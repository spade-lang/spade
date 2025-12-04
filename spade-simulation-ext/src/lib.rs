pub mod error;
pub mod field_ref;
pub mod range;

use std::rc::Rc;
use std::sync::RwLock;

use color_eyre::eyre::{anyhow, Context};
use field_ref::{FieldRef, FieldSource};
use logos::Logos;
use num::{BigUint, ToPrimitive, Zero};
#[cfg(feature = "python")]
use pyo3::prelude::*;
use rustc_hash::FxHashMap as HashMap;
use spade_codespan_reporting::term::termcolor::Buffer;

use ::spade::compiler_state::CompilerState;
use range::UptoRange;
use spade_ast_lowering::id_tracker::{ExprIdTracker, ImplIdTracker};
use spade_ast_lowering::SelfContext;
use spade_common::location_info::{Loc, WithLocation};
use spade_common::name::{Identifier, Path as SpadePath};
use spade_diagnostics::diag_list::DiagList;
use spade_diagnostics::emitter::CodespanEmitter;
use spade_diagnostics::{CodeBundle, CompilationError, DiagHandler, Diagnostic};
use spade_hir::expression::Safety;
use spade_hir::symbol_table::{LookupError, SymbolTable};
use spade_hir::{symbol_table::FrozenSymtab, ItemList};
use spade_hir::{Parameter, TypeSpec, UnitHead};
use spade_hir_lowering::monomorphisation::MonoState;
use spade_hir_lowering::pipelines::MaybePipelineContext;
use spade_hir_lowering::substitution::Substitutions;
use spade_hir_lowering::{expr_to_mir, MirLowerable};
use spade_mir::codegen::{mangle_input, mangle_output};
use spade_mir::eval::{eval_statements, Value};
use spade_parser::lexer;
use spade_parser::Parser;
use spade_typeinference::equation::{KnownTypeVar, TypedExpression};
use spade_typeinference::error::UnificationErrorExt;
use spade_typeinference::traits::TraitImplList;
use spade_typeinference::{GenericListSource, HasType, TypeState};
use spade_types::ConcreteType;
use vcd_translate::translation::{self, inner_translate_value};

use crate::error::{Error, Result};

trait Reportable {
    type Inner;
    fn report_and_convert(
        self,
        error_buffer: &mut Buffer,
        code: &CodeBundle,
        diag_handler: &mut DiagHandler,
    ) -> Result<Self::Inner>;
}

impl<T, E> Reportable for std::result::Result<T, E>
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
                Err(error::Error::CompilationError {
                    msg: "Failed to compile Spade code".to_string(),
                })
            }
        }
    }
}

/// #[pyo3(get)] does not work unless the struct is #[pyclass]. Since we can build this crate both
/// with and without python support, we therefore need to #[cfg] away the #[pyo3(get)] fields.
/// THis macro removes that boilerplate
#[macro_export]
macro_rules! maybe_pyclass {
    ($( #[$sattr:meta] )* $svis:vis struct $sname:ident {
        $( $(#[$mattr:meta])* $mvis:vis $mname:ident : $mty:ty),*$(,)?
    }) => {
        $(#[$sattr])*
        $svis struct $sname {
            $(
                #[cfg(feature = "python")]
                $(#[$mattr])*
                $mvis $mname: $mty,
                #[cfg(not(feature = "python"))]
                $mvis $mname: $mty
            ),*
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
    item_list: ItemList,
    trait_impls: TraitImplList,
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

#[cfg_attr(feature = "python", pyclass(subclass))]
pub struct Spade {
    // state: CompilerState,
    code: CodeBundle,
    error_buffer: Buffer,
    diag_handler: DiagHandler,
    owned: Option<OwnedState>,
    uut: Loc<SpadePath>,
    /// Type state used for new code written into the context of this struct.
    type_state: TypeState,
    uut_head: UnitHead,
    compilation_cache: HashMap<(KnownTypeVar, String), Value>,
    field_cache: HashMap<Vec<String>, FieldRef>,
}

impl Spade {
    pub fn new_impl(uut_name: String, state_path: String) -> color_eyre::Result<Self> {
        let state_bytes = std::fs::read(&state_path)
            .with_context(|| format!("Failed to read state file at {state_path}"))?;

        let (state, _) = bincode::serde::borrow_decode_from_slice::<CompilerState, _>(
            &state_bytes,
            bincode::config::standard(),
        )
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
        let uut_name = state
            .symtab
            .symtab()
            .lookup_final_id(&uut, &[])
            .map_err(|_| anyhow!("Did not find a NameID for {uut}"))?;

        let uut_head = Self::lookup_function_like(&uut, state.symtab.symtab())
            .map_err(Diagnostic::from)
            .report_and_convert(&mut error_buffer, &code.read().unwrap(), &mut diag_handler)?;

        if !uut_head.get_type_params().is_empty() {
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

        let mir_context = state
            .mir_context
            .get(&uut_name)
            .ok_or_else(|| anyhow!("Did not find a mir context for unit"))?;

        let code = code.read().unwrap().clone();
        Ok(Self {
            uut,
            code,
            error_buffer,
            diag_handler,
            type_state: mir_context.type_state.create_child(),
            owned: Some(OwnedState {
                symtab,
                item_list: state.item_list,
                trait_impls: TraitImplList::new(),
                idtracker: state.idtracker,
                impl_idtracker: state.impl_idtracker,
            }),
            uut_head,
            compilation_cache: HashMap::default(),
            field_cache: HashMap::default(),
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

    pub fn arg_value(&mut self, arg: &str, expr: &str) -> Result<(String, BitString)> {
        self.port_value_raw(arg, expr)
            .map(|(name, v)| (name, BitString(v.as_string())))
    }

    /// Compares the value of the specified field against spade_expr
    /// Requires the field to be a pure backward type, otherwise an error message is returned
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
        let (relevant_bits, ty, concrete) = self.extract_field_read_bits(field, output_bits)?;

        //  FIXME(Performance): We can improve performance here by not compiling
        // the human readable value unless needed

        let spade_bits = BitString(self.compile_expr(spade_expr, &ty)?.as_string());

        Ok(ComparisonResult {
            expected_spade: spade_expr.to_string(),
            expected_bits: spade_bits,
            got_spade: val_to_spade(relevant_bits.inner(), concrete),
            got_bits: relevant_bits.clone(),
        })
    }

    /// Computes a human readable representation of the specified field's value
    /// Requires the field to be a pure backward type, otherwise an error message is returned
    pub fn field_value(
        &mut self,
        // The field to get the value of
        field: FieldRef,
        // The bits of the whole output struct
        output_bits: &BitString,
    ) -> Result<String> {
        let (relevant_bits, _ty, concrete) = self.extract_field_read_bits(field, output_bits)?;

        Ok(val_to_spade(relevant_bits.inner(), concrete))
    }

    /// Compiles a a spade snippet into a value that matches the field
    pub fn compile_field_value(&mut self, field: &FieldRef, value: &str) -> Result<BitString> {
        // We don't actually use the result here, but we want to pigyback off
        // the error message
        let (_, actual_ty) = field.write_range_and_type()?;
        self.compile_expr(&value, &actual_ty)
            .map(|v| BitString(v.as_string()))
    }

    #[tracing::instrument(level = "trace", skip(self))]
    pub fn output_as_field_ref(&mut self) -> Result<Option<FieldRef>> {
        if let Some(cached) = self.field_cache.get(&vec!["o".to_string()]) {
            return Ok(Some(cached.clone()));
        }
        let output_type = match self.output_type()? {
            Some(t) => t,
            None => return Ok(None),
        };
        let generic_list = self
            .type_state
            .create_generic_list(GenericListSource::Anonymous, &[], &[], None, &[])
            .report_and_convert(&mut self.error_buffer, &self.code, &mut self.diag_handler)?;

        let ty = self
            .type_state
            .type_var_from_hir(output_type.loc(), &output_type, &generic_list)
            .report_and_convert(&mut self.error_buffer, &self.code, &mut self.diag_handler)?;

        let owned_state = self.owned.as_ref().unwrap();
        let concrete = self
            .type_state
            .ungenerify_type(
                &ty,
                owned_state.symtab.symtab(),
                &owned_state.item_list.types,
            )
            .unwrap();

        let fwd_size = concrete.to_mir_type().size();
        let back_size = concrete.to_mir_type().backward_size();

        let result = FieldRef {
            fwd_range: if fwd_size != BigUint::zero() {
                Some(UptoRange {
                    from: 0,
                    to: fwd_size
                        .to_u64()
                        .ok_or(anyhow!("Field index exceeds {} bits", usize::MAX))?,
                    is_full: true,
                })
            } else {
                None
            },
            back_range: if back_size != BigUint::zero() {
                Some(UptoRange {
                    from: 0,
                    to: back_size
                        .to_u64()
                        .ok_or(anyhow!("Field index exceeds {} bits", usize::MAX))?,
                    is_full: true,
                })
            } else {
                None
            },
            ty: ty
                .resolve(&self.type_state)
                .into_known(&self.type_state)
                .ok_or_else(|| anyhow!("Found an incomplete type"))?,
            path: vec!["o".to_string()],
            source: FieldSource::Output {},
        };
        self.field_cache
            .insert(vec!["o".to_string()], result.clone());
        Ok(Some(result))
    }

    pub fn field_of_field(&mut self, field: &mut FieldRef, next: &str) -> Result<FieldRef> {
        let mut full_path = field.path.clone();
        full_path.push(next.to_string());
        if let Some(cached) = self.field_cache.get(&full_path) {
            return Ok(cached.clone());
        }

        // Create a new variable which is guaranteed to have the output type
        let owned_state = self.take_owned();
        let mut symtab = owned_state.symtab.unfreeze();

        symtab.new_scope();
        let o_name = symtab.add_local_variable(Identifier("o".to_string()).nowhere());

        let ty = &field.ty;
        let ty_id = ty.insert(&mut self.type_state);

        let concrete =
            self.type_state
                .ungenerify_type(&ty_id, &symtab, &owned_state.item_list.types);
        let has_field = concrete
            .map(|c| concrete_ty_has_field(&c, next))
            .unwrap_or_default();

        if !has_field {
            return Err(Error::NoSuchField {
                ty: format!("{ty}"),
                field: next.to_string(),
                path: full_path.clone(),
            });
        }
        // Even though we made sure the field exists, we don't know the non-concrete type of
        // the field which we need later. So we'll need to invent an expression and infer the
        // appropriate type

        // NOTE: safe unwrap, o_name is something we just created, so it can be any type
        let g = self.type_state.new_generic_any();
        self.type_state
            .add_equation(TypedExpression::Name(o_name.clone()), g);
        self.type_state
            .unify(
                &o_name,
                &ty_id,
                &spade_typeinference::Context {
                    symtab: &symtab,
                    items: &owned_state.item_list,
                    trait_impls: &owned_state.trait_impls,
                },
            )
            .into_default_diagnostic(().nowhere(), &self.type_state)
            .report_and_convert(&mut self.error_buffer, &self.code, &mut self.diag_handler)?;

        // Now that we have a type which we can work with, we can create a virtual expression
        // which accesses the field in order to learn the type of the field
        let expr = format!("o.{}", next);
        let file_id = self.code.add_file("py".to_string(), expr.clone());
        let mut parser = Parser::new(lexer::TokenKind::lexer(&expr), file_id);

        // Parse the expression
        let ast = parser.expression().report_and_convert(
            &mut self.error_buffer,
            &self.code,
            &mut self.diag_handler,
        )?;

        let mut ast_ctx = spade_ast_lowering::Context {
            symtab,
            item_list: owned_state.item_list,
            idtracker: owned_state.idtracker,
            impl_idtracker: owned_state.impl_idtracker,
            pipeline_ctx: None,
            self_ctx: SelfContext::FreeStanding,
            current_unit: None,
            diags: DiagList::new(),
            safety: Safety::Default,
        };
        let hir = spade_ast_lowering::visit_expression(&ast, &mut ast_ctx).at_loc(&ast);

        self.handle_diags(&mut ast_ctx.diags)?;

        let type_ctx = spade_typeinference::Context {
            symtab: &ast_ctx.symtab,
            items: &ast_ctx.item_list,
            trait_impls: &owned_state.trait_impls,
        };

        let generic_list = self
            .type_state
            .create_generic_list(GenericListSource::Anonymous, &[], &[], None, &[])
            .report_and_convert(&mut self.error_buffer, &self.code, &mut self.diag_handler)?;
        // NOTE: We need to actually have the type information about what we're
        // assigning to available here
        self.type_state
            .visit_expression(&hir, &type_ctx, &generic_list);

        let mut diags = self.type_state.diags.drain_to_new();
        self.handle_diags(&mut diags)?;

        let g = self.type_state.new_generic_any();
        self.type_state
            .unify_expression_generic_error(
                &hir,
                &g,
                &spade_typeinference::Context {
                    symtab: &ast_ctx.symtab,
                    items: &ast_ctx.item_list,
                    trait_impls: &owned_state.trait_impls,
                },
            )
            .report_and_convert(&mut self.error_buffer, &self.code, &mut self.diag_handler)?;

        ast_ctx.symtab.close_scope();

        let result_type = hir.get_type(&self.type_state);

        // Finally, we need to figure out the range of the field in in the
        // type. Since all previous steps passed, this can assume that
        // the types are good so we can do lots of unwrapping
        let struct_ty = &self
            .type_state
            .concrete_type_of_name(&o_name.nowhere(), &ast_ctx.symtab, &ast_ctx.item_list.types)
            .unwrap();

        let get_range = |outer_range: Option<UptoRange>,
                         size_fn: &dyn Fn(&ConcreteType) -> BigUint|
         -> Result<Option<UptoRange>> {
            if let Some(outer_range) = outer_range {
                let mut start_in_outer = BigUint::zero();
                let mut self_size = BigUint::zero();

                for (f, ty) in struct_ty.assume_struct().1.iter() {
                    if f.0 == *next {
                        self_size = size_fn(ty);
                        break;
                    }
                    start_in_outer += size_fn(ty)
                }

                let outer_start = outer_range.from + &start_in_outer;
                let start = (outer_start.clone())
                    .to_u64()
                    .ok_or(anyhow!("Field index exceeds {} bits", usize::MAX))?;
                let end = (outer_start + &self_size)
                    .to_u64()
                    .ok_or(anyhow!("Field index exceeds {} bits", usize::MAX))?;

                let is_full =
                    outer_range.is_full && outer_range.from == start && outer_range.to == end;

                if self_size != BigUint::zero() {
                    Ok(Some(UptoRange {
                        from: start,
                        to: end,
                        is_full,
                    }))
                } else {
                    Ok(None)
                }
            } else {
                Ok(None)
            }
        };

        let spade_ast_lowering::Context {
            symtab,
            item_list,
            idtracker,
            impl_idtracker,
            pipeline_ctx: _,
            self_ctx: _,
            current_unit: _,
            mut diags,
            safety: _,
        } = ast_ctx;

        self.handle_diags(&mut diags)?;

        self.return_owned(OwnedState {
            symtab: symtab.freeze(),
            item_list,
            trait_impls: self.type_state.trait_impls.clone(),
            idtracker,
            impl_idtracker,
        });

        let mut path = field.path.clone();
        path.push(next.to_string());

        let result = FieldRef {
            fwd_range: get_range(field.fwd_range, &|ty| ty.to_mir_type().size())?,
            back_range: get_range(field.back_range, &|ty| ty.to_mir_type().backward_size())?,
            ty: result_type
                .resolve(&self.type_state)
                .into_known(&self.type_state)
                .ok_or_else(|| anyhow!("Found incomplete type"))?,
            source: field.source.clone(),
            path,
        };

        self.field_cache.insert(full_path, result.clone());

        Ok(result)
    }

    /// Access a field of the DUT output or its subfields
    #[tracing::instrument(level = "trace", skip(self))]
    pub fn output_field(&mut self, path: Vec<String>) -> Result<Option<FieldRef>> {
        println!("output_field from {}", path.join("."));
        self.output_as_field_ref()?
            .map(|mut out| {
                for field in path {
                    out = self.field_of_field(&mut out, &field)?
                }

                Ok(out)
            })
            .transpose()
    }

    pub fn arg_as_field(&mut self, arg_name: &str) -> Result<FieldRef> {
        let path = vec!["i".to_string(), arg_name.to_string()];
        if let Some(cached) = self.field_cache.get(&path) {
            return Ok(cached.clone());
        }
        let (source, ty) = self.get_arg(arg_name)?;
        let ty_id = ty.insert(&mut self.type_state);

        let owned_state = self.take_owned();

        let concrete = self
            .type_state
            .ungenerify_type(
                &ty_id,
                owned_state.symtab.symtab(),
                &owned_state.item_list.types,
            )
            .unwrap();

        let fwd_size = concrete.to_mir_type().size();
        let back_size = concrete.to_mir_type().backward_size();

        let result = FieldRef {
            fwd_range: if fwd_size != BigUint::zero() {
                Some(UptoRange {
                    from: 0,
                    to: fwd_size
                        .to_u64()
                        .ok_or(anyhow!("Field index exceeds {} bits", usize::MAX))?,
                    is_full: true,
                })
            } else {
                None
            },
            back_range: if back_size != BigUint::zero() {
                Some(UptoRange {
                    from: 0,
                    to: back_size
                        .to_u64()
                        .ok_or(anyhow!("Field index exceeds {} bits", usize::MAX))?,
                    is_full: true,
                })
            } else {
                None
            },
            path: path.clone(),
            ty,
            source,
        };

        self.field_cache.insert(path, result.clone());

        self.return_owned(owned_state);

        Ok(result)
    }
}

impl Spade {
    /// Given a field, and `output_bits` as a binary value representing the whole field
    /// source, returns the type of the field as well as a bit string that make up the
    /// specified field
    pub fn extract_field_read_bits(
        &mut self,
        field: FieldRef,
        output_bits: &BitString,
    ) -> Result<(BitString, KnownTypeVar, ConcreteType)> {
        let (range, ty) = field.read_range_and_type()?;

        let owned_state = self.owned.as_ref().unwrap();

        let ty_id = ty.insert(&mut self.type_state);
        let concrete = self
            .type_state
            .ungenerify_type(
                &ty_id,
                owned_state.symtab.symtab(),
                &owned_state.item_list.types,
            )
            .unwrap();

        let relevant_bits =
            BitString(output_bits.inner()[range.from as usize..range.to as usize].to_owned());

        Ok((relevant_bits, ty, concrete))
    }

    /// Computes expr as a value for port. If the type of expr does not match the expected an error
    /// is returned. Likewise if uut does not have such a port.
    ///
    /// The returned value is the name of the port in the verilog, and the value
    #[tracing::instrument(level = "trace", skip(self))]
    pub fn port_value_raw(
        &mut self,
        arg: &str,
        expr: &str,
    ) -> Result<(String, spade_mir::eval::Value)> {
        let (source, ty) = self.get_arg(arg)?;

        let val = self.compile_expr(expr, &ty)?;
        Ok((source.fwd_mangled().to_string(), val))
    }

    #[tracing::instrument(level = "trace", skip(symtab, name))]
    fn lookup_function_like(
        name: &Loc<SpadePath>,
        symtab: &SymbolTable,
    ) -> std::result::Result<UnitHead, LookupError> {
        symtab.lookup_unit(name).map(|(_, head)| head.inner)
    }

    /// Tries to get the type and the name of the port in the generated verilog of the specified
    /// input port
    #[tracing::instrument(level = "trace", skip(self))]
    fn get_arg(&mut self, arg: &str) -> Result<(FieldSource, KnownTypeVar)> {
        let owned_state = self.owned.as_ref().unwrap();
        let symtab = owned_state.symtab.symtab();
        let head = Self::lookup_function_like(&self.uut, symtab)
            .map_err(Diagnostic::from)
            .report_and_convert(&mut self.error_buffer, &self.code, &mut self.diag_handler)?;

        for Parameter {
            name,
            ty,
            no_mangle,
            field_translator: _,
        } in &head.inputs.0
        {
            if arg == name.0 {
                let source = FieldSource::Input {
                    mangled_fwd: mangle_input(no_mangle, &arg),
                    mangled_back: mangle_output(no_mangle, &arg),
                };

                let generic_list = self
                    .type_state
                    .create_generic_list(GenericListSource::Anonymous, &[], &[], None, &[])
                    .report_and_convert(
                        &mut self.error_buffer,
                        &self.code,
                        &mut self.diag_handler,
                    )?;
                let ty = self
                    .type_state
                    .type_var_from_hir(ty.loc(), &ty, &generic_list)
                    .report_and_convert(&mut self.error_buffer, &self.code, &mut self.diag_handler)?
                    .resolve(&self.type_state)
                    .into_known(&self.type_state)
                    .ok_or_else(|| anyhow!("Expression had generic type"))?;

                return Ok((source, ty.clone()));
            }
        }

        Err(crate::error::Error::NoSuchInput {
            top: format!("{}", self.uut),
            name: arg.to_string(),
        })
    }

    /// Evaluates the provided expression as the specified type and returns the result
    /// as a string of 01xz
    #[tracing::instrument(level = "trace", skip(self, ty))]
    pub fn compile_expr(
        &mut self,
        expr: &str,
        ty: &KnownTypeVar,
    ) -> Result<spade_mir::eval::Value> {
        let cache_key = (ty.clone(), expr.to_string());
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
            item_list,
            trait_impls,
            idtracker,
            impl_idtracker,
        } = self
            .owned
            .take()
            .expect("attempting to re-take owned state");

        let symtab = symtab.unfreeze();

        let mut ast_ctx = spade_ast_lowering::Context {
            symtab,
            item_list,
            idtracker,
            impl_idtracker,
            pipeline_ctx: None,
            self_ctx: SelfContext::FreeStanding,
            current_unit: None,
            diags: DiagList::new(),
            safety: Safety::Default,
        };

        let hir = spade_ast_lowering::visit_expression(&ast, &mut ast_ctx).at_loc(&ast);

        let spade_ast_lowering::Context {
            symtab,
            item_list,
            mut idtracker,
            impl_idtracker,
            pipeline_ctx: _,
            self_ctx: _,
            current_unit: _,
            mut diags,
            safety: _,
        } = ast_ctx;
        self.handle_diags(&mut diags)?;

        let mut symtab = symtab.freeze();

        let type_ctx = spade_typeinference::Context {
            symtab: symtab.symtab(),
            items: &item_list,
            trait_impls: &trait_impls,
        };
        let generic_list = self
            .type_state
            .create_generic_list(GenericListSource::Anonymous, &[], &[], None, &[])
            .report_and_convert(&mut self.error_buffer, &self.code, &mut self.diag_handler)?;

        self.type_state
            .visit_expression(&hir, &type_ctx, &generic_list);

        let mut diags = self.type_state.diags.drain_to_new();
        self.handle_diags(&mut diags)?;

        let ty_id = ty.insert(&mut self.type_state);
        self.type_state
            .unify_expression_generic_error(
                &hir,
                &ty_id,
                &spade_typeinference::Context {
                    symtab: symtab.symtab(),
                    items: &item_list,
                    trait_impls: &trait_impls,
                },
            )
            .report_and_convert(&mut self.error_buffer, &self.code, &mut self.diag_handler)?;
        self.type_state
            .check_requirements(
                true,
                &spade_typeinference::Context {
                    items: &item_list,
                    symtab: symtab.symtab(),
                    trait_impls: &trait_impls,
                },
            )
            .report_and_convert(&mut self.error_buffer, &self.code, &mut self.diag_handler)?;

        let mut hir_ctx = spade_hir_lowering::Context {
            symtab: &mut symtab,
            idtracker: &mut idtracker,
            types: &mut self.type_state,
            item_list: &item_list,
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
            item_list,
            trait_impls,
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

    fn handle_diags(&mut self, diags: &mut DiagList) -> Result<()> {
        for diag in diags.drain() {
            Err(diag).report_and_convert(
                &mut self.error_buffer,
                &self.code,
                &mut self.diag_handler,
            )?
        }
        Ok(())
    }
}

fn val_to_spade(val: &str, ty: ConcreteType) -> String {
    let val_vcd = translation::value_from_str(val);
    let mut result = String::new();
    inner_translate_value(&mut result, &val_vcd, &ty);
    result
}

fn concrete_ty_has_field(ty: &ConcreteType, field: &str) -> bool {
    match ty {
        ConcreteType::Struct {
            name: _,
            is_port: _,
            members,
            field_translators: _,
        } => members.iter().find(|(n, _)| n.0 == field).is_some(),
        ConcreteType::Backward(inner) | ConcreteType::Wire(inner) => {
            concrete_ty_has_field(inner, field)
        }
        _ => false,
    }
}
