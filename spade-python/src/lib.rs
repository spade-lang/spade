mod translation;

use std::rc::Rc;
use std::sync::RwLock;

use codespan_reporting::term::termcolor::Buffer;
use color_eyre::eyre::{anyhow, Context};
use itertools::Itertools;
use logos::Logos;
use pyo3::prelude::*;

use spade::compiler_state::CompilerState;
use spade::lexer;
use spade_ast_lowering::id_tracker::{ExprIdTracker, ImplIdTracker};
use spade_common::location_info::{Loc, WithLocation};
use spade_common::name::{Identifier, Path as SpadePath};
use spade_diagnostics::emitter::CodespanEmitter;
use spade_diagnostics::{CodeBundle, CompilationError, DiagHandler};
use spade_hir::symbol_table::{LookupError, SymbolTable};
use spade_hir::TypeSpec;
use spade_hir::{symbol_table::FrozenSymtab, FunctionLike, ItemList};
use spade_hir_lowering::monomorphisation::MonoState;
use spade_hir_lowering::substitution::Substitutions;
use spade_hir_lowering::{expr_to_mir, MirLowerable};
use spade_mir::codegen::mangle_input;
use spade_mir::eval::eval_statements;
use spade_parser::Parser;
use spade_typeinference::equation::{TypeVar, TypedExpression};
use spade_typeinference::{GenericListSource, HasType, TypeState};
use spade_types::ConcreteType;
use translation::BitTranslator;
use vcd_translate::translation::inner_translate_value;

trait Reportable {
    type Inner;
    fn report_and_convert(
        self,
        error_buffer: &mut Buffer,
        code: &CodeBundle,
        diag_handler: &mut DiagHandler,
    ) -> PyResult<Self::Inner>;
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
    ) -> PyResult<Self::Inner> {
        match self {
            Ok(val) => Ok(val),
            Err(e) => {
                e.report(error_buffer, code, diag_handler);
                if !error_buffer.is_empty() {
                    println!("{}", String::from_utf8_lossy(error_buffer.as_slice()));
                }
                Err(anyhow!("Failed to compile spade").into())
            }
        }
    }
}

#[pyclass]
#[derive(PartialEq, Eq, Clone, Debug)]
struct BitString(pub String);

#[pymethods]
impl BitString {
    #[new]
    pub fn new(bits: String) -> Self {
        Self(bits)
    }

    fn inner(&self) -> &String {
        &self.0
    }
}

#[pyclass]
#[derive(Clone)]
struct SpadeType(pub ConcreteType);

/// State which we need to modify later. Stored in an Option so we can
/// take ownership of temporarily
struct OwnedState {
    symtab: FrozenSymtab,
    idtracker: ExprIdTracker,
    impl_idtracker: ImplIdTracker,
}

#[pyclass]
struct ComparisonResult {
    #[pyo3(get)]
    pub expected_spade: String,
    #[pyo3(get)]
    pub expected_bits: BitString,
    #[pyo3(get)]
    pub got_spade: String,
    #[pyo3(get)]
    pub got_bits: BitString,
}

#[pyclass]
#[derive(Clone)]
struct FieldRef {
    #[pyo3(get)]
    pub range: (u64, u64),
    pub ty: TypeVar,
}

#[pyclass(subclass)]
struct Spade {
    // state: CompilerState,
    code: CodeBundle,
    error_buffer: Buffer,
    diag_handler: DiagHandler,
    owned: Option<OwnedState>,
    item_list: ItemList,
    uut: Loc<SpadePath>,
    type_state: TypeState,
    uut_head: Box<dyn FunctionLike + Send>,
}

#[pymethods]
impl Spade {
    #[new]
    pub fn new(uut_name: String, state_path: String) -> PyResult<Self> {
        let state_str = std::fs::read_to_string(&state_path)
            .with_context(|| format!("Failed to read state file at {state_path}"))?;
        let state = ron::from_str::<CompilerState>(&state_str)
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

        let uut_head = Self::lookup_function_like(&uut, state.symtab.symtab()).report_and_convert(
            &mut error_buffer,
            &code.read().unwrap(),
            &mut diag_handler,
        )?;

        if !uut_head.type_params().is_empty() {
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
        })
    }

    /// Computes expr as a value for port. If the type of expr does not match the expected an error
    /// is returned. Likewise if uut does not have such a port.
    ///
    /// The returned value is the name of the port in the verilog, and the value
    #[tracing::instrument(level = "trace", skip(self))]
    fn port_value(&mut self, port: &str, expr: &str) -> PyResult<(String, BitString)> {
        let (port_name, port_ty) = self.get_port(port.into())?;

        let mut type_state = TypeState::new();
        let generic_list = type_state.create_generic_list(GenericListSource::Anonymous, &vec![]);
        let ty = type_state.type_var_from_hir(&port_ty, &generic_list);

        let val = self.compile_expr(expr, &ty)?;
        Ok((port_name, val))
    }

    #[tracing::instrument(level = "trace", skip(self, field))]
    fn compare_field(
        &mut self,
        // The field to compare
        field: FieldRef,
        // The spade expression to compare against
        spade_expr: &str,
        // The bits of the whole output struct
        output_bits: &BitString,
    ) -> PyResult<ComparisonResult> {
        let spade_bits = self.compile_expr(spade_expr, &field.ty)?;

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
            got_spade: val_to_spade(&relevant_bits.inner(), concrete),
            got_bits: relevant_bits.clone(),
        })
    }

    fn field_value(
        &mut self,
        // The field to get the value of
        field: FieldRef,
        // The bits of the whole output struct
        output_bits: &BitString,
    ) -> PyResult<String> {
        let concrete = TypeState::ungenerify_type(
            &field.ty,
            self.owned.as_ref().unwrap().symtab.symtab(),
            &self.item_list.types,
        )
        .unwrap();

        let relevant_bits = &BitString(
            output_bits.inner()[field.range.0 as usize..field.range.1 as usize].to_owned(),
        );

        Ok(val_to_spade(&relevant_bits.inner(), concrete))
    }

    #[tracing::instrument(level = "trace", skip(self))]
    fn output_as_field_ref(&mut self) -> PyResult<FieldRef> {
        let output_type = self.output_type()?;
        let generic_list = self
            .type_state
            .create_generic_list(GenericListSource::Anonymous, &vec![]);

        let ty = self
            .type_state
            .type_var_from_hir(&output_type, &generic_list);

        let concrete = TypeState::ungenerify_type(
            &ty,
            self.owned.as_ref().unwrap().symtab.symtab(),
            &self.item_list.types,
        )
        .unwrap();

        let size = concrete.to_mir_type().size();

        Ok(FieldRef {
            range: (0, size),
            ty,
        })
    }

    /// Access a field of the DUT output or its subfields
    #[tracing::instrument(level = "trace", skip(self))]
    fn output_field(&mut self, path: Vec<String>) -> PyResult<FieldRef> {
        let output_type = self.output_type()?;

        // Create a new variable which is guaranteed to have the output type
        let owned = self.take_owned();
        let mut symtab = owned.symtab.unfreeze();

        symtab.new_scope();
        let o_name = symtab.add_local_variable(Identifier("o".to_string()).nowhere());

        let generic_list = self
            .type_state
            .create_generic_list(GenericListSource::Anonymous, &vec![]);
        let ty = self
            .type_state
            .type_var_from_hir(&output_type, &generic_list);

        // NOTE: safe unwrap, o_name is something we just created, so it can be any type
        let g = self.type_state.new_generic();
        self.type_state
            .add_equation(TypedExpression::Name(o_name.clone()), g);
        self.type_state.unify(&o_name, &ty, &symtab).unwrap();

        // Now that we have a type which we can work with, we can create a virtual expression
        // which accesses the field in order to learn the type of the field
        let expr = format!("o.{}", path.iter().join(","));
        let file_id = self.code.add_file("py".to_string(), expr.clone().into());
        let mut parser = Parser::new(lexer::TokenKind::lexer(&expr), file_id);

        // Parse the expression
        let ast = parser.expression().report_and_convert(
            &mut self.error_buffer,
            &self.code,
            &mut self.diag_handler,
        )?;

        let idtracker = owned.idtracker;

        let mut ast_ctx = spade_ast_lowering::Context {
            symtab,
            idtracker,
            pipeline_ctx: None,
            impl_idtracker: owned.impl_idtracker,
        };
        let hir = spade_ast_lowering::visit_expression(&ast, &mut ast_ctx)
            .report_and_convert(&mut self.error_buffer, &self.code, &mut self.diag_handler)?
            .at_loc(&ast);

        let generic_list = self
            .type_state
            .create_generic_list(GenericListSource::Anonymous, &vec![]);
        // NOTE: We need to actually have the type information about what we're assigning to here
        // available
        let type_ctx = spade_typeinference::Context {
            symtab: &ast_ctx.symtab,
            items: &self.item_list,
        };
        self.type_state
            .visit_expression(&hir, &type_ctx, &generic_list)
            .report_and_convert(&mut self.error_buffer, &self.code, &mut self.diag_handler)?;

        let g = self.type_state.new_generic();
        self.type_state
            .unify_expression_generic_error(&hir, &g, &ast_ctx.symtab)
            .report_and_convert(&mut self.error_buffer, &self.code, &mut self.diag_handler)?;

        ast_ctx.symtab.close_scope();

        let result_type = hir.get_type(&self.type_state).unwrap();

        // Finally, we need to figure out the range of the field in in the
        // type. Since all previous steps passed, this can assume that
        // the types are good so we can do lots of unwraping
        let concrete = self
            .type_state
            .name_type(&o_name.nowhere(), &ast_ctx.symtab, &self.item_list.types)
            .unwrap();
        let (mut start, mut end) = (0, concrete.to_mir_type().size());

        for field in path {
            let mut current_offset = 0;
            for (f, ty) in concrete.assume_struct().1 {
                let self_size = ty.to_mir_type().size();
                if f.0 == field {
                    start = start + current_offset;
                    end = start + self_size;
                    break;
                }
                current_offset += self_size;
            }
        }

        self.return_owned(OwnedState {
            symtab: ast_ctx.symtab.freeze(),
            idtracker: ast_ctx.idtracker,
            impl_idtracker: ast_ctx.impl_idtracker,
        });

        Ok(FieldRef {
            range: (start, end),
            ty: result_type,
        })
    }
}

impl Spade {
    #[tracing::instrument(level = "trace", skip(symtab, name))]
    fn lookup_function_like(
        name: &Loc<SpadePath>,
        symtab: &SymbolTable,
    ) -> Result<Box<dyn FunctionLike + Send>, LookupError> {
        if let Ok(e) = symtab.lookup_entity(name) {
            Ok(Box::new(e.1.inner))
        } else if let Ok(f) = symtab.lookup_function(name) {
            Ok(Box::new(f.1.inner))
        } else {
            let p = symtab.lookup_pipeline(name)?;
            Ok(Box::new(p.1.inner))
        }
    }

    /// Tries to get the type and the name of the port in the generated verilog of the specified
    /// input port
    #[tracing::instrument(level = "trace", skip(self))]
    fn get_port(&mut self, port: String) -> PyResult<(String, TypeSpec)> {
        let owned = self.owned.as_ref().unwrap();
        let symtab = owned.symtab.symtab();
        let head = Self::lookup_function_like(&self.uut, &symtab).report_and_convert(
            &mut self.error_buffer,
            &self.code,
            &mut self.diag_handler,
        )?;

        for (name, ty) in &head.inputs().0 {
            if port == name.0 {
                return Ok((mangle_input(&port), ty.inner.clone()));
            }
        }

        Err(anyhow!("{port} is not a port of {}", self.uut).into())
    }

    /// Evaluates the provided expression as the specified type and returns the result
    /// as a string of 01xz
    #[tracing::instrument(level = "trace", skip(self, ty))]
    pub fn compile_expr(&mut self, expr: &str, ty: &impl HasType) -> PyResult<BitString> {
        let file_id = self.code.add_file("py".to_string(), expr.into());
        let mut parser = Parser::new(lexer::TokenKind::lexer(&expr), file_id);

        // Parse the expression
        let ast = parser.expression().report_and_convert(
            &mut self.error_buffer,
            &self.code,
            &mut self.diag_handler,
        )?;

        let OwnedState {
            symtab,
            idtracker,
            impl_idtracker,
        } = self
            .owned
            .take()
            .expect("attempting to re-take owned state");

        let symtab = symtab.unfreeze();

        let mut ast_ctx = spade_ast_lowering::Context {
            symtab,
            idtracker,
            pipeline_ctx: None,
            impl_idtracker,
        };
        let hir = spade_ast_lowering::visit_expression(&ast, &mut ast_ctx)
            .report_and_convert(&mut self.error_buffer, &self.code, &mut self.diag_handler)?
            .at_loc(&ast);

        let mut symtab = ast_ctx.symtab.freeze();

        let generic_list = self
            .type_state
            .create_generic_list(GenericListSource::Anonymous, &vec![]);

        let type_ctx = spade_typeinference::Context {
            symtab: &symtab.symtab(),
            items: &self.item_list,
        };
        self.type_state
            .visit_expression(&hir, &type_ctx, &generic_list)
            .report_and_convert(&mut self.error_buffer, &self.code, &mut self.diag_handler)?;

        self.type_state
            .unify_expression_generic_error(&hir, ty, &symtab.symtab())
            .report_and_convert(&mut self.error_buffer, &self.code, &mut self.diag_handler)?;

        let mut hir_ctx = spade_hir_lowering::Context {
            symtab: &mut symtab,
            idtracker: &mut ast_ctx.idtracker,
            types: &self.type_state,
            item_list: &self.item_list,
            // NOTE: This requires changes if we end up wanting to write tests
            // for generic units
            mono_state: &mut MonoState::new(),
            subs: &mut Substitutions::new(),
            diag_handler: &mut self.diag_handler,
        };

        let mir = expr_to_mir(hir, &mut hir_ctx).report_and_convert(
            &mut self.error_buffer,
            &self.code,
            &mut self.diag_handler,
        )?;

        self.return_owned(OwnedState {
            symtab,
            idtracker: ast_ctx.idtracker,
            impl_idtracker: ast_ctx.impl_idtracker,
        });

        Ok(BitString(
            eval_statements(&mir.to_vec_no_source_map()).as_string(),
        ))
    }

    /// Return the output type of uut
    #[tracing::instrument(level = "trace", skip(self))]
    fn output_type(&mut self) -> PyResult<TypeSpec> {
        let ty = self
            .uut_head
            .output_type()
            .clone()
            .ok_or_else(|| anyhow!("{} does not have an output type", self.uut))?;

        Ok(ty.inner)
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
    let val_vcd = vcd_translate::translation::value_from_str(&val);
    let mut result = String::new();
    inner_translate_value(&mut result, &val_vcd, &ty);
    result
}

/// A Python module implemented in Rust.
#[pymodule]
fn spade(_py: Python, m: &PyModule) -> PyResult<()> {
    m.add_class::<Spade>()?;
    m.add_class::<BitString>()?;
    m.add_class::<SpadeType>()?;
    m.add_class::<ComparisonResult>()?;
    m.add_class::<BitTranslator>()?;
    Ok(())
}
