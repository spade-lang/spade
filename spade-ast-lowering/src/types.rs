use hir::symbol_table::{SymbolTable, TypeDeclKind, TypeSymbol};
use local_impl::local_impl;
use spade_ast as ast;
use spade_common::{location_info::WithLocation, name::Path};
use spade_hir as hir;

use crate::{visit_type_param, Result};

pub fn lower_type_declaration(
    decl: &ast::TypeDeclaration,
    symtab: &mut SymbolTable,
) -> Result<hir::TypeDeclaration> {
    symtab.new_scope();
    symtab.push_namespace(decl.name.clone());
    // Add the generic types declared here to the symtab
    for param in &decl.generic_args {
        match &param.inner {
            ast::TypeParam::TypeName(name) => {
                symtab.add_type(
                    Path::ident(name.clone()),
                    TypeSymbol::GenericArg.at_loc(&param),
                );
            }
            ast::TypeParam::Integer(name) => {
                symtab.add_type(
                    Path::ident(name.clone()),
                    TypeSymbol::GenericInt.at_loc(&param),
                );
            }
        }
    }
    symtab.pop_namespace();

    let ast::TypeDeclaration {
        name,
        kind,
        generic_args,
    } = decl;

    let this_path = Path(vec![name.clone()]);

    let (id, _) = symtab.lookup_type_symbol(&this_path.clone().at_loc(&name))
        .expect("Found no entry for typedecl in symtab. Was it not visited during global symbol collection?");

    let generic_args = generic_args
        .iter()
        .map(|param| param.try_map_ref(|p| visit_type_param(p, symtab)))
        .collect::<Result<Vec<_>>>()?;

    let kind = match kind {
        ast::TypeDeclKind::Enum(e) => {
            hir::TypeDeclKind::Enum(e.try_map_ref::<_, crate::Error, _>(|e| {
                let ast::Enum { name: _, options } = e;

                let options = options
                    .iter()
                    .map(|(name, params)| {
                        let params = crate::visit_parameter_list(
                            params.as_ref().unwrap_or(&ast::ParameterList(vec![])),
                            symtab,
                        )?;

                        let option_path = this_path.clone().push_ident(name.clone());

                        let (id, _) = symtab
                            .lookup_function(&option_path.nowhere())
                            .expect("Expected enum variant to be in symtab as a function");

                        Ok((id.at_loc(name), params.clone()))
                    })
                    .collect::<Result<Vec<_>>>()?;

                Ok(hir::Enum { options })
            })?)
        }
        ast::TypeDeclKind::Struct(s) => {
            hir::TypeDeclKind::Struct(s.try_map_ref::<_, crate::Error, _>(|s| {
                let ast::Struct {
                    name: _,
                    members,
                    port_keyword: _,
                } = s;
                let members = crate::visit_parameter_list(members, symtab)?;
                Ok(hir::Struct {
                    members,
                    is_port: s.is_port(),
                })
            })?)
        }
    };

    symtab.close_scope();

    let declaration = hir::TypeDeclaration {
        name: id.at_loc(&name),
        kind,
        generic_args,
    };

    Ok(declaration)
}

#[local_impl]
impl IsPort for ast::TypeSpec {
    fn is_port(&self, symtab: &SymbolTable) -> Result<bool> {
        match self {
            ast::TypeSpec::Tuple(inner) => {
                for t in inner {
                    if t.is_port(symtab)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            ast::TypeSpec::Array { inner, size: _ } => inner.is_port(symtab),
            ast::TypeSpec::Named(name, _) => {
                let (_, symbol) = symtab.lookup_type_symbol(name)?;

                match &symbol.inner {
                    TypeSymbol::Declared(_, kind) => match kind {
                        TypeDeclKind::Struct { is_port } => Ok(*is_port),
                        TypeDeclKind::Enum => Ok(false),
                        TypeDeclKind::Primitive { is_port } => Ok(*is_port),
                    },
                    TypeSymbol::GenericArg => Ok(false),
                    TypeSymbol::GenericInt => Ok(false),
                }
            }
            ast::TypeSpec::Unit(_) => Ok(false),
            ast::TypeSpec::Backward(_) => Ok(true),
            ast::TypeSpec::Wire(_) => Ok(true),
        }
    }
}
