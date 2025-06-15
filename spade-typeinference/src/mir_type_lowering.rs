use std::collections::HashMap;

use hir::symbol_table::SymbolTable;
use hir::{Parameter, TypeExpression, TypeSpec};
use spade_common::id_tracker::ExprID;
use spade_common::location_info::{Loc, WithLocation};
use spade_common::name::NameID;
use spade_diagnostics::Diagnostic;
use spade_hir::{self as hir, ConstGenericWithId};
use spade_hir::{TypeDeclaration, TypeList};
use spade_types::{ConcreteType, KnownType};

use crate::equation::{TypeVar, TypeVarID, TypedExpression};
use crate::TypeState;

pub trait HasConcreteType {
    fn into_typed_expression(&self) -> Loc<TypedExpression>;
}

impl<T> HasConcreteType for &mut T
where
    T: HasConcreteType,
{
    fn into_typed_expression(&self) -> Loc<TypedExpression> {
        (**self).into_typed_expression()
    }
}

impl<T> HasConcreteType for &T
where
    T: HasConcreteType,
{
    fn into_typed_expression(&self) -> Loc<TypedExpression> {
        (*self).into_typed_expression()
    }
}

impl<T> HasConcreteType for Box<T>
where
    T: HasConcreteType,
{
    fn into_typed_expression(&self) -> Loc<TypedExpression> {
        self.as_ref().into_typed_expression()
    }
}

impl HasConcreteType for Loc<ExprID> {
    fn into_typed_expression(&self) -> Loc<TypedExpression> {
        TypedExpression::Id(self.inner).at_loc(self)
    }
}

impl HasConcreteType for Loc<hir::Expression> {
    fn into_typed_expression(&self) -> Loc<TypedExpression> {
        TypedExpression::Id(self.id).at_loc(self)
    }
}

impl HasConcreteType for Loc<hir::Pattern> {
    fn into_typed_expression(&self) -> Loc<TypedExpression> {
        TypedExpression::Id(self.id).at_loc(self)
    }
}
impl HasConcreteType for Loc<ConstGenericWithId> {
    fn into_typed_expression(&self) -> Loc<TypedExpression> {
        TypedExpression::Id(self.id).at_loc(self)
    }
}

impl HasConcreteType for Loc<NameID> {
    fn into_typed_expression(&self) -> Loc<TypedExpression> {
        TypedExpression::Name(self.inner.clone()).at_loc(self)
    }
}

impl TypeState {
    pub fn type_decl_to_concrete(
        decl: &TypeDeclaration,
        type_list: &TypeList,
        params: Vec<ConcreteType>,
        invert: bool,
    ) -> ConcreteType {
        // Mapping between generic name and type param

        assert!(
            params.len() == decl.generic_args.len(),
            "Too few type decl params in {:?}",
            decl
        );

        let generic_subs = decl
            .generic_args
            .iter()
            .zip(params.iter())
            .map(|(lhs, rhs)| (lhs.name_id(), rhs))
            .collect::<HashMap<_, _>>();

        match &decl.kind {
            hir::TypeDeclKind::Enum(e) => {
                let options = e
                    .options
                    .iter()
                    .map(|(name, args)| {
                        let args = args
                            .0
                            .iter()
                            .map(|arg| {
                                (
                                    arg.name.inner.clone(),
                                    Self::type_spec_to_concrete(
                                        &arg.ty.inner,
                                        type_list,
                                        &generic_subs,
                                        false,
                                    ),
                                )
                            })
                            .collect();
                        (name.inner.clone(), args)
                    })
                    .collect();
                ConcreteType::Enum { options }
            }
            hir::TypeDeclKind::Struct(s) => {
                let members = s
                    .members
                    .0
                    .iter()
                    .map(
                        |Parameter {
                             name: ident,
                             ty: t,
                             no_mangle: _,
                             field_translator: _,
                         }| {
                            (
                                ident.inner.clone(),
                                Self::type_spec_to_concrete(t, type_list, &generic_subs, invert),
                            )
                        },
                    )
                    .collect();

                let translators = s.members.0.iter().filter_map(
                    |Parameter {
                         name,
                         field_translator,
                         ..
                     }| {
                        field_translator
                            .as_ref()
                            .map(|t| (name.inner.clone(), t.clone()))
                    },
                );

                ConcreteType::Struct {
                    name: decl.name.inner.clone(),
                    is_port: s.is_port,
                    members,
                    field_translators: translators.collect(),
                }
            }
            hir::TypeDeclKind::Primitive(primitive) => ConcreteType::Single {
                base: primitive.clone(),
                params,
            },
        }
    }

    pub fn type_expr_to_concrete(
        expr: &TypeExpression,
        type_list: &TypeList,
        generic_substitutions: &HashMap<NameID, &ConcreteType>,
        invert: bool,
    ) -> ConcreteType {
        match &expr {
            hir::TypeExpression::Integer(val) => ConcreteType::Integer(val.clone()),
            hir::TypeExpression::TypeSpec(inner) => {
                Self::type_spec_to_concrete(inner, type_list, generic_substitutions, invert)
            }
            hir::TypeExpression::ConstGeneric(_) => {
                unreachable!("Const generic in type_expr_to_concrete")
            }
        }
    }

    pub fn type_spec_to_concrete(
        spec: &TypeSpec,
        type_list: &TypeList,
        generic_substitutions: &HashMap<NameID, &ConcreteType>,
        invert: bool,
    ) -> ConcreteType {
        match spec {
            TypeSpec::Declared(name, params) => {
                let params = params
                    .iter()
                    .map(|p| {
                        Self::type_expr_to_concrete(p, type_list, generic_substitutions, invert)
                    })
                    .collect();

                let actual = type_list
                    .get(name)
                    .unwrap_or_else(|| panic!("Expected {:?} to be in type list", name));

                Self::type_decl_to_concrete(actual, type_list, params, invert)
            }
            TypeSpec::Generic(name) => {
                // Substitute the generic for the current substitution
                (*generic_substitutions
                    .get(name)
                    .unwrap_or_else(|| panic!("Expected a substitution for {}", name)))
                .clone()
            }
            TypeSpec::Tuple(t) => {
                let inner = t
                    .iter()
                    .map(|v| {
                        Self::type_spec_to_concrete(
                            &v.inner,
                            type_list,
                            generic_substitutions,
                            invert,
                        )
                    })
                    .collect::<Vec<_>>();
                ConcreteType::Tuple(inner)
            }
            TypeSpec::Array { inner, size } => {
                let size_type = Box::new(Self::type_expr_to_concrete(
                    size,
                    type_list,
                    generic_substitutions,
                    invert,
                ));

                let size = if let ConcreteType::Integer(size) = size_type.as_ref() {
                    size.clone()
                } else {
                    panic!("Array size must be an integer")
                };

                ConcreteType::Array {
                    inner: Box::new(Self::type_spec_to_concrete(
                        inner,
                        type_list,
                        generic_substitutions,
                        invert,
                    )),
                    size,
                }
            }
            TypeSpec::Wire(inner) => {
                let inner = Box::new(Self::type_spec_to_concrete(
                    inner,
                    type_list,
                    generic_substitutions,
                    invert,
                ));
                if invert {
                    ConcreteType::Backward(inner)
                } else {
                    ConcreteType::Wire(inner)
                }
            }
            TypeSpec::Inverted(inner) => Self::type_spec_to_concrete(
                inner,
                type_list,
                generic_substitutions,
                // Recursive inversions uninvert, so if we're already inverted while
                // reaching another inversion, go back to the normal direction
                !invert,
            ),
            TypeSpec::TraitSelf(_) => panic!("Trying to concretize HIR TraitSelf type"),
            TypeSpec::Wildcard(_) => panic!("Trying to concretize HIR Wildcard type"),
        }
    }

    pub fn inner_ungenerify_type(
        &self,
        var: &TypeVarID,
        symtab: &SymbolTable,
        type_list: &TypeList,
        invert: bool,
    ) -> Option<ConcreteType> {
        match var.resolve(self) {
            TypeVar::Known(_, KnownType::Error, _) => Some(ConcreteType::Error),
            TypeVar::Known(_, KnownType::Named(t), params) => {
                let params = params
                    .iter()
                    .map(|v| self.inner_ungenerify_type(v, symtab, type_list, invert))
                    .collect::<Option<Vec<_>>>()?;

                type_list
                    .get(t)
                    .map(|t| Self::type_decl_to_concrete(&t.inner, type_list, params, invert))
            }
            TypeVar::Known(_, KnownType::Integer(val), params) => {
                assert!(params.is_empty(), "integers cannot have type parameters");

                Some(ConcreteType::Integer(val.clone()))
            }
            TypeVar::Known(_, KnownType::Bool(val), params) => {
                assert!(
                    params.is_empty(),
                    "type level bools cannot have type parameters"
                );

                Some(ConcreteType::Bool(*val))
            }
            TypeVar::Known(_, KnownType::Array, inner) => {
                let value = self.inner_ungenerify_type(&inner[0], symtab, type_list, invert);
                let size = self.ungenerify_type(&inner[1], symtab, type_list).map(|t| {
                    if let ConcreteType::Integer(size) = t {
                        size
                    } else {
                        panic!("Array size must be an integer")
                    }
                });

                match (value, size) {
                    (Some(value), Some(size)) => Some(ConcreteType::Array {
                        inner: Box::new(value),
                        size,
                    }),
                    _ => None,
                }
            }
            TypeVar::Known(_, KnownType::Tuple, inner) => {
                let inner = inner
                    .iter()
                    .map(|v| self.inner_ungenerify_type(v, symtab, type_list, invert))
                    .collect::<Option<Vec<_>>>()?;
                Some(ConcreteType::Tuple(inner))
            }
            TypeVar::Known(_, KnownType::Wire, inner) => {
                if invert {
                    self.inner_ungenerify_type(&inner[0], symtab, type_list, invert)
                        .map(|t| ConcreteType::Backward(Box::new(t)))
                } else {
                    self.inner_ungenerify_type(&inner[0], symtab, type_list, invert)
                        .map(|t| ConcreteType::Wire(Box::new(t)))
                }
            }
            TypeVar::Known(_, KnownType::Inverted, inner) => {
                self.inner_ungenerify_type(&inner[0], symtab, type_list, !invert)
            }
            TypeVar::Unknown(_, _, _, _) => None,
        }
    }

    /// Converts the specified type to a concrete type, returning None
    /// if it fails
    pub fn ungenerify_type(
        &self,
        var: &TypeVarID,
        symtab: &SymbolTable,
        type_list: &TypeList,
    ) -> Option<ConcreteType> {
        self.inner_ungenerify_type(var, symtab, type_list, false)
    }

    /// Returns the type of the specified expression ID as a concrete type. If the type is not
    /// known, or the type is Generic, panics
    pub fn concrete_type_of_infallible(
        &self,
        id: ExprID,
        symtab: &SymbolTable,
        type_list: &TypeList,
    ) -> ConcreteType {
        self.concrete_type_of(id.nowhere(), symtab, type_list)
            .expect("Expr had generic type")
    }

    /// Returns the concrete type of anything that might have a concrete type. Errors
    /// if the type is not fully known.
    pub fn concrete_type_of(
        &self,
        id: impl HasConcreteType,
        symtab: &SymbolTable,
        types: &TypeList,
    ) -> Result<ConcreteType, Diagnostic> {
        let id = id.into_typed_expression();
        let t = self.type_of(&id.inner);

        if let Some(t) = self.ungenerify_type(&t, symtab, types) {
            Ok(t)
        } else {
            if std::env::var("SPADE_TRACE_TYPEINFERENCE").is_ok() {
                println!("The incomplete type is {}", t.debug_resolve(self))
            }
            Err(
                Diagnostic::error(id, "Type of expression is not fully known")
                    .primary_label("The type of this expression is not fully known")
                    .note(format!("Found incomplete type: {t}", t = t.display(self))),
            )
        }
    }

    /// Like `concrete_type_of` but reports an error message that mentions names
    /// instead of an expression
    pub fn concrete_type_of_name(
        &self,
        name: &Loc<NameID>,
        symtab: &SymbolTable,
        types: &TypeList,
    ) -> Result<ConcreteType, Diagnostic> {
        let t = self.type_of(&TypedExpression::Name(name.inner.clone()));

        if let Some(t) = self.ungenerify_type(&t, symtab, types) {
            Ok(t)
        } else {
            Err(
                Diagnostic::error(name, format!("Type of {name} is not fully known"))
                    .primary_label(format!("The type of {name} is not fully known"))
                    .note(format!("Found incomplete type: {t}", t = t.display(self))),
            )
        }
    }
}
