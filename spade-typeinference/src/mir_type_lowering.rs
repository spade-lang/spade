use rustc_hash::FxHashMap as HashMap;

use hir::symbol_table::SymbolTable;
use hir::{Parameter, TypeExpression, TypeSpec};
use spade_common::id_tracker::ExprID;
use spade_common::location_info::{Loc, WithLocation};
use spade_common::name::NameID;
use spade_diagnostics::Diagnostic;
use spade_hir::pretty_print::PrettyPrint;
use spade_hir::{self as hir, ConstGeneric, ConstGenericWithId, Generic};
use spade_hir::{TypeDeclaration, TypeList};
use spade_types::{ConcreteType, KnownType, PrimitiveType};

use crate::TypeState;
use crate::constraints::ConstraintExpr;
use crate::equation::{TypeVar, TypeVarID, TypedExpression};

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

impl HasConcreteType for Loc<&ExprID> {
    fn into_typed_expression(&self) -> Loc<TypedExpression> {
        TypedExpression::Id(*self.inner).at_loc(self)
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
    ) -> Result<ConcreteType, Diagnostic> {
        // Mapping between generic name and type param

        assert!(
            params.len() == decl.generic_args.len(),
            "Too few type decl params in {:?}\n\n    params: {:?}\n    decl: {:?}",
            decl,
            params,
            decl.generic_args
        );

        let generic_subs = decl
            .generic_args
            .iter()
            .zip(params.iter())
            .map(|(lhs, rhs)| (lhs.name.clone(), rhs))
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
                                Ok((
                                    arg.name.inner.clone(),
                                    Self::type_spec_to_concrete(
                                        &arg.ty.inner,
                                        type_list,
                                        &generic_subs,
                                    )?,
                                ))
                            })
                            .collect::<Result<Vec<_>, Diagnostic>>()?;
                        Ok((name.inner.clone(), args))
                    })
                    .collect::<Result<Vec<_>, Diagnostic>>()?;

                Ok(ConcreteType::Enum { options })
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
                             wire: _,
                             field_translator: _,
                         }| {
                            Ok((
                                ident.inner.clone(),
                                Self::type_spec_to_concrete(t, type_list, &generic_subs)?,
                            ))
                        },
                    )
                    .collect::<Result<Vec<_>, Diagnostic>>()?;

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

                Ok(ConcreteType::Struct {
                    name: decl.name.inner.clone(),
                    members,
                    field_translators: translators.collect(),
                })
            }
            hir::TypeDeclKind::Primitive(PrimitiveType::Clock) => Ok(ConcreteType::Single {
                base: PrimitiveType::Clock,
                params,
            }),
            hir::TypeDeclKind::Primitive(primitive) => {
                let leaf = ConcreteType::Single {
                    base: primitive.clone(),
                    params,
                };
                Ok(leaf)
            }
            hir::TypeDeclKind::Alias(a) => {
                Self::type_spec_to_concrete(&a.type_spec, type_list, &generic_subs)
            }
        }
    }

    pub fn type_expr_to_concrete(
        expr: &TypeExpression,
        type_list: &TypeList,
        generic_substitutions: &HashMap<Generic, &ConcreteType>,
    ) -> Result<ConcreteType, Diagnostic> {
        match &expr {
            hir::TypeExpression::Bool(val) => Ok(ConcreteType::Bool(*val)),
            hir::TypeExpression::Integer(val) => Ok(ConcreteType::Integer(val.clone())),
            hir::TypeExpression::String(val) => Ok(ConcreteType::String(val.clone())),
            hir::TypeExpression::TypeSpec(inner) => {
                Self::type_spec_to_concrete(inner, type_list, generic_substitutions)
            }
            hir::TypeExpression::ConstGeneric(cg) => {
                Self::const_generic_to_concrete(cg, generic_substitutions)
            }
        }
    }

    pub fn type_spec_to_concrete(
        spec: &TypeSpec,
        type_list: &TypeList,
        generic_substitutions: &HashMap<Generic, &ConcreteType>,
    ) -> Result<ConcreteType, Diagnostic> {
        match spec {
            TypeSpec::Declared(name, params) => {
                let params = params
                    .iter()
                    .map(|p| Self::type_expr_to_concrete(p, type_list, generic_substitutions))
                    .collect::<Result<Vec<_>, _>>()?;

                let actual = type_list.get(name);

                if let Some(actual) = actual {
                    Self::type_decl_to_concrete(actual, type_list, params)
                } else {
                    Err(Diagnostic::bug(
                        name,
                        format!("Expected {:?} to be in type list", name),
                    ))
                }
            }
            TypeSpec::Generic(name) => {
                // Substitute the generic for the current substitution
                if let Some(sub) = generic_substitutions.get(name) {
                    Ok((*sub).clone())
                } else {
                    let loc = match name {
                        Generic::Named(n) => n.loc(),
                        Generic::Hidden(g) => g.loc(),
                    };
                    Err(Diagnostic::bug(
                        ().at_loc(&loc),
                        format!("Expected a substitution for {}", name.pretty_print()),
                    ))
                }
            }
            TypeSpec::Tuple(t) => {
                let inner = t
                    .iter()
                    .map(|v| {
                        Self::type_spec_to_concrete(&v.inner, type_list, generic_substitutions)
                    })
                    .collect::<Result<Vec<_>, _>>()?;

                Ok(ConcreteType::Tuple(inner))
            }
            TypeSpec::Array { inner, size } => {
                let size_type = Box::new(Self::type_expr_to_concrete(
                    size,
                    type_list,
                    generic_substitutions,
                )?);

                let size = match size_type.as_ref() {
                    ConcreteType::Integer(size) => size.clone(),
                    _ => {
                        return Err(Diagnostic::bug(
                            ().at_loc(size),
                            "Array size must be an integer",
                        ));
                    }
                };

                Ok(ConcreteType::Array {
                    inner: Box::new(Self::type_spec_to_concrete(
                        inner,
                        type_list,
                        generic_substitutions,
                    )?),
                    size,
                })
            }

            TypeSpec::Inverted(inner) => Ok(ConcreteType::Backward(Box::new(
                Self::type_spec_to_concrete(inner, type_list, generic_substitutions)?,
            ))),

            TypeSpec::CopyView(inner) => Ok(ConcreteType::CopyView(Box::new(
                Self::type_spec_to_concrete(inner, type_list, generic_substitutions)?,
            ))),

            TypeSpec::TraitSelf(_) => panic!("Trying to concretize HIR TraitSelf type"),
            TypeSpec::Wildcard(_) => panic!("Trying to concretize HIR Wildcard type"),
        }
    }

    pub fn const_generic_to_concrete(
        cg: &Loc<ConstGeneric>,
        subs: &HashMap<Generic, &ConcreteType>,
    ) -> Result<ConcreteType, Diagnostic> {
        let expr = TypeState::const_generic_to_constraint_expr(&cg.inner, &|n| {
            // Unlike TypeState::visit_const_generic, instead of the generic list we use the
            // substitution map to resolve generic names
            match subs.get(&Generic::Named(n.clone())) {
                Some(ConcreteType::Integer(val)) => Ok(ConstraintExpr::Integer(val.clone())),
                Some(ConcreteType::Bool(val)) => Ok(ConstraintExpr::Bool(*val)),
                Some(ConcreteType::String(val)) => Ok(ConstraintExpr::String(val.clone())),
                Some(_) => Err(Diagnostic::bug(
                    cg,
                    format!("Non-literal substitution for const generic {n}"),
                )),
                None => Err(Diagnostic::bug(
                    cg,
                    format!("No substitution for const generic {n}"),
                )),
            }
        })?;

        let loc = ().at_loc(cg);
        match expr.evaluate(&|_| None, &loc)? {
            ConstraintExpr::Integer(val) => Ok(ConcreteType::Integer(val)),
            ConstraintExpr::Bool(val) => Ok(ConcreteType::Bool(val)),
            ConstraintExpr::String(val) => Ok(ConcreteType::String(val)),
            _ => Err(
                Diagnostic::error(cg, "Could not evaluate const generic expression")
                    .primary_label("Operands have mismatched types"),
            ),
        }
    }

    pub fn inner_ungenerify_type(
        &self,
        var: &TypeVarID,
        symtab: &SymbolTable,
        type_list: &TypeList,
    ) -> Result<Option<ConcreteType>, Diagnostic> {
        match var.resolve(self) {
            TypeVar::Known(_, KnownType::Error, _) => Ok(Some(ConcreteType::Error)),
            TypeVar::Known(_, KnownType::Named(t), params) => {
                let params = params
                    .iter()
                    .map(|v| self.inner_ungenerify_type(v, symtab, type_list))
                    .collect::<Result<Vec<_>, Diagnostic>>()?
                    .into_iter()
                    .collect::<Option<Vec<_>>>();

                let Some(params) = params else {
                    // None is still valid, not an error: just means that the type is not fully
                    // known yet
                    return Ok(None);
                };

                match type_list.get(&t) {
                    Some(t) => Ok(Some(Self::type_decl_to_concrete(t, type_list, params)?)),
                    None => Ok(None),
                }
            }
            TypeVar::Known(loc, KnownType::Integer(val), params) => {
                if !params.is_empty() {
                    return Err(Diagnostic::bug(loc, "integers cannot have type parameters"));
                }

                Ok(Some(ConcreteType::Integer(val.clone())))
            }
            TypeVar::Known(loc, KnownType::Bool(val), params) => {
                if !params.is_empty() {
                    return Err(Diagnostic::bug(
                        loc,
                        "type level bools cannot have type parameters",
                    ));
                }

                Ok(Some(ConcreteType::Bool(val)))
            }
            TypeVar::Known(loc, KnownType::String(val), params) => {
                if !params.is_empty() {
                    return Err(Diagnostic::bug(
                        loc,
                        "type level strings cannot have type parameters",
                    ));
                }

                Ok(Some(ConcreteType::String(val.clone())))
            }
            TypeVar::Known(loc, KnownType::Array, inner) => {
                let value = self.inner_ungenerify_type(&inner[0], symtab, type_list)?;
                let size = self.ungenerify_type(&inner[1], symtab, type_list)?;

                match (value, size) {
                    (Some(value), Some(ConcreteType::Integer(size))) => {
                        Ok(Some(ConcreteType::Array {
                            inner: Box::new(value),
                            size,
                        }))
                    }
                    (Some(_), Some(_)) => Err(Diagnostic::bug(
                        loc,
                        "Array size must be an integer type level value",
                    )),
                    _ => Ok(None),
                }
            }
            TypeVar::Known(_, KnownType::Tuple, inner) => {
                let inner = inner
                    .iter()
                    .map(|v| self.inner_ungenerify_type(v, symtab, type_list))
                    .collect::<Result<Vec<_>, Diagnostic>>()?
                    .into_iter()
                    .collect::<Option<Vec<_>>>();

                match inner {
                    Some(inner) => Ok(Some(ConcreteType::Tuple(inner))),
                    None => Ok(None),
                }
            }
            TypeVar::Known(_, KnownType::Inverted, inner) => Ok(self
                .inner_ungenerify_type(&inner[0], symtab, type_list)?
                .map(|t| ConcreteType::Backward(Box::new(t)))),
            TypeVar::Known(_, KnownType::CopyView, inner) => Ok(self
                .inner_ungenerify_type(&inner[0], symtab, type_list)?
                .map(|t| ConcreteType::CopyView(Box::new(t)))),
            TypeVar::Unknown(_, _, _, _) => Ok(None),
        }
    }

    /// Converts the specified type to a concrete type, returning None
    /// if the type is not fully known or a diagnostic if it fails.
    pub fn ungenerify_type(
        &self,
        var: &TypeVarID,
        symtab: &SymbolTable,
        type_list: &TypeList,
    ) -> Result<Option<ConcreteType>, Diagnostic> {
        Ok(self
            .inner_ungenerify_type(var, symtab, type_list)?
            .map(|ty| ty.resolve_recursive_inversions(false)))
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

        if let Some(t) = self.ungenerify_type(&t, symtab, types)? {
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

        if let Some(t) = self.ungenerify_type(&t, symtab, types)? {
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
