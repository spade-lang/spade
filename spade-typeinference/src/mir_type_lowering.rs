use rustc_hash::FxHashMap as HashMap;

use hir::symbol_table::SymbolTable;
use hir::{Parameter, TypeExpression, TypeSpec};
use spade_common::id_tracker::ExprID;
use spade_common::location_info::{Loc, WithLocation};
use spade_common::name::NameID;
use spade_diagnostics::{Diagnostic, diag_bail};
use spade_hir::pretty_print::PrettyPrint;
use spade_hir::{self as hir, ConstGeneric, ConstGenericWithId, Generic};
use spade_hir::{TypeDeclaration, TypeList};
use spade_types::{ConcreteType, KnownType, PrimitiveType};

use crate::Result;
use crate::TypeState;
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
        &self,
        decl: &TypeDeclaration,
        type_list: &TypeList,
        params: Vec<ConcreteType>,
    ) -> Result<ConcreteType> {
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
                                    self.type_spec_to_concrete(
                                        &arg.ty.inner,
                                        type_list,
                                        &generic_subs,
                                    )?,
                                ))
                            })
                            .collect::<Result<_>>()?;
                        Ok((name.inner.clone(), args))
                    })
                    .collect::<Result<_>>()?;

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
                                self.type_spec_to_concrete(t, type_list, &generic_subs)?,
                            ))
                        },
                    )
                    .collect::<Result<_>>()?;

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
                self.type_spec_to_concrete(&a.type_spec, type_list, &generic_subs)
            }
        }
    }

    pub fn type_expr_to_concrete(
        &self,
        expr: &TypeExpression,
        type_list: &TypeList,
        generic_substitutions: &HashMap<Generic, &ConcreteType>,
    ) -> Result<ConcreteType> {
        match &expr {
            hir::TypeExpression::Bool(val) => Ok(ConcreteType::Bool(*val)),
            hir::TypeExpression::Integer(val) => Ok(ConcreteType::Integer(val.clone())),
            hir::TypeExpression::String(val) => Ok(ConcreteType::String(val.clone())),
            hir::TypeExpression::TypeSpec(inner) => {
                self.type_spec_to_concrete(inner, type_list, generic_substitutions)
            }
            hir::TypeExpression::ConstGeneric(cg) => {
                self.const_generic_to_concrete(cg, generic_substitutions)
            }
        }
    }

    pub fn const_generic_to_concrete(
        &self,
        cg: &Loc<ConstGeneric>,
        generic_substitutions: &HashMap<Generic, &ConcreteType>,
    ) -> Result<ConcreteType> {
        // In order to avoid having multiple evaluation paths for const generics we re-use the
        // const generic evaluation that we alreaedy have on TypeState. However, it can evaluate
        // things to partial values, and requires a type state in order to evaluate.
        //
        // When doing const HIR const generic concretization, we know that we have no unknown
        // type variables, so we will concretize the const generic into a const generic that has
        // no variables first, then use a type state to do the evaluation.
        fn concretize(
            cg: &Loc<ConstGeneric>,
            generic_substitutions: &HashMap<Generic, &ConcreteType>,
        ) -> Result<ConstGeneric> {
            macro_rules! map_inner {
                ($variant:path, ($($inner:expr),*)) => {
                    Ok($variant($( Box::new(concretize($inner, generic_substitutions)?.at_loc($inner)) ),*))
                }
            }
            match &cg.inner {
                ConstGeneric::Name(n) => {
                    let substituted = generic_substitutions
                        .get(&Generic::Named(n.clone()))
                        .ok_or_else(|| {
                            Diagnostic::bug(
                                cg,
                                "Did not find this name in the generic substitutions",
                            )
                        })
                        .and_then(|ty: &&ConcreteType| match ty {
                            ConcreteType::Error => {
                                diag_bail!(cg, "Found an error type in a HIR const generic")
                            }
                            ConcreteType::Tuple(_)
                            | ConcreteType::Struct { .. }
                            | ConcreteType::Array { .. }
                            | ConcreteType::Enum { .. }
                            | ConcreteType::Backward(_)
                            | ConcreteType::CopyView(_)
                            | ConcreteType::Single { .. } => {
                                diag_bail!(cg, "Found a type, not a value in a HIR const generic")
                            }
                            ConcreteType::Integer(value) => Ok(ConstGeneric::Int(value.clone())),
                            ConcreteType::Bool(val) => Ok(ConstGeneric::Bool(*val)),
                            ConcreteType::String(s) => Ok(ConstGeneric::Str(s.clone())),
                        });

                    substituted
                }

                ConstGeneric::Bool(_) | ConstGeneric::Int(_) | ConstGeneric::Str(_) => {
                    Ok(cg.inner.clone())
                }

                ConstGeneric::Add(l, r) => map_inner!(ConstGeneric::Add, (l, r)),
                ConstGeneric::Sub(l, r) => map_inner!(ConstGeneric::Sub, (l, r)),
                ConstGeneric::Mul(l, r) => map_inner!(ConstGeneric::Mul, (l, r)),
                ConstGeneric::Div(l, r) => map_inner!(ConstGeneric::Div, (l, r)),
                ConstGeneric::Mod(l, r) => map_inner!(ConstGeneric::Mod, (l, r)),

                ConstGeneric::Lt(l, r) => map_inner!(ConstGeneric::Lt, (l, r)),
                ConstGeneric::Gt(l, r) => map_inner!(ConstGeneric::Gt, (l, r)),
                ConstGeneric::Le(l, r) => map_inner!(ConstGeneric::Le, (l, r)),
                ConstGeneric::Ge(l, r) => map_inner!(ConstGeneric::Ge, (l, r)),
                ConstGeneric::LogicalAnd(l, r) => map_inner!(ConstGeneric::LogicalAnd, (l, r)),
                ConstGeneric::LogicalOr(l, r) => map_inner!(ConstGeneric::LogicalOr, (l, r)),
                ConstGeneric::LogicalXor(l, r) => map_inner!(ConstGeneric::LogicalXor, (l, r)),
                ConstGeneric::IntBitsFor(i) => map_inner!(ConstGeneric::IntBitsFor, (i)),
                ConstGeneric::UintBitsFor(i) => map_inner!(ConstGeneric::UintBitsFor, (i)),
                ConstGeneric::Eq(l, r) => map_inner!(ConstGeneric::Eq, (l, r)),
                ConstGeneric::NotEq(l, r) => map_inner!(ConstGeneric::NotEq, (l, r)),
                ConstGeneric::LogicalNot(i) => map_inner!(ConstGeneric::LogicalNot, (i)),
            }
        }

        let concrete = concretize(cg, generic_substitutions)?;

        // We will invent a new type state just to do this checking. Since we already got rid
        // of all variables, we can safely do this just to help with evaluation
        let mut child = self.create_child();
        let gl = child.create_empty_generic_list(crate::GenericListSource::Anonymous);
        let constraint_expr = child.visit_const_generic(&concrete, &gl)?;

        let value = constraint_expr.evaluate(self);

        let result = match value {
            crate::constraints::ConstraintExpr::Bool(val) => ConcreteType::Bool(val),
            crate::constraints::ConstraintExpr::Integer(val) => ConcreteType::Integer(val.clone()),
            crate::constraints::ConstraintExpr::String(val) => ConcreteType::String(val.clone()),

            crate::constraints::ConstraintExpr::Var(_)
            | crate::constraints::ConstraintExpr::Sum(_, _)
            | crate::constraints::ConstraintExpr::Difference(_, _)
            | crate::constraints::ConstraintExpr::Product(_, _)
            | crate::constraints::ConstraintExpr::Div(_, _)
            | crate::constraints::ConstraintExpr::Mod(_, _)
            | crate::constraints::ConstraintExpr::Sub(_)
            | crate::constraints::ConstraintExpr::Eq(_, _)
            | crate::constraints::ConstraintExpr::NotEq(_, _)
            | crate::constraints::ConstraintExpr::Lt(_, _)
            | crate::constraints::ConstraintExpr::Gt(_, _)
            | crate::constraints::ConstraintExpr::Le(_, _)
            | crate::constraints::ConstraintExpr::Ge(_, _)
            | crate::constraints::ConstraintExpr::LogicalNot(_)
            | crate::constraints::ConstraintExpr::LogicalAnd(_, _)
            | crate::constraints::ConstraintExpr::LogicalOr(_, _)
            | crate::constraints::ConstraintExpr::LogicalXor(_, _)
            | crate::constraints::ConstraintExpr::IntBitsToRepresent(_)
            | crate::constraints::ConstraintExpr::UintBitsToRepresent(_) => {
                diag_bail!(
                    cg,
                    "Evaluating this HIR const expression did not result in a fully known value"
                )
            }
        };
        Ok(result)
    }

    pub fn type_spec_to_concrete(
        &self,
        spec: &TypeSpec,
        type_list: &TypeList,
        generic_substitutions: &HashMap<Generic, &ConcreteType>,
    ) -> Result<ConcreteType> {
        match spec {
            TypeSpec::Declared(name, params) => {
                let params = params
                    .iter()
                    .map(|p| self.type_expr_to_concrete(p, type_list, generic_substitutions))
                    .collect::<Result<_>>()?;

                let actual = type_list
                    .get(name)
                    .unwrap_or_else(|| panic!("Expected {:?} to be in type list", name));

                self.type_decl_to_concrete(actual, type_list, params)
            }
            TypeSpec::Generic(name) => {
                // Substitute the generic for the current substitution
                Ok((*generic_substitutions.get(name).unwrap_or_else(|| {
                    panic!("Expected a substitution for {}", name.pretty_print())
                }))
                .clone())
            }
            TypeSpec::Tuple(t) => {
                let inner = t
                    .iter()
                    .map(|v| self.type_spec_to_concrete(&v.inner, type_list, generic_substitutions))
                    .collect::<Result<_>>()?;
                Ok(ConcreteType::Tuple(inner))
            }
            TypeSpec::Array { inner, size } => {
                let size_type =
                    Box::new(self.type_expr_to_concrete(size, type_list, generic_substitutions)?);

                let size = if let ConcreteType::Integer(size) = size_type.as_ref() {
                    size.clone()
                } else {
                    panic!("Array size must be an integer")
                };

                Ok(ConcreteType::Array {
                    inner: Box::new(self.type_spec_to_concrete(
                        inner,
                        type_list,
                        generic_substitutions,
                    )?),
                    size,
                })
            }

            TypeSpec::Inverted(inner) => Ok(ConcreteType::Backward(Box::new(
                self.type_spec_to_concrete(inner, type_list, generic_substitutions)?,
            ))),

            TypeSpec::CopyView(inner) => Ok(ConcreteType::CopyView(Box::new(
                self.type_spec_to_concrete(inner, type_list, generic_substitutions)?,
            ))),

            TypeSpec::TraitSelf(_) => panic!("Trying to concretize HIR TraitSelf type"),
            TypeSpec::Wildcard(_) => panic!("Trying to concretize HIR Wildcard type"),
        }
    }

    pub fn inner_ungenerify_type(
        &self,
        var: &TypeVarID,
        symtab: &SymbolTable,
        type_list: &TypeList,
    ) -> Result<Option<ConcreteType>> {
        match var.resolve(self) {
            TypeVar::Known(_, KnownType::Error, _) => Ok(Some(ConcreteType::Error)),
            TypeVar::Known(_, KnownType::Named(t), params) => {
                let Some(params) = params
                    .iter()
                    .map(|v| self.inner_ungenerify_type(v, symtab, type_list))
                    .collect::<Result<Option<Vec<_>>>>()?
                else {
                    return Ok(None);
                };

                Ok(type_list
                    .get(&t)
                    .map(|t| self.type_decl_to_concrete(&t.inner, type_list, params))
                    .transpose()?)
            }
            TypeVar::Known(_, KnownType::Integer(val), params) => {
                assert!(params.is_empty(), "integers cannot have type parameters");

                Ok(Some(ConcreteType::Integer(val.clone())))
            }
            TypeVar::Known(_, KnownType::Bool(val), params) => {
                assert!(
                    params.is_empty(),
                    "type level bools cannot have type parameters"
                );

                Ok(Some(ConcreteType::Bool(val)))
            }
            TypeVar::Known(_, KnownType::String(val), params) => {
                assert!(
                    params.is_empty(),
                    "type level strings cannot have type parameters"
                );

                Ok(Some(ConcreteType::String(val.clone())))
            }
            TypeVar::Known(_, KnownType::Array, inner) => {
                let value = self.inner_ungenerify_type(&inner[0], symtab, type_list)?;
                let size = self
                    .ungenerify_type(&inner[1], symtab, type_list)?
                    .map(|t| {
                        if let ConcreteType::Integer(size) = t {
                            size
                        } else {
                            panic!("Array size must be an integer")
                        }
                    });

                match (value, size) {
                    (Some(value), Some(size)) => Ok(Some(ConcreteType::Array {
                        inner: Box::new(value),
                        size,
                    })),
                    _ => Ok(None),
                }
            }
            TypeVar::Known(_, KnownType::Tuple, inner) => {
                let Some(inner) = inner
                    .iter()
                    .map(|v| self.inner_ungenerify_type(v, symtab, type_list))
                    .collect::<Result<Option<Vec<_>>>>()?
                else {
                    return Ok(None);
                };
                Ok(Some(ConcreteType::Tuple(inner)))
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
    /// if it fails
    pub fn ungenerify_type(
        &self,
        var: &TypeVarID,
        symtab: &SymbolTable,
        type_list: &TypeList,
    ) -> Result<Option<ConcreteType>> {
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
    ) -> Result<ConcreteType> {
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
    ) -> Result<ConcreteType> {
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
