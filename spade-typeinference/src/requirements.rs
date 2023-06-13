use spade_common::location_info::WithLocation;
use spade_common::name::Path;
use spade_common::num_ext::InfallibleToBigInt;

use spade_common::{location_info::Loc, name::Identifier};
use spade_diagnostics::{diag_anyhow, diag_assert, diag_bail, Diagnostic};
use spade_hir::expression::IntLiteral;
use spade_hir::symbol_table::{TypeDeclKind, TypeSymbol};
use spade_hir::ArgumentList;
use spade_types::KnownType;

use crate::equation::TypeVar;
use crate::error::{Error, Result, UnificationErrorExt};
use crate::method_resolution::select_method;
use crate::{Context, GenericListSource, TypeState};

#[derive(Clone, Debug)]
pub enum Requirement {
    HasField {
        /// The type which should have the associated field
        target_type: Loc<TypeVar>,
        /// The field which is required to exist on the struct
        field: Loc<Identifier>,
        /// The expression from which this requirement arrises
        expr: Loc<TypeVar>,
    },
    HasMethod {
        /// The ID of the expression which causes this requirement
        expr_id: Loc<u64>,
        /// The type which should have the associated method
        target_type: Loc<TypeVar>,
        /// The method which should exist on the type
        method: Loc<Identifier>,
        /// The expression from which this requirement arrises
        expr: Loc<TypeVar>,
        /// The argument list passed to the method. This should include the `self` expression as
        /// the appropriate argument (first positional or a non-shorthand self otherwise)
        args: Loc<ArgumentList>,
    },
    /// The type should be an integer large enough to fit the specified value
    FitsIntLiteral {
        value: IntLiteral,
        target_type: Loc<TypeVar>,
    },
}

impl Requirement {
    pub fn replace_type_var(&mut self, from: &TypeVar, to: &TypeVar) {
        match self {
            Requirement::HasField {
                target_type,
                expr,
                field: _,
            } => {
                TypeState::replace_type_var(target_type, from, to);
                TypeState::replace_type_var(expr, from, to);
            }
            Requirement::HasMethod {
                expr_id: _,
                target_type,
                expr,
                method: _,
                args: _,
            } => {
                TypeState::replace_type_var(target_type, from, to);
                TypeState::replace_type_var(expr, from, to);
            }
            Requirement::FitsIntLiteral {
                value: _,
                target_type,
            } => {
                TypeState::replace_type_var(target_type, from, to);
            }
        }
    }

    /// Check if there are updates that allow us to resolve the requirement.
    /// - If target_type is still `Unknown`, we don't know how to resolve the requirement
    /// - Otherwise it will either be unsatsifieable. i.e. the new type does not fulfil the
    /// requirement, in which case an error is returned
    /// - Or the requirement is now satisfied, in which case new unification tasks which are
    /// applied due to the result are returned. After this, the constraint is no longer needed
    /// and can be dropped
    pub fn check(&self, type_state: &mut TypeState, ctx: &Context) -> Result<RequirementResult> {
        match self {
            Requirement::HasField {
                target_type,
                field,
                expr,
            } => {
                target_type.expect_named_or_inverted(
                    false,
                    |inverted, type_name, params| {
                        // Check if we're dealing with a struct
                        match ctx.symtab.type_symbol_by_id(&type_name).inner {
                            TypeSymbol::Declared(_, TypeDeclKind::Struct { is_port: _ }) => {}
                            TypeSymbol::Declared(_, TypeDeclKind::Enum) => {
                                return Err(Error::FieldAccessOnEnum {
                                    loc: target_type.loc(),
                                    actual_type: type_name.clone(),
                                })
                            }
                            TypeSymbol::Declared(_, TypeDeclKind::Primitive { is_port: _ }) => {
                                return Err(Error::FieldAccessOnPrimitive {
                                    loc: target_type.loc(),
                                    actual_type: type_name.clone(),
                                })
                            }
                            TypeSymbol::GenericArg | TypeSymbol::GenericInt => {
                                return Err(Error::FieldAccessOnGeneric {
                                    loc: target_type.loc(),
                                    name: type_name.clone(),
                                })
                            }
                        }

                        // Get the struct, find the type of the field and unify
                        let s = ctx.symtab.struct_by_id(&type_name);

                        let field_spec = if let Some(spec) = s.params.try_get_arg_type(field) {
                            spec
                        } else {
                            return Err(Error::NoSuchField {
                                field: field.clone(),
                                _struct: type_name.clone(),
                            });
                        };

                        // The generic list here refers to the generics being passed to the
                        // types of the struct here. We need to construct it from the
                        // inferred generics.
                        let mapping = s
                            .type_params
                            .iter()
                            .map(|p| p.clone().name_id())
                            .zip(params.iter().cloned())
                            .collect();

                        let generic_list = type_state
                            .add_mapped_generic_list(GenericListSource::Anonymous, mapping);

                        let raw_field_type =
                            type_state.type_var_from_hir(&field_spec, &generic_list);
                        let field_type = if inverted {
                            match raw_field_type {
                                TypeVar::Backward(inner) => TypeVar::Wire(inner),
                                TypeVar::Wire(inner) => TypeVar::Backward(inner),
                                TypeVar::Inverted(inner) => *inner,
                                // If we were in an inverted context and we find
                                // a type which is not a wire, we need to invert
                                // it.
                                // This means that `a.b` if b is `T` is `~T`
                                other => TypeVar::Inverted(Box::new(other)),
                            }
                        } else {
                            raw_field_type
                        };

                        Ok(RequirementResult::Satisfied(vec![Replacement {
                            from: expr.clone(),
                            to: field_type,
                        }]))
                    },
                    || Ok(RequirementResult::NoChange),
                    |other| {
                        Err(Error::FieldAccessOnNonStruct {
                            loc: expr.loc(),
                            got: other.clone(),
                        })
                    },
                )
            }
            Requirement::HasMethod {
                expr_id,
                target_type,
                method,
                expr,
                args,
            } => target_type.expect_named(
                |type_name, _params| {
                    let implementor = select_method(expr.loc(), type_name, method, ctx.items)?;

                    let fn_head = ctx.symtab.unit_by_id(&implementor);

                    type_state.handle_function_like(
                        expr_id.clone(),
                        &expr.inner,
                        &implementor,
                        &fn_head.inner,
                        args,
                        ctx,
                        false,
                        true,
                    )?;
                    Ok(RequirementResult::Satisfied(vec![]))
                },
                || Ok(RequirementResult::NoChange),
                |other| {
                    Err(
                        Diagnostic::error(expr, format!("{other} does not have any methods"))
                            .into(),
                    )
                },
            ),
            Requirement::FitsIntLiteral { value, target_type } => {
                let int_type = ctx
                    .symtab
                    .lookup_type_symbol(&Path::from_strs(&["int"]).nowhere())
                    .map_err(|_| diag_anyhow!(target_type, "The type int was not in the symtab"))?
                    .0;

                target_type.expect_specific_named(
                    int_type,
                    |params| {
                        diag_assert!(target_type, params.len() == 2);
                        match (params[0].clone(), params[1].clone()) {
                            (TypeVar::Known(KnownType::Integer(lo), lo_params), TypeVar::Known(KnownType::Integer(hi), hi_params)) => {
                                assert!(lo_params.is_empty());
                                assert!(hi_params.is_empty());
                                let value = value.clone().as_signed();

                                if lo <= value && value <= hi {
                                    Ok(RequirementResult::Satisfied(vec![]))
                                } else {
                                    let diagnostic = Diagnostic::error(
                                        target_type,
                                        format!("Integer value does not fit in int<{lo}..{hi}>"),
                                    )
                                    .primary_label(format!(
                                        "{value} does not fit in an int<{lo}..{hi}>"
                                    ));

                                    let diagnostic = if lo == 0.to_bigint() {
                                        diagnostic.note(format!(
                                            "int<{lo}..{hi}> fits unsigned integers in the range (0, {hi})",
                                        ))
                                    } else {
                                        diagnostic.note(format!(
                                            "int<{lo}..{hi}> fits integers in the range ({lo}, {hi})",
                                        ))
                                    };

                                    Err(diagnostic.into())
                                }
                        },
                        (_, _) => Ok(RequirementResult::NoChange),
                    }},
                    || Ok(RequirementResult::NoChange),
                    |other| diag_bail!(target_type, "Inferred {other} for integer literal"),
                )
            }
        }
    }

    /// Check if this requirement is satisfied. If so, apply the resulting replacements to the
    /// type state, otherwise add the requirement to the type state requirement list
    #[tracing::instrument(level = "trace", skip(type_state, ctx))]
    pub fn check_or_add(self, type_state: &mut TypeState, ctx: &Context) -> Result<()> {
        match self.check(type_state, ctx)? {
            RequirementResult::NoChange => Ok(type_state.add_requirement(self)),
            RequirementResult::Satisfied(replacements) => {
                for Replacement { from, to } in replacements {
                    type_state
                        .unify(&from.inner, &to, &ctx.symtab)
                        .map_normal_err(|(got, expected)| Error::UnspecifiedTypeError {
                            expected,
                            got,
                            loc: from.loc(),
                        })?;
                }
                Ok(())
            }
        }
    }
}

#[derive(Debug)]
pub struct Replacement {
    pub from: Loc<TypeVar>,
    pub to: TypeVar,
}

#[must_use]
pub enum RequirementResult {
    /// The requirement remains but not enough information is available about
    /// whether or not it is satisfied
    NoChange,
    /// The requirement is now satisfied and can be removed. Refinements of other
    /// type variables which can now be applied are returned
    Satisfied(Vec<Replacement>),
}
