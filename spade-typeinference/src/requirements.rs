use num::traits::Pow;
use num::{BigInt, ToPrimitive, Zero};
use spade_common::location_info::WithLocation;
use spade_common::name::Path;
use spade_common::num_ext::InfallibleToBigInt;
use spade_common::{location_info::Loc, name::Identifier};
use spade_diagnostics::{diag_anyhow, diag_assert, diag_bail, Diagnostic};
use spade_hir::expression::CallKind;
use spade_hir::symbol_table::{TypeDeclKind, TypeSymbol};
use spade_hir::{ArgumentList, Expression, TypeExpression};
use spade_types::KnownType;

use crate::equation::{TraitList, TypeVar};
use crate::error::{Result, TypeMismatch, UnificationErrorExt};
use crate::method_resolution::select_method;
use crate::trace_stack::TraceStackEntry;
use crate::{Context, GenericListSource, GenericListToken, TurbofishCtx, TypeState};

#[derive(Clone, Debug)]
pub enum ConstantInt {
    Generic(TypeVar),
    Literal(BigInt),
}

#[derive(Clone, Debug)]
pub enum Requirement {
    HasField {
        /// The type which should have the associated field
        target_type: Loc<TypeVar>,
        /// The field which is required to exist on the struct
        field: Loc<Identifier>,
        /// The expression from which this requirement arises
        expr: Loc<TypeVar>,
    },
    HasMethod {
        call_kind: CallKind,
        /// The ID of the expression which causes this requirement
        expr_id: Loc<u64>,
        /// The type which should have the associated method
        target_type: Loc<TypeVar>,
        /// For method call on monomorphised generic with trait bounds
        /// The traits which should be searched for the method
        trait_list: Option<TraitList>,
        /// The method which should exist on the type
        method: Loc<Identifier>,
        /// The expression from which this requirement arises
        expr: Loc<TypeVar>,
        /// The argument list passed to the method. This should include the `self` expression as
        /// the appropriate argument (first positional or a non-shorthand self otherwise)
        args: Loc<ArgumentList<Expression>>,
        /// The turbofish specified on the method.
        turbofish: Option<Loc<ArgumentList<TypeExpression>>>,
        /// The generic list of the context where this is instantiated
        prev_generic_list: GenericListToken,
    },
    /// The type should be an integer large enough to fit the specified value
    FitsIntLiteral {
        value: ConstantInt,
        target_type: Loc<TypeVar>,
    },
    ValidPipelineOffset {
        definition_depth: Loc<TypeVar>,
        current_stage: Loc<TypeVar>,
        reference_offset: Loc<TypeVar>,
    },
    PositivePipelineDepth {
        depth: Loc<TypeVar>,
    },
    RangeIndexEndAfterStart {
        expr: Loc<()>,
        start: Loc<TypeVar>,
        end: Loc<TypeVar>,
    },
    RangeIndexInArray {
        index: Loc<TypeVar>,
        size: Loc<TypeVar>,
    },
    /// The provided TypeVar should all share a base type
    SharedBase(Vec<Loc<TypeVar>>),
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
                trait_list,
                expr,
                method: _,
                args: _,
                turbofish: _,
                prev_generic_list: _,
                call_kind: _,
            } => {
                if let TypeVar::Unknown(_, _, from_trait_list, _) = from {
                    if !from_trait_list.inner.is_empty() {
                        *trait_list = Some(from_trait_list.clone());
                    }
                }
                TypeState::replace_type_var(target_type, from, to);
                TypeState::replace_type_var(expr, from, to);
            }
            Requirement::FitsIntLiteral { value, target_type } => {
                match value {
                    ConstantInt::Generic(var) => TypeState::replace_type_var(var, from, to),
                    ConstantInt::Literal(_) => {}
                };
                TypeState::replace_type_var(target_type, from, to);
            }
            Requirement::ValidPipelineOffset {
                definition_depth,
                current_stage,
                reference_offset,
            } => {
                TypeState::replace_type_var(definition_depth, from, to);
                TypeState::replace_type_var(current_stage, from, to);
                TypeState::replace_type_var(reference_offset, from, to);
            }
            Requirement::RangeIndexEndAfterStart {
                expr: _,
                start,
                end,
            } => {
                TypeState::replace_type_var(start, from, to);
                TypeState::replace_type_var(end, from, to);
            }
            Requirement::RangeIndexInArray { index, size } => {
                TypeState::replace_type_var(index, from, to);
                TypeState::replace_type_var(size, from, to);
            }
            Requirement::PositivePipelineDepth { depth } => {
                TypeState::replace_type_var(depth, from, to)
            }
            Requirement::SharedBase(bases) => {
                for t in bases {
                    TypeState::replace_type_var(t, from, to)
                }
            }
        }
    }

    /// Check if there are updates that allow us to resolve the requirement.
    /// - If target_type is still `Unknown`, we don't know how to resolve the requirement
    /// - Otherwise it will either be unsatisfiable. i.e. the new type does not fulfill the
    /// requirement, in which case an error is returned
    /// - Or the requirement is now satisfied, in which case new unification tasks which are
    /// applied due to the result are returned. After this, the constraint is no longer needed
    /// and can be dropped
    #[tracing::instrument(level = "trace", skip(type_state, ctx))]
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
                        match ctx.symtab.type_symbol_by_id(type_name).inner {
                            TypeSymbol::Declared(_, TypeDeclKind::Struct { is_port: _ }) => {}
                            TypeSymbol::Declared(_, TypeDeclKind::Enum) => {
                                return Err(Diagnostic::error(
                                    target_type,
                                    "Field access on an enum type",
                                )
                                .primary_label(format!("expected a struct, got {}", type_name))
                                .help("Field access is only allowed on structs"));
                            }
                            TypeSymbol::Declared(_, TypeDeclKind::Primitive { is_port: _ }) => {
                                return Err(Diagnostic::error(
                                    target_type,
                                    "Field access on a primitive type",
                                )
                                .primary_label(format!("expected a struct, got {}", type_name))
                                .note("Field access is only allowed on structs"));
                            }
                            TypeSymbol::GenericArg { traits: _ } | TypeSymbol::GenericMeta(_) => {
                                return Err(Diagnostic::error(
                                    target_type,
                                    "Field access on a generic type",
                                )
                                .primary_label(format!("Expected struct found {target_type}"))
                                .note("Field access is only allowed on structs"))
                            }
                        }

                        // Get the struct, find the type of the field and unify
                        let s = ctx.symtab.struct_by_id(type_name);

                        let field_spec = if let Some(spec) = s.params.try_get_arg_type(field) {
                            spec
                        } else {
                            return Err(Diagnostic::error(
                                field,
                                format!("{} has no field named {}", type_name, field),
                            )
                            .primary_label(format!("Not a field of {type_name}")));
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
                            type_state.type_var_from_hir(expr.loc(), field_spec, &generic_list)?;
                        let field_type = if inverted {
                            match raw_field_type {
                                TypeVar::Known(loc, KnownType::Wire, inner) => {
                                    TypeVar::backward(loc, inner[0].clone())
                                }
                                TypeVar::Known(_, KnownType::Inverted, inner) => inner[0].clone(),
                                // If we were in an inverted context and we find
                                // a type which is not a wire, we need to invert
                                // it.
                                // This means that `a.b` if b is `T` is `inv T`
                                other => TypeVar::inverted(target_type.loc(), other),
                            }
                        } else {
                            raw_field_type
                        };

                        Ok(RequirementResult::Satisfied(vec![Replacement {
                            from: expr.clone(),
                            to: field_type,
                            context: None,
                        }]))
                    },
                    || Ok(RequirementResult::NoChange),
                    |_| {
                        Err(Diagnostic::error(
                            target_type,
                            format!("Field access on {} which is not a struct", target_type),
                        )
                        .primary_label(format!("Expected a struct, found {}", target_type))
                        .help("Field access is only allowed on structs"))
                    },
                )
            }
            Requirement::HasMethod {
                expr_id,
                target_type,
                method,
                trait_list: _,
                expr,
                args,
                turbofish,
                prev_generic_list,
                call_kind,
            } => target_type.expect_named(
                |_type_name, _params| {
                    let Some(implementor) =
                        select_method(expr.loc(), target_type, method, &type_state.trait_impls)?
                    else {
                        return Ok(RequirementResult::NoChange);
                    };

                    let fn_head = ctx.symtab.unit_by_id(&implementor);

                    type_state.handle_function_like(
                        *expr_id,
                        &expr.inner,
                        &implementor,
                        &fn_head,
                        call_kind,
                        args,
                        ctx,
                        false,
                        true,
                        turbofish.as_ref().map(|turbofish| TurbofishCtx {
                            turbofish,
                            prev_generic_list,
                            type_ctx: ctx,
                        }),
                        prev_generic_list,
                    )?;
                    Ok(RequirementResult::Satisfied(vec![]))
                },
                || Ok(RequirementResult::NoChange),
                |other| {
                    Err(Diagnostic::error(
                        expr,
                        format!("{other} does not have any methods"),
                    ))
                },
            ),
            Requirement::FitsIntLiteral { value, target_type } => {
                let int_type = ctx
                    .symtab
                    .lookup_type_symbol(&Path::from_strs(&["int"]).nowhere())
                    .map_err(|_| diag_anyhow!(target_type, "The type int was not in the symtab"))?
                    .0;
                let uint_type = ctx
                    .symtab
                    .lookup_type_symbol(&Path::from_strs(&["uint"]).nowhere())
                    .map_err(|_| diag_anyhow!(target_type, "The type int was not in the symtab"))?
                    .0;

                target_type.expect_named(
                    |name, params| {
                        let unsigned = if name == &int_type {
                            false
                        }
                        else if name == &uint_type {
                            true
                        }
                        else {
                            return Err(Diagnostic::error(
                                target_type,
                                format!("Expected {target_type}, got integer literal")
                            )
                                .primary_label(format!("expected {target_type}")));
                        };

                        diag_assert!(target_type, params.len() == 1);
                        params[0].expect_integer(
                            |size| {
                                let two = 2.to_bigint();

                                let size_u32 = size.to_u32().ok_or_else(|| {
                                    Diagnostic::bug(
                                        target_type,
                                        "Integer size does not fit in 32-bit unsigned number",
                                    )
                                    .note("How did you manage to trigger this 🤔")
                                })?;

                                let value = match value {
                                    ConstantInt::Generic(TypeVar::Unknown(_, _, _, _)) => return Ok(RequirementResult::NoChange),
                                    ConstantInt::Generic(TypeVar::Known(_, KnownType::Integer(val), _)) => {
                                        val.clone()
                                    }
                                    ConstantInt::Generic(other @ TypeVar::Known(_, _, _)) => diag_bail!(
                                        target_type,
                                        "Inferred non-integer type ({other}) for type level integer"
                                    ),
                                    ConstantInt::Literal(val) => val.clone(),
                                };

                                // If the value is 0, we can fit it into any integer and
                                // can get rid of the requirement
                                if value == BigInt::zero() {
                                    return Ok(RequirementResult::Satisfied(vec![]));
                                }

                                let contained_range = if unsigned {
                                    (
                                        BigInt::zero(),
                                        two.pow(size_u32) - 1.to_bigint(),
                                    )
                                } else {
                                    (
                                        -two.clone().pow(size_u32.saturating_sub(1)),
                                        two.pow(size_u32.saturating_sub(1)).checked_sub(&1.to_bigint()).unwrap_or(0.to_bigint())
                                    )
                                };

                                if value < contained_range.0 || value > contained_range.1 {
                                    let diagnostic = Diagnostic::error(
                                        target_type,
                                        format!("Integer value does not fit in int<{size}>"),
                                    )
                                    .primary_label(format!(
                                        "{value} does not fit in an {name}<{size}>"
                                    ));

                                    let diagnostic = if unsigned {
                                        diagnostic.note(format!(
                                            "{name}<{size}> fits unsigned integers in the range (0, {})",
                                            contained_range.1,
                                        ))
                                    } else {
                                        diagnostic.note(format!(
                                            "{name}<{size}> fits integers in the range ({}, {})",
                                            contained_range.0, contained_range.1
                                        ))
                                    };

                                    Err(diagnostic)
                                } else {
                                    Ok(RequirementResult::Satisfied(vec![]))
                                }
                            },
                            || Ok(RequirementResult::NoChange),
                            |_| diag_bail!(target_type, "Inferred {target_type} for integer literal"),
                        )
                    },
                    || Ok(RequirementResult::NoChange),
                    |other| diag_bail!(target_type, "Inferred {other} for integer literal"),
                )
            }
            Requirement::PositivePipelineDepth { depth } => match &depth.inner {
                TypeVar::Known(_, KnownType::Integer(i), _) => {
                    if i < &BigInt::zero() {
                        Err(Diagnostic::error(depth, "Negative pipeline depth")
                            .primary_label(format!("Expected non-negative depth, found {i}")))
                    } else {
                        Ok(RequirementResult::Satisfied(vec![]))
                    }
                }
                TypeVar::Known(_, _, _) => {
                    Err(diag_anyhow!(depth, "Got non integer pipeline depth"))
                }
                TypeVar::Unknown(_, _, _, _) => Ok(RequirementResult::NoChange),
            },
            Requirement::RangeIndexEndAfterStart { expr, start, end } => {
                match (&start.inner, &end.inner) {
                    (
                        TypeVar::Known(_, KnownType::Integer(start_val), _),
                        TypeVar::Known(_, KnownType::Integer(end_val), _),
                    ) => {
                        if start_val > end_val {
                            Err(Diagnostic::error(
                                expr,
                                "The end of the range must be after the start",
                            )
                            .primary_label("Range end before start")
                            .secondary_label(start, format!("Start was inferred to be {start_val}"))
                            .secondary_label(end, format!("End was inferred to be {end_val}"))
                            .help("If you want to swap the order of the elements, you can use `std::conv::flip_array`"))
                        } else {
                            Ok(RequirementResult::Satisfied(vec![]))
                        }
                    }
                    (TypeVar::Unknown(_, _, _, _), _) | (_, TypeVar::Unknown(_, _, _, _)) => {
                        Ok(RequirementResult::NoChange)
                    }
                    (TypeVar::Known(_, _, _), TypeVar::Known(_, _, _)) => Err(diag_anyhow!(
                        start,
                        "Got non-integer ranges ({start}:{end})"
                    )),
                }
            }
            Requirement::RangeIndexInArray { index, size } => match (&index.inner, &size.inner) {
                (
                    TypeVar::Known(_, KnownType::Integer(index_val), _),
                    TypeVar::Known(_, KnownType::Integer(size_val), _),
                ) => {
                    if index_val > size_val {
                        Err(Diagnostic::error(index, "Range index out of bounds")
                            .primary_label(format!("Index `{index_val}` out of bounds"))
                            .secondary_label(
                                size,
                                format!("The array only has {size_val} elements"),
                            ))
                    } else {
                        Ok(RequirementResult::Satisfied(vec![]))
                    }
                }
                (TypeVar::Unknown(_, _, _, _), _) | (_, TypeVar::Unknown(_, _, _, _)) => {
                    Ok(RequirementResult::NoChange)
                }
                (TypeVar::Known(_, _, _), TypeVar::Known(_, _, _)) => Err(diag_anyhow!(
                    index,
                    "Got non-integer index or size (index: {index}, size: {size})"
                )),
            },
            Requirement::ValidPipelineOffset {
                definition_depth,
                current_stage,
                reference_offset,
            } => match (&definition_depth.inner, &reference_offset.inner) {
                (TypeVar::Known(_, dk, _), TypeVar::Known(_, rk, _)) => match (&dk, &rk) {
                    (KnownType::Integer(ddepth), KnownType::Integer(rdepth)) => {
                        if rdepth < &BigInt::zero() {
                            Err(Diagnostic::error(
                                reference_offset,
                                format!("Pipeline references cannot refer to negative stages, inferred {rdepth}")
                            )
                                .primary_label(format!("This references stage {rdepth}"))
                                .help(format!("This offset is relative to the current stage which is {current_stage}")))
                        } else if rdepth > ddepth {
                            Err(Diagnostic::error(
                                reference_offset,
                                format!("Pipeline references stage {rdepth} which is beyond the end of the pipeline")
                            )
                                .primary_label("Reference past the end of the pipeline")
                                .secondary_label(definition_depth, format!(
                                    "Depth {ddepth} specified here"
                                ))
                                .help(format!(
                                    "This offset is relative to the current stage which is {current_stage}"
                                )))
                        } else {
                            Ok(RequirementResult::Satisfied(vec![]))
                        }
                    }
                    (KnownType::Integer(_), _) => Err(Diagnostic::bug(
                        reference_offset,
                        "Inferred non-integer pipeline depth",
                    )),
                    (_, _) => Err(Diagnostic::bug(
                        definition_depth,
                        "Inferred non-integer pipeline depth",
                    )),
                },
                (TypeVar::Known(_, _, _), TypeVar::Unknown(_, _, _, _)) => {
                    Ok(RequirementResult::NoChange)
                }
                (TypeVar::Unknown(_, _, _, _), TypeVar::Known(_, _, _)) => {
                    Ok(RequirementResult::NoChange)
                }
                (TypeVar::Unknown(_, _, _, _), TypeVar::Unknown(_, _, _, _)) => {
                    Ok(RequirementResult::NoChange)
                }
            },
            Requirement::SharedBase(types) => {
                let first_known = types.iter().find_map(|t| match &t.inner {
                    TypeVar::Known(loc, base, params) => {
                        Some((loc, base.clone().at_loc(t), params))
                    }
                    TypeVar::Unknown(_, _, _, _) => None,
                });

                if let Some((loc, base, first_params)) = first_known {
                    Ok(RequirementResult::Satisfied(
                        types
                            .iter()
                            .map(|ty| {
                                let base = base.clone();
                                // Since we unify requirement results, we can just use placeholder
                                // parameters here. We know that the number of parameters should
                                // be the same as the params of the first base we found
                                Replacement {
                                    from: ty.clone(),
                                    to: TypeVar::Known(
                                        *loc,
                                        base.inner.clone(),
                                        first_params
                                            .iter()
                                            .map(|_| type_state.new_generic_any())
                                            .collect(),
                                    ),
                                    context: Some(Box::new(move |d, TypeMismatch { e, g }| {
                                        let base = base.clone();
                                        d.message(format!("Expected type {e}, got {g}"))
                                            .primary_label(format!("expected {e}"))
                                            .secondary_label(
                                                base,
                                                format!("type {g} inferred here"),
                                            )
                                    })),
                                }
                            })
                            .collect(),
                    ))
                } else {
                    Ok(RequirementResult::NoChange)
                }
            }
        }
    }

    /// Check if this requirement is satisfied. If so, apply the resulting replacements to the
    /// type state, otherwise add the requirement to the type state requirement list
    #[tracing::instrument(level = "trace", skip(type_state, ctx))]
    pub fn check_or_add(self, type_state: &mut TypeState, ctx: &Context) -> Result<()> {
        match self.check(type_state, ctx)? {
            RequirementResult::NoChange => {
                type_state.add_requirement(self);
                Ok(())
            }
            RequirementResult::Satisfied(replacements) => {
                type_state
                    .trace_stack
                    .push(TraceStackEntry::ResolvedRequirement(self.clone()));
                for Replacement { from, to, context } in replacements {
                    type_state
                        .unify(&from.inner, &to, ctx)
                        .into_diagnostic_or_default(&from, context)?;
                }
                Ok(())
            }
        }
    }
}

pub struct Replacement {
    pub from: Loc<TypeVar>,
    pub to: TypeVar,
    pub context: Option<Box<dyn Fn(Diagnostic, TypeMismatch) -> Diagnostic>>,
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
