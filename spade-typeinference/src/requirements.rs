use itertools::Itertools;
use num::traits::Pow;
use num::{BigInt, ToPrimitive, Zero};
use spade_common::id_tracker::ExprID;
use spade_common::location_info::WithLocation;
use spade_common::name::Path;
use spade_common::num_ext::InfallibleToBigInt;
use spade_common::{location_info::Loc, name::Identifier};
use spade_diagnostics::{diag_anyhow, diag_assert, diag_bail, Diagnostic};
use spade_hir::expression::CallKind;
use spade_hir::pretty_print::PrettyPrint;
use spade_hir::symbol_table::{TypeDeclKind, TypeSymbol};
use spade_hir::{ArgumentList, Expression, Generic, TypeExpression, WhereClauseKind};
use spade_types::KnownType;

use crate::equation::{ResolvedNamedOrInverted, TypeVar, TypeVarID};
use crate::error::{Result, TypeMismatch, UnificationErrorExt};
use crate::method_resolution::{select_method, FunctionLikeName};
use crate::trace_stack::TraceStackEntry;
use crate::traits::TraitList;
use crate::{Context, GenericListSource, GenericListToken, TurbofishCtx, TypeState};

#[derive(Clone, Debug)]
pub enum ConstantInt {
    Generic(TypeVarID),
    Literal(BigInt),
}

#[derive(Clone, Debug)]
pub enum Requirement {
    HasField {
        /// The type which should have the associated field
        target_type: Loc<TypeVarID>,
        /// The field which is required to exist on the struct
        field: Loc<Identifier>,
        /// The expression from which this requirement arises
        expr: Loc<TypeVarID>,
    },
    HasMethod {
        call_kind: CallKind,
        /// The ID of the expression which causes this requirement
        expr_id: Loc<ExprID>,
        /// The type which should have the associated method
        target_type: Loc<TypeVarID>,
        /// For method call on monomorphised generic with trait bounds
        /// The traits which should be searched for the method
        trait_list: Option<TraitList>,
        /// The method which should exist on the type
        method: Loc<Identifier>,
        /// The expression from which this requirement arises
        expr: Loc<TypeVarID>,
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
        target_type: Loc<TypeVarID>,
    },
    ValidPipelineOffset {
        definition_depth: Loc<TypeVarID>,
        current_stage: Loc<TypeVarID>,
        reference_offset: Loc<TypeVarID>,
    },
    PositivePipelineDepth {
        depth: Loc<TypeVarID>,
    },
    RangeIndexEndAfterStart {
        expr: Loc<()>,
        start: Loc<TypeVarID>,
        end: Loc<TypeVarID>,
    },
    RangeIndexInArray {
        index: Loc<TypeVarID>,
        size: Loc<TypeVarID>,
    },
    ArrayIndexeeIsNonZero {
        index: Loc<()>,
        array: Loc<TypeVarID>,
        array_size: Loc<TypeVarID>,
    },
    WhereInequality {
        var: Generic,
        lhs: Loc<TypeVarID>,
        rhs: Loc<TypeVarID>,
        inequality: WhereClauseKind,
        message: Option<String>,
        callsite: Option<Loc<()>>,
    },
    /// The provided TypeVarID should all share a base type
    SharedBase(Vec<Loc<TypeVarID>>),
}

impl Requirement {
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
                let resolved = target_type
                    .resolve(&type_state)
                    .clone()
                    .resolve_named_or_inverted(false, type_state);
                match resolved {
                    ResolvedNamedOrInverted::Named(inverted, type_name, params) => {
                        // Check if we're dealing with a struct
                        match ctx.symtab.type_symbol_by_id(&type_name).inner {
                            TypeSymbol::Declared(_, TypeDeclKind::Struct { is_port: _ }) => {}
                            TypeSymbol::Declared(_, TypeDeclKind::Enum) => {
                                return Err(Diagnostic::error(
                                    target_type,
                                    "Field access on an enum type",
                                )
                                .primary_label(format!("expected a struct, got {}", type_name))
                                .help("Field access is only allowed on structs"));
                            }
                            TypeSymbol::Declared(_, TypeDeclKind::Primitive { .. }) => {
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
                                .primary_label(format!(
                                    "Expected struct found {}",
                                    target_type.display(type_state)
                                ))
                                .note("Field access is only allowed on structs"))
                            }
                            TypeSymbol::Alias(_) => diag_bail!(
                                target_type,
                                "Found a type alias that wasn't lowered during AST lowering"
                            ),
                        }

                        // Get the struct, find the type of the field and unify
                        let s = ctx.symtab.struct_by_id(&type_name);

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
                            .map(|p| p.clone().name.clone())
                            .zip(params.iter().cloned())
                            .collect();

                        let generic_list = type_state
                            .add_mapped_generic_list(GenericListSource::Anonymous, mapping);

                        let raw_field_type =
                            type_state.type_var_from_hir(expr.loc(), field_spec, &generic_list)?;
                        let field_type = if inverted {
                            match raw_field_type.resolve(type_state) {
                                TypeVar::Known(loc, KnownType::Wire, inner) => {
                                    TypeVar::backward(loc.loc(), inner[0].clone(), type_state)
                                        .insert(type_state)
                                }
                                TypeVar::Known(_, KnownType::Inverted, inner) => inner[0].clone(),
                                // If we were in an inverted context and we find
                                // a type which is not a wire, we need to invert
                                // it.
                                // This means that `a.b` if b is `T` is `inv T`
                                _ => TypeVar::inverted(target_type.loc(), raw_field_type)
                                    .insert(type_state),
                            }
                        } else {
                            raw_field_type
                        };

                        Ok(RequirementResult::Satisfied(vec![Replacement {
                            from: expr.clone(),
                            to: field_type,
                            context: None,
                        }]))
                    }
                    ResolvedNamedOrInverted::Unknown => Ok(RequirementResult::NoChange),
                    ResolvedNamedOrInverted::Other => Err(Diagnostic::error(
                        target_type,
                        format!(
                            "Field access on {} which is not a struct",
                            target_type.display(type_state)
                        ),
                    )
                    .primary_label(format!(
                        "Expected a struct, found {}",
                        target_type.display(type_state)
                    ))
                    .help("Field access is only allowed on structs")),
                }
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
            } => match &target_type.inner.resolve(type_state) {
                TypeVar::Known(_, KnownType::Error, _) => {
                    return Ok(RequirementResult::Satisfied(vec![]))
                }
                TypeVar::Known(_, _, _) => {
                    let Some(implementor) = select_method(
                        expr.loc(),
                        target_type,
                        method,
                        &ctx.trait_impls,
                        type_state,
                    )?
                    else {
                        return Ok(RequirementResult::NoChange);
                    };

                    let fn_head = ctx.symtab.unit_by_id(&implementor);

                    type_state.handle_function_like(
                        *expr_id,
                        &expr.inner,
                        &FunctionLikeName::Method(method.inner.clone()),
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
                }
                TypeVar::Unknown(_, _, traits, _) => {
                    let candidates = traits
                        .inner
                        .iter()
                        .filter_map(|r#trait| {
                            ctx.items
                                .get_trait(&r#trait.name)
                                .and_then(|t| t.fns.get(method))
                                .map(|method| (r#trait, method))
                        })
                        .collect::<Vec<_>>();

                    match candidates.as_slice() {
                        [] => {
                            return Ok(RequirementResult::UnsatisfiedNow(Diagnostic::error(
                                expr_id,
                                format!(
                                    "{target_type} has no method `{method}`",
                                    target_type = target_type.display(type_state)
                                ),
                            )))
                        }
                        // NOTE: We need to wait until we've unified with a known type
                        // before dropping this requirement in order to create a generic list
                        [_] => Ok(RequirementResult::NoChange),
                        multiple => Err(Diagnostic::error(
                            expr_id,
                            format!("Multiple traits have a method `{method}` "),
                        )
                        .primary_label("Ambiguous method call")
                        .secondary_label(
                            target_type,
                            format!(
                                "This has type {target_type}",
                                target_type = target_type.display(type_state)
                            ),
                        )
                        .note(format!(
                            "The method `{method}` exists on all these traits: {} and {}",
                            multiple[0..multiple.len() - 1]
                                .iter()
                                .map(|(t, _)| t.display(type_state))
                                .join(", "),
                            multiple[multiple.len() - 1].0.display(type_state)
                        ))),
                    }
                }
            },
            Requirement::FitsIntLiteral { value, target_type } => {
                let int_type = ctx
                    .symtab
                    .lookup_type_symbol(&Path::from_strs(&["int"]).nowhere(), false)
                    .map_err(|_| diag_anyhow!(target_type, "The type int was not in the symtab"))?
                    .0;
                let uint_type = ctx
                    .symtab
                    .lookup_type_symbol(&Path::from_strs(&["uint"]).nowhere(), false)
                    .map_err(|_| diag_anyhow!(target_type, "The type int was not in the symtab"))?
                    .0;

                target_type.resolve(type_state).expect_named(
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
                                format!("Expected {target_type}, got integer literal", target_type = target_type.display(type_state))
                            )
                                .primary_label(format!("expected {target_type}", target_type = target_type.display(type_state))));
                        };

                        diag_assert!(target_type, params.len() == 1);
                        params[0].resolve(type_state).expect_integer(
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
                                    ConstantInt::Generic(tvar) => {
                                        match tvar.resolve(type_state) {
                                            TypeVar::Unknown(_, _, _, _) => return Ok(RequirementResult::NoChange),
                                            TypeVar::Known(_, KnownType::Integer(val), _) => {
                                                val.clone()
                                            }
                                            other @ TypeVar::Known(_, _, _) => diag_bail!(
                                                target_type,
                                                "Inferred non-integer type ({other}) for type level integer", other = other.display(type_state)
                                            ),
                                        }
                                    }
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
                            |_| diag_bail!(target_type, "Inferred {target_type} for integer literal", target_type = target_type.display(type_state)),
                            || Ok(RequirementResult::NoChange),
                        )
                    },
                    || Ok(RequirementResult::NoChange),
                    |other| diag_bail!(target_type, "Inferred {other} for integer literal", other = other.display(type_state)),
                    || Ok(RequirementResult::NoChange),
                )
            }
            Requirement::PositivePipelineDepth { depth } => {
                match &depth.inner.resolve(type_state) {
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
                }
            }
            Requirement::RangeIndexEndAfterStart { expr, start, end } => {
                match (&start.resolve(type_state), &end.resolve(type_state)) {
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
                        "Got non-integer ranges ({start}:{end})",
                        start = start.display(type_state),
                        end = end.display(type_state),
                    )),
                }
            }
            Requirement::RangeIndexInArray { index, size } => {
                match (&index.resolve(type_state), &size.resolve(type_state)) {
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
                        "Got non-integer index or size (index: {index}, size: {size})",
                        index = index.display(type_state),
                        size = size.display(type_state),
                    )),
                }
            }
            Requirement::ArrayIndexeeIsNonZero {
                index,
                array,
                array_size,
            } => match &array_size.resolve(type_state) {
                TypeVar::Known(_, KnownType::Integer(size), _) => {
                    if size == &BigInt::ZERO {
                        Err(
                            Diagnostic::error(index, "Arrays without elements cannot be indexed")
                                .primary_label("Indexing zero-element array")
                                .secondary_label(
                                    array,
                                    format!("This has type {}", array.display(type_state)),
                                ),
                        )
                    } else {
                        Ok(RequirementResult::Satisfied(vec![]))
                    }
                }
                TypeVar::Unknown(_, _, _, _) => Ok(RequirementResult::NoChange),
                other => diag_bail!(
                    index,
                    "Inferred non-integer array size ({other})",
                    other = other.display(type_state)
                ),
            },
            Requirement::ValidPipelineOffset {
                definition_depth,
                current_stage,
                reference_offset,
            } => match (
                &definition_depth.resolve(type_state),
                &reference_offset.resolve(type_state),
            ) {
                (TypeVar::Known(_, dk, _), TypeVar::Known(_, rk, _)) => match (&dk, &rk) {
                    (KnownType::Integer(ddepth), KnownType::Integer(rdepth)) => {
                        if rdepth < &BigInt::zero() {
                            Err(Diagnostic::error(
                                reference_offset,
                                format!("Pipeline references cannot refer to negative stages, inferred {rdepth}")
                            )
                                .primary_label(format!("This references stage {rdepth}"))
                                .help(format!("This offset is relative to the current stage which is {current_stage}", current_stage = current_stage.display(type_state))))
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
                                    "This offset is relative to the current stage which is {current_stage}",
                                    current_stage = current_stage.display(type_state)
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
            Requirement::WhereInequality {
                var,
                lhs,
                rhs,
                inequality,
                message,
                callsite,
            } => match (lhs.resolve(type_state), rhs.resolve(type_state)) {
                (
                    TypeVar::Known(_, KnownType::Integer(lhs_val), _),
                    TypeVar::Known(_, KnownType::Integer(rhs_val), _),
                ) => {
                    let result = match inequality {
                        WhereClauseKind::Eq => {
                            diag_bail!(lhs, "Found an == constraint being handled by requirements")
                        }
                        WhereClauseKind::Neq => lhs_val != rhs_val,
                        WhereClauseKind::Lt => lhs_val < rhs_val,
                        WhereClauseKind::Leq => lhs_val <= rhs_val,
                        WhereClauseKind::Gt => lhs_val > rhs_val,
                        WhereClauseKind::Geq => lhs_val >= rhs_val,
                    };

                    if result {
                        Ok(RequirementResult::Satisfied(vec![]))
                    } else {
                        let loc = callsite.unwrap_or(lhs.loc());
                        let mut diag = Diagnostic::error(
                            loc,
                            format!(
                                "Expected {var} {inequality} {rhs_val} but {var} is {lhs_val} ",
                                var = var.pretty_print()
                            ),
                        )
                        .primary_label(format!(
                            "Expected {var} {inequality} {rhs_val}, but {var} is {lhs_val}",
                            var = var.pretty_print()
                        ));
                        if let Some(message) = message {
                            diag = diag.note(message.to_string())
                        }
                        Err(diag)
                    }
                }
                (TypeVar::Unknown(_, _, _, _), _) | (_, TypeVar::Unknown(_, _, _, _)) => {
                    Ok(RequirementResult::NoChange)
                }
                (TypeVar::Known(_, KnownType::Integer(_), _), _) => {
                    diag_bail!(rhs, "Found non-integer in where clause inequality")
                }
                (_, TypeVar::Known(_, _, _)) => {
                    diag_bail!(lhs, "Found non-integer in where clause inequality")
                }
            },
            Requirement::SharedBase(types) => {
                let first_known = types
                    .iter()
                    .find_map(|t| match t.resolve(type_state).clone() {
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
                                        loc,
                                        base.inner.clone(),
                                        first_params
                                            .iter()
                                            .map(|_| type_state.new_generic_any())
                                            .collect(),
                                    )
                                    .insert(type_state),
                                    context: None,
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
            RequirementResult::NoChange | RequirementResult::UnsatisfiedNow(_) => {
                type_state.add_requirement(self);
                Ok(())
            }
            RequirementResult::Satisfied(replacements) => {
                type_state
                    .owned
                    .trace_stack
                    .push(|| TraceStackEntry::ResolvedRequirement(self.clone()));
                for Replacement { from, to, context } in replacements {
                    type_state
                        .unify(&from.inner, &to, ctx)
                        .into_diagnostic_or_default(&from, context, type_state)?;
                }
                Ok(())
            }
        }
    }
}

pub struct Replacement {
    pub from: Loc<TypeVarID>,
    pub to: TypeVarID,
    pub context: Option<Box<dyn Fn(Diagnostic, TypeMismatch) -> Diagnostic>>,
}

#[must_use]
pub enum RequirementResult {
    /// The requirement remains but not enough information is available about
    /// whether or not it is satisfied
    NoChange,
    /// This requirement is unsatisfied now, but may be satisfied before the type checking
    /// of the whole unit is done. A final pass of requirements of a module should
    /// emit these as errors, earlier checks should treat them as NoChange
    UnsatisfiedNow(Diagnostic),
    /// The requirement is now satisfied and can be removed. Refinements of other
    /// type variables which can now be applied are returned
    Satisfied(Vec<Replacement>),
}
