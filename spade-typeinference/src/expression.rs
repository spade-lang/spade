use num::{BigInt, One};
use spade_common::location_info::{Loc, WithLocation};
use spade_common::name::Identifier;
use spade_common::num_ext::InfallibleToBigInt;
use spade_diagnostics::diagnostic::DiagnosticLevel;
use spade_diagnostics::{diag_anyhow, Diagnostic};
use spade_hir::expression::{BinaryOperator, IntLiteralKind, NamedArgument, UnaryOperator};
use spade_hir::{ExprKind, Expression};
use spade_macros::trace_typechecker;
use spade_types::meta_types::MetaType;
use spade_types::KnownType;

use crate::constraints::{bits_to_store, ce_int, ce_var, ConstraintExpr, ConstraintSource};
use crate::equation::{TypeVar, TypedExpression};
use crate::error::{TypeMismatch as Tm, UnificationErrorExt};
use crate::fixed_types::{t_bit, t_bool, t_void};
use crate::requirements::{ConstantInt, Requirement};
use crate::{Context, GenericListToken, HasType, Result, TraceStackEntry, TypeState};

macro_rules! assuming_kind {
    ($pattern:pat = $expr:expr => $block:block) => {
        if let $pattern = &$expr.inner.kind {
            $block
        } else {
            panic!("Incorrect assumption about expression kind")
        };
    };
}

impl TypeState {
    #[trace_typechecker]
    #[tracing::instrument(level = "trace", skip_all)]
    pub fn visit_identifier(&mut self, expression: &Loc<Expression>, ctx: &Context) -> Result<()> {
        assuming_kind!(ExprKind::Identifier(ident) = &expression => {
            // Add an equation for the anonymous id
            self.unify_expression_generic_error(
                expression,
                &TypedExpression::Name(ident.clone()),
                ctx
            )?;
        });
        Ok(())
    }

    #[trace_typechecker]
    #[tracing::instrument(level = "trace", skip_all)]
    pub fn visit_type_level_integer(
        &mut self,
        expression: &Loc<Expression>,
        generic_list: &GenericListToken,
        ctx: &Context,
    ) -> Result<()> {
        assuming_kind!(ExprKind::TypeLevelInteger(value) = &expression => {
            let (t, _size) = self.new_generic_number(expression.loc(), ctx);
            self.unify(&t, &expression.inner, ctx)
                .into_diagnostic(expression.loc(), |diag, Tm{e: _, g: _got}| {
                    diag
                        .level(DiagnosticLevel::Bug)
                        .message("Failed to unify integer literal with integer")
                })?;
            let generic = self.get_generic_list(generic_list).get(value).ok_or_else(|| {
                Diagnostic::bug(expression, "Found no generic list when visiting {value}")
            })?;
            self.add_requirement(
                Requirement::FitsIntLiteral {
                    value: ConstantInt::Generic(generic.clone()),
                    target_type: t.at_loc(expression)
                }
            )
        });
        Ok(())
    }

    #[tracing::instrument(level = "trace", skip_all)]
    pub fn visit_pipeline_ref(
        &mut self,
        expression: &Loc<Expression>,
        generic_list: &GenericListToken,
        ctx: &Context,
    ) -> Result<()> {
        assuming_kind!(ExprKind::PipelineRef{stage, name, declares_name, depth_typeexpr_id} = &expression => {
            // If this reference declares the referenced name, add a new equation
            if *declares_name {
                let new_var = self.new_generic_type(expression.loc());
                self.add_equation(TypedExpression::Name(name.clone().inner), new_var)
            }

            let depth = self.new_generic_tlint(stage.loc());
            self.add_equation(TypedExpression::Id(*depth_typeexpr_id), depth.clone());
            let depth = match &stage.inner {
                spade_hir::expression::PipelineRefKind::Absolute(name) => {
                    let key = TypedExpression::Name(name.inner.clone());
                    let var = if !self.equations.contains_key(&key) {
                        let var = self.new_generic_tlint(stage.loc());
                        self.add_equation(key.clone(), var.clone());
                        self.trace_stack.push(TraceStackEntry::PreAddingPipelineLabel(name.inner.clone(), var.clone()));
                        var
                    } else {
                        let var = self.equations.get(&key).unwrap().clone();
                        self.trace_stack.push(TraceStackEntry::RecoveringPipelineLabel(name.inner.clone(), var.clone()));
                        var
                    };
                    // NOTE: Safe unwrap, depth is fresh
                    self.unify(&depth, &var, ctx).unwrap()
                },
                spade_hir::expression::PipelineRefKind::Relative(expr) => {
                    let expr_var = self.hir_type_expr_to_var(expr, generic_list)?;
                    let total_offset = self.new_generic_tlint(stage.loc());
                    self.add_constraint(
                        total_offset.clone(),
                        ConstraintExpr::Sum(
                            Box::new(ConstraintExpr::Var(expr_var)),
                            Box::new(ConstraintExpr::Var(self.get_pipeline_state(expression)?
                                .current_stage_depth.clone()))
                        ),
                        stage.loc(),
                        &total_offset,
                        ConstraintSource::PipelineRegOffset{reg: expr.loc(), total: self.get_pipeline_state(expr)?.total_depth.loc()}
                    );
                    // Safe unwrap, depth is a fresh type var
                    self.unify(&depth, &total_offset, ctx).unwrap()
                },
            };

            let pipeline_state = self.pipeline_state
                .as_ref()
                .ok_or_else(|| diag_anyhow!(
                    expression,
                    "Expected a pipeline state"
                ))?;
            self.add_requirement(Requirement::ValidPipelineOffset {
                definition_depth: pipeline_state
                    .total_depth
                    .clone(),
                current_stage: pipeline_state.current_stage_depth.clone().nowhere(),
                reference_offset: depth.at_loc(stage)
            });

            // Add an equation for the anonymous id
            self.unify_expression_generic_error(
                expression,
                &TypedExpression::Name(name.clone().inner),
                ctx
            )?;
        });
        Ok(())
    }

    #[trace_typechecker]
    #[tracing::instrument(level = "trace", skip_all)]
    pub fn visit_int_literal(&mut self, expression: &Loc<Expression>, ctx: &Context) -> Result<()> {
        assuming_kind!(ExprKind::IntLiteral(value, kind) = &expression => {
            let (t, _size) = match kind {
                IntLiteralKind::Unsized => self.new_generic_number(expression.loc(), ctx),
                IntLiteralKind::Signed(size) => {
                    let (t, size_var) = self.new_split_generic_int(expression.loc(), ctx.symtab);
                    // NOTE: Safe unwrap, we're unifying a generic int with a size
                    self.unify(&size_var, &KnownType::Integer(size.to_bigint()).at_loc(expression), ctx).unwrap();
                    (t, size_var)
                },
                IntLiteralKind::Unsigned(size) => {
                    let (t, size_var) = self.new_split_generic_uint(expression.loc(), ctx.symtab);
                    // NOTE: Safe unwrap, we're unifying a generic int with a size
                    self.unify(&size_var, &KnownType::Integer(size.to_bigint()).at_loc(expression), ctx).unwrap();
                    (t, size_var)
                }
            };
            self.unify(&t, &expression.inner, ctx)
                .into_diagnostic(expression.loc(), |diag, Tm{e: _, g: _got}| {
                    diag
                        .level(DiagnosticLevel::Bug)
                        .message("Failed to unify integer literal with integer")
                })?;
            self.add_requirement(Requirement::FitsIntLiteral {
                value: ConstantInt::Literal(value.clone()),
                target_type: t.at_loc(expression)
            });
        });
        Ok(())
    }

    #[trace_typechecker]
    #[tracing::instrument(level = "trace", skip_all)]
    pub fn visit_bool_literal(
        &mut self,
        expression: &Loc<Expression>,
        ctx: &Context,
    ) -> Result<()> {
        assuming_kind!(ExprKind::BoolLiteral(_) = &expression => {
            self.unify_expression_generic_error(expression, &t_bool(ctx.symtab).at_loc(expression), ctx)?;
        });
        Ok(())
    }

    #[trace_typechecker]
    #[tracing::instrument(level = "trace", skip_all)]
    pub fn visit_bit_literal(&mut self, expression: &Loc<Expression>, ctx: &Context) -> Result<()> {
        assuming_kind!(ExprKind::BitLiteral(_) = &expression => {
            self.unify_expression_generic_error(expression, &t_bit(ctx.symtab).at_loc(expression), ctx)?;
        });
        Ok(())
    }

    #[trace_typechecker]
    #[tracing::instrument(level = "trace", skip_all)]
    pub fn visit_tuple_literal(
        &mut self,
        expression: &Loc<Expression>,
        ctx: &Context,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        assuming_kind!(ExprKind::TupleLiteral(inner) = &expression => {
            for expr in inner {
                self.visit_expression(expr, ctx, generic_list)?;
                // NOTE: safe unwrap, we know this expr has a type because we just visited
            }

            let mut inner_types = vec![];
            for expr in inner {
                let t = self.type_of(&TypedExpression::Id(expr.id)).unwrap();

                inner_types.push(t);
            }

            self.unify_expression_generic_error(
                expression,
                &TypeVar::Known(expression.loc(), KnownType::Tuple, inner_types),
                ctx
            )?;
        });
        Ok(())
    }

    #[trace_typechecker]
    #[tracing::instrument(level = "trace", skip_all)]
    pub fn visit_tuple_index(
        &mut self,
        expression: &Loc<Expression>,
        ctx: &Context,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        assuming_kind!(ExprKind::TupleIndex(tup, index) = &expression => {
            self.visit_expression(tup, ctx, generic_list)?;
            let t = self.type_of(&TypedExpression::Id(tup.id))?;

            let inner_types = match t {
                TypeVar::Known(_, KnownType::Tuple, inner) => inner,
                ref t @ TypeVar::Known(ref other_source, _, _) => {
                    return Err(Diagnostic::error(tup.loc(), "Attempt to use tuple indexing on non-tuple")
                        .primary_label(format!("expected tuple, got {t}"))
                        .secondary_label(index, "Because this is a tuple index")
                        .secondary_label(other_source, format!("Type {t} inferred here"))
                    );
                }
                TypeVar::Unknown(_, _, _, MetaType::Type | MetaType::Any) => {
                    return Err(
                        Diagnostic::error(tup.as_ref(), "Type of tuple indexee must be known at this point")
                            .primary_label("The type of this must be known")
                    )
                }
                TypeVar::Unknown(ref other_source, _, _, meta @ (MetaType::Uint | MetaType::Int | MetaType::Number | MetaType::Bool)) => {
                    return Err(
                        Diagnostic::error(tup.as_ref(), "Cannot use tuple indexing on a type level number")
                            .primary_label("Tuple indexing on type level number")
                        .secondary_label(other_source, format!("Meta-type {meta} inferred here"))
                    )
                }
            };

            if (index.inner as usize) < inner_types.len() {
                let true_inner_type = inner_types[index.inner as usize].clone();
                self.unify_expression_generic_error(
                    expression,
                    &true_inner_type,
                    ctx
                )?
            } else {
                return Err(Diagnostic::error(index, "Tuple index out of bounds")
                    .primary_label(format!("Tuple only has {} elements", inner_types.len()))
                    .note(format!("     Index: {}", index))
                    .note(format!("Tuple size: {}", inner_types.len()))
                );
            }
        });
        Ok(())
    }

    #[trace_typechecker]
    #[tracing::instrument(level = "trace", skip_all)]
    pub fn visit_field_access(
        &mut self,
        expression: &Loc<Expression>,
        ctx: &Context,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        assuming_kind!(ExprKind::FieldAccess(target, field) = &expression => {
            self.visit_expression(target, ctx, generic_list)?;

            let target_type = self.type_of(&TypedExpression::Id(target.id))?;
            let self_type = self.type_of(&TypedExpression::Id(expression.id))?;

            let requirement = Requirement::HasField {
                target_type: target_type.at_loc(target),
                field: field.clone(),
                expr: self_type.at_loc(expression)
            };

            requirement.check_or_add(self, ctx)?;
        });
        Ok(())
    }

    #[trace_typechecker]
    #[tracing::instrument(level = "trace", skip_all)]
    pub fn visit_method_call(
        &mut self,
        expression: &Loc<Expression>,
        ctx: &Context,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        assuming_kind!(ExprKind::MethodCall{call_kind, target, name, args, turbofish} = &expression => {
            // NOTE: We don't visit_expression here as it is being added to the argument_list
            // which we *do* visit
            // self.visit_expression(target, ctx, generic_list)?;

            let args_with_self = args.clone().map(|mut args| {
                match &mut args {
                    spade_hir::ArgumentList::Named(inner) => {
                        inner.push(NamedArgument::Full(
                            Identifier("self".to_string()).at_loc(target),
                            target.as_ref().clone()
                        ))
                    },
                    spade_hir::ArgumentList::Positional(list) => list.insert(0, target.as_ref().clone()),
                };
                args
            });

            self.visit_argument_list(&args_with_self, ctx, generic_list)?;

            let target_type = self.type_of(&TypedExpression::Id(target.id))?;
            let self_type = self.type_of(&TypedExpression::Id(expression.id))?;

            let trait_list = if let TypeVar::Unknown(_, _, trait_list, MetaType::Type) = &target_type {
                if !trait_list.inner.is_empty() {
                    Some(trait_list.clone())
                } else {
                    None
                }
            } else {
                None
            };

            let requirement = Requirement::HasMethod {
                expr_id: expression.map_ref(|e| e.id),
                target_type: target_type.at_loc(target),
                trait_list,
                method: name.clone(),
                expr: self_type.at_loc(expression),
                args: args_with_self,
                turbofish: turbofish.clone(),
                prev_generic_list: generic_list.clone(),
                call_kind: call_kind.clone()
            };

            requirement.check_or_add(self, ctx)?
        });
        Ok(())
    }

    #[trace_typechecker]
    #[tracing::instrument(level = "trace", skip_all)]
    pub fn visit_array_literal(
        &mut self,
        expression: &Loc<Expression>,
        ctx: &Context,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        assuming_kind!(ExprKind::ArrayLiteral(members) = &expression => {
            for expr in members {
                self.visit_expression(expr, ctx, generic_list)?;
            }

            // unify all elements in array pairwise, e.g. unify(0, 1), unify(1, 2), ...
            for (l, r) in members.iter().zip(members.iter().skip(1)) {
                self.unify(r, l, ctx)
                    .into_diagnostic(r, |diag, Tm{e: expected, g: _got}| {
                        diag.message(format!(
                            "Array element type mismatch. Expected {}",
                            expected
                        ))
                        .primary_label(format!("Expected {}", expected))
                        .secondary_label(members.first().unwrap().loc(), "To match this".to_string())
                    })?;
            }

            let inner_type = if members.is_empty() {
                self.new_generic_type(expression.loc())
            }
            else {
                members[0].get_type(self)?
            };

            let size_type = TypeVar::Known(expression.loc(), KnownType::Integer(members.len().to_bigint()), vec![]);
            let result_type = TypeVar::array(
                expression.loc(),
                inner_type,
                size_type,
            );

            self.unify_expression_generic_error(expression, &result_type, ctx)?;
        });
        Ok(())
    }

    pub fn visit_array_shorthand_literal(
        &mut self,
        expression: &Loc<Expression>,
        ctx: &Context,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        assuming_kind!(ExprKind::ArrayShorthandLiteral(expr, amount) = &expression => {
            self.visit_expression(expr, ctx, generic_list)?;


            let inner_type = expr.get_type(self)?;
            let size_type = self.visit_const_generic_with_id(amount, generic_list, ConstraintSource::ArraySize, ctx)?;
            // Force the type to be a uint
            let uint_type = self.new_generic_tluint(expression.loc());
            self.unify(&size_type, &uint_type, ctx).into_default_diagnostic(expression.loc())?;

            let result_type = TypeVar::array(expression.loc(), inner_type, size_type);

            self.unify_expression_generic_error(expression, &result_type, ctx)?;
        });
        Ok(())
    }

    #[trace_typechecker]
    #[tracing::instrument(level = "trace", skip_all)]
    pub fn visit_create_ports(
        &mut self,
        expression: &Loc<Expression>,
        ctx: &Context,
        _generic_list: &GenericListToken,
    ) -> Result<()> {
        assuming_kind!(ExprKind::CreatePorts = &expression => {
            let inner_type = self.new_generic_type(expression.loc());
            let inverted = TypeVar::Known(expression.loc(), KnownType::Inverted, vec![inner_type.clone()]);
            let compound = TypeVar::tuple(expression.loc(), vec![inner_type, inverted]);
            self.unify_expression_generic_error(expression, &compound, ctx)?;
        });
        Ok(())
    }

    #[trace_typechecker]
    #[tracing::instrument(level = "trace", skip_all)]
    pub fn visit_index(
        &mut self,
        expression: &Loc<Expression>,
        ctx: &Context,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        assuming_kind!(ExprKind::Index(target, index) = &expression => {
            // Visit child nodes
            self.visit_expression(target, ctx, generic_list)?;
            self.visit_expression(index, ctx, generic_list)?;

            // Add constraints
            let inner_type = self.new_generic_type(expression.loc());

            // Unify inner type with this expression
            self.unify_expression_generic_error(
                expression,
                &inner_type,
                ctx
            )?;

            let array_size = self.new_generic_tluint(expression.loc());
            let (int_type, int_size) = self.new_split_generic_uint(index.loc(), ctx.symtab);

            // NOTE[et]: Only used for size constraints of this exact type - this can be a
            // requirement instead, that way we remove a lot of complexity! :D
            self.add_constraint(
                int_size,
                bits_to_store(ce_var(&array_size) - ce_int(BigInt::one())),
                index.loc(),
                &int_type,
                ConstraintSource::ArrayIndexing
            );

            self.unify(&index.inner, &int_type, ctx)
                .into_diagnostic(index.as_ref(), |diag, Tm{e: _expected, g: got}| {

                    diag.message(format!("Index must be an integer, got {}", got))
                        .primary_label("Expected integer".to_string())
                })?;

            let array_type = TypeVar::array(
                expression.loc(),
                expression.get_type(self)?,
                array_size.clone()
            );
            self.add_requirement(Requirement::ArrayIndexeeIsNonZero {
                index: index.loc(),
                array: array_type.clone().at_loc(target),
                array_size: array_size.clone().at_loc(index)
            });
            self.unify(&target.inner, &array_type, ctx)
                .into_diagnostic(target.as_ref(), |diag, Tm{e: _expected, g: got}| {
                    diag
                        .message(format!("Index target must be an array, got {}", got))
                        .primary_label("Expected array".to_string())
                })?;
        });
        Ok(())
    }

    #[trace_typechecker]
    #[tracing::instrument(level = "trace", skip_all)]
    pub fn visit_range_index(
        &mut self,
        expression: &Loc<Expression>,
        ctx: &Context,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        assuming_kind!(ExprKind::RangeIndex{
            target,
            ref start,
            ref end,
        } = &expression => {
            self.visit_expression(target, ctx, generic_list)?;
            // Add constraints
            let inner_type = self.new_generic_type(target.loc());

            let start_var = self.visit_const_generic_with_id(start, generic_list, ConstraintSource::RangeIndex, ctx)?;
            let end_var = self.visit_const_generic_with_id(end, generic_list, ConstraintSource::RangeIndex, ctx)?;

            let in_array_size = self.new_generic_tluint(target.loc());
            let in_array_type = TypeVar::array(expression.loc(), inner_type.clone(), in_array_size.clone());
            let out_array_size = self.new_generic_tluint(target.loc());
            let out_array_type = TypeVar::array(expression.loc(), inner_type.clone(), out_array_size.clone());

            let out_size_constraint = ConstraintExpr::Var(end_var.clone()) - ConstraintExpr::Var(start_var.clone());
            self.add_constraint(out_array_size, out_size_constraint, expression.loc(), &out_array_type, ConstraintSource::RangeIndex);

            self.add_requirement(Requirement::RangeIndexEndAfterStart { expr: expression.loc(), start: start_var.clone().at_loc(&start), end: end_var.clone().at_loc(end) });
            self.add_requirement(Requirement::RangeIndexInArray { index: end_var.at_loc(end), size: in_array_size.at_loc(&target.loc()) });

            self.unify(&expression.inner, &out_array_type, ctx)
                .into_default_diagnostic(expression)?;


            self.unify(&target.inner, &in_array_type, ctx)
                .into_diagnostic(target.as_ref(), |diag, Tm{e: _expected, g: got}| {
                    diag
                        .message(format!("Index target must be an array, got {}", got))
                        .primary_label("Expected array".to_string())
                })?;
        });
        Ok(())
    }

    #[trace_typechecker]
    #[tracing::instrument(level = "trace", skip_all)]
    pub fn visit_block_expr(
        &mut self,
        expression: &Loc<Expression>,
        ctx: &Context,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        assuming_kind!(ExprKind::Block(block) = expression => {
            self.visit_block(block, ctx, generic_list)?;

            if let Some(result) = &block.result {
                // Unify the return type of the block with the type of this expression
                self.unify(&expression.inner, &result.inner, ctx)
                    // NOTE: We could be more specific about this error specifying
                    // that the type of the block must match the return type, though
                    // that might just be spammy.
                    .into_default_diagnostic(result)?;
            } else {
                // Block without return value. Unify with void type.
                self.unify(&expression.inner, &t_void(ctx.symtab).at_loc(expression), ctx)
                    .into_diagnostic(Loc::nowhere(()), |err, Tm{g: _, e: _}| {
                        diag_anyhow!(
                            Loc::nowhere(()),
                            "This error shouldn't be possible: {err:?}"
                        )})?;
            }
        });
        Ok(())
    }

    #[trace_typechecker]
    #[tracing::instrument(level = "trace", skip_all)]
    pub fn visit_if(
        &mut self,
        expression: &Loc<Expression>,
        ctx: &Context,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        assuming_kind!(ExprKind::If(cond, on_true, on_false) = &expression => {
            self.visit_expression(cond, ctx, generic_list)?;
            self.visit_expression(on_true, ctx, generic_list)?;
            self.visit_expression(on_false, ctx, generic_list)?;

            self.unify(&cond.inner, &t_bool(ctx.symtab).at_loc(cond), ctx)
                .into_diagnostic(cond.as_ref(), |diag, Tm{e: _expected, g: got}| {
                    diag.
                        message(format!("If condition must be a bool, got {}", got))
                        .primary_label("Expected boolean")
                })?;
            self.unify(&on_false.inner, &on_true.inner, ctx)
                .into_diagnostic(on_false.as_ref(), |diag, Tm{e: expected, g: got}| {
                    diag.message("If branches have incompatible type")
                        .primary_label(format!("But this has type {got}"))
                        .secondary_label(on_true.as_ref(), format!("This branch has type {expected}"))
                })?;
            self.unify(expression, &on_false.inner, ctx)
                .into_default_diagnostic(expression)?;
        });
        Ok(())
    }

    #[trace_typechecker]
    #[tracing::instrument(level = "trace", skip_all)]
    pub fn visit_match(
        &mut self,
        expression: &Loc<Expression>,
        ctx: &Context,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        assuming_kind!(ExprKind::Match(cond, branches) = &expression => {
            self.visit_expression(cond, ctx, generic_list)?;

            for (i, (pattern, result)) in branches.iter().enumerate() {
                self.visit_pattern(pattern, ctx, generic_list)?;

                self.unify(pattern, &cond.inner, ctx)
                    .into_default_diagnostic(pattern)?;

                self.visit_expression(result, ctx, generic_list)?;

                if i != 0 {
                    self.unify(&branches[0].1, result, ctx).into_diagnostic(
                        result,
                        |diag, Tm{e: expected, g: got}| {
                            diag.message("Match branches have incompatible type")
                                .primary_label(format!("This branch has type {got}"))
                                .secondary_label(&branches[0].1, format!("But this one has type {expected}"))
                        }
                    )?;
                }
            }

            assert!(
                !branches.is_empty(),
                "Empty match statements should be checked by ast lowering"
            );

            self.unify_expression_generic_error(&branches[0].1, expression, ctx)?;
        });
        Ok(())
    }

    #[trace_typechecker]
    #[tracing::instrument(level = "trace", skip_all)]
    pub fn visit_binary_operator(
        &mut self,
        expression: &Loc<Expression>,
        ctx: &Context,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        assuming_kind!(ExprKind::BinaryOperator(lhs, op, rhs) = &expression => {
            self.visit_expression(lhs, ctx, generic_list)?;
            self.visit_expression(rhs, ctx, generic_list)?;
            match op.inner {
                BinaryOperator::Add
                | BinaryOperator::Sub | BinaryOperator::Mul if self.use_wordlenght_inference => {
                    let lhs_t = self.new_generic_int(expression.loc(), ctx.symtab);
                    self.unify_expression_generic_error(lhs, &lhs_t, ctx)?;
                    let rhs_t = self.new_generic_int(expression.loc(), ctx.symtab);
                    self.unify_expression_generic_error(rhs, &rhs_t, ctx)?;
                    let result_t = self.new_generic_int(expression.loc(), ctx.symtab);
                    self.unify_expression_generic_error(expression, &result_t, ctx)?;
                }
                BinaryOperator::Add
                | BinaryOperator::Sub => {
                    let (in_t, lhs_size) = self.new_generic_number(expression.loc(), ctx);
                    let (result_t, result_size) = self.new_generic_number(expression.loc(), ctx);

                    self.add_constraint(
                        result_size.clone(),
                        ce_var(&lhs_size) + ce_int(BigInt::one()),
                        expression.loc(),
                        &result_t,
                        ConstraintSource::AdditionOutput
                    );
                    self.add_constraint(
                        lhs_size.clone(),
                        ce_var(&result_size) + -ce_int(BigInt::one()),
                        lhs.loc(),
                        &in_t,
                        ConstraintSource::AdditionOutput
                    );

                    self.unify_expression_generic_error(lhs, &in_t, ctx)?;
                    self.unify_expression_generic_error(lhs, &rhs.inner, ctx)?;
                    self.unify_expression_generic_error(expression, &result_t, ctx)?;

                    self.add_requirement(Requirement::SharedBase(vec![
                        in_t.at_loc(lhs),
                        result_t.at_loc(expression)
                    ]));

                }
                BinaryOperator::Mul => {
                    let (lhs_t, lhs_size) = self.new_generic_number(expression.loc(), ctx);
                    let (rhs_t, rhs_size) = self.new_generic_number(expression.loc(), ctx);
                    let (result_t, result_size) = self.new_generic_number(expression.loc(), ctx);

                    // Result size is sum of input sizes
                    self.add_constraint(
                        result_size.clone(),
                        ce_var(&lhs_size) + ce_var(&rhs_size),
                        expression.loc(),
                        &result_t,
                        ConstraintSource::MultOutput
                    );
                    self.add_constraint(
                        lhs_size.clone(),
                        ce_var(&result_size) + -ce_var(&rhs_size),
                        lhs.loc(),
                        &lhs_t,
                        ConstraintSource::MultOutput
                    );
                    self.add_constraint(rhs_size.clone(),
                        ce_var(&result_size) + -ce_var(&lhs_size),
                        rhs.loc(),
                        &rhs_t
                        , ConstraintSource::MultOutput
                    );

                    self.unify_expression_generic_error(lhs, &lhs_t, ctx)?;
                    self.unify_expression_generic_error(rhs, &rhs_t, ctx)?;
                    self.unify_expression_generic_error(expression, &result_t, ctx)?;

                    self.add_requirement(Requirement::SharedBase(vec![
                        lhs_t.at_loc(lhs),
                        rhs_t.at_loc(rhs),
                        result_t.at_loc(expression)
                    ]));
                }
                // Division, being integer division has the same width out as in
                BinaryOperator::Div | BinaryOperator::Mod => {
                    let (int_type, _size) = self.new_generic_number(expression.loc(), ctx);

                    self.unify_expression_generic_error(lhs, &int_type, ctx)?;
                    self.unify_expression_generic_error(lhs, &rhs.inner, ctx)?;
                    self.unify_expression_generic_error(expression, &rhs.inner, ctx)?;
                },
                // Shift operators have the same width in as they do out
                BinaryOperator::LeftShift
                | BinaryOperator::BitwiseAnd
                | BinaryOperator::BitwiseXor
                | BinaryOperator::BitwiseOr
                | BinaryOperator::ArithmeticRightShift
                | BinaryOperator::RightShift => {
                    let (int_type, _size) = self.new_generic_number(expression.loc(), ctx);

                    // FIXME: Make generic over types that can be bitmanipulated
                    self.unify_expression_generic_error(lhs, &int_type, ctx)?;
                    self.unify_expression_generic_error(lhs, &rhs.inner, ctx)?;
                    self.unify_expression_generic_error(expression, &rhs.inner, ctx)?;
                }
                BinaryOperator::Eq
                | BinaryOperator::NotEq
                | BinaryOperator::Gt
                | BinaryOperator::Lt
                | BinaryOperator::Ge
                | BinaryOperator::Le => {
                    let (base, _size) = self.new_generic_number(expression.loc(), ctx);
                    // FIXME: Make generic over types that can be compared
                    self.unify_expression_generic_error(lhs, &base, ctx)?;
                    self.unify_expression_generic_error(lhs, &rhs.inner, ctx)?;
                    self.unify_expression_generic_error(expression, &t_bool(ctx.symtab).at_loc(expression), ctx)?;
                }
                BinaryOperator::LogicalAnd
                | BinaryOperator::LogicalOr
                | BinaryOperator::LogicalXor => {
                    self.unify_expression_generic_error(lhs, &t_bool(ctx.symtab).at_loc(expression), ctx)?;
                    self.unify_expression_generic_error(lhs, &rhs.inner, ctx)?;

                    self.unify_expression_generic_error(expression, &t_bool(ctx.symtab).at_loc(expression), ctx)?;
                }
            }
        });
        Ok(())
    }

    #[trace_typechecker]
    #[tracing::instrument(level = "trace", skip_all)]
    pub fn visit_unary_operator(
        &mut self,
        expression: &Loc<Expression>,
        ctx: &Context,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        assuming_kind!(ExprKind::UnaryOperator(op, operand) = &expression => {
            self.visit_expression(operand, ctx, generic_list)?;
            match &op.inner {
                UnaryOperator::Sub => {
                    let int_type = self.new_generic_int(expression.loc(), ctx.symtab);
                    self.unify_expression_generic_error(operand, &int_type, ctx)?;
                    self.unify_expression_generic_error(expression, &int_type, ctx)?
                }
                UnaryOperator::BitwiseNot => {
                    let (number_type, _) = self.new_generic_number(expression.loc(), ctx);
                    self.unify_expression_generic_error(operand, &number_type, ctx)?;
                    self.unify_expression_generic_error(expression, &number_type, ctx)?
                }
                UnaryOperator::Not => {
                    self.unify_expression_generic_error(operand, &t_bool(ctx.symtab).at_loc(expression), ctx)?;
                    self.unify_expression_generic_error(expression, &t_bool(ctx.symtab).at_loc(expression), ctx)?
                }
                UnaryOperator::Dereference => {
                    let result_type = self.new_generic_type(expression.loc());
                    let reference_type = TypeVar::wire(expression.loc(), result_type.clone());
                    self.unify_expression_generic_error(operand, &reference_type, ctx)?;
                    self.unify_expression_generic_error(expression, &result_type, ctx)?
                }
                UnaryOperator::Reference => {
                    let result_type = self.new_generic_type(expression.loc());
                    let reference_type = TypeVar::wire(expression.loc(), result_type.clone());
                    self.unify_expression_generic_error(operand, &result_type, ctx)?;
                    self.unify_expression_generic_error(expression, &reference_type, ctx)?
                }
            }
        });
        Ok(())
    }
}
