pub mod error;
pub mod error_reporting;
mod linear_check;
pub mod monomorphisation;
pub mod name_map;
pub mod passes;
mod pattern;
pub mod pipelines;
mod statement_list;
pub mod substitution;
mod usefulness;

use std::collections::HashMap;

use error::{expect_entity, expect_function, expect_pipeline};
use hir::expression::CallKind;
use hir::expression::LocExprExt;
use local_impl::local_impl;

use hir::param_util::{match_args_with_params, Argument};
use hir::symbol_table::{FrozenSymtab, PatternableKind};
use hir::{ItemList, Pattern, PatternArgument, UnitKind, UnitName};
use mir::types::Type as MirType;
use mir::{ConstantValue, ValueName};
use monomorphisation::MonoState;
pub use name_map::NameSourceMap;
use num::{BigUint, One, Zero};
use pattern::DeconstructedPattern;
use pipelines::lower_pipeline;
use spade_common::id_tracker::ExprIdTracker;
use spade_common::location_info::WithLocation;
use spade_common::name::{Identifier, Path};
use spade_diagnostics::{diag_assert, diag_bail, DiagHandler, Diagnostic};
use spade_typeinference::equation::TypeVar;
use spade_typeinference::equation::TypedExpression;
use spade_typeinference::GenericListToken;
use statement_list::StatementList;
use substitution::Substitutions;
use thiserror::Error;
use usefulness::{is_useful, PatStack, Usefulness};

use crate::error::{Error, Result};
use spade_common::{location_info::Loc, name::NameID};
use spade_hir as hir;
use spade_hir::{expression::BinaryOperator, ExprKind, Expression, Statement, Unit};
use spade_mir as mir;
use spade_typeinference::TypeState;
use spade_types::{ConcreteType, PrimitiveType};

pub trait Manglable {
    fn mangled(&self) -> String;
}
impl Manglable for NameID {
    fn mangled(&self) -> String {
        let str_name = self.1.as_strs().join("_");
        format!("{}_n{}", str_name, self.0)
    }
}

pub trait UnitNameExt {
    fn as_mir(&self) -> mir::UnitName;
}

impl UnitNameExt for UnitName {
    fn as_mir(&self) -> mir::UnitName {
        match self {
            UnitName::WithID(name) => mir::UnitName::Escaped {
                name: format!("{}[{}]", name.inner.1.as_strs().join("::"), name.inner.0),
                path: name.inner.1.as_strings(),
            },
            UnitName::FullPath(name) => mir::UnitName::Escaped {
                name: name.inner.1.as_strs().join("::"),
                path: name.inner.1.as_strings(),
            },
            UnitName::Unmangled(name, _) => mir::UnitName::Unescaped(name.clone()),
        }
    }
}

pub trait MirLowerable {
    fn to_mir_type(&self) -> mir::types::Type;
}

impl MirLowerable for ConcreteType {
    fn to_mir_type(&self) -> mir::types::Type {
        use mir::types::Type;
        use ConcreteType as CType;

        match self {
            CType::Tuple(inner) => {
                Type::Tuple(inner.iter().map(MirLowerable::to_mir_type).collect())
            }
            CType::Array { inner, size } => Type::Array {
                inner: Box::new(inner.to_mir_type()),
                length: size.clone(),
            },
            CType::Single {
                base: PrimitiveType::Bool,
                params: _,
            } => Type::Bool,
            CType::Single {
                base: PrimitiveType::Clock,
                params: _,
            } => Type::Bool,
            CType::Single {
                base: PrimitiveType::Int,
                params,
            } => match params.as_slice() {
                [CType::Integer(val)] => Type::Int(val.clone()),
                t => unreachable!("{:?} is an invalid generic parameter for an integer", t),
            },
            CType::Single {
                base: PrimitiveType::Uint,
                params,
            } => match params.as_slice() {
                [CType::Integer(val)] => Type::Int(val.clone()),
                t => unreachable!("{:?} is an invalid generic parameter for an integer", t),
            },
            CType::Single {
                base: PrimitiveType::Memory,
                params,
            } => match params.as_slice() {
                [inner, CType::Integer(length)] => Type::Memory {
                    inner: Box::new(inner.to_mir_type()),
                    length: length.clone(),
                },
                t => unreachable!("{:?} is an invalid generic parameter for a memory", t),
            },
            CType::Integer(_) => {
                unreachable!("Found an integer at the base level of a type")
            }
            CType::Enum { options } => {
                let inner = options
                    .iter()
                    .map(|o| o.1.iter().map(|t| t.1.to_mir_type()).collect())
                    .collect();
                Type::Enum(inner)
            }
            CType::Struct { name: _, members } => {
                let members = members.iter().map(|(_, t)| t.to_mir_type()).collect();
                Type::Tuple(members)
            }
            CType::Backward(inner) => Type::Backward(Box::new(inner.to_mir_type())),
            // At this point we no longer need to know if this is a Wire or not, it will
            // behave exactly as a normal type
            CType::Wire(inner) => inner.to_mir_type(),
        }
    }
}

pub trait NameIDExt {
    /// Return the corresponding MIR value name for this NameID
    fn value_name(&self) -> mir::ValueName;
}

impl NameIDExt for NameID {
    fn value_name(&self) -> mir::ValueName {
        let mangled = format!("{}", self.1.tail());
        mir::ValueName::Named(self.0, mangled)
    }
}

struct PatternCondition {
    pub statements: Vec<mir::Statement>,
    pub result_name: ValueName,
}

/// Returns a name which is `true` if all of `ops` are true, along with helper
/// statements required for that computation. If `ops` is empt, a single `true` constant
/// is returned
pub fn all_conditions(ops: Vec<ValueName>, ctx: &mut Context) -> (Vec<mir::Statement>, ValueName) {
    if ops.is_empty() {
        let id = ctx.idtracker.next();
        (
            vec![mir::Statement::Constant(
                id,
                MirType::Bool,
                ConstantValue::Bool(true),
            )],
            ValueName::Expr(id),
        )
    } else if ops.len() == 1 {
        (vec![], ops[0].clone())
    } else {
        let mut result_name = ops[0].clone();
        let mut statements = vec![];
        for op in &ops[1..] {
            let new_name = ValueName::Expr(ctx.idtracker.next());
            statements.push(mir::Statement::Binding(mir::Binding {
                name: new_name.clone(),
                operator: mir::Operator::LogicalAnd,
                operands: vec![result_name, op.clone()],
                ty: MirType::Bool,
                loc: None,
            }));
            result_name = new_name;
        }
        (statements, result_name)
    }
}

#[local_impl]
impl PatternLocal for Loc<Pattern> {
    /// Lower a pattern to its individual parts. Requires the `Pattern::id` to be
    /// present in the code before this
    /// self_name is the name of the operand which this pattern matches
    #[tracing::instrument(name = "Pattern::lower", level = "trace", skip(self, ctx))]
    fn lower(&self, self_name: ValueName, ctx: &mut Context) -> Result<StatementList> {
        let mut result = StatementList::new();
        match &self.kind {
            hir::PatternKind::Integer(_) => {}
            hir::PatternKind::Bool(_) => {}
            hir::PatternKind::Name { .. } => {}
            hir::PatternKind::Tuple(inner) => {
                let inner_types = if let mir::types::Type::Tuple(inner) = &ctx
                    .types
                    .type_of_id(self.id, ctx.symtab.symtab(), &ctx.item_list.types)
                    .to_mir_type()
                {
                    inner.clone()
                } else {
                    unreachable!("Tuple destructuring of non-tuple");
                };

                for (i, p) in inner.iter().enumerate() {
                    result.push_primary(
                        mir::Statement::Binding(mir::Binding {
                            name: p.value_name(),
                            operator: mir::Operator::IndexTuple(i as u64, inner_types.clone()),
                            operands: vec![self_name.clone()],
                            ty: ctx
                                .types
                                .type_of_id(p.id, ctx.symtab.symtab(), &ctx.item_list.types)
                                .to_mir_type(),
                            loc: None,
                        }),
                        p,
                    );

                    result.append(p.lower(p.value_name(), ctx)?)
                }
            }
            hir::PatternKind::Type(path, args) => {
                let patternable = ctx.symtab.symtab().patternable_type_by_id(path);
                match patternable.kind {
                    PatternableKind::Struct => {
                        let s = ctx.symtab.symtab().struct_by_id(path);

                        let inner_types = if let mir::types::Type::Tuple(inner) = &ctx
                            .types
                            .type_of_id(self.id, ctx.symtab.symtab(), &ctx.item_list.types)
                            .to_mir_type()
                        {
                            inner.clone()
                        } else {
                            unreachable!("Struct destructuring of non-tuple");
                        };

                        for PatternArgument {
                            target,
                            value,
                            kind: _,
                        } in args
                        {
                            let i = s.params.arg_index(target).unwrap();

                            result.push_primary(
                                mir::Statement::Binding(mir::Binding {
                                    name: value.value_name(),
                                    operator: mir::Operator::IndexTuple(
                                        i as u64,
                                        inner_types.clone(),
                                    ),
                                    operands: vec![self_name.clone()],
                                    ty: ctx
                                        .types
                                        .type_of_id(
                                            value.id,
                                            ctx.symtab.symtab(),
                                            &ctx.item_list.types,
                                        )
                                        .to_mir_type(),
                                    loc: None,
                                }),
                                value,
                            );

                            result.append(value.lower(value.value_name(), ctx)?)
                        }
                    }
                    PatternableKind::Enum => {
                        let enum_variant = ctx.symtab.symtab().enum_variant_by_id(path);
                        let self_type = ctx
                            .types
                            .type_of_id(self.id, ctx.symtab.symtab(), &ctx.item_list.types)
                            .to_mir_type();

                        for (i, p) in args.iter().enumerate() {
                            result.push_primary(
                                mir::Statement::Binding(mir::Binding {
                                    name: p.value.value_name(),
                                    operator: mir::Operator::EnumMember {
                                        variant: enum_variant.option,
                                        member_index: i,
                                        enum_type: self_type.clone(),
                                    },
                                    operands: vec![self_name.clone()],
                                    ty: ctx
                                        .types
                                        .type_of_id(
                                            p.value.id,
                                            ctx.symtab.symtab(),
                                            &ctx.item_list.types,
                                        )
                                        .to_mir_type(),
                                    loc: None,
                                }),
                                &p.value,
                            );

                            result.append(p.value.lower(p.value.value_name(), ctx)?)
                        }
                    }
                }
            }
        }

        Ok(result)
    }

    /// Returns MIR code for a condition that must hold for `expr` to satisfy
    /// this pattern.
    #[tracing::instrument(level = "trace", skip(self, ctx))]
    fn condition(&self, value_name: &ValueName, ctx: &mut Context) -> Result<PatternCondition> {
        let output_id = ctx.idtracker.next();
        let result_name = ValueName::Expr(output_id);
        match &self.kind {
            hir::PatternKind::Integer(val) => {
                let self_type =
                    ctx.types
                        .type_of_id(self.id, ctx.symtab.symtab(), &ctx.item_list.types);
                let const_id = ctx.idtracker.next();
                let statements = vec![
                    mir::Statement::Constant(
                        const_id,
                        self_type.to_mir_type(),
                        ConstantValue::Int(val.clone()),
                    ),
                    mir::Statement::Binding(mir::Binding {
                        name: result_name.clone(),
                        ty: MirType::Bool,
                        operator: mir::Operator::Eq,
                        operands: vec![value_name.clone(), ValueName::Expr(const_id)],
                        loc: None,
                    }),
                ];

                Ok(PatternCondition {
                    statements,
                    result_name,
                })
            }
            hir::PatternKind::Bool(true) => Ok(PatternCondition {
                statements: vec![],
                result_name: value_name.clone(),
            }),
            hir::PatternKind::Bool(false) => {
                let statements = vec![mir::Statement::Binding(mir::Binding {
                    name: result_name.clone(),
                    ty: MirType::Bool,
                    operator: mir::Operator::LogicalNot,
                    operands: vec![value_name.clone()],
                    loc: None,
                })];

                Ok(PatternCondition {
                    statements,
                    result_name,
                })
            }
            hir::PatternKind::Name { .. } => Ok(PatternCondition {
                statements: vec![mir::Statement::Constant(
                    output_id,
                    MirType::Bool,
                    mir::ConstantValue::Bool(true),
                )],
                result_name,
            }),
            hir::PatternKind::Tuple(branches) => {
                assert!(
                    !branches.is_empty(),
                    "Tuple patterns without any subpatterns are unsupported"
                );

                let subpatterns = branches
                    .iter()
                    .map(|pat| pat.condition(&pat.value_name(), ctx))
                    .collect::<Result<Vec<_>>>()?;

                let conditions = subpatterns
                    .iter()
                    .map(|sub| sub.result_name.clone())
                    .collect::<Vec<_>>();

                let mut statements = subpatterns
                    .into_iter()
                    .flat_map(|sub| sub.statements.into_iter())
                    .collect::<Vec<_>>();

                let (mut new_statements, result_name) = all_conditions(conditions, ctx);
                statements.append(&mut new_statements);

                Ok(PatternCondition {
                    statements,
                    result_name,
                })
            }
            hir::PatternKind::Type(path, args) => {
                let patternable = ctx.symtab.symtab().patternable_type_by_id(path);

                let self_type = ctx
                    .types
                    .type_of_id(self.id, ctx.symtab.symtab(), &ctx.item_list.types)
                    .to_mir_type();

                let self_condition_id = ctx.idtracker.next();
                let self_condition_name = ValueName::Expr(self_condition_id);
                let self_condition = match patternable.kind {
                    PatternableKind::Enum => {
                        let enum_variant = ctx.symtab.symtab().enum_variant_by_id(path);

                        mir::Statement::Binding(mir::Binding {
                            name: self_condition_name.clone(),
                            operator: mir::Operator::IsEnumVariant {
                                variant: enum_variant.option,
                                enum_type: self_type,
                            },
                            operands: vec![value_name.clone()],
                            ty: MirType::Bool,
                            loc: None,
                        })
                    }
                    PatternableKind::Struct => mir::Statement::Constant(
                        self_condition_id,
                        MirType::Bool,
                        ConstantValue::Bool(true),
                    ),
                };

                // let enum_variant = ctx.symtab.symtab().enum_variant_by_id(path);

                let mut conditions = vec![self_condition_name];
                let mut cond_statements = vec![];
                cond_statements.push(self_condition);
                for p in args.iter() {
                    // NOTE: We know that `lower` will generate a binding for this
                    // argument with the specified value_name, so we can just use that
                    let value_name = p.value.value_name();

                    let mut cond = p.value.condition(&value_name, ctx)?;
                    conditions.push(cond.result_name.clone());
                    cond_statements.append(&mut cond.statements);
                }

                let (mut extra_statements, result_name) = all_conditions(conditions, ctx);
                cond_statements.append(&mut extra_statements);

                Ok(PatternCondition {
                    statements: cond_statements,
                    result_name,
                })
            }
        }
    }

    /// Get the name which the whole pattern should be bound. In practice,
    /// this will be the pattern ID unless the pattern is just a name, in
    /// which case it will be a name
    ///
    /// This is done to avoid creating too many unnecessary ExprID variables
    /// in the output code to make it more readable
    fn value_name(&self) -> ValueName {
        match &self.kind {
            hir::PatternKind::Name {
                name,
                pre_declared: _,
            } => return name.value_name(),
            hir::PatternKind::Integer(_) => {}
            hir::PatternKind::Bool(_) => {}
            hir::PatternKind::Tuple(_) => {}
            hir::PatternKind::Type(_, _) => {}
        }
        ValueName::Expr(self.id)
    }

    /// Return true if this pattern is just an alias for another name. If this is not
    /// the case, an alias from its true name to `value_name` must be generated
    fn is_alias(&self) -> bool {
        match self.kind {
            hir::PatternKind::Name { .. } => true,
            hir::PatternKind::Integer(_) => false,
            hir::PatternKind::Bool(_) => false,
            hir::PatternKind::Tuple(_) => false,
            hir::PatternKind::Type(_, _) => false,
        }
    }

    /// Returns an error if the pattern is refutable, i.e. it does not match all possible
    /// values it binds to
    #[tracing::instrument(level = "trace", skip(self, ctx))]
    fn is_refutable(&self, ctx: &Context) -> Usefulness {
        let operand_ty = ctx
            .types
            .type_of_id(self.id, ctx.symtab.symtab(), &ctx.item_list.types);

        let pat_stacks = vec![PatStack::new(vec![DeconstructedPattern::from_hir(
            self, ctx,
        )])];

        // The patterns which make a wildcard useful are the ones that are missing
        // from the match statement
        is_useful(
            &PatStack::new(vec![DeconstructedPattern::wildcard(&operand_ty)]),
            &usefulness::Matrix::new(&pat_stacks),
        )
    }
}

#[local_impl]
impl StatementLocal for Statement {
    #[tracing::instrument(name = "Statement::lower", level = "trace", skip(self, ctx))]
    fn lower(&self, ctx: &mut Context) -> Result<StatementList> {
        let mut result = StatementList::new();
        match self {
            Statement::Binding(pattern, _t, value) => {
                result.append(value.lower(ctx)?);

                let refutability = pattern.is_refutable(ctx);
                if refutability.is_useful() {
                    return Err(Error::RefutablePattern {
                        pattern: pattern.loc(),
                        witnesses: refutability.witnesses,
                        binding_kind: "let",
                    });
                }

                result.push_primary(
                    mir::Statement::Binding(mir::Binding {
                        name: pattern.value_name(),
                        operator: mir::Operator::Alias,
                        operands: vec![value.variable(ctx.subs)?],
                        ty: ctx
                            .types
                            .type_of_id(pattern.id, ctx.symtab.symtab(), &ctx.item_list.types)
                            .to_mir_type(),
                        loc: Some(pattern.loc()),
                    }),
                    pattern,
                );
                result.append(pattern.lower(value.variable(ctx.subs)?, ctx)?);
            }
            Statement::Register(register) => {
                result.append(register.clock.lower(ctx)?);

                if let Some((trig, value)) = &register.reset {
                    result.append(trig.lower(ctx)?);
                    result.append(value.lower(ctx)?);
                }

                result.append(register.value.lower(ctx)?);

                let refutability = register.pattern.is_refutable(ctx);
                if refutability.is_useful() {
                    return Err(Error::RefutablePattern {
                        pattern: register.pattern.loc(),
                        witnesses: refutability.witnesses,
                        binding_kind: "reg",
                    });
                }

                let ty = ctx.types.type_of_id(
                    register.pattern.id,
                    ctx.symtab.symtab(),
                    &ctx.item_list.types,
                );

                if ty.is_port() {
                    return Err(Error::PortInRegister {
                        loc: register.value.loc(),
                        ty,
                    });
                }

                result.push_primary(
                    mir::Statement::Register(mir::Register {
                        name: register.pattern.value_name(),
                        ty: ctx
                            .types
                            .type_of_id(
                                register.pattern.id,
                                ctx.symtab.symtab(),
                                &ctx.item_list.types,
                            )
                            .to_mir_type(),
                        clock: register.clock.variable(ctx.subs)?,
                        reset: register
                            .reset
                            .as_ref()
                            .map::<Result<_>, _>(|(value, trig)| {
                                Ok((value.variable(ctx.subs)?, trig.variable(ctx.subs)?))
                            })
                            .transpose()?,
                        value: register.value.variable(ctx.subs)?,
                        loc: Some(register.pattern.loc()),
                    }),
                    &register.pattern,
                );

                result.append(register.pattern.lower(register.pattern.value_name(), ctx)?);
            }
            Statement::Declaration(_) => {}
            Statement::PipelineRegMarker => {
                ctx.subs.current_stage += 1;
            }
            Statement::Label(_) => {}
            Statement::Assert(expr) => {
                result.append(expr.lower(ctx)?);
                result.push_anonymous(mir::Statement::Assert(
                    expr.variable(ctx.subs)?.at_loc(expr),
                ))
            }
            Statement::Set { target, value } => {
                result.append(target.lower(ctx)?);
                result.append(value.lower(ctx)?);
                result.push_anonymous(mir::Statement::Set {
                    target: target.variable(ctx.subs)?.at_loc(target),
                    value: value.variable(ctx.subs)?.at_loc(value),
                })
            }
        }
        Ok(result)
    }
}

pub fn expr_to_mir(expr: Loc<Expression>, ctx: &mut Context) -> Result<StatementList> {
    expr.lower(ctx)
}

#[local_impl]
impl ExprLocal for Loc<Expression> {
    /// If the verilog code for this expression is just an alias for another variable
    /// that is returned here. This allows us to skip generating wires that we don't
    /// really need
    fn alias(&self, subs: &Substitutions) -> Result<Option<mir::ValueName>> {
        match &self.kind {
            ExprKind::Identifier(ident) => match subs.lookup(ident) {
                substitution::Substitution::Undefined => Err(Error::UndefinedVariable {
                    name: ident.clone().at_loc(self),
                }),
                substitution::Substitution::Waiting(available_in, name) => {
                    Err(Error::UseBeforeReady {
                        name: name.at_loc(self),
                        referenced_at_stage: subs.current_stage,
                        unavailable_for: available_in,
                    })
                }
                substitution::Substitution::Available(current) => Ok(Some(current.value_name())),
                substitution::Substitution::Port => Ok(Some(ident.value_name())),
            },
            ExprKind::IntLiteral(_) => Ok(None),
            ExprKind::BoolLiteral(_) => Ok(None),
            ExprKind::TupleLiteral(_) => Ok(None),
            ExprKind::TupleIndex(_, _) => Ok(None),
            ExprKind::FieldAccess(_, _) => Ok(None),
            ExprKind::CreatePorts => Ok(None),
            ExprKind::ArrayLiteral { .. } => Ok(None),
            ExprKind::Index(_, _) => Ok(None),
            ExprKind::Block(block) => block.result.variable(subs).map(Some),
            ExprKind::If(_, _, _) => Ok(None),
            ExprKind::Match(_, _) => Ok(None),
            ExprKind::BinaryOperator(_, _, _) => Ok(None),
            ExprKind::UnaryOperator(_, _) => Ok(None),
            ExprKind::PipelineRef {
                stage,
                name,
                declares_name: _,
            } => {
                match subs.lookup_referenced(stage.inner, name) {
                    substitution::Substitution::Undefined => {
                        Err(Error::UndefinedVariable { name: name.clone() })
                    }
                    substitution::Substitution::Waiting(available_at, _) => {
                        // Available at is the amount of cycles left at the stage
                        // from which the variable is requested.
                        let referenced_at_stage = subs.current_stage - available_at;
                        Err(Error::UseBeforeReady {
                            name: name.clone(),
                            referenced_at_stage,
                            unavailable_for: available_at,
                        })
                    }
                    substitution::Substitution::Available(name) => Ok(Some(name.value_name())),
                    substitution::Substitution::Port => Ok(Some(name.value_name())),
                }
            }
            ExprKind::Call { .. } => Ok(None),
            ExprKind::MethodCall { .. } => diag_bail!(
                self,
                "method call should have been lowered to function by this point"
            ),
        }
    }

    // NOTE: this impl and a few others could be moved to a impl block that does not have
    // the Loc requirement if desired
    fn variable(&self, subs: &Substitutions) -> Result<mir::ValueName> {
        // If this expressions should not use the standard __expr__{} variable,
        // that is specified here

        Ok(self.alias(subs)?.unwrap_or(mir::ValueName::Expr(self.id)))
    }

    fn lower(&self, ctx: &mut Context) -> Result<StatementList> {
        let mut result = StatementList::new();

        let hir_type = ctx
            .types
            .expr_type(self, ctx.symtab.symtab(), &ctx.item_list.types)?;
        let self_type = hir_type.to_mir_type();

        match &self.kind {
            ExprKind::Identifier(_) => {
                // Empty. The identifier will be defined elsewhere
            }
            ExprKind::IntLiteral(value) => {
                let ty = self_type;
                result.push_primary(
                    mir::Statement::Constant(
                        self.id,
                        ty,
                        mir::ConstantValue::Int(value.clone().as_signed()),
                    ),
                    self,
                );
            }
            ExprKind::BoolLiteral(value) => {
                let ty = self_type;
                result.push_primary(
                    mir::Statement::Constant(self.id, ty, mir::ConstantValue::Bool(*value)),
                    self,
                );
            }
            ExprKind::BinaryOperator(lhs, op, rhs) => {
                let binop_builder = |op| -> Result<()> {
                    result.append(lhs.lower(ctx)?);
                    result.append(rhs.lower(ctx)?);

                    result.push_primary(
                        mir::Statement::Binding(mir::Binding {
                            name: self.variable(ctx.subs)?,
                            operator: op,
                            operands: vec![lhs.variable(ctx.subs)?, rhs.variable(ctx.subs)?],
                            ty: self_type,
                            loc: Some(self.loc()),
                        }),
                        self,
                    );
                    Ok(())
                };
                use mir::Operator::*;
                match op {
                    BinaryOperator::Add => binop_builder(Add)?,
                    BinaryOperator::Sub => binop_builder(Sub)?,
                    BinaryOperator::Mul => binop_builder(Mul)?,
                    BinaryOperator::Eq => binop_builder(Eq)?,
                    BinaryOperator::NotEq => binop_builder(NotEq)?,
                    BinaryOperator::Gt => binop_builder(Gt)?,
                    BinaryOperator::Lt => binop_builder(Lt)?,
                    BinaryOperator::Ge => binop_builder(Ge)?,
                    BinaryOperator::Le => binop_builder(Le)?,
                    BinaryOperator::LogicalXor => binop_builder(LogicalXor)?,
                    BinaryOperator::LeftShift => binop_builder(LeftShift)?,
                    BinaryOperator::RightShift => binop_builder(RightShift)?,
                    BinaryOperator::ArithmeticRightShift => binop_builder(ArithmeticRightShift)?,
                    BinaryOperator::LogicalAnd => binop_builder(LogicalAnd)?,
                    BinaryOperator::LogicalOr => binop_builder(LogicalOr)?,
                    BinaryOperator::BitwiseAnd => binop_builder(BitwiseAnd)?,
                    BinaryOperator::BitwiseOr => binop_builder(BitwiseOr)?,
                    BinaryOperator::BitwiseXor => binop_builder(BitwiseXor)?,
                };
            }
            ExprKind::UnaryOperator(op, operand) => {
                let unop_builder = |op| -> Result<()> {
                    result.append(operand.lower(ctx)?);

                    result.push_primary(
                        mir::Statement::Binding(mir::Binding {
                            name: self.variable(ctx.subs)?,
                            operator: op,
                            operands: vec![operand.variable(ctx.subs)?],
                            ty: self_type,
                            loc: Some(self.loc()),
                        }),
                        self,
                    );
                    Ok(())
                };
                use mir::Operator::*;
                match op {
                    hir::expression::UnaryOperator::Sub => unop_builder(USub)?,
                    hir::expression::UnaryOperator::Not => unop_builder(Not)?,
                    hir::expression::UnaryOperator::FlipPort => unop_builder(FlipPort)?,
                    hir::expression::UnaryOperator::BitwiseNot => unop_builder(BitwiseNot)?,
                    // Dereferences do nothing for codegen of the actual operator. It only
                    // prevents pipelining, hence Alias is fine here
                    hir::expression::UnaryOperator::Dereference => unop_builder(Alias)?,
                    hir::expression::UnaryOperator::Reference => unop_builder(Alias)?,
                };
            }
            ExprKind::TupleLiteral(elems) => {
                for elem in elems {
                    result.append(elem.lower(ctx)?)
                }

                result.push_primary(
                    mir::Statement::Binding(mir::Binding {
                        name: self.variable(ctx.subs)?,
                        operator: mir::Operator::ConstructTuple,
                        operands: elems
                            .iter()
                            .map(|e| e.variable(ctx.subs))
                            .collect::<Result<_>>()?,
                        ty: self_type,
                        loc: Some(self.loc()),
                    }),
                    self,
                )
            }
            ExprKind::TupleIndex(tup, idx) => {
                result.append(tup.lower(ctx)?);

                let types = if let mir::types::Type::Tuple(inner) = &ctx
                    .types
                    .expr_type(tup, ctx.symtab.symtab(), &ctx.item_list.types)?
                    .to_mir_type()
                {
                    inner.clone()
                } else {
                    unreachable!("Tuple indexing of non-tuple: {:?}", self_type);
                };

                result.push_primary(
                    mir::Statement::Binding(mir::Binding {
                        name: self.variable(ctx.subs)?,
                        operator: mir::Operator::IndexTuple(idx.inner as u64, types),
                        operands: vec![tup.variable(ctx.subs)?],
                        ty: self_type,
                        loc: Some(self.loc()),
                    }),
                    self,
                )
            }
            ExprKind::CreatePorts => {
                let (inner_type, right_mir_type) = match &hir_type {
                    ConcreteType::Tuple(inner) => {
                        if inner.len() != 2 {
                            diag_bail!(self, "port type was not 2-tuple. Got {hir_type}")
                        }

                        (&inner[0], inner[1].to_mir_type())
                    }
                    _ => {
                        diag_bail!(self, "port type was not tuple. Got {hir_type}")
                    }
                };

                if !inner_type.is_port() {
                    // For good diagnostics, we also need to look up the TypeVars
                    let self_tvar = ctx
                        .types
                        .type_of(&TypedExpression::Id(self.id))
                        .unwrap_or_else(|_| panic!("Found no type for {}", self.id));

                    let inner_tvar = match &self_tvar {
                        TypeVar::Tuple(inner) => {
                            if inner.len() != 2 {
                                diag_bail!(self, "port type was not 2-tuple. Got {hir_type}")
                            }

                            &inner[0]
                        }
                        _ => {
                            diag_bail!(self, "port type was not tuple. Got {hir_type}")
                        }
                    };

                    return Err(Diagnostic::error(
                        self,
                        "A port expression cannot create non-port values",
                    )
                    .primary_label(format!("{inner_tvar} is not a port type"))
                    .note(format!("The port expression creates a {self_tvar}"))
                    .into());
                }

                let inner_mir_type = inner_type.to_mir_type();

                let lname = mir::ValueName::Expr(ctx.idtracker.next());
                let rname = mir::ValueName::Expr(ctx.idtracker.next());

                result.append_secondary(
                    vec![
                        mir::Statement::Binding(mir::Binding {
                            name: lname.clone(),
                            operator: mir::Operator::Nop,
                            operands: vec![],
                            ty: inner_mir_type,
                            loc: Some(self.loc()),
                        }),
                        mir::Statement::Binding(mir::Binding {
                            name: rname.clone(),
                            operator: mir::Operator::FlipPort,
                            operands: vec![lname.clone()],
                            ty: right_mir_type,
                            loc: Some(self.loc()),
                        }),
                    ],
                    self,
                    "Port construction",
                );
                result.push_primary(
                    mir::Statement::Binding(mir::Binding {
                        name: self.variable(ctx.subs)?,
                        operator: mir::Operator::ConstructTuple,
                        operands: vec![lname, rname],
                        ty: self_type,
                        loc: Some(self.loc()),
                    }),
                    self,
                )
            }
            ExprKind::FieldAccess(target, field) => {
                result.append(target.lower(ctx)?);

                let ctype =
                    ctx.types
                        .expr_type(target, ctx.symtab.symtab(), &ctx.item_list.types)?;

                let member_types =
                    if let mir::types::Type::Tuple(members) = &ctype.to_mir_type() {
                        members.clone()
                    } else {
                        unreachable!("Field access on non-struct {:?}", self_type)
                    };

                let field_index = if let ConcreteType::Struct { name: _, members } = ctype {
                    let field_indices = members
                        .iter()
                        .enumerate()
                        .filter_map(
                            |(i, (name, _))| {
                                if name == &field.inner {
                                    Some(i)
                                } else {
                                    None
                                }
                            },
                        )
                        .collect::<Vec<_>>();

                    diag_assert!(
                        self,
                        field_indices.len() == 1,
                        "Expected exactly 1 field with the name {field}, got {}",
                        field_indices.len()
                    );

                    *field_indices.first().unwrap()
                } else {
                    unreachable!("Field access on non-struct {:?}", self_type)
                };

                result.push_primary(
                    mir::Statement::Binding(mir::Binding {
                        name: self.variable(ctx.subs)?,
                        operator: mir::Operator::IndexTuple(field_index as u64, member_types),
                        operands: vec![target.variable(ctx.subs)?],
                        ty: self_type,
                        loc: Some(self.loc()),
                    }),
                    self,
                )
            }
            ExprKind::ArrayLiteral(values) => {
                for elem in values {
                    result.append(elem.lower(ctx)?)
                }
                result.push_primary(
                    mir::Statement::Binding(mir::Binding {
                        name: self.variable(ctx.subs)?,
                        operator: mir::Operator::ConstructArray,
                        operands: values
                            .iter()
                            .map(|v| v.variable(ctx.subs))
                            .collect::<Result<_>>()?,
                        ty: self_type,
                        loc: Some(self.loc()),
                    }),
                    self,
                )
            }
            ExprKind::Index(target, index) => {
                result.append(target.lower(ctx)?);
                result.append(index.lower(ctx)?);

                result.push_primary(
                    mir::Statement::Binding(mir::Binding {
                        name: self.variable(ctx.subs)?,
                        operator: mir::Operator::IndexArray,
                        operands: vec![target.variable(ctx.subs)?, index.variable(ctx.subs)?],
                        ty: self_type,
                        loc: Some(self.loc()),
                    }),
                    self,
                )
            }
            ExprKind::Block(block) => {
                for statement in &block.statements {
                    result.append(statement.lower(ctx)?);
                }
                result.append(block.result.lower(ctx)?);

                // Empty. The block result will always be the last expression
            }
            ExprKind::If(cond, on_true, on_false) => {
                result.append(cond.lower(ctx)?);
                result.append(on_true.lower(ctx)?);
                result.append(on_false.lower(ctx)?);

                result.push_primary(
                    mir::Statement::Binding(mir::Binding {
                        name: self.variable(ctx.subs)?,
                        operator: mir::Operator::Select,
                        operands: vec![
                            cond.variable(ctx.subs)?,
                            on_true.variable(ctx.subs)?,
                            on_false.variable(ctx.subs)?,
                        ],
                        ty: ctx
                            .types
                            .expr_type(self, ctx.symtab.symtab(), &ctx.item_list.types)?
                            .to_mir_type(),
                        loc: Some(self.loc()),
                    }),
                    self,
                );
            }
            ExprKind::Match(operand, branches) => {
                let operand_ty =
                    ctx.types
                        .expr_type(operand, ctx.symtab.symtab(), &ctx.item_list.types)?;

                // Check for missing branches
                let pat_stacks = branches
                    .iter()
                    .map(|(pat, _)| PatStack::new(vec![DeconstructedPattern::from_hir(pat, ctx)]))
                    .collect::<Vec<_>>();

                // The patterns which make a wildcard useful are the ones that are missing
                // from the match statement
                let wildcard_useful = is_useful(
                    &PatStack::new(vec![DeconstructedPattern::wildcard(&operand_ty)]),
                    &usefulness::Matrix::new(&pat_stacks),
                );

                if wildcard_useful.is_useful() {
                    return Err(Error::MissingPatterns {
                        match_expr: self.loc(),
                        useful_branches: wildcard_useful.witnesses,
                    });
                }

                result.append(operand.lower(ctx)?);
                let mut operands = vec![];
                for (pat, result_expr) in branches {
                    result.append(pat.lower(operand.variable(ctx.subs)?, ctx)?);

                    let cond = pat.condition(&operand.variable(ctx.subs)?, ctx)?;
                    result.append_secondary(cond.statements, pat, "Pattern condition");

                    result.append(result_expr.lower(ctx)?);

                    operands.push(cond.result_name);
                    operands.push(result_expr.variable(ctx.subs)?);
                }

                result.push_primary(
                    mir::Statement::Binding(mir::Binding {
                        name: self.variable(ctx.subs)?,
                        operator: mir::Operator::Match,
                        operands,
                        ty: ctx
                            .types
                            .expr_type(self, ctx.symtab.symtab(), &ctx.item_list.types)?
                            .to_mir_type(),
                        loc: Some(self.loc()),
                    }),
                    self,
                )
            }
            ExprKind::Call { kind, callee, args } => {
                let head = ctx.symtab.symtab().unit_by_id(callee);
                let args =
                    match_args_with_params(args, &head.inputs, false).map_err(Diagnostic::from)?;

                match (kind, &head.unit_kind.inner) {
                    (CallKind::Function, UnitKind::Function(_))
                    | (CallKind::Entity(_), UnitKind::Entity) => {
                        result.append(self.handle_call(callee, &args, ctx)?);
                    }
                    (CallKind::Pipeline(_, cdepth), UnitKind::Pipeline(udepth)) => {
                        if cdepth != udepth {
                            return Err(Diagnostic::error(
                                cdepth,
                                "Pipeline depth mismatch".to_string(),
                            )
                            .primary_label(format!("Expected depth {udepth}"))
                            .secondary_label(udepth, format!("{} has depth {udepth}", head.name))
                            .into());
                        }

                        result.append(self.handle_call(callee, &args, ctx)?);
                    }
                    (CallKind::Function, other) => {
                        return Err(expect_function(callee, head.loc(), other))
                    }
                    (CallKind::Entity(inst), other) => {
                        return Err(expect_entity(inst, callee, head.loc(), other))
                    }
                    (CallKind::Pipeline(inst, _), other) => {
                        return Err(expect_pipeline(inst, callee, head.loc(), other))
                    }
                }
            }
            ExprKind::PipelineRef { .. } => {
                // Empty: Pipeline refs are lowered in the alias checking
            }
            ExprKind::MethodCall { .. } => {
                diag_bail!(
                    self,
                    "Method should already have been lowered at this point"
                )
            }
        }
        Ok(result)
    }

    fn handle_call(
        &self,
        name: &NameID,
        args: &[Argument],
        ctx: &mut Context,
    ) -> Result<StatementList> {
        let mut result = StatementList::new();
        for param in args {
            result.append(param.value.lower(ctx)?);
        }

        // Check if this is a standard library function which we are supposed to
        // handle
        macro_rules! handle_special_functions {
            ($([$($path:expr),*] => $handler:ident),*) => {
                $(
                    let path = Path(vec![$(Identifier($path.to_string()).nowhere()),*]).nowhere();
                    let final_id = ctx.symtab.symtab().try_lookup_final_id(&path);
                    if final_id
                        .map(|n| &n == name)
                        .unwrap_or(false)
                    {
                        return self.$handler(result, args, ctx);
                    };
                )*
            }
        }

        // Check if this is a call to something generic. If so we need to ensure that the
        // generic arguments were not mapped to ports
        let tok = GenericListToken::Expression(self.id);
        let instance_list = ctx.types.get_generic_list(&tok);
        for (name, ty) in instance_list {
            let actual = TypeState::ungenerify_type(ty, ctx.symtab.symtab(), &ctx.item_list.types);
            if actual.as_ref().map(|t| t.is_port()).unwrap_or(false) {
                return Err(Error::PortInGenericType {
                    loc: self.loc(),
                    param: name.clone(),
                    // NOTE: Safe because we were able to run `t.is_port()` above
                    actual: actual.unwrap(),
                });
            }
        }

        handle_special_functions! {
            ["std", "mem", "clocked_memory"] => handle_clocked_memory_decl,
            ["std", "mem", "clocked_memory_init"] => handle_clocked_memory_initial_decl,
            ["std", "mem", "read_memory"] => handle_read_memory,
            ["std", "conv", "trunc"] => handle_trunc,
            ["std", "conv", "sext"] => handle_sext,
            ["std", "conv", "zext"] => handle_zext,
            ["std", "conv", "concat"] => handle_concat,
            ["std", "ops", "div_pow2"] => handle_div_pow2,
            ["std", "ports", "new_mut_wire"] => handle_new_mut_wire,
            ["std", "ports", "read_mut_wire"] => handle_read_mut_wire
        }

        // Look up the name in the executable list to see if this is a type instantiation
        match ctx.item_list.executables.get(name) {
            Some(hir::ExecutableItem::EnumInstance { base_enum, variant }) => {
                let variant_count = match ctx.item_list.types.get(base_enum) {
                    Some(type_decl) => match &type_decl.kind {
                        hir::TypeDeclKind::Enum(e) => e.inner.options.len(),
                        _ => panic!("Instantiating enum of type which is not an enum"),
                    },
                    None => panic!("No type declaration found for {}", base_enum),
                };

                result.push_primary(
                    mir::Statement::Binding(mir::Binding {
                        name: self.variable(ctx.subs)?,
                        ty: ctx
                            .types
                            .expr_type(self, ctx.symtab.symtab(), &ctx.item_list.types)?
                            .to_mir_type(),
                        operator: mir::Operator::ConstructEnum {
                            variant: *variant,
                            variant_count,
                        },
                        operands: args
                            .iter()
                            .map(|arg| arg.value.variable(ctx.subs))
                            .collect::<Result<_>>()?,
                        loc: Some(self.loc()),
                    }),
                    self,
                )
            }
            Some(hir::ExecutableItem::StructInstance) => result.push_primary(
                mir::Statement::Binding(mir::Binding {
                    name: self.variable(ctx.subs)?,
                    ty: ctx
                        .types
                        .expr_type(self, ctx.symtab.symtab(), &ctx.item_list.types)?
                        .to_mir_type(),
                    operator: mir::Operator::ConstructTuple,
                    operands: args
                        .iter()
                        .map(|arg| arg.value.variable(ctx.subs))
                        .collect::<Result<Vec<_>>>()?,
                    loc: Some(self.loc()),
                }),
                self,
            ),
            Some(hir::ExecutableItem::Unit(u)) => {
                let (type_params, unit_name) = (&u.head.type_params, u.name.clone());

                let instance_name = if !type_params.is_empty() {
                    let t = type_params
                        .iter()
                        .map(|param| {
                            let name = param.name_id();

                            instance_list[&name].clone()
                        })
                        .collect();

                    UnitName::WithID(
                        ctx.mono_state
                            .request_compilation(unit_name, t, ctx.symtab)
                            .nowhere(),
                    )
                } else {
                    unit_name
                };

                result.push_primary(
                    mir::Statement::Binding(mir::Binding {
                        name: self.variable(ctx.subs)?,
                        operator: mir::Operator::Instance(instance_name.as_mir(), Some(self.loc())),
                        operands: args
                            .iter()
                            .map(|arg| arg.value.variable(ctx.subs))
                            .collect::<Result<_>>()?,
                        ty: ctx
                            .types
                            .expr_type(self, ctx.symtab.symtab(), &ctx.item_list.types)?
                            .to_mir_type(),
                        loc: Some(self.loc()),
                    }),
                    self,
                );
            }
            Some(hir::ExecutableItem::BuiltinUnit(name, head)) => {
                let (unit_name, type_params, head_loc) = (name, &head.type_params, head.loc());

                // NOTE: Ideally this check would be done earlier, when defining the generic
                // builtin. However, at the moment, the compiler does not know if the generic
                // is an intrinsic until here when it has gone through the list of intrinsics
                if !type_params.is_empty() {
                    return Err(Error::InstantiatingGenericBuiltin {
                        loc: self.loc(),
                        head: head_loc,
                    });
                }

                // NOTE: Builtin entities are not part of the item list, but we
                // should still emit the code for instantiating them
                result.push_primary(
                    mir::Statement::Binding(mir::Binding {
                        name: self.variable(ctx.subs)?,
                        operator: mir::Operator::Instance(unit_name.as_mir(), Some(self.loc())),
                        operands: args
                            .iter()
                            .map(|arg| arg.value.variable(ctx.subs))
                            .collect::<Result<_>>()?,
                        ty: ctx
                            .types
                            .expr_type(self, ctx.symtab.symtab(), &ctx.item_list.types)?
                            .to_mir_type(),
                        loc: Some(self.loc()),
                    }),
                    self,
                );
            }
            None => {
                unreachable!("Instantiating an item which is not known")
            }
        }
        Ok(result)
    }

    /// Result is the initial statement list to expand and return
    fn handle_clocked_memory_decl(
        &self,
        result: StatementList,
        args: &[Argument],
        ctx: &mut Context,
    ) -> Result<StatementList> {
        self.handle_clocked_memory(result, args, ctx, false)
    }

    fn handle_clocked_memory_initial_decl(
        &self,
        result: StatementList,
        args: &[Argument],
        ctx: &mut Context,
    ) -> Result<StatementList> {
        self.handle_clocked_memory(result, args, ctx, true)
    }

    fn handle_clocked_memory(
        &self,
        result: StatementList,
        args: &[Argument],
        ctx: &mut Context,
        has_initial: bool,
    ) -> Result<StatementList> {
        // The localimpl macro is a bit stupid
        let mut result = result;

        let elem_count = if let ConcreteType::Single {
            base: PrimitiveType::Memory,
            params,
        } =
            ctx.types
                .expr_type(self, ctx.symtab.symtab(), &ctx.item_list.types)?
        {
            if let ConcreteType::Integer(size) = params[1].clone() {
                size
            } else {
                panic!("Second param of memory declaration type was not integer")
            }
        } else {
            panic!("Decl memory declares a non-memory")
        };

        let initial = if has_initial {
            let initial_arg = &args[2];

            if let Some(witness) = initial_arg.value.runtime_requirement_witness() {
                return Err(Diagnostic::error(
                    initial_arg.value,
                    "Memory initial values must be known at compile time",
                )
                .primary_label("Value not known at compile time")
                .secondary_label(
                    witness,
                    "This subexpression cannot be computed at compile time",
                )
                .into());
            }

            if let ExprKind::ArrayLiteral(elems) = &initial_arg.value.kind {
                let values = elems
                    .iter()
                    .map(|e| Ok(e.lower(ctx)?.to_vec_no_source_map()))
                    .collect::<Result<Vec<_>>>()?;

                Some(values)
            } else {
                diag_bail!(initial_arg.value, "Memory initial value was not array")
            }
        } else {
            None
        };

        // Figure out the sizes of the operands
        let port_t =
            ctx.types
                .expr_type(args[1].value, ctx.symtab.symtab(), &ctx.item_list.types)?;
        if let ConcreteType::Array { inner, size } = port_t {
            if let ConcreteType::Tuple(tup_inner) = *inner {
                assert!(
                    tup_inner.len() == 3,
                    "Expected exactly 3 types in write port tuple"
                );
                let write_ports = size;
                let addr_w = tup_inner[1].to_mir_type().size();
                let inner_w = tup_inner[2].to_mir_type().size();

                result.push_primary(
                    mir::Statement::Binding(mir::Binding {
                        name: self.variable(ctx.subs)?,
                        operator: mir::Operator::DeclClockedMemory {
                            addr_w,
                            inner_w,
                            write_ports,
                            elems: elem_count,
                            initial,
                        },
                        operands: args
                            .iter()
                            // The third argument (if present) is the initial values which
                            // are passed in the operand
                            .take(2)
                            .map(|arg| arg.value.variable(ctx.subs))
                            .collect::<Result<Vec<_>>>()?,
                        ty: ctx
                            .types
                            .expr_type(self, ctx.symtab.symtab(), &ctx.item_list.types)?
                            .to_mir_type(),
                        loc: Some(self.loc()),
                    }),
                    self,
                )
            } else {
                panic!("Clocked array write port inner was not tuple")
            }
        } else {
            panic!("Clocked array write ports were not array")
        }

        Ok(result)
    }

    /// Result is the initial statement list to expand and return
    fn handle_read_memory(
        &self,
        result: StatementList,
        args: &[Argument],
        ctx: &mut Context,
    ) -> Result<StatementList> {
        // The localimpl macro is a bit stupid
        let mut result = result;

        let target = &args[0].value;
        let index = &args[1].value;

        let self_type = ctx
            .types
            .expr_type(self, ctx.symtab.symtab(), &ctx.item_list.types)?
            .to_mir_type();

        result.push_primary(
            mir::Statement::Binding(mir::Binding {
                name: self.variable(ctx.subs)?,
                operator: mir::Operator::IndexMemory,
                operands: vec![target.variable(ctx.subs)?, index.variable(ctx.subs)?],
                ty: self_type,
                loc: Some(self.loc()),
            }),
            self,
        );

        Ok(result)
    }

    fn handle_trunc(
        &self,
        result: StatementList,
        args: &[Argument],
        ctx: &mut Context,
    ) -> Result<StatementList> {
        let mut result = result;

        let self_type = ctx
            .types
            .expr_type(self, ctx.symtab.symtab(), &ctx.item_list.types)?
            .to_mir_type();

        let input_type = ctx
            .types
            .expr_type(args[0].value, ctx.symtab.symtab(), &ctx.item_list.types)?
            .to_mir_type();

        if self_type.size() > input_type.size() {
            let input_loc = args[0].value.loc();
            return Err(Diagnostic::error(input_loc, "Truncating to a larger value")
                .primary_label(format!(
                    "This value is {} bit{}",
                    input_type.size(),
                    if input_type.size() == One::one() {
                        ""
                    } else {
                        "s"
                    }
                ))
                .secondary_label(
                    self,
                    format!("The value is truncated to {} bits here", self_type.size()),
                )
                .note("Truncation can only remove bits")
                .into());
        }

        result.push_primary(
            mir::Statement::Binding(mir::Binding {
                name: self.variable(ctx.subs)?,
                operator: mir::Operator::Truncate,
                operands: vec![args[0].value.variable(ctx.subs)?],
                ty: ctx
                    .types
                    .expr_type(self, ctx.symtab.symtab(), &ctx.item_list.types)?
                    .to_mir_type(),
                loc: Some(self.loc()),
            }),
            self,
        );

        Ok(result)
    }

    fn handle_sext(
        &self,
        result: StatementList,
        args: &[Argument],
        ctx: &mut Context,
    ) -> Result<StatementList> {
        let mut result = result;

        let self_type = ctx
            .types
            .expr_type(self, ctx.symtab.symtab(), &ctx.item_list.types)?
            .to_mir_type();

        let input_type = ctx
            .types
            .expr_type(args[0].value, ctx.symtab.symtab(), &ctx.item_list.types)?
            .to_mir_type();

        let extra_bits = if self_type.size() > input_type.size() {
            self_type.size() - input_type.size()
        } else {
            BigUint::zero()
        };

        result.push_primary(
            mir::Statement::Binding(mir::Binding {
                name: self.variable(ctx.subs)?,
                operator: mir::Operator::SignExtend {
                    extra_bits,
                    operand_size: input_type.size(),
                },
                operands: vec![args[0].value.variable(ctx.subs)?],
                ty: self_type,
                loc: Some(self.loc()),
            }),
            self,
        );

        Ok(result)
    }

    fn handle_zext(
        &self,
        result: StatementList,
        args: &[Argument],
        ctx: &mut Context,
    ) -> Result<StatementList> {
        let mut result = result;

        let self_type = ctx
            .types
            .expr_type(self, ctx.symtab.symtab(), &ctx.item_list.types)?
            .to_mir_type();

        let input_type = ctx
            .types
            .expr_type(args[0].value, ctx.symtab.symtab(), &ctx.item_list.types)?
            .to_mir_type();

        let extra_bits = if self_type.size() > input_type.size() {
            self_type.size() - input_type.size()
        } else {
            BigUint::zero()
        };

        result.push_primary(
            mir::Statement::Binding(mir::Binding {
                name: self.variable(ctx.subs)?,
                operator: mir::Operator::ZeroExtend { extra_bits },
                operands: vec![args[0].value.variable(ctx.subs)?],
                ty: self_type,
                loc: None,
            }),
            self,
        );

        Ok(result)
    }

    fn handle_concat(
        &self,
        result: StatementList,
        args: &[Argument],
        ctx: &mut Context,
    ) -> Result<StatementList> {
        let mut result = result;

        let arg0_type = ctx
            .types
            .expr_type(args[0].value, ctx.symtab.symtab(), &ctx.item_list.types)?
            .to_mir_type();
        let arg1_type = ctx
            .types
            .expr_type(args[1].value, ctx.symtab.symtab(), &ctx.item_list.types)?
            .to_mir_type();

        let self_type = ctx
            .types
            .expr_type(self, ctx.symtab.symtab(), &ctx.item_list.types)?
            .to_mir_type();

        if self_type.size() != arg0_type.size() + arg1_type.size() {
            Err(Error::ConcatSizeMismatch {
                lhs: arg0_type.size().at_loc(args[0].value),
                rhs: arg1_type.size().at_loc(args[1].value),
                expected: arg0_type.size() + arg1_type.size(),
                result: self_type.size().at_loc(self),
            })
        } else {
            result.push_primary(
                mir::Statement::Binding(mir::Binding {
                    name: self.variable(ctx.subs)?,
                    operator: mir::Operator::Concat,
                    operands: vec![
                        args[0].value.variable(ctx.subs)?,
                        args[1].value.variable(ctx.subs)?,
                    ],
                    ty: self_type,
                    loc: None,
                }),
                self,
            );

            Ok(result)
        }
    }

    fn handle_div_pow2(
        &self,
        result: StatementList,
        args: &[Argument],
        ctx: &mut Context,
    ) -> Result<StatementList> {
        let mut result = result;

        let self_type = ctx
            .types
            .expr_type(self, ctx.symtab.symtab(), &ctx.item_list.types)?
            .to_mir_type();

        result.push_primary(
            mir::Statement::Binding(mir::Binding {
                name: self.variable(ctx.subs)?,
                operator: mir::Operator::DivPow2,
                operands: vec![
                    args[0].value.variable(ctx.subs)?,
                    args[1].value.variable(ctx.subs)?,
                ],
                ty: self_type,
                loc: Some(self.loc()),
            }),
            self,
        );

        Ok(result)
    }

    fn handle_new_mut_wire(
        &self,
        result: StatementList,
        args: &[Argument],
        ctx: &mut Context,
    ) -> Result<StatementList> {
        let mut result = result;

        assert!(args.is_empty());

        let self_type = ctx
            .types
            .expr_type(self, ctx.symtab.symtab(), &ctx.item_list.types)?
            .to_mir_type();

        result.push_primary(
            mir::Statement::Binding(mir::Binding {
                name: self.variable(ctx.subs)?,
                operator: mir::Operator::Nop,
                operands: vec![],
                ty: self_type,
                loc: None,
            }),
            self,
        );

        Ok(result)
    }

    fn handle_read_mut_wire(
        &self,
        result: StatementList,
        args: &[Argument],
        ctx: &mut Context,
    ) -> Result<StatementList> {
        let mut result = result;

        assert_eq!(args.len(), 1);

        let self_type = ctx
            .types
            .expr_type(self, ctx.symtab.symtab(), &ctx.item_list.types)?
            .to_mir_type();

        result.push_primary(
            mir::Statement::Binding(mir::Binding {
                name: self.variable(ctx.subs)?,
                operator: mir::Operator::ReadPort,
                operands: vec![args[0].value.variable(ctx.subs)?],
                ty: self_type,
                loc: None,
            }),
            self,
        );

        Ok(result)
    }
}

pub struct Context<'a> {
    pub symtab: &'a mut FrozenSymtab,
    pub idtracker: &'a mut ExprIdTracker,
    pub types: &'a TypeState,
    pub item_list: &'a ItemList,
    pub mono_state: &'a mut MonoState,
    pub subs: &'a mut Substitutions,
    pub diag_handler: &'a mut DiagHandler,
}

pub fn generate_unit<'a>(
    unit: &Unit,
    name: UnitName,
    types: &TypeState,
    symtab: &mut FrozenSymtab,
    idtracker: &mut ExprIdTracker,
    item_list: &ItemList,
    // Map of names generated by codegen to the original name in the source code.
    name_map: &mut HashMap<NameID, NameID>,
    mono_state: &mut MonoState,
    diag_handler: &mut DiagHandler,
    name_source_map: &mut NameSourceMap,
) -> Result<mir::Entity> {
    let mir_inputs = unit
        .inputs
        .iter()
        .map(|(name_id, _)| {
            let name = name_id.1.tail().to_string();
            let val_name = name_id.value_name();
            let ty = types
                .name_type(name_id, symtab.symtab(), &item_list.types)?
                .to_mir_type();

            Ok((name, val_name, ty))
        })
        .collect::<Result<_>>()?;

    let mut statements = StatementList::new();
    let subs = &mut Substitutions::new();

    if let UnitKind::Pipeline(_) = unit.head.unit_kind.inner {
        lower_pipeline(
            &unit.inputs,
            &unit.body,
            types,
            &mut statements,
            subs,
            symtab,
            item_list,
            name_map,
        )?;
    }

    let mut ctx = Context {
        symtab,
        idtracker,
        types,
        subs,
        item_list,
        mono_state,
        diag_handler,
    };

    statements.append(unit.body.lower(&mut ctx)?);

    let output_t = types
        .expr_type(&unit.body, symtab.symtab(), &item_list.types)?
        .to_mir_type();

    linear_check::check_linear_types(
        &unit.inputs,
        &unit.body,
        types,
        symtab.symtab(),
        &item_list.types,
    )?;

    Ok(mir::Entity {
        name: name.as_mir(),
        inputs: mir_inputs,
        output: unit.body.variable(subs)?,
        output_type: output_t,
        statements: statements.to_vec(name_source_map),
    })
}
