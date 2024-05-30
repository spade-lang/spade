mod attributes;
pub mod error;
mod linear_check;
pub mod monomorphisation;
pub mod name_map;
pub mod passes;
mod pattern;
pub mod pipelines;
mod statement_list;
pub mod substitution;
mod usefulness;

use std::collections::BTreeMap;

use attributes::AttributeListExt;
use attributes::LocAttributeExt;
use error::format_witnesses;
use error::refutable_pattern_diagnostic;
use error::undefined_variable;
use error::use_before_ready;
use error::{expect_entity, expect_function, expect_pipeline};
use hir::expression::BitLiteral;
use hir::expression::CallKind;
use hir::expression::LocExprExt;
use hir::ArgumentList;
use hir::Attribute;
use hir::Parameter;
use hir::TypeDeclKind;
use hir::TypeSpec;
use hir::WalTrace;
use local_impl::local_impl;
use num::ToPrimitive;

use hir::param_util::{match_args_with_params, Argument};
use hir::symbol_table::{FrozenSymtab, PatternableKind};
use hir::{ItemList, Pattern, PatternArgument, UnitKind, UnitName};
use mir::types::Type as MirType;
use mir::MirInput;
use mir::ValueNameSource;
use mir::{ConstantValue, ValueName};
use monomorphisation::MonoItem;
use monomorphisation::MonoState;
use name_map::NameSource;
pub use name_map::NameSourceMap;
use num::{BigUint, One, Zero};
use pattern::DeconstructedPattern;
use pipelines::lower_pipeline;
use pipelines::MaybePipelineContext;
use spade_common::id_tracker::ExprIdTracker;
use spade_common::location_info::WithLocation;
use spade_common::name::{Identifier, Path};
use spade_common::num_ext::InfallibleToBigInt;
use spade_diagnostics::diag_anyhow;
use spade_diagnostics::{diag_assert, diag_bail, DiagHandler, Diagnostic};
use spade_typeinference::equation::TypeVar;
use spade_typeinference::equation::TypedExpression;
use spade_typeinference::GenericListToken;
use spade_typeinference::HasType;
use spade_types::KnownType;
use statement_list::StatementList;
use substitution::Substitution;
use substitution::Substitutions;
use usefulness::{is_useful, PatStack, Usefulness};

use crate::error::Result;
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
        let kind = match self {
            UnitName::WithID(name) => mir::unit_name::UnitNameKind::Escaped {
                name: format!("{}[{}]", name.inner.1.as_strs().join("::"), name.inner.0),
                path: name.inner.1.as_strings(),
            },
            UnitName::FullPath(name) => mir::unit_name::UnitNameKind::Escaped {
                name: name.inner.1.as_strs().join("::"),
                path: name.inner.1.as_strings(),
            },
            UnitName::Unmangled(name, _) => mir::unit_name::UnitNameKind::Unescaped(name.clone()),
        };

        mir::UnitName {
            kind,
            source: match self {
                UnitName::WithID(name) => name.inner.clone(),
                UnitName::FullPath(name) => name.inner.clone(),
                UnitName::Unmangled(_, name) => name.inner.clone(),
            },
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
                base: PrimitiveType::Bool | PrimitiveType::Clock | PrimitiveType::Bit,
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
                [CType::Integer(val)] => Type::UInt(val.clone()),
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
            CType::Single {
                base: PrimitiveType::Void,
                params: _,
            } => Type::Void,
            CType::Single {
                base: PrimitiveType::InOut,
                params,
            } => match params.as_slice() {
                [inner] => Type::InOut(Box::new(inner.to_mir_type())),
                t => unreachable!("{:?} is an invalid generic parameter for inout", t),
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
                let members = members
                    .iter()
                    .map(|(n, t)| (n.0.clone(), t.to_mir_type()))
                    .collect();
                Type::Struct(members)
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

    fn value_name_with_alternate_source(&self, source: ValueNameSource) -> mir::ValueName;
}

impl NameIDExt for NameID {
    fn value_name(&self) -> mir::ValueName {
        self.value_name_with_alternate_source(ValueNameSource::Name(self.clone()))
    }

    fn value_name_with_alternate_source(&self, source: ValueNameSource) -> mir::ValueName {
        let mangled = format!("{}", self.1.tail());
        mir::ValueName::Named(self.0, mangled, source)
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

                        let mir_type = &ctx
                            .types
                            .type_of_id(self.id, ctx.symtab.symtab(), &ctx.item_list.types)
                            .to_mir_type();
                        let inner_types = if let mir::types::Type::Struct(inner) = mir_type {
                            inner.iter().map(|s| s.1.clone()).collect::<Vec<_>>()
                        } else {
                            unreachable!("Struct destructuring of non-struct");
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

pub fn do_wal_trace_lowering(
    pattern: &Loc<hir::Pattern>,
    main_value_name: &ValueName,
    wal_traceable: &Loc<hir::WalTraceable>,
    wal_trace: &Loc<WalTrace>,
    ty: &ConcreteType,
    result: &mut StatementList,
    ctx: &mut Context,
) -> Result<()> {
    let hir::WalTrace { clk, rst } = &wal_trace.inner;
    let hir::WalTraceable {
        suffix,
        uses_clk,
        uses_rst,
    } = &wal_traceable.inner;

    let mut check_clk_or_rst =
        |signal: &Option<Loc<Expression>>, uses: bool, name, suffix| -> Result<()> {
            match (signal, uses) {
                (None, false) => {}
                (None, true) => {
                    return Err(Diagnostic::error(
                        wal_trace,
                        format!("The {name} signal for this trace must be provided"),
                    ))
                }
                (Some(signal), false) => {
                    return Err(
                        Diagnostic::error(signal, format!("Unnecessary {name} signal"))
                            .primary_label(format!("Unnecessary {name} signal"))
                            .secondary_label(
                                wal_traceable,
                                format!("This struct does not need a {name} signal for tracing"),
                            ),
                    )
                }
                (Some(signal), true) => result.push_anonymous(mir::Statement::WalTrace {
                    name: main_value_name.clone(),
                    val: signal.variable(ctx.subs)?,
                    suffix: format!("__{suffix}__{}", wal_traceable.suffix.clone()),
                    ty: MirType::Bool,
                }),
            }
            Ok(())
        };
    check_clk_or_rst(clk, *uses_clk, "clock", "clk")?;
    check_clk_or_rst(rst, *uses_rst, "reset", "rst")?;

    if let ConcreteType::Struct { name: _, members } = ty {
        let inner_types = members
            .iter()
            .map(|(_, t)| t.to_mir_type())
            .collect::<Vec<_>>();

        // Sanity check that all fields are either pure input or pure output
        for (n, ty) in members {
            let mir_ty = ty.to_mir_type();
            if mir_ty.backward_size() != BigUint::zero()
                && ty.to_mir_type().size() != BigUint::zero()
            {
                return Err(Diagnostic::error(
                    pattern,
                    "Wal tracing does not work on types with mixed-direction fields",
                )
                .primary_label(format!(
                    "The field '{n}' of the struct has both & and &mut wires"
                )));
            }
        }

        let inner_backward_types = members
            .iter()
            .filter_map(|(_, t)| match t.to_mir_type() {
                MirType::Backward(i) => Some(i.as_ref().clone()),
                _ => None,
            })
            .collect::<Vec<_>>();

        // If we have &mut wires, we need a flipped port to read the values from because
        // we need to work around a small bug. Create an anonymous value for this
        // lifeguard spade#252
        let flipped_id = ctx.idtracker.next();
        let flipped_ty = MirType::Struct(
            members
                .iter()
                .filter_map(|(n, ty)| match ty.to_mir_type() {
                    MirType::Backward(i) => Some((n.clone().0, i.as_ref().clone())),
                    _ => None,
                })
                .collect(),
        );
        let flipped_port = mir::Statement::Binding(mir::Binding {
            name: ValueName::Expr(flipped_id),
            operator: mir::Operator::ReadMutWires,
            operands: vec![main_value_name.clone()],
            ty: flipped_ty.clone(),
            loc: None,
        });
        if !flipped_ty.size().is_zero() {
            result.push_anonymous(flipped_port);
        }

        // The forward port has the backward variants included, so extracting `(a, &mut b, c)` so
        // the forward fields will be [0] and [2]
        // The backward copy only has the mut wire, so it is (&mut b) and the index is [0]
        let mut i_all = 0;
        let mut i_backward = 0;
        for (n, ty) in members.iter() {
            let new_id = ctx.idtracker.next();
            let field_name = ValueName::Expr(new_id);

            let (is_backward, mir_ty, operand, operator) = match ty.to_mir_type() {
                MirType::Backward(b) => {
                    let result = (
                        true,
                        *b,
                        ValueName::Expr(flipped_id),
                        mir::Operator::IndexTuple(i_backward, inner_backward_types.clone()),
                    );
                    i_backward += 1;
                    i_all += 1;
                    result
                }
                other => {
                    let result = (
                        false,
                        other,
                        main_value_name.clone(),
                        mir::Operator::IndexTuple(i_all, inner_types.clone()),
                    );
                    i_all += 1;
                    result
                }
            };
            // Insert an indexing operation, and a wal trace on the result.
            result.push_anonymous(mir::Statement::Binding(mir::Binding {
                name: field_name.clone(),
                operator,
                operands: vec![operand],
                ty: mir_ty.clone(),
                loc: None,
            }));

            // Add the wal trace statement
            result.push_anonymous(mir::Statement::WalTrace {
                name: main_value_name.clone(),
                val: field_name,
                suffix: format!("__{n}__{}", suffix.clone()),
                ty: mir_ty,
            });

            // Add the new expression to the type state so we can look it up
            // during translation. Doing this is a messy process however, because
            // we lost information. We'll cheat, and unify the expression with
            // indexing for the correct field on the pattern.
            // This is kind of a giant hack and makes quite a few assumptions about
            // the rest of the compiler
            // If problems occur in this code, it is probably a good idea to start
            // looking at refactoring this into a more sane state

            let dummy_expr_id = ctx.idtracker.next();
            let dummy_expr = if is_backward {
                hir::Expression {
                    id: new_id,
                    kind: ExprKind::Call {
                        kind: CallKind::Entity(().nowhere()),
                        callee: ctx
                            .symtab
                            .symtab()
                            .lookup_unit(
                                &Path::from_strs(&["std", "ports", "read_mut_wire"]).nowhere(),
                            )
                            .expect("did not find std::ports::read_mut_wire in symtab")
                            .0
                            .nowhere(),
                        args: ArgumentList::Positional(vec![hir::Expression {
                            kind: ExprKind::FieldAccess(
                                Box::new(
                                    hir::Expression {
                                        kind: ExprKind::Null,
                                        id: dummy_expr_id,
                                    }
                                    .nowhere(),
                                ),
                                n.clone().nowhere(),
                            ),
                            id: ctx.idtracker.next(),
                        }
                        .nowhere()])
                        .nowhere(),
                        turbofish: None,
                    },
                }
                .nowhere()
            } else {
                hir::Expression {
                    kind: ExprKind::FieldAccess(
                        Box::new(
                            hir::Expression {
                                kind: ExprKind::Null,
                                id: dummy_expr_id,
                            }
                            .nowhere(),
                        ),
                        n.clone().nowhere(),
                    ),
                    id: new_id,
                }
                .nowhere()
            };

            let type_ctx = spade_typeinference::Context {
                symtab: ctx.symtab.symtab(),
                items: ctx.item_list,
            };
            let generic_list = &ctx.types.create_generic_list(
                spade_typeinference::GenericListSource::Anonymous,
                &[],
                None,
            )?;
            ctx.types
                .visit_expression(&dummy_expr, &type_ctx, generic_list)
                .map_err(|e| {
                    diag_anyhow!(
                        wal_trace,
                        "{e}\n Unification error while laundering a struct"
                    )
                })?;

            ctx.types
                .unify(
                    &TypedExpression::Id(pattern.id),
                    &TypedExpression::Id(dummy_expr_id),
                    &spade_typeinference::Context {
                        symtab: ctx.symtab.symtab(),
                        items: ctx.item_list,
                    },
                )
                .unwrap(); // Unification with a completely generic expr
            ctx.types.check_requirements(&type_ctx).unwrap();
        }
    } else {
        diag_bail!(wal_trace, "Tracing on non-struct")
    }

    Ok(())
}

pub fn lower_wal_trace(
    pattern: &Loc<hir::Pattern>,
    wal_trace: &Loc<WalTrace>,
    ctx: &mut Context,
    result: &mut StatementList,
    concrete_ty: &ConcreteType,
) -> Result<()> {
    let hir_ty = pattern
        .get_type(ctx.types)
        .map_err(|_| diag_anyhow!(pattern, "Pattern had no type during WAL trace generation"))?;
    match &hir_ty {
        TypeVar::Known(_, spade_types::KnownType::Named(name), _) => {
            let ty = ctx.item_list.types.get(name);

            match ty.as_ref().map(|ty| &ty.inner.kind) {
                Some(TypeDeclKind::Struct(s)) => {
                    if let Some(suffix) = &s.wal_traceable {
                        do_wal_trace_lowering(
                            pattern,
                            &pattern.value_name(),
                            suffix,
                            wal_trace,
                            concrete_ty,
                            result,
                            ctx,
                        )?;
                    } else {
                        return Err(Diagnostic::error(
                            wal_trace,
                            "#[wal_trace] on struct without #[wal_traceable]",
                        )
                        .primary_label(format!("{} does not have #[wal_traceable]", name))
                        .secondary_label(
                            pattern,
                            format!("This has type {} which does not have #[wal_traceable]", hir_ty),
                        )
                        .note("This most likely means that the struct can not be analyzed by a wal script"));
                    }
                }
                Some(other) => {
                    return Err(Diagnostic::error(
                        wal_trace,
                        "#[wal_trace] can only be applied to values of struct type",
                    )
                    .primary_label(format!("#[wal_trace] on {}", other.name()))
                    .secondary_label(
                        pattern,
                        format!("This has type {} which is {}", hir_ty, other.name()),
                    )
                    .into())
                }
                None => {
                    diag_bail!(wal_trace, "wal_trace on non-declared type")
                }
            }
        }
        other => {
            return Err(Diagnostic::error(
                wal_trace,
                "#[wal_trace] can only be applied to values of struct type",
            )
            .primary_label(format!("#[wal_trace] on {}", other))
            .secondary_label(pattern, format!("This has type {other}")))
        }
    }
    Ok(())
}

#[local_impl]
impl StatementLocal for Statement {
    #[tracing::instrument(name = "Statement::lower", level = "trace", skip(self, ctx))]
    fn lower(&self, ctx: &mut Context) -> Result<StatementList> {
        let mut result = StatementList::new();
        match self {
            Statement::Binding(hir::Binding {
                pattern,
                ty: _,
                value,
                wal_trace,
            }) => {
                result.append(value.lower(ctx)?);

                let refutability = pattern.is_refutable(ctx);
                if refutability.is_useful() {
                    return Err(refutable_pattern_diagnostic(
                        pattern.loc(),
                        &refutability,
                        "let",
                    ));
                }

                let concrete_ty =
                    ctx.types
                        .type_of_id(pattern.id, ctx.symtab.symtab(), &ctx.item_list.types);

                let mir_ty = concrete_ty.to_mir_type();

                result.push_primary(
                    mir::Statement::Binding(mir::Binding {
                        name: pattern.value_name(),
                        operator: mir::Operator::Alias,
                        operands: vec![value.variable(ctx.subs)?],
                        ty: mir_ty.clone(),
                        loc: Some(pattern.loc()),
                    }),
                    pattern,
                );

                if let Some(wal_trace) = wal_trace {
                    lower_wal_trace(pattern, wal_trace, ctx, &mut result, &concrete_ty)?;
                }

                result.append(pattern.lower(value.variable(ctx.subs)?, ctx)?);
            }
            Statement::Register(register) => {
                let hir::Register {
                    clock,
                    reset,
                    initial,
                    pattern,
                    value,
                    value_type: _,
                    attributes,
                } = &register;
                result.append(clock.lower(ctx)?);

                if let Some((trig, value)) = &reset {
                    result.append(trig.lower(ctx)?);
                    result.append(value.lower(ctx)?);
                }

                if let Some(initial) = initial {
                    result.append(initial.lower(ctx)?);
                }

                result.append(value.lower(ctx)?);

                let refutability = pattern.is_refutable(ctx);
                if refutability.is_useful() {
                    return Err(refutable_pattern_diagnostic(
                        pattern.loc(),
                        &refutability,
                        "reg",
                    ));
                }

                let ty =
                    ctx.types
                        .type_of_id(pattern.id, ctx.symtab.symtab(), &ctx.item_list.types);

                if ty.is_port() {
                    return Err(
                        Diagnostic::error(value, "Ports cannot be put in a register")
                            .primary_label("This is a port")
                            .note(format!("{ty} is a port")),
                    );
                }

                let mut traced = None;
                attributes.lower(&mut |attr| match &attr.inner {
                    Attribute::Fsm { state } => {
                        traced = Some(state.value_name());
                        Ok(())
                    }
                    Attribute::WalTraceable { .. } => Err(attr.report_unused("register")),
                })?;

                let initial = if let Some(init) = initial {
                    if let Some(witness) = init.runtime_requirement_witness() {
                        return Err(Diagnostic::error(
                            init,
                            "Register initial values must be known at compile time",
                        )
                        .primary_label("Value not known at compile time")
                        .secondary_label(
                            witness,
                            "This subexpression cannot be computed at compile time",
                        ));
                    };

                    Some(init.lower(ctx)?.to_vec_no_source_map())
                } else {
                    None
                };

                result.push_primary(
                    mir::Statement::Register(mir::Register {
                        name: pattern.value_name(),
                        ty: ctx
                            .types
                            .type_of_id(pattern.id, ctx.symtab.symtab(), &ctx.item_list.types)
                            .to_mir_type(),
                        clock: clock.variable(ctx.subs)?,
                        reset: reset
                            .as_ref()
                            .map::<Result<_>, _>(|(value, trig)| {
                                Ok((value.variable(ctx.subs)?, trig.variable(ctx.subs)?))
                            })
                            .transpose()?,
                        initial,
                        value: value.variable(ctx.subs)?,
                        loc: Some(pattern.loc()),
                        traced,
                    }),
                    pattern,
                );

                result.append(pattern.lower(pattern.value_name(), ctx)?);
            }
            Statement::Declaration(_) => {}
            Statement::PipelineRegMarker(_cond) => {
                // NOTE: Cond is handled by pipeline lowering
                ctx.subs.current_stage += 1;
            }
            Statement::Label(_) => {}
            Statement::Assert(expr) => {
                result.append(expr.lower(ctx)?);
                result.push_anonymous(mir::Statement::Assert(
                    expr.variable(ctx.subs)?.at_loc(expr),
                ))
            }
            Statement::WalSuffixed { suffix, target } => {
                let ty = ctx
                    .types
                    .name_type(target, ctx.symtab.symtab(), &ctx.item_list.types)?
                    .to_mir_type();

                result.push_anonymous(mir::Statement::WalTrace {
                    name: target.value_name(),
                    val: target.value_name(),
                    suffix: suffix.0.clone(),
                    ty,
                })
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
                Substitution::Undefined => Err(undefined_variable(&ident.clone().at_loc(self))),
                Substitution::Waiting(available_in, name) => Err(use_before_ready(
                    &name.at_loc(self),
                    subs.current_stage,
                    available_in,
                )),
                Substitution::Available(current) => Ok(Some(current.value_name())),
                Substitution::Port | Substitution::ZeroSized => Ok(Some(ident.value_name())),
            },
            ExprKind::IntLiteral(_, _) => Ok(None),
            ExprKind::TypeLevelInteger(_) => Ok(None),
            ExprKind::BoolLiteral(_) => Ok(None),
            ExprKind::BitLiteral(_) => Ok(None),
            ExprKind::TupleLiteral(_) => Ok(None),
            ExprKind::TupleIndex(_, _) => Ok(None),
            ExprKind::FieldAccess(_, _) => Ok(None),
            ExprKind::CreatePorts => Ok(None),
            ExprKind::ArrayLiteral { .. } => Ok(None),
            ExprKind::Index(_, _) => Ok(None),
            ExprKind::RangeIndex { .. } => Ok(None),
            ExprKind::Block(block) => {
                if let Some(result) = &block.result {
                    result.variable(subs).map(Some)
                } else {
                    Ok(None)
                }
            }
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
                    Substitution::Undefined => Err(undefined_variable(name)),
                    Substitution::Waiting(available_at, _) => {
                        // Available at is the amount of cycles left at the stage
                        // from which the variable is requested.
                        let referenced_at_stage = subs.current_stage - available_at;
                        Err(use_before_ready(name, referenced_at_stage, available_at))
                    }
                    Substitution::Available(name) => Ok(Some(name.value_name())),
                    Substitution::Port | Substitution::ZeroSized => Ok(Some(name.value_name())),
                }
            }
            ExprKind::StageReady => Ok(None),
            ExprKind::StageValid => Ok(None),
            ExprKind::Call { .. } => Ok(None),
            ExprKind::MethodCall { .. } => diag_bail!(
                self,
                "method call should have been lowered to function by this point"
            ),
            ExprKind::Null => {
                diag_bail!(self, "Null expression found during hir lowering")
            }
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
            ExprKind::IntLiteral(value, _) => {
                let ty = self_type;
                result.push_primary(
                    mir::Statement::Constant(self.id, ty, mir::ConstantValue::Int(value.clone())),
                    self,
                );
            }
            ExprKind::TypeLevelInteger(name) => {
                let ty = self_type;
                if let Some(generic_list) = ctx.unit_generic_list {
                    let value = ctx.types.type_var_from_hir(
                        self.loc(),
                        &hir::TypeSpec::Generic(name.clone().nowhere()),
                        generic_list,
                    );

                    let value = match TypeState::ungenerify_type(
                        &value,
                        ctx.symtab.symtab(),
                        &ctx.item_list.types,
                    ) {
                        Some(ConcreteType::Integer(value)) => value,
                        Some(other) => diag_bail!(self, "Inferred {other} for type level integer"),
                        None => diag_bail!(self, "Did not find a type for {name}"),
                    };

                    result.push_primary(
                        mir::Statement::Constant(
                            self.id,
                            ty,
                            mir::ConstantValue::Int(value.to_bigint()),
                        ),
                        self,
                    )
                } else {
                    diag_bail!(
                        self,
                        "Attempted to use type level integer in non-generic function"
                    )
                }
            }
            ExprKind::BoolLiteral(value) => {
                let ty = self_type;
                result.push_primary(
                    mir::Statement::Constant(self.id, ty, mir::ConstantValue::Bool(*value)),
                    self,
                );
            }
            ExprKind::BitLiteral(value) => {
                let ty = self_type;
                let cv = match value {
                    BitLiteral::Low => mir::ConstantValue::Bool(false),
                    BitLiteral::High => mir::ConstantValue::Bool(true),
                    BitLiteral::HighImp => mir::ConstantValue::HighImp,
                };
                result.push_primary(mir::Statement::Constant(self.id, ty, cv), self);
            }
            ExprKind::BinaryOperator(lhs, op, rhs) => {
                macro_rules! binop_builder {
                    ($op:ident) => {{
                        result.append(lhs.lower(ctx)?);
                        result.append(rhs.lower(ctx)?);

                        result.push_primary(
                            mir::Statement::Binding(mir::Binding {
                                name: self.variable(ctx.subs)?,
                                operator: $op,
                                operands: vec![lhs.variable(ctx.subs)?, rhs.variable(ctx.subs)?],
                                ty: self_type,
                                loc: Some(self.loc()),
                            }),
                            self,
                        );
                    }};
                }
                macro_rules! dual_binop_builder {
                    ($sop:ident, $uop:ident) => {{
                        result.append(lhs.lower(ctx)?);
                        result.append(rhs.lower(ctx)?);

                        let op = match &ctx
                            .types
                            .expr_type(lhs, ctx.symtab.symtab(), &ctx.item_list.types)?
                            .to_mir_type()
                        {
                            mir::types::Type::Int(_) => $sop,
                            mir::types::Type::UInt(_) => $uop,
                            other => panic!("Dual binop on {other} which is not int or uint"),
                        };

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
                    }};
                }

                use mir::Operator::*;
                match op.inner {
                    BinaryOperator::Add => dual_binop_builder!(Add, UnsignedAdd),
                    BinaryOperator::Sub => dual_binop_builder!(Sub, UnsignedSub),
                    BinaryOperator::Mul => dual_binop_builder!(Mul, UnsignedMul),
                    BinaryOperator::Eq => binop_builder!(Eq),
                    BinaryOperator::NotEq => binop_builder!(NotEq),
                    BinaryOperator::Gt => dual_binop_builder!(Gt, UnsignedGt),
                    BinaryOperator::Lt => dual_binop_builder!(Lt, UnsignedLt),
                    BinaryOperator::Ge => dual_binop_builder!(Ge, UnsignedGe),
                    BinaryOperator::Le => dual_binop_builder!(Le, UnsignedLe),
                    BinaryOperator::LogicalXor => binop_builder!(LogicalXor),
                    BinaryOperator::LeftShift => binop_builder!(LeftShift),
                    BinaryOperator::RightShift => binop_builder!(RightShift),
                    BinaryOperator::ArithmeticRightShift => binop_builder!(ArithmeticRightShift),
                    BinaryOperator::LogicalAnd => binop_builder!(LogicalAnd),
                    BinaryOperator::LogicalOr => binop_builder!(LogicalOr),
                    BinaryOperator::BitwiseAnd => binop_builder!(BitwiseAnd),
                    BinaryOperator::BitwiseOr => binop_builder!(BitwiseOr),
                    BinaryOperator::BitwiseXor => binop_builder!(BitwiseXor),
                    BinaryOperator::Div => {
                        match &rhs.inner.kind {
                            ExprKind::IntLiteral(val, _) => {
                                let val_u128 = val.to_u128()
                                    .ok_or_else(|| Diagnostic::error(
                                        rhs.loc(),
                                        "Division by constants larger than 2^128 is unsupported"
                                    ))?;

                                if val_u128.count_ones() == 1 {
                                    dual_binop_builder!(Div, UnsignedDiv)
                                } else {
                                    return Err(Diagnostic::error(rhs.loc(), "Division can only be performed on powers of two")
                                    .primary_label("Division by non-power-of-two value")
                                    .help("Non-power-of-two division is generally slow and should usually be done over multiple cycles.")
                                    .span_suggest_replace(
                                        format!("If you are sure you want to divide by {val}, use `std::ops::comb_div`"),
                                        op,
                                        "`std::ops::comb_div`"
                                    ))
                                }
                            }
                            _ => {
                                return Err(Diagnostic::error(self, "Division can only be performed on constant powers of two")
                                    .primary_label("Division by non-constant value")
                                    .help("Division is generally slow and should be done over multiple cycles.")
                                    .span_suggest_replace(
                                        "If you are sure you want to divide by a non-constant, use `std::ops::comb_div`",
                                        op,
                                        "`std::ops::comb_div`"
                                    ))
                            }
                        }
                    }
                    BinaryOperator::Mod => {
                        match &rhs.inner.kind {
                            ExprKind::IntLiteral(val, _) => {
                                let val_u128 = val.to_u128()
                                    .ok_or_else(|| Diagnostic::error(
                                        rhs.loc(),
                                        "Modulo by constants larger than 2^128 is unsupported"
                                    ))?;

                                if val_u128.count_ones() == 1 {
                                    dual_binop_builder!(Mod, UnsignedMod)
                                } else {
                                    return Err(Diagnostic::error(rhs.loc(), "Modulo can only be performed on powers of two")
                                    .primary_label("Modulo by non-power-of-two value")
                                    .help("Non-power-of-two modulo is generally slow and should usually be done over multiple cycles.")
                                    .span_suggest_replace(
                                        format!("If you are sure you want to divide by {val}, use `std::ops::comb_mod`"),
                                        op,
                                        "`std::ops::comb_mod`"
                                    ))
                                }
                            }
                            _ => {
                                return Err(Diagnostic::error(self, "Modulo can only be performed on constant powers of two")
                                    .primary_label("Modulo by non-constant value")
                                    .help("Modulo is generally slow and should be done over multiple cycles.")
                                    .span_suggest_replace(
                                        "If you are sure you want to divide by a non-constant, use `std::ops::comb_mod`",
                                        op,
                                        "`std::ops::comb_mod`"
                                    ))
                            }
                        }
                    }
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
                        TypeVar::Known(_, KnownType::Tuple, inner) => {
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
                    .note(format!("The port expression creates a {self_tvar}")));
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
                    if let mir::types::Type::Struct(members) = &ctype.clone().to_mir_type() {
                        members.iter().map(|s| s.1.clone()).collect::<Vec<_>>()
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
            ExprKind::RangeIndex { target, start, end } => {
                result.append(target.lower(ctx)?);

                match target.get_type(ctx.types)? {
                    TypeVar::Known(_, KnownType::Array, inner) => match &inner[1] {
                        TypeVar::Known(_, KnownType::Integer(size), _) => {
                            if &start.inner >= size {
                                return Err(Diagnostic::error(start, "Array index out of bounds")
                                    .primary_label("index out of bounds")
                                    .secondary_label(
                                        target.as_ref(),
                                        format!("This array only has {size} elements"),
                                    ));
                            }
                            if &end.inner > size {
                                return Err(Diagnostic::error(end, "Array index out of bounds")
                                    .primary_label("index out of bounds")
                                    .secondary_label(
                                        target.as_ref(),
                                        format!("This array only has {size} elements"),
                                    ));
                            }
                        }
                        _ => {
                            diag_bail!(self, "Array size was not integer")
                        }
                    },
                    _ => diag_bail!(self, "Range indexing on non-array"),
                };

                result.push_primary(
                    mir::Statement::Binding(mir::Binding {
                        name: self.variable(ctx.subs)?,
                        operator: mir::Operator::RangeIndexArray {
                            start: start.inner.clone(),
                            end_exclusive: end.inner.clone(),
                        },
                        operands: vec![target.variable(ctx.subs)?],
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
                if let Some(block_result) = &block.result {
                    result.append(block_result.lower(ctx)?);
                }

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
                    let witnesses = format_witnesses(&wildcard_useful.witnesses);

                    return Err(Diagnostic::error(
                        self.loc(),
                        format!("Non-exhaustive match: {witnesses} not covered"),
                    )
                    .primary_label(format!("{witnesses} not covered")));
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
            ExprKind::Call {
                kind,
                callee,
                args,
                turbofish: _,
            } => {
                let head = ctx.symtab.symtab().unit_by_id(callee);
                let args = match_args_with_params(args, &head.inputs.inner, false)
                    .map_err(Diagnostic::from)?;

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
                            .secondary_label(udepth, format!("{} has depth {udepth}", head.name)));
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
            ExprKind::StageReady => {
                let signal = ctx
                    .pipeline_context
                    .get(self)?
                    .ready_signals
                    .get(ctx.subs.current_stage)
                    .ok_or_else(|| Diagnostic::bug(self, "Pipeline ready signal overflow"))?;

                // If there is no enable signal, valid will be true, generate a constant
                match signal {
                    Some(signal_name) => {
                        // NOTE: we could use the aliases method here, but that
                        // would require duplicating the logic to check if the enable
                        // signal is set
                        result.push_primary(
                            mir::Statement::Binding(mir::Binding {
                                name: self.variable(ctx.subs)?,
                                operator: mir::Operator::Alias,
                                operands: vec![signal_name.clone()],
                                ty: mir::types::Type::Bool,
                                loc: Some(self.loc()),
                            }),
                            self,
                        )
                    }
                    None => result.push_primary(
                        mir::Statement::Constant(
                            self.id,
                            mir::types::Type::Bool,
                            mir::ConstantValue::Bool(true),
                        ),
                        self,
                    ),
                }
            }
            ExprKind::StageValid => {
                let signal = ctx
                    .pipeline_context
                    .get(self)?
                    .valid_signals
                    .get(ctx.subs.current_stage)
                    .ok_or_else(|| Diagnostic::bug(self, "Pipeline valid signal overflow"))?;

                match signal {
                    Some(signal_name) => {
                        // NOTE: we could use the aliases method here, but that
                        // would require duplicating the logic to check if the enable
                        // signal is set
                        result.push_primary(
                            mir::Statement::Binding(mir::Binding {
                                name: self.variable(ctx.subs)?,
                                operator: mir::Operator::Alias,
                                operands: vec![signal_name.clone()],
                                ty: mir::types::Type::Bool,
                                loc: Some(self.loc()),
                            }),
                            self,
                        )
                    }
                    None => result.push_primary(
                        mir::Statement::Constant(
                            self.id,
                            mir::types::Type::Bool,
                            mir::ConstantValue::Bool(true),
                        ),
                        self,
                    ),
                }
            }
            ExprKind::MethodCall { .. } => {
                diag_bail!(
                    self,
                    "Method should already have been lowered at this point"
                )
            }
            ExprKind::Null => {
                diag_bail!(self, "Null expression found during hir lowering")
            }
        }
        Ok(result)
    }

    fn handle_call(
        &self,
        name: &Loc<NameID>,
        args: &[Argument<Expression, TypeSpec>],
        ctx: &mut Context,
    ) -> Result<StatementList> {
        let mut result = StatementList::new();
        for param in args {
            result.append(param.value.lower(ctx)?);
        }

        let tok = GenericListToken::Expression(self.id);
        let instance_list = ctx.types.get_generic_list(&tok);
        let generic_port_check = || {
            // Check if this is a call to something generic. If so we need to ensure that the
            // generic arguments were not mapped to ports
            for (name, ty) in instance_list {
                let actual =
                    TypeState::ungenerify_type(ty, ctx.symtab.symtab(), &ctx.item_list.types);
                if actual.as_ref().map(|t| t.is_port()).unwrap_or(false) {
                    return Err(
                        Diagnostic::error(self.loc(), "Generic types cannot be ports")
                            .primary_label(format!(
                                "Parameter {name} is {actual} which is a port type",
                                actual = actual.unwrap()
                            )),
                    );
                }
            }
            Ok(())
        };

        // Check if this is a standard library function which we are supposed to
        // handle
        macro_rules! handle_special_function {
            ([$($path:expr),*] $allow_port:expr => $handler:ident {allow_port}) => {
                handle_special_function!([$($path),*] => $handler true)
            };
            ([$($path:expr),*] $allow_port:expr => $handler:ident) => {
                handle_special_function!([$($path),*] => $handler false)
            };
            ([$($path:expr),*] => $handler:ident $allow_port:expr) => {
                let path = Path(vec![$(Identifier($path.to_string()).nowhere()),*]).nowhere();
                let final_id = ctx.symtab.symtab().try_lookup_final_id(&path);
                if final_id
                    .map(|n| &n == &name.inner)
                    .unwrap_or(false)
                {
                    if !$allow_port {
                        generic_port_check()?;
                    }

                    return self.$handler(&name, result, args, ctx);
                };
            }
        }
        macro_rules! handle_special_functions {
            ($([$($path:expr),*] => $handler:ident $({$extra:tt})?),*) => {
                $(
                    handle_special_function!([$($path),*] true => $handler $({$extra})?)
                );*
            };
        }

        handle_special_functions! {
            ["std", "mem", "clocked_memory"] => handle_clocked_memory_decl,
            ["std", "mem", "clocked_memory_init"] => handle_clocked_memory_initial_decl,
            ["std", "mem", "read_memory"] => handle_read_memory,
            ["std", "conv", "trunc"] => handle_trunc,
            ["std", "conv", "sext"] => handle_sext,
            ["std", "conv", "zext"] => handle_zext,
            ["std", "conv", "concat"] => handle_concat,
            ["std", "conv", "unsafe", "unsafe_cast"] => handle_unsafe_cast {allow_port},
            ["std", "conv", "flip_array"] => handle_flip_array,
            ["std", "ops", "div_pow2"] => handle_div_pow2,
            ["std", "ops", "gray_to_bin"] => handle_gray_to_bin,
            ["std", "ops", "reduce_and"] => handle_reduce_and,
            ["std", "ops", "reduce_or"] => handle_reduce_or,
            ["std", "ops", "reduce_xor"] => handle_reduce_xor,
            ["std", "ops", "comb_div"] => handle_comb_div,
            ["std", "ops", "comb_mod"] => handle_comb_mod,
            ["std", "ports", "new_mut_wire"] => handle_new_mut_wire,
            ["std", "ports", "read_mut_wire"] => handle_read_mut_wire
        }

        generic_port_check()?;

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
                            .request_compilation(
                                unit_name,
                                false,
                                t,
                                ctx.symtab,
                                ctx.self_mono_item.clone().map(|item| (item, self.loc())),
                            )
                            .nowhere(),
                    )
                } else {
                    unit_name
                };

                let params = args
                    .iter()
                    .zip(&u.head.inputs.0)
                    .map(|(_, input)| mir::ParamName {
                        name: input.name.0.to_string(),
                        no_mangle: input.no_mangle,
                    })
                    .collect();

                result.push_primary(
                    mir::Statement::Binding(mir::Binding {
                        name: self.variable(ctx.subs)?,
                        operator: mir::Operator::Instance {
                            name: instance_name.as_mir(),
                            params,
                            loc: Some(self.loc()),
                        },
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
                let (unit_name, type_params) = (name, &head.type_params);

                // NOTE: Ideally this check would be done earlier, when defining the generic
                // builtin. However, at the moment, the compiler does not know if the generic
                // is an intrinsic until here when it has gone through the list of intrinsics
                if !type_params.is_empty() {
                    return Err(Diagnostic::error(
                        self.loc(),
                        "Generic builtins cannot be instantiated",
                    )
                    .primary_label("Invalid instance")
                    .secondary_label(head, "Because this is a generic __builtin__"));
                }

                let params = args
                    .iter()
                    .zip(&head.inputs.0)
                    .map(|(_, input)| mir::ParamName {
                        name: input.name.0.to_string(),
                        no_mangle: input.no_mangle,
                    })
                    .collect();

                // NOTE: Builtin entities are not part of the item list, but we
                // should still emit the code for instantiating them
                result.push_primary(
                    mir::Statement::Binding(mir::Binding {
                        name: self.variable(ctx.subs)?,
                        operator: mir::Operator::Instance {
                            name: unit_name.as_mir(),
                            params,
                            loc: Some(self.loc()),
                        },
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
        _path: &Loc<NameID>,
        result: StatementList,
        args: &[Argument<Expression, TypeSpec>],
        ctx: &mut Context,
    ) -> Result<StatementList> {
        self.handle_clocked_memory(result, args, ctx, false)
    }

    fn handle_clocked_memory_initial_decl(
        &self,
        _path: &Loc<NameID>,
        result: StatementList,
        args: &[Argument<Expression, TypeSpec>],
        ctx: &mut Context,
    ) -> Result<StatementList> {
        self.handle_clocked_memory(result, args, ctx, true)
    }

    fn handle_clocked_memory(
        &self,
        result: StatementList,
        args: &[Argument<Expression, TypeSpec>],
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
                ));
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
                            elems: elem_count.clone(),
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
        _path: &Loc<NameID>,
        result: StatementList,
        args: &[Argument<Expression, TypeSpec>],
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
        _path: &Loc<NameID>,
        result: StatementList,
        args: &[Argument<Expression, TypeSpec>],
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
                .primary_label(format!("This value is {}", bits_str(input_type.size()),))
                .secondary_label(
                    self,
                    format!("The value is truncated to {} bits here", self_type.size()),
                )
                .note("Truncation can only remove bits"));
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
        path: &Loc<NameID>,
        result: StatementList,
        args: &[Argument<Expression, TypeSpec>],
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

        if self_type.size() < input_type.size() {
            let input_loc = args[0].value.loc();
            return Err(Diagnostic::error(self, "Sign-extending to a shorter value")
                .primary_label(format!(
                    "The value is sign-extended to {} here",
                    bits_str(self_type.size()),
                ))
                .secondary_label(
                    input_loc,
                    format!("This value is {} bits", input_type.size()),
                )
                .note("")
                .span_suggest_replace(
                    "Sign-extension cannot decrease width, use trunc instead",
                    path,
                    "trunc",
                ));
        }

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
        path: &Loc<NameID>,
        result: StatementList,
        args: &[Argument<Expression, TypeSpec>],
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

        if self_type.size() < input_type.size() {
            let input_loc = args[0].value.loc();
            return Err(Diagnostic::error(self, "Zero-extending to a shorter value")
                .primary_label(format!(
                    "The value is zero-extended to {} here",
                    bits_str(self_type.size()),
                ))
                .secondary_label(
                    input_loc,
                    format!("This value is {}", bits_str(input_type.size())),
                )
                .span_suggest_replace(
                    "Zero-extension cannot decrease width, use trunc instead",
                    path,
                    "trunc",
                ));
        }

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

    fn handle_unsafe_cast(
        &self,
        _path: &Loc<NameID>,
        result: StatementList,
        args: &[Argument<Expression, TypeSpec>],
        ctx: &mut Context,
    ) -> Result<StatementList> {
        let mut result = result;

        let self_type_hir = ctx
            .types
            .expr_type(self, ctx.symtab.symtab(), &ctx.item_list.types)?;
        let self_type = self_type_hir.to_mir_type();

        let input_type_hir =
            ctx.types
                .expr_type(args[0].value, ctx.symtab.symtab(), &ctx.item_list.types)?;
        let input_type = input_type_hir.to_mir_type();

        if self_type.backward_size() != BigUint::zero() {
            return Err(Diagnostic::error(
                self,
                format!("Attempting to cast to type containing &mut value"),
            )
            .primary_label(format!("{self_type_hir} has a &mut wire")));
        }
        if input_type.backward_size() != BigUint::zero() {
            return Err(Diagnostic::error(
                args[0].value,
                format!("Attempting to cast from type containing &mut value"),
            )
            .primary_label(format!("{input_type_hir} has a &mut wire")));
        }

        if self_type.size() != input_type.size() {
            let input_loc = args[0].value.loc();
            return Err(Diagnostic::error(
                self,
                format!(
                    "Type size mismatch. Attempting to cast {} to {}",
                    bits_str(input_type.size()),
                    bits_str(self_type.size())
                ),
            )
            .primary_label(format!(
                "The output type has {}",
                bits_str(self_type.size())
            ))
            .secondary_label(
                input_loc,
                format!("The source has {}", bits_str(input_type.size()),),
            )
            .help("unsafe_cast can only convert between types of identical size"));
        }

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

    fn handle_flip_array(
        &self,
        _path: &Loc<NameID>,
        result: StatementList,
        args: &[Argument<Expression, TypeSpec>],
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
                operator: mir::Operator::Bitreverse,
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
        _path: &Loc<NameID>,
        result: StatementList,
        args: &[Argument<Expression, TypeSpec>],
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
            Err(Diagnostic::bug(
                self_type.size().at_loc(self),
                format!(
                    "Concatenation produces {result} bits, expected {expected}",
                    expected = arg0_type.size() + arg1_type.size()
                ),
            ))
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
        _path: &Loc<NameID>,
        result: StatementList,
        args: &[Argument<Expression, TypeSpec>],
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

    fn handle_gray_to_bin(
        &self,
        _path: &Loc<NameID>,
        result: StatementList,
        args: &[Argument<Expression, TypeSpec>],
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
                operator: mir::Operator::Gray2Bin {
                    num_bits: self_type.size(),
                },
                operands: vec![args[0].value.variable(ctx.subs)?],
                ty: self_type,
                loc: Some(self.loc()),
            }),
            self,
        );

        Ok(result)
    }

    fn handle_reduce_and(
        &self,
        _path: &Loc<NameID>,
        result: StatementList,
        args: &[Argument<Expression, TypeSpec>],
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
                operator: mir::Operator::ReduceAnd,
                operands: vec![args[0].value.variable(ctx.subs)?],
                ty: self_type,
                loc: Some(self.loc()),
            }),
            self,
        );

        Ok(result)
    }

    fn handle_reduce_or(
        &self,
        _path: &Loc<NameID>,
        result: StatementList,
        args: &[Argument<Expression, TypeSpec>],
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
                operator: mir::Operator::ReduceOr,
                operands: vec![args[0].value.variable(ctx.subs)?],
                ty: self_type,
                loc: Some(self.loc()),
            }),
            self,
        );

        Ok(result)
    }

    fn handle_reduce_xor(
        &self,
        _path: &Loc<NameID>,
        result: StatementList,
        args: &[Argument<Expression, TypeSpec>],
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
                operator: mir::Operator::ReduceXor,
                operands: vec![args[0].value.variable(ctx.subs)?],
                ty: self_type,
                loc: Some(self.loc()),
            }),
            self,
        );

        Ok(result)
    }

    fn handle_comb_div(
        &self,
        _path: &Loc<NameID>,
        result: StatementList,
        args: &[Argument<Expression, TypeSpec>],
        ctx: &mut Context,
    ) -> Result<StatementList> {
        let mut result = result;

        let self_type = ctx
            .types
            .expr_type(self, ctx.symtab.symtab(), &ctx.item_list.types)?
            .to_mir_type();

        let operator = match self_type {
            mir::types::Type::Int(_) => mir::Operator::Div,
            mir::types::Type::UInt(_) => mir::Operator::UnsignedDiv,
            other => {
                return Err(Diagnostic::bug(
                    self,
                    format!("Inferred non-integer type ({other}) for division operand"),
                ))
            }
        };

        result.push_primary(
            mir::Statement::Binding(mir::Binding {
                name: self.variable(ctx.subs)?,
                operator,
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

    fn handle_comb_mod(
        &self,
        _path: &Loc<NameID>,
        result: StatementList,
        args: &[Argument<Expression, TypeSpec>],
        ctx: &mut Context,
    ) -> Result<StatementList> {
        let mut result = result;

        let self_type = ctx
            .types
            .expr_type(self, ctx.symtab.symtab(), &ctx.item_list.types)?
            .to_mir_type();

        let operator = match self_type {
            mir::types::Type::Int(_) => mir::Operator::Mod,
            mir::types::Type::UInt(_) => mir::Operator::UnsignedMod,
            other => {
                return Err(Diagnostic::bug(
                    self,
                    format!("Inferred non-integer type ({other}) for modulo operand"),
                ))
            }
        };

        result.push_primary(
            mir::Statement::Binding(mir::Binding {
                name: self.variable(ctx.subs)?,
                operator,
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
        _path: &Loc<NameID>,
        result: StatementList,
        args: &[Argument<Expression, TypeSpec>],
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
        _path: &Loc<NameID>,
        result: StatementList,
        args: &[Argument<Expression, TypeSpec>],
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

pub fn bits_str(bits: BigUint) -> String {
    format!("{} bit{}", bits, if bits == One::one() { "" } else { "s" })
}

pub struct Context<'a> {
    pub symtab: &'a mut FrozenSymtab,
    pub idtracker: &'a mut ExprIdTracker,
    pub types: &'a mut TypeState,
    pub item_list: &'a ItemList,
    pub mono_state: &'a mut MonoState,
    // The generic list token of the currently generated uint if it is generic, otherwise None
    pub unit_generic_list: &'a Option<GenericListToken>,
    pub subs: &'a mut Substitutions,
    pub diag_handler: &'a mut DiagHandler,
    pub pipeline_context: &'a mut MaybePipelineContext,
    pub self_mono_item: Option<MonoItem>,
}

pub fn generate_unit<'a>(
    unit: &Unit,
    name: UnitName,
    types: &mut TypeState,
    symtab: &mut FrozenSymtab,
    idtracker: &mut ExprIdTracker,
    item_list: &ItemList,
    unit_generic_list: &Option<GenericListToken>,
    // Map of names generated by codegen to the original name in the source code.
    name_map: &mut BTreeMap<NameID, NameID>,
    mono_state: &mut MonoState,
    diag_handler: &mut DiagHandler,
    name_source_map: &mut NameSourceMap,
    self_mono_item: Option<MonoItem>,
) -> Result<mir::Entity> {
    let mir_inputs = unit
        .head
        .inputs
        .0
        .iter()
        .zip(&unit.inputs)
        .map(
            |(
                Parameter {
                    name: _,
                    ty: type_spec,
                    no_mangle,
                },
                (name_id, _),
            )| {
                let name = name_id.1.tail().to_string();
                let val_name = name_id.value_name();
                let ty = types
                    .name_type(name_id, symtab.symtab(), &item_list.types)?
                    .to_mir_type();

                if ty.backward_size() != BigUint::zero() && ty.size() != BigUint::zero() {
                    if let Some(no_mangle) = no_mangle {
                        return Err(Diagnostic::error(
                            no_mangle,
                            "Ports with both & and &mut cannot be #[no_mangle]",
                        )
                        .primary_label("Not allowed on mixed-direction ports")
                        .secondary_label(type_spec, "This has both & and &mut components"));
                    }
                }

                name_source_map.insert_primary(&val_name, NameSource::Name(name_id.clone()));

                Ok(MirInput {
                    name,
                    val_name,
                    ty,
                    no_mangle: *no_mangle,
                })
            },
        )
        .collect::<Result<_>>()?;

    let mut statements = StatementList::new();
    let subs = &mut Substitutions::new();
    let pipeline_context = &mut MaybePipelineContext::NotPipeline;

    let mut ctx = Context {
        symtab,
        idtracker,
        types,
        subs,
        item_list,
        unit_generic_list,
        mono_state,
        diag_handler,
        pipeline_context,
        self_mono_item,
    };

    if let UnitKind::Pipeline(_) = unit.head.unit_kind.inner {
        lower_pipeline(
            &unit.inputs,
            &unit.body,
            &mut statements,
            &mut ctx,
            name_map,
        )?;
    }

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
