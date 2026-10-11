use itertools::Itertools;
use nesty::{Code, code};
use spade_common::{
    location_info::Loc,
    name::{Identifier, NameID},
};

use crate::{
    ArgumentList, AttributeList, Binding, ConstGeneric, ConstGenericWithId, ExprKind, Expression,
    Generic, Input, Memory, Pattern, PatternArgument, Register, Statement, TraitSpec,
    TypeExpression, TypeParam, TypeSpec, Unit, UnitHead, WhereClause,
    expression::{IncompleteExpression, NamedArgument, OuterLambdaParam, Safety},
};

pub trait PrettyDebug {
    fn pretty_debug(&self) -> String;
}

impl PrettyDebug for Identifier {
    fn pretty_debug(&self) -> String {
        format!("{self}")
    }
}

impl PrettyDebug for NameID {
    fn pretty_debug(&self) -> String {
        format!("{self:?}")
    }
}

impl PrettyDebug for Unit {
    fn pretty_debug(&self) -> String {
        let Self {
            name,
            head:
                UnitHead {
                    name: _,
                    inputs: _,
                    is_nonstatic_method: _,
                    output_type,
                    unit_type_params,
                    hidden_type_params,
                    scope_type_params,
                    unit_kind,
                    where_clauses,
                    unsafe_marker,
                    documentation,
                    deprecation_note: _,
                },
            attributes,
            inputs,
            body,
        } = self;

        let type_params = format!(
            "<{} | {} | {}>",
            scope_type_params
                .iter()
                .map(PrettyDebug::pretty_debug)
                .join(","),
            hidden_type_params
                .iter()
                .map(PrettyDebug::pretty_debug)
                .join(","),
            unit_type_params
                .iter()
                .map(PrettyDebug::pretty_debug)
                .join(", ")
        );

        let inputs = inputs
            .iter()
            .map(|Input { wire, name, ty }| {
                format!(
                    "{}{}: {}",
                    if wire.is_some() { "wire " } else { "" },
                    name.pretty_debug(),
                    ty.pretty_debug()
                )
            })
            .join(", ");

        code! [
            [0] documentation;
            [0] format!(
                    "{} {}{unit_kind:?} {}{}({}) -> {}",
                    attributes.pretty_debug(),
                    if unsafe_marker.is_some() { "unsafe " } else { "" },
                    name.name_id().pretty_debug(),
                    type_params,
                    inputs,
                    output_type.pretty_debug()
                );
            [1] format!("where: {}", where_clauses.iter().map(PrettyDebug::pretty_debug).join(", "));
            [0] "{";
            [1]     body.pretty_debug();
            [0] "}";
        ]
        .to_string()
    }
}

impl PrettyDebug for WhereClause {
    fn pretty_debug(&self) -> String {
        match self {
            WhereClause::Int {
                target,
                kind,
                constraint,
                if_unsatisfied,
            } => format!(
                "{} {kind} {}{}",
                target.pretty_debug(),
                constraint.pretty_debug(),
                if_unsatisfied
                    .as_ref()
                    .map(|message| format!(" else {message:?}"))
                    .unwrap_or_default()
            ),
            WhereClause::Type { target, traits } => format!(
                "{}: {}",
                target.pretty_debug(),
                traits.iter().map(|t| t.pretty_debug()).join(" + }")
            ),
        }
    }
}

impl PrettyDebug for AttributeList {
    fn pretty_debug(&self) -> String {
        if self.0.len() != 0 {
            "[attribute list omitted]".to_string()
        } else {
            String::new()
        }
    }
}

impl PrettyDebug for TypeExpression {
    fn pretty_debug(&self) -> String {
        match self {
            TypeExpression::Bool(b) => format!("{b}"),
            TypeExpression::Integer(i) => format!("{i}"),
            TypeExpression::String(s) => format!("{s:?}"),
            TypeExpression::TypeSpec(type_spec) => type_spec.pretty_debug(),
            TypeExpression::ConstGeneric(inner) => inner.pretty_debug(),
        }
    }
}

impl PrettyDebug for TypeSpec {
    fn pretty_debug(&self) -> String {
        match self {
            TypeSpec::Declared(name, args) => {
                format!(
                    "{}<{}>",
                    name.pretty_debug(),
                    args.iter().map(|arg| arg.pretty_debug()).join(", ")
                )
            }
            TypeSpec::Generic(g) => g.pretty_debug(),
            TypeSpec::Tuple(inner) => format!(
                "({})",
                inner.iter().map(|arg| arg.pretty_debug()).join(", ")
            ),
            TypeSpec::Array { inner, size } => {
                format!("[{}; {}]", inner.pretty_debug(), size.pretty_debug())
            }
            TypeSpec::Inverted(inner) => format!("inv {}", inner.pretty_debug()),
            TypeSpec::CopyView(inner) => format!("&{}", inner.pretty_debug()),
            TypeSpec::TraitSelf(_) => "Self".to_string(),
            TypeSpec::Wildcard(_) => "_".to_string(),
        }
    }
}

impl PrettyDebug for ConstGeneric {
    fn pretty_debug(&self) -> String {
        match self {
            ConstGeneric::Name(n) => n.pretty_debug(),
            ConstGeneric::Bool(b) => format!("{b}"),
            ConstGeneric::Int(big_int) => format!("{big_int}"),
            ConstGeneric::Str(s) => format!("{s:?}"),
            ConstGeneric::Add(lhs, rhs) => {
                format!("({} + {})", lhs.pretty_debug(), rhs.pretty_debug())
            }
            ConstGeneric::Sub(lhs, rhs) => {
                format!("({} - {})", lhs.pretty_debug(), rhs.pretty_debug())
            }
            ConstGeneric::Mul(lhs, rhs) => {
                format!("({} * {})", lhs.pretty_debug(), rhs.pretty_debug())
            }
            ConstGeneric::Div(lhs, rhs) => {
                format!("({} / {})", lhs.pretty_debug(), rhs.pretty_debug())
            }
            ConstGeneric::Mod(lhs, rhs) => {
                format!("({} % {})", lhs.pretty_debug(), rhs.pretty_debug())
            }
            ConstGeneric::IntBitsFor(inner) => inner.pretty_debug().to_string(),
            ConstGeneric::UintBitsFor(inner) => inner.pretty_debug().to_string(),
            ConstGeneric::Eq(lhs, rhs) => {
                format!("({} == {})", lhs.pretty_debug(), rhs.pretty_debug())
            }
            ConstGeneric::NotEq(lhs, rhs) => {
                format!("({} != {})", lhs.pretty_debug(), rhs.pretty_debug())
            }
            ConstGeneric::Lt(lhs, rhs) => {
                format!("({} < {})", lhs.pretty_debug(), rhs.pretty_debug())
            }
            ConstGeneric::Gt(lhs, rhs) => {
                format!("({} > {})", lhs.pretty_debug(), rhs.pretty_debug())
            }
            ConstGeneric::Le(lhs, rhs) => {
                format!("({} <= {})", lhs.pretty_debug(), rhs.pretty_debug())
            }
            ConstGeneric::Ge(lhs, rhs) => {
                format!("({} >= {})", lhs.pretty_debug(), rhs.pretty_debug())
            }
            ConstGeneric::LogicalNot(inner) => {
                format!("(!{})", inner.pretty_debug())
            }
            ConstGeneric::LogicalAnd(lhs, rhs) => {
                format!("({} && {})", lhs.pretty_debug(), rhs.pretty_debug())
            }
            ConstGeneric::LogicalOr(lhs, rhs) => {
                format!("({} || {})", lhs.pretty_debug(), rhs.pretty_debug())
            }
            ConstGeneric::LogicalXor(lhs, rhs) => {
                format!("({} ^^ {})", lhs.pretty_debug(), rhs.pretty_debug())
            }
            ConstGeneric::LeftShift(lhs, rhs) => {
                format!("({} << {})", lhs.pretty_debug(), rhs.pretty_debug())
            }
            ConstGeneric::RightShift(lhs, rhs) => {
                format!("({} >> {})", lhs.pretty_debug(), rhs.pretty_debug())
            }
        }
    }
}

impl PrettyDebug for ConstGenericWithId {
    fn pretty_debug(&self) -> String {
        self.inner.pretty_debug()
    }
}

impl PrettyDebug for Expression {
    fn pretty_debug(&self) -> String {
        self.kind.pretty_debug()
    }
}

impl PrettyDebug for ExprKind {
    fn pretty_debug(&self) -> String {
        match &self {
            crate::ExprKind::Error => "{error}".to_string(),
            crate::ExprKind::Identifier(name_id) => name_id.pretty_debug(),
            crate::ExprKind::IntLiteral(value, _) => format!("{value}"),
            crate::ExprKind::BoolLiteral(value) => format!("{value}"),
            crate::ExprKind::TriLiteral(value) => format!("{value:?}"),
            crate::ExprKind::TypeLevelBool(name_id) => name_id.pretty_debug(),
            crate::ExprKind::TypeLevelInteger(name_id) => name_id.pretty_debug(),
            crate::ExprKind::TupleLiteral(inner) => {
                format!("({})", inner.iter().map(|i| i.pretty_debug()).join(", "))
            }
            crate::ExprKind::ArrayLiteral(inner) => {
                format!("[{}]", inner.iter().map(|i| i.pretty_debug()).join(", "))
            }
            crate::ExprKind::ArrayShorthandLiteral(inner, size) => {
                format!("[{}; {}]", inner.pretty_debug(), size.pretty_debug())
            }
            crate::ExprKind::Index(base, idx) => {
                format!("{}[{}]", base.pretty_debug(), idx.pretty_debug())
            }
            crate::ExprKind::Incomplete(_, inner) => {
                match inner {
                    IncompleteExpression::IncompleteDot { base, has_inst: _, has_depth: _ } => format!("{}.(incomplete)", base.pretty_debug())
                }
            }
            crate::ExprKind::RangeIndex { target, start, end } => {
                format!(
                    "{}[{}..{}]",
                    target.pretty_debug(),
                    start.pretty_debug(),
                    end.pretty_debug()
                )
            }
            crate::ExprKind::TupleIndex(base, idx) => {
                format!("{}.{}", base.pretty_debug(), idx)
            }
            crate::ExprKind::FieldAccess(base, field) => {
                format!("{}.{}", base.pretty_debug(), field)
            }
            crate::ExprKind::TypeCast(base, ty) => {
                format!("{} as {}", base.pretty_debug(), ty.pretty_debug())
            }
            crate::ExprKind::MethodCall {
                target,
                sugar_info: _,
                name,
                args,
                call_kind: _,
                turbofish,
                safety,
            } => {
                code! {
                    [0] format!("{}{}", if *safety == Safety::Unsafe { "unsafe " } else { "" }, target.pretty_debug());
                    [1]    format!(".{name}<{}>", turbofish.pretty_debug());
                    [1]    args.pretty_debug().to_string()
                }.to_string()
            }
            crate::ExprKind::Call {
                kind: _,
                callee,
                args,
                turbofish,
                safety,
                verilog_attr_groups: _,
            } => {
                code! {
                    [0] format!("{}{}::<{}>{}", if *safety == Safety::Unsafe { "unsafe " } else { "" }, callee.pretty_debug(), turbofish.pretty_debug(), args.pretty_debug());
                }.to_string()
            }
            crate::ExprKind::AssociatedCall {
                kind: _,
                callee,
                callee_ty: _,
                name,
                args,
                turbofish,
                safety,
            } => {
                code! {
                    [0] format!("{}{}::{}::<{}>{}", if *safety == Safety::Unsafe { "unsafe " } else { "" }, callee.pretty_debug(), name.pretty_debug(), turbofish.pretty_debug(), args.pretty_debug());
                }.to_string()
            }
            crate::ExprKind::BinaryOperator(lhs, op, rhs) => {
                format!("({} {} {})", lhs.pretty_debug(), op, rhs.pretty_debug())
            },
            crate::ExprKind::UnaryOperator(op, rhs) => format!("{op}{}", rhs.pretty_debug()),
            crate::ExprKind::Match(expr, branches) => {
                code!{
                    [0] format!("match {} {{", expr.pretty_debug());
                    [1]     branches.iter().map(|(pat, if_cond, expr)| {
                        let if_cond = match if_cond {
                            Some(c) => format!(" if {}", c.pretty_debug()),
                            None => "".to_string(),
                        };
                        format!("{}{if_cond} => {},", pat.pretty_debug(), expr.pretty_debug())
                    }).join("\n");
                    [0] "}"
                }.to_string()
            },
            crate::ExprKind::ConstTypeExpr(block) => {
                format!("{{ {} }}", block.pretty_debug())
            },
            crate::ExprKind::Block(block) => {
                code!{
                    [0] "{";
                    [1]    block.statements.iter().map(|stmt| stmt.pretty_debug()).join("\n");
                    [1]    block.result.pretty_debug();
                    [0] "}"
                }.to_string()
            },
            crate::ExprKind::If { cond, on_true, on_false } => code! {
                [0] format!("if {} {{", cond.pretty_debug());
                [1]    on_true.pretty_debug();
                [0] "} else {";
                [1]    on_false.pretty_debug();
                [0] "}";
            }.to_string(),
            crate::ExprKind::TypeLevelIf { cond, on_true, on_false } => {
                code!{
                    [0] format!("gen if {} {{", cond.pretty_debug());
                    [1]    on_true.pretty_debug();
                    [0] "} else {";
                    [1]    on_false.pretty_debug();
                    [0] "}";
                }.to_string()
            }
            crate::ExprKind::TypeLevelMatch { expression, branches } => {
                code!{
                    [0] format!("gen match {} {{", expression.pretty_debug());
                    [1]     branches.iter().map(|(pat, expr)| format!(
                                "{} => {},",
                                pat.pretty_debug(),
                                expr.pretty_debug(),
                            )).join("\n");
                    [0] "}";
                }.to_string()
            }
            crate::ExprKind::PipelineRef {
                stage: _,
                name: _,
                declares_name: _,
                depth_typeexpr_id: _,
            } => "[pipeline ref omitted]".to_string(),
            crate::ExprKind::LambdaDef {
                unit_kind,
                lambda_type,
                type_params,
                outer_generic_params: captured_generic_params,
                lambda_unit,
                arguments,
                body,
                captures: _,
                clock: _,
            } => {
                code!{
                    [0] format!("lambda: {unit_kind:?} ({}) {{", arguments.iter().map(PrettyDebug::pretty_debug).join(", "));
                    [1]     body.pretty_debug();
                    [0] "}";
                    [2] format!("Lambda creates {}", lambda_unit.pretty_debug());
                    [2] format!(
                        "with type {}<Args: {}, Captures: {}, Outer: {}>",
                        lambda_type.pretty_debug(),
                        type_params.arg.iter().map(PrettyDebug::pretty_debug).join(", "),
                        type_params.captures.iter().map(PrettyDebug::pretty_debug).join(", "),
                        type_params.outer.iter().map(PrettyDebug::pretty_debug).join(", ")
                    );
                    [2] format!(
                        "and captures type params [{}]",
                        captured_generic_params.iter().map(PrettyDebug::pretty_debug).join(", ")
                    );
                }.to_string()
            },
            crate::ExprKind::StageValid => "stage.valid".to_string(),
            crate::ExprKind::StageReady => "stage.ready".to_string(),
            crate::ExprKind::StaticUnreachable(_) => {
                "<STATIC_UNREACHABLE>".to_string()
            },

            crate::ExprKind::Null => "<NULL>".to_string(),
        }
    }
}

impl PrettyDebug for Generic {
    fn pretty_debug(&self) -> String {
        match self {
            Generic::Named(name_id) => name_id.pretty_debug(),
            Generic::Hidden(id) => format!("<hidden#{}>", id.0),
        }
    }
}

impl PrettyDebug for TypeParam {
    fn pretty_debug(&self) -> String {
        let Self {
            name,
            trait_bounds,
            meta,
            default,
        } = self;

        format!(
            "{meta:?} {}: ({}) = ({})",
            name.pretty_debug(),
            trait_bounds
                .iter()
                .map(PrettyDebug::pretty_debug)
                .join(", "),
            default
                .as_deref()
                .map(|d| format!(" = {}", d.pretty_debug()))
                .unwrap_or_default(),
        )
    }
}

impl PrettyDebug for TraitSpec {
    fn pretty_debug(&self) -> String {
        format!("{self}")
    }
}

impl PrettyDebug for OuterLambdaParam {
    fn pretty_debug(&self) -> String {
        let Self {
            name_in_lambda,
            name_in_body,
        } = self;
        format!("(in def: {name_in_lambda}, in body: {name_in_body})")
    }
}

impl PrettyDebug for Pattern {
    fn pretty_debug(&self) -> String {
        match &self.kind {
            crate::PatternKind::Integer(val) => format!("{val}"),
            crate::PatternKind::Bool(val) => format!("{val}"),
            crate::PatternKind::Bound {
                name,
                inner: Some(pat),
                pre_declared: _,
                wire,
            } => format!(
                "{}{} @ {}",
                if wire.is_some() { "wire " } else { "" },
                name.pretty_debug(),
                pat.pretty_debug()
            ),
            crate::PatternKind::Bound {
                name,
                inner: None,
                pre_declared: _,
                wire,
            } => format!(
                "{}{}",
                if wire.is_some() { "wire " } else { "" },
                name.pretty_debug()
            ),
            crate::PatternKind::Tuple(inner) => {
                format!("({})", inner.iter().map(|i| i.pretty_debug()).join(", "))
            }
            crate::PatternKind::Array(inner) => {
                format!("[{}]", inner.iter().map(|i| i.pretty_debug()).join(", "))
            }
            crate::PatternKind::Type(base, args) => format!(
                "{}{{{}}}",
                base.pretty_debug(),
                args.iter().map(|arg| arg.pretty_debug()).join(", ")
            ),
        }
    }
}

impl PrettyDebug for Statement {
    fn pretty_debug(&self) -> String {
        match self {
            Statement::Error => "{error}".to_string(),
            Statement::Binding(Binding { pattern, ty, value }) => {
                format!(
                    "let {}: {} = {};",
                    pattern.pretty_debug(),
                    ty.pretty_debug(),
                    value.pretty_debug()
                )
            }
            Statement::Expression(expr) => format!("{};", expr.pretty_debug()),
            Statement::Memory(Memory {
                keyword: _,
                ty,
                array_typespec_id: _,
                initial,
                ports,
            }) => code! [
                [0] format!(
                        "memory{} {}",
                        if let Some(t) = ty { format!(": {}", t.pretty_debug()) } else { String::new() },
                        initial
                            .as_ref()
                            .map(|val| format!("initial ({})", val.pretty_debug()))
                            .unwrap_or(String::new()),
                    );
                [0] "{";
                [1]     ports.0
                            .iter()
                            .map(|port| format!(
                                "{}: {},",
                                port.name.pretty_debug(),
                                port.ty.pretty_debug(),
                            ))
                            .join("\n");
                [0] "};";
            ]
            .to_string(),
            Statement::Register(Register {
                keyword: _,
                pattern,
                clock,
                reset,
                initial,
                value,
                value_type,
                attributes,
            }) => {
                format!(
                    "{} reg({}) {}: {}{}{} = {};",
                    attributes.pretty_debug(),
                    clock.pretty_debug(),
                    pattern.pretty_debug(),
                    value_type.pretty_debug(),
                    reset
                        .as_ref()
                        .map(|(trig, val)| format!(
                            "reset ({}: {})",
                            trig.pretty_debug(),
                            val.pretty_debug()
                        ))
                        .unwrap_or(String::new()),
                    initial
                        .as_ref()
                        .map(|val| format!("initial ({})", val.pretty_debug()))
                        .unwrap_or(String::new()),
                    value.pretty_debug()
                )
            }
            Statement::Declaration(names) => {
                format!(
                    "decl {};",
                    names.iter().map(PrettyDebug::pretty_debug).join(", ")
                )
            }
            Statement::PipelineRegMarker(_) => "[pipeline reg marker]".to_string(),
            Statement::Label(name) => format!("'{};", name.pretty_debug()),
            Statement::Assert(loc) => format!("assert {};", loc.pretty_debug()),
        }
    }
}

impl PrettyDebug for PatternArgument {
    fn pretty_debug(&self) -> String {
        format!("{}: {}", self.target, self.value.pretty_debug())
    }
}

impl<Inner> PrettyDebug for NamedArgument<Inner>
where
    Inner: PrettyDebug,
{
    fn pretty_debug(&self) -> String {
        match self {
            NamedArgument::Full(name, val) => {
                format!("{}: {}", name.pretty_debug(), val.pretty_debug())
            }
            NamedArgument::Short(_, value) => value.pretty_debug(),
        }
    }
}

impl<Inner> PrettyDebug for ArgumentList<Inner>
where
    Inner: PrettyDebug,
{
    fn pretty_debug(&self) -> String {
        match self {
            ArgumentList::Named(args) => code! {
                [0] "{ ";
                [1] args.iter().map(|arg| arg.pretty_debug()).join("\n");
                [0] " }";
            }
            .to_string(),
            ArgumentList::Positional(args) => code! {
                [0] "(";
                [1]     args.iter().map(|arg| arg.pretty_debug()).join("\n");
                [0] ")"
            }
            .to_string(),
        }
    }
}

impl<T> PrettyDebug for &T
where
    T: PrettyDebug,
{
    fn pretty_debug(&self) -> String {
        (*self).pretty_debug()
    }
}

impl<T> PrettyDebug for Loc<T>
where
    T: PrettyDebug,
{
    fn pretty_debug(&self) -> String {
        self.inner.pretty_debug()
    }
}

impl<T> PrettyDebug for Option<T>
where
    T: PrettyDebug,
{
    fn pretty_debug(&self) -> String {
        match self {
            Some(inner) => inner.pretty_debug(),
            None => String::new(),
        }
    }
}
