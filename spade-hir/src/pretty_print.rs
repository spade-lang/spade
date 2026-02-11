use itertools::Itertools;
use spade_common::{
    location_info::Loc,
    name::{Identifier, NameID},
};
use spade_types::meta_types::MetaType;

use crate::{
    symbol_table::GenericArg, ConstGeneric, Generic, Parameter, ParameterList, TraitName,
    TraitSpec, TypeExpression, TypeParam, TypeSpec, UnitHead, UnitKind,
};

pub trait MaybePrettyPrint {
    fn maybe_pretty_print(&self) -> Option<String>;

    fn with_trailing_space(&self) -> String {
        match self.maybe_pretty_print() {
            Some(s) => format!("{} ", s),
            None => "".to_string(),
        }
    }
}

pub trait PrettyPrint {
    fn pretty_print(&self) -> String;
}

impl PrettyPrint for NameID {
    fn pretty_print(&self) -> String {
        format!("{}", self.1.tail())
    }
}

impl PrettyPrint for Identifier {
    fn pretty_print(&self) -> String {
        format!("{self}")
    }
}

impl MaybePrettyPrint for MetaType {
    fn maybe_pretty_print(&self) -> Option<String> {
        match self {
            MetaType::Any => Some("#any".to_string()),
            MetaType::Type => None,
            MetaType::Number => Some("#number".to_string()),
            MetaType::Int => Some("#int".to_string()),
            MetaType::Uint => Some("#uint".to_string()),
            MetaType::Bool => Some("#bool".to_string()),
            MetaType::Str => Some("#str".to_string()),
        }
    }
}

impl PrettyPrint for GenericArg {
    fn pretty_print(&self) -> String {
        match self {
            GenericArg::TypeName { name, traits } => {
                let traits = if traits.is_empty() {
                    "".to_string()
                } else {
                    format!(
                        ": {}",
                        traits
                            .iter()
                            .map(|t| format!("{}", t.pretty_print()))
                            .join(", ")
                    )
                };

                format!("{}{}", name, traits)
            }
            GenericArg::TypeWithMeta { name, meta } => {
                let meta = match meta {
                    spade_types::meta_types::MetaType::Any => "#any ",
                    spade_types::meta_types::MetaType::Type => "",
                    spade_types::meta_types::MetaType::Number => "#number ",
                    spade_types::meta_types::MetaType::Int => "#int ",
                    spade_types::meta_types::MetaType::Uint => "#uint ",
                    spade_types::meta_types::MetaType::Bool => "#bool ",
                    spade_types::meta_types::MetaType::Str => "#str ",
                };

                format!("{}{}", meta, name.pretty_print())
            }
        }
    }
}

impl PrettyPrint for TraitName {
    fn pretty_print(&self) -> String {
        match self {
            TraitName::Named(name) => name.pretty_print(),
            TraitName::Anonymous(_) => "[Anonymous]".to_string(),
        }
    }
}

impl PrettyPrint for TraitSpec {
    fn pretty_print(&self) -> String {
        let tp = match &self.type_params {
            Some(tp) => format!("<{}>", tp.iter().map(|tp| tp.pretty_print()).join(", ")),
            None => "".to_string(),
        };
        format!("{}{}", self.name.pretty_print(), tp)
    }
}
impl PrettyPrint for ConstGeneric {
    fn pretty_print(&self) -> String {
        match self {
            ConstGeneric::Name(n) => n.pretty_print(),
            ConstGeneric::Bool(b) => format!("{b}"),
            ConstGeneric::Int(big_int) => format!("{big_int}"),
            ConstGeneric::Str(s) => format!("{s:?}"),
            ConstGeneric::Add(lhs, rhs) => {
                format!("({} + {})", lhs.pretty_print(), rhs.pretty_print())
            }
            ConstGeneric::Sub(lhs, rhs) => {
                format!("({} - {})", lhs.pretty_print(), rhs.pretty_print())
            }
            ConstGeneric::Mul(lhs, rhs) => {
                format!("({} * {})", lhs.pretty_print(), rhs.pretty_print())
            }
            ConstGeneric::Div(lhs, rhs) => {
                format!("({} / {})", lhs.pretty_print(), rhs.pretty_print())
            }
            ConstGeneric::Mod(lhs, rhs) => {
                format!("({} % {})", lhs.pretty_print(), rhs.pretty_print())
            }
            ConstGeneric::UintBitsToFit(inner) => {
                format!("{}", inner.pretty_print())
            }
            ConstGeneric::Eq(lhs, rhs) => {
                format!("({} == {})", lhs.pretty_print(), rhs.pretty_print())
            }
            ConstGeneric::NotEq(lhs, rhs) => {
                format!("({} != {})", lhs.pretty_print(), rhs.pretty_print())
            }
            ConstGeneric::LogicalNot(inner) => {
                format!("(!{})", inner.pretty_print())
            }
            ConstGeneric::LogicalAnd(lhs, rhs) => {
                format!("({} && {})", lhs.pretty_print(), rhs.pretty_print())
            }
            ConstGeneric::LogicalOr(lhs, rhs) => {
                format!("({} || {})", lhs.pretty_print(), rhs.pretty_print())
            }
            ConstGeneric::LogicalXor(lhs, rhs) => {
                format!("({} ^^ {})", lhs.pretty_print(), rhs.pretty_print())
            }
        }
    }
}

impl PrettyPrint for TypeExpression {
    fn pretty_print(&self) -> String {
        match self {
            TypeExpression::Bool(val) => format!("{val}"),
            TypeExpression::Integer(val) => format!("{val}"),
            TypeExpression::String(val) => format!("{val:?}"),
            TypeExpression::TypeSpec(ts) => ts.pretty_print(),
            TypeExpression::ConstGeneric(cg) => cg.pretty_print(),
        }
    }
}

impl PrettyPrint for TypeSpec {
    fn pretty_print(&self) -> String {
        match self {
            TypeSpec::Declared(base, args) => {
                let args = if !args.is_empty() {
                    format!("<{}>", args.iter().map(|arg| arg.pretty_print()).join(", "))
                } else {
                    "".to_string()
                };
                format!("{}{}", base.pretty_print(), args)
            }
            TypeSpec::Generic(g) => g.pretty_print(),
            TypeSpec::Tuple(inner) => format!(
                "({})",
                inner.iter().map(|arg| arg.pretty_print()).join(", ")
            ),
            TypeSpec::Array { inner, size } => {
                format!("[{}; {}]", inner.pretty_print(), size.pretty_print())
            }
            TypeSpec::Inverted(inner) => format!("inv {}", inner.pretty_print()),
            TypeSpec::Wire(inner) => format!("&{}", inner.pretty_print()),
            TypeSpec::TraitSelf(_) => format!("self"),
            TypeSpec::Wildcard(_) => format!("_"),
        }
    }
}

impl PrettyPrint for Generic {
    fn pretty_print(&self) -> String {
        match self {
            Generic::Named(name_id) => name_id.pretty_print(),
            Generic::Hidden(_) => "(hidden generic)".to_string(),
        }
    }
}

impl PrettyPrint for TypeParam {
    fn pretty_print(&self) -> String {
        let Self {
            name,
            trait_bounds,
            meta,
            default,
        } = self;

        let traits = if trait_bounds.is_empty() {
            "".to_string()
        } else {
            format!(
                "<{}>",
                trait_bounds.iter().map(|tb| tb.pretty_print()).join(", ")
            )
        };

        let default = match default {
            Some(d) => format!(" = {}", d.pretty_print()),
            None => "".to_string(),
        };

        format!(
            "{}{}{traits}{default}",
            meta.with_trailing_space(),
            name.pretty_print(),
        )
    }
}

impl PrettyPrint for UnitKind {
    fn pretty_print(&self) -> String {
        match self {
            UnitKind::Function(crate::FunctionKind::Fn) => "fn".to_string(),
            UnitKind::Function(crate::FunctionKind::Struct) => "struct".to_string(),
            UnitKind::Function(crate::FunctionKind::Enum) => "enum variant".to_string(),
            UnitKind::Entity => "entity".to_string(),
            UnitKind::Pipeline {
                depth,
                depth_typeexpr_id: _,
            } => format!("pipeline({})", depth.pretty_print()),
        }
    }
}

impl PrettyPrint for UnitHead {
    fn pretty_print(&self) -> String {
        let Self {
            name,
            inputs,
            is_nonstatic_method: _,
            output_type,
            unit_type_params,
            hidden_type_params: _,
            scope_type_params: _,
            unit_kind,
            where_clauses: _,
            unsafe_marker,
            documentation: _,
            deprecation_note: _,
        } = self;
        let output_type = match output_type {
            Some(output_type) => format!(" -> {}", output_type.pretty_print()),
            None => "".to_string(),
        };
        let type_params = if unit_type_params.is_empty() {
            "".to_string()
        } else {
            format!(
                "<{}>",
                unit_type_params
                    .iter()
                    .map(|tp| tp.pretty_print())
                    .join(", ")
            )
        };
        let inputs = inputs.pretty_print();
        format!(
            "{}{} {}{}({}){}",
            if unsafe_marker.is_some() {
                "unsafe "
            } else {
                ""
            },
            unit_kind.pretty_print(),
            name,
            type_params,
            inputs,
            output_type
        )
    }
}

impl PrettyPrint for Parameter {
    fn pretty_print(&self) -> String {
        let Parameter {
            no_mangle: _,
            field_translator: _,
            name,
            ty,
        } = self;

        format!("{}: {}", name.pretty_print(), ty.pretty_print())
    }
}

impl PrettyPrint for ParameterList {
    fn pretty_print(&self) -> String {
        self.0.iter().map(|param| param.pretty_print()).join(", ")
    }
}

impl<T> PrettyPrint for &T
where
    T: PrettyPrint,
{
    fn pretty_print(&self) -> String {
        (*self).pretty_print()
    }
}

impl<T> PrettyPrint for Loc<T>
where
    T: PrettyPrint,
{
    fn pretty_print(&self) -> String {
        self.inner.pretty_print()
    }
}

impl<T> PrettyPrint for Option<T>
where
    T: PrettyPrint,
{
    fn pretty_print(&self) -> String {
        match self {
            Some(inner) => inner.pretty_print(),
            None => String::new(),
        }
    }
}
