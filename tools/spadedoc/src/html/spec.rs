use std::borrow::Cow;

use color_eyre::eyre::Result;
use rinja::Template;
use spade_common::name::Identifier;
use spade_hir::{ConstGeneric, TraitSpec, TypeExpression, TypeSpec};

#[derive(Debug, Template)]
pub enum Spec<'r> {
    /// ```rinja
    /// {{ name.0 }}
    /// {% if !type_args.is_empty() %}
    /// <{{ type_args|join(", ") }}>
    /// {% endif %}
    /// ```
    #[template(ext = "html", in_doc = true)]
    Declared {
        name: Cow<'r, Identifier>,
        type_args: Vec<Spec<'r>>,
    },
    /// ```rinja
    /// {{ self.0 }}
    /// ```
    #[template(ext = "html", in_doc = true)]
    Number(i64),
    /// ```rinja
    /// [{{ ty.render()?|safe }}; {{+ size.render()?|safe }}]
    /// ```
    #[template(ext = "html", in_doc = true)]
    Array {
        ty: Box<Spec<'r>>,
        size: Box<Spec<'r>>,
    },
    /// ```rinja
    /// ({{ self.0|join(", ") }})
    /// ```
    #[template(ext = "html", in_doc = true)]
    Tuple(Vec<Spec<'r>>),
    /// ```rinja
    /// {{"inv "}}{{ self.0.render()?|safe }}
    /// ```
    #[template(ext = "html", in_doc = true)]
    Inverted(Box<Spec<'r>>),
    /// ```rinja
    /// &{{ self.0.render()?|safe }}
    /// ```
    #[template(ext = "html", in_doc = true)]
    Wire(Box<Spec<'r>>),

    /// ```rinja
    /// {{ "{" }}{{ self.0.render()?|safe }}{{ "}" }}
    /// ```
    #[template(ext = "html", in_doc = true)]
    ConstGenericRoot(Box<Spec<'r>>),

    /// ```rinja
    /// ({{ self.0.render()?|safe }})
    /// ```
    #[template(ext = "html", in_doc = true)]
    Parenthesized(Box<Spec<'r>>),

    /// ```rinja
    /// {{ self.lhs.render()?|safe }} {{" "}}{{ self.op }}{{" "}} {{ self.rhs.render()?|safe }}
    /// ```
    #[template(ext = "html", in_doc = true)]
    ConstGenericBinOp {
        lhs: Box<Spec<'r>>,
        op: String,
        rhs: Box<Spec<'r>>,
    },

    /// ```rinja
    /// {{ self.name }}({{ self.args|join(", ") }})
    /// ```
    #[template(ext = "html", in_doc = true)]
    ConstGenericFunc { name: String, args: Vec<Spec<'r>> },
}

impl<'r> Spec<'r> {
    pub fn mirror_typespec(spec: &'r TypeSpec) -> Result<Self> {
        match spec {
            TypeSpec::Array { inner, size } => Ok(Spec::Array {
                ty: Box::new(Self::mirror_typespec(inner)?),
                size: Box::new(Self::mirror_typeexpr(size)?),
            }),
            TypeSpec::Declared(name, args) => Ok(Spec::Declared {
                name: Cow::Owned(name.inner.1.tail()),
                type_args: args
                    .iter()
                    .map(|s| Self::mirror_typeexpr(&s))
                    .collect::<Result<Vec<_>>>()?,
            }),
            TypeSpec::Generic(name) => Ok(Spec::Declared {
                name: Cow::Owned(name.inner.1.tail()),
                type_args: vec![],
            }),
            TypeSpec::Inverted(inner) => {
                Ok(Spec::Inverted(Box::new(Self::mirror_typespec(inner)?)))
            }
            TypeSpec::Wire(inner) => Ok(Spec::Wire(Box::new(Self::mirror_typespec(inner)?))),
            TypeSpec::Tuple(specs) => Ok(Spec::Tuple(
                specs
                    .into_iter()
                    .map(|s| Self::mirror_typespec(s))
                    .collect::<Result<Vec<_>>>()?,
            )),
            _ => todo!("{spec}"),
        }
    }

    pub fn mirror_typeexpr(expr: &'r TypeExpression) -> Result<Self> {
        match expr {
            TypeExpression::Integer(i) => {
                Ok(Spec::Number(i.iter_u64_digits().next().unwrap() as i64))
            }
            TypeExpression::TypeSpec(ts) => Ok(Self::mirror_typespec(ts)?),
            TypeExpression::ConstGeneric(cg) => Ok(Self::mirror_constgeneric(cg, true, false)?),
        }
    }

    /// We use `root` so we know whether this is the outermost const generic and thus needs `{}` if
    /// not just a number or name.
    pub fn mirror_constgeneric(
        expr: &'r ConstGeneric,
        root: bool,
        needs_surround: bool,
    ) -> Result<Self> {
        let mut spec = match expr {
            ConstGeneric::Name(name) => Self::Declared {
                name: Cow::Owned(name.inner.1.tail()),
                type_args: vec![],
            },
            ConstGeneric::Const(const_number) => {
                Self::Number(const_number.iter_u64_digits().next().unwrap() as i64)
            }
            ConstGeneric::Add(lhs, rhs) => Self::ConstGenericBinOp {
                lhs: Self::mirror_constgeneric(lhs, false, false)?.into(),
                op: "+".into(),
                rhs: Self::mirror_constgeneric(rhs, false, false)?.into(),
            },
            ConstGeneric::Sub(lhs, rhs) => Self::ConstGenericBinOp {
                lhs: Self::mirror_constgeneric(lhs, false, false)?.into(),
                op: "-".into(),
                rhs: Self::mirror_constgeneric(rhs, false, true)?.into(),
            },
            ConstGeneric::Mul(lhs, rhs) => Self::ConstGenericBinOp {
                lhs: Self::mirror_constgeneric(lhs, false, true)?.into(),
                op: "*".into(),
                rhs: Self::mirror_constgeneric(rhs, false, true)?.into(),
            },
            ConstGeneric::Div(lhs, rhs) => Self::ConstGenericBinOp {
                lhs: Self::mirror_constgeneric(lhs, false, true)?.into(),
                op: "/".into(),
                rhs: Self::mirror_constgeneric(rhs, false, true)?.into(),
            },
            ConstGeneric::Mod(lhs, rhs) => Self::ConstGenericBinOp {
                lhs: Self::mirror_constgeneric(lhs, false, true)?.into(),
                op: "%".into(),
                rhs: Self::mirror_constgeneric(rhs, false, true)?.into(),
            },
            ConstGeneric::UintBitsToFit(arg) => Self::ConstGenericFunc {
                name: "uint_bits_to_fit".into(),
                args: vec![Self::mirror_constgeneric(arg, false, false)?],
            },
            ConstGeneric::Eq(lhs, rhs) => Self::ConstGenericBinOp {
                lhs: Self::mirror_constgeneric(lhs, false, true)?.into(),
                op: "==".into(),
                rhs: Self::mirror_constgeneric(rhs, false, true)?.into(),
            },
            ConstGeneric::NotEq(lhs, rhs) => Self::ConstGenericBinOp {
                lhs: Self::mirror_constgeneric(lhs, false, true)?.into(),
                op: "!=".into(),
                rhs: Self::mirror_constgeneric(rhs, false, true)?.into(),
            },
        };
        if root {
            Ok(Self::ConstGenericRoot(Box::new(spec)))
        } else {
            if needs_surround
                && !matches!(
                    expr,
                    ConstGeneric::Name(_) | ConstGeneric::Const(_) | ConstGeneric::UintBitsToFit(_)
                )
            {
                spec = Self::Parenthesized(Box::new(spec));
            }
            Ok(spec)
        }
    }

    pub fn mirror_traitspec(spec: &'r TraitSpec) -> Result<Spec<'r>> {
        Ok(Spec::Declared {
            name: Cow::Owned(Identifier(spec.name.to_string())),
            type_args: spec
                .type_params
                .as_ref()
                .map(|params| {
                    params
                        .iter()
                        .map(|type_param| Spec::mirror_typeexpr(type_param))
                        .collect::<Result<Vec<_>>>()
                })
                .unwrap_or(Ok(vec![]))?,
        })
    }
}
