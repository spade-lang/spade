use itertools::Itertools;
use spade_common::location_info::{Loc, WithLocation};
use spade_common::name::{Identifier, NameID};

use spade_diagnostics::Diagnostic;
use spade_hir::{ImplTarget, TypeExpression, TypeSpec};
use spade_types::KnownType;

use crate::equation::TypeVar;
use crate::traits::{TraitImpl, TraitImplList};

#[derive(Debug, PartialEq, Eq)]
pub enum FunctionLikeName {
    Method(Identifier),
    Free(NameID),
}
impl std::fmt::Display for FunctionLikeName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FunctionLikeName::Method(n) => write!(f, "{n}"),
            FunctionLikeName::Free(n) => write!(f, "{n}"),
        }
    }
}

pub trait IntoImplTarget {
    fn into_impl_target(&self) -> Option<ImplTarget>;
}

impl IntoImplTarget for KnownType {
    fn into_impl_target(&self) -> Option<ImplTarget> {
        match self {
            KnownType::Named(name) => Some(ImplTarget::Named(name.clone())),
            KnownType::Integer(_) | KnownType::Bool(_) => None,
            KnownType::Tuple => None,
            KnownType::Array => Some(ImplTarget::Array),
            KnownType::Wire => Some(ImplTarget::Wire),
            KnownType::Inverted => Some(ImplTarget::Inverted),
        }
    }
}

/// Attempts to look up which function to call when calling `method` on a var
/// of type `self_type`.
/// Returns the method to call if it is fully known and exists, an error if there is
/// no such method, or None if the method is ambiguous
pub fn select_method(
    expr: Loc<()>,
    self_type: &TypeVar,
    method: &Loc<Identifier>,
    trait_impls: &TraitImplList,
) -> Result<Option<Loc<NameID>>, Diagnostic> {
    let target = self_type
        .expect_known::<_, _, _, Option<ImplTarget>>(
            |ktype, _params| ktype.into_impl_target(),
            || None,
        )
        .ok_or_else(|| Diagnostic::error(expr, format!("{self_type} does not have any methods")))?;

    // Go to the item list to check if this name has any methods
    let impls = trait_impls.inner.get(&target).cloned().unwrap_or(vec![]);

    // Gather all the candidate methods which we may want to call.
    let (matched_candidates, maybe_candidates, unmatched_candidates): (Vec<_>, Vec<_>, Vec<_>) =
        impls
            .iter()
            .flat_map(
                |TraitImpl {
                     name: _,
                     type_params: _,
                     impl_block: r#impl,
                 }| {
                    r#impl.fns.iter().map(move |(fn_name, actual_fn)| {
                        if fn_name == &method.inner {
                            let is_overlapping = spec_is_overlapping(&r#impl.target, self_type);
                            let selected = actual_fn.0.clone().at_loc(&actual_fn.1);
                            match is_overlapping {
                                Overlap::Yes => (Some(selected), None, None),
                                Overlap::Maybe => (None, Some(selected), None),
                                Overlap::No => (None, None, Some(&r#impl.target)),
                            }
                        } else {
                            (None, None, None)
                        }
                    })
                },
            )
            .multiunzip();

    let matched_candidates = matched_candidates
        .into_iter()
        .filter_map(|x| x)
        .collect::<Vec<_>>();
    let maybe_candidates = maybe_candidates
        .into_iter()
        .filter_map(|x| x)
        .collect::<Vec<_>>();
    let unmatched_candidates = unmatched_candidates
        .into_iter()
        .filter_map(|x| x)
        .collect::<Vec<_>>();

    if !maybe_candidates.is_empty() {
        return Ok(None);
    }

    let final_method = match matched_candidates.as_slice() {
        [name] => name,
        [] => {
            let mut d =
                Diagnostic::error(method, format!("`{self_type}` has no method `{method}`"))
                    .primary_label("No such method")
                    .secondary_label(expr, format!("This has type `{self_type}`"));

            match unmatched_candidates.as_slice() {
                [] => {}
                [one] => {
                    d.add_help(format!("The method exists for `{one}`"));
                }
                multiple => {
                    d.add_help(format!(
                        "The method exists for `{}`, and `{}`",
                        multiple[0..multiple.len() - 1]
                            .iter()
                            .map(|t| format!("`{t}`"))
                            .join(", "),
                        multiple.last().unwrap()
                    ));
                }
            };
            return Err(d);
        }
        _ => {
            return Err(Diagnostic::bug(
                method,
                "Multiple candidates satisfy this method",
            ))
        }
    };

    Ok(Some(final_method.clone()))
}

enum Overlap {
    /// We know for sure if there is overlap
    Yes,
    No,
    /// We Are not sure yet if there is overlap. This happens if we have X<_>
    /// satisfies but X<T> where T is concrete
    Maybe,
}

trait IterExt {
    fn all_overlap(self) -> Overlap;
}

impl<T> IterExt for T
where
    T: Iterator<Item = Overlap>,
{
    fn all_overlap(self) -> Overlap {
        for o in self {
            match o {
                Overlap::Yes => {}
                Overlap::No => return Overlap::No,
                Overlap::Maybe => return Overlap::Maybe,
            }
        }
        Overlap::Yes
    }
}

fn specs_are_overlapping(specs: &[Loc<TypeSpec>], vars: &[TypeVar]) -> Overlap {
    if specs.len() == vars.len() {
        specs
            .iter()
            .zip(vars)
            .map(|(s, v)| spec_is_overlapping(s, v))
            .all_overlap()
    } else {
        Overlap::No
    }
}

fn expr_is_overlapping(expr: &TypeExpression, var: &TypeVar) -> Overlap {
    match (&expr, var) {
        (TypeExpression::Integer(eval), TypeVar::Known(_, KnownType::Integer(vval), _)) => {
            if eval == vval {
                Overlap::Yes
            } else {
                Overlap::No
            }
        }
        (TypeExpression::Integer(_), TypeVar::Unknown(_, _, _, _)) => Overlap::Maybe,
        (TypeExpression::Integer(_), _) => {
            unreachable!("Non integer and non-generic type matched with integer")
        }
        (TypeExpression::TypeSpec(s), v) => spec_is_overlapping(s, v),
        (TypeExpression::ConstGeneric(_), _) => {
            unreachable!("Const generic in expr_is_overlapping")
        }
    }
}

fn exprs_are_overlapping(exprs: &[Loc<TypeExpression>], vars: &[TypeVar]) -> Overlap {
    if exprs.len() == vars.len() {
        exprs
            .iter()
            .zip(vars)
            .map(|(e, v)| expr_is_overlapping(e, v))
            .all_overlap()
    } else {
        Overlap::No
    }
}

fn spec_is_overlapping(spec: &TypeSpec, var: &TypeVar) -> Overlap {
    match (spec, var) {
        // Generics overlap with anything
        (TypeSpec::Generic(_), _) => Overlap::Yes,
        // For anything non-generic, we need a concrete type to know if there is overlap.
        (_, TypeVar::Unknown(_, _, _, _)) => Overlap::Maybe,
        (
            TypeSpec::Declared(specname, specparams),
            TypeVar::Known(_, KnownType::Named(varname), varparams),
        ) => {
            if &specname.inner == varname {
                exprs_are_overlapping(specparams, varparams)
            } else {
                Overlap::No
            }
        }
        (TypeSpec::Declared(_, _), _) => Overlap::No,

        // NOTE: This block currently cannot be tested because we can't add methods to
        // anything other than declared types
        (TypeSpec::Tuple(sspecs), TypeVar::Known(_, KnownType::Tuple, vvars)) => {
            specs_are_overlapping(sspecs, vvars)
        }
        (TypeSpec::Tuple(_), _) => Overlap::No,
        (TypeSpec::Array { inner, size }, TypeVar::Known(_, KnownType::Array, vvars)) => [
            spec_is_overlapping(inner, &vvars[0]),
            expr_is_overlapping(size, &vvars[1]),
        ]
        .into_iter()
        .all_overlap(),
        (TypeSpec::Array { .. }, _) => Overlap::No,
        // Unit types cannot have methods right now and KnownType cannot be `unit`, so
        // for now we'll always return false from this
        // FIXME: Type inference ignores TypeSpec::Unit, so presumably those are very unsupported
        // anyway
        (TypeSpec::Unit(_), _) => Overlap::No,
        (TypeSpec::Inverted(sinner), TypeVar::Known(_, KnownType::Inverted, vinner))
        | (TypeSpec::Wire(sinner), TypeVar::Known(_, KnownType::Wire, vinner)) => {
            spec_is_overlapping(sinner, &vinner[0])
        }
        (TypeSpec::Inverted(_), _) => Overlap::No,
        (TypeSpec::Wire(_), _) => Overlap::No,

        // TraitSelf cannot appear as the impl target, so what we do here is irrelevant
        (TypeSpec::TraitSelf(_), TypeVar::Known(_, _, _)) => {
            unreachable!("Trait self in impl target")
        }
        (TypeSpec::Wildcard(_), _) => unreachable!("Wildcard during type spec overlap check"),
    }
}
