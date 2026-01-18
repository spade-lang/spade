// Utilities related to argument matching between callers and callees. Lives in spade-hir
// because this is required twice in the compilation process: first during type inference,
// and then again during hir lowering

use itertools::Itertools;
use rustc_hash::FxHashSet as HashSet;
use spade_diagnostics::Diagnostic;

use spade_common::{location_info::Loc, name::Identifier};

use crate::expression::NamedArgument;
use crate::{ArgumentList, ParameterList, TypeParam, TypeSpec};

#[derive(Debug, PartialEq, Clone)]
pub enum ArgumentError {
    TooFewArguments {
        got: usize,
        expected: usize,
        missing: Vec<Identifier>,
        at: Loc<()>,
    },
    TooManyArguments {
        got: usize,
        expected: usize,
        extra: Vec<Loc<()>>,
        at: Loc<()>,
    },
    NoSuchArgument {
        name: Loc<Identifier>,
    },
    MissingArguments {
        missing: Vec<Identifier>,
        at: Loc<()>,
    },
    DuplicateNamedBindings {
        new: Loc<Identifier>,
        prev_loc: Loc<()>,
    },
}

impl From<ArgumentError> for Diagnostic {
    fn from(error: ArgumentError) -> Self {
        match error {
            ArgumentError::TooManyArguments {
                expected,
                got,
                extra,
                at,
            } => {
                let plural = if expected == 1 { "" } else { "s" };
                let mut base = Diagnostic::error(
                    at,
                    format!("Too many arguments. Expected {expected}, got {got}"),
                )
                .primary_label(format!("Expected {expected} argument{plural}"));

                for e in extra {
                    base = base.secondary_label(e, "Unexpected argument".to_string())
                }
                base
            }
            ArgumentError::TooFewArguments {
                expected,
                got,
                missing,
                at,
            } => {
                let missing_plural = if missing.len() == 1 { "" } else { "s" };

                let leading_comma = if got == 0 { "" } else { ", " };
                let suggestion = format!(
                    "{leading_comma}{}",
                    missing.iter().map(|p| format!("/* {p} */")).join(", ")
                );

                Diagnostic::error(
                    at,
                    format!("Too few arguments. Expected {expected}, got {got}"),
                )
                .primary_label(format!(
                    "Missing {count} argument{missing_plural}",
                    count = missing.len()
                ))
                .span_suggest_insert_after(
                    format!("Consider providing the argument{missing_plural}"),
                    at,
                    suggestion,
                )
            }
            ArgumentError::NoSuchArgument { name } => {
                Diagnostic::error(&name, format!("No such argument: {name}"))
                    .primary_label("No such argument")
            }
            ArgumentError::MissingArguments { mut missing, at } => {
                let plural = if missing.len() == 1 { "" } else { "s" };

                missing.sort_by_key(|arg| arg.as_str());

                let arg_list = missing.iter().map(|i| i.as_str()).join(", ");

                Diagnostic::error(at, format!("Missing argument{plural}: {arg_list}"))
                    .primary_label(format!("Missing argument{plural}: {arg_list}"))
            }
            ArgumentError::DuplicateNamedBindings { new, prev_loc } => {
                Diagnostic::error(&new, format!("{new} specified multiple times"))
                    .primary_label("Later specified here")
                    .secondary_label(prev_loc, "First specified here")
            }
        }
    }
}

pub enum ArgumentKind {
    Positional,
    Named,
    ShortNamed,
}

/// A resolved positional or named argument. Used by both value arguments and turbofishes.
/// TypeLike is the target type for arguments, and () for turbofishes
pub struct Argument<'a, T, TypeLike> {
    pub target: &'a Loc<Identifier>,
    pub value: &'a Loc<T>,
    pub target_type: &'a TypeLike,
    pub kind: ArgumentKind,
}

pub struct ParameterListWrapper<'a, TypeLike>(Vec<(&'a Loc<Identifier>, &'a TypeLike)>);

impl<'a, TypeLike> ParameterListWrapper<'a, TypeLike> {
    fn try_get_arg_type(&self, name: &Identifier) -> Option<&'a TypeLike> {
        self.0.iter().find_map(|(aname, val)| {
            if &aname.inner == name {
                Some(*val)
            } else {
                None
            }
        })
    }

    fn arg_index(&self, name: &Identifier) -> Option<usize> {
        self.0
            .iter()
            .enumerate()
            .find_map(|(i, (aname, _))| if &aname.inner == name { Some(i) } else { None })
    }
}

pub trait ParameterListLike<'a, TypeLike> {
    fn as_listlike(&'a self) -> ParameterListWrapper<'a, TypeLike>;
}

impl<'a> ParameterListLike<'a, TypeSpec> for ParameterList {
    fn as_listlike(&'a self) -> ParameterListWrapper<'a, TypeSpec> {
        ParameterListWrapper(self.0.iter().map(|p| (&p.name, &p.ty.inner)).collect())
    }
}

impl<'a> ParameterListLike<'a, ()> for &[Loc<TypeParam>] {
    fn as_listlike(&'a self) -> ParameterListWrapper<'a, ()> {
        ParameterListWrapper(
            self.iter()
                .flat_map(|p| p.inner.ident())
                .map(|n| (n, &()))
                .collect(),
        )
    }
}

/// Matches the arguments passed in an argument list with the parameters of a parameter list. If
/// the arguments match (correct amount of positional arguments, or unique mapping of named
/// arguments), the mapping from argument to parameter is returned as a vector in positional order
/// (but with named argument targets included for better diagnostics)
pub fn match_args_with_params<'a, T: Clone, TypeLike>(
    arg_list: &'a Loc<ArgumentList<T>>,
    params: &'a impl ParameterListLike<'a, TypeLike>,
    is_method: bool,
) -> Result<Vec<Argument<'a, T, TypeLike>>, ArgumentError> {
    match &arg_list.inner {
        ArgumentList::Positional(inner) => {
            let inner_loc = arg_list.shrink_left("(").shrink_right(")");

            let params = params.as_listlike();
            if inner.len() < params.0.len() {
                return Err(ArgumentError::TooFewArguments {
                    got: inner.len() - if is_method { 1 } else { 0 },
                    expected: params.0.len() - if is_method { 1 } else { 0 },
                    missing: params
                        .0
                        .iter()
                        .skip(inner.len())
                        .map(|(name, _)| name.inner.clone())
                        .collect(),
                    at: inner_loc,
                });
            }

            if inner.len() > params.0.len() {
                return Err(ArgumentError::TooManyArguments {
                    got: inner.len() - if is_method { 1 } else { 0 },
                    expected: params.0.len() - if is_method { 1 } else { 0 },
                    extra: inner
                        .iter()
                        .skip(params.0.len())
                        .map(|arg| arg.loc())
                        .collect(),
                    at: inner_loc,
                });
            }

            Ok(inner
                .iter()
                .zip(params.0)
                .map(|(arg, param)| Argument {
                    target: param.0,
                    target_type: param.1,
                    value: arg,
                    kind: ArgumentKind::Positional,
                })
                .collect())
        }
        ArgumentList::Named(inner) => {
            let mut bound: HashSet<Loc<Identifier>> = HashSet::default();
            let params = params.as_listlike();
            let mut unbound = params
                .0
                .iter()
                .map(|(ident, _)| ident.inner.clone())
                .collect::<HashSet<_>>();

            let mut result = inner
                .iter()
                .map(|arg| {
                    let (target, expr, kind) = match arg {
                        NamedArgument::Full(i, e) => (i, e, ArgumentKind::Named),
                        NamedArgument::Short(i, e) => (i, e, ArgumentKind::ShortNamed),
                    };

                    // Check if this is a new binding
                    if let Some(prev) = bound.get(target) {
                        return Err(ArgumentError::DuplicateNamedBindings {
                            new: target.clone(),
                            prev_loc: prev.loc(),
                        });
                    }
                    bound.insert(target.clone());

                    let target_type = if let Some(t) = params.try_get_arg_type(&target.inner) {
                        t
                    } else {
                        return Err(ArgumentError::NoSuchArgument {
                            name: target.clone(),
                        });
                    };

                    unbound.remove(target);

                    // NOTE: Safe unwrap, we already checked that the parameter
                    // list has this arg
                    let index = params.arg_index(target).unwrap();

                    Ok((
                        index,
                        Argument {
                            target,
                            value: expr,
                            target_type,
                            kind,
                        },
                    ))
                })
                .collect::<Result<Vec<_>, ArgumentError>>()?;

            result.sort_by_key(|(i, _)| *i);

            let result = result.into_iter().map(|(_, arg)| arg).collect();

            if !unbound.is_empty() {
                return Err(ArgumentError::MissingArguments {
                    missing: unbound.into_iter().collect(),
                    at: arg_list.loc(),
                });
            };

            Ok(result)
        }
    }
}
