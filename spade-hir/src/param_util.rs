// Utilities related to argument matching between callers and callees. Lives in spade-hir
// because this is required twice in the compilation process: first during type inference,
// and then again during hir lowering

use itertools::{EitherOrBoth, Itertools};
use rustc_hash::FxHashSet as HashSet;
use spade_diagnostics::Diagnostic;

use spade_common::{location_info::Loc, name::Identifier};

use crate::expression::NamedArgument;
use crate::{ArgumentList, ParameterList, TypeExpression, TypeParam, TypeSpec};

#[derive(Debug, PartialEq, Clone)]
pub enum ArgumentError {
    TooFewArguments {
        got: usize,
        expected: usize,
        missing: Vec<Identifier>,
        at: Loc<()>,
        num_defaults: usize,
    },
    TooManyArguments {
        got: usize,
        expected: usize,
        extra: Vec<Loc<()>>,
        at: Loc<()>,
        num_defaults: usize,
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
                num_defaults,
            } => {
                let plural = if expected == 1 { "" } else { "s" };

                let at_most = if num_defaults > 0 { "at most " } else { "" };
                let between = if num_defaults > 0 {
                    format!("between {} and ", expected - num_defaults)
                } else {
                    "".into()
                };

                let mut base = Diagnostic::error(
                    at,
                    format!("Too many arguments. Expected {between}{expected}, got {got}"),
                )
                .primary_label(format!("Expected {at_most}{expected} argument{plural}"));

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
                num_defaults,
            } => {
                let missing_plural = if missing.len() == 1 { "" } else { "s" };

                let at_least = if num_defaults > 0 { "at_least " } else { "" };
                let between = if num_defaults > 0 {
                    format!("between {} and ", expected - num_defaults)
                } else {
                    "".into()
                };

                let leading_comma = if got == 0 { "" } else { ", " };
                let suggestion = format!(
                    "{leading_comma}{}",
                    missing.iter().map(|p| format!("/* {p} */")).join(", ")
                );

                Diagnostic::error(
                    at,
                    format!("Too few arguments. Expected {between}{expected}, got {got}"),
                )
                .primary_label(format!(
                    "Missing {at_least}{count} argument{missing_plural}",
                    count = missing.len() - num_defaults
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
    Default,
}

/// A resolved positional or named argument. Used by both value arguments and turbofishes.
/// TypeLike is the target type for arguments, and () for turbofishes
pub struct Argument<'a, T, TypeLike> {
    pub target: &'a Loc<Identifier>,
    pub value: &'a Loc<T>,
    pub target_type: &'a TypeLike,
    pub kind: ArgumentKind,
}

pub struct ParameterListWrapper<'a, TypeLike, T>(
    Vec<(&'a Loc<Identifier>, &'a TypeLike, Option<&'a Loc<T>>)>,
);

impl<'a, TypeLike, T> ParameterListWrapper<'a, TypeLike, T> {
    fn try_get_arg_type(&self, name: &Identifier) -> Option<&'a TypeLike> {
        self.0.iter().find_map(|(aname, val, _)| {
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
            .find_map(|(i, (aname, _, _))| if &aname.inner == name { Some(i) } else { None })
    }

    fn arg_default(&self, name: &'a Identifier) -> Option<Option<&'a Loc<T>>> {
        self.0.iter().find_map(|(aname, _, default)| {
            if &aname.inner == name {
                Some(default.clone())
            } else {
                None
            }
        })
    }
}

pub trait ParameterListLike<'a, TypeLike, T> {
    fn as_listlike(&'a self) -> ParameterListWrapper<'a, TypeLike, T>;
}

impl<'a, T> ParameterListLike<'a, TypeSpec, T> for ParameterList {
    fn as_listlike(&'a self) -> ParameterListWrapper<'a, TypeSpec, T> {
        ParameterListWrapper(
            self.0
                .iter()
                .map(|p| (&p.name, &p.ty.inner, None))
                .collect(),
        )
    }
}

impl<'a> ParameterListLike<'a, (), TypeExpression> for &[Loc<TypeParam>] {
    fn as_listlike(&'a self) -> ParameterListWrapper<'a, (), TypeExpression> {
        ParameterListWrapper(
            self.iter()
                .map(|p| (p.ident().unwrap(), &(), p.default.as_deref()))
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
    params: &'a impl ParameterListLike<'a, TypeLike, T>,
    is_method: bool,
) -> Result<Vec<Argument<'a, T, TypeLike>>, ArgumentError> {
    match &arg_list.inner {
        ArgumentList::Positional(inner) => {
            let inner_loc = arg_list.shrink_left("(").shrink_right(")");
            let params = params.as_listlike();

            // The error message changes when there are default values
            let num_defaults = params
                .0
                .iter()
                .rev()
                .take_while(|param| param.2.is_some())
                .count();

            inner
                .iter()
                .zip_longest(&params.0)
                .enumerate()
                .map(|(i, item)| match item {
                    EitherOrBoth::Both(arg, param) => Ok(Argument {
                        target: param.0,
                        target_type: param.1,
                        value: arg,
                        kind: ArgumentKind::Positional,
                    }),
                    EitherOrBoth::Left(_) => Err(ArgumentError::TooManyArguments {
                        got: inner.len() - if is_method { 1 } else { 0 },
                        expected: params.0.len() - if is_method { 1 } else { 0 },
                        extra: inner
                            .iter()
                            .skip(params.0.len())
                            .map(|arg| arg.loc())
                            .collect(),
                        at: inner_loc,
                        num_defaults,
                    }),
                    EitherOrBoth::Right(param) => match param.2 {
                        Some(d) => Ok(Argument {
                            target: param.0,
                            target_type: param.1,
                            value: d,
                            kind: ArgumentKind::Default,
                        }),
                        None => Err(ArgumentError::TooFewArguments {
                            got: i - if is_method { 1 } else { 0 },
                            expected: params.0.len() - if is_method { 1 } else { 0 },
                            missing: params
                                .0
                                .iter()
                                .skip(inner.len())
                                .map(|(name, _, _)| name.inner.clone())
                                .collect(),
                            at: inner_loc,
                            num_defaults,
                        }),
                    },
                })
                .collect()
        }
        ArgumentList::Named(inner) => {
            let mut bound: HashSet<Loc<Identifier>> = HashSet::default();
            let params = params.as_listlike();
            let mut unbound = params
                .0
                .iter()
                .cloned()
                .map(|(ident, _, _)| ident)
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

            for name in unbound.clone() {
                // NOTE: Safe unwraps, all these are guaranteed to exist because they belong to an
                // unbound parameter
                if let Some(default) = params.arg_default(&name).unwrap() {
                    let index = params.arg_index(&name).unwrap();
                    let target_type = params.try_get_arg_type(&name).unwrap();
                    unbound.remove(&name);
                    result.push((
                        index,
                        Argument {
                            target: name,
                            value: default,
                            target_type,
                            kind: ArgumentKind::Default,
                        },
                    ))
                }
            }

            result.sort_by_key(|(i, _)| *i);

            let result = result.into_iter().map(|(_, arg)| arg).collect();

            if !unbound.is_empty() {
                return Err(ArgumentError::MissingArguments {
                    missing: unbound.into_iter().map(|u| u.inner).collect(),
                    at: arg_list.loc(),
                });
            };

            Ok(result)
        }
    }
}
