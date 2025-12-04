use rustc_hash::FxHashMap as HashMap;
use serde::{Deserialize, Serialize};
use spade_common::location_info::Loc;
use spade_diagnostics::{diag_bail, Diagnostic};

use crate::{ImplBlock, ImplTarget, TraitName, TraitSpec, TypeExpression, TypeSpec};

type TargetArgs = Vec<TypeExpression>;
type TraitArgs = Vec<TypeExpression>;

type ConcreteImpls = HashMap<TargetArgs, Vec<(TraitArgs, Loc<ImplBlock>)>>;
type ImplementedTraits = HashMap<TraitName, ConcreteImpls>;

#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub struct ImplTab {
    pub inner: HashMap<ImplTarget, ImplementedTraits>,
}

impl ImplTab {
    pub fn new() -> Self {
        Self {
            inner: HashMap::default(),
        }
    }

    pub fn insert(
        &mut self,
        target: ImplTarget,
        trait_spec: TraitSpec,
        target_args: Vec<TypeExpression>,
        block: Loc<ImplBlock>,
    ) -> Result<(), Diagnostic> {
        let impls = self.inner.entry(target.clone()).or_default();
        let trait_impls = impls.entry(trait_spec.name.clone()).or_default();

        let trait_args = trait_spec
            .type_params
            .map(|a| a.inner.into_iter().map(|a| a.inner).collect())
            .unwrap_or_default();

        {
            let overlapping_targets = trait_impls.iter().filter(|(args, _)| {
                args.iter()
                    .zip(&target_args)
                    .all(|(l, r)| type_exprs_overlap(l, r))
            });
            let mut overlapping_traits = overlapping_targets
                .flat_map(|(_, impls)| impls.iter())
                .filter(|(args, _)| {
                    args.iter()
                        .zip(&trait_args)
                        .all(|(l, r)| type_exprs_overlap(l, r))
                })
                .map(|(_, block)| block);

            if let Some(duplicate) = overlapping_traits.next() {
                let name = match &trait_spec.name {
                    TraitName::Named(n) => n,
                    TraitName::Anonymous(_) => {
                        diag_bail!(block, "Found multiple impls of anonymous trait")
                    }
                };
                return Err(Diagnostic::error(
                    block,
                    format!(
                        "Multiple implementations of {} for {}",
                        name,
                        &target.display(&target_args)
                    ),
                )
                .secondary_label(duplicate, "Previous impl here"));
            }
        }

        let impls = trait_impls.entry(target_args).or_default();
        impls.push((trait_args, block));
        Ok(())
    }
}

pub fn type_specs_overlap(l: &TypeSpec, r: &TypeSpec) -> bool {
    match (l, r) {
        // Generic types overlap with all types
        (TypeSpec::Generic(_), _) => true,
        (_, TypeSpec::Generic(_)) => true,
        // Declared types overlap if their base is the same and their generics overlap
        (TypeSpec::Declared(lbase, lparams), TypeSpec::Declared(rbase, rparams)) => {
            lbase == rbase
                && lparams
                    .iter()
                    .zip(rparams)
                    .all(|(le, re)| type_exprs_overlap(le, re))
        }
        (TypeSpec::Declared(_, _), _) => false,
        (TypeSpec::Tuple(linner), TypeSpec::Tuple(rinner)) => linner
            .iter()
            .zip(rinner)
            .all(|(l, r)| type_specs_overlap(l, r)),
        (TypeSpec::Tuple(_), _) => false,
        (
            TypeSpec::Array {
                inner: linner,
                size: lsize,
            },
            TypeSpec::Array {
                inner: rinner,
                size: rsize,
            },
        ) => type_specs_overlap(linner, rinner) && type_exprs_overlap(lsize, rsize),
        (TypeSpec::Array { .. }, _) => false,
        (TypeSpec::Inverted(linner), TypeSpec::Inverted(rinner)) => {
            type_specs_overlap(&linner.inner, &rinner.inner)
        }
        (TypeSpec::Inverted(_), _) => todo!(),
        (TypeSpec::Wire(linner), TypeSpec::Wire(rinner)) => type_specs_overlap(linner, rinner),
        (TypeSpec::Wire(_), _) => false,
        (TypeSpec::TraitSelf(_), _) => unreachable!("Self type cannot be checked for overlap"),
        (TypeSpec::Wildcard(_), _) => {
            unreachable!("Wildcard type cannot be checked for overlap")
        }
    }
}

pub fn type_exprs_overlap(l: &TypeExpression, r: &TypeExpression) -> bool {
    match (l, r) {
        (TypeExpression::ConstGeneric(_), _) | (_, TypeExpression::ConstGeneric(_)) => {
            unreachable!("Const generic during type_exprs_overlap")
        }
        (TypeExpression::TypeSpec(lspec), TypeExpression::TypeSpec(rspec)) => {
            type_specs_overlap(lspec, rspec)
        }
        // The only way an integer or a string overlaps with a type is if it is a generic, so both
        // of these branches overlap
        (TypeExpression::TypeSpec(_), _) | (_, TypeExpression::TypeSpec(_)) => true,
        // Base type-level values overlap if they are equal
        (TypeExpression::Integer(rval), TypeExpression::Integer(lval)) => rval == lval,
        (TypeExpression::String(rval), TypeExpression::String(lval)) => rval == lval,
        _ => false,
    }
}
