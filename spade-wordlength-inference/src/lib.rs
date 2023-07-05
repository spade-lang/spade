use std::collections::BTreeMap;

use inferer::{Equation, Inferer};
use range::Range;
use spade_common::location_info::Loc;
use spade_hir::{symbol_table::FrozenSymtab, Unit};
use spade_typeinference::{equation::TypeVar, fixed_types::t_int, TypeState};
use spade_types::KnownType;

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum InferMethod {
    IA,
    AA,
    AAIA,
}

pub mod error;

mod affine;
mod inferer;
mod range;

pub type Res = error::Result<Option<Equation>>;

pub fn infer_and_check(
    wl_infer_method: InferMethod,
    type_state: &mut TypeState,
    frozen_symtab: &FrozenSymtab,
    unit: &Unit,
) -> error::Result<()> {
    let mut inferer = inferer::Inferer::new(type_state, frozen_symtab.symtab());
    inferer.expression(&unit.body)?;

    let mut wordlengths_from_typechecker = BTreeMap::new();
    for (tys, var) in inferer.mappings.iter() {
        match &tys.inner {
            (
                _,
                TypeVar::Known(KnownType::Integer(lo), _),
                TypeVar::Known(KnownType::Integer(hi), _),
            ) => {
                wordlengths_from_typechecker.insert(*var, Range::new(lo.clone(), hi.clone()));
            }
            (_, TypeVar::Unknown(_), _) | (_, _, TypeVar::Unknown(_)) => { /* NOP */ }

            _ => panic!("Wat? {:?} {:?}", tys, var),
        }
    }

    let wordlengths_from_inferrer = Inferer::infer(
        wl_infer_method,
        &inferer.equations,
        wordlengths_from_typechecker.clone(),
        &inferer.locs,
    )?;

    for (ty, var) in inferer.mappings.iter() {
        let ty = &ty.inner.0;
        // None errors are checked when mir-lowering, this isn't necessarily an error
        let inferred_range = if let Some(inferred_range) = wordlengths_from_inferrer.get(var) {
            inferred_range.clone()
        } else {
            continue;
        };
        let loc = inferer.locs.get(var).cloned().unwrap_or(Loc::nowhere(()));
        if let Some(typechecker_range) = wordlengths_from_typechecker.get(var) {
            let typechecker_range = typechecker_range.clone();
            if typechecker_range != inferred_range {
                return Err(error::WordlengthMismatch {
                    typechecked: typechecker_range,
                    inferred: inferred_range,
                    inferred_at: loc,
                }
                .into());
            }
        };
        to_wordlength_error(
            inferer.type_state.unify(
                ty,
                &TypeVar::Known(
                    t_int(inferer.symtab),
                    vec![
                        TypeVar::Known(KnownType::Integer(inferred_range.lo().clone()), Vec::new()),
                        TypeVar::Known(KnownType::Integer(inferred_range.hi().clone()), Vec::new()),
                    ],
                ),
                inferer.symtab,
            ),
            loc,
        )?;
    }

    Ok(())
}

fn to_wordlength_error<A>(
    ty_err: Result<A, spade_typeinference::error::UnificationError>,
    loc: Loc<()>,
) -> error::Result<A> {
    match ty_err {
        Ok(v) => Ok(v),
        Err(err) => Err(error::UnificationError { at: loc, err }.into()),
    }
}
