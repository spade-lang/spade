use std::collections::BTreeMap;

use inferer::{Equation, Inferer};
use num::ToPrimitive;
use range::Range;
use spade_common::location_info::Loc;
use spade_hir::{symbol_table::FrozenSymtab, Unit};
use spade_typeinference::{equation::TypeVar, TypeState};
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

    let mut known = BTreeMap::new();
    //
    for (ty, var) in inferer.mappings.iter() {
        match &ty.inner {
            TypeVar::Known(KnownType::Integer(_), sub) => match sub.as_slice() {
                [TypeVar::Known(KnownType::Integer(lo), _), TypeVar::Known(KnownType::Integer(hi), _)] =>
                {
                    known.insert(*var, Range::new(lo.clone(), hi.clone()));
                }
                other => panic!("An int is malformed {:?}", other),
            },
            TypeVar::Known(KnownType::Type(n), _) => panic!("How do I handle a type? {:?}", n),
            TypeVar::Unknown(_) => {
                // known.insert(var, Range { lo: 0, hi: 0 });
            }

            TypeVar::Tuple(_)
            | TypeVar::Array { .. }
            | TypeVar::Backward(_)
            | TypeVar::Wire(_)
            | TypeVar::Inverted(_) => panic!("Wat? {:?} {:?}", ty, var),
        }
    }

    let known = Inferer::infer(wl_infer_method, &inferer.equations, known, &inferer.locs)?;

    for (ty, var) in inferer.mappings.iter() {
        // None errors are checked when mir-lowering, this isn't necessarily an error
        let inferred_wl =
            if let Some(inferred_wl) = known.get(var).and_then(|guess| guess.to_wordlength()) {
                inferred_wl
            } else {
                continue;
            };
        let typechecker_wl =
            if let TypeVar::Known(KnownType::Integer(typechecker_wl), _) = &ty.inner {
                // 2^32 bits should be enough for anyone - right?
                typechecker_wl.to_u32().unwrap()
            } else {
                continue;
            };
        let loc = inferer.locs.get(var).cloned().unwrap_or(Loc::nowhere(()));
        if typechecker_wl != inferred_wl {
            // NOTE: To make these types better, the known types need to have a Loc on
            // them, something I really don't feel like doing right now.
            // NOTE: Printing the actual ranges of values would be nice!
            return Err(error::WordlengthMismatch {
                typechecked: typechecker_wl,
                inferred: inferred_wl,
                inferred_at: loc,
            }
            .into());
        }
        to_wordlength_error(
            inferer.type_state.unify(
                ty,
                &TypeVar::Known(KnownType::Integer(inferred_wl.into()), Vec::new()),
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
        Err(_err) => Err(error::UnificationError { at: loc }.into()),
    }
}
