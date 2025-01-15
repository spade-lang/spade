use local_impl::local_impl;
use num::BigInt;
use spade_common::location_info::Loc;
use spade_diagnostics::diag_bail;
use spade_hir::ConstGenericWithId;
use spade_types::ConcreteType;

use crate::Context;
use crate::Result;

#[local_impl]
impl ConstGenericExt for Loc<ConstGenericWithId> {
    fn resolve_int(&self, ctx: &Context) -> Result<BigInt> {
        let ty = ctx
            .types
            .concrete_type_of(self, ctx.symtab.symtab(), &ctx.item_list.types)?;

        let start = match ty {
            ConcreteType::Integer(value) => value,
            other => diag_bail!(self, "Inferred {other} for type level integer"),
        };

        Ok(start)
    }
}
