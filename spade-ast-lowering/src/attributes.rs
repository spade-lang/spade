use ast::{Attribute, AttributeList};
use local_impl::local_impl;
use spade_ast as ast;
use spade_common::location_info::{Loc, WithLocation};
use spade_diagnostics::Diagnostic;
use spade_hir as hir;

use crate::error::Result;

#[local_impl]
impl AttributeListExt for AttributeList {
    /// Removes #[no_mangle] from the attribute list and returns it if
    /// it was present
    fn consume_no_mangle(&mut self) -> Option<Loc<()>> {
        let mut mangle_attribute = None;
        self.0.retain(|attr| match attr.inner {
            Attribute::NoMangle => {
                mangle_attribute = Some(attr.loc());
                false
            }
            _ => false,
        });
        mangle_attribute
    }

    fn report_unused(&self, on: &str) -> Result<()> {
        if let Some(attr) = self.0.first() {
            Err(attr.report_unused(on))
        } else {
            Ok(())
        }
    }

    fn lower(
        &self,
        handler: &mut impl FnMut(&Loc<ast::Attribute>) -> Result<Option<hir::Attribute>>,
    ) -> Result<hir::AttributeList> {
        let inner = self
            .0
            .iter()
            .map(|attr| {
                let loc = attr.loc();
                Ok(handler(attr)?.map(|o| o.at_loc(&loc)))
            })
            .collect::<Result<Vec<_>>>()?
            .into_iter()
            .flatten()
            .collect();

        Ok(hir::AttributeList(inner))
    }
}

#[local_impl]
impl LocAttributeExt for Loc<ast::Attribute> {
    /// Report this attribute as unused on `on`
    /// on should be written not fit in the sentence {} is not a valid attribute for {on},
    /// i.e. `a thing` or `an item` should probably be used
    fn report_unused(&self, on: &str) -> Diagnostic {
        Diagnostic::error(
            self,
            format!("{} is not a valid attribute for {on}", self.name()),
        )
        .primary_label(format!("Unsupported attribute for {on}"))
    }
}
