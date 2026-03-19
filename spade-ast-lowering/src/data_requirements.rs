use spade_common::location_info::{Loc, WithLocation};

use crate::Context;

pub fn new_data_trait_spec(loc: &Loc<()>, ctx: &Context) -> Loc<spade_hir::TraitSpec> {
    spade_hir::TraitSpec {
        name: spade_hir::TraitName::Named(
            None,
            ctx.symtab
                .lang_item(spade_hir::symbol_table::LangItem::DataTrait)
                .clone()
                .at_loc(&loc),
        ),
        type_params: None,
        paren_syntax: false,
    }
    .at_loc(&loc)
}
