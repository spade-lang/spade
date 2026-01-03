use tower_lsp::lsp_types::{Location, Position, Url};

use crate::backend::ServerBackend;

use super::util::{FieldInfo, PositionDetails};

pub trait GotoDefinition {
    fn find_definition(&self, pos: &Position, uri: &Url) -> Option<Location>;
}

impl GotoDefinition for ServerBackend {
    fn find_definition(&self, pos: &Position, uri: &Url) -> Option<Location> {
        let ref pos @ PositionDetails {
            loc: _,
            ref name,
            unit_type_state: _,
        } = self.get_position_details(pos, uri)?;

        let contextual = self.contextual_expression_info(pos);

        let symtab = self.symtab.lock().unwrap();
        let symtab = symtab.as_ref()?;

        let field = contextual.field.and_then(|f| match f {
            FieldInfo::Field {
                name,
                st,
                field_ty: _,
            } => st
                .params
                .0
                .iter()
                .find(|param| param.name == name)
                .map(|param| param.name.loc()),
            FieldInfo::Method {
                target_unit,
                target_ty: _,
            } => Some(target_unit.loc()),
        });

        let from_thing = name
            .as_ref()
            .and_then(|name| symtab.symtab().thing_by_id(name))
            .map(|thing| thing.loc());

        let from_type = name
            .as_ref()
            .and_then(|name| symtab.symtab().try_type_symbol_by_id(&name))
            .map(|thing| thing.loc());

        field
            .or(from_thing)
            .or(from_type)
            .and_then(|loc| self.loc_to_location(loc).ok())
    }
}
