use spade_codespan_reporting::files::Location;
use tower_lsp::lsp_types::Position;

pub fn loc_to_position(loc: Location) -> Position {
    // NOTE: Position is zero-based, Location is one-based.
    Position {
        line: (loc.line_number - 1) as _,
        character: (loc.column_number - 1) as _,
    }
}
