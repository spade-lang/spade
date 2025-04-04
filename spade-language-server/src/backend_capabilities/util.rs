use crate::backend::ServerBackend;

use camino::Utf8PathBuf;
use color_eyre::eyre::{anyhow, Context};
use spade_codespan_reporting::files::Files;
use spade_common::location_info::Loc;
use spade_diagnostics::CodeBundle;
use tower_lsp::lsp_types::{Location, Position, Range, Url};

pub fn loc_to_location(loc: Loc<()>, code: &CodeBundle) -> color_eyre::Result<Location> {
    let Loc {
        inner: _,
        span,
        file_id,
    } = loc;

    let file = code
        .files
        .get(file_id)
        .with_context(|| format!("get file corresponding to file_id {file_id}"))?;
    let path = Utf8PathBuf::from(file.name().to_string());
    let spade_codespan_reporting::files::Location {
        line_number: start_line,
        column_number: start_column,
    } = file
        .location((), span.start().to_usize())
        .with_context(|| {
            format!(
                "line and column of byte offset {} in {}",
                span.start(),
                path
            )
        })?;
    let spade_codespan_reporting::files::Location {
        line_number: end_line,
        column_number: end_column,
    } = file
        .location((), span.end().to_usize())
        .with_context(|| format!("line and column of byte offset {} in {}", span.end(), path))?;
    Ok(Location {
        uri: Url::from_file_path(&path).map_err(|_| anyhow!("path '{path}' is not absolute"))?,
        range: Range {
            start: Position::new(start_line as u32 - 1, start_column as u32 - 1),
            end: Position::new(end_line as u32 - 1, end_column as u32 - 1),
        },
    })
}

// Misc helper functionality
impl ServerBackend {
    pub(super) fn loc_to_location(&self, loc: Loc<()>) -> color_eyre::Result<Location> {
        let code = &*self.code.lock().unwrap();
        loc_to_location(loc, code)
    }

    pub(super) fn in_same_file(&self, uri: &Url, loc: &Loc<()>) -> color_eyre::Result<bool> {
        let location = self.loc_to_location(loc.loc())?;

        Ok(location.uri == *uri)
    }

    pub(super) fn pos_in_loc(&self, loc: &Loc<()>, pos: &Position) -> bool {
        let location = self.loc_to_location(*loc);

        if location.is_err() {
            return false;
        }

        let Location {
            range: Range { start, end },
            ..
        } = location.unwrap();

        let is_in = if start.line > pos.line || end.line < pos.line {
            false
        } else if start.line == pos.line && end.line == pos.line {
            start.character <= pos.character && end.character >= pos.character
        } else if start.line == pos.line {
            start.character <= pos.character
        } else if end.line == pos.line {
            end.character >= pos.character
        } else {
            true
        };

        is_in
    }
    pub(super) fn pos_after_loc(&self, loc: &Loc<()>, pos: &Position) -> color_eyre::Result<bool> {
        let Location {
            range: Range { end, .. },
            ..
        } = self.loc_to_location(*loc)?;

        Ok(pos.line > end.line)
    }
}
