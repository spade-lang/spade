use std::fmt::Display;

use regex::Regex;
use rustc_hash::FxHashMap as HashMap;
use spade_codespan_reporting::files::{Files, Location, SimpleFile};
use tap::Pipe;
use tower_lsp::lsp_types::Range;

use crate::tests::utils::loc_to_position;

#[derive(Debug)]
pub struct Marker {
    pub range: Range,
    pub diagnostic: Option<String>,
    pub goto: bool,
    pub goto_target: bool,
    pub goto_target_end: bool,
    pub comps: bool,
    pub hover: bool,
}

pub fn find_markers(
    file: &SimpleFile<impl Display + Clone, impl AsRef<str>>,
) -> HashMap<i32, Marker> {
    let re = Regex::new(r"(?m)(\^+)\[(\d+)](.*)$").unwrap();
    let line_above = |loc: Location| Location {
        line_number: loc.line_number - 1,
        column_number: loc.column_number,
    };
    re.captures_iter(file.source().as_ref())
        .map(|c| {
            let range = c.get(1).unwrap();
            let id = c.get(2).unwrap().as_str().parse().unwrap();
            let kind = c.get(3).unwrap().as_str().trim();
            let diagnostic = kind.strip_prefix("diagnostic: ").map(str::to_string);
            let goto = kind == "goto";
            let goto_target = kind == "goto-target";
            let goto_target_end = kind == "goto-target-end";
            let comps = kind == "comps";
            let hover = kind == "hover";
            (
                id,
                Marker {
                    range: Range::new(
                        file.location((), range.start())
                            .unwrap()
                            .pipe(line_above)
                            .pipe(loc_to_position),
                        file.location((), range.end())
                            .unwrap()
                            .pipe(line_above)
                            .pipe(loc_to_position),
                    ),
                    diagnostic,
                    goto,
                    goto_target,
                    goto_target_end,
                    comps,
                    hover,
                },
            )
        })
        .collect()
}
