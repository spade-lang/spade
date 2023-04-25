use std::path::PathBuf;

use logos::Logos;
use spade_common::name::Path as SpadePath;
use spade_parser::{lexer, Parser};

#[derive(Clone, Debug)]
pub struct NamespacedFile {
    /// The namespace which is the root of this file, i.e. what is referred
    /// to when when starting a path with lib::
    pub base_namespace: SpadePath,
    /// The namespace of the items added in this file.
    pub namespace: SpadePath,
    pub file: PathBuf,
}

/// Parses `a::b,a::b::c,test.spade` as `root_namespace: a::b, namespace: a::b::c, file: test.spade`
/// if no , is present, attempts to parse a path and set root and namespace to vec![]
pub fn namespaced_file(arg: &str) -> Result<NamespacedFile, String> {
    let parts = arg.split(',').collect::<Vec<_>>();

    match parts.len() {
        0 => Err("Expected a string".to_string()),
        1 => Ok(NamespacedFile {
            file: arg.try_into().map_err(|e| format!("{e}"))?,
            namespace: SpadePath(vec![]),
            base_namespace: SpadePath(vec![]),
        }),
        3 => {
            let root_namespace = if parts[0].is_empty() {
                SpadePath(vec![])
            } else {
                let mut root_parser = Parser::new(lexer::TokenKind::lexer(parts[0]), 0);
                root_parser.path().map_err(|e| format!("{e}"))?.inner
            };

            let namespace = if parts[1].is_empty() {
                SpadePath(vec![])
            } else {
                let mut namespace_parser = Parser::new(lexer::TokenKind::lexer(parts[1]), 0);
                namespace_parser.path().map_err(|e| format!("{e}"))?.inner
            };

            Ok(NamespacedFile {
                base_namespace: root_namespace,
                file: parts[2].try_into().map_err(|e| format!("{e}"))?,
                namespace,
            })
        }
        other => Err(format!(
            "Expected filename or <root>,<namespace>,<filename>. Got string with {other} commas"
        )),
    }
}
