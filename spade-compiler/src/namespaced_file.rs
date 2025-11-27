use std::path::PathBuf;

use logos::Logos;
use spade_common::name::Path as SpadePath;
use spade_parser::{lexer, Parser};

#[derive(Clone, Debug, PartialEq, Eq)]
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
            file: arg.into(),
            namespace: SpadePath(vec![]),
            base_namespace: SpadePath(vec![]),
        }),
        3 => {
            let root_namespace = if parts[0].is_empty() {
                SpadePath(vec![])
            } else {
                let mut root_parser = Parser::new(lexer::TokenKind::lexer(parts[0]), 0);
                root_parser
                    .path()
                    .map_err(|e| {
                        format!(
                            "\nwhen parsing '{}': {}",
                            parts[0],
                            e.labels.message.as_str()
                        )
                    })?
                    .inner
            };

            let namespace = if parts[1].is_empty() {
                SpadePath(vec![])
            } else {
                // NOTE: could be a bit smarter here and look for keywords manually
                let mut namespace_parser = Parser::new(lexer::TokenKind::lexer(parts[1]), 0);
                namespace_parser
                    .path()
                    .map_err(|e| {
                        format!(
                            "\nwhen parsing '{}': {}",
                            parts[1],
                            e.labels.message.as_str()
                        )
                    })?
                    .inner
            };

            Ok(NamespacedFile {
                base_namespace: root_namespace,
                file: parts[2].into(),
                namespace,
            })
        }
        other => Err(format!(
            "Expected filename or <root>,<namespace>,<filename>. Got string with {other} commas"
        )),
    }
}

pub fn dummy_file() -> NamespacedFile {
    namespaced_file("a,a,a.spade").unwrap()
}

#[cfg(test)]
mod tests {
    use spade_common::{
        location_info::WithLocation as _,
        name::{Identifier, Path as SpadePath, PathSegment},
    };

    use crate::namespaced_file::NamespacedFile;

    use super::namespaced_file;

    #[test]
    fn parsing_namespaced_file_works() {
        assert_eq!(
            namespaced_file("a,a::b,b.spade"),
            Ok(NamespacedFile {
                base_namespace: SpadePath(vec![PathSegment::Named(
                    Identifier::intern("a").nowhere()
                )]),
                namespace: SpadePath(vec![
                    PathSegment::Named(Identifier::intern("a").nowhere()),
                    PathSegment::Named(Identifier::intern("b").nowhere())
                ]),
                file: "b.spade".into(),
            })
        );
    }

    #[test]
    fn invalid_path_errors_without_panic() {
        assert!(namespaced_file("lib,lib::pipeline,pipeline.spade").is_err());
    }
}
