use crate::backend::ServerBackend;

use camino::Utf8PathBuf;
use color_eyre::eyre::{anyhow, Context};
use spade_codespan::Span;
use spade_codespan_reporting::files::{line_starts, Files};
use spade_common::{
    location_info::Loc,
    name::{Identifier, NameID},
};
use spade_diagnostics::CodeBundle;
use spade_hir::{
    query::Thing, symbol_table::StructCallable, ExecutableItem, ExprKind, Expression, TypeSpec,
    UnitHead,
};
use spade_typeinference::{
    equation::{TypeVar, TypeVarID},
    method_resolution::select_method,
    HasType, TypeState,
};
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
    pub(crate) fn pos_uri_to_loc(&self, pos: &Position, uri: &Url) -> color_eyre::Result<Loc<()>> {
        let code = &*self.code.lock().unwrap();
        let path = uri
            .to_file_path()
            .map_err(|_| anyhow!("URI {} was not a file", uri))?;

        let file = code
            .dump_files()
            .into_iter()
            .enumerate()
            .find(|(_id, (file, _content))| **file == path.to_string_lossy().to_string());

        match file {
            Some((id, (_file, content))) => {
                let line_starts = line_starts(content);

                let start = line_starts.skip(pos.line as usize).next();

                match start {
                    Some(s) => Ok(Loc {
                        inner: (),
                        span: Span::new(s as u32 + pos.character, s as u32 + pos.character),
                        file_id: id,
                    }),
                    None => Err(anyhow!("Line is out of range for file")),
                }
            }
            None => Err(anyhow!("Did not find a file for {}", uri)),
        }
    }

    pub(super) fn loc_to_location(&self, loc: Loc<()>) -> color_eyre::Result<Location> {
        let code = &*self.code.lock().unwrap();
        loc_to_location(loc, code)
    }

    pub(crate) fn get_position_details(
        &self,
        pos: &Position,
        uri: &Url,
    ) -> Option<PositionDetails> {
        let Some(loc) = self.pos_uri_to_loc(pos, uri).ok() else {
            return None;
        };

        let name = self
            .query_cache
            .lock()
            .unwrap()
            .names_around(&loc)
            .last()
            .map(|loc| loc.map(|inner| inner.clone()));

        let current_unit = self
            .query_cache
            .lock()
            .unwrap()
            .things_around(&loc)
            .iter()
            .find_map(|thing| match thing.inner {
                Thing::Executable(ExecutableItem::Unit(u)) => Some(u),
                _ => None,
            })
            .cloned();

        let unit_type_state = current_unit.as_ref().and_then(|u| {
            self.type_states
                .lock()
                .unwrap()
                .get(u.name.name_id())
                .cloned()
        });

        Some(PositionDetails {
            loc,
            name,
            unit_type_state,
        })
    }

    pub(crate) fn contextual_expression_info(
        &self,
        PositionDetails {
            loc,
            name: _,
            unit_type_state,
        }: &PositionDetails,
    ) -> ContextualExpressionInfo {
        let qq = self.query_cache.lock().unwrap();
        let things_around = qq.things_around(loc);

        let type_info = things_around
            .iter()
            .filter_map(|thing| match &thing.inner {
                Thing::Expr(expr) => Some(expr),
                Thing::Pattern(_) | Thing::Statement(_) | Thing::Executable(_) => None,
            })
            .filter_map(|expr| {
                unit_type_state.as_ref().and_then(|ts| {
                    let Some(self_ty) = expr.try_get_type(ts) else {
                        return None;
                    };

                    Some((expr.clone(), self_ty))
                })
            })
            .collect::<Vec<_>>();

        let struct_field_info = things_around
            .iter()
            .filter_map(|thing| match &thing.inner {
                Thing::Expr(expression) => Some((thing, expression)),
                Thing::Pattern(_) | Thing::Statement(_) | Thing::Executable(_) => None,
            })
            .find_map(|(thing, expr)| match &expr.kind {
                ExprKind::FieldAccess(base, field) => {
                    if field.contains_start(loc) {
                        unit_type_state.as_ref().and_then(|ts| {
                            let symtab = self.symtab.lock().unwrap();
                            let Some(symtab) = symtab.as_ref() else {
                                return None;
                            };

                            let Some(target_ty) = base.try_get_type(ts) else {
                                return None;
                            };

                            let TypeVar::Known(_, spade_types::KnownType::Named(name), _) =
                                target_ty.resolve(ts)
                            else {
                                return None;
                            };

                            let s = symtab.struct_by_id(name);

                            let Some(param) = s.params.0.iter().find(|p| &p.name == field) else {
                                return None;
                            };

                            Some(FieldInfo::Field {
                                name: param.name.clone(),
                                st: s.clone(),
                                field_ty: param.ty.inner.clone(),
                            })
                        })
                    } else {
                        None
                    }
                }
                ExprKind::MethodCall {
                    target,
                    name,
                    args: _,
                    call_kind: _,
                    turbofish: _,
                } => {
                    if name.contains_start(loc) {
                        unit_type_state.as_ref().and_then(|ts| {
                            let Some(target_ty) = target.try_get_type(ts) else {
                                return None;
                            };

                            select_method(
                                thing.loc(),
                                &target_ty,
                                name,
                                &self.trait_impls.lock().unwrap(),
                                ts,
                            )
                            .ok()
                            .flatten()
                            .and_then(|callee| {
                                let symtab = self.symtab.lock().unwrap();
                                let Some(symtab) = symtab.as_ref() else {
                                    return None;
                                };
                                let target_unit = symtab.unit_by_id(&callee.inner);
                                Some(FieldInfo::Method {
                                    target_unit,
                                    target_ty,
                                })
                            })
                        })
                    } else {
                        None
                    }
                }
                _ => None,
            });

        ContextualExpressionInfo {
            expression: type_info,
            field: struct_field_info,
        }
    }
}

pub(crate) struct PositionDetails {
    pub loc: Loc<()>,
    pub name: Option<Loc<NameID>>,
    pub unit_type_state: Option<TypeState>,
}

#[derive(Debug)]
pub(crate) struct ContextualExpressionInfo {
    pub expression: Vec<(Expression, TypeVarID)>,
    pub field: Option<FieldInfo>,
}

#[derive(Debug)]
pub(crate) enum FieldInfo {
    Field {
        name: Loc<Identifier>,
        st: Loc<StructCallable>,
        field_ty: TypeSpec,
    },
    Method {
        target_unit: Loc<UnitHead>,
        target_ty: TypeVarID,
    },
}
