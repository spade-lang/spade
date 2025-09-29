use std::{borrow::Cow, collections::BTreeMap, fmt::Display, fs::File, io::Write};

use camino::{Utf8Path, Utf8PathBuf};
use color_eyre::Result;
use local_impl::local_impl;
use pathdiff::diff_utf8_paths;
use spade_common::{
    location_info::WithLocation,
    name::{Identifier, Path as SpadePath},
};
use spade_hir::{symbol_table::Thing, TraitName, TypeDeclKind, TypeDeclaration, UnitHead};

use crate::{
    html::{
        self, spec::Spec, GenericTypeParam, ImplementationMember, ItemContent, ItemKind,
        ItemListing, ListedEntry, RenderedMarkdown, Signature, StructSignature, UnitSignature,
        WhereClause,
    },
    Documentation, Item,
};

#[derive(Debug, Clone, Copy)]
pub(crate) struct Documentable<'a, T> {
    pub namespace: &'a SpadePath,
    /// the root module has no "name"
    pub name: Option<&'a Identifier>,
    pub inner: T,
}
#[local_impl]
impl<T> Wrap for T {
    fn wrap<'a, U>(self, other: &'_ Documentable<'a, U>) -> Documentable<'a, T> {
        Documentable {
            namespace: &other.namespace,
            name: other.name,
            inner: self,
        }
    }
}

struct PathState {
    path: Utf8PathBuf,
    root: Utf8PathBuf,
}
impl PathState {
    fn enter_from_root<S: AsRef<Utf8Path>>(
        &mut self,
        iter: impl Iterator<Item = S>,
    ) -> std::io::Result<()> {
        self.path = iter.fold(self.root.clone(), |acc, nxt| acc.join(nxt));
        std::fs::create_dir_all(&self.path)
    }

    fn enter_root(&mut self) -> std::io::Result<()> {
        self.enter_from_root(core::iter::empty::<&str>())
    }

    fn style_path(&self) -> Utf8PathBuf {
        self.relative_path([Utf8Path::new("styles.css")])
    }

    fn spade_highlight_path(&self) -> Utf8PathBuf {
        self.relative_path([Utf8Path::new("spade-highlight.js")])
    }

    fn spade_css_path(&self) -> Utf8PathBuf {
        self.relative_path([Utf8Path::new("spade-theme.css")])
    }

    fn path<S: AsRef<Utf8Path>>(&self, path: impl IntoIterator<Item = S>) -> Utf8PathBuf {
        path.into_iter()
            .fold(self.root.clone(), |acc, nxt| acc.join(nxt))
    }

    fn relative_path<S: AsRef<Utf8Path>>(&self, path: impl IntoIterator<Item = S>) -> Utf8PathBuf {
        diff_utf8_paths(self.path(path), &self.path).unwrap()
    }

    fn spade_path_to_file(&self, path: &SpadePath, ident: Option<&Identifier>) -> Utf8PathBuf {
        if let Some(ident) = ident {
            self.path(
                path.0
                    .iter()
                    .map(|seg| &seg.inner)
                    .map(|seg| Utf8Path::new(&seg.0))
                    .chain([Utf8Path::new(&format!("{}.html", ident.0))]),
            )
        } else {
            self.path([Utf8Path::new("index.html")])
        }
    }

    fn relative_from_path(&self, path: &SpadePath, ident: Option<&Identifier>) -> Utf8PathBuf {
        diff_utf8_paths(self.spade_path_to_file(path, ident), &self.path).unwrap()
    }
}

pub struct Renderer<'d> {
    state: PathState,
    documentation: &'d Documentation,
}

impl<'d> Renderer<'d> {
    pub fn new(root: Utf8PathBuf, documentation: &'d Documentation) -> Self {
        Self {
            state: PathState {
                path: root.clone(),
                root,
            },
            documentation,
        }
    }

    pub fn render(&mut self) -> Result<()> {
        self.state.enter_root()?;

        self.item(Documentable {
            namespace: &SpadePath(vec![]),
            name: None,
            inner: &Item::Module(self.documentation.root.1.clone()),
        })?;

        for (path, items) in &self.documentation.documentables {
            self.state
                .enter_from_root(path.0.iter().map(|ident| &ident.0))?;

            for (name, item) in items {
                self.item(Documentable {
                    namespace: path,
                    name: Some(name),
                    inner: item,
                })?;
            }
        }

        let styles = self.state.root.join("styles.css");
        std::fs::write(styles, include_str!("styles.css"))?;

        let font = self.state.root.join("DMSans-VariableFont_opsz,wght.ttf");
        std::fs::write(font, include_bytes!("DMSans-VariableFont_opsz,wght.ttf"))?;

        let highlight_js = self.state.root.join("spade-highlight.js");
        std::fs::write(highlight_js, include_str!("html/spade-highlight.js"))?;

        let highlight_css = self.state.root.join("spade-theme.css");
        std::fs::write(highlight_css, include_str!("html/spade-theme.css"))?;

        Ok(())
    }

    fn item(&mut self, item: Documentable<&Item>) -> Result<()> {
        let kind = item.inner.kind();
        let doc = item.inner.documentation();

        let content: Vec<_> = core::iter::empty()
            .chain(self.item_listing(item)?)
            .chain(self.enum_variants(item)?)
            .chain(self.type_impls(item)?)
            .collect();

        let name = item
            .name
            .as_ref()
            .map(|ident| &ident.0)
            .unwrap_or(&self.documentation.root.0);

        write_template(
            &self.state.spade_path_to_file(item.namespace, item.name),
            html::Item {
                root_namespace_path: self.state.relative_path(["index.html"]),
                root_namespace: self.documentation.root.0.as_str(),

                style_ref: self.state.style_path(),
                spade_highlight_path: self.state.spade_highlight_path(),
                spade_css_path: self.state.spade_css_path(),

                name,
                namespace: html::Path::new(item.namespace.0.as_slice()),
                kind,

                signature: self.signature(item.inner)?,
                doc: RenderedMarkdown::render(doc),
                content: content.as_slice(),
            },
        )
    }

    fn item_listing(&mut self, item: Documentable<&Item>) -> Result<Vec<ItemContent<'d>>> {
        let module = if let Item::Module(module) = item.inner {
            module.wrap(&item)
        } else {
            return Ok(vec![]);
        };

        let mut item_lists: BTreeMap<ItemKind, Vec<ListedEntry>> = BTreeMap::default();

        let namespace = if module.name.is_none() {
            // Special case for root module
            module.namespace.clone() // will be empty
        } else {
            module.namespace.push_ident(
                module
                    .name
                    .expect("just checked its not none")
                    .clone()
                    .nowhere(),
            )
        };

        if let Some(children) = self.documentation.documentables.get(&namespace) {
            for (ident, item) in children {
                item_lists
                    .entry(item.kind())
                    .or_default()
                    .push(html::ListedEntry {
                        name: &ident.0,
                        link: self
                            .state
                            .relative_from_path(&namespace, Some(&ident))
                            .into_string(),
                    });
            }
        }

        let mut listings = vec![];
        for (kind, mut entries) in item_lists {
            entries.sort_by_key(|entry| entry.name);
            listings.push(ItemContent::ItemListing(ItemListing {
                title: kind.plural(),
                entries,
            }));
        }
        Ok(listings)
    }

    fn enum_variants<'a>(
        &mut self,
        item: Documentable<&'a Item>,
    ) -> Result<Option<ItemContent<'a>>> {
        if let Item::Type(TypeDeclaration {
            kind: TypeDeclKind::Enum(e),
            ..
        }) = item.inner
        {
            let mut variants = vec![];
            for option in &e.options {
                let id = &option.0.inner;
                let variant = self
                    .documentation
                    .symtab
                    .symtab()
                    .enum_variant_by_id(id)
                    .inner;
                variants.push(if option.1.inner.0.is_empty() {
                    html::Variant::Unit(
                        Cow::from(variant.name.inner.0),
                        RenderedMarkdown::render(&variant.documentation),
                    )
                } else {
                    html::Variant::Valued(
                        Cow::from(variant.name.inner.0),
                        option
                            .1
                            .inner
                            .0
                            .iter()
                            .map(|param| {
                                || -> Result<_> {
                                    Ok(html::Param(
                                        &param.name.0,
                                        Spec::mirror_typespec(&param.ty)?,
                                    ))
                                }()
                            })
                            .collect::<Result<_>>()?,
                        RenderedMarkdown::render(&variant.documentation),
                    )
                });
            }
            Ok(Some(ItemContent::Variants(html::Variants(variants))))
        } else {
            Ok(None)
        }
    }

    fn type_impls(&self, item: Documentable<&Item>) -> Result<Vec<ItemContent<'d>>> {
        if let Item::Type(ty) = item.inner {
            let mut impls = vec![];
            if let Some(i) = self
                .documentation
                .flattened_impls
                .get(&spade_hir::ImplTarget::Named(ty.name.inner.clone()))
            {
                for (traitname, implblock) in i {
                    let target = Spec::mirror_typespec(&implblock.target.inner)?;
                    impls.push(ItemContent::Implementation(html::Implementation {
                        type_params: implblock
                            .type_params
                            .iter()
                            .map(|type_param| GenericTypeParam::mirror_typeparam(type_param))
                            .collect::<Result<_>>()?,
                        impld_trait: if let TraitName::Named(n) = traitname {
                            Some(n.inner.1.tail().0.into())
                        } else {
                            None
                        },
                        target,
                        members: {
                            let mut keys = implblock.fns.keys().collect::<Vec<_>>();
                            keys.sort_by_key(|identifier| &identifier.0);
                            keys.into_iter()
                                .map(|key| {
                                    self.documentation
                                        .symtab
                                        .symtab()
                                        .things
                                        .get(&implblock.fns[key].0)
                                        .map(|thing| match thing {
                                            Thing::Unit(unit_head) => unit_head,
                                            _ => todo!(), // other impl members
                                        })
                                        .unwrap()
                                })
                                .filter_map(|unit_head| {
                                    self.unit_signature(
                                        unit_head, false, /* impl members are never extern */
                                    )
                                    .transpose()
                                    .map(|signature| (unit_head, signature))
                                })
                                .map(|(unit_head, signature)| {
                                    signature.map(|signature| ImplementationMember {
                                        doc: RenderedMarkdown::render(&unit_head.documentation),
                                        signature,
                                    })
                                })
                                .collect::<Result<_>>()?
                        },
                    }));
                }
            }
            Ok(impls)
        } else {
            Ok(vec![])
        }
    }

    fn unit_signature<'a>(
        &self,
        head: &'a UnitHead,
        is_external: bool,
    ) -> Result<Option<Signature<'a>>> {
        Ok(Some(Signature::UnitSignature(UnitSignature {
            is_external,
            attributes: vec![],
            kind: &head.unit_kind,
            name: head.name.0.as_str(),
            type_params: head
                .unit_type_params
                .iter()
                .map(|type_param| GenericTypeParam::mirror_typeparam(type_param))
                .collect::<Result<Vec<_>>>()?,
            params: head
                .inputs
                .0
                .iter()
                .map(|param| {
                    Ok(html::Param(
                        &param.name.0,
                        Spec::mirror_typespec(&param.ty)?,
                    ))
                })
                .collect::<Result<_>>()?,
            output: match &head.output_type {
                Some(ty) => Some(Spec::mirror_typespec(ty)?),
                _ => None,
            },
            where_clauses: head
                .where_clauses
                .iter()
                .map(|where_clause| {
                    || -> Result<_> {
                        let (target, constraints) = match &**where_clause {
                            // TODO: Rdner kind and if_unsatisfied
                            spade_hir::WhereClause::Int { target, constraint, kind: _, if_unsatisfied: _} => (
                                target,
                                vec![Spec::mirror_constgeneric(constraint, true, false)?],
                            ),
                            spade_hir::WhereClause::Type { target, traits } => (
                                target,
                                traits
                                    .iter()
                                    .map(|trait_spec| Spec::mirror_traitspec(trait_spec))
                                    .collect::<Result<Vec<_>>>()?,
                            ),
                        };
                        Ok(WhereClause {
                            target: Spec::Declared {
                                name: Cow::Owned(target.1.tail()),
                                type_args: vec![],
                            },
                            constraints,
                        })
                    }()
                })
                .collect::<Result<Vec<_>>>()?,
        })))
    }

    fn signature<'a>(&self, item: &'a Item) -> Result<Option<Signature<'a>>> {
        match item {
            Item::Unit(head, is_external) => self.unit_signature(head, *is_external),
            Item::Type(ty_decl) => match &ty_decl.kind {
                TypeDeclKind::Struct(struct_decl) => {
                    Ok(Some(Signature::StructSignature(StructSignature {
                        attributes: vec![],
                        name: ty_decl.name.1.tail().to_string(),
                        type_params: ty_decl
                            .generic_args
                            .iter()
                            .map(|type_param| GenericTypeParam::mirror_typeparam(type_param))
                            .collect::<Result<Vec<_>>>()?,
                        members: struct_decl
                            .members
                            .0
                            .iter()
                            .map(|param| {
                                Ok(html::Param(
                                    &param.name.0,
                                    Spec::mirror_typespec(&param.ty)?,
                                ))
                            })
                            .collect::<Result<_>>()?,
                    })))
                }
                _ => Ok(None),
            },
            _ => Ok(None),
        }
    }
}

fn write_template(link: &Utf8PathBuf, template: impl Display) -> Result<()> {
    std::fs::create_dir_all(link.parent().unwrap())?;
    let mut file = File::create(link)?;
    file.write_fmt(format_args!("{template}"))?;
    Ok(())
}
