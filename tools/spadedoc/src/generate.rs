use camino::Utf8PathBuf;
use itertools::Itertools;
use pulldown_cmark::{Options, Parser};
use spade_ast::{
    self as ast, AttributeList, ExternalMod, ModuleBody, TraitDef, TraitSpec, TypeDeclKind,
    TypeDeclaration, TypeParam, TypeSpec, Unit, UnitKind, WhereClause,
};
use spade_common::{
    location_info::{Loc, WithLocation},
    name::{Identifier, NameID, Path, PathSegment},
};
use spade_diagnostics::diag_list::DiagList;
use spade_hir::symbol_table::{self as symtab, SymbolTable, Thing, TypeSymbol};
use std::{
    collections::BTreeMap,
    fs::File,
    io::{BufWriter, Write as _},
    sync::{Arc, Mutex},
};

use crate::{
    error::{DResult, DocError},
    fwrite,
    html::Node,
    impls::Impls,
    print::{self},
};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum ItemKind {
    Primitive,
    Module,
    Struct,
    Enum,
    Function,
    Entity,
    Pipeline,
    TypeAlias,
    Trait,
}

impl ItemKind {
    pub fn singular(&self) -> &'static str {
        match self {
            ItemKind::Primitive => "Primitive",
            ItemKind::Module => "Module",
            ItemKind::Struct => "Struct",
            ItemKind::Enum => "Enum",
            ItemKind::Function => "Function",
            ItemKind::Entity => "Entity",
            ItemKind::Pipeline => "Pipeline",
            ItemKind::TypeAlias => "Type Alias",
            ItemKind::Trait => "Trait",
        }
    }

    pub fn plural(&self) -> &'static str {
        match self {
            ItemKind::Primitive => "Primitives",
            ItemKind::Module => "Modules",
            ItemKind::Struct => "Structs",
            ItemKind::Enum => "Enums",
            ItemKind::Function => "Functions",
            ItemKind::Entity => "Entities",
            ItemKind::Pipeline => "Pipelines",
            ItemKind::TypeAlias => "Type Aliases",
            ItemKind::Trait => "Traits",
        }
    }

    pub fn color_class(&self) -> &'static str {
        match self {
            ItemKind::Primitive => "color-primitive",
            ItemKind::Module => "color-mod",
            ItemKind::Struct => "color-struct",
            ItemKind::Enum => "color-enum",
            ItemKind::Function => "color-fn",
            ItemKind::Entity => "color-entity",
            ItemKind::Pipeline => "color-pipeline",
            ItemKind::TypeAlias => "color-type-alias",
            ItemKind::Trait => "color-trait",
        }
    }

    /// Converts a [`NameID`] to an [`ItemKind`].
    ///
    /// This will result in [`None`] for e.g. generics, where we don't want to link to.
    pub(crate) fn from_name_id(nid: &NameID, symtab: &SymbolTable) -> Option<ItemKind> {
        if let Some(thing) = symtab.thing_by_id(nid) {
            match thing {
                Thing::Struct(_) => Some(ItemKind::Struct),
                Thing::EnumVariant(_) => None, // shouldn't happen
                Thing::Unit(loc) => match loc.inner.unit_kind.inner {
                    spade_hir::UnitKind::Function(_) => Some(ItemKind::Function),
                    spade_hir::UnitKind::Entity => Some(ItemKind::Entity),
                    spade_hir::UnitKind::Pipeline { .. } => Some(ItemKind::Pipeline),
                },
                Thing::Variable(_) => None,   // shouldn't happen
                Thing::Alias { .. } => None,  // shouldn't happen, revisit for `Self`
                Thing::ArrayLabel(_) => None, // shouldn't happen
                Thing::Module(_, _) => Some(ItemKind::Module),
                Thing::Trait(_) => Some(ItemKind::Trait),
                Thing::Dummy => None, // shouldn't happen
            }
        } else {
            match symtab.type_symbol_by_id(nid).inner {
                TypeSymbol::Declared(_, _, symtab::TypeDeclKind::Struct) => Some(ItemKind::Struct),
                TypeSymbol::Declared(_, _, symtab::TypeDeclKind::Enum) => Some(ItemKind::Enum),
                TypeSymbol::Declared(_, _, symtab::TypeDeclKind::Primitive { .. }) => {
                    Some(ItemKind::Primitive)
                }
                TypeSymbol::Declared(_, _, symtab::TypeDeclKind::Alias) => {
                    Some(ItemKind::TypeAlias)
                }
                TypeSymbol::GenericArg { .. } => None,
                TypeSymbol::GenericMeta(_) => None,
            }
        }
    }
}

struct ItemListEntry<'a> {
    name: &'a str,
    short_description: String,
}

impl<'a> ItemListEntry<'a> {
    #[allow(dead_code)]
    pub fn new_without_doc(name: &'a str) -> Self {
        ItemListEntry {
            name: name,
            short_description: String::new(),
        }
    }
    pub fn new_with_doc(name: &'a str, attributes: &AttributeList) -> Self {
        ItemListEntry {
            name,
            short_description: attributes
                .merge_docs()
                .lines()
                .take_while(|line| !line.is_empty())
                .join("\n"),
        }
    }
}

pub(crate) struct Generator {
    pub(crate) symtab: SymbolTable,
    pub(crate) current_dir: Utf8PathBuf,
    pub(crate) impls: Impls,
    pub(crate) diags: Arc<Mutex<DiagList>>,
    /// Used to determine if we need an additional ../ in a path.
    ///
    /// `a::b::c` would result in `a/b/c/index.html` for a module but
    /// `a/b/item.c.html` for a non-module.
    pub(crate) is_module: bool,
    pub(crate) primitives: ModuleBody,
}

impl Generator {
    pub fn doc_mod(&mut self, module: &ast::ModuleBody) -> DResult<()> {
        let mut contents: BTreeMap<ItemKind, Vec<ItemListEntry>> = BTreeMap::new();

        // We collect all items in this module body for its description and generate
        // the item pages along the way.
        for item in &module.members {
            match item {
                ast::Item::Type(t) => {
                    let (kind, attrs) = match &t.kind {
                        TypeDeclKind::Enum(e) => (ItemKind::Enum, &e.attributes),
                        TypeDeclKind::Struct(s) => (ItemKind::Struct, &s.attributes),
                        TypeDeclKind::Alias(a) => (ItemKind::TypeAlias, &a.attributes),
                    };
                    let name = t.name.as_str();
                    contents
                        .entry(kind)
                        .or_default()
                        .push(ItemListEntry::new_with_doc(name, attrs));

                    self.describe(FileName::Item(name), |g, b| g.doc_type(b, &t))?;
                }
                ast::Item::ExternalMod(m) => {
                    let name = m.name.as_str();
                    contents
                        .entry(ItemKind::Module)
                        .or_default()
                        .push(ItemListEntry::new_with_doc(name, &m.attributes));

                    // Don't need to generate stuff here as external mods have their own file and
                    // will thus be documented by the spadedoc main file iterator
                }
                ast::Item::Module(m) => {
                    let name = m.name.as_str();
                    contents
                        .entry(ItemKind::Module)
                        .or_default()
                        .push(ItemListEntry::new_with_doc(name, &m.attributes));

                    self.symtab.push_namespace(PathSegment::Named(m.name));
                    self.current_dir.push(name);
                    std::fs::create_dir_all(self.current_dir.as_path()).map_err(|_| {
                        DocError::FWriteError
                        // FIXME:
                        // Diagnostic::error(m, format!("Couldn't create folder at {dir} : {e}"))
                    })?;
                    let res = self.doc_mod(&m.body);
                    self.current_dir.pop();
                    self.symtab.pop_namespace();
                    res?;
                }
                ast::Item::ImplBlock(_) => {}
                ast::Item::Unit(u) => {
                    let kind = match &u.head.unit_kind.inner {
                        UnitKind::Function => ItemKind::Function,
                        UnitKind::Entity => ItemKind::Entity,
                        UnitKind::Pipeline(_) => ItemKind::Pipeline,
                    };
                    let name = u.head.name.as_str();
                    contents
                        .entry(kind)
                        .or_default()
                        .push(ItemListEntry::new_with_doc(name, &u.head.attributes));

                    self.describe(FileName::Item(name), |g, b| g.doc_unit(b, &u))?;
                }
                ast::Item::TraitDef(t) => {
                    let name = t.name.as_str();
                    contents
                        .entry(ItemKind::Trait)
                        .or_default()
                        .push(ItemListEntry::new_with_doc(name, &t.attributes));

                    self.describe(FileName::Item(name), |g, b| g.doc_trait(b, &t))?;
                }
                ast::Item::Use(_, _) => {}
            }
        }

        // Add primitives to core
        if self.symtab.current_namespace() == &Path::from_strs(&["core"]) {
            // Need to take them as we need to also borrow self for describe later on
            let primitives = std::mem::replace(&mut self.primitives.members, vec![]);
            for item in &primitives {
                match item {
                    ast::Item::ExternalMod(m) => {
                        let name = m.name.as_str();
                        contents
                            .entry(ItemKind::Primitive)
                            .or_default()
                            .push(ItemListEntry::new_with_doc(name, &m.attributes));

                        self.describe(FileName::Primitive(name), |g, b| g.doc_primitive(b, &m))?;
                    }
                    _ => {}
                }
            }
        }

        let Some(seg) = self.symtab.current_namespace().0.last().cloned() else {
            // root
            return Ok(());
        };
        let name = seg
            .to_named_str()
            .expect("Documenting module not in named path");

        self.symtab.pop_namespace();

        self.describe(FileName::Module(name), |g, b| {
            main(b, |b| {
                g.path_breadcrumbs(b)?;
                write_title(b, ItemKind::Module, name)?;
                write_markdown(&module.documentation.join("\n"), |md| {
                    collapsible(b, &["main_desc"], md.write())
                })?;
                for (kind, mut entries) in contents {
                    entries.sort_by_key(|e| e.name);
                    b.tag("section", |b| {
                        b.tag("h3", |b| {
                            fwrite!(b, kind.plural());
                            Ok(())
                        })?;
                        b.styled_tag("dl", &["item-table"], |b| {
                            let href: fn(&mut Node<'_>, &ItemListEntry) -> DResult<()> = match kind
                            {
                                ItemKind::Module => |b, e| {
                                    fwrite!(b, e.name, "/index.html");
                                    Ok(())
                                },
                                ItemKind::Primitive => |b, e| {
                                    fwrite!(b, "primitive.", e.name, ".html");
                                    Ok(())
                                },
                                _ => |b, e| {
                                    fwrite!(b, "item.", e.name, ".html");
                                    Ok(())
                                },
                            };
                            for entry in entries {
                                b.tag("dt", |b| {
                                    fwrite!(b, "<a class=\"", kind.color_class(), "\" href=\"");
                                    href(b, &entry)?;
                                    fwrite!(b, "\">", &entry.name, "</a>");
                                    Ok(())
                                })?;
                                b.tag("dd", |b| {
                                    write_markdown(&entry.short_description, |md| (md.write())(b))
                                })?;
                            }
                            Ok(())
                        })
                    })?;
                }
                Ok(())
            })
        })?;

        self.symtab.push_namespace(seg);

        Ok(())
    }

    fn doc_type(&mut self, body: &mut Node<'_>, t: &Loc<TypeDeclaration>) -> DResult<()> {
        let doc = match &t.inner.kind {
            TypeDeclKind::Enum(e) => e.attributes.merge_docs(),
            TypeDeclKind::Struct(s) => s.attributes.merge_docs(),
            TypeDeclKind::Alias(a) => a.attributes.merge_docs(),
        };

        let kind = match &t.inner.kind {
            TypeDeclKind::Enum(_) => ItemKind::Enum,
            TypeDeclKind::Struct(_) => ItemKind::Struct,
            TypeDeclKind::Alias(_) => ItemKind::TypeAlias,
        };

        let nameid = self
            .symtab
            .lookup_id(&Path::ident(t.name.clone()).nowhere(), true)
            .unwrap();

        main(body, |body| {
            self.path_breadcrumbs(body)?;
            write_title(body, kind, t.inner.name.as_str())?;
            self.in_codeblock(body, |b| match &t.inner.kind {
                TypeDeclKind::Enum(e) => self.print_enum(b, e, &t.visibility, &t.generic_args),
                TypeDeclKind::Struct(s) => self.print_struct(b, s, &t.visibility, &t.generic_args),
                TypeDeclKind::Alias(_) => Ok(()),
            })?;
            write_markdown(&doc, |md| collapsible(body, &["main_desc"], md.write()))?;

            // (Trait) implementation blocks
            if let Some((direct, traits)) = self.impls.for_type.get(&nameid).cloned() {
                if !direct.is_empty() {
                    body.tag("h2", |b| {
                        fwrite!(b, "Implementations");
                        Ok(())
                    })?;
                }

                for d in direct {
                    self.impl_block(
                        body,
                        &d.type_params,
                        None,
                        &d.target,
                        &d.units,
                        &d.where_clauses,
                    )?;
                }

                if !traits.is_empty() {
                    body.tag("h2", |b| {
                        fwrite!(b, "Trait Implementations");
                        Ok(())
                    })?;
                }

                for t in traits {
                    self.impl_block(
                        body,
                        &t.type_params,
                        Some(&t.r#trait),
                        &t.target,
                        &t.units,
                        &t.where_clauses,
                    )?;
                }
            }

            Ok(())
        })
    }

    fn impl_block(
        &mut self,
        body: &mut Node<'_>,
        generics: &Option<Loc<Vec<Loc<TypeParam>>>>,
        r#trait: Option<&TraitSpec>,
        target: &TypeSpec,
        units: &[Loc<Unit>],
        where_clauses: &[WhereClause],
    ) -> DResult<()> {
        body.open_details(
            |body| {
                body.styled_tag("span", &["impl-heading"], |body| {
                    if let Some(params) = &generics {
                        fwrite!(body, "impl&lt;");

                        print::separated(body, ", ", params.iter(), |b, p| {
                            self.print_type_param(b, &p.inner)
                        })?;

                        fwrite!(body, "&gt; ");
                    } else {
                        fwrite!(body, "impl ");
                    }
                    if let Some(r#trait) = r#trait {
                        self.print_trait_spec(body, r#trait)?;
                        fwrite!(body, " for ");
                    }
                    self.print_type_spec(body, target)?;
                    self.print_where_clauses(body, &where_clauses)?;
                    Ok(())
                })
            },
            |body| {
                body.styled_tag("div", &["impl-items"], |body| {
                    for u in units {
                        let doc = u.head.attributes.merge_docs();

                        if !doc.is_empty() {
                            body.open_details(
                                |body| {
                                    body.styled_tag("span", &["impl-unit-head"], |body| {
                                        self.print_unit_head(body, &u.head)
                                    })
                                },
                                |body| write_markdown(&doc, |md| (md.write())(body)),
                            )?;
                        } else {
                            body.tag("div", |body| {
                                body.styled_tag("span", &["impl-unit-head"], |body| {
                                    self.print_unit_head(body, &u.head)
                                })
                            })?;
                        }
                    }
                    Ok(())
                })
            },
        )
    }

    fn doc_unit(&mut self, body: &mut Node<'_>, u: &Loc<Unit>) -> DResult<()> {
        let doc = u.head.attributes.merge_docs();

        let kind = match &u.head.unit_kind.inner {
            UnitKind::Function => ItemKind::Function,
            UnitKind::Entity => ItemKind::Entity,
            UnitKind::Pipeline(_) => ItemKind::Pipeline,
        };

        main(body, |body| {
            self.path_breadcrumbs(body)?;
            write_title(body, kind, u.head.name.as_str())?;
            self.in_codeblock(body, |b| self.print_unit_head(b, &u.head))?;
            write_markdown(&doc, |md| collapsible(body, &["main_desc"], md.write()))?;

            Ok(())
        })
    }

    fn doc_trait(&mut self, body: &mut Node<'_>, t: &Loc<TraitDef>) -> DResult<()> {
        let doc = t.attributes.merge_docs();

        main(body, |body| {
            self.path_breadcrumbs(body)?;
            write_title(body, ItemKind::Trait, t.name.as_str())?;
            self.in_codeblock(body, |b| self.print_trait_def(b, &t))?;
            write_markdown(&doc, |md| collapsible(body, &["main_desc"], md.write()))?;

            Ok(())
        })
    }

    fn doc_primitive(&mut self, body: &mut Node<'_>, m: &Loc<ExternalMod>) -> DResult<()> {
        let doc = m.attributes.merge_docs();

        main(body, |body| {
            self.path_breadcrumbs(body)?;
            write_title(body, ItemKind::Primitive, m.name.as_str())?;
            write_markdown(&doc, |md| collapsible(body, &["main_desc"], md.write()))?;

            Ok(())
        })
    }

    fn path_breadcrumbs(&mut self, body: &mut Node<'_>) -> DResult<()> {
        let from = self.symtab.current_namespace().0.as_slice();

        body.tag("div", |d| {
            self.link_to(d, &[], ItemKind::Module, |a| {
                fwrite!(a, "::");
                Ok(())
            })?;

            for (i, seg) in from.iter().enumerate() {
                let seg = seg
                    .to_named_str()
                    .expect("Breadcrumb to non-named path segment");
                self.link_to(d, &from[..(i + 1)], ItemKind::Module, |a| {
                    fwrite!(a, seg, "::");
                    Ok(())
                })?;
            }

            Ok(())
        })
    }

    /// Wraps the given builder function `f` inside an anchor tag to the specified identifier.
    ///
    /// Don't forget to use `symtab.lookup_id().1` to get the actual path, otherwise this will
    /// create an invalid link.
    pub(super) fn link_to(
        &self,
        n: &mut Node<'_>,
        to: &[PathSegment],
        kind: ItemKind,
        f: impl FnOnce(&mut Node<'_>) -> DResult<()>,
    ) -> DResult<()> {
        #[inline(always)]
        fn name(s: &PathSegment) -> &str {
            s.to_named_str()
                .expect("Tried to create file in non-named path segment")
        }

        fwrite!(n, "<a class=\"", kind.color_class(), "\" href=\"");

        let mut from = self.symtab.current_namespace().0.iter();

        // Determine path end to `to/item.end.html` or `to/end/index.html` based on
        // whether it is targeting a module or not.
        let core;
        let (mut to, end) = match kind {
            ItemKind::Module => (to.iter(), String::from("index.html")),
            ItemKind::Primitive => {
                let (end, _) = to.split_last().expect("No segment in path to Item");
                core = [PathSegment::Named(Identifier::intern("core").nowhere())];
                (core.iter(), format!("primitive.{}.html", name(end)))
            }
            _ => {
                let (end, rest) = to.split_last().expect("No segment in path to Item");
                (rest.iter(), format!("item.{}.html", name(end)))
            }
        };

        // When we describe a module, we are one hierarchy level deeper,
        // e.g. `a/b/c/index.html` instead of `a/b/item.c.html`.
        if self.is_module {
            fwrite!(n, "../");
        }

        // Check at which point the given paths diverge
        let mut to_next = to.next();
        'diverge: while let Some(seg_from) = from.next() {
            if to_next == Some(seg_from) {
                to_next = to.next();
            } else {
                fwrite!(n, "../");
                break 'diverge;
            }
        }
        // Go up from `from` to the common root
        while let Some(_) = from.next() {
            fwrite!(n, "../");
        }
        // Append to path and then the path end based on whether it's targeting a module or not from above
        if let Some(seg) = to_next {
            fwrite!(n, name(seg), "/");
        }
        for seg in to {
            fwrite!(n, name(seg), "/");
        }

        fwrite!(n, &end, "\">");
        f(n)?;
        fwrite!(n, "</a>");

        Ok(())
    }

    /// Describes an item or module by providing a html node inside the common wrapper.
    ///
    /// Also sets the `is_module` flag.
    fn describe(
        &mut self,
        name: FileName<'_>,
        f: impl FnOnce(&mut Generator, &mut Node<'_>) -> DResult<()>,
    ) -> DResult<()> {
        let name = match name {
            FileName::Module(name) => {
                self.current_dir.push("index.html");
                self.is_module = true;
                name
            }
            FileName::Item(name) => {
                self.current_dir.push(format!("item.{name}.html"));
                self.is_module = false;
                name
            }
            FileName::Primitive(name) => {
                self.current_dir.push(format!("primitive.{name}.html"));
                self.is_module = false;
                name
            }
        };
        let file = File::create(self.current_dir.as_path()).unwrap();
        self.current_dir.pop();
        std::fs::write(
            &self.current_dir.join("styles.css"),
            include_str!("./styles.css"),
        )
        .expect(&format!(
            "Failed to write style.css into {}",
            self.current_dir
        ));
        let mut buf = BufWriter::new(file);
        let mut node = Node::new(&mut buf);

        fwrite!(&mut node, "<!DOCTYPE html>");
        node.tag("html", |html| {
            html.tag("head", |head| {
                fwrite!(head, r#"<meta charset="utf-8">"#);
                fwrite!(
                    head,
                    r#"<meta name="viewport" content="width=device-width,initial-scale=1">"#
                );
                fwrite!(head, r#"<link rel="stylesheet" href="styles.css">"#);
                head.tag("title", |t| {
                    let ns = &self.symtab.current_namespace().0;
                    if ns.is_empty() {
                        fwrite!(t, name, " - Spadedoc");
                    } else {
                        fwrite!(t, name, " in ");
                        for seg in ns {
                            fwrite!(t, "::", seg.unwrap_named().as_str());
                        }
                        fwrite!(t, " - Spadedoc");
                    }
                    Ok(())
                })
            })?;
            html.tag("body", |n| f(self, n))
        })?;

        buf.flush().unwrap();

        Ok(())
    }
}

enum FileName<'s> {
    Module(&'s str),
    Item(&'s str),
    Primitive(&'s str),
}
fn main(b: &mut Node<'_>, f: impl FnOnce(&mut Node<'_>) -> DResult<()>) -> DResult<()> {
    b.tag("main", f)
}

fn collapsible(
    b: &mut Node<'_>,
    styles: &[&str],
    f: impl FnOnce(&mut Node<'_>) -> DResult<()>,
) -> DResult<()> {
    fwrite!(b, "<details open class=\"");
    for s in styles {
        fwrite!(b, s, " ");
    }
    fwrite!(b, "\">");
    b.styled_tag("summary", &["hidden-open-summary"], |b| {
        b.tag("span", |b| {
            fwrite!(b, "Expand");
            Ok(())
        })
    })?;
    f(b)?;
    fwrite!(b, "</details>");
    Ok(())
}

fn write_title(node: &mut Node<'_>, kind: ItemKind, name: &str) -> DResult<()> {
    node.styled_tag("h1", &["item-heading"], |h| {
        fwrite!(h, kind.singular(), " ");
        h.styled_tag("span", &[kind.color_class()], |s| {
            fwrite!(s, name);
            Ok(())
        })
    })
}

struct MarkdownContent {
    html_output: String,
}

impl MarkdownContent {
    fn write(self) -> impl FnOnce(&mut Node<'_>) -> DResult<()> {
        move |n| {
            ammonia::Builder::new()
                .clean(&self.html_output)
                .write_to(n.io())
                .unwrap();
            Ok(())
        }
    }
}

fn write_markdown<'n>(
    markdown: &str,
    f: impl FnOnce(MarkdownContent) -> DResult<()>,
) -> DResult<()> {
    let mut options = Options::empty();
    options.insert(Options::ENABLE_TABLES);
    options.insert(Options::ENABLE_STRIKETHROUGH);
    options.insert(Options::ENABLE_SMART_PUNCTUATION);
    options.insert(Options::ENABLE_MATH);
    options.insert(Options::ENABLE_GFM);
    let parser = Parser::new_ext(markdown, options);

    let mut html_output = String::new();
    pulldown_cmark::html::push_html(&mut html_output, parser);
    if !html_output.is_empty() {
        f(MarkdownContent { html_output })?;
    }

    Ok(())
}
