use camino::Utf8PathBuf;
use pulldown_cmark::{Options, Parser};
use spade_ast::{self as ast, TraitDef, TypeDeclKind, TypeDeclaration, Unit, UnitKind};
use spade_common::{
    location_info::{Loc, WithLocation},
    name::{NameID, Path, PathSegment},
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
    errors::{DResult, DocError},
    fwrite,
    html::Node,
    impls::Impls,
    print,
};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum ItemKind {
    Module,
    Struct,
    Enum,
    Function,
    Entity,
    Pipeline,
    Primitive,
    TypeAlias,
    Trait,
}

impl ItemKind {
    pub fn singular(&self) -> &'static str {
        match self {
            ItemKind::Module => "Module",
            ItemKind::Struct => "Struct",
            ItemKind::Enum => "Enum",
            ItemKind::Function => "Function",
            ItemKind::Entity => "Entity",
            ItemKind::Pipeline => "Pipeline",
            ItemKind::Primitive => "Primitive",
            ItemKind::TypeAlias => "Type Alias",
            ItemKind::Trait => "Trait",
        }
    }

    pub fn plural(&self) -> &'static str {
        match self {
            ItemKind::Module => "Modules",
            ItemKind::Struct => "Structs",
            ItemKind::Enum => "Enums",
            ItemKind::Function => "Functions",
            ItemKind::Entity => "Entities",
            ItemKind::Pipeline => "Pipelines",
            ItemKind::Primitive => "Primitives",
            ItemKind::TypeAlias => "Type Aliases",
            ItemKind::Trait => "Traits",
        }
    }

    pub fn scolor(&self) -> &'static str {
        match self {
            ItemKind::Module => "color-mod",
            ItemKind::Struct => "color-struct",
            ItemKind::Enum => "color-enum",
            ItemKind::Function => "color-fn",
            ItemKind::Entity => "color-entity",
            ItemKind::Pipeline => "color-pipeline",
            ItemKind::Primitive => "color-primitive",
            ItemKind::TypeAlias => "color-type-alias",
            ItemKind::Trait => "color-trait",
        }
    }

    pub(crate) fn from_id(nid: &NameID, symtab: &SymbolTable) -> ItemKind {
        if let Some(thing) = symtab.thing_by_id(nid) {
            match thing {
                Thing::Struct(_) => ItemKind::Struct,
                Thing::EnumVariant(_) => todo!(),
                Thing::Unit(loc) => match loc.inner.unit_kind.inner {
                    spade_hir::UnitKind::Function(_) => ItemKind::Function,
                    spade_hir::UnitKind::Entity => ItemKind::Entity,
                    spade_hir::UnitKind::Pipeline { .. } => ItemKind::Pipeline,
                },
                Thing::Variable(_) => todo!(),
                Thing::Alias { .. } => unreachable!(),
                Thing::ArrayLabel(_) => todo!(),
                Thing::Module(_, _) => ItemKind::Module,
                Thing::Trait(_) => ItemKind::Trait,
                Thing::Dummy => todo!(),
            }
        } else {
            match symtab.type_symbol_by_id(nid).inner {
                TypeSymbol::Declared(_, _, symtab::TypeDeclKind::Struct) => ItemKind::Struct,
                TypeSymbol::Declared(_, _, symtab::TypeDeclKind::Enum) => ItemKind::Enum,
                TypeSymbol::Declared(_, _, symtab::TypeDeclKind::Primitive { .. }) => {
                    ItemKind::Primitive
                }
                TypeSymbol::Declared(_, _, symtab::TypeDeclKind::Alias) => unreachable!(),
                TypeSymbol::GenericArg { .. } => todo!(),
                TypeSymbol::GenericMeta(_) => todo!(),
            }
        }
    }
}

pub(crate) struct Generator {
    pub(crate) symtab: SymbolTable,
    pub(crate) current_dir: Utf8PathBuf,
    pub(crate) impls: Impls,
    pub(crate) diags: Arc<Mutex<DiagList>>,
}

impl Generator {
    pub fn doc_mod(&mut self, module: &ast::ModuleBody) -> DResult<()> {
        println!("{}", self.current_dir);

        let mut contents: BTreeMap<ItemKind, Vec<&'static str>> = BTreeMap::new();

        for item in &module.members {
            match item {
                ast::Item::Type(t) => {
                    let kind = match &t.kind {
                        TypeDeclKind::Enum(_) => ItemKind::Enum,
                        TypeDeclKind::Struct(_) => ItemKind::Struct,
                        TypeDeclKind::Alias(_) => ItemKind::TypeAlias,
                    };
                    let name = t.name.as_str();
                    contents.entry(kind).or_default().push(name);

                    self.describe(FileName::Item(name), |g, b| g.doc_type(b, &t))?;
                }
                ast::Item::ExternalMod(m) => {
                    contents
                        .entry(ItemKind::Module)
                        .or_default()
                        .push(m.name.as_str());
                }
                ast::Item::Module(m) => {
                    let name = m.name.as_str();
                    contents.entry(ItemKind::Module).or_default().push(name);
                    self.symtab.push_namespace(PathSegment::Named(m.name));
                    self.current_dir.push(name);
                    std::fs::create_dir_all(self.current_dir.as_path()).map_err(|_| {
                        DocError::FWriteError
                        // TODO:
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
                    contents.entry(kind).or_default().push(name);
                    self.describe(FileName::Item(name), |g, b| g.doc_unit(b, &u))?;
                }
                ast::Item::TraitDef(t) => {
                    let name = t.name.as_str();
                    contents.entry(ItemKind::Trait).or_default().push(name);
                    self.describe(FileName::Item(name), |g, b| g.doc_trait(b, &t))?;
                }
                ast::Item::Use(_, _) => {}
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

        self.describe(FileName::Module, |g, b| {
            main(b, |b| {
                g.path_breadcrumbs(b, true)?;
                write_title(b, ItemKind::Module, name)?;
                write_markdown(&module.documentation.join("\n"), |md| {
                    collapsable(b, &["main_desc"], md.write())
                })?;
                for (kind, mut entries) in contents {
                    entries.sort();
                    b.tag("section", |b| {
                        b.tag("h3", |b| {
                            fwrite!(b, kind.plural());
                            Ok(())
                        })?;
                        b.stag("ul", &["clean_ul"], |b| {
                            if kind == ItemKind::Module {
                                for name in entries {
                                    b.tag("li", |b| {
                                        fwrite!(
                                            b,
                                            "<a class=\"",
                                            ItemKind::Module.scolor(),
                                            "\" href=\"",
                                            &name,
                                            "/index.html\">",
                                            &name,
                                            "</a>"
                                        );
                                        Ok(())
                                    })?;
                                }
                                Ok(())
                            } else {
                                for name in entries {
                                    b.tag("li", |b| {
                                        fwrite!(
                                            b,
                                            "<a class=\"",
                                            kind.scolor(),
                                            "\" href=\"item.",
                                            &name,
                                            ".html\">",
                                            &name,
                                            "</a>"
                                        );
                                        Ok(())
                                    })?;
                                }
                                Ok(())
                            }
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
            self.path_breadcrumbs(body, false)?;
            write_title(body, kind, t.inner.name.as_str())?;
            write_markdown(&doc, |md| collapsable(body, &["main_desc"], md.write()))?;

            if let Some((direct, traits)) = self.impls.for_type.get(&nameid) {
                for d in direct {
                    if let Some(params) = &d.type_params {
                        fwrite!(body, "impl&lt;");
                        print::seperated(body, ", ", params.iter(), |b, p| {
                            self.print_type_param(b, &p.inner)
                        })?;
                        fwrite!(body, "&gt; ");
                    } else {
                        fwrite!(body, "impl ");
                    }
                    self.print_type_spec(body, &d.target)?;
                    for unit in &d.units {
                        self.in_codeblock(body, |b| self.print_unithead(b, &unit.head))?;
                    }
                    fwrite!(body, "<br>");
                }
                for t in traits {
                    if let Some(params) = &t.type_params {
                        fwrite!(body, "impl&lt;");
                        print::seperated(body, ", ", params.iter(), |b, p| {
                            self.print_type_param(b, &p.inner)
                        })?;
                        fwrite!(body, "&gt; ");
                    } else {
                        fwrite!(body, "impl ");
                    }
                    self.print_trait_spec(body, &t.r#trait)?;
                    fwrite!(body, " for ");
                    self.print_type_spec(body, &t.target)?;
                    for unit in &t.units {
                        self.in_codeblock(body, |b| self.print_unithead(b, &unit.head))?;
                    }
                    fwrite!(body, "<br>");
                }
            }

            Ok(())
        })
    }

    fn doc_unit(&mut self, body: &mut Node<'_>, u: &Loc<Unit>) -> DResult<()> {
        let doc = u.head.attributes.merge_docs();

        let kind = match &u.head.unit_kind.inner {
            UnitKind::Function => ItemKind::Function,
            UnitKind::Entity => ItemKind::Entity,
            UnitKind::Pipeline(_) => ItemKind::Pipeline,
        };

        main(body, |body| {
            self.path_breadcrumbs(body, false)?;
            write_title(body, kind, u.head.name.as_str())?;
            self.in_codeblock(body, |b| self.print_unithead(b, &u.head))?;
            write_markdown(&doc, |md| collapsable(body, &["main_desc"], md.write()))?;

            Ok(())
        })
    }

    fn doc_trait(&mut self, body: &mut Node<'_>, t: &Loc<TraitDef>) -> DResult<()> {
        main(body, |body| {
            self.path_breadcrumbs(body, false)?;
            write_title(body, ItemKind::Trait, t.name.as_str())?;

            for unit in &t.methods {
                self.in_codeblock(body, |b| self.print_unithead(b, &unit))?;
            }

            Ok(())
        })
    }

    fn path_breadcrumbs(&mut self, body: &mut Node<'_>, from_mod: bool) -> DResult<()> {
        let from = self.symtab.current_namespace().0.as_slice();

        body.tag("div", |d| {
            self.link_to(d, &[], ItemKind::Module, from_mod, true, |a| {
                fwrite!(a, "::");
                Ok(())
            })?;

            for (i, seg) in from.iter().enumerate() {
                let seg = seg
                    .to_named_str()
                    .expect("Breadcrumb to non-named path segment");
                self.link_to(d, &from[..(i + 1)], ItemKind::Module, from_mod, true, |a| {
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
        from_mod: bool,
        to_mod: bool,
        f: impl FnOnce(&mut Node<'_>) -> DResult<()>,
    ) -> DResult<()> {
        fwrite!(n, "<a class=\"", kind.scolor(), "\" href=\"");

        #[inline(always)]
        fn name(s: &PathSegment) -> &str {
            s.to_named_str()
                .expect("Tried to create file in non-named path segment")
        }

        let mut from = self.symtab.current_namespace().0.iter();
        let (mut to, end) = match to_mod {
            false => {
                let (end, rest) = to.split_last().expect("No segment in path to Item");
                (rest.iter(), format!("item.{}.html", name(end)))
            }
            true => (to.iter(), String::from("index.html")),
        };

        if from_mod {
            fwrite!(n, "../");
        }

        let mut to_next = to.next();
        'diverge: while let Some(seg_from) = from.next() {
            if to_next == Some(seg_from) {
                to_next = to.next();
            } else {
                fwrite!(n, "../");
                break 'diverge;
            }
        }
        while let Some(_) = from.next() {
            fwrite!(n, "../");
        }
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

    fn describe(
        &mut self,
        name: FileName<'_>,
        f: impl FnOnce(&mut Generator, &mut Node<'_>) -> DResult<()>,
    ) -> DResult<()> {
        match name {
            FileName::Module => self.current_dir.push("index.html"),
            FileName::Item(name) => self.current_dir.push(format!("item.{name}.html")),
        }
        let file = File::create(self.current_dir.as_path()).unwrap();
        self.current_dir.pop();
        let mut buf = BufWriter::new(file);
        let mut node = Node::new(&mut buf);

        fwrite!(&mut node, "<!DOCTYPE html>");
        node.tag("html", |html| {
            html.tag("head", |head| {
                fwrite!(head, r#"<meta charset="utf-8">"#);
                fwrite!(head, r#"<link rel="stylesheet" href="/styles.css">"#);
                head.tag("title", |t| {
                    fwrite!(t, "Some file - Spadedoc");
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
    Module,
    Item(&'s str),
}
fn main(b: &mut Node<'_>, f: impl FnOnce(&mut Node<'_>) -> DResult<()>) -> DResult<()> {
    b.tag("main", f)
}

fn collapsable(
    b: &mut Node<'_>,
    styles: &[&str],
    f: impl FnOnce(&mut Node<'_>) -> DResult<()>,
) -> DResult<()> {
    fwrite!(b, "<details open class=\"");
    for s in styles {
        fwrite!(b, s, " ");
    }
    fwrite!(b, "\">");
    b.tag("summary", |b| {
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
    node.stag("h1", &["item-heading"], |h| {
        fwrite!(h, kind.singular(), " ");
        h.stag("span", &[kind.scolor()], |s| {
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
