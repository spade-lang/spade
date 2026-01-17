use std::{borrow::Cow, fmt::Display};

use askama::Template;
use camino::Utf8PathBuf;
use color_eyre::eyre::Result;
use pulldown_cmark::{Options, Parser};
use spade_common::name::PathSegment;
use spade_hir::{Attribute, TypeParam, UnitKind};
use spade_types::meta_types::MetaType;
use spec::Spec;

pub mod spec;

#[derive(Template)]
#[template(path = "item.html")]
pub struct Item<'r> {
    pub root_namespace_path: Utf8PathBuf,
    pub root_namespace: &'r str,

    pub style_ref: Utf8PathBuf,
    pub spade_highlight_path: Utf8PathBuf,
    pub spade_css_path: Utf8PathBuf,

    pub name: &'r str,
    pub namespace: Option<Path>,
    pub kind: ItemKind,

    pub signature: Option<Signature<'r>>,
    pub doc: RenderedMarkdown,
    pub content: &'r [ItemContent<'r>],
}

// Order of items here relates to ordering on module pages.
// (tho I didn't order them specifically, MR welcome :>)
#[derive(Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum ItemKind {
    Module,
    Function,
    Entity,
    Pipeline,
    Struct,
    Enum,
    TypeAlias,
    Primitive,
    Trait,
}
impl ItemKind {
    pub fn plural(&self) -> &'static str {
        match self {
            ItemKind::Module => "Modules",
            ItemKind::Function => "Functions",
            ItemKind::Entity => "Entities",
            ItemKind::Pipeline => "Pipelines",
            ItemKind::Struct => "Structs",
            ItemKind::Enum => "Enums",
            ItemKind::TypeAlias => "Type aliases",
            ItemKind::Primitive => "Primitives",
            ItemKind::Trait => "Traits",
        }
    }
}

/// ```askama
/// {{ self.target.render()?|safe }} {%if !constraints.is_empty() %} {{ ": " }} {% endif %} {{ self.constraints|join(" + ") }}
/// ```
#[derive(Debug, Template)]
#[template(in_doc = true, ext = "html")]
pub struct WhereClause<'r> {
    pub target: Spec<'r>,
    pub constraints: Vec<Spec<'r>>,
}

/// ```askama
/// {% if let Some(meta) = &meta %} {{ meta }} {{" "}} {% endif %} {{ self.inner.render()?|safe }}
/// ```
#[derive(Debug, Template)]
#[template(in_doc = true, ext = "html")]
pub struct GenericTypeParam<'r> {
    pub meta: Option<String>,
    pub inner: WhereClause<'r>,
}

impl<'r> GenericTypeParam<'r> {
    pub fn mirror_typeparam(type_param: &'r TypeParam) -> Result<Self> {
        let where_clause = WhereClause {
            target: Spec::Declared {
                name: Cow::Borrowed(type_param.ident().unwrap().inner.as_str()),
                type_args: vec![],
            },
            constraints: type_param
                .trait_bounds
                .iter()
                .map(|trait_spec| Spec::mirror_traitspec(trait_spec))
                .collect::<Result<Vec<_>>>()?,
        };

        Ok(GenericTypeParam {
            meta: match type_param.meta {
                MetaType::Uint => Some("#uint".into()),
                MetaType::Int => Some("#int".into()),
                _ => None,
            },
            inner: where_clause,
        })
    }
}

// FIXME: params.len() > 2 is a dumb heuristic, should actually compute length
/// ```askama
/// {% if is_external %}
///     {{"extern "}}
/// {% endif %}
/// {% match kind %}
///     {% when spade_hir::UnitKind::Function with (_) %}
///         fn
///     {% when spade_hir::UnitKind::Entity %}
///         entity
///     {% when spade_hir::UnitKind::Pipeline with { depth, .. } %}
///         pipeline({{ Spec::mirror_typeexpr(&depth.inner)? }})
/// {% endmatch %}
/// {{ " " }} {{ name }}
/// {% if !type_params.is_empty() %}
/// <
///     {%if type_params.len() > 2 %}
///         {{"\n    "}}{{ type_params|join(",\n    ")|safe }}{{"\n"}}
///     {%else%}
///         {{ type_params|join(", ")|safe }}
///     {%endif%}
/// >
/// {% endif %}
/// (
///     {%if params.len() > 2 %}
///         {{"\n    "}}{{ params|join(",\n    ")|safe }}{{"\n"}}
///     {%else%}
///         {{ params|join(", ")|safe }}
///     {%endif%}
/// )
/// {% if let Some(out) = output +%} -> {{ " " }} {{ out|safe }}{% endif %}
/// {% if !where_clauses.is_empty() %}
/// {{ "\n    where "}}
/// {% if where_clauses.len() > 2 %}
/// {{"\n          "}}
/// {% endif %}
/// {{ where_clauses|join(",\n          ") }}
/// {% endif %}
/// ;
/// ```
#[derive(Debug, Template)]
#[template(in_doc = true, ext = "html")]
pub struct UnitSignature<'r> {
    pub is_external: bool,
    pub attributes: Vec<Attribute>,
    pub kind: &'r UnitKind,
    pub name: &'r str,
    // we treat the type parameter as a where clause since they are basically the same thing. the
    // first tuple argument is whether there should be a #uint or something
    pub type_params: Vec<GenericTypeParam<'r>>,
    pub params: Vec<Param<'r>>,
    pub output: Option<Spec<'r>>,
    pub where_clauses: Vec<WhereClause<'r>>,
}

/// ```askama
/// {{ "struct " }} {{ name }}
/// {% if !type_params.is_empty() %}
/// <
///     {%if type_params.len() > 2 %}
///         {{"\n    "}}{{ type_params|join(",\n    ")|safe }}{{"\n"}}
///     {%else%}
///         {{ type_params|join(", ")|safe }}
///     {%endif%}
/// > {{ " " }}
/// {% endif %}
/// {
///     {{"\n    "}}{{ members|join(",\n    ")|safe }}{{"\n"}}
/// }
/// ```
#[derive(Debug, Template)]
#[template(in_doc = true, ext = "html")]
pub struct StructSignature<'r> {
    pub attributes: Vec<Attribute>,
    pub name: String,
    pub type_params: Vec<GenericTypeParam<'r>>,
    pub members: Vec<Param<'r>>,
}

#[derive(Debug, Template)]
pub enum Signature<'r> {
    /// ```askama
    /// {{ self.0|safe }}
    /// ```
    #[template(in_doc = true, ext = "html")]
    UnitSignature(UnitSignature<'r>),
    /// ```askama
    /// {{ self.0|safe }}
    /// ```
    #[template(in_doc = true, ext = "html")]
    StructSignature(StructSignature<'r>),
}

/// ```askama
/// {{ self.0 }}: {{+ self.1|safe }}
/// ```
#[derive(Debug, Template)]
#[template(in_doc = true, ext = "html")]
pub struct Param<'r>(pub &'r str, pub Spec<'r>);

pub enum ItemContent<'r> {
    ItemListing(ItemListing<'r>),
    Variants(Variants<'r>),
    Implementation(Implementation<'r>),
}
impl Display for ItemContent<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ItemContent::ItemListing(listing) => listing.fmt(f),
            ItemContent::Variants(var) => var.fmt(f),
            ItemContent::Implementation(imp) => imp.fmt(f),
        }
    }
}

#[derive(Debug)]
pub struct RenderedMarkdown(String);

impl RenderedMarkdown {
    pub fn render(markdown: &str) -> Self {
        let mut options = Options::empty();
        options.insert(Options::ENABLE_TABLES);
        options.insert(Options::ENABLE_STRIKETHROUGH);
        options.insert(Options::ENABLE_SMART_PUNCTUATION);
        options.insert(Options::ENABLE_MATH);
        options.insert(Options::ENABLE_GFM);
        let parser = Parser::new_ext(markdown, options);

        let mut html_output = String::new();
        pulldown_cmark::html::push_html(&mut html_output, parser);

        let sanitized = ammonia::clean(&html_output);

        Self(sanitized)
    }
}
impl Display for RenderedMarkdown {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

#[derive(Template)]
#[template(path = "item_listing.html")]
pub struct ItemListing<'r> {
    pub title: &'r str,
    pub entries: Vec<ListedEntry<'r>>,
}
pub struct ListedEntry<'r> {
    pub name: &'r str,
    pub link: String,
}

#[derive(Template)]
#[template(path = "variants.html")]
pub struct Variants<'r>(pub Vec<Variant<'r>>);
pub enum Variant<'r> {
    Unit(Cow<'r, str>, RenderedMarkdown),
    Valued(Cow<'r, str>, Vec<Param<'r>>, RenderedMarkdown),
}

/// ```askama
/// <pre class="member"><code class="language-spade hljs">{{ signature }}</code></pre>
/// {{ doc|safe }}
/// ````
#[derive(Debug, Template)]
#[template(in_doc = true, ext = "html")]
pub struct ImplementationMember<'r> {
    pub doc: RenderedMarkdown,
    pub signature: Signature<'r>,
}

#[derive(Debug, Template)]
#[template(path = "implementation.html")]
pub struct Implementation<'r> {
    pub type_params: Vec<GenericTypeParam<'r>>,
    pub impld_trait: Option<Cow<'r, str>>,
    pub target: Spec<'r>,
    pub members: Vec<ImplementationMember<'r>>,
}

#[derive(Template)]
#[template(path = "path.html")]
pub struct Path {
    segments: Vec<Segment>,
    last: Segment,
}

pub struct Segment {
    value: String,
}

impl Path {
    pub fn new(path: &[PathSegment]) -> Option<Self> {
        let (last, segments) = path.split_last()?;
        Some(Self {
            segments: segments
                .iter()
                .map(|value| Segment {
                    value: value.to_string(),
                })
                .collect(),
            last: Segment {
                value: last.to_string(),
            },
        })
    }
}
