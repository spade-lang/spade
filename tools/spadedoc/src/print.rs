use crate::{
    error::{DResult, DocError},
    fwrite,
    generate::{Generator, ItemKind},
    html::Node,
};
use spade_ast::{
    Enum, ParameterList, Struct, TraitSpec, TypeExpression, TypeParam, TypeSpec, UnitHead,
};
use spade_common::{
    location_info::{Loc, WithLocation},
    name::{Path, Visibility},
};
use std::io::Write as _;

impl Generator {
    pub fn in_codeblock(
        &self,
        b: &mut Node<'_>,
        f: impl FnOnce(&mut Node<'_>) -> DResult<()>,
    ) -> DResult<()> {
        fwrite!(b, "<pre><code>");
        f(b)?;
        fwrite!(b, "</pre></code>");
        Ok(())
    }

    pub fn print_enum(
        &self,
        b: &mut Node<'_>,
        e: &Enum,
        visibility: &Visibility,
        generic_args: &Option<Loc<Vec<Loc<TypeParam>>>>,
    ) -> DResult<()> {
        self.print_visibility(b, visibility)?;

        fwrite!(b, "enum ");

        fwrite!(b, e.name.as_str());

        if let Some(params) = generic_args {
            fwrite!(b, "&lt;");
            separated(b, ", ", params.iter(), |b, p| {
                self.print_type_param(b, &p.inner)
            })?;
            fwrite!(b, "&gt;");
        }

        fwrite!(b, " {");

        for variant in &e.variants {
            fwrite!(b, "<br>&emsp;", variant.name.as_str());
            if let Some(fields) = &variant.args {
                fwrite!(b, " { ");
                self.print_parameter_list(b, fields)?;
                fwrite!(b, " }");
            }
            fwrite!(b, ",");
        }

        if e.variants.is_empty() {
            fwrite!(b, "}");
        } else {
            fwrite!(b, "<br>}");
        }

        Ok(())
    }

    pub fn print_struct(
        &self,
        b: &mut Node<'_>,
        s: &Struct,
        visibility: &Visibility,
        generic_args: &Option<Loc<Vec<Loc<TypeParam>>>>,
    ) -> DResult<()> {
        self.print_visibility(b, visibility)?;

        fwrite!(b, "struct ");

        fwrite!(b, s.name.as_str());

        if let Some(params) = generic_args {
            fwrite!(b, "&lt;");
            separated(b, ", ", params.iter(), |b, p| {
                self.print_type_param(b, &p.inner)
            })?;
            fwrite!(b, "&gt;");
        }

        fwrite!(b, " {");

        for (_attrs, _wire, name, ty) in &s.members.args {
            fwrite!(b, "<br>&emsp;");
            fwrite!(b, name.as_str(), ": ");
            self.print_type_spec(b, &ty.inner)?;
            fwrite!(b, ",");
        }

        if s.members.args.is_empty() {
            fwrite!(b, "}");
        } else {
            fwrite!(b, "<br>}");
        }

        Ok(())
    }

    pub fn print_unit_head(&self, b: &mut Node<'_>, unit: &UnitHead) -> DResult<()> {
        self.print_visibility(b, &unit.visibility)?;

        if let Some(_) = unit.unsafe_token {
            fwrite!(b, "unsafe ");
        }
        if let Some(_) = unit.extern_token {
            fwrite!(b, "extern ");
        }

        let kind = match &unit.unit_kind.inner {
            spade_ast::UnitKind::Function => {
                fwrite!(b, "fn ");
                ItemKind::Function
            }
            spade_ast::UnitKind::Entity => {
                fwrite!(b, "entity ");
                ItemKind::Entity
            }
            spade_ast::UnitKind::Pipeline(len) => {
                fwrite!(b, "pipeline(");
                self.print_type_expr(b, len)?;
                fwrite!(b, ") ");
                ItemKind::Pipeline
            }
        };

        b.styled_tag("span", &[kind.color_class()], |b| {
            fwrite!(b, unit.name.as_str());
            Ok(())
        })?;
        if let Some(params) = &unit.type_params {
            fwrite!(b, "&lt;");
            separated(b, ", ", params.iter(), |b, p| {
                self.print_type_param(b, &p.inner)
            })?;
            fwrite!(b, "&gt;");
        }
        fwrite!(b, "(");
        self.print_parameter_list(b, &unit.inputs)?;
        fwrite!(b, ")");

        if let Some((_, out)) = &unit.output_type {
            fwrite!(b, " -&gt; ");
            self.print_type_spec(b, &out.inner)?;
        }

        if !unit.where_clauses.is_empty() {
            fwrite!(b, "<br>where");
            for clause in &unit.where_clauses {
                fwrite!(b, "<br>&emsp;");
                match clause {
                    spade_ast::WhereClause::GenericInt {
                        target, .. // TODO
                    } => {
                        self.print_path(b, target)?;
                        fwrite!(b, ": ");
                    }
                    spade_ast::WhereClause::TraitBounds { target, traits } => {
                        self.print_path(b, target)?;
                        fwrite!(b, ": ");
                        separated(b, " + ", traits.iter(), |b, t| self.print_trait_spec(b, t))?;
                    }
                }
                fwrite!(b, ",");
            }
        }

        Ok(())
    }

    pub(crate) fn print_visibility(
        &self,
        b: &mut Node<'_>,
        visibility: &Visibility,
    ) -> DResult<()> {
        match visibility {
            Visibility::Implicit => {}
            Visibility::Public => fwrite!(b, "pub "),
            Visibility::AtLib => fwrite!(b, "pub(lib) "),
            Visibility::AtSelf => fwrite!(b, "pub(self) "),
            Visibility::AtSuper => fwrite!(b, "pub(super) "),
            // Only used for enum variants, and there we don't print visibility as it's
            // not reproducable from ast either
            Visibility::AtSuperSuper => unreachable!(),
        }
        Ok(())
    }

    pub(crate) fn print_type_param(&self, b: &mut Node<'_>, inner: &TypeParam) -> DResult<()> {
        match inner {
            TypeParam::TypeName {
                name,
                traits,
                default,
            } => {
                fwrite!(b, name.as_str());
                if !traits.is_empty() {
                    fwrite!(b, ": ");
                    separated(b, " + ", traits.iter(), |b, t| self.print_trait_spec(b, t))?;
                }
                if let Some(default) = default {
                    fwrite!(b, " = ");
                    self.print_type_expr(b, default)?;
                }
            }
            TypeParam::TypeWithMeta {
                meta,
                name,
                default,
            } => {
                fwrite!(b, "#", meta.as_str(), " ", name.as_str());
                if let Some(default) = default {
                    fwrite!(b, " = ");
                    self.print_type_expr(b, default)?;
                }
            }
        }
        Ok(())
    }

    fn print_path(&self, b: &mut Node<'_>, path: &Path) -> DResult<()> {
        separated(b, "::", path.0.iter().enumerate(), |b, (i, seg)| {
            let p = &path.0[..(i + 1)];
            let lookup = self.symtab.lookup_id(&Path(p.to_vec()).nowhere(), true);

            let seg = seg.to_named_str().expect("Path to non-named path segment");

            match lookup {
                Ok(nid) => {
                    if let Some(kind) = ItemKind::from_name_id(&nid, &self.symtab) {
                        // This probably is only be possible when reexporting modules, which we don't print yet, but alas.
                        let is_module = matches!(kind, ItemKind::Module);
                        self.link_to(b, &nid.1.0, is_module, kind, |b| {
                            fwrite!(b, seg);
                            Ok(())
                        })?;
                    } else {
                        // Probably a generic or `Self`, only want to write it without a link
                        fwrite!(b, seg);
                    }
                }
                Err(_) => {
                    // Also generics, we currently only add them to symtab for impls and I haven't wrapped my head around
                    // reentering namespaces yet, so just write it without a link
                    fwrite!(b, seg);
                }
            }

            Ok(())
        })
    }

    pub(crate) fn print_type_spec(&self, b: &mut Node<'_>, spec: &TypeSpec) -> DResult<()> {
        match spec {
            TypeSpec::Tuple(exprs) => {
                fwrite!(b, "(");
                separated(b, ", ", exprs.iter(), |b, e| {
                    self.print_type_expr(b, &e.inner)
                })?;
                fwrite!(b, ")");
            }
            TypeSpec::Array { inner, size } => {
                fwrite!(b, "[");
                self.print_type_expr(b, &inner.inner)?;
                fwrite!(b, "; ");
                self.print_type_expr(b, &size.inner)?;
                fwrite!(b, "]");
            }
            TypeSpec::Named(path, args) => {
                self.print_path(b, path)?;
                if let Some(args) = args {
                    fwrite!(b, "&lt;");
                    separated(b, ", ", args.inner.iter(), |b, expr| {
                        self.print_type_expr(b, &expr.inner)
                    })?;
                    fwrite!(b, "&gt;");
                }
            }
            TypeSpec::Inverted(expr) => {
                fwrite!(b, "inv ");
                self.print_type_expr(b, &expr.inner)?;
            }
            TypeSpec::Impl(traits) => {
                fwrite!(b, "impl ");
                separated(b, " + ", traits.iter(), |b, spec| {
                    self.print_trait_spec(b, spec)
                })?;
            }
            TypeSpec::Wildcard => {
                fwrite!(b, "_");
            }
        }
        Ok(())
    }

    fn print_type_expr(&self, b: &mut Node<'_>, expr: &TypeExpression) -> DResult<()> {
        match expr {
            TypeExpression::TypeSpec(loc) => self.print_type_spec(b, &loc.inner),
            TypeExpression::Bool(_) => Ok(()),
            TypeExpression::Integer(big_int) => {
                write!(b.io(), "{}", big_int).map_err(|_| DocError::FWriteError)
            }
            TypeExpression::String(_) => Ok(()),
            TypeExpression::ConstGeneric(_) => Ok(()),
        }
    }

    pub(crate) fn print_trait_spec(&self, b: &mut Node<'_>, spec: &TraitSpec) -> DResult<()> {
        self.print_path(b, &spec.path)?;
        if let Some(args) = &spec.type_params {
            fwrite!(b, "&lt;");
            separated(b, ", ", args.inner.iter(), |b, expr| {
                self.print_type_expr(b, &expr.inner)
            })?;
            fwrite!(b, "&gt;");
        }
        Ok(())
    }

    fn print_parameter_list(&self, b: &mut Node<'_>, list: &ParameterList) -> DResult<()> {
        let mut started = false;
        if let Some(_) = list.self_ {
            fwrite!(b, "self");
            started = true;
        }
        for (_attrs, wire, name, ty) in &list.args {
            if started {
                fwrite!(b, ", ");
            }
            started = true;
            if wire.is_some() {
                fwrite!(b, "wire ");
            }
            fwrite!(b, name.as_str(), ": ");
            self.print_type_spec(b, &ty.inner)?;
        }
        Ok(())
    }
}

pub(crate) fn separated<I: Iterator>(
    b: &mut Node<'_>,
    sep: &'static str,
    mut iter: I,
    f: impl Fn(&mut Node<'_>, I::Item) -> DResult<()>,
) -> DResult<()> {
    if let Some(first) = iter.next() {
        f(b, first)?;
    } else {
        return Ok(());
    }

    for e in iter {
        fwrite!(b, sep);
        f(b, e)?;
    }
    Ok(())
}
