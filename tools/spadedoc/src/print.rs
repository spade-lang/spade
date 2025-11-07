use crate::{
    errors::{DResult, DocError},
    fwrite,
    generate::{Generator, ItemKind},
    html::Node,
};
use spade_ast::{ParameterList, TraitSpec, TypeExpression, TypeParam, TypeSpec, UnitHead};
use spade_common::{location_info::WithLocation, name::Path};
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

    pub fn print_unithead(&self, b: &mut Node<'_>, unit: &UnitHead) -> DResult<()> {
        if let Some(_) = unit.unsafe_token {
            fwrite!(b, "unsafe ");
        }
        if let Some(_) = unit.extern_token {
            fwrite!(b, "extern ");
        }

        match &unit.unit_kind.inner {
            spade_ast::UnitKind::Function => fwrite!(b, "fn "),
            spade_ast::UnitKind::Entity => fwrite!(b, "entity "),
            spade_ast::UnitKind::Pipeline(len) => {
                fwrite!(b, "pipeline(");
                self.print_type_expr(b, len)?;
                fwrite!(b, ") ");
            }
        }

        fwrite!(b, unit.name.as_str());
        if let Some(params) = &unit.type_params {
            println!("{:?}", params);
            fwrite!(b, "&lt;");
            seperated(b, ", ", params.iter(), |b, p| {
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
                        seperated(b, " + ", traits.iter(), |b, t| self.print_trait_spec(b, t))?;
                    }
                }
                fwrite!(b, ",");
            }
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
                    seperated(b, " + ", traits.iter(), |b, t| self.print_trait_spec(b, t))?;
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
        seperated(b, "::", path.0.iter().enumerate(), |b, (i, seg)| {
            let p = &path.0[..(i + 1)];
            let lookup = self.symtab.lookup_id(&Path(p.to_vec()).nowhere(), true);

            let seg = seg.to_named_str().expect("Path to non-named path segment");

            match lookup {
                Ok(nid) => {
                    let kind = ItemKind::from_id(&nid, &self.symtab);
                    self.link_to(
                        b,
                        &nid.1.0,
                        kind,
                        false, /* TODO */
                        false, /* TODO */
                        |b| {
                            fwrite!(b, seg);
                            Ok(())
                        },
                    )?;
                }
                Err(_) => {
                    // Probably generics or primitives
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
                seperated(b, ", ", exprs.iter(), |b, e| {
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
                    seperated(b, ", ", args.inner.iter(), |b, expr| {
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
                seperated(b, " + ", traits.iter(), |b, spec| {
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
            seperated(b, ", ", args.inner.iter(), |b, expr| {
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

pub(crate) fn seperated<I: Iterator>(
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
