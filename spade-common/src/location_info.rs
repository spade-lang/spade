use std::ops::Range;

use codespan::Span;
use serde::{Deserialize, Serialize};

use crate::error_reporting::AsLabel;

pub trait HasCodespan {
    fn codespan(&self) -> Span;
}
impl<T> HasCodespan for Loc<T> {
    fn codespan(&self) -> Span {
        self.span
    }
}
impl HasCodespan for Span {
    fn codespan(&self) -> Span {
        self.clone()
    }
}
impl HasCodespan for std::ops::Range<usize> {
    fn codespan(&self) -> Span {
        lspan(self.clone())
    }
}

pub trait WithLocation: Sized {
    fn at(self, file_id: usize, span: &impl HasCodespan) -> Loc<Self>
    where
        Self: Sized,
    {
        Loc::new(self, span.codespan(), file_id)
    }

    /// Creates a new Loc from another Loc
    fn at_loc<T: Sized>(self, loc: &Loc<T>) -> Loc<Self> {
        Loc::new(self, loc.span, loc.file_id)
    }

    fn between(
        self,
        file_id: usize,
        start: &impl HasCodespan,
        end: &impl HasCodespan,
    ) -> Loc<Self> {
        Loc::new(self, start.codespan().merge(end.codespan()), file_id)
    }

    fn between_locs<T, Y>(self, start: &Loc<T>, end: &Loc<Y>) -> Loc<Self> {
        assert!(start.file_id == end.file_id);
        Loc::new(self, start.codespan().merge(end.codespan()), end.file_id())
    }

    fn nowhere(self) -> Loc<Self>
    where
        Self: Sized,
    {
        self.at(0, &Span::new(0, 0))
    }
}

impl WithLocation for () {}
impl WithLocation for u128 {}
impl WithLocation for u64 {}
impl WithLocation for i64 {}
impl WithLocation for usize {}
impl WithLocation for bool {}
impl<T> WithLocation for Vec<T> {}

pub fn lspan(s: logos::Span) -> Span {
    Span::new(s.start as u32, s.end as u32)
}

#[cfg(test)]
pub fn dummy() -> Span {
    Span::new(0, 0)
}

#[derive(Clone, Copy, Serialize, Deserialize)]
pub struct Loc<T> {
    pub inner: T,
    #[serde(skip)]
    pub span: Span,
    #[serde(skip)]
    pub file_id: usize,
}

impl<T> Loc<T> {
    pub fn new(inner: T, span: Span, file_id: usize) -> Self {
        Self {
            inner,
            span,
            file_id,
        }
    }
    pub fn nowhere(inner: T) -> Self {
        Self::new(inner, Span::new(0, 0), 0)
    }

    pub fn strip(self) -> T {
        self.inner
    }

    pub fn strip_ref(&self) -> &T {
        &self.inner
    }

    pub fn separate(self) -> (Self, Span) {
        let span = self.span;
        (self, span)
    }

    pub fn separate_loc(self) -> (Self, Loc<()>) {
        let loc = self.loc();
        (self, loc)
    }

    pub fn split(self) -> (T, Span) {
        (self.inner, self.span)
    }
    pub fn split_ref(&self) -> (&T, Span) {
        (&self.inner, self.span)
    }
    pub fn split_loc(self) -> (T, Loc<()>) {
        let loc = self.loc();
        (self.inner, loc)
    }
    pub fn split_loc_ref(&self) -> (&T, Loc<()>) {
        let loc = self.loc();
        (&self.inner, loc)
    }

    pub fn map<Y>(self, mut op: impl FnMut(T) -> Y) -> Loc<Y> {
        Loc {
            inner: op(self.inner),
            span: self.span,
            file_id: self.file_id,
        }
    }
    pub fn map_ref<Y>(&self, mut op: impl FnMut(&T) -> Y) -> Loc<Y> {
        Loc {
            inner: op(&self.inner),
            span: self.span,
            file_id: self.file_id,
        }
    }
    pub fn try_map_ref<Y, E, F>(&self, mut op: F) -> Result<Loc<Y>, E>
    where
        F: FnMut(&T) -> Result<Y, E>,
    {
        Ok(Loc {
            inner: op(&self.inner)?,
            span: self.span,
            file_id: self.file_id,
        })
    }

    pub fn loc(&self) -> Loc<()> {
        Loc {
            inner: (),
            span: self.span,
            file_id: self.file_id,
        }
    }
}

impl<T> Into<Range<usize>> for Loc<T> {
    fn into(self) -> Range<usize> {
        self.span.into()
    }
}

impl<T, E> Loc<Result<T, E>> {
    pub fn map_err<E2>(self, err_fn: impl Fn(E, Loc<()>) -> E2) -> Result<Loc<T>, E2> {
        match self.inner {
            Ok(inner) => Ok(Loc {
                inner,
                span: self.span,
                file_id: self.file_id,
            }),
            Err(e) => Err(err_fn(e, ().at(self.file_id, &self.span))),
        }
    }
}

impl<T> PartialEq for Loc<T>
where
    T: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.inner == other.inner
    }
}

impl<T> Eq for Loc<T> where T: Eq {}

impl<T> std::fmt::Display for Loc<T>
where
    T: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.inner)
    }
}

impl<T> std::hash::Hash for Loc<T>
where
    T: std::hash::Hash,
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.inner.hash(state)
    }
}

impl<T> std::fmt::Debug for Loc<T>
where
    T: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "l({:3}..{:3})[{:?}]",
            self.span.start(),
            self.span.end(),
            self.inner
        )
    }
}

impl<T> std::ops::Add<T> for Loc<T>
where
    T: std::ops::Add,
    T::Output: WithLocation,
{
    type Output = Loc<T::Output>;

    fn add(self, other: T) -> Self::Output {
        let loc = self.loc();
        (self.strip() + other).at_loc(&loc)
    }
}

impl<T> std::ops::Deref for Loc<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}
impl<T> std::ops::DerefMut for Loc<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}

impl<T> AsLabel for Loc<T> {
    fn file_id(&self) -> usize {
        self.file_id
    }

    fn span(&self) -> std::ops::Range<usize> {
        self.span.into()
    }
}
