use serde::{Deserialize, Serialize};
use spade_codespan::{ByteOffset, Span};
use spade_codespan_reporting::diagnostic::Label;

pub trait AsLabel {
    fn file_id(&self) -> usize;
    fn span(&self) -> std::ops::Range<usize>;

    fn primary_label(&self) -> Label<usize> {
        Label::primary(self.file_id(), self.span())
    }

    fn secondary_label(&self) -> Label<usize> {
        Label::secondary(self.file_id(), self.span())
    }
}

pub type FullSpan = (Span, usize);

impl<T> From<&Loc<T>> for FullSpan {
    fn from(loc: &Loc<T>) -> Self {
        (loc.span, loc.file_id)
    }
}

impl<T> From<Loc<T>> for FullSpan {
    fn from(loc: Loc<T>) -> Self {
        FullSpan::from(&loc)
    }
}

impl AsLabel for FullSpan {
    fn span(&self) -> std::ops::Range<usize> {
        self.0.into()
    }

    fn file_id(&self) -> usize {
        self.1
    }
}

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
        *self
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

impl<T> WithLocation for T {}

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
    pub span: Span,
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

    pub fn is_same_loc<R>(&self, other: &Loc<R>) -> bool {
        self.span == other.span && self.file_id == other.file_id
    }

    pub fn map<Y>(self, mut op: impl FnMut(T) -> Y) -> Loc<Y> {
        Loc {
            inner: op(self.inner),
            span: self.span,
            file_id: self.file_id,
        }
    }

    pub fn try_map<Y, E>(self, mut op: impl FnMut(T) -> Result<Y, E>) -> Result<Loc<Y>, E> {
        Ok(Loc {
            inner: op(self.inner)?,
            span: self.span,
            file_id: self.file_id,
        })
    }

    pub fn map_ref<Y>(&self, mut op: impl FnMut(&T) -> Y) -> Loc<Y> {
        Loc {
            inner: op(&self.inner),
            span: self.span,
            file_id: self.file_id,
        }
    }

    pub fn try_map_ref<Y, E>(&self, mut op: impl FnMut(&T) -> Result<Y, E>) -> Result<Loc<Y>, E> {
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

    pub fn contains_start<R>(&self, other: &Loc<R>) -> bool {
        other.file_id == self.file_id
            && other.span.start() >= self.span.start()
            && other.span.start() < self.span.end()
    }

    pub fn start_span(&self) -> Loc<()> {
        ().at(
            self.file_id,
            &Span::new(self.span.start(), self.span.start()),
        )
    }
    pub fn end_span(&self) -> Loc<()> {
        ().at(self.file_id, &Span::new(self.span.end(), self.span.end()))
    }

    /// Shrinks a Loc on the left size by the width of the specified string.
    /// For example (( abc ))
    ///             ^^^^^^^^^ .shrink_left("((")
    /// results in
    /// For example (( abc ))
    ///               ^^^^^^^
    ///
    /// Note that this is only valid if the loc actually points to the specified string,
    /// otherwise the behaviour is undefined
    ///
    /// If the span is empty, does nothing
    pub fn shrink_left(&self, s: &str) -> Loc<()> {
        if self.span.start() == self.span.end() {
            self.loc()
        } else {
            Loc {
                inner: (),
                span: Span::new(
                    self.span.start() + ByteOffset::from_str_len(s),
                    self.span.end(),
                ),
                file_id: self.file_id,
            }
        }
    }

    /// See [shrink_right]
    pub fn shrink_right(&self, s: &str) -> Loc<()> {
        if self.span.start() == self.span.end() {
            self.loc()
        } else {
            Loc {
                inner: (),
                span: Span::new(
                    self.span.start(),
                    self.span.end() - ByteOffset::from_str_len(s),
                ),
                file_id: self.file_id,
            }
        }
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

impl<T> Loc<Option<T>>
where
    T: WithLocation,
{
    pub fn transpose(self) -> Option<Loc<T>> {
        let loc = self.loc();
        match self.inner {
            Some(inner) => Some(inner.at_loc(&loc)),
            None => None,
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

impl<T> PartialOrd for Loc<T>
where
    T: PartialOrd,
{
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.inner.partial_cmp(&other.inner)
    }
}

impl<T> Ord for Loc<T>
where
    T: Ord,
{
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.inner.cmp(&other.inner)
    }
}

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
        self.inner.fmt(f)
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
