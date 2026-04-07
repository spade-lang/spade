use std::{
    fmt,
    fs::File,
    io::{self, BufWriter, Write},
};

use crate::error::{DResult, DocError};

#[macro_export]
macro_rules! fwrite {
    ($w:expr, $($e:expr),*) => {{
        $(
            $crate::html::FastWrite::write($e, $w)?;
        )*
    }}
}

pub trait FastWrite {
    fn write(&self, w: &mut impl fmt::Write) -> DResult<()>;
}

impl FastWrite for str {
    fn write(&self, w: &mut impl fmt::Write) -> DResult<()> {
        w.write_str(self).map_err(|_| DocError::FWriteError)
    }
}
impl<'a> FastWrite for &'a str {
    fn write(&self, w: &mut impl fmt::Write) -> DResult<()> {
        w.write_str(self).map_err(|_| DocError::FWriteError)
    }
}
impl FastWrite for String {
    fn write(&self, w: &mut impl fmt::Write) -> DResult<()> {
        w.write_str(self).map_err(|_| DocError::FWriteError)
    }
}

pub struct Node<'b> {
    buf: &'b mut BufWriter<File>,
}

impl<'b> Node<'b> {
    pub fn new(buf: &'b mut BufWriter<File>) -> Self {
        Self { buf }
    }

    pub fn tag(
        &mut self,
        tag: impl FastWrite,
        inner: impl FnOnce(&mut Node<'_>) -> DResult<()>,
    ) -> DResult<()> {
        fwrite!(self, "<", &tag, ">");

        inner(self)?;

        fwrite!(self, "</", &tag, ">");

        Ok(())
    }

    pub fn styled_tag(
        &mut self,
        tag: impl FastWrite,
        styles: &[&str],
        inner: impl FnOnce(&mut Node<'_>) -> DResult<()>,
    ) -> DResult<()> {
        fwrite!(self, "<", &tag, " class=\"");
        for s in styles {
            fwrite!(self, s, " ");
        }
        fwrite!(self, "\">");

        inner(self)?;

        fwrite!(self, "</", &tag, ">");

        Ok(())
    }

    pub fn io(&mut self) -> &mut impl io::Write {
        self.buf
    }
}

impl fmt::Write for Node<'_> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.buf
            .write_all(s.as_bytes())
            .map_err(|_| std::fmt::Error)?;
        Ok(())
    }
}
