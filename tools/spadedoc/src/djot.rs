use std::borrow::Cow;

use jotdown::{Attributes, Container, Event, Parser, Render as _, html::Renderer};
use logos::Logos as _;
use spade::lexer::TokenKind;

use crate::{error::DResult, html::Node};

pub struct DjotContent {
    html_output: String,
}

impl DjotContent {
    pub fn write(self) -> impl FnOnce(&mut Node<'_>) -> DResult<()> {
        move |n| {
            ammonia::Builder::new()
                .add_allowed_classes("span", SyntaxColor::CLASSES)
                .clean(&self.html_output)
                .write_to(n.io())
                .unwrap();
            Ok(())
        }
    }
}

pub fn write_djot<'n>(markdown: &str, f: impl FnOnce(DjotContent) -> DResult<()>) -> DResult<()> {
    let parser = Parser::new(markdown);

    let mut html_output = String::new();
    let renderer = Renderer::minified();
    renderer
        .push(
            SyntaxProcessor {
                inner: parser,
                state: State::Await,
            },
            &mut html_output,
        )
        .expect("Error emitting djot");

    if !html_output.is_empty() {
        f(DjotContent { html_output })?;
    }

    Ok(())
}

#[derive(Clone, Copy)]
enum State {
    /// Wait for a codeblock with spade as language
    Await,
    /// Emit raw start tag
    Start,
    /// Emit raw html stuff
    Color,
    /// Emit raw end tag
    End,
}
struct SyntaxProcessor<'s, I: Iterator<Item = Event<'s>>> {
    inner: I,
    state: State,
}

impl<'s, I: Iterator<Item = Event<'s>>> Iterator for SyntaxProcessor<'s, I> {
    type Item = Event<'s>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.state {
            State::Await => {
                let next = self.inner.next();
                match &next {
                    Some(Event::Start(Container::CodeBlock { language }, _))
                        if language.split(",").next() == Some("spade") =>
                    {
                        self.state = State::Start;
                    }
                    _ => {}
                }
                next
            }
            State::Start => {
                self.state = State::Color;
                Some(Event::Start(
                    Container::RawBlock {
                        format: Cow::Borrowed("html"),
                    },
                    Attributes::default(),
                ))
            }
            State::Color => {
                let mut source = String::new();
                loop {
                    match self.inner.next() {
                        None => break,
                        Some(Event::End(Container::CodeBlock { .. })) => break,
                        Some(Event::Str(s)) => {
                            source.push_str(&s);
                        }
                        _ => {}
                    }
                }

                let mut highlighted = String::new();
                let mut lexer = TokenKind::lexer(&source);
                let mut current = (0, SyntaxColor::None);

                while let Some(tok) = lexer.next() {
                    let tok = tok.unwrap();
                    // Update color
                    let color = SyntaxColor::for_token(&tok);
                    if color != current.1 {
                        if current.1 != SyntaxColor::None {
                            highlighted.push_str("</span>");
                        }
                        if color != SyntaxColor::None {
                            highlighted.extend(["<span class=\"", color.class(), "\">"]);
                        }
                        current.1 = color;
                    }

                    let until = lexer.span().end;
                    let to_write = &source[current.0..until];
                    write_escape(to_write, &mut highlighted);
                    current.0 = until;
                }
                if current.1 != SyntaxColor::None {
                    highlighted.push_str("</span>");
                }

                self.state = State::End;
                Some(Event::Str(Cow::Owned(highlighted)))
            }
            State::End => {
                self.state = State::Await;
                Some(Event::End(Container::RawBlock {
                    format: Cow::Borrowed("html"),
                }))
            }
        }
    }
}

// Stolen from jotdown html.rs and modified
fn write_escape(mut s: &str, out: &mut String) {
    let mut ent = "";
    while let Some(i) = s.find(|c| {
        match c {
            '<' => Some("&lt;"),
            '>' => Some("&gt;"),
            '&' => Some("&amp;"),
            '"' => Some("&quot;"),
            _ => None,
        }
        .map_or(false, |s| {
            ent = s;
            true
        })
    }) {
        out.push_str(&s[..i]);
        out.push_str(ent);
        s = &s[i + 1..];
    }
    out.push_str(s)
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum SyntaxColor {
    None,
    Comment,
    Number,
    String,
    Bool,
    Keyword,
}

impl SyntaxColor {
    /// Classes to be allowed on spans for ammonia
    const CLASSES: &[&'static str] = &[
        "lex-comment",
        "lex-number",
        "lex-string",
        "lex-bool",
        "lex-kw",
    ];

    fn class(&self) -> &'static str {
        match self {
            SyntaxColor::None => "",
            SyntaxColor::Comment => "lex-comment",
            SyntaxColor::Number => "lex-number",
            SyntaxColor::String => "lex-string",
            SyntaxColor::Bool => "lex-bool",
            SyntaxColor::Keyword => "lex-kw",
        }
    }

    fn for_token(token: &TokenKind) -> Self {
        match token {
            TokenKind::Identifier(_) => SyntaxColor::None,
            TokenKind::Integer(_) => SyntaxColor::Number,
            TokenKind::HexInteger(_) => SyntaxColor::Number,
            TokenKind::BinInteger(_) => SyntaxColor::Number,
            TokenKind::True
            | TokenKind::False
            | TokenKind::Low
            | TokenKind::High
            | TokenKind::HighImp => SyntaxColor::Bool,
            TokenKind::Reg => SyntaxColor::Keyword,
            TokenKind::Let => SyntaxColor::Keyword,
            TokenKind::Decl => SyntaxColor::Keyword,
            TokenKind::Instance => SyntaxColor::Keyword,
            // TokenKind::Reset => todo!(),
            // TokenKind::Initial => todo!(),
            TokenKind::If => SyntaxColor::Keyword,
            TokenKind::Else => SyntaxColor::Keyword,
            TokenKind::Match => SyntaxColor::Keyword,
            TokenKind::Set => SyntaxColor::Keyword,
            TokenKind::Pipeline => SyntaxColor::Keyword,
            // TokenKind::Stage => todo!(),
            TokenKind::Entity => SyntaxColor::Keyword,
            TokenKind::Trait => SyntaxColor::Keyword,
            TokenKind::Impl => SyntaxColor::Keyword,
            TokenKind::For => SyntaxColor::Keyword,
            TokenKind::Function => SyntaxColor::Keyword,
            TokenKind::Enum => SyntaxColor::Keyword,
            TokenKind::Struct => SyntaxColor::Keyword,
            TokenKind::Port => SyntaxColor::Keyword,
            TokenKind::Wire => SyntaxColor::Keyword,
            TokenKind::Mod => SyntaxColor::Keyword,
            TokenKind::Type => SyntaxColor::Keyword,
            TokenKind::Use => SyntaxColor::Keyword,
            TokenKind::As => SyntaxColor::Keyword,
            TokenKind::Assert => SyntaxColor::Keyword,
            TokenKind::Mut => SyntaxColor::Keyword,
            TokenKind::Inv => SyntaxColor::Keyword,
            TokenKind::Pub => SyntaxColor::Keyword,
            TokenKind::Where => SyntaxColor::Keyword,
            TokenKind::Gen => SyntaxColor::Keyword,
            TokenKind::Extern => SyntaxColor::Keyword,
            TokenKind::Unsafe => SyntaxColor::Keyword,
            // TokenKind::Plus => todo!(),
            // TokenKind::Minus => todo!(),
            // TokenKind::Asterisk => todo!(),
            // TokenKind::Slash => todo!(),
            // TokenKind::Percentage => todo!(),
            // TokenKind::Equals => todo!(),
            // TokenKind::NotEquals => todo!(),
            // TokenKind::Lt => todo!(),
            // TokenKind::Gt => todo!(),
            // TokenKind::Le => todo!(),
            // TokenKind::Ge => todo!(),
            // TokenKind::ArithmeticRightShift => todo!(),
            // TokenKind::RightShift => todo!(),
            // TokenKind::LeftShift => todo!(),
            // TokenKind::PlusDot => todo!(),
            // TokenKind::MinusDot => todo!(),
            // TokenKind::AsteriskDot => todo!(),
            // TokenKind::RightShiftDot => todo!(),
            // TokenKind::LeftShiftDot => todo!(),
            // TokenKind::DoublePipe => todo!(),
            // TokenKind::LogicalAnd => todo!(),
            // TokenKind::LogicalXor => todo!(),
            // TokenKind::Ampersand => todo!(),
            // TokenKind::Pipe => todo!(),
            // TokenKind::Not => todo!(),
            // TokenKind::BitwiseXor => todo!(),
            // TokenKind::Tilde => todo!(),
            // TokenKind::InfixOperatorSeparator => todo!(),
            // TokenKind::Assignment => todo!(),
            // TokenKind::OpenParen => todo!(),
            // TokenKind::CloseParen => todo!(),
            // TokenKind::OpenBrace => todo!(),
            // TokenKind::CloseBrace => todo!(),
            // TokenKind::OpenBracket => todo!(),
            // TokenKind::CloseBracket => todo!(),
            // TokenKind::FatArrow => todo!(),
            // TokenKind::SlimArrow => todo!(),
            // TokenKind::At => todo!(),
            // TokenKind::Comma => todo!(),
            // TokenKind::Dot => todo!(),
            // TokenKind::DotDot => todo!(),
            // TokenKind::Semi => todo!(),
            // TokenKind::GreekQuestionMark => todo!(),
            // TokenKind::Colon => todo!(),
            // TokenKind::PathSeparator => todo!(),
            // TokenKind::Hash => todo!(),
            // TokenKind::Dollar => todo!(),
            // TokenKind::Label(identifier) => todo!(),
            // TokenKind::LabelRef(identifier) => todo!(),
            TokenKind::AsciiCharLiteral(_) => SyntaxColor::String,
            TokenKind::AsciiStringLiteral(_) => SyntaxColor::String,
            TokenKind::Utf8CharLiteral => SyntaxColor::String,
            TokenKind::String(_) => SyntaxColor::String,
            TokenKind::OutsideDocumentation(_) => SyntaxColor::Comment,
            TokenKind::InsideDocumentation(_) => SyntaxColor::Comment,
            TokenKind::Whitespace => SyntaxColor::None,
            TokenKind::Comment => SyntaxColor::Comment,
            TokenKind::BlockCommentStart => SyntaxColor::Comment,
            TokenKind::BlockCommentEnd => SyntaxColor::Comment,
            TokenKind::Eof => SyntaxColor::None,
            _ => SyntaxColor::None,
        }
    }
}
