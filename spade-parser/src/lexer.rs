use logos::Logos;

use num::BigUint;

#[derive(Debug, PartialEq, Clone)]
pub enum LiteralKind {
    Unsized,
    Signed(BigUint),
    Unsigned(BigUint),
}

fn parse_int(slice: &str, radix: u32) -> (BigUint, LiteralKind) {
    let lower = slice.to_ascii_lowercase().replace(['_'], "");

    let (cleaned, kind) = if lower.contains("u") {
        let split = lower.split("u").collect::<Vec<_>>();
        let kind = LiteralKind::Unsigned(BigUint::parse_bytes(split[1].as_bytes(), 10).unwrap());
        (split[0], kind)
    } else if lower.contains("i") {
        let split = lower.split("i").collect::<Vec<_>>();
        let kind = LiteralKind::Signed(BigUint::parse_bytes(split[1].as_bytes(), 10).unwrap());
        (split[0], kind)
    } else {
        (lower.as_str(), LiteralKind::Unsized)
    };

    (
        BigUint::parse_bytes(cleaned.as_bytes(), radix).unwrap(),
        kind,
    )
}

#[derive(Logos, Debug, PartialEq, Clone)]
pub enum TokenKind {
    // Unholy regex for unicode identifiers. Stolen from Repnop who stole it from Evrey
    #[regex(r#"(?x:
        [\p{XID_Start}_]
        \p{XID_Continue}*
        (\u{3F} | \u{21} | (\u{3F}\u{21}) | \u{2048})? # ? ! ?! ⁈
    )"#, |lex| lex.slice().to_string())]
    Identifier(String),

    #[regex(r"[0-9][0-9_]*([uUiI][0-9]+)?", |lex| {
        parse_int(lex.slice(), 10)
    })]
    Integer((BigUint, LiteralKind)),
    #[regex(r"0x[0-9A-Fa-f][0-9_A-Fa-f]*([uUiI][0-9]+)?", |lex| {
        parse_int(&lex.slice()[2..], 16)
    })]
    HexInteger((BigUint, LiteralKind)),
    #[regex(r"0b[0-1][0-1_]*([uUiI][0-9]+)?", |lex| {
        parse_int(&lex.slice()[2..], 2)
    })]
    BinInteger((BigUint, LiteralKind)),

    #[token("true")]
    True,
    #[token("false")]
    False,

    #[token("LOW")]
    Low,
    #[token("HIGH")]
    High,
    #[token("HIGHIMP")]
    HighImp,

    // Keywords
    #[token("reg")]
    Reg,
    #[token("let")]
    Let,
    #[token("decl")]
    Decl,
    #[token("inst")]
    Instance,
    #[token("reset")]
    Reset,
    #[token("initial")]
    Initial,
    #[token("if")]
    If,
    #[token("else")]
    Else,
    #[token("match")]
    Match,
    #[token("set")]
    Set,

    #[token("pipeline")]
    Pipeline,
    #[token("stage")]
    Stage,
    #[token("entity")]
    Entity,
    #[token("trait")]
    Trait,
    #[token("impl")]
    Impl,
    #[token("for")]
    For,
    #[token("fn")]
    Function,
    #[token("enum")]
    Enum,
    #[token("struct")]
    Struct,
    #[token("port")]
    Port,
    #[token("mod")]
    Mod,
    #[token("use")]
    Use,
    #[token("as")]
    As,
    #[token("assert")]
    Assert,
    #[token("mut")]
    Mut,
    #[token("inv")]
    Inv,
    #[token("where")]
    Where,

    #[token("gen")]
    Gen,

    #[token("extern")]
    Extern,

    // Math operators
    #[token("+")]
    Plus,
    #[token("-")]
    Minus,
    #[token("*")]
    Asterisk,
    #[token("/")]
    Slash,
    #[token("%")]
    Percentage,
    #[token("==")]
    Equals,
    #[token("!=")]
    NotEquals,
    #[token("<")]
    Lt,
    #[token(">")]
    Gt,
    #[token("<=")]
    Le,
    #[token(">=")]
    Ge,
    #[token(">>>")]
    ArithmeticRightShift,
    #[token(">>")]
    RightShift,
    #[token("<<")]
    LeftShift,
    #[token("||")]
    LogicalOr,
    #[token("&&")]
    LogicalAnd,
    #[token("^^")]
    LogicalXor,
    #[token("&")]
    Ampersand,
    #[token("|")]
    BitwiseOr,
    #[token("!")]
    Not,
    #[token("^")]
    BitwiseXor,
    #[token("~")]
    Tilde,
    #[token("`")]
    InfixOperatorSeparator,
    #[token("'")]
    SingleQuote,

    // Other operators
    #[token("=")]
    Assignment,

    #[token("(")]
    OpenParen,
    #[token(")")]
    CloseParen,

    #[token("{")]
    OpenBrace,
    #[token("}")]
    CloseBrace,

    #[token("[")]
    OpenBracket,
    #[token("]")]
    CloseBracket,

    #[token("=>")]
    FatArrow,
    #[token("->")]
    SlimArrow,
    #[token(",")]
    Comma,
    #[token(".")]
    Dot,
    #[token("..")]
    DotDot,
    #[token(";")]
    Semi,
    #[token(";")]
    GreekQuestionMark,
    #[token(":")]
    Colon,
    #[token("::")]
    PathSeparator,
    #[token("#")]
    Hash,
    #[token("$")]
    Dollar,

    #[regex("///[^\n]*", |lex| lex.slice()[3..].to_string())]
    OutsideDocumentation(String),
    #[regex("//![^\n]*", |lex| lex.slice()[3..].to_string())]
    InsideDocumentation(String),

    /// Ignoring whitespace
    #[regex("[ \t\n\r]", logos::skip)]
    Whitespace,

    #[regex("//[^\n]*", logos::skip)]
    Comment,

    #[token("/*")]
    BlockCommentStart,
    #[token("*/")]
    BlockCommentEnd,

    Eof,
}

impl TokenKind {
    pub fn as_str(&self) -> &'static str {
        match self {
            TokenKind::Identifier(_) => "identifier",
            TokenKind::Integer(_) => "integer",
            TokenKind::HexInteger(_) => "hexadecimal integer",
            TokenKind::BinInteger(_) => "binary integer",
            TokenKind::True => "true",
            TokenKind::False => "false",
            TokenKind::Low => "LOW",
            TokenKind::High => "HIGH",
            TokenKind::HighImp => "HIGHIMP",

            TokenKind::Let => "let",
            TokenKind::Reg => "reg",
            TokenKind::Decl => "decl",
            TokenKind::Entity => "entity",
            TokenKind::Pipeline => "pipeline",
            TokenKind::Stage => "stage",
            TokenKind::Instance => "inst",
            TokenKind::Reset => "reset",
            TokenKind::Initial => "initial",
            TokenKind::If => "if",
            TokenKind::Else => "else",
            TokenKind::Match => "match",
            TokenKind::Impl => "impl",
            TokenKind::Trait => "trait",
            TokenKind::For => "for",
            TokenKind::Function => "fn",
            TokenKind::Enum => "enum",
            TokenKind::Struct => "struct",
            TokenKind::Port => "port",
            TokenKind::Mod => "mod",
            TokenKind::As => "as",
            TokenKind::Use => "use",
            TokenKind::Assert => "assert",
            TokenKind::Set => "set",
            TokenKind::Mut => "mut",
            TokenKind::Inv => "inv",
            TokenKind::Where => "where",

            TokenKind::Gen => "gen",

            TokenKind::Extern => "extern",

            TokenKind::Assignment => "=",
            TokenKind::Plus => "+",
            TokenKind::Minus => "-",
            TokenKind::Asterisk => "*",
            TokenKind::Slash => "/",
            TokenKind::Percentage => "%",
            TokenKind::Equals => "==",
            TokenKind::NotEquals => "!=",
            TokenKind::Lt => "<",
            TokenKind::Gt => ">",
            TokenKind::Le => "<=",
            TokenKind::Ge => ">=",
            TokenKind::LeftShift => "<<",
            TokenKind::RightShift => ">>",
            TokenKind::ArithmeticRightShift => ">>>",
            TokenKind::LogicalOr => "||",
            TokenKind::LogicalAnd => "&&",
            TokenKind::LogicalXor => "^^",
            TokenKind::Ampersand => "&",
            TokenKind::BitwiseOr => "|",
            TokenKind::Not => "!",
            TokenKind::Tilde => "~",
            TokenKind::BitwiseXor => "^",
            TokenKind::InfixOperatorSeparator => "`",

            TokenKind::OpenParen => "(",
            TokenKind::CloseParen => ")",
            TokenKind::OpenBrace => "{",
            TokenKind::CloseBrace => "}",
            TokenKind::OpenBracket => "[",
            TokenKind::CloseBracket => "]",

            TokenKind::FatArrow => "=>",
            TokenKind::SlimArrow => "->",
            TokenKind::Semi => ";",
            TokenKind::GreekQuestionMark => "GreekQuestionMark(;)",
            TokenKind::Colon => ":",
            TokenKind::Comma => ",",
            TokenKind::Dot => ".",
            TokenKind::DotDot => "..",
            TokenKind::PathSeparator => "::",
            TokenKind::SingleQuote => "'",

            TokenKind::Hash => "#",
            TokenKind::Dollar => "$",

            TokenKind::Eof => "end of file",

            TokenKind::OutsideDocumentation(_) => "///",
            TokenKind::InsideDocumentation(_) => "//!",

            TokenKind::Whitespace => "whitespace",
            TokenKind::Comment => "comment",

            TokenKind::BlockCommentStart => "/*",
            TokenKind::BlockCommentEnd => "*/",
        }
    }

    pub fn is_identifier(&self) -> bool {
        matches!(self, TokenKind::Identifier(_))
    }
    pub fn is_integer(&self) -> bool {
        matches!(
            self,
            TokenKind::Integer(_) | TokenKind::HexInteger(_) | TokenKind::BinInteger(_)
        )
    }

    pub fn as_biguint(&self) -> Option<BigUint> {
        match self {
            TokenKind::Integer((i, _))
            | TokenKind::HexInteger((i, _))
            | TokenKind::BinInteger((i, _)) => Some(i.clone()),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use spade_common::num_ext::InfallibleToBigUint;

    use super::*;

    #[test]
    fn identifiers_work() {
        let mut lex = TokenKind::lexer("abc123_");

        assert_eq!(
            lex.next(),
            Some(Ok(TokenKind::Identifier("abc123_".to_string())))
        );
    }

    #[test]
    fn integer_literals_work() {
        let mut lex = TokenKind::lexer("123");

        assert_eq!(
            lex.next(),
            Some(Ok(TokenKind::Integer((
                123_u32.to_biguint(),
                LiteralKind::Unsized
            ))))
        );
        assert_eq!(lex.next(), None);
    }

    #[test]
    fn sized_uint_integer_literals_work() {
        let mut lex = TokenKind::lexer("123u3");

        assert_eq!(
            lex.next(),
            Some(Ok(TokenKind::Integer((
                123_u32.to_biguint(),
                LiteralKind::Unsigned(3u32.to_biguint())
            ))))
        );
        assert_eq!(lex.next(), None);
    }

    #[test]
    fn sized_int_integer_literals_work() {
        let mut lex = TokenKind::lexer("123i3");

        assert_eq!(
            lex.next(),
            Some(Ok(TokenKind::Integer((
                123_u32.to_biguint(),
                LiteralKind::Signed(3u32.to_biguint())
            ))))
        );
        assert_eq!(lex.next(), None);
    }

    #[test]
    fn hex_array() {
        let mut lex = TokenKind::lexer("[0x45]");
        assert_eq!(lex.next(), Some(Ok(TokenKind::OpenBracket)));
        assert_eq!(
            lex.next(),
            Some(Ok(TokenKind::HexInteger((
                0x45_u32.to_biguint(),
                LiteralKind::Unsized
            ))))
        );
        assert_eq!(lex.next(), Some(Ok(TokenKind::CloseBracket)));
        assert_eq!(lex.next(), None);
    }

    #[test]
    fn invalid_hex_is_not_hex() {
        let mut lex = TokenKind::lexer("0xg");
        assert_eq!(
            lex.next(),
            Some(Ok(TokenKind::Integer((
                0_u32.to_biguint(),
                LiteralKind::Unsized
            ))))
        );
        assert_eq!(
            lex.next(),
            Some(Ok(TokenKind::Identifier("xg".to_string())))
        );
        assert_eq!(lex.next(), None);
    }

    #[test]
    fn doc_comments_slice_correctly() {
        let mut lex = TokenKind::lexer("//! Hello\n///G'day");
        assert_eq!(
            lex.next(),
            Some(Ok(TokenKind::InsideDocumentation(" Hello".to_string())))
        );
        assert_eq!(
            lex.next(),
            Some(Ok(TokenKind::OutsideDocumentation("G'day".to_string())))
        );
        assert_eq!(lex.next(), None);
    }
}
