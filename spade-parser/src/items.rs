use spade_ast::{
    AttributeList, Enum, Expression, ExternalMod, ImplBlock, Item, Module, Struct, TraitDef,
    TraitSpec, TypeDeclKind, TypeDeclaration, TypeSpec, Unit, UseStatement,
};
use spade_common::location_info::{AsLabel, Loc, WithLocation};
use spade_common::name::Visibility;
use spade_diagnostics::Diagnostic;

use crate::error::UnexpectedToken;
use crate::{
    error::CSErrorTransformations, lexer::TokenKind, KeywordPeekingParser, Parser, Result,
};

pub(crate) struct UnitParser {}

impl KeywordPeekingParser<Loc<Unit>> for UnitParser {
    fn is_leading_token(&self) -> fn(&TokenKind) -> bool {
        |kind| {
            vec![
                TokenKind::Function,
                TokenKind::Entity,
                TokenKind::Pipeline,
                TokenKind::Extern,
                TokenKind::Unsafe,
            ]
            .contains(kind)
        }
    }

    fn parse(
        &self,
        parser: &mut Parser,
        attributes: &AttributeList,
        visibility: &Loc<Visibility>,
    ) -> Result<Loc<Unit>> {
        let head = if let Some(head) = parser.unit_head(attributes, visibility)? {
            head
        } else {
            return Err(Diagnostic::bug(
                parser.peek()?,
                "UnitParser matched leading_tokens but parser returned None",
            ));
        };

        parser.set_item_context(head.unit_kind.clone())?;

        let allow_stages = head.unit_kind.is_pipeline();
        let after_head_token = parser.peek()?; // will be ; if it's extern
        let block_result = (|| {
            if let Some(block) = parser.block(allow_stages)? {
                let (block, block_span) = block.separate();
                Ok((Some(block), block_span))
            } else if parser.peek_kind(&TokenKind::Semi)? {
                let tok = parser.eat_unconditional()?;

                Ok((None, ().at(parser.file_id, &tok.span).span))
            } else {
                let next = parser.peek()?;
                Err(Diagnostic::error(
                    next.clone(),
                    format!("Unexpected `{}`, expected body or `;`", next.kind.as_str(),),
                )
                .primary_label(format!("Unexpected {}", &next.kind.as_str()))
                .secondary_label(&head, format!("Expected body for this {}", head.unit_kind)))
            }
        })();

        let (block, block_span) = match block_result {
            Ok(inner) => inner,
            Err(e) => {
                parser.clear_item_context();
                return Err(e);
            }
        };

        if head.extern_token.is_some() && block.is_some() {
            return Err(Diagnostic::error(
                head.extern_token.unwrap(),
                "`extern` units cannot have a body",
            )
            .span_suggest_remove("Remove this body", block.as_ref().unwrap()));
        } else if head.extern_token.is_none() & block.is_none() {
            return Err(Diagnostic::error(
                &head,
                format!("This {} is missing a body", head.unit_kind),
            )
            .span_suggest_replace(
                format!("Did you forget to add the {}'s body?", head.unit_kind),
                after_head_token,
                " {}",
            )
            .span_suggest_insert_before(
                format!("Or did you mean to declare an `extern` {}?", head.unit_kind),
                &head.unit_kind,
                "extern ",
            ));
        }

        parser.clear_item_context();

        Ok(Unit {
            head: head.inner.clone(),
            body: block.map(|inner| inner.map(|inner| Expression::Block(Box::new(inner)))),
        }
        .between(parser.file_id, &head, &block_span))
    }
}

pub(crate) struct TraitDefParser {}

impl KeywordPeekingParser<Loc<TraitDef>> for TraitDefParser {
    fn is_leading_token(&self) -> fn(&TokenKind) -> bool {
        |kind| kind == &TokenKind::Trait
    }

    fn parse(
        &self,
        parser: &mut Parser,
        attributes: &AttributeList,
        visibility: &Loc<Visibility>,
    ) -> Result<Loc<TraitDef>> {
        let start_token = parser.eat_unconditional()?;

        let name = parser.identifier()?;

        let type_params = parser.generics_list()?;

        let where_clauses = parser.where_clauses()?;

        let mut result = TraitDef {
            visibility: visibility.clone(),
            name,
            type_params,
            where_clauses,
            attributes: attributes.clone(),
            methods: vec![],
        };

        parser.eat(&TokenKind::OpenBrace)?;

        loop {
            let vis = Visibility::Implicit.nowhere();

            let Some(mut decl) = parser.unit_head(&AttributeList::empty(), &vis)? else {
                break;
            };

            decl.visibility = vis;
            result.methods.push(decl);
            parser.eat(&TokenKind::Semi)?;
        }
        let end_token = parser.eat(&TokenKind::CloseBrace)?;

        Ok(result.between(parser.file_id, &start_token.span, &end_token.span))
    }
}

pub(crate) struct ImplBlockParser {}

impl KeywordPeekingParser<Loc<ImplBlock>> for ImplBlockParser {
    fn is_leading_token(&self) -> fn(&TokenKind) -> bool {
        |kind| kind == &TokenKind::Impl
    }

    fn parse(
        &self,
        parser: &mut Parser,
        attributes: &AttributeList,
        visibility: &Loc<Visibility>,
    ) -> Result<Loc<ImplBlock>> {
        let start_token = parser.eat_unconditional()?;
        parser.disallow_attributes(attributes, &start_token)?;
        parser.disallow_visibility(visibility, &start_token)?;

        let type_params = parser.generics_list()?;

        let trait_or_target_path = parser.type_spec(false)?;

        let (r#trait, target) = if parser.peek_and_eat(&TokenKind::For)?.is_some() {
            let (trait_path, params) = match trait_or_target_path.inner.clone() {
                TypeSpec::Named(p, params) => (p, params),
                other => {
                    return Err(Diagnostic::error(
                        trait_or_target_path,
                        format!("{other} is not a trait"),
                    ))
                }
            };
            let r#trait = TraitSpec {
                path: trait_path.clone(),
                type_params: params,
                paren_syntax: false,
            }
            .at_loc(&trait_or_target_path);

            let target = parser.type_spec(false)?;

            (Some(r#trait), target)
        } else {
            let target = trait_or_target_path;
            (None, target)
        };

        let where_clauses = parser.where_clauses()?;

        let (body, body_span) = parser.surrounded(
            &TokenKind::OpenBrace,
            Parser::impl_body,
            &TokenKind::CloseBrace,
        )?;

        Ok(ImplBlock {
            r#trait,
            type_params,
            target,
            where_clauses,
            units: body,
        }
        .between(parser.file_id, &start_token.span, &body_span.span))
    }
}

pub(crate) struct StructParser {}

impl KeywordPeekingParser<Loc<TypeDeclaration>> for StructParser {
    fn is_leading_token(&self) -> fn(&TokenKind) -> bool {
        |kind| kind == &TokenKind::Struct
    }

    fn parse(
        &self,
        parser: &mut Parser,
        attributes: &AttributeList,
        visibility: &Loc<Visibility>,
    ) -> Result<Loc<TypeDeclaration>> {
        let start_token = parser.eat_unconditional()?;

        let port_keyword = parser
            .peek_and_eat(&TokenKind::Port)?
            .map(|tok| ().at(parser.file_id, &tok.span()));

        let name = parser.identifier()?;

        let type_params = parser.generics_list()?;

        let (members, members_loc) = parser.surrounded(
            &TokenKind::OpenBrace,
            Parser::type_parameter_list,
            &TokenKind::CloseBrace,
        )?;
        let members = members.at_loc(&members_loc);

        let result = TypeDeclaration {
            visibility: visibility.clone(),
            name: name.clone(),
            kind: TypeDeclKind::Struct(
                Struct {
                    name,
                    members,
                    port_keyword,
                    attributes: attributes.clone(),
                }
                .between(parser.file_id, &start_token.span, &members_loc),
            ),
            generic_args: type_params,
        }
        .between(parser.file_id, &start_token.span, &members_loc);

        Ok(result)
    }
}

pub(crate) struct EnumParser {}

impl KeywordPeekingParser<Loc<TypeDeclaration>> for EnumParser {
    fn is_leading_token(&self) -> fn(&TokenKind) -> bool {
        |kind| kind == &TokenKind::Enum
    }

    fn parse(
        &self,
        parser: &mut Parser,
        attributes: &AttributeList,
        visibility: &Loc<Visibility>,
    ) -> Result<Loc<TypeDeclaration>> {
        let start_token = parser.eat_unconditional()?;

        let name = parser.identifier()?;

        let type_params = parser.generics_list()?;

        let (options, options_loc) = parser.surrounded(
            &TokenKind::OpenBrace,
            |s: &mut Parser| {
                s.comma_separated(Parser::enum_variant, &TokenKind::CloseBrace)
                    .no_context()
            },
            &TokenKind::CloseBrace,
        )?;

        let result = TypeDeclaration {
            visibility: visibility.clone(),
            name: name.clone(),
            kind: TypeDeclKind::Enum(
                Enum {
                    name,
                    variants: options,
                    attributes: attributes.clone(),
                }
                .between(parser.file_id, &start_token.span, &options_loc),
            ),
            generic_args: type_params,
        }
        .between(parser.file_id, &start_token.span, &options_loc);

        Ok(result)
    }
}

pub(crate) struct ModuleParser {}

impl KeywordPeekingParser<Item> for ModuleParser {
    fn is_leading_token(&self) -> fn(&TokenKind) -> bool {
        |kind| kind == &TokenKind::Mod
    }

    fn parse(
        &self,
        parser: &mut Parser,
        attributes: &AttributeList,
        visibility: &Loc<Visibility>,
    ) -> Result<Item> {
        let start = parser.eat_unconditional()?;
        let name = parser.identifier()?;

        if parser.peek_kind(&TokenKind::OpenBrace)? {
            let open_brace = parser.peek()?;
            let (body, end) = parser.surrounded(
                &TokenKind::OpenBrace,
                Parser::module_body,
                &TokenKind::CloseBrace,
            )?;
            Ok(Item::Module(
                Module {
                    visibility: visibility.clone(),
                    name,
                    body: body.between(parser.file_id, &open_brace.span, &end.span),
                    attributes: attributes.clone(),
                }
                .between(parser.file_id, &start, &end),
            ))
        } else if parser.peek_and_eat(&TokenKind::Semi)?.is_some() {
            let end = name.loc();
            Ok(Item::ExternalMod(
                ExternalMod {
                    visibility: visibility.clone(),
                    name,
                    attributes: attributes.clone(),
                }
                .between(parser.file_id, &start, &end),
            ))
        } else {
            Err(UnexpectedToken {
                got: parser.peek()?,
                expected: vec![";", "{"],
            }
            .into())
        }
    }
}

pub(crate) struct UseParser {}

impl KeywordPeekingParser<(AttributeList, Loc<Vec<UseStatement>>)> for UseParser {
    fn is_leading_token(&self) -> fn(&TokenKind) -> bool {
        |kind| kind == &TokenKind::Use
    }

    fn parse(
        &self,
        parser: &mut Parser,
        attributes: &AttributeList,
        visibility: &Loc<Visibility>,
    ) -> Result<(AttributeList, Loc<Vec<UseStatement>>)> {
        let start = parser.eat_unconditional()?;
        let paths = parser.path_tree_with_as_alias()?;
        let end = parser.eat(&TokenKind::Semi)?;

        Ok((
            attributes.clone(),
            paths
                .into_iter()
                .map(|(path, alias)| UseStatement {
                    visibility: visibility.clone(),
                    path,
                    alias,
                })
                .collect::<Vec<_>>()
                .between(parser.file_id, &start.span(), &end.span()),
        ))
    }
}
