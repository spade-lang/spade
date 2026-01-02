use proc_macro::TokenStream;
use proc_macro2::{Literal, Span, TokenStream as TokenStream2};
use quote::{quote, ToTokens};
use syn::parse::{Nothing, Parse, ParseStream};
use syn::punctuated::Punctuated;
use syn::{parse_macro_input, parse_quote};
use syn::{Error, Expr, Fields, FieldsNamed, Ident, ImplItemFn, ItemStruct, Token};

// Thanks to discord user Yandros(MemeOverloard) for doing the bulk of the work with this
// macro
#[proc_macro_attribute]
pub fn trace_parser(attrs: TokenStream, input: TokenStream) -> TokenStream {
    parse_macro_input!(attrs as Nothing);
    let mut input = parse_macro_input!(input as ImplItemFn);
    let block = &mut input.block;

    let function_name = format!("{}", input.sig.ident);

    *block = parse_quote!({
        self.parse_stack.push(ParseStackEntry::Enter(#function_name.to_string()));
        let ret: Result<_> = (|| #block)();
        if let Err(e) = &ret {
            self.parse_stack.push(ParseStackEntry::ExitWithDiagnostic(e.clone()));
        }
        else {
            self.parse_stack.push(ParseStackEntry::Exit);
        }
        ret
    });
    input.into_token_stream().into()
}

#[proc_macro_attribute]
pub fn trace_typechecker(attrs: TokenStream, input: TokenStream) -> TokenStream {
    parse_macro_input!(attrs as Nothing);
    let mut input = parse_macro_input!(input as ImplItemFn);
    let block = &mut input.block;

    let function_name = format!("{}", input.sig.ident);

    *block = parse_quote!({
        self.trace_stack.push(|| TraceStackEntry::Enter(#function_name.to_string()));
        let ret: Result<_> = (|| #block)();
        self.trace_stack.push(|| TraceStackEntry::Exit);
        ret
    });
    input.into_token_stream().into()
}

enum DiagnosticMessage {
    /// `"message"`
    Literal(Literal),
    /// `"literal containing {} or more expressions as format arguments", 1`
    Formatted(Literal, Punctuated<Expr, Token![,]>),
}

impl Parse for DiagnosticMessage {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let first = input.parse()?;
        let _: Option<Token![,]> = input.parse()?;
        if input.is_empty() {
            return Ok(DiagnosticMessage::Literal(first));
        }
        let rest = Punctuated::parse_terminated(input)?;
        Ok(DiagnosticMessage::Formatted(first, rest))
    }
}

impl DiagnosticMessage {
    fn quote(&self) -> TokenStream2 {
        match self {
            DiagnosticMessage::Literal(lit) => quote!( #lit ),
            DiagnosticMessage::Formatted(lit, rest) => quote!(format!(#lit, #rest)),
        }
    }
}

/// E.g. `primary, "Expected {} arguments, got {}", diag.expected, diag.got`
struct DiagnosticAttribute {
    ident: Ident,
    message: Option<DiagnosticMessage>,
}

impl Parse for DiagnosticAttribute {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let ident = input.parse()?;
        if input.is_empty() {
            return Ok(DiagnosticAttribute {
                ident,
                message: None,
            });
        }
        let _: Token![,] = input.parse()?;
        let message = Some(input.parse()?);
        Ok(DiagnosticAttribute { ident, message })
    }
}

fn field_attributes(fields: &FieldsNamed) -> Result<Vec<(&Ident, DiagnosticAttribute)>, Error> {
    fields
        .named
        .iter()
        .filter_map(|field| {
            field.ident.as_ref().map(|field_ident| {
                // Zip the attributes together with the field they're on.
                std::iter::zip(
                    std::iter::repeat(field_ident),
                    // Only the #[diagnostic]-attributes
                    field.attrs.iter().filter(|attr| {
                        attr.path()
                            .get_ident()
                            .map(|ident| ident == "diagnostic")
                            .unwrap_or(false)
                    }),
                )
            })
        })
        .flatten()
        .map(|(field, attr)| match attr.parse_args() {
            Ok(attr) => Ok((field, attr)),
            Err(_) => {
                Err(Error::new_spanned(attr, "inner attribute is malformed\nexpected #[diagnostic(<primary/secondary>, <MESSAGE...>)]"))
            }
        })
        .collect()
}

/// Expected usage:
///
/// ```ignore
/// #[derive(IntoDiagnostic, Clone)]
/// #[diagnostic(error, "Expected argument list")]
/// pub(crate) struct ExpectedArgumentList {
///     #[diagnostic(primary, "Expected argument list for this instantiation")]
///     pub base_expr: Loc<()>,
///     pub next_token: Token,
/// }
/// ```
fn actual_derive_diagnostic(input: ItemStruct) -> Result<TokenStream, Error> {
    let fields = match &input.fields {
        Fields::Named(fields) => fields,
        Fields::Unnamed(_) | Fields::Unit => {
            return Err(Error::new(
                Span::call_site(),
                "Can only derive IntoDiagnostic on structs with named fields",
            ));
        }
    };
    let ident = input.ident;

    // Get the top attribute: `#[diagnostic(error, "...")]`
    let top_attribute = input
        .attrs
        .iter()
        .find(|attr| {
            attr.path()
                .get_ident()
                .map(|ident| ident == "diagnostic")
                .unwrap_or(false)
        })
        .ok_or_else(|| Error::new(Span::call_site(), "missing outer #[diagnostic] attribute"))?;
    let DiagnosticAttribute {
        ident: level,
        message: primary_message,
    } = top_attribute
        .parse_args()
        .map_err(|_| Error::new_spanned(top_attribute, "top attribute is malformed\nexpected something like `#[diagnostic(error, \"uh oh, stinky\")]`"))?;
    let primary_message = primary_message.map(|msg| msg.quote());

    // Look for field attributes (`#[diagnostic(primary, "...")]`), as a vec of
    // idents and their diagnostic attribute. Only diagnostic attributes are
    // handled.
    let attrs = field_attributes(fields)?;
    let primary = attrs
        .iter()
        .find(|(_, attr)| attr.ident == "primary")
        .ok_or_else(|| Error::new(Span::call_site(), "primary span is required"))?;
    let primary_span = primary.0;
    let primary_label = primary
        .1
        .message
        .as_ref()
        .map(DiagnosticMessage::quote)
        .map(|msg| quote!( .primary_label(#msg) ))
        .unwrap_or_default();
    let secondary_labels = attrs
        .iter()
        .filter(|(_, attr)| attr.ident == "secondary")
        .map(|(field, attr)| -> Result<_, Error> {
            let message = attr
                .message
                .as_ref()
                .map(DiagnosticMessage::quote)
                .ok_or_else(|| {
                    Error::new(Span::call_site(), "secondary spans require a message")
                })?;
            Ok(quote!( .secondary_label(diag.#field, #message) ))
        })
        .collect::<Result<Vec<_>, _>>()?;

    // Generate the code, with safe paths.
    Ok(quote! {
        impl std::convert::From<#ident> for ::spade_diagnostics::Diagnostic {
            fn from(diag: #ident) -> Self {
                ::spade_diagnostics::Diagnostic::#level(
                    diag.#primary_span,
                    #primary_message
                )
                #primary_label
                #(#secondary_labels)*
            }
        }
    }
    .into())
}

#[proc_macro_derive(IntoDiagnostic, attributes(diagnostic))]
pub fn derive_diagnostic(input: TokenStream) -> TokenStream {
    match syn::parse2(input.into())
        .and_then(actual_derive_diagnostic)
        .map_err(|e| e.into_compile_error().into())
    {
        Ok(ts) | Err(ts) => ts,
    }
}

/// Expected usage:
///
/// ```ignore
/// #[derive(IntoSubdiagnostic)]
/// #[diagnostic(suggestion, "Use `{` if you want to add items to this enum variant")]
/// pub(crate) struct SuggestBraceEnumVariant {
///     #[diagnostic(replace, "{")]
///     pub open_paren: Loc<()>,
///     #[diagnostic(replace, "}")]
///     pub close_paren: Loc<()>,
/// }
/// ```
fn actual_derive_subdiagnostic(input: ItemStruct) -> Result<TokenStream, Error> {
    let fields = match &input.fields {
        Fields::Named(fields) => fields,
        Fields::Unnamed(_) | Fields::Unit => {
            return Err(Error::new(
                Span::call_site(),
                "Can only derive IntoSubdiagnostic on structs with named fields",
            ));
        }
    };
    let ident = input.ident;

    // Get the top attribute: `#[diagnostic(suggestion, "...")]`
    let top_attribute = input
        .attrs
        .iter()
        .find(|attr| {
            attr.path()
                .get_ident()
                .map(|ident| ident == "diagnostic")
                .unwrap_or(false)
        })
        .ok_or_else(|| Error::new(Span::call_site(), "missing outer #[diagnostic] attribute"))?;
    let DiagnosticAttribute {
        ident: subdiag_kind,
        message,
    } = top_attribute
        .parse_args()
        .map_err(|_| Error::new_spanned(top_attribute, "top attribute is malformed\nexpected something like `#[diagnostic(suggestion, \"uh oh, stinky\")]`"))?;
    let message = message
        .as_ref()
        .map(DiagnosticMessage::quote)
        .unwrap_or(quote!(""));

    // Look for field attributes (`#[diagnostic(replace, "...")]`), as a vec of
    // idents and their diagnostic attribute. Only diagnostic attributes are
    // handled.
    let attrs = field_attributes(fields)?;
    let tokens = match subdiag_kind.to_string().as_str() {
        "suggestion" => {
            let parts = attrs
                .iter()
                .map(|(field, attr)| {
                    let replacement = attr
                        .message
                        .as_ref()
                        .map(DiagnosticMessage::quote)
                        .unwrap_or(quote!(""));
                    match attr.ident.to_string().as_str() {
                        "replace" => Ok(quote!((diag.#field.into(), #replacement.to_string()))),
                        "insert_before" | "insert_after" | "remove" => todo!(),
                        _ => Err(Error::new_spanned(
                            &attr.ident,
                            "unknown suggestion part kind",
                        )),
                    }
                })
                .collect::<Result<Vec<_>, _>>()?;
            quote! {
                impl std::convert::From<#ident> for ::spade_diagnostics::diagnostic::Subdiagnostic {
                    fn from(diag: #ident) -> Self {
                        ::spade_diagnostics::diagnostic::Subdiagnostic::Suggestion {
                            parts: vec![#(#parts),*],
                            message: #message.into(),
                        }
                    }
                }
            }
        }
        _ => {
            return Err(Error::new_spanned(
                subdiag_kind,
                "unknown subdiagnostic kind",
            ))
        }
    };
    Ok(tokens.into())
}

#[proc_macro_derive(IntoSubdiagnostic, attributes(diagnostic))]
pub fn derive_subdiagnostic(input: TokenStream) -> TokenStream {
    match syn::parse2(input.into())
        .and_then(actual_derive_subdiagnostic)
        .map_err(|e| e.into_compile_error().into())
    {
        Ok(ts) | Err(ts) => ts,
    }
}

#[cfg(test)]
mod test {
    mod into_diagnostic {
        #[test]
        fn ui() {
            let t = trybuild::TestCases::new();
            t.compile_fail("tests/into_diagnostic/ui/*.rs");
        }
    }

    mod into_subdiagnostic {
        #[test]
        fn ui() {
            let t = trybuild::TestCases::new();
            t.compile_fail("tests/into_subdiagnostic/ui/*.rs");
        }
    }
}
