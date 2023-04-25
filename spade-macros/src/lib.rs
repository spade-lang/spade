use proc_macro::TokenStream;
use proc_macro2::Literal;
use proc_macro2::TokenStream as TokenStream2;
use proc_macro_error::{abort, abort_call_site, proc_macro_error};
use quote::{quote, ToTokens};
use syn::Fields;
use syn::FieldsNamed;
use syn::{
    parse::{Nothing, Parse, ParseStream},
    parse_macro_input, parse_quote,
    punctuated::Punctuated,
    Expr, Ident, ImplItemMethod, Token,
};

// Thanks to discord user Yandros(MemeOverloard) for doing the bulk of the work with this
// macro
#[proc_macro_attribute]
pub fn trace_parser(attrs: TokenStream, input: TokenStream) -> TokenStream {
    parse_macro_input!(attrs as Nothing);
    let mut input = parse_macro_input!(input as ImplItemMethod);
    let block = &mut input.block;

    let function_name = format!("{}", input.sig.ident);

    *block = parse_quote!({
        self.parse_stack.push(ParseStackEntry::Enter(#function_name.to_string()));
        let ret: Result<_> = (|| #block)();
        if let Err(e) = &ret {
            self.parse_stack.push(ParseStackEntry::ExitWithError(e.clone()));
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
    let mut input = parse_macro_input!(input as ImplItemMethod);
    let block = &mut input.block;

    let function_name = format!("{}", input.sig.ident);

    *block = parse_quote!({
        self.trace_stack.push(TraceStackEntry::Enter(#function_name.to_string()));
        let ret: Result<_> = (|| #block)();
        self.trace_stack.push(TraceStackEntry::Exit);
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

fn field_attributes(fields: &FieldsNamed) -> Vec<(&Ident, DiagnosticAttribute)> {
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
                        attr.path
                            .get_ident()
                            .map(|ident| ident == "diagnostic")
                            .unwrap_or(false)
                    }),
                )
            })
        })
        .flatten()
        .map(|(field, attr)| match attr.parse_args() {
            Ok(attr) => (field, attr),
            Err(_) => {
                abort!(attr, "inner attribute is malformed\nexpected #[diagnostic(<primary/secondary>, <MESSAGE...>)]")
            }
        })
        .collect()
}

#[proc_macro_error]
#[proc_macro_derive(IntoDiagnostic, attributes(diagnostic))]
pub fn derive_diagnostic(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as syn::ItemStruct);
    let fields = match &input.fields {
        Fields::Named(fields) => fields,
        Fields::Unnamed(_) => {
            abort_call_site!("Can only derive IntoDiagnostic on structs with named fields")
        }
        Fields::Unit => {
            abort_call_site!("Can only derive IntoDiagnostic on structs with named fields")
        }
    };
    let ident = input.ident;
    let top_attribute = input
        .attrs
        .iter()
        .find(|attr| {
            attr.path
                .get_ident()
                .map(|ident| ident == "diagnostic")
                .unwrap_or(false)
        })
        .unwrap_or_else(|| abort_call_site!("missing outer #[diagnostic] attribute"));
    let DiagnosticAttribute {
        ident: level,
        message: primary_message,
    } = top_attribute
        .parse_args()
        .unwrap_or_else(|_| abort!(top_attribute, "top attribute is malformed\nexpected something like `#[diagnostic(error, \"uh oh, stinky\")]`"));
    let primary_message = primary_message.map(|msg| msg.quote());
    let attrs = field_attributes(fields);
    let primary = attrs
        .iter()
        .find(|(_, attr)| attr.ident == "primary")
        .unwrap_or_else(|| abort_call_site!("primary span is required"));
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
        .map(|(field, attr)| {
            let message = attr
                .message
                .as_ref()
                .map(DiagnosticMessage::quote)
                .unwrap_or_else(|| abort_call_site!("secondary spans require a message"));
            quote!( .secondary_label(diag.#field, #message) )
        });

    quote! {
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
    .into()
}

#[proc_macro_error]
#[proc_macro_derive(IntoSubdiagnostic, attributes(diagnostic))]
pub fn derive_subdiagnostic(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as syn::ItemStruct);
    let fields = match &input.fields {
        Fields::Named(fields) => fields,
        Fields::Unnamed(_) => {
            abort_call_site!("Can only derive IntoSubdiagnostic on structs with named fields")
        }
        Fields::Unit => {
            abort_call_site!("Can only derive IntoSubdiagnostic on structs with named fields")
        }
    };
    let ident = input.ident;
    let top_attribute = input
        .attrs
        .iter()
        .find(|attr| {
            attr.path
                .get_ident()
                .map(|ident| ident == "diagnostic")
                .unwrap_or(false)
        })
        .unwrap_or_else(|| abort_call_site!("missing outer #[diagnostic] attribute"));
    let DiagnosticAttribute {
        ident: subdiag_kind,
        message,
    } = top_attribute
        .parse_args()
        .unwrap_or_else(|_| abort!(top_attribute, "top attribute is malformed\nexpected something like `#[diagnostic(suggestion, \"uh oh, stinky\")]`"));
    let message = message
        .as_ref()
        .map(DiagnosticMessage::quote)
        .unwrap_or(quote!(""));
    let attrs = field_attributes(fields);
    match subdiag_kind.to_string().as_str() {
        "suggestion" => {
            let parts = attrs.iter().filter_map(|(field, attr)| {
                let replacement = attr
                    .message
                    .as_ref()
                    .map(DiagnosticMessage::quote)
                    .unwrap_or(quote!(""));
                match attr.ident.to_string().as_str() {
                    "replace" => Some(quote!((diag.#field.into(), #replacement.to_string()))),
                    "insert_before" => todo!(),
                    "insert_after" => todo!(),
                    "remove" => todo!(),
                    _ => abort!(attr.ident, "unknown suggestion part kind"),
                }
            });
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
        .into(),
        _ => abort!(subdiag_kind, "unknown subdiagnostic kind"),
    }
}

#[cfg(test)]
mod test {
    #[test]
    fn ui() {
        let t = trybuild::TestCases::new();
        t.compile_fail("tests/ui/*.rs");
    }
}
