use tower_lsp::lsp_types::{CompletionItem, CompletionItemKind};

const KEYWORDS: [&str; 34] = [
    "true", "false", "LOW", "HIGH", "HIGHIMP", "reg", "let", "decl", "inst", "reset", "initial",
    "if", "else", "match", "set", "pipeline", "stage", "entity", "trait", "impl", "for", "fn",
    "enum", "struct", "port", "mod", "use", "as", "assert", "mut", "where", "$config", "$if",
    "$else",
];
pub const NR_OF_KEYWORDS: usize = KEYWORDS.len();

pub fn get_keyword_completions() -> [CompletionItem; NR_OF_KEYWORDS] {
    KEYWORDS
        .iter()
        .map(|s| get_keyword_completion(s))
        .collect::<Vec<CompletionItem>>()
        .try_into()
        .unwrap()
}

fn get_keyword_completion(label: &str) -> CompletionItem {
    let mut comp_item = CompletionItem::new_simple(label.to_string(), label.to_string());
    comp_item.kind = Some(CompletionItemKind::KEYWORD);

    comp_item
}
