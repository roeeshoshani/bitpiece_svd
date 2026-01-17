use proc_macro2::Span;
use syn::Ident;

/// Convert an arbitrary string into a *safe* Rust identifier.
/// - invalid chars -> '_'
/// - leading digit -> prefix '_'
/// - Rust keyword -> append '_'
pub fn ident(s: impl AsRef<str>) -> Ident {
    let mut out = s.as_ref().to_string();

    // Replace invalid chars with underscores
    out = out
        .chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || c == '_' {
                c
            } else {
                '_'
            }
        })
        .collect();

    // Cannot be empty
    if out.is_empty() {
        out.push('_');
    }

    // Cannot start with a digit
    if out.chars().next().unwrap().is_ascii_digit() {
        out.insert(0, '_');
    }

    // Avoid keywords
    if is_rust_keyword(&out) {
        out.push('_');
    }

    Ident::new(&out, Span::call_site())
}

pub fn snake_ident(s: impl AsRef<str>) -> Ident {
    ident(heck::AsSnakeCase(s.as_ref()).to_string())
}

fn is_rust_keyword(s: &str) -> bool {
    matches!(
        s,
        "as" | "break"
            | "const"
            | "continue"
            | "crate"
            | "else"
            | "enum"
            | "extern"
            | "false"
            | "fn"
            | "for"
            | "if"
            | "impl"
            | "in"
            | "let"
            | "loop"
            | "match"
            | "mod"
            | "move"
            | "mut"
            | "pub"
            | "ref"
            | "return"
            | "self"
            | "Self"
            | "static"
            | "struct"
            | "super"
            | "trait"
            | "true"
            | "type"
            | "unsafe"
            | "use"
            | "where"
            | "while"
            | "async"
            | "await"
            | "dyn"
            | "yield"
            | "try"
    )
}
