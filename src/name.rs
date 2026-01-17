use svd_parser::svd;

/// Use SVD groupName if present; else strip trailing digits from peripheral name.
pub fn group_key_from_peripheral(p: &svd::PeripheralInfo) -> String {
    if let Some(g) = &p.group_name {
        return g.clone();
    }
    strip_trailing_digits(&p.name)
}

/// module name sanitization (snake_case + avoid keywords)
pub fn sanitize_mod_name(s: &str) -> String {
    let mut m = heck::AsSnakeCase(s).to_string();
    if is_keyword(&m) {
        m.push('_');
    }
    m
}

fn strip_trailing_digits(name: &str) -> String {
    let mut end = name.len();
    for (i, ch) in name.char_indices().rev() {
        if ch.is_ascii_digit() {
            end = i;
        } else {
            break;
        }
    }
    name[..end].trim_end_matches('_').to_string()
}

fn is_keyword(s: &str) -> bool {
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
    )
}
