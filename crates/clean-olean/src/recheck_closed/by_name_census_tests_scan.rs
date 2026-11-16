// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The by-name census's lexer and item discovery over the kernel's source
//! (`by_name_census_tests.rs`).

use super::*;

// ─────────────────────────────────────────────────────────────────────────────
// Lexing and item discovery.
// ─────────────────────────────────────────────────────────────────────────────

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum Tok {
    Ident(String),
    Str(String),
    ByteStr(String),
    Punct(char),
}

/// Tokenize Rust source: comments dropped, string/char literals folded,
/// everything else an identifier or a single punctuation character.
pub(super) fn lex(src: &str) -> Vec<Tok> {
    let b: Vec<char> = src.chars().collect();
    let mut out = Vec::new();
    let mut i = 0;
    let at = |i: usize, s: &str| -> bool {
        s.chars().enumerate().all(|(k, c)| b.get(i + k) == Some(&c))
    };
    while i < b.len() {
        let c = b[i];
        if at(i, "//") {
            while i < b.len() && b[i] != '\n' {
                i += 1;
            }
            continue;
        }
        if at(i, "/*") {
            let mut depth = 0;
            while i < b.len() {
                if at(i, "/*") {
                    depth += 1;
                    i += 2;
                } else if at(i, "*/") {
                    depth -= 1;
                    i += 2;
                    if depth == 0 {
                        break;
                    }
                } else {
                    i += 1;
                }
            }
            continue;
        }
        // Raw string r"…", r#"…"#, br"…".
        let prev_ident = i > 0 && (b[i - 1].is_alphanumeric() || b[i - 1] == '_');
        if !prev_ident && (c == 'r' || (c == 'b' && b.get(i + 1) == Some(&'r'))) {
            let mut j = if c == 'b' { i + 2 } else { i + 1 };
            let mut hashes = 0;
            while b.get(j) == Some(&'#') {
                hashes += 1;
                j += 1;
            }
            if b.get(j) == Some(&'"') {
                j += 1;
                let start = j;
                loop {
                    if j >= b.len() {
                        break;
                    }
                    if b[j] == '"' && (0..hashes).all(|k| b.get(j + 1 + k) == Some(&'#')) {
                        break;
                    }
                    j += 1;
                }
                let value = b[start..j.min(b.len())].iter().collect();
                out.push(if c == 'b' {
                    Tok::ByteStr(value)
                } else {
                    Tok::Str(value)
                });
                i = j + 1 + hashes;
                continue;
            }
        }
        if c == '"' || (!prev_ident && c == 'b' && b.get(i + 1) == Some(&'"')) {
            let byte = c == 'b';
            let mut j = i + 1 + usize::from(byte);
            let mut s = String::new();
            while j < b.len() && b[j] != '"' {
                if b[j] == '\\' {
                    j += 1;
                    let escaped = *b.get(j).expect("terminated Rust string escape");
                    j += 1;
                    match escaped {
                        'n' => s.push('\n'),
                        'r' => s.push('\r'),
                        't' => s.push('\t'),
                        '0' => s.push('\0'),
                        '\\' | '\'' | '"' => s.push(escaped),
                        'x' => {
                            let digits: String = b[j..j + 2].iter().collect();
                            s.push(char::from(
                                u8::from_str_radix(&digits, 16).expect("Rust hex escape"),
                            ));
                            j += 2;
                        }
                        'u' => {
                            assert_eq!(b.get(j), Some(&'{'), "Rust Unicode escape");
                            j += 1;
                            let start = j;
                            while b.get(j) != Some(&'}') {
                                j += 1;
                            }
                            let digits: String =
                                b[start..j].iter().filter(|c| **c != '_').collect();
                            s.push(
                                char::from_u32(
                                    u32::from_str_radix(&digits, 16).expect("Rust Unicode scalar"),
                                )
                                .expect("Rust Unicode scalar"),
                            );
                            j += 1;
                        }
                        '\n' | '\r' => {
                            while b.get(j).is_some_and(|c| c.is_whitespace()) {
                                j += 1;
                            }
                        }
                        _ => panic!("unknown Rust string escape: {escaped}"),
                    }
                } else {
                    s.push(b[j]);
                    j += 1;
                }
            }
            out.push(if byte { Tok::ByteStr(s) } else { Tok::Str(s) });
            i = j + 1;
            continue;
        }
        if c == '\'' {
            // A char literal ('x', '\n', '\u{..}'); otherwise a lifetime.
            if b.get(i + 1) == Some(&'\\') {
                let mut j = i + 2;
                while j < b.len() && b[j] != '\'' {
                    j += 1;
                }
                i = j + 1;
                continue;
            }
            if b.get(i + 2) == Some(&'\'') {
                i += 3;
                continue;
            }
            i += 1;
            continue;
        }
        if c.is_alphabetic() || c == '_' {
            let mut j = i;
            while j < b.len() && (b[j].is_alphanumeric() || b[j] == '_') {
                j += 1;
            }
            out.push(Tok::Ident(b[i..j].iter().collect()));
            i = j;
            continue;
        }
        if c.is_ascii_digit() {
            let mut j = i;
            while j < b.len() && (b[j].is_alphanumeric() || b[j] == '_' || b[j] == '.') {
                if b[j] == '.' && !b.get(j + 1).is_some_and(char::is_ascii_digit) {
                    break;
                }
                j += 1;
            }
            i = j;
            continue;
        }
        if !c.is_whitespace() {
            out.push(Tok::Punct(c));
        }
        i += 1;
    }
    out
}

pub(super) fn ident(t: Option<&Tok>) -> Option<&str> {
    match t {
        Some(Tok::Ident(s)) => Some(s),
        _ => None,
    }
}

pub(super) fn is_punct(t: Option<&Tok>, c: char) -> bool {
    matches!(t, Some(Tok::Punct(p)) if *p == c)
}

/// Index just past the brace block opening at `open` (`toks[open] == '{'`).
pub(super) fn close_brace(toks: &[Tok], open: usize) -> usize {
    let mut depth = 0i32;
    let mut i = open;
    while i < toks.len() {
        match toks[i] {
            Tok::Punct('{') => depth += 1,
            Tok::Punct('}') => {
                depth -= 1;
                if depth == 0 {
                    return i + 1;
                }
            }
            _ => {}
        }
        i += 1;
    }
    toks.len()
}

/// A function, static/const, or macro: where its tokens are.
#[derive(Debug)]
pub(super) struct Item {
    pub(super) file: String,
    /// Index into [`Items::files`].
    pub(super) file_idx: usize,
    pub(super) name: String,
    /// The `impl`/`trait` block's type or trait name, if any.
    pub(super) owner: Option<String>,
    /// Token range of the item in its file.
    pub(super) range: (usize, usize),
}

#[derive(Default)]
pub(super) struct Items {
    /// Every source file's tokens.
    pub(super) files: Vec<Vec<Tok>>,
    /// Names of the kernel's own traits.
    pub(super) traits: BTreeSet<String>,
    /// Names of every type or trait some kernel `impl`/`trait` block is for.
    pub(super) owners: BTreeSet<String>,
    /// `struct`/`enum`/`union`/`type` definitions, with the attributes in
    /// front of them (`#[error("…", f(x))]` calls code from a derive). A
    /// reached type's definition is scanned like a body: its field types are
    /// values its methods call methods on.
    pub(super) type_defs: BTreeMap<String, Vec<Item>>,
    /// Type → the traits some kernel `impl Trait for Type` implements for it
    /// (a trait's default methods are callable on the type).
    pub(super) traits_of: BTreeMap<String, BTreeSet<String>>,
    /// `(type, trait)` → the methods its `impl Trait for Type` block defines.
    pub(super) impl_fns: BTreeMap<(String, String), Vec<(String, usize)>>,
    /// Traits used as `dyn Trait` anywhere in the crate. A value coerced to
    /// one carries a vtable holding EVERY method of its impl, so each is
    /// reachable once the type is.
    pub(super) dyn_traits: BTreeSet<String>,
    pub(super) fns: BTreeMap<String, Vec<Item>>,
    pub(super) statics: BTreeMap<String, Vec<Item>>,
    pub(super) macros: BTreeMap<String, Vec<Item>>,
    /// File → its `use` imports.
    pub(super) uses: BTreeMap<String, Vec<UseEntry>>,
    /// Every source file, relative to the kernel's `src/`.
    pub(super) file_names: BTreeSet<String>,
}

/// One imported name (or glob) of a `use` declaration.
#[derive(Debug)]
pub(super) struct UseEntry {
    /// The module the item comes from, as a kernel file-module path
    /// (`["env", "types"]`), or `None` when the path leaves the kernel crate.
    pub(super) module: Option<Vec<String>>,
    /// The imported item's own name; `None` for a glob.
    pub(super) name: Option<String>,
    /// The name it is bound to in the importing file.
    pub(super) alias: Option<String>,
}

/// The module path of a kernel source file: `env/types.rs` → `[env, types]`,
/// `env/mod.rs` → `[env]`, `lib.rs` → `[]`.
pub(super) fn module_of(file: &str) -> Vec<String> {
    let stem = file.strip_suffix(".rs").unwrap_or(file);
    let stem = stem.strip_suffix("/mod").unwrap_or(stem);
    if stem == "lib" {
        return Vec::new();
    }
    stem.split('/').map(str::to_string).collect()
}

pub(super) type RawUse = (Vec<String>, Option<String>, Option<String>);

/// One `use` tree starting at `i`; returns the index after it.
pub(super) fn use_tree(
    toks: &[Tok],
    mut i: usize,
    prefix: &mut Vec<String>,
    out: &mut Vec<RawUse>,
) -> usize {
    let depth_at_entry = prefix.len();
    loop {
        match toks.get(i) {
            Some(Tok::Punct('{')) => {
                i += 1;
                loop {
                    if is_punct(toks.get(i), '}') {
                        break;
                    }
                    i = use_tree(toks, i, prefix, out);
                    if is_punct(toks.get(i), ',') {
                        i += 1;
                        continue;
                    }
                    break;
                }
                if is_punct(toks.get(i), '}') {
                    i += 1;
                }
                break;
            }
            Some(Tok::Punct('*')) => {
                out.push((prefix.clone(), None, None));
                i += 1;
                break;
            }
            Some(Tok::Ident(seg)) => {
                let seg = seg.clone();
                if is_punct(toks.get(i + 1), ':') && is_punct(toks.get(i + 2), ':') {
                    prefix.push(seg);
                    i += 3;
                    continue;
                }
                let mut alias = None;
                i += 1;
                if ident(toks.get(i)) == Some("as") {
                    alias = ident(toks.get(i + 1)).map(str::to_string);
                    i += 2;
                }
                out.push((prefix.clone(), Some(seg), alias));
                break;
            }
            _ => break,
        }
    }
    prefix.truncate(depth_at_entry);
    i
}

/// The LOGICAL module path of every kernel file a `#[path = "…"] mod name;`
/// declaration includes: its declaring module plus `name`, which is what
/// `super::` and `self::` inside it mean -- not the file's own path.
/// `env/native_reducers_sint.rs` includes `native_reducers_sint_reg.rs` as
/// `mod registration`, so that file's `use super::*;` names
/// `env::native_reducers_sint`, where its registrations' fn items are; read as
/// `module_of` its file path it named `env`, and the 55 signed-int reducers the
/// replay links were reached by nothing (linker census, 2026-09-29).
pub(super) fn path_attr_modules(
    file_names: &BTreeSet<String>,
    files: &[Vec<Tok>],
) -> BTreeMap<String, Vec<String>> {
    // included file -> (declaring file, module name)
    let mut parent: BTreeMap<String, (String, String)> = BTreeMap::new();
    for (file, toks) in file_names.iter().zip(files) {
        let dir = file.rsplit_once('/').map_or("", |(d, _)| d);
        for i in 0..toks.len() {
            let is_path_attr = is_punct(toks.get(i), '#')
                && is_punct(toks.get(i + 1), '[')
                && ident(toks.get(i + 2)) == Some("path")
                && is_punct(toks.get(i + 3), '=')
                && is_punct(toks.get(i + 5), ']');
            let (true, Some(Tok::Str(rel))) = (is_path_attr, toks.get(i + 4)) else {
                continue;
            };
            // Skip further attributes and a visibility, then `mod <name> ;`.
            let mut k = i + 6;
            loop {
                if is_punct(toks.get(k), '#') && is_punct(toks.get(k + 1), '[') {
                    let mut depth = 0i32;
                    k += 1;
                    while k < toks.len() {
                        match toks[k] {
                            Tok::Punct('[') => depth += 1,
                            Tok::Punct(']') => {
                                depth -= 1;
                                if depth == 0 {
                                    break;
                                }
                            }
                            _ => {}
                        }
                        k += 1;
                    }
                    k += 1;
                } else if ident(toks.get(k)) == Some("pub") {
                    k += 1;
                    if is_punct(toks.get(k), '(') {
                        while k < toks.len() && !is_punct(toks.get(k), ')') {
                            k += 1;
                        }
                        k += 1;
                    }
                } else {
                    break;
                }
            }
            let (Some("mod"), Some(name)) = (ident(toks.get(k)), ident(toks.get(k + 1))) else {
                continue;
            };
            let mut target: Vec<&str> = Vec::new();
            for seg in dir.split('/').chain(rel.split('/')) {
                match seg {
                    "" | "." => {}
                    ".." => {
                        target.pop();
                    }
                    s => target.push(s),
                }
            }
            let target = target.join("/");
            if file_names.contains(&target) {
                parent.insert(target, (file.clone(), name.to_string()));
            }
        }
    }
    fn logical(
        file: &str,
        parent: &BTreeMap<String, (String, String)>,
        depth: usize,
    ) -> Vec<String> {
        match parent.get(file) {
            Some((declaring, name)) if depth < 16 => {
                let mut m = logical(declaring, parent, depth + 1);
                m.push(name.clone());
                m
            }
            _ => module_of(file),
        }
    }
    parent
        .keys()
        .map(|f| (f.clone(), logical(f, &parent, 0)))
        .collect()
}

/// Parse every `use` declaration in `toks` (a whole file) into entries.
/// `here` is the file's logical module path (`path_attr_modules`, else
/// `module_of`).
pub(super) fn parse_uses(
    here: Vec<String>,
    toks: &[Tok],
    file_names: &BTreeSet<String>,
) -> Vec<UseEntry> {
    let is_module = |segs: &[String]| {
        let p = segs.join("/");
        file_names.contains(&format!("{p}.rs")) || file_names.contains(&format!("{p}/mod.rs"))
    };
    let mut raw = Vec::new();
    for (i, t) in toks.iter().enumerate() {
        if ident(Some(t)) == Some("use") {
            let mut prefix = Vec::new();
            use_tree(toks, i + 1, &mut prefix, &mut raw);
        }
    }
    raw.into_iter()
        .map(|(path, name, alias)| {
            let mut segs = path.into_iter();
            let module = match segs.next().as_deref() {
                Some("crate") => Some(segs.collect::<Vec<_>>()),
                Some("self") => Some(here.iter().cloned().chain(segs).collect()),
                Some("super") => {
                    let mut m = here.clone();
                    m.pop();
                    let mut rest: Vec<String> = segs.collect();
                    while rest.first().map(String::as_str) == Some("super") {
                        m.pop();
                        rest.remove(0);
                    }
                    Some(m.into_iter().chain(rest).collect())
                }
                Some(first) => {
                    let mut local = here.clone();
                    local.push(first.to_string());
                    if is_module(&local) {
                        Some(local.into_iter().chain(segs).collect())
                    } else {
                        None
                    }
                }
                // `use name;` at the top level: a crate.
                None => None,
            };
            UseEntry {
                module,
                name,
                alias,
            }
        })
        .collect()
}

/// The owner named by an `impl` header's tokens (between `impl` and `{`).
pub(super) fn impl_owner(header: &[Tok]) -> Option<String> {
    let header: Vec<&Tok> = header
        .iter()
        .take_while(|t| ident(Some(t)) != Some("where"))
        .collect();
    let start = header
        .iter()
        .rposition(|t| ident(Some(t)) == Some("for"))
        .map_or(0, |p| p + 1);
    let mut depth = 0i32;
    let mut last = None;
    for t in &header[start..] {
        match t {
            Tok::Punct('<') => depth += 1,
            Tok::Punct('>') => depth -= 1,
            Tok::Ident(s) if depth == 0 && s != "dyn" && s != "impl" => last = Some(s.clone()),
            _ => {}
        }
    }
    last
}

/// The trait named by an `impl Trait for Type` header, if any.
pub(super) fn impl_trait(header: &[Tok]) -> Option<String> {
    let for_at = header.iter().position(|t| ident(Some(t)) == Some("for"))?;
    let mut depth = 0i32;
    let mut last = None;
    for t in &header[..for_at] {
        match t {
            Tok::Punct('<') => depth += 1,
            Tok::Punct('>') => depth -= 1,
            Tok::Ident(s) if depth == 0 => last = Some(s.clone()),
            _ => {}
        }
    }
    last
}

/// `text` up to its first `#[cfg(test)] mod <ident> {`, if any.
pub(super) fn strip_inline_test_module(text: &str) -> &str {
    let mut from = 0;
    while let Some(at) = text[from..].find("#[cfg(test)]") {
        let start = from + at;
        let rest = text[start + "#[cfg(test)]".len()..].trim_start();
        if let Some(after_mod) = rest.strip_prefix("mod ") {
            let ident_end = after_mod
                .find(|c: char| !(c.is_alphanumeric() || c == '_'))
                .unwrap_or(after_mod.len());
            if after_mod[ident_end..].trim_start().starts_with('{') {
                return &text[..start];
            }
        }
        from = start + 1;
    }
    text
}

#[allow(clippy::too_many_arguments)]
pub(super) fn collect_items(
    file: &str,
    file_idx: usize,
    toks: &[Tok],
    base: usize,
    owner: Option<&str>,
    via_trait: Option<&str>,
    items: &mut Items,
) {
    let mut i = 0;
    while i < toks.len() {
        match ident(toks.get(i)) {
            Some("impl") | Some("trait") => {
                let is_trait = ident(toks.get(i)) == Some("trait");
                let Some(open) = (i..toks.len())
                    .find(|&k| is_punct(toks.get(k), '{') || is_punct(toks.get(k), ';'))
                else {
                    break;
                };
                if is_punct(toks.get(open), ';') {
                    i = open + 1;
                    continue;
                }
                let name = if is_trait {
                    ident(toks.get(i + 1)).map(str::to_string)
                } else {
                    impl_owner(&toks[i + 1..open])
                };
                let trait_name = if is_trait {
                    None
                } else {
                    impl_trait(&toks[i + 1..open])
                };
                if let (Some(ty), Some(tr)) = (&name, &trait_name) {
                    items
                        .traits_of
                        .entry(ty.clone())
                        .or_default()
                        .insert(tr.clone());
                }
                if let Some(n) = &name {
                    items.owners.insert(n.clone());
                    if is_trait {
                        items.traits.insert(n.clone());
                    }
                }
                let end = close_brace(toks, open);
                collect_items(
                    file,
                    file_idx,
                    &toks[open + 1..end - 1],
                    base + open + 1,
                    name.as_deref(),
                    trait_name.as_deref(),
                    items,
                );
                i = end;
            }
            Some("mod") if ident(toks.get(i + 1)).is_some() && is_punct(toks.get(i + 2), '{') => {
                let end = close_brace(toks, i + 2);
                collect_items(
                    file,
                    file_idx,
                    &toks[i + 3..end - 1],
                    base + i + 3,
                    None,
                    None,
                    items,
                );
                i = end;
            }
            Some("fn") if ident(toks.get(i + 1)).is_some() => {
                let name = ident(toks.get(i + 1)).unwrap_or_default().to_string();
                let mut k = i + 2;
                let mut paren = 0i32;
                while k < toks.len() {
                    // `[T; N]` in a signature holds a `;` that ends nothing.
                    match toks[k] {
                        Tok::Punct('(') | Tok::Punct('[') => paren += 1,
                        Tok::Punct(')') | Tok::Punct(']') => paren -= 1,
                        Tok::Punct('{') | Tok::Punct(';') if paren == 0 => break,
                        _ => {}
                    }
                    k += 1;
                }
                if is_punct(toks.get(k), '{') {
                    let end = close_brace(toks, k);
                    if let (Some(ty), Some(tr)) = (owner, via_trait) {
                        let idx = items.fns.get(&name).map_or(0, Vec::len);
                        items
                            .impl_fns
                            .entry((ty.to_string(), tr.to_string()))
                            .or_default()
                            .push((name.clone(), idx));
                    }
                    items.fns.entry(name.clone()).or_default().push(Item {
                        file: file.to_string(),
                        file_idx,
                        name,
                        owner: owner.map(str::to_string),
                        range: (base + i, base + end),
                    });
                    i = end;
                } else {
                    i = k + 1;
                }
            }
            Some("static") | Some("const")
                if ident(toks.get(i + 1)).is_some_and(|n| n != "fn" && n != "_") =>
            {
                let name = ident(toks.get(i + 1)).unwrap_or_default().to_string();
                let mut k = i + 2;
                let mut depth = 0i32;
                while k < toks.len() {
                    match toks[k] {
                        Tok::Punct('(') | Tok::Punct('[') | Tok::Punct('{') => depth += 1,
                        Tok::Punct(')') | Tok::Punct(']') | Tok::Punct('}') => depth -= 1,
                        Tok::Punct(';') if depth <= 0 => break,
                        _ => {}
                    }
                    k += 1;
                }
                items.statics.entry(name.clone()).or_default().push(Item {
                    file: file.to_string(),
                    file_idx,
                    name,
                    owner: owner.map(str::to_string),
                    range: (base + i, base + k.min(toks.len())),
                });
                i = k + 1;
            }
            Some("struct") | Some("enum") | Some("union") | Some("type")
                if ident(toks.get(i + 1)).is_some() =>
            {
                let name = ident(toks.get(i + 1)).unwrap_or_default().to_string();
                // The definition runs to its closing brace, or to `;` for a
                // tuple struct, unit struct or alias.
                let mut k = i + 2;
                let mut depth = 0i32;
                let mut end = toks.len();
                while k < toks.len() {
                    match toks[k] {
                        Tok::Punct('(') | Tok::Punct('[') | Tok::Punct('<') => depth += 1,
                        Tok::Punct(')') | Tok::Punct(']') | Tok::Punct('>') => depth -= 1,
                        Tok::Punct(';') if depth <= 0 => {
                            end = k + 1;
                            break;
                        }
                        Tok::Punct('{') if depth <= 0 => {
                            end = close_brace(toks, k);
                            break;
                        }
                        _ => {}
                    }
                    k += 1;
                }
                // Include the attributes in front: walk back over `#[…]`
                // groups (and `pub`/`pub(crate)`).
                let mut start = i;
                loop {
                    if start > 0 && ident(toks.get(start - 1)) == Some("pub") {
                        start -= 1;
                        continue;
                    }
                    if start > 0 && is_punct(toks.get(start - 1), ')') {
                        // `pub(crate)`
                        if let Some(p) = (0..start - 1).rev().find(|&k| is_punct(toks.get(k), '('))
                        {
                            if p > 0 && ident(toks.get(p - 1)) == Some("pub") {
                                start = p - 1;
                                continue;
                            }
                        }
                    }
                    if start > 0 && is_punct(toks.get(start - 1), ']') {
                        let mut depth = 0i32;
                        let mut k = start - 1;
                        loop {
                            match toks[k] {
                                Tok::Punct(']') => depth += 1,
                                Tok::Punct('[') => depth -= 1,
                                _ => {}
                            }
                            if depth == 0 || k == 0 {
                                break;
                            }
                            k -= 1;
                        }
                        if k > 0 && is_punct(toks.get(k - 1), '#') {
                            start = k - 1;
                            continue;
                        }
                    }
                    break;
                }
                items.type_defs.entry(name.clone()).or_default().push(Item {
                    file: file.to_string(),
                    file_idx,
                    name,
                    owner: None,
                    range: (base + start, base + end.min(toks.len())),
                });
                i = end;
            }
            Some("macro_rules")
                if is_punct(toks.get(i + 1), '!') && ident(toks.get(i + 2)).is_some() =>
            {
                let name = ident(toks.get(i + 2)).unwrap_or_default().to_string();
                let Some(open) = (i + 3..toks.len()).find(|&k| is_punct(toks.get(k), '{')) else {
                    break;
                };
                let end = close_brace(toks, open);
                items.macros.entry(name.clone()).or_default().push(Item {
                    file: file.to_string(),
                    file_idx,
                    name,
                    owner: None,
                    range: (base + open, base + end),
                });
                i = end;
            }
            // A module-level macro invocation (`name!(pub X = "Nat.add");`,
            // `thread_local! { … }`) can define items the parser cannot see:
            // register it as a static under every SCREAMING_CASE identifier
            // it contains, so a use of that identifier reaches its literals.
            Some(_)
                if is_punct(toks.get(i + 1), '!')
                    && matches!(toks.get(i + 2), Some(Tok::Punct('(' | '[' | '{'))) =>
            {
                let (open_c, close_c) = match toks[i + 2] {
                    Tok::Punct('(') => ('(', ')'),
                    Tok::Punct('[') => ('[', ']'),
                    _ => ('{', '}'),
                };
                let mut depth = 0i32;
                let mut k = i + 2;
                while k < toks.len() {
                    if is_punct(toks.get(k), open_c) {
                        depth += 1;
                    } else if is_punct(toks.get(k), close_c) {
                        depth -= 1;
                        if depth == 0 {
                            break;
                        }
                    }
                    k += 1;
                }
                let end = (k + 1).min(toks.len());
                let defined: BTreeSet<String> = toks[i + 2..end]
                    .iter()
                    .filter_map(|t| ident(Some(t)))
                    .filter(|s| is_screaming(s))
                    .map(str::to_string)
                    .collect();
                for name in defined {
                    items.statics.entry(name.clone()).or_default().push(Item {
                        file: file.to_string(),
                        file_idx,
                        name,
                        owner: owner.map(str::to_string),
                        range: (base + i, base + end),
                    });
                }
                // ...and every lower-case identifier HANDED to it at its top
                // level as a function it may define
                // (`define_small_uint_reducers!(reduce_uint8_add, …)` writes
                // `fn reduce_uint8_add` from a `$add:ident`). A use of that
                // name reaches the invocation, and through it the macro's
                // body. Measured 2026-09-29 by the linker census: 55 kernel
                // items the replay links (the UInt/Int reducers every
                // `ensure_native_reducers` registers, which
                // `native_fold_authority::fold_key_universe` runs) were
                // reached by no source item, because their only callers were
                // these generated functions.
                for name in macro_handed_fn_names(&toks[i + 2..end]) {
                    items.fns.entry(name.clone()).or_default().push(Item {
                        file: file.to_string(),
                        file_idx,
                        name,
                        owner: owner.map(str::to_string),
                        range: (base + i, base + end),
                    });
                }
                // Items declared with keywords inside (`thread_local!`'s
                // `static`) are still collected.
                collect_items(
                    file,
                    file_idx,
                    &toks[i + 3..end.saturating_sub(1).max(i + 3)],
                    base + i + 3,
                    owner,
                    via_trait,
                    items,
                );
                i = end;
            }
            _ => i += 1,
        }
    }
}

/// The lower-case identifiers at the TOP level of a macro invocation's
/// delimited arguments (`group` starts at its opening delimiter): the names it
/// is handed, any of which a `$name:ident` fragment may turn into a function.
/// Keywords are not names; a nested group is the macro's input syntax, not a
/// name it is handed.
fn macro_handed_fn_names(group: &[Tok]) -> BTreeSet<String> {
    const KEYWORDS: &[&str] = &[
        "as", "async", "const", "crate", "dyn", "else", "enum", "false", "fn", "for", "if", "impl",
        "in", "let", "loop", "match", "mod", "move", "mut", "pub", "ref", "return", "self",
        "static", "struct", "super", "trait", "true", "type", "unsafe", "use", "where", "while",
    ];
    let mut depth = 0i32;
    let mut out = BTreeSet::new();
    for t in group {
        match t {
            Tok::Punct('(' | '[' | '{') => depth += 1,
            Tok::Punct(')' | ']' | '}') => depth -= 1,
            Tok::Ident(name)
                if depth == 1
                    && name.starts_with(|c: char| c.is_ascii_lowercase() || c == '_')
                    && !KEYWORDS.contains(&name.as_str()) =>
            {
                out.insert(name.clone());
            }
            _ => {}
        }
    }
    out
}

pub(super) fn kernel_src() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../clean-kernel/src")
}

pub(super) fn source_files(root: &Path) -> Vec<(String, String)> {
    let mut out = Vec::new();
    let mut stack = vec![root.to_path_buf()];
    while let Some(dir) = stack.pop() {
        for entry in std::fs::read_dir(&dir).expect("read kernel dir") {
            let path = entry.expect("dir entry").path();
            let name = path
                .file_name()
                .map(|f| f.to_string_lossy().into_owned())
                .unwrap_or_default();
            if path.is_dir() {
                // `bin/` holds separate binaries, not the kernel library.
                if !name.contains("test") && name != "bin" {
                    stack.push(path);
                }
                continue;
            }
            if !name.ends_with(".rs") || name.contains("test") {
                continue;
            }
            let text = std::fs::read_to_string(&path).expect("read kernel source");
            let rel = path
                .strip_prefix(root)
                .expect("under root")
                .to_string_lossy()
                .replace('\\', "/");
            out.push((rel, strip_inline_test_module(&text).to_string()));
        }
    }
    out.sort();
    out
}

/// Whether `s` is a SCREAMING_CASE identifier (a static or const name).
pub(super) fn is_screaming(s: &str) -> bool {
    s.len() > 1
        && s.chars().next().is_some_and(|c| c.is_ascii_uppercase())
        && s.chars()
            .all(|c| c.is_ascii_uppercase() || c.is_ascii_digit() || c == '_')
}
