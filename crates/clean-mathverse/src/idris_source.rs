// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structured importer for Idris2 `.idr` source files.
//!
//! Idris2 surface declarations are line-oriented `name : type` signatures.
//! Idris is layout/indentation sensitive, so this importer only takes
//! signatures that begin at **column 0** (not indented): a column-0 `name :
//! type` is a top-level signature, whereas an indented `name : type` is a
//! `where`-block local / record field / type-of-a-binder that we must NOT
//! lift to the top level. It also recognises the head of a `data <Name> :
//! <type> where` declaration (the `<Name> : <type>` part).
//!
//! Each signature's `type` string is parsed into a real structural
//! [`FlatExpr`] tree and written to one shard per directory via
//! [`write_idris_shard`]. It mirrors the Agda `.agda` importer
//! ([`crate::agda_source`]): every header is tagged `SourceSystem::Idris2`,
//! `ImportConfidence::Unverified`, and `AXIOMATIZED`, with `value_idx =
//! NO_VALUE` because Idris source carries no proof term we reconstruct here.
//!
//! Like the Agda importer, this is a Level-0/1 **data import**, not a
//! verified elaboration. A signature whose type cannot be parsed into a
//! real tree is **skipped** — never replaced with a `FlatExpr::sort(0)`
//! placeholder (the `structured_importers_refuse_stubs` invariant).

use crate::shard::ShardWriter;
use crate::types::{
    AxiomProfile, ContentDomain, DeclKind, ImportConfidence, MathverseConstantHeader, SourceSystem,
    NO_VALUE,
};

/// A top-level Idris2 signature: `name : type_repr`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IdrisDecl {
    /// The declared name (the leading token before the top-level `:`,
    /// after stripping any visibility/totality modifier prefix).
    pub name: String,
    /// The raw type text following the top-level `:`, with continuation
    /// lines flattened to single spaces.
    pub type_repr: String,
}

/// Function/totality/visibility modifiers that may precede a name on a
/// signature line (`public export f : T`, `total foo : T`).
const MODIFIERS: &[&str] = &[
    "public", "export", "private", "total", "partial", "covering", "%default",
];

/// Parse the top-level `name : type` signatures of an Idris2 source file.
///
/// What is handled:
///   * line comments (`-- …`), block comments (`{- … -}`, nestable), and
///     `||| …` docstring lines (stripped),
///   * `module` / `import` / `%`-pragma lines and operator-fixity lines
///     (`infixl` / `infixr` / `infix` / `prefix`) are skipped,
///   * visibility/totality modifier prefixes (`public export`, `export`,
///     `private`, `total`, `partial`, `covering`) before the name,
///   * `data <Name> : <type> where` declarations — the `<Name> : <type>`
///     head is taken,
///   * multi-line type signatures: a column-0 signature whose type
///     continues on following indented lines.
///
/// Layout rule: a `name : type` signature is taken **only** when it begins
/// at column 0. An indented `name : type` is a `where`-block local, a
/// record field, or a binder type, and is skipped — we never lift it to the
/// top level.
///
/// Be conservative: anything not confidently a top-level signature is
/// skipped. We never fabricate a declaration.
pub fn parse_idris_file(content: &str, _filename: &str) -> Vec<IdrisDecl> {
    let logical = strip_comments(content);
    let lines: Vec<&str> = logical.lines().collect();
    let mut decls = Vec::new();
    let mut i = 0usize;
    while i < lines.len() {
        let line = lines[i];
        if line.trim().is_empty() {
            i += 1;
            continue;
        }
        // Layout rule: only column-0 lines can begin a top-level signature.
        // An indented line is a where-block local / field / clause body and
        // is never a top-level declaration head.
        if leading_ws(line) != 0 {
            i += 1;
            continue;
        }
        let trimmed = line.trim_start();
        // Skip keyword / structural lines that are never plain signatures,
        // EXCEPT `data …`/`record …` which carry a `<Name> : <type>` head.
        if is_skippable_line(trimmed) {
            i += 1;
            continue;
        }
        // `data Name : type where` / `record Name : type where`: take the
        // `Name : type` head (strip the leading `data`/`record` keyword and
        // any trailing `where`).
        let effective = strip_data_head(trimmed).unwrap_or(trimmed);
        // Strip leading visibility/totality modifiers (`public export f`).
        let effective = strip_modifiers(effective);
        // A top-level signature begins with a name token followed by a
        // top-level `:` (not `:=`, not `::`).
        let Some((name, type_head)) = split_name_and_type(effective) else {
            i += 1;
            continue;
        };
        // A head ending in a `where` keyword opens a block (`data … where`,
        // `… : T where` GADT/local-block): the type is complete on this
        // line, and everything indented under it is a member, not a type
        // continuation.
        let opens_block = ends_with_where(type_head);
        // Collect continuation lines: subsequent lines indented strictly
        // more than column 0 that are not blank, a new declaration, a
        // nested signature, or a clause body.
        let mut type_parts = vec![strip_trailing_where(type_head.trim()).to_owned()];
        let mut j = i + 1;
        if !opens_block {
            while j < lines.len() {
                let cont = lines[j];
                if cont.trim().is_empty() {
                    break;
                }
                // A continuation must be indented (column > 0); a column-0
                // line starts a new declaration.
                if leading_ws(cont) == 0 {
                    break;
                }
                let cont_trimmed = cont.trim_start();
                if is_skippable_line(cont_trimmed) {
                    break;
                }
                // A continuation that is itself a `name : type` signature
                // (has its own top-level colon) or a definition clause
                // (`f x = …`) ends the type.
                if find_top_level_colon(cont_trimmed).is_some() || looks_like_clause(cont_trimmed) {
                    break;
                }
                type_parts.push(strip_trailing_where(cont_trimmed.trim()).to_owned());
                j += 1;
            }
        }
        let type_repr = normalize_ws(&type_parts.join(" "));
        if !name.is_empty() && !type_repr.is_empty() {
            decls.push(IdrisDecl { name, type_repr });
        }
        i = j.max(i + 1);
    }
    decls
}

/// Write parsed Idris declarations to a shard.
///
/// For each decl the `type_repr` string is parsed into a real `FlatExpr`
/// tree via [`parse_idris_type`]. A decl whose type fails to parse is
/// **skipped** — never replaced with a `sort(0)` placeholder. This is the
/// import-time guarantee that the resulting shard satisfies
/// `expr_count > constant_count`.
///
/// Every header carries `value_idx = NO_VALUE` (Idris source has no proof
/// term we reconstruct), `ImportConfidence::Unverified`, and `AXIOMATIZED`.
///
/// Returns the number of declarations actually written.
pub fn write_idris_shard(decls: &[IdrisDecl], writer: &mut ShardWriter) -> usize {
    let mut written = 0usize;
    for decl in decls {
        let Some(type_idx) = parse_idris_type(&decl.type_repr, writer) else {
            // Parse failure: skip rather than fall back to sort(0).
            continue;
        };
        let name_idx = writer.add_string(&decl.name);
        writer.add_constant(MathverseConstantHeader {
            name_idx,
            type_idx,
            value_idx: NO_VALUE,
            source_system: SourceSystem::Idris2 as u8,
            import_confidence: ImportConfidence::Unverified as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: DeclKind::Axiom as u8,
            axiom_profile: AxiomProfile::AXIOMATIZED,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        });
        written += 1;
    }
    written
}

/// Strip Idris comments (line `-- …`, nestable block `{- … -}`, and `|||`
/// docstring lines), replacing them with whitespace so column/line
/// structure is preserved.
fn strip_comments(content: &str) -> String {
    let chars: Vec<char> = content.chars().collect();
    let mut out = String::with_capacity(content.len());
    let mut i = 0usize;
    let mut block_depth = 0usize;
    let mut in_string = false;
    let mut escaped = false;
    while i < chars.len() {
        let ch = chars[i];
        let next = chars.get(i + 1).copied();
        if block_depth > 0 {
            if ch == '{' && next == Some('-') {
                block_depth += 1;
                out.push(' ');
                out.push(' ');
                i += 2;
                continue;
            }
            if ch == '-' && next == Some('}') {
                block_depth -= 1;
                out.push(' ');
                out.push(' ');
                i += 2;
                continue;
            }
            out.push(if ch == '\n' { '\n' } else { ' ' });
            i += 1;
            continue;
        }
        if in_string {
            out.push(ch);
            if escaped {
                escaped = false;
            } else if ch == '\\' {
                escaped = true;
            } else if ch == '"' {
                in_string = false;
            }
            i += 1;
            continue;
        }
        // Block comment start.
        if ch == '{' && next == Some('-') {
            block_depth = 1;
            out.push(' ');
            out.push(' ');
            i += 2;
            continue;
        }
        // `|||` documentation comment: a line that, after leading
        // whitespace, begins with `|||`. Consume to end of line.
        if ch == '|' && next == Some('|') && chars.get(i + 2) == Some(&'|') && at_line_start(&out) {
            while i < chars.len() && chars[i] != '\n' {
                out.push(' ');
                i += 1;
            }
            continue;
        }
        // Line comment: `--` not part of a longer operator-dash run.
        if ch == '-' && next == Some('-') && !is_dash_run_operator(&chars, i) {
            while i < chars.len() && chars[i] != '\n' {
                out.push(' ');
                i += 1;
            }
            continue;
        }
        if ch == '"' {
            in_string = true;
            out.push(ch);
            i += 1;
            continue;
        }
        out.push(ch);
        i += 1;
    }
    out
}

/// True when everything emitted so far on the current (last) line is
/// whitespace — i.e. the cursor is at the logical start of a line.
fn at_line_start(out: &str) -> bool {
    out.rsplit('\n')
        .next()
        .map(|seg| seg.chars().all(|c| c.is_whitespace()))
        .unwrap_or(true)
}

/// Idris's line-comment rule: `--` opens a comment unless it is immediately
/// followed by another operator-symbol character (`-->`, `--|` etc. are
/// legal operator tokens). We approximate: a dash run is a comment iff the
/// character after the final dash is not an operator-continuation symbol.
fn is_dash_run_operator(chars: &[char], start: usize) -> bool {
    let mut k = start;
    while k < chars.len() && chars[k] == '-' {
        k += 1;
    }
    matches!(chars.get(k), Some(c) if is_op_symbol(*c))
}

fn is_op_symbol(ch: char) -> bool {
    matches!(ch, '!'..='/' | ':'..='@' | '^' | '|' | '~') && !matches!(ch, '(' | ')' | ';' | ',')
}

/// True for lines that are keywords / structural, never a plain signature.
fn is_skippable_line(trimmed: &str) -> bool {
    // `%`-pragmas (`%default total`, `%hint`, `%foreign`, …).
    if trimmed.starts_with('%') {
        return true;
    }
    for kw in [
        "module",
        "import",
        "namespace",
        "infix",
        "infixl",
        "infixr",
        "prefix",
        "syntax",
        "using",
        "mutual",
        "parameters",
        "where",
        "interface",
        "implementation",
    ] {
        if matches_keyword(trimmed, kw) {
            return true;
        }
    }
    false
}

/// `kw` appears as a leading whole word (followed by whitespace or EOL).
fn matches_keyword(text: &str, kw: &str) -> bool {
    match text.strip_prefix(kw) {
        Some(rest) => rest.is_empty() || rest.starts_with(|c: char| c.is_whitespace()),
        None => false,
    }
}

/// If `trimmed` is a `data Name : type [where]` or `record Name : type
/// [where]` declaration, return the `Name : type` head (with the leading
/// keyword stripped). The trailing `where` is stripped later. Returns
/// `None` for the GADT-less / equational forms `data Name where`,
/// `data Name = …` and `record Name params where` that have no top-level
/// `:` head we can parse.
fn strip_data_head(trimmed: &str) -> Option<&str> {
    for kw in ["data", "record"] {
        if let Some(rest) = trimmed.strip_prefix(kw) {
            if rest.starts_with(|c: char| c.is_whitespace()) {
                let head = rest.trim_start();
                // Only a head that actually carries a top-level `:` is a
                // typed (GADT-style) declaration head we can parse.
                if find_top_level_colon(head).is_some() {
                    return Some(head);
                }
                return None;
            }
        }
    }
    None
}

/// Strip a leading run of visibility/totality modifier keywords.
fn strip_modifiers(mut text: &str) -> &str {
    loop {
        let t = text.trim_start();
        let mut advanced = false;
        for m in MODIFIERS {
            if let Some(rest) = t.strip_prefix(m) {
                if rest.is_empty() || rest.starts_with(|c: char| c.is_whitespace()) {
                    text = rest;
                    advanced = true;
                    break;
                }
            }
        }
        if !advanced {
            return t;
        }
    }
}

/// True when `text` ends with a whole-word `where` keyword (a block
/// opener), e.g. `data Foo : Type where`.
fn ends_with_where(text: &str) -> bool {
    let t = text.trim_end();
    match t.strip_suffix("where") {
        Some(stripped) => stripped.is_empty() || stripped.ends_with(|c: char| c.is_whitespace()),
        None => false,
    }
}

/// Remove a trailing ` where` keyword (used by `data … where`) from a type
/// fragment so it does not leak into the type expression.
fn strip_trailing_where(text: &str) -> &str {
    let t = text.trim_end();
    if let Some(stripped) = t.strip_suffix("where") {
        // Ensure it was a whole word (`… where`, not `…somewhere`).
        if stripped.is_empty() || stripped.ends_with(|c: char| c.is_whitespace()) {
            return stripped.trim_end();
        }
    }
    t
}

/// Heuristic: a line that looks like an equational definition clause
/// (`f x y = …`) rather than a continuation of a type. We treat a line
/// containing a top-level `=` (not `==`, `=>`, `<=`, `>=`) before any
/// top-level `:` as a clause.
fn looks_like_clause(text: &str) -> bool {
    let colon = find_top_level_colon(text);
    let eq = find_top_level_define_eq(text);
    match (eq, colon) {
        (Some(e), Some(c)) => e < c,
        (Some(_), None) => true,
        _ => false,
    }
}

/// Find a top-level standalone `=` (definition), skipping `==`, `=>`, `<=`,
/// `>=`, `/=`, and bracketed regions.
fn find_top_level_define_eq(text: &str) -> Option<usize> {
    let mut paren = 0i32;
    let mut brace = 0i32;
    let mut bracket = 0i32;
    let mut in_string = false;
    let mut escaped = false;
    let chars: Vec<(usize, char)> = text.char_indices().collect();
    let mut i = 0usize;
    while i < chars.len() {
        let (idx, ch) = chars[i];
        if in_string {
            if escaped {
                escaped = false;
            } else if ch == '\\' {
                escaped = true;
            } else if ch == '"' {
                in_string = false;
            }
            i += 1;
            continue;
        }
        match ch {
            '"' => in_string = true,
            '(' => paren += 1,
            ')' if paren > 0 => paren -= 1,
            '{' => brace += 1,
            '}' if brace > 0 => brace -= 1,
            '[' => bracket += 1,
            ']' if bracket > 0 => bracket -= 1,
            '=' if paren == 0 && brace == 0 && bracket == 0 => {
                let next = chars.get(i + 1).map(|(_, c)| *c);
                let prev = i.checked_sub(1).and_then(|p| chars.get(p)).map(|(_, c)| *c);
                if next != Some('=')
                    && next != Some('>')
                    && prev != Some('=')
                    && prev != Some('<')
                    && prev != Some('>')
                    && prev != Some('/')
                    && prev != Some(':')
                {
                    return Some(idx);
                }
            }
            _ => {}
        }
        i += 1;
    }
    None
}

/// Split a line into `(name, type_head)` at its first top-level `:`,
/// where `name` is the first whitespace-delimited token before the colon.
/// Idris allows a list `f, g : T` (or `f g : T`) declaring several names
/// with the same type; we take the first as the representative.
///
/// Returns `None` when there is no top-level `:` (e.g. a clause `f x = …`),
/// or when the colon is part of `:=`/`::` or sits inside brackets.
fn split_name_and_type(line: &str) -> Option<(String, &str)> {
    let colon = find_top_level_colon(line)?;
    let name_part = line[..colon].trim();
    let type_part = &line[colon + 1..];
    if name_part.is_empty() || type_part.trim().is_empty() {
        return None;
    }
    // The name segment must be a plain list of name tokens (allowing `,`
    // separators), with no `=`, `->`, `(`, etc. at top level; otherwise
    // this is not a signature line but some other construct.
    if name_part.contains('=') || name_part.contains("->") || name_part.contains('\u{2192}') {
        return None;
    }
    let first = name_part
        .split(|c: char| c.is_whitespace() || c == ',')
        .find(|t| !t.is_empty())?;
    if !is_valid_name(first) {
        return None;
    }
    Some((first.to_owned(), type_part))
}

/// A declared name must contain at least one identifier/operator character
/// and must not be lone bracket punctuation.
fn is_valid_name(tok: &str) -> bool {
    if tok.is_empty() {
        return false;
    }
    if tok
        .chars()
        .all(|c| matches!(c, '(' | ')' | '{' | '}' | '[' | ']' | ',' | ';'))
    {
        return false;
    }
    true
}

/// Find the first top-level `:` (depth-0, not `:=`, not `::`) in `text`.
fn find_top_level_colon(text: &str) -> Option<usize> {
    let mut paren = 0i32;
    let mut brace = 0i32;
    let mut bracket = 0i32;
    let mut in_string = false;
    let mut escaped = false;
    let chars: Vec<(usize, char)> = text.char_indices().collect();
    let mut i = 0usize;
    while i < chars.len() {
        let (idx, ch) = chars[i];
        if in_string {
            if escaped {
                escaped = false;
            } else if ch == '\\' {
                escaped = true;
            } else if ch == '"' {
                in_string = false;
            }
            i += 1;
            continue;
        }
        match ch {
            '"' => in_string = true,
            '(' => paren += 1,
            ')' if paren > 0 => paren -= 1,
            '{' => brace += 1,
            '}' if brace > 0 => brace -= 1,
            '[' => bracket += 1,
            ']' if bracket > 0 => bracket -= 1,
            ':' if paren == 0 && brace == 0 && bracket == 0 => {
                let next = chars.get(i + 1).map(|(_, c)| *c);
                let prev = i.checked_sub(1).and_then(|p| chars.get(p)).map(|(_, c)| *c);
                if next != Some('=') && next != Some(':') && prev != Some(':') {
                    return Some(idx);
                }
            }
            _ => {}
        }
        i += 1;
    }
    None
}

fn leading_ws(line: &str) -> usize {
    line.chars().take_while(|c| c.is_whitespace()).count()
}

fn normalize_ws(text: &str) -> String {
    text.split_whitespace().collect::<Vec<_>>().join(" ")
}

// ---------------------------------------------------------------------------
// Idris type-expression parser → FlatExpr tree.
//
// Mirrors the Agda type parser: a small recursive-descent parser over a
// token stream producing Pi / Const / App / BVar / Sort nodes. It is
// deliberately conservative — anything it does not understand makes it
// return `None`, and the caller skips the declaration (never a sort(0)
// stub).
// ---------------------------------------------------------------------------

use clean_kernel::flat::FlatExpr;

const NO_LEVELS: u32 = u32::MAX;
const BINDER_DEFAULT: u8 = 0;
const BINDER_IMPLICIT: u8 = 1;
const BINDER_INST_IMPLICIT: u8 = 3;
const SORT_PROP: u32 = 0;
const SORT_TYPE: u32 = 1;

#[derive(Debug, Clone, PartialEq, Eq)]
enum Tok {
    Ident(String),
    Nat(u64),
    LParen,
    RParen,
    LBrace,
    RBrace,
    Arrow,
    Comma,
    Colon,
    Forall, // `forall` / `∀`
    Underscore,
}

fn lex(src: &str) -> Vec<Tok> {
    let chars: Vec<char> = src.chars().collect();
    let mut out = Vec::new();
    let mut i = 0usize;
    while i < chars.len() {
        let ch = chars[i];
        if ch.is_whitespace() {
            i += 1;
            continue;
        }
        // Arrows: ASCII `->` and Unicode `→`.
        if ch == '-' && chars.get(i + 1) == Some(&'>') {
            out.push(Tok::Arrow);
            i += 2;
            continue;
        }
        if ch == '\u{2192}' {
            // →
            out.push(Tok::Arrow);
            i += 1;
            continue;
        }
        // `=>` (constraint / implicit arrow) — treat as a plain arrow so
        // `Ord a => a -> a` reads as a Pi chain.
        if ch == '=' && chars.get(i + 1) == Some(&'>') {
            out.push(Tok::Arrow);
            i += 2;
            continue;
        }
        if ch == '\u{21d2}' {
            // ⇒
            out.push(Tok::Arrow);
            i += 1;
            continue;
        }
        // `:=` is not valid in a type expr — stop defensively.
        if ch == ':' && chars.get(i + 1) == Some(&'=') {
            break;
        }
        match ch {
            '(' => {
                out.push(Tok::LParen);
                i += 1;
                continue;
            }
            ')' => {
                out.push(Tok::RParen);
                i += 1;
                continue;
            }
            '{' => {
                out.push(Tok::LBrace);
                i += 1;
                continue;
            }
            '}' => {
                out.push(Tok::RBrace);
                i += 1;
                continue;
            }
            ',' => {
                out.push(Tok::Comma);
                i += 1;
                continue;
            }
            ':' => {
                out.push(Tok::Colon);
                i += 1;
                continue;
            }
            '\u{2200}' => {
                // ∀
                out.push(Tok::Forall);
                i += 1;
                continue;
            }
            _ => {}
        }
        if ch.is_ascii_digit() {
            let start = i;
            while i < chars.len() && chars[i].is_ascii_digit() {
                i += 1;
            }
            let s: String = chars[start..i].iter().collect();
            match s.parse::<u64>() {
                Ok(n) => out.push(Tok::Nat(n)),
                Err(_) => return out, // overflow: bail, caller skips
            }
            continue;
        }
        // `λ` (U+03BB) and ASCII `\` introduce a lambda abstraction, which
        // is a *term*, not a type former. Bail so the caller skips.
        if ch == '\u{3bb}' || ch == '\\' {
            return out;
        }
        if is_ident_start(ch) {
            let start = i;
            while i < chars.len() && is_ident_continue(chars[i]) {
                i += 1;
            }
            let id: String = chars[start..i].iter().collect();
            // Reserved Idris keywords that cannot head a plain type
            // expression — bail rather than treat them as identifiers.
            if matches!(
                id.as_str(),
                "let"
                    | "in"
                    | "where"
                    | "with"
                    | "record"
                    | "data"
                    | "do"
                    | "case"
                    | "of"
                    | "rewrite"
                    | "if"
                    | "then"
                    | "else"
            ) {
                return out;
            }
            if id == "forall" {
                out.push(Tok::Forall);
            } else if id == "_" {
                out.push(Tok::Underscore);
            } else {
                out.push(Tok::Ident(id));
            }
            continue;
        }
        // Unknown character (e.g. a stray operator glyph) — cannot parse
        // faithfully. Return what we have; a premature/incomplete end is a
        // failure in `parse_idris_type`'s fully-consumed check.
        return out;
    }
    out
}

fn is_ident_start(ch: char) -> bool {
    ch.is_alphabetic() || ch == '_'
}

/// Idris identifiers: alphanumerics, `_`, `'`, `.` (qualified names).
fn is_ident_continue(ch: char) -> bool {
    ch.is_alphanumeric() || matches!(ch, '_' | '\'' | '.')
}

/// Recognise an Idris sort atom: `Type`, `Type0`, or `Type` with a level
/// suffix. Idris's universe of types is `Type`; `Type0`..`TypeN` index it.
/// Anything else (e.g. `Typeable`) is a user constant, not a sort.
fn is_sort_atom(name: &str) -> bool {
    if name == "Type" {
        return true;
    }
    if let Some(rest) = name.strip_prefix("Type") {
        return !rest.is_empty() && rest.chars().all(|c| c.is_ascii_digit());
    }
    false
}

struct Parser<'w> {
    toks: Vec<Tok>,
    pos: usize,
    writer: &'w mut ShardWriter,
    bound: Vec<String>,
    expr_budget: u32,
}

impl<'w> Parser<'w> {
    fn new(toks: Vec<Tok>, writer: &'w mut ShardWriter) -> Self {
        Self {
            toks,
            pos: 0,
            writer,
            bound: Vec::new(),
            expr_budget: 4096,
        }
    }
    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.pos)
    }
    fn bump(&mut self) -> Option<Tok> {
        let t = self.toks.get(self.pos).cloned()?;
        self.pos += 1;
        Some(t)
    }
    fn eat(&mut self, want: &Tok) -> bool {
        if self.peek() == Some(want) {
            self.pos += 1;
            true
        } else {
            false
        }
    }
    fn add(&mut self, e: FlatExpr) -> Option<u32> {
        if self.expr_budget == 0 {
            return None;
        }
        self.expr_budget -= 1;
        Some(self.writer.add_expr(e))
    }

    fn parse_type(&mut self) -> Option<u32> {
        if matches!(self.peek(), Some(Tok::Forall)) {
            self.bump();
            self.parse_forall_chain()
        } else {
            self.parse_arrow()
        }
    }

    /// After `forall`/`∀`, parse one or more binders followed by a `.` or
    /// `→`/`,` separator, then the body. Idris writes `forall a . body`;
    /// the `.` is lexed as part of an identifier-with-dot, so we accept the
    /// `,`/`→` separators an Agda-style chain uses and also a bare list of
    /// untyped names terminated by an arrow/comma (which we cannot type, so
    /// bail rather than fabricate).
    fn parse_forall_chain(&mut self) -> Option<u32> {
        let mut binders: Vec<(u8, u32)> = Vec::new();
        let mut pushed = 0usize;
        loop {
            if matches!(self.peek(), Some(Tok::Comma) | Some(Tok::Arrow)) {
                self.bump();
                break;
            }
            if self.peek().is_none() {
                self.unwind(pushed);
                return None;
            }
            let group = match self.parse_binder_group(true) {
                Some(g) => g,
                None => {
                    self.unwind(pushed);
                    return None;
                }
            };
            for (name, binfo, ty_idx) in group {
                self.bound.push(name);
                pushed += 1;
                binders.push((binfo, ty_idx));
            }
        }
        let body = match self.parse_type() {
            Some(b) => b,
            None => {
                self.unwind(pushed);
                return None;
            }
        };
        let mut acc = body;
        for (binfo, ty_idx) in binders.iter().rev() {
            acc = self.add(FlatExpr::pi(*binfo, *ty_idx, acc))?;
        }
        self.unwind(pushed);
        Some(acc)
    }

    fn unwind(&mut self, n: usize) {
        for _ in 0..n {
            self.bound.pop();
        }
    }

    /// Parse one binder group: `(x y : T)` or `{x : T}` (implicit). For an
    /// untyped binder (`{A}` / a bare name in a `forall`) we cannot
    /// reconstruct the type faithfully, so we bail rather than fabricate.
    fn parse_binder_group(&mut self, _allow_untyped: bool) -> Option<Vec<(String, u8, u32)>> {
        let (close, binfo) = match self.peek() {
            Some(Tok::LParen) => (Some(Tok::RParen), BINDER_DEFAULT),
            Some(Tok::LBrace) => (Some(Tok::RBrace), BINDER_IMPLICIT),
            _ => return None,
        };
        self.bump(); // opening bracket
                     // Idris implicit binders may carry a multiplicity / `auto` keyword
                     // we don't model; if the group is not a plain `names : T`, bail.
        let mut names = Vec::new();
        while matches!(self.peek(), Some(Tok::Ident(_)) | Some(Tok::Underscore)) {
            names.push(self.expect_ident()?);
        }
        if names.is_empty() {
            return None;
        }
        let ty = if matches!(self.peek(), Some(Tok::Colon)) {
            self.bump();
            self.parse_type()?
        } else {
            // Untyped binder: no annotation to reconstruct. Bail.
            return None;
        };
        // Auto/instance implicit `{auto p : T}` would have consumed `auto`
        // as a name above; the resulting binder is still a Pi, which is an
        // acceptable Level-0 approximation. Mark single-name brace binders
        // tagged with a constraint-y close as inst-implicit is out of scope;
        // keep `binfo` as parsed.
        let _ = BINDER_INST_IMPLICIT;
        if let Some(close) = close.as_ref() {
            if !self.eat(close) {
                return None;
            }
        }
        Some(names.into_iter().map(|n| (n, binfo, ty)).collect())
    }

    fn expect_ident(&mut self) -> Option<String> {
        match self.bump()? {
            Tok::Ident(s) => Some(s),
            Tok::Underscore => Some("_".into()),
            _ => None,
        }
    }

    /// `arrow := app (→ arrow)?` — right-associative. Also handles a
    /// leading bracketed dependent binder Pi such as `(A : Type) → A → A`
    /// and `{A : Type} → A → A`.
    fn parse_arrow(&mut self) -> Option<u32> {
        // A bracketed group is a binder Pi only when it carries a `: T`
        // annotation (`(x : T) → …` / `{x : T} → …`); a bare `(A → B)` is a
        // parenthesised atom handled by `parse_app`.
        if matches!(self.peek(), Some(Tok::LBrace) | Some(Tok::LParen))
            && self.looks_like_binder_group()
        {
            let group = self.parse_binder_group(false)?;
            if !self.eat(&Tok::Arrow) {
                return None;
            }
            let binfos_tys: Vec<(u8, u32)> = group.iter().map(|(_, b, t)| (*b, *t)).collect();
            let n = group.len();
            for (name, _, _) in &group {
                self.bound.push(name.clone());
            }
            let body = self.parse_type();
            self.unwind(n);
            let body = body?;
            let mut acc = body;
            for (binfo, ty) in binfos_tys.iter().rev() {
                acc = self.add(FlatExpr::pi(*binfo, *ty, acc))?;
            }
            return Some(acc);
        }
        let lhs = self.parse_app()?;
        if !self.eat(&Tok::Arrow) {
            return Some(lhs);
        }
        // `A → B` ≡ `(_ : A) → B`. Push an anonymous binder so de Bruijn
        // indices in `B` account for the new binding level.
        self.bound.push("_".into());
        let rhs = self.parse_type();
        self.bound.pop();
        let rhs = rhs?;
        self.add(FlatExpr::pi(BINDER_DEFAULT, lhs, rhs))
    }

    /// Lookahead: does the bracketed group at the cursor contain a
    /// top-level `:` before its matching close? Only then is it a binder
    /// (`(x : T)`); otherwise it is a parenthesised type atom.
    fn looks_like_binder_group(&self) -> bool {
        match self.peek() {
            // Implicit `{…}` brackets are always binder positions in a type
            // expression — but only if they carry a `: T` annotation.
            Some(Tok::LBrace) => self.bracket_has_top_colon(&Tok::LBrace, &Tok::RBrace),
            Some(Tok::LParen) => self.bracket_has_top_colon(&Tok::LParen, &Tok::RParen),
            _ => false,
        }
    }

    fn bracket_has_top_colon(&self, open: &Tok, close: &Tok) -> bool {
        let mut depth = 0i32;
        let mut k = self.pos;
        while let Some(t) = self.toks.get(k) {
            if t == open {
                depth += 1;
            } else if t == close {
                depth -= 1;
                if depth == 0 {
                    return false;
                }
            } else if depth == 1 && matches!(t, Tok::Colon) {
                return true;
            }
            k += 1;
        }
        false
    }

    /// Left-associative application: `f a b` ≡ `((f a) b)`.
    fn parse_app(&mut self) -> Option<u32> {
        let mut head = self.parse_atom()?;
        while matches!(
            self.peek(),
            Some(Tok::Ident(_) | Tok::Nat(_) | Tok::Underscore | Tok::LParen)
        ) {
            let arg = self.parse_atom()?;
            head = self.add(FlatExpr::app(head, arg))?;
        }
        Some(head)
    }

    fn parse_atom(&mut self) -> Option<u32> {
        match self.peek().cloned()? {
            Tok::LParen => {
                self.bump();
                let inner = self.parse_type()?;
                if !self.eat(&Tok::RParen) {
                    return None;
                }
                Some(inner)
            }
            Tok::Nat(n) => {
                self.bump();
                self.add(FlatExpr::lit_nat(n))
            }
            Tok::Underscore => {
                self.bump();
                self.add(FlatExpr::sort(SORT_PROP))
            }
            Tok::Ident(name) => {
                self.bump();
                self.emit_name(&name)
            }
            _ => None,
        }
    }

    fn emit_name(&mut self, name: &str) -> Option<u32> {
        // Idris universe atom: `Type` / `Type0` / `TypeN` → sort(1).
        // (Universe levels are out of scope for a Level-0 import — a
        // documented surface approximation, not a verified universe.) Only
        // recognised sort shapes become sorts so user names like `Typeable`
        // stay Consts.
        if is_sort_atom(name) {
            return self.add(FlatExpr::sort(SORT_TYPE));
        }
        // Bound variable: innermost binding wins.
        if let Some(pos) = self.bound.iter().rposition(|n| n == name) {
            let depth = self.bound.len() - 1 - pos;
            return self.add(FlatExpr::bvar(depth as u32));
        }
        // Free name → Const reference.
        let name_idx = self.writer.add_string(name);
        self.add(FlatExpr::const_ref(name_idx, NO_LEVELS))
    }
}

/// Parse an Idris type-expression string into `writer`, returning the root
/// expression index. Returns `None` on parse failure or empty input;
/// callers must treat that as "skip this declaration", never as a licence
/// to emit a placeholder. On success the entire token stream must be
/// consumed (a trailing unparsed remainder is a failure).
pub(crate) fn parse_idris_type(src: &str, writer: &mut ShardWriter) -> Option<u32> {
    let toks = lex(src);
    if toks.is_empty() {
        return None;
    }
    let mut p = Parser::new(toks, writer);
    let root = p.parse_type()?;
    if p.pos != p.toks.len() {
        // Unconsumed tokens mean the type contained a construct we do not
        // model (e.g. record syntax, `λ`, with-clauses). Skip it.
        return None;
    }
    Some(root)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn strings(w: &ShardWriter) -> Vec<String> {
        (0..w.string_count())
            .map(|i| w.string_at(i as u32).to_owned())
            .collect()
    }

    #[test]
    fn parse_idris_file_extracts_signatures_skipping_noise_and_locals() {
        let content = "\
module Example

import Data.Nat

||| the polymorphic identity function
id : a -> a
id x = x

-- a line comment
data Foo : Type where
  MkFoo : Foo

const : a -> b -> a
const x y = x
  where
    helper : a -> a
    helper z = z
";
        let decls = parse_idris_file(content, "Example.idr");
        let names: Vec<&str> = decls.iter().map(|d| d.name.as_str()).collect();
        // `id`, the `Foo` data head, and `const` are top-level. The indented
        // `helper` local and `MkFoo` constructor (indented) must be SKIPPED.
        assert_eq!(names, vec!["id", "Foo", "const"]);
        assert_eq!(decls[0].type_repr, "a -> a");
        assert_eq!(decls[1].type_repr, "Type");
        assert!(
            !names.contains(&"helper"),
            "indented where-block local 'helper' must be skipped, got {names:?}"
        );
        assert!(
            !names.contains(&"MkFoo"),
            "indented constructor 'MkFoo' must be skipped, got {names:?}"
        );
    }

    #[test]
    fn modifiers_are_stripped_from_name() {
        let content = "\
public export
foo : Nat -> Nat
foo x = x

total
bar : Nat
bar = 0
";
        let decls = parse_idris_file(content, "Mods.idr");
        // `public export` is on its own line; the signature line is `foo :
        // ...`. Both `foo` and `bar` are taken with their type heads.
        let names: Vec<&str> = decls.iter().map(|d| d.name.as_str()).collect();
        assert!(names.contains(&"foo"), "got {names:?}");
        assert!(names.contains(&"bar"), "got {names:?}");
    }

    #[test]
    fn inline_modifier_prefix_is_stripped() {
        let decls = parse_idris_file("export myFun : a -> a\n", "M.idr");
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].name, "myFun");
        assert_eq!(decls[0].type_repr, "a -> a");
    }

    #[test]
    fn write_idris_shard_emits_real_type_not_litstr_or_sort0() {
        // `id : {a : Type} -> a -> a` must produce a real Pi/BVar tree:
        // multiple FlatExpr nodes, and the binder name `a` must NOT leak
        // into the string table (it should resolve to a BVar).
        let decls = vec![IdrisDecl {
            name: "id".into(),
            type_repr: "{a : Type} -> a -> a".into(),
        }];
        let mut w = ShardWriter::new();
        let written = write_idris_shard(&decls, &mut w);
        assert_eq!(written, 1, "the id signature must be written");
        // Real tree ⇒ more exprs than constants (the no-stub signature).
        assert!(
            w.expr_count() > w.constant_count(),
            "expected expr_count ({}) > constant_count ({})",
            w.expr_count(),
            w.constant_count()
        );
        // Binder name `a` is bound ⇒ must not appear as a free Const string.
        let ss = strings(&w);
        assert!(
            !ss.iter().any(|s| s == "a"),
            "binder name 'a' leaked into strings {ss:?} — implicit binder \
             not parsed as a Pi/BVar"
        );
    }

    #[test]
    fn simple_signature_type_is_not_litstr_or_sort0() {
        // The doc-snippet `id : a -> a` must yield a real type index whose
        // node is neither a LitStr nor sort(0): an arrow builds a Pi.
        let decls = parse_idris_file("id : a -> a\n", "I.idr");
        assert_eq!(decls.len(), 1);
        let mut w = ShardWriter::new();
        let written = write_idris_shard(&decls, &mut w);
        assert_eq!(written, 1);
        // `a -> a`: Const(a) [shared], Pi. At least 2 exprs, more than 1
        // constant.
        assert!(
            w.expr_count() > w.constant_count(),
            "expr_count {} must exceed constant_count {} (no sort(0) stub)",
            w.expr_count(),
            w.constant_count()
        );
        assert!(w.expr_count() >= 2, "arrow must build a real Pi tree");
    }

    #[test]
    fn parse_idris_type_arrow_chain_builds_pis() {
        let mut w = ShardWriter::new();
        let root = parse_idris_type("Nat -> Nat -> Type", &mut w).expect("parse");
        assert!(w.expr_count() >= 3, "expected real tree");
        assert_eq!(root, w.expr_count() as u32 - 1, "root is the outer Pi");
        let ss = strings(&w);
        assert!(ss.iter().any(|s| s == "Nat"), "Nat head missing: {ss:?}");
    }

    #[test]
    fn dependent_pi_resolves_binder_to_bvar() {
        // `(a : Type) -> a -> a`: the two `a` in the body must be BVars, so
        // `a` must NOT appear in the string table.
        let mut w = ShardWriter::new();
        let _ = parse_idris_type("(a : Type) -> a -> a", &mut w).expect("parse");
        let ss = strings(&w);
        assert!(!ss.iter().any(|s| s == "a"), "a leaked as Const: {ss:?}");
    }

    #[test]
    fn constraint_arrow_parses() {
        // `Ord a => a -> a`: the `=>` is treated as an arrow. The constraint
        // `Ord a` becomes an application head; the whole thing is a Pi chain.
        let mut w = ShardWriter::new();
        let _ = parse_idris_type("Ord a => a -> a", &mut w).expect("parse");
        assert!(w.expr_count() >= 3, "expected real tree");
    }

    #[test]
    fn application_nests_left() {
        let mut w = ShardWriter::new();
        let _ = parse_idris_type("Vect n a", &mut w).expect("parse");
        // Const(Vect), Const(n), App, Const(a), App.
        assert!(w.expr_count() >= 4, "expected real app tree");
    }

    #[test]
    fn empty_and_garbage_return_none() {
        let mut w = ShardWriter::new();
        assert!(parse_idris_type("", &mut w).is_none());
        assert!(parse_idris_type("   ", &mut w).is_none());
        // A `\`-lambda term is out of scope; the unknown glyph aborts the
        // lex and leaves an unconsumable remainder ⇒ None (skip, not stub).
        assert!(parse_idris_type("\\x => x", &mut w).is_none());
    }

    #[test]
    fn indented_signature_is_not_a_top_level_decl() {
        // A purely indented `name : type` (no column-0 head) yields nothing.
        let decls = parse_idris_file("  local : Nat -> Nat\n", "L.idr");
        assert!(
            decls.is_empty(),
            "indented signature must not be lifted to top level, got {decls:?}"
        );
    }
}
