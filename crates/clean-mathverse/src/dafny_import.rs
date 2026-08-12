// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structured importer for Dafny.
use crate::error::MathverseResult;
use crate::shard::ShardWriter;
use crate::types::{
    AxiomProfile, ContentDomain, DeclKind as ShardDeclKind, ImportConfidence,
    MathverseConstantHeader, SourceSystem, NO_VALUE,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum DeclKind {
    Method,
    Function,
    Lemma,
    Predicate,
    Datatype,
    Class,
    Trait,
    Module,
}

impl DeclKind {
    /// Map Dafny surface-syntax kind to the shard-level [`ShardDeclKind`].
    /// Lemma → Theorem; Method/Function/Predicate → Definition;
    /// Datatype/Class/Trait → Inductive; Module → Axiom (opaque container).
    fn to_shard(self) -> ShardDeclKind {
        match self {
            Self::Lemma => ShardDeclKind::Theorem,
            Self::Method | Self::Function | Self::Predicate => ShardDeclKind::Definition,
            Self::Datatype | Self::Class | Self::Trait => ShardDeclKind::Inductive,
            Self::Module => ShardDeclKind::Axiom,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct DafnyDeclaration {
    pub name: String,
    pub kind: DeclKind,
    pub type_sig: Option<String>,
    /// Ordered parameter-type strings (the `T` in each `x: T`), as
    /// captured from the `(...)` parameter list. Used to assemble the
    /// declaration's overall function type. Empty for nullary decls and
    /// for kinds that carry no parameter list (datatype/class/...).
    pub param_types: Vec<String>,
    /// The result-type string. For `method ... returns (r: T)` it is
    /// `T`; for `function f(...): T` it is `T`; otherwise `None`.
    pub return_type: Option<String>,
    pub source_file: String,
}
#[derive(Clone, Debug)]
struct Scope {
    name: String,
    body_end: usize,
}

pub(crate) fn parse_dafny_file(content: &str, filename: &str) -> Vec<DafnyDeclaration> {
    let clean = sanitize_content(content);
    let bytes = clean.as_bytes();
    let mut decls = Vec::new();
    let mut scopes = Vec::<Scope>::new();
    let mut i = 0;

    while i < bytes.len() {
        while scopes.last().is_some_and(|scope| i >= scope.body_end) {
            scopes.pop();
        }
        if !is_ident_boundary(bytes, i) {
            i += 1;
            continue;
        }
        if let Some(parsed) = try_parse_decl(content, bytes, i, filename, &scopes) {
            if let Some(scope) = parsed.scope {
                scopes.push(scope);
            }
            decls.push(parsed.decl);
            i = parsed.next_pos.max(i + 1);
            continue;
        }
        i += 1;
    }
    decls
}

/// Write parsed declarations to a shard.
///
/// For each declaration we assemble a real `FlatExpr` type tree as the
/// right-associative arrow from the parameter types to the result type
/// (see [`result_type_for`] for the per-kind result choice) via
/// [`crate::dafny_type_parser`]. A declaration whose type cannot be
/// faithfully parsed — or whose kind has no signature we model — is
/// **skipped**, never replaced with a `sort(0)` placeholder. This keeps
/// the shard's `expr_count > constant_count` and is the import-time
/// guarantee against name-only shards.
///
/// This is a Level-0/1 data import: types are emitted as free `Const`
/// references under their Dafny surface names with
/// [`ImportConfidence::Unverified`] and [`AxiomProfile::AXIOMATIZED`].
/// Nothing here is kernel-verified.
///
/// Returns the number of declarations actually written.
pub(crate) fn write_dafny_shard(
    decls: &[DafnyDeclaration],
    writer: &mut ShardWriter,
) -> MathverseResult<usize> {
    let mut written = 0usize;
    for decl in decls {
        let Some(result) = result_type_for(decl) else {
            // Kind with no signature we faithfully model (datatype,
            // class, trait, module) or a method/function with no
            // declared result type — skip rather than fake.
            continue;
        };
        let Some(type_idx) =
            crate::dafny_type_parser::assemble_decl_type(&decl.param_types, &result, writer)
        else {
            // A parameter or result type we don't model — skip.
            continue;
        };
        let name_idx = writer.add_string(&decl.name);
        let header = MathverseConstantHeader {
            name_idx,
            type_idx,
            value_idx: NO_VALUE,
            source_system: SourceSystem::Dafny as u8,
            import_confidence: ImportConfidence::Unverified as u8,
            content_domain: ContentDomain::Software as u8,
            decl_kind: decl.kind.to_shard() as u8,
            axiom_profile: AxiomProfile::AXIOMATIZED,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        };
        writer.add_constant(header);
        written += 1;
    }
    Ok(written)
}

/// Choose the result-type string used as the codomain of a
/// declaration's assembled arrow type:
///
/// - `Lemma` → `Prop` (the ensures/requires statement is a proposition;
///   its body is out of scope, so we only render `params -> Prop`).
/// - `Predicate` → `bool` (Dafny predicates are boolean-valued).
/// - `Method` / `Function` → the declared `returns` / `:` type, if any.
///   With no declared result type we cannot faithfully render a
///   codomain, so return `None` (the caller skips the decl).
/// - `Datatype` / `Class` / `Trait` / `Module` → `None`: these are
///   type-formers / containers, not `params -> result` signatures we
///   model. Skipped rather than faked.
fn result_type_for(decl: &DafnyDeclaration) -> Option<String> {
    match decl.kind {
        DeclKind::Lemma => Some("Prop".to_string()),
        DeclKind::Predicate => Some(
            decl.return_type
                .clone()
                .unwrap_or_else(|| "bool".to_string()),
        ),
        DeclKind::Method | DeclKind::Function => decl.return_type.clone(),
        DeclKind::Datatype | DeclKind::Class | DeclKind::Trait | DeclKind::Module => None,
    }
}
struct ParsedDecl {
    decl: DafnyDeclaration,
    next_pos: usize,
    scope: Option<Scope>,
}

fn try_parse_decl(
    content: &str,
    clean: &[u8],
    start: usize,
    filename: &str,
    scopes: &[Scope],
) -> Option<ParsedDecl> {
    let mut i = start;
    loop {
        let (_, end) = read_ident(clean, i)?;
        match &clean[i..end] {
            b"ghost" | b"static" => i = skip_ws_and_attrs(clean, end),
            _ => break,
        }
    }

    let (kind, kw_end) = parse_kind(clean, i)?;
    let mut i = skip_ws_and_attrs(clean, kw_end);
    let (name_start, name_end) = read_name(clean, i)?;
    let local_name = content[name_start..name_end].to_string();
    i = skip_ws_and_attrs(clean, name_end);

    let mut parts = Vec::new();
    let mut param_types = Vec::new();
    let mut return_type = None;
    if clean.get(i) == Some(&b'<') {
        let end = consume_balanced(clean, i, b'<', b'>')?;
        parts.push(normalize_fragment(&content[i..=end]));
        i = skip_ws_and_attrs(clean, end + 1);
    }
    if clean.get(i) == Some(&b'(') {
        let end = consume_balanced(clean, i, b'(', b')')?;
        // Inner text excludes the surrounding parens.
        param_types = extract_param_types(&content[i + 1..end]);
        parts.push(normalize_fragment(&content[i..=end]));
        i = end + 1;
    }

    loop {
        i = skip_ws_and_attrs(clean, i);
        if let Some(end) = match_word(clean, i, b"returns") {
            let sig_end = consume_returns_clause(clean, end)?;
            let after_kw = skip_ws_and_attrs(clean, end);
            if return_type.is_none() {
                return_type = extract_returns_type(content, clean, after_kw);
            }
            parts.push(normalize_fragment(&content[i..sig_end]));
            i = sig_end;
        } else if clean.get(i) == Some(&b':') {
            let sig_end = consume_type_clause(clean, i);
            if return_type.is_none() {
                // Skip the ':' itself; the result type is what follows.
                return_type = nonempty_fragment(&content[i + 1..sig_end]);
            }
            parts.push(normalize_fragment(&content[i..sig_end]));
            i = sig_end;
        } else if let Some(end) = match_word(clean, i, b"requires") {
            let sig_end = consume_spec_clause(clean, end);
            parts.push(normalize_fragment(&content[i..sig_end]));
            i = sig_end;
        } else if let Some(end) = match_word(clean, i, b"ensures") {
            let sig_end = consume_spec_clause(clean, end);
            parts.push(normalize_fragment(&content[i..sig_end]));
            i = sig_end;
        } else if let Some(end) = match_word(clean, i, b"decreases") {
            let sig_end = consume_spec_clause(clean, end);
            parts.push(normalize_fragment(&content[i..sig_end]));
            i = sig_end;
        } else {
            break;
        }
    }

    let full_name = qualify_name(scopes, &local_name);
    let body_pos = skip_ws_and_attrs(clean, i);
    let mut scope = None;
    let mut next_pos = body_pos;

    if clean.get(body_pos) == Some(&b'{') {
        let body_end =
            consume_balanced(clean, body_pos, b'{', b'}').unwrap_or(clean.len().saturating_sub(1));
        if is_scope_kind(kind) {
            scope = Some(Scope {
                name: local_name,
                body_end,
            });
            next_pos = body_pos + 1;
        } else {
            next_pos = body_end + 1;
        }
    }

    Some(ParsedDecl {
        decl: DafnyDeclaration {
            name: full_name,
            kind,
            type_sig: (!parts.is_empty()).then(|| parts.join(" ")),
            param_types,
            return_type,
            source_file: filename.to_string(),
        },
        next_pos,
        scope,
    })
}

fn parse_kind(clean: &[u8], i: usize) -> Option<(DeclKind, usize)> {
    let (start, end) = read_ident(clean, i)?;
    let kind = match &clean[start..end] {
        b"method" => DeclKind::Method,
        b"function" => DeclKind::Function,
        b"lemma" => DeclKind::Lemma,
        b"predicate" => DeclKind::Predicate,
        b"datatype" => DeclKind::Datatype,
        b"class" => DeclKind::Class,
        b"trait" => DeclKind::Trait,
        b"module" => DeclKind::Module,
        _ => return None,
    };
    Some((kind, end))
}
fn is_scope_kind(kind: DeclKind) -> bool {
    matches!(
        kind,
        DeclKind::Datatype | DeclKind::Class | DeclKind::Trait | DeclKind::Module
    )
}

fn sanitize_content(content: &str) -> String {
    let src = content.as_bytes();
    let mut out = src.to_vec();
    let mut i = 0;
    while i < out.len() {
        if src[i] == b'/' && i + 1 < out.len() && src[i + 1] == b'/' {
            out[i] = b' ';
            out[i + 1] = b' ';
            i += 2;
            while i < out.len() && src[i] != b'\n' {
                out[i] = b' ';
                i += 1;
            }
        } else if src[i] == b'/' && i + 1 < out.len() && src[i + 1] == b'*' {
            out[i] = b' ';
            out[i + 1] = b' ';
            i += 2;
            while i + 1 < out.len() {
                if src[i] == b'*' && src[i + 1] == b'/' {
                    out[i] = b' ';
                    out[i + 1] = b' ';
                    i += 2;
                    break;
                }
                if src[i] != b'\n' {
                    out[i] = b' ';
                }
                i += 1;
            }
        } else if src[i] == b'"' {
            out[i] = b' ';
            i += 1;
            while i < out.len() {
                if src[i] == b'\\' && i + 1 < out.len() {
                    out[i] = b' ';
                    out[i + 1] = b' ';
                    i += 2;
                    continue;
                }
                let ch = src[i];
                if ch == b'"' {
                    out[i] = b' ';
                    i += 1;
                    break;
                }
                if ch != b'\n' {
                    out[i] = b' ';
                }
                i += 1;
            }
        } else if src[i] == b'\'' {
            out[i] = b' ';
            i += 1;
            while i < out.len() {
                if src[i] == b'\\' && i + 1 < out.len() {
                    out[i] = b' ';
                    out[i + 1] = b' ';
                    i += 2;
                    continue;
                }
                let ch = src[i];
                if ch == b'\'' {
                    out[i] = b' ';
                    i += 1;
                    break;
                }
                if ch != b'\n' {
                    out[i] = b' ';
                }
                i += 1;
            }
        } else {
            i += 1;
        }
    }
    String::from_utf8(out).expect("sanitized Dafny content stays UTF-8")
}
fn consume_returns_clause(clean: &[u8], i: usize) -> Option<usize> {
    let i = skip_ws_and_attrs(clean, i);
    if clean.get(i) == Some(&b'(') {
        Some(consume_balanced(clean, i, b'(', b')')? + 1)
    } else {
        Some(consume_type_clause(clean, i))
    }
}

fn consume_type_clause(clean: &[u8], start: usize) -> usize {
    let mut i = start + usize::from(clean.get(start) == Some(&b':'));
    let mut paren = 0usize;
    let mut bracket = 0usize;
    let mut angle = 0usize;
    while i < clean.len() {
        match clean[i] {
            b'(' => paren += 1,
            b')' if paren > 0 => paren -= 1,
            b'[' => bracket += 1,
            b']' if bracket > 0 => bracket -= 1,
            b'<' => angle += 1,
            b'>' if angle > 0 => angle -= 1,
            _ => {}
        }
        if paren == 0 && bracket == 0 && angle == 0 {
            if matches!(clean[i], b'\n' | b';' | b'{') {
                break;
            }
            let j = skip_inline_ws(clean, i);
            if j > i && next_clause_starts(clean, j) {
                break;
            }
        }
        i += 1;
    }
    i
}

fn consume_spec_clause(clean: &[u8], mut i: usize) -> usize {
    let mut paren = 0usize;
    let mut bracket = 0usize;
    while i < clean.len() {
        match clean[i] {
            b'(' => paren += 1,
            b')' if paren > 0 => paren -= 1,
            b'[' => bracket += 1,
            b']' if bracket > 0 => bracket -= 1,
            _ => {}
        }
        if paren == 0 && bracket == 0 {
            if matches!(clean[i], b'\n' | b';' | b'{') {
                break;
            }
            let j = skip_inline_ws(clean, i);
            if j > i && next_clause_starts(clean, j) {
                break;
            }
        }
        i += 1;
    }
    i
}
fn next_clause_starts(clean: &[u8], i: usize) -> bool {
    match_word(clean, i, b"requires").is_some()
        || match_word(clean, i, b"ensures").is_some()
        || match_word(clean, i, b"decreases").is_some()
        || match_word(clean, i, b"returns").is_some()
}
fn normalize_fragment(fragment: &str) -> String {
    fragment.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// Whitespace-normalize `s`; return `None` if it is empty.
fn nonempty_fragment(s: &str) -> Option<String> {
    let n = normalize_fragment(s);
    (!n.is_empty()).then_some(n)
}

/// Extract the ordered list of parameter-type strings from the inner
/// text of a `(...)` parameter list (parens already stripped).
///
/// Handles `(x: int, y: nat)` and the grouped shorthand
/// `(x, y: int)` (both names share the trailing type). Leading
/// `ghost` / `nameonly` modifiers on a parameter are ignored — they
/// affect the binder, not the type. A run of names that ends without a
/// type binding (which is not valid Dafny in this position) contributes
/// nothing.
fn extract_param_types(inner: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut pending_unnamed = 0usize; // grouped names awaiting a type
    for segment in split_top_level_commas(inner) {
        let seg = segment.trim();
        if seg.is_empty() {
            continue;
        }
        match split_top_level_colon(seg) {
            Some((_names, ty)) => {
                if let Some(ty) = nonempty_fragment(ty) {
                    // The colon-bearing segment plus any pending grouped
                    // names all take this type.
                    for _ in 0..=pending_unnamed {
                        out.push(ty.clone());
                    }
                }
                pending_unnamed = 0;
            }
            None => {
                // A bare name like the `x` in `(x, y: int)` — defer
                // until the next segment supplies the shared type.
                pending_unnamed += 1;
            }
        }
    }
    out
}

/// Extract the result-type string from a `returns` clause. `i` points
/// at the first non-ws byte after the `returns` keyword. The clause is
/// either `returns (r: T)` (single result) — we take `T` — or, in
/// general, `returns (r0: T0, r1: T1)` which we treat as a single
/// tupled result `(T0, T1)` so it can be parsed as a tuple type.
fn extract_returns_type(content: &str, clean: &[u8], i: usize) -> Option<String> {
    if clean.get(i) != Some(&b'(') {
        // `returns T` without parens is unusual; take the type clause.
        let end = consume_type_clause(clean, i);
        return nonempty_fragment(&content[i..end]);
    }
    let end = consume_balanced(clean, i, b'(', b')')?;
    let inner = &content[i + 1..end];
    let mut types = extract_param_types(inner);
    match types.len() {
        0 => None,
        1 => types.pop(),
        _ => Some(format!("({})", types.join(", "))),
    }
}

/// Split `s` on top-level commas (ignoring commas nested inside
/// `()`, `<>`, or `[]`).
fn split_top_level_commas(s: &str) -> Vec<&str> {
    let bytes = s.as_bytes();
    let mut out = Vec::new();
    let (mut paren, mut angle, mut bracket) = (0i32, 0i32, 0i32);
    let mut start = 0usize;
    for (idx, &b) in bytes.iter().enumerate() {
        match b {
            b'(' => paren += 1,
            b')' => paren -= 1,
            b'<' => angle += 1,
            b'>' => angle -= 1,
            b'[' => bracket += 1,
            b']' => bracket -= 1,
            b',' if paren == 0 && angle == 0 && bracket == 0 => {
                out.push(&s[start..idx]);
                start = idx + 1;
            }
            _ => {}
        }
    }
    out.push(&s[start..]);
    out
}

/// Split a `name: type` parameter segment on the first top-level colon.
/// Returns `(names_part, type_part)`, or `None` when there is no
/// top-level colon. Colons nested in `<>`/`()`/`[]` are ignored (Dafny
/// map types use `,` not `:`, but be defensive).
fn split_top_level_colon(seg: &str) -> Option<(&str, &str)> {
    let bytes = seg.as_bytes();
    let (mut paren, mut angle, mut bracket) = (0i32, 0i32, 0i32);
    for (idx, &b) in bytes.iter().enumerate() {
        match b {
            b'(' => paren += 1,
            b')' => paren -= 1,
            b'<' => angle += 1,
            b'>' => angle -= 1,
            b'[' => bracket += 1,
            b']' => bracket -= 1,
            b':' if paren == 0 && angle == 0 && bracket == 0 => {
                return Some((&seg[..idx], &seg[idx + 1..]));
            }
            _ => {}
        }
    }
    None
}
fn qualify_name(scopes: &[Scope], local: &str) -> String {
    if scopes.is_empty() {
        return local.to_string();
    }
    let mut name = String::new();
    for scope in scopes {
        if !name.is_empty() {
            name.push('.');
        }
        name.push_str(&scope.name);
    }
    if !name.is_empty() {
        name.push('.');
    }
    name.push_str(local);
    name
}

fn skip_ws_and_attrs(clean: &[u8], mut i: usize) -> usize {
    loop {
        while i < clean.len() && clean[i].is_ascii_whitespace() {
            i += 1;
        }
        if clean.get(i) == Some(&b'{') && clean.get(i + 1) == Some(&b':') {
            if let Some(end) = consume_balanced(clean, i, b'{', b'}') {
                i = end + 1;
                continue;
            }
        }
        return i;
    }
}
fn skip_inline_ws(clean: &[u8], mut i: usize) -> usize {
    while i < clean.len() && matches!(clean[i], b' ' | b'\t' | b'\r') {
        i += 1;
    }
    i
}

fn consume_balanced(clean: &[u8], start: usize, open: u8, close: u8) -> Option<usize> {
    if clean.get(start) != Some(&open) {
        return None;
    }
    let mut depth = 0usize;
    let mut i = start;
    while i < clean.len() {
        if clean[i] == open {
            depth += 1;
        } else if clean[i] == close {
            depth -= 1;
            if depth == 0 {
                return Some(i);
            }
        }
        i += 1;
    }
    None
}

fn read_name(clean: &[u8], start: usize) -> Option<(usize, usize)> {
    let (_, mut i) = read_ident(clean, start)?;
    while clean.get(i) == Some(&b'.') {
        let (seg_start, seg_end) = read_ident(clean, i + 1)?;
        if seg_start != i + 1 {
            break;
        }
        i = seg_end;
    }
    Some((start, i))
}

fn read_ident(clean: &[u8], start: usize) -> Option<(usize, usize)> {
    if !matches!(clean.get(start), Some(b) if is_ident_start(*b)) {
        return None;
    }
    let mut end = start + 1;
    while end < clean.len() && is_ident_continue(clean[end]) {
        end += 1;
    }
    Some((start, end))
}
fn match_word(clean: &[u8], start: usize, word: &[u8]) -> Option<usize> {
    let end = start.checked_add(word.len())?;
    if clean.get(start..end)? != word {
        return None;
    }
    if start > 0 && is_ident_continue(clean[start - 1]) {
        return None;
    }
    if end < clean.len() && is_ident_continue(clean[end]) {
        return None;
    }
    Some(end)
}
fn is_ident_boundary(clean: &[u8], i: usize) -> bool {
    matches!(clean.get(i), Some(b) if is_ident_start(*b))
        && (i == 0 || !is_ident_continue(clean[i - 1]))
}
fn is_ident_start(b: u8) -> bool {
    b.is_ascii_alphabetic() || b == b'_'
}
fn is_ident_continue(b: u8) -> bool {
    is_ident_start(b) || b.is_ascii_digit()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_dafny_decls_with_scopes_and_specs() {
        let content = "module Sample {\n  ghost method Compute<T>(x: T, ys: seq<int>) returns (r: int)\n    requires |ys| > 0\n    ensures r >= 0\n    decreases |ys|\n  {\n    var s := \"method Fake() returns (z: int) { z := 0; }\";\n    if |ys| > 1 { var tmp := ys[0]; }\n  }\n  static function Max<T>(x: T, y: T): T\n    requires true\n  { x }\n  predicate Valid(x: int)\n    ensures x >= 0\n  { x >= 0 }\n}\nmodule Outer {\n  class Box<T> {\n    lemma Reveal(v: T)\n      ensures true\n    { }\n  }\n  trait Ordered<T> {\n    ghost predicate Less(x: T, y: T)\n      requires true\n    { true }\n  }\n  datatype Option<T> = Some(value: T) | None\n}\n";
        let decls = parse_dafny_file(content, "sample.dfy");
        let names: Vec<_> = decls.iter().map(|d| d.name.as_str()).collect();
        assert_eq!(
            names,
            vec![
                "Sample",
                "Sample.Compute",
                "Sample.Max",
                "Sample.Valid",
                "Outer",
                "Outer.Box",
                "Outer.Box.Reveal",
                "Outer.Ordered",
                "Outer.Ordered.Less",
                "Outer.Option"
            ]
        );
        assert_eq!(decls[1].kind, DeclKind::Method);
        assert_eq!(decls[1].type_sig.as_deref(), Some("<T> (x: T, ys: seq<int>) returns (r: int) requires |ys| > 0 ensures r >= 0 decreases |ys|"));
        assert_eq!(decls[2].kind, DeclKind::Function);
        assert_eq!(
            decls[2].type_sig.as_deref(),
            Some("<T> (x: T, y: T) : T requires true")
        );
        assert_eq!(decls[3].kind, DeclKind::Predicate);
        assert_eq!(decls[5].kind, DeclKind::Class);
        assert_eq!(decls[5].type_sig.as_deref(), Some("<T>"));
        assert_eq!(decls[6].kind, DeclKind::Lemma);
        assert_eq!(decls[6].type_sig.as_deref(), Some("(v: T) ensures true"));
        assert_eq!(decls[8].kind, DeclKind::Predicate);
        assert_eq!(
            decls[8].type_sig.as_deref(),
            Some("(x: T, y: T) requires true")
        );
        assert_eq!(decls[9].kind, DeclKind::Datatype);
        assert_eq!(decls[9].type_sig.as_deref(), Some("<T>"));
    }

    #[test]
    fn test_write_dafny_shard_emits_real_types() {
        // Real importer: each writable declaration produces a genuine
        // FlatExpr type tree, so the shard's expr_count must exceed its
        // constant_count (the structural-fidelity guarantee).
        let content = "module M {\n  method Inc(x: int) returns (y: int)\n    ensures y == x + 1\n  { y := x + 1; }\n  function Id<T>(x: T): T { x }\n}\n";
        let decls = parse_dafny_file(content, "roundtrip.dfy");
        assert!(!decls.is_empty());
        let mut writer = ShardWriter::new();
        let written =
            write_dafny_shard(&decls, &mut writer).expect("real importer must write a shard");
        assert!(written > 0, "expected at least one declaration written");
        assert_eq!(
            writer.constant_count(),
            written,
            "one constant per written decl"
        );
        assert!(
            writer.expr_count() > writer.constant_count(),
            "expr_count ({}) must exceed constant_count ({}) — a real type \
             tree per decl, not one shared placeholder",
            writer.expr_count(),
            writer.constant_count()
        );
    }

    #[test]
    fn test_parse_dafny_captures_param_and_return_types() {
        let content =
            "method M(x: int, y: nat) returns (r: bool)\n  ensures true\n  { r := true; }\n";
        let decls = parse_dafny_file(content, "m.dfy");
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].param_types, vec!["int", "nat"]);
        assert_eq!(decls[0].return_type.as_deref(), Some("bool"));
    }

    #[test]
    fn test_parse_dafny_function_colon_return_type() {
        let content = "function f(x: int): nat { x }\n";
        let decls = parse_dafny_file(content, "f.dfy");
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].param_types, vec!["int"]);
        assert_eq!(decls[0].return_type.as_deref(), Some("nat"));
    }

    #[test]
    fn test_parse_dafny_grouped_param_names_share_type() {
        let content = "function g(x, y: int): int { x }\n";
        let decls = parse_dafny_file(content, "g.dfy");
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].param_types, vec!["int", "int"]);
    }
}
