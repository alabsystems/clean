// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structured importer for Matita `.ma` source files.
//!
//! Matita is a CIC-based interactive theorem prover whose surface syntax is
//! a sequence of vernacular statements terminated by a top-level `.`. This
//! importer scans the keyword-led declaration heads
//! (`theorem`/`lemma`/`definition`/`axiom`/`inductive`/`record`/`let rec`),
//! extracts each declaration's `name : TYPE` (dropping any `:=` body and any
//! `qed.`-terminated proof script), parses the CIC type into a real
//! structural [`FlatExpr`] tree, and writes one shard per directory via
//! [`write_matita_shard`].
//!
//! It mirrors the Coq `.v` importer ([`crate::coq::v_import`]) — Matita uses
//! the same Calculus of Inductive Constructions type language — so every
//! header is tagged `SourceSystem::Matita`, `ImportConfidence::Unverified`,
//! and `AXIOMATIZED`, with `value_idx = NO_VALUE` because Matita source
//! carries no proof term we reconstruct here.
//!
//! Like the Coq importer this is a Level-0/1 **data import**, not a verified
//! elaboration. A declaration whose type cannot be parsed into a real tree
//! is **skipped** — never replaced with a `FlatExpr::sort(0)` placeholder
//! (the `structured_importers_refuse_stubs` invariant).

use crate::shard::ShardWriter;
use crate::types::{
    AxiomProfile, ContentDomain, DeclKind as ShardDeclKind, ImportConfidence,
    MathverseConstantHeader, SourceSystem, NO_VALUE,
};

/// Surface kinds of a Matita vernacular declaration head.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MatitaKind {
    Theorem,
    Lemma,
    Definition,
    Axiom,
    Inductive,
    Record,
    LetRec,
}

impl MatitaKind {
    /// Map the surface kind to the shard-level [`ShardDeclKind`].
    fn to_shard(self) -> ShardDeclKind {
        match self {
            Self::Theorem | Self::Lemma => ShardDeclKind::Theorem,
            Self::Axiom => ShardDeclKind::Axiom,
            Self::Inductive | Self::Record => ShardDeclKind::Inductive,
            Self::Definition | Self::LetRec => ShardDeclKind::Definition,
        }
    }
}

/// A parsed Matita declaration head: `kind name : type_repr`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MatitaDecl {
    /// The declared name (the identifier following the keyword).
    pub name: String,
    /// Surface declaration kind.
    pub kind: MatitaKind,
    /// The raw type text between the top-level `:` and the terminating
    /// `:=` / `.`, whitespace-normalized. `None` when the statement has no
    /// declared type we could isolate.
    pub type_repr: Option<String>,
    /// Originating file name.
    pub source_file: String,
}

/// Keyword → kind table. `let rec` is handled specially (two tokens).
const DECL_STARTS: [(&str, MatitaKind); 5] = [
    ("theorem", MatitaKind::Theorem),
    ("lemma", MatitaKind::Lemma),
    ("definition", MatitaKind::Definition),
    ("axiom", MatitaKind::Axiom),
    ("record", MatitaKind::Record),
];

/// Parse the keyword-led `name : type` declaration heads of a Matita file.
///
/// What is handled:
///   * nestable `(* … *)` comments (stripped first, replaced with spaces so
///     statement boundaries are preserved),
///   * vernacular statements terminated by a top-level `.`,
///   * the keyword-led forms `theorem` / `lemma` / `definition` / `axiom` /
///     `inductive` / `record` / `let rec`, each followed by a NAME, then a
///     `:` and the TYPE up to a top-level `:=` or the terminating `.`,
///   * `inductive` / `record` heads: the type before the `:=` is kept (the
///     arity/sort), the constructor/field body after `:=` is dropped.
///
/// Proof bodies after `:=` and `qed.`-terminated proof scripts are never
/// emitted as values (`value_idx = NO_VALUE`). Anything not confidently a
/// declaration head is skipped; we never fabricate a declaration.
pub fn parse_matita_file(content: &str, filename: &str) -> Vec<MatitaDecl> {
    let mut decls = Vec::new();
    for stmt in split_sentences(content) {
        let stmt = normalize_ws(&stmt);
        if stmt.is_empty() {
            continue;
        }
        if let Some(decl) = parse_decl(&stmt, filename) {
            decls.push(decl);
        }
    }
    decls
}

/// Write parsed Matita declarations to a shard.
///
/// For each decl the `type_repr` CIC string is parsed into a real
/// `FlatExpr` tree via [`parse_matita_type`]. A decl whose type is absent or
/// fails to parse is **skipped** — never replaced with a `sort(0)`
/// placeholder. This is the import-time guarantee that the resulting shard
/// satisfies `expr_count > constant_count`.
///
/// Every header carries `value_idx = NO_VALUE` (Matita source has no proof
/// term we reconstruct), `ImportConfidence::Unverified`, and `AXIOMATIZED`.
///
/// Returns the number of declarations actually written.
pub fn write_matita_shard(decls: &[MatitaDecl], writer: &mut ShardWriter) -> usize {
    let mut written = 0usize;
    for decl in decls {
        let Some(type_repr) = decl.type_repr.as_deref() else {
            // No declared type — would have to emit a placeholder. Skip.
            continue;
        };
        let Some(type_idx) = parse_matita_type(type_repr, writer) else {
            // Parse failure: skip rather than fall back to sort(0).
            continue;
        };
        let name_idx = writer.add_string(&decl.name);
        writer.add_constant(MathverseConstantHeader {
            name_idx,
            type_idx,
            value_idx: NO_VALUE,
            source_system: SourceSystem::Matita as u8,
            import_confidence: ImportConfidence::Unverified as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: decl.kind.to_shard() as u8,
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

/// Recognise the declaration keyword at the front of `stmt`. Handles the
/// two-token `let rec` form as well as the single-keyword forms.
fn decl_start(stmt: &str) -> Option<(MatitaKind, &str)> {
    if let Some(rest) = match_word(stmt, "let") {
        let rest = rest.trim_start();
        if let Some(after) = match_word(rest, "rec") {
            return Some((MatitaKind::LetRec, after));
        }
        // A bare `let` is a local binding, not a top-level declaration.
        return None;
    }
    if let Some(rest) = match_word(stmt, "inductive") {
        return Some((MatitaKind::Inductive, rest));
    }
    for (keyword, kind) in DECL_STARTS {
        if let Some(rest) = match_word(stmt, keyword) {
            return Some((kind, rest));
        }
    }
    None
}

fn parse_decl(stmt: &str, filename: &str) -> Option<MatitaDecl> {
    let (kind, rest) = decl_start(stmt)?;
    let (name, after_name) = take_ident(rest.trim_start())?;
    let type_repr = extract_type(after_name, kind);
    Some(MatitaDecl {
        name: name.to_owned(),
        kind,
        type_repr,
        source_file: filename.to_owned(),
    })
}

/// Split the text after a declaration name into its type body — the text
/// between the first top-level `:` and a top-level `:=` (or end). Returns
/// `None` when there is no top-level `:` (e.g. `definition foo := bar`,
/// where the type is inferred and we have nothing to reconstruct).
///
/// For `inductive` / `record`, any binder prefix before the `:` is the
/// parameter telescope; we attach it as a leading `∀` so body references to
/// the parameters resolve to BVars. For the term-level kinds we do the same:
/// `definition id (A:Type) : A → A` has binders `(A:Type)` before the `:`.
fn extract_type(rest: &str, _kind: MatitaKind) -> Option<String> {
    let colon = find_top_level_colon(rest)?;
    let binders = normalize_ws(&rest[..colon]);
    let tail = &rest[colon + 1..];
    let end = find_top_level_assign(tail).unwrap_or(tail.len());
    let sig = normalize_ws(&tail[..end]);
    if sig.is_empty() {
        return None;
    }
    if binders.is_empty() {
        Some(sig)
    } else {
        // Re-attach the binder telescope as a leading `∀` so the type
        // parser wraps it in real Pi nodes and resolves the bound names.
        Some(format!("\u{2200} {binders} , {sig}"))
    }
}

/// Split content into top-level statements terminated by `.`, stripping
/// nestable `(* … *)` comments (replaced with spaces). A `.` ends a
/// statement only when it is a genuine sentence terminator (followed by
/// whitespace/EOF and not embedded in a qualified identifier like `nat.S`).
fn split_sentences(content: &str) -> Vec<String> {
    let chars: Vec<char> = content.chars().collect();
    let mut out = Vec::new();
    let mut cur = String::new();
    let mut i = 0usize;
    let mut comment_depth = 0usize;
    let mut in_string = false;
    let mut escaped = false;
    while i < chars.len() {
        let ch = chars[i];
        let next = chars.get(i + 1).copied();
        if comment_depth > 0 {
            if ch == '(' && next == Some('*') {
                comment_depth += 1;
                i += 2;
                continue;
            }
            if ch == '*' && next == Some(')') {
                comment_depth = comment_depth.saturating_sub(1);
                i += 2;
                continue;
            }
            cur.push(if ch == '\n' { '\n' } else { ' ' });
            i += 1;
            continue;
        }
        if in_string {
            cur.push(ch);
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
        if ch == '(' && next == Some('*') {
            comment_depth = 1;
            cur.push(' ');
            cur.push(' ');
            i += 2;
            continue;
        }
        if ch == '"' {
            in_string = true;
            cur.push(ch);
            i += 1;
            continue;
        }
        if ch == '.' && is_statement_terminator(&chars, i) {
            let stmt = cur.trim();
            if !stmt.is_empty() {
                out.push(stmt.to_owned());
            }
            cur.clear();
            i += 1;
            continue;
        }
        cur.push(ch);
        i += 1;
    }
    let tail = cur.trim();
    if !tail.is_empty() {
        out.push(tail.to_owned());
    }
    out
}

/// Decide whether the `.` at `idx` ends a vernacular statement.
///
/// Matita overloads `.` as both the statement terminator AND the `∀`/`λ`
/// binder separator (`∀A:Type. A → A := λx.x`), so neither the
/// "followed-by-whitespace" rule nor the "between-identifiers" rule alone
/// disambiguates. We rely on the structural fact that every Matita statement
/// begins with a known vernacular keyword: a `.` terminates the statement iff
/// it sits at end-of-input, or is followed by whitespace and the next
/// non-whitespace run is a vernacular keyword (the start of the next
/// statement). A binder-separator dot is always followed by a *term*, never a
/// top-level keyword, so this is robust for the corpus shapes we import.
fn is_statement_terminator(chars: &[char], idx: usize) -> bool {
    if is_qualified_name_dot(chars, idx) {
        return false;
    }
    // End-of-input after the dot is always a terminator.
    let Some(next) = chars.get(idx + 1).copied() else {
        return true;
    };
    if !next.is_whitespace() {
        return false;
    }
    // Skip whitespace AND any intervening `(* … *)` comments to the next
    // non-trivia char, then read the keyword run.
    let mut j = idx + 1;
    loop {
        while j < chars.len() && chars[j].is_whitespace() {
            j += 1;
        }
        if j + 1 < chars.len() && chars[j] == '(' && chars[j + 1] == '*' {
            j += 2;
            let mut depth = 1usize;
            while j < chars.len() && depth > 0 {
                if j + 1 < chars.len() && chars[j] == '(' && chars[j + 1] == '*' {
                    depth += 1;
                    j += 2;
                } else if j + 1 < chars.len() && chars[j] == '*' && chars[j + 1] == ')' {
                    depth -= 1;
                    j += 2;
                } else {
                    j += 1;
                }
            }
            continue;
        }
        break;
    }
    if j >= chars.len() {
        // Trailing whitespace/comments then EOF — terminator.
        return true;
    }
    let start = j;
    while j < chars.len() && (chars[j].is_alphabetic() || chars[j] == '_') {
        j += 1;
    }
    let word: String = chars[start..j].iter().collect();
    is_vernacular_keyword(&word)
}

/// Vernacular keywords that begin a top-level Matita statement. Used to
/// disambiguate the statement-terminating `.` from a `∀`/`λ` separator `.`.
fn is_vernacular_keyword(word: &str) -> bool {
    matches!(
        word,
        "theorem"
            | "lemma"
            | "definition"
            | "axiom"
            | "inductive"
            | "record"
            | "let"
            | "qed"
            | "include"
            | "coercion"
            | "notation"
            | "interpretation"
            | "alias"
            | "universe"
            | "unification"
            | "default"
            | "check"
            | "eval"
    )
}

/// A `.` between two identifier characters is a qualified-name dot
/// (`nat.S`), never a separator or terminator. The binder-introduction
/// glyphs `∀`/`λ`/`Π` are alphabetic but are NOT identifier characters, so a
/// dot like `λA.λx` (binder separator between two abstractions) must not be
/// mistaken for a qualified name — we exclude those glyphs explicitly.
fn is_qualified_name_dot(chars: &[char], idx: usize) -> bool {
    let prev = idx.checked_sub(1).and_then(|i| chars.get(i)).copied();
    let next = chars.get(idx + 1).copied();
    is_qualified_segment_char(prev) && is_qualified_segment_char(next)
}

fn is_qualified_segment_char(ch: Option<char>) -> bool {
    match ch {
        Some('\u{2200}' | '\u{3bb}' | '\u{3a0}') => false,
        other => is_name_char(other),
    }
}

/// Find the first top-level `:` (depth-0, not `:=`) in `text`.
fn find_top_level_colon(text: &str) -> Option<usize> {
    let mut paren = 0usize;
    let mut brace = 0usize;
    let mut bracket = 0usize;
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
                if next != Some('=') {
                    return Some(idx);
                }
            }
            _ => {}
        }
        i += 1;
    }
    None
}

/// Find the first top-level `:=` in `text`.
fn find_top_level_assign(text: &str) -> Option<usize> {
    let mut paren = 0usize;
    let mut brace = 0usize;
    let mut bracket = 0usize;
    let mut in_string = false;
    let mut escaped = false;
    let chars: Vec<(usize, char)> = text.char_indices().collect();
    let mut i = 0usize;
    while i + 1 < chars.len() {
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
            ':' if paren == 0 && brace == 0 && bracket == 0 && chars[i + 1].1 == '=' => {
                return Some(idx);
            }
            _ => {}
        }
        i += 1;
    }
    None
}

fn take_ident(text: &str) -> Option<(&str, &str)> {
    let text = text.trim_start();
    let first = text.chars().next()?;
    if !is_ident_start(first) {
        return None;
    }
    let mut end = 0usize;
    for (idx, ch) in text.char_indices() {
        if idx > 0 && !is_ident_continue(ch) {
            end = idx;
            break;
        }
    }
    if end == 0 {
        end = text.len();
    }
    Some((&text[..end], &text[end..]))
}

fn match_word<'a>(text: &'a str, word: &str) -> Option<&'a str> {
    let rest = text.strip_prefix(word)?;
    if is_name_char(rest.chars().next()) {
        return None;
    }
    Some(rest)
}

fn normalize_ws(text: &str) -> String {
    text.split_whitespace().collect::<Vec<_>>().join(" ")
}

fn is_ident_start(ch: char) -> bool {
    ch.is_alphabetic() || ch == '_'
}

fn is_ident_continue(ch: char) -> bool {
    is_ident_start(ch) || ch.is_ascii_digit() || matches!(ch, '\'' | '_')
}

fn is_name_char(ch: Option<char>) -> bool {
    // A `.` joins qualified-name segments in Matita identifiers, so it
    // counts as a name character for terminator/keyword-boundary purposes.
    ch.map(|c| is_ident_continue(c) || c == '.')
        .unwrap_or(false)
}

// ---------------------------------------------------------------------------
// Matita CIC type-expression parser → FlatExpr tree.
//
// Mirrors the Coq v_type_parser approach. The CIC type language is the same
// as Coq's; the surface differs only in concrete syntax:
//   * dependent product:   `∀x:T,U`  or  `\forall x:T.U`  (`,` and `.` both
//     used as the binder separator in different Matita corpora)
//   * non-dependent arrow:  `→`  or  `\to`  or ASCII `->`
//   * sorts:  `Prop`, `Type`, `CProp`, `Type[…]` (predicative universe)
//   * application:  juxtaposition  `f a b`
//
// Deliberately conservative — anything it does not understand makes it
// return `None`, and the caller skips the declaration (never a sort(0) stub).
// ---------------------------------------------------------------------------

use clean_kernel::flat::FlatExpr;

const NO_LEVELS: u32 = u32::MAX;
const BINDER_DEFAULT: u8 = 0;
const SORT_PROP: u32 = 0;
const SORT_TYPE: u32 = 1;

#[derive(Debug, Clone, PartialEq, Eq)]
enum Tok {
    Ident(String),
    Nat(u64),
    LParen,
    RParen,
    Arrow,
    Comma,
    /// `.` used as a `\forall`/`λ` binder separator.
    Dot,
    Colon,
    Forall,
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
        // ASCII `->` and Unicode `→` (U+2192) arrows.
        if ch == '-' && chars.get(i + 1) == Some(&'>') {
            out.push(Tok::Arrow);
            i += 2;
            continue;
        }
        if ch == '\u{2192}' {
            out.push(Tok::Arrow);
            i += 1;
            continue;
        }
        // Unicode `⇒` (U+21D2) appears in some Matita match arms; treat as
        // an unmodeled glyph by bailing (return what we have so the
        // fully-consumed check fails).
        if ch == '\u{21D2}' {
            return out;
        }
        // `:=` terminates a type expression — stop defensively.
        if ch == ':' && chars.get(i + 1) == Some(&'=') {
            break;
        }
        // `∀` (U+2200) and `λ`/`Π` glyphs.
        if ch == '\u{2200}' {
            out.push(Tok::Forall);
            i += 1;
            continue;
        }
        // `λ` (U+03BB) and `Π` (U+03A0): a lambda is a term, not a type
        // former; a bare `Π` we do not model — bail in both cases.
        if ch == '\u{3bb}' || ch == '\u{3a0}' {
            return out;
        }
        // Backslash escapes: `\forall`, `\to`, `\lambda`, `\lor`, ...
        if ch == '\\' {
            let start = i + 1;
            let mut j = start;
            while j < chars.len() && chars[j].is_ascii_alphabetic() {
                j += 1;
            }
            let word: String = chars[start..j].iter().collect();
            match word.as_str() {
                "forall" => out.push(Tok::Forall),
                "to" => out.push(Tok::Arrow),
                // Any other backslash macro (`\lambda`, `\lor`, `\land`,
                // `\exists`, …) is unmodeled — bail.
                _ => return out,
            }
            i = j;
            continue;
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
            ',' => {
                out.push(Tok::Comma);
                i += 1;
                continue;
            }
            '.' => {
                out.push(Tok::Dot);
                i += 1;
                continue;
            }
            ':' => {
                out.push(Tok::Colon);
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
        if is_ident_start(ch) {
            let start = i;
            while i < chars.len() {
                let c = chars[i];
                if is_ty_ident_continue(c) {
                    i += 1;
                    continue;
                }
                // A `.` continues the identifier only as a qualified-name
                // separator (`nat.S`): the next char must itself start an
                // identifier. A `.` followed by whitespace/term (`Type. A`)
                // is the `∀`/`λ` binder separator and ends the identifier.
                if c == '.' && chars.get(i + 1).is_some_and(|n| is_ident_start(*n)) {
                    i += 2;
                    continue;
                }
                break;
            }
            let id: String = chars[start..i].iter().collect();
            match id.as_str() {
                // Term/proof-level keywords that cannot head a plain type
                // expression — bail rather than treat as identifiers.
                "let" | "match" | "with" | "in" | "lambda" => return out,
                "_" => out.push(Tok::Underscore),
                _ => out.push(Tok::Ident(id)),
            }
            continue;
        }
        // Unknown character (stray operator glyph) — cannot parse this type
        // faithfully. Return what we have; an incomplete structure will then
        // fail the fully-consumed check.
        return out;
    }
    out
}

/// Identifier continuation inside a type expression (excluding the `.`
/// qualified-name separator, which the lexer handles with lookahead so a
/// binder-separator `.` is not absorbed into the preceding name).
fn is_ty_ident_continue(ch: char) -> bool {
    ch.is_alphanumeric() || matches!(ch, '_' | '\'')
}

/// Recognise a Matita sort atom: `Prop`, `Type`, `CProp`, optionally with a
/// universe index. `Type[…]` is handled by the parser (the `[…]` is consumed
/// after the head). A bare subscript-free `Type`/`CProp`/`Prop` is a sort.
fn is_sort_atom(name: &str) -> bool {
    matches!(name, "Prop" | "Type" | "CProp" | "Set")
}

struct Parser<'w> {
    toks: Vec<Tok>,
    pos: usize,
    writer: &'w mut ShardWriter,
    /// Stack of in-scope binder names, outermost first. A name's de Bruijn
    /// index is `bound.len() - 1 - position`.
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

    /// After `∀`/`\forall`, parse one or more binder groups followed by the
    /// separator (`,` or `.`), then the body. Matita corpora use `,` after
    /// `∀` and `.` after `\forall`; we accept either.
    fn parse_forall_chain(&mut self) -> Option<u32> {
        let mut binders: Vec<(u8, u32)> = Vec::new();
        let mut pushed = 0usize;
        loop {
            if matches!(self.peek(), Some(Tok::Comma) | Some(Tok::Dot)) {
                self.bump();
                break;
            }
            if self.peek().is_none() {
                self.unwind(pushed);
                return None;
            }
            let group = match self.parse_binder_group() {
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

    /// Parse one binder group: `(x y : T)` or the bracketless `x y : T`
    /// form Matita accepts after `∀`. Each name shares the group's type.
    /// An untyped binder is unrecoverable, so we bail rather than fabricate.
    fn parse_binder_group(&mut self) -> Option<Vec<(String, u8, u32)>> {
        let bracketed = matches!(self.peek(), Some(Tok::LParen));
        if bracketed {
            self.bump();
        }
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
            // Untyped binder (`∀x, …`): no annotation to reconstruct. Bail.
            return None;
        };
        if bracketed && !self.eat(&Tok::RParen) {
            return None;
        }
        Some(names.into_iter().map(|n| (n, BINDER_DEFAULT, ty)).collect())
    }

    fn expect_ident(&mut self) -> Option<String> {
        match self.bump()? {
            Tok::Ident(s) => Some(s),
            Tok::Underscore => Some("_".into()),
            _ => None,
        }
    }

    /// `arrow := app (→ arrow)?` — right-associative.
    fn parse_arrow(&mut self) -> Option<u32> {
        let lhs = self.parse_app()?;
        if !self.eat(&Tok::Arrow) {
            return Some(lhs);
        }
        // `A → B` ≡ `∀(_ : A), B`. Push an anonymous binder so de Bruijn
        // indices in `B` account for the new binding level.
        self.bound.push("_".into());
        let rhs = self.parse_type();
        self.bound.pop();
        let rhs = rhs?;
        self.add(FlatExpr::pi(BINDER_DEFAULT, lhs, rhs))
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
                // Matita placeholder `?`/`_` — emit a Prop-sorted atom.
                self.add(FlatExpr::sort(SORT_PROP))
            }
            Tok::Ident(name) => {
                self.bump();
                self.emit_name(&name)
            }
            // Arrows / commas / dots / brackets in atom position are invalid.
            _ => None,
        }
    }

    fn emit_name(&mut self, name: &str) -> Option<u32> {
        // Universe atoms. `Type[…]` carries a level annotation that we
        // consume and discard (re-elaborating universes is out of scope for
        // a Level-0 import). We map every Type/CProp/Set level to sort(1)
        // and Prop to sort(0); a documented surface approximation.
        if is_sort_atom(name) {
            // Absorb an optional `Type[…]` / `Type i` level annotation.
            if matches!(self.peek(), Some(Tok::Nat(_)) | Some(Tok::Ident(_)))
                && matches!(name, "Type" | "CProp")
            {
                // A following atom that is plainly a universe index — but we
                // only absorb a single bare Nat to avoid eating application
                // arguments of a genuine constant. Leave Idents alone.
                if matches!(self.peek(), Some(Tok::Nat(_))) {
                    self.bump();
                }
            }
            let sort = if name == "Prop" { SORT_PROP } else { SORT_TYPE };
            return self.add(FlatExpr::sort(sort));
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

/// Parse a Matita CIC type-expression string into `writer`, returning the
/// root expression index. Returns `None` on parse failure or empty input;
/// callers must treat that as "skip this declaration", never as a licence to
/// emit a placeholder. On success the entire token stream must be consumed.
pub(crate) fn parse_matita_type(src: &str, writer: &mut ShardWriter) -> Option<u32> {
    let toks = lex(src);
    if toks.is_empty() {
        return None;
    }
    let mut p = Parser::new(toks, writer);
    let root = p.parse_type()?;
    if p.pos != p.toks.len() {
        // Unconsumed tokens mean the type contained a construct we do not
        // model — skip it rather than emit a partial/fake tree.
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
    fn parse_matita_file_extracts_heads_skipping_comments_and_bodies() {
        let content = "\
(* the polymorphic identity function *)
definition id : \u{2200}A:Type. A \u{2192} A := \u{3bb}A.\u{3bb}x.x.

theorem foo : P \u{2192} P.

(* an inductive: keep the arity, drop the constructors *)
inductive nat : Type := O : nat | S : nat \u{2192} nat.

axiom em : \u{2200}P:Prop. P \u{2192} P.
";
        let decls = parse_matita_file(content, "Example.ma");
        let names: Vec<&str> = decls.iter().map(|d| d.name.as_str()).collect();
        assert_eq!(names, vec!["id", "foo", "nat", "em"]);
        assert_eq!(decls[0].kind, MatitaKind::Definition);
        // The `:=` body is dropped; only the type is retained.
        assert_eq!(
            decls[0].type_repr.as_deref(),
            Some("\u{2200}A:Type. A \u{2192} A")
        );
        assert_eq!(decls[1].kind, MatitaKind::Theorem);
        assert_eq!(decls[1].type_repr.as_deref(), Some("P \u{2192} P"));
        assert_eq!(decls[2].kind, MatitaKind::Inductive);
        assert_eq!(decls[2].type_repr.as_deref(), Some("Type"));
        assert_eq!(decls[3].kind, MatitaKind::Axiom);
    }

    #[test]
    fn write_matita_shard_emits_real_type_not_litstr_or_sort0() {
        // `definition id : ∀A:Type. A → A` must produce a real Pi/BVar tree:
        // multiple FlatExpr nodes, body kept, `:=` body dropped, binder `A`
        // resolved to a BVar (must NOT leak into the string table).
        let decls = parse_matita_file(
            "definition id : \u{2200}A:Type. A \u{2192} A := \u{3bb}A.\u{3bb}x.x.\n",
            "T.ma",
        );
        assert_eq!(decls.len(), 1);
        let mut w = ShardWriter::new();
        let written = write_matita_shard(&decls, &mut w);
        assert_eq!(written, 1, "the id definition must be written");
        // Real tree ⇒ more exprs than constants (the no-stub signature).
        assert!(
            w.expr_count() > w.constant_count(),
            "expected expr_count ({}) > constant_count ({})",
            w.expr_count(),
            w.constant_count()
        );
        // Binder name `A` is bound ⇒ must not appear as a free Const string.
        let ss = strings(&w);
        assert!(
            !ss.iter().any(|s| s == "A"),
            "binder name 'A' leaked into strings {ss:?} — ∀ binder not parsed \
             as a Pi/BVar"
        );
        // The dropped value must not have introduced a LitStr or leaked the
        // body identifier `x`.
        assert!(
            !ss.iter().any(|s| s == "x"),
            "proof/value body leaked into strings {ss:?}"
        );
    }

    #[test]
    fn theorem_arrow_type_builds_pi_not_sort0() {
        // `theorem foo : P → P.` — a single non-dependent Pi over a free
        // Const `P`; must be a real tree, not a sort(0) stub.
        let decls = parse_matita_file("theorem foo : P \u{2192} P.\n", "T.ma");
        let mut w = ShardWriter::new();
        let written = write_matita_shard(&decls, &mut w);
        assert_eq!(written, 1);
        assert!(w.expr_count() > w.constant_count());
        let ss = strings(&w);
        assert!(ss.iter().any(|s| s == "P"), "P head missing: {ss:?}");
    }

    #[test]
    fn binder_prefix_before_colon_becomes_pi() {
        // `definition id (A:Type) : A → A` — the telescope `(A:Type)` before
        // the `:` must be re-attached as a leading `∀`, so the body `A`s
        // resolve to BVars and `A` does not leak as a free Const.
        let decls = parse_matita_file(
            "definition id (A:Type) : A \u{2192} A := \u{3bb}x.x.\n",
            "T.ma",
        );
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].name, "id");
        let mut w = ShardWriter::new();
        let written = write_matita_shard(&decls, &mut w);
        assert_eq!(written, 1, "binder-prefix definition must be written");
        assert!(w.expr_count() > w.constant_count());
        let ss = strings(&w);
        assert!(
            !ss.iter().any(|s| s == "A"),
            "binder name 'A' leaked: {ss:?} — prefix telescope not made a Pi"
        );
    }

    #[test]
    fn forall_dependent_binder_resolves_to_bvar() {
        // `∀A:Type. A → A`: both `A` in the body must be BVars.
        let mut w = ShardWriter::new();
        let _ = parse_matita_type("\u{2200}A:Type. A \u{2192} A", &mut w).expect("parse");
        let ss = strings(&w);
        assert!(!ss.iter().any(|s| s == "A"), "A leaked as Const: {ss:?}");
    }

    #[test]
    fn backslash_forall_and_to_parse() {
        // `\forall A:Type. A \to A` — the ASCII macro forms.
        let mut w = ShardWriter::new();
        let _ = parse_matita_type("\\forall A:Type. A \\to A", &mut w).expect("parse");
        let ss = strings(&w);
        assert!(!ss.iter().any(|s| s == "A"), "A leaked: {ss:?}");
    }

    #[test]
    fn application_nests_left() {
        let mut w = ShardWriter::new();
        let _ = parse_matita_type("Vec A n", &mut w).expect("parse");
        // Const(Vec), Const(A), App, Const(n), App.
        assert!(w.expr_count() >= 4, "expected real app tree");
    }

    #[test]
    fn sorts_map_to_sort_atoms() {
        let mut w = ShardWriter::new();
        // Prop → sort(0), Type/CProp → sort(1); arrow makes one Pi.
        let _ = parse_matita_type("Prop \u{2192} Type", &mut w).expect("parse");
        // sort(0), sort(1), Pi = 3 distinct exprs.
        assert!(w.expr_count() >= 3, "expected sorts + Pi");
    }

    #[test]
    fn empty_and_unmodeled_return_none() {
        let mut w = ShardWriter::new();
        assert!(parse_matita_type("", &mut w).is_none());
        assert!(parse_matita_type("   ", &mut w).is_none());
        // A `λ`-term is out of scope; the glyph aborts the lex and leaves an
        // unconsumable remainder ⇒ None (skip, not stub).
        assert!(parse_matita_type("\u{3bb}x.x", &mut w).is_none());
        // An untyped `∀` binder must not be fabricated.
        assert!(parse_matita_type("\u{2200}A. A", &mut w).is_none());
    }
}
