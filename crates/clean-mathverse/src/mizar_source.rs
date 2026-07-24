// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structured importer for Mizar `.miz` **source** files (text tier).
//!
//! This is a **self-contained, toolchain-free** importer that parses Mizar
//! SOURCE directly. It is deliberately distinct from, and shares nothing
//! with, the unwired [`crate::mizar`] module (which consumes semantically
//! elaborated XML produced by the Mizar verifier toolchain). It mirrors the
//! Agda source importer ([`crate::agda_source`]): every header is tagged
//! `SourceSystem::Mizar`, `ImportConfidence::Unverified`, and `AXIOMATIZED`,
//! with `value_idx = NO_VALUE` because we keep only the *statement* (type)
//! of a theorem and drop its `proof … end;` body.
//!
//! What we extract:
//!   * `theorem` items: the asserted FOL formula becomes a prop-typed
//!     STATEMENT (the constant's type). The name comes from a leading label
//!     (`Th1:`, `Lm2:`) when present, otherwise a stable synthesized name
//!     (`<filename>__thm<index>`). The following `proof … end;` body is
//!     skipped (`value_idx = NO_VALUE`).
//!   * `definition … end;` blocks: a `func` / `pred` / `mode` / `attr`
//!     pattern with its `-> type` / `means` / `equals` signature becomes a
//!     constant whose type is that signature, parsed into a real tree.
//!
//! Mizar surface is much harder than Agda. We are intentionally
//! conservative: any formula/type using a construct we do not model
//! (`consider`, Fraenkel `{ … where … }`, schemes, anything needing
//! `.voc`/environ fixity resolution) is **skipped** — the declaration is
//! dropped, never replaced with a `FlatExpr::sort(0)` / `LitStr` stub (the
//! `structured_importers_refuse_stubs` invariant). Honestly, a large
//! fraction of real-corpus formulas are skipped; that is the correct,
//! non-fabricating behavior.

use crate::shard::ShardWriter;
use crate::types::{
    AxiomProfile, ContentDomain, DeclKind, ImportConfidence, MathverseConstantHeader, SourceSystem,
    NO_VALUE,
};

/// A top-level Mizar item we chose to import: a name and its raw type/
/// statement text (the formula for a `theorem`, the signature for a
/// `definition` pattern).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MizarDecl {
    /// The declared name (theorem label, synthesized theorem name, or the
    /// definition pattern name).
    pub name: String,
    /// The raw statement/type text, with continuation lines flattened to
    /// single spaces and `::` comments removed.
    pub type_repr: String,
}

/// Parse the top-level importable items of a Mizar `.miz` source file.
///
/// We strip `::` line comments, then scan for `theorem` and
/// `definition … end;` blocks at the top level. The environ header (`environ
/// … begin`) and proof bodies are skipped. Anything not confidently one of
/// the handled item shapes is ignored; we never fabricate a declaration.
pub fn parse_mizar_file(content: &str, filename: &str) -> Vec<MizarDecl> {
    let logical = strip_comments(content);
    // Work on a single flattened string with normalized whitespace so that
    // multi-line formulas join cleanly; keyword boundaries are preserved
    // because we only ever collapse runs of whitespace to one space.
    let flat = normalize_ws(&logical);
    let stem = file_stem(filename);
    let mut decls = Vec::new();
    let mut thm_index = 0usize;

    // Cursor scan over the flattened text. We look for the next top-level
    // `theorem` or `definition` keyword (whole-word), parse that item, and
    // advance past it.
    let bytes = flat.as_bytes();
    let mut i = 0usize;
    while i < flat.len() {
        if let Some(rest) = keyword_at(&flat, i, "theorem") {
            // `theorem` <maybe label> <formula> [proof … end;] | ;
            let after = i + "theorem".len();
            let (stmt_end, next) = theorem_statement_span(&flat, after);
            let raw = flat[after..stmt_end].trim();
            let (label, formula) = split_label(raw);
            let name = match label {
                Some(l) => l.to_owned(),
                None => {
                    thm_index += 1;
                    format!("{stem}__thm{thm_index}")
                }
            };
            let formula = formula.trim();
            if !formula.is_empty() {
                decls.push(MizarDecl {
                    name,
                    type_repr: formula.to_owned(),
                });
            }
            i = next;
            let _ = rest;
            continue;
        }
        if let Some(_rest) = keyword_at(&flat, i, "definition") {
            let after = i + "definition".len();
            // Find the matching `end;` for this definition block.
            if let Some(end_pos) = find_block_end(&flat, after) {
                let body = &flat[after..end_pos];
                if let Some(decl) = parse_definition_block(body) {
                    decls.push(decl);
                }
                i = end_pos + "end;".len();
                continue;
            }
            // Unterminated definition: stop scanning, nothing reliable left.
            break;
        }
        // Advance one UTF-8 char.
        i += utf8_len(bytes[i]);
    }
    decls
}

/// Write parsed Mizar declarations to a shard.
///
/// Each `type_repr` is parsed into a real `FlatExpr` tree via
/// [`parse_mizar_formula`]. A decl whose statement/type fails to parse is
/// **skipped** — never replaced with a `sort(0)` / `LitStr` placeholder.
/// Every header carries `value_idx = NO_VALUE` (the proof body is dropped),
/// `ImportConfidence::Unverified`, and `AXIOMATIZED`.
///
/// Returns the number of declarations actually written.
pub fn write_mizar_shard(decls: &[MizarDecl], writer: &mut ShardWriter) -> usize {
    let mut written = 0usize;
    for decl in decls {
        let Some(type_idx) = parse_mizar_formula(&decl.type_repr, writer) else {
            continue;
        };
        let name_idx = writer.add_string(&decl.name);
        writer.add_constant(MathverseConstantHeader {
            name_idx,
            type_idx,
            value_idx: NO_VALUE,
            source_system: SourceSystem::Mizar as u8,
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

// ---------------------------------------------------------------------------
// Lexical preprocessing.
// ---------------------------------------------------------------------------

/// Strip Mizar `::` line comments, replacing them with spaces so that line
/// structure is preserved for downstream normalization. A `::` runs to end
/// of line. Mizar has no block comments and no string literals in formulas.
fn strip_comments(content: &str) -> String {
    let mut out = String::with_capacity(content.len());
    for line in content.split_inclusive('\n') {
        // Find `::` and truncate. There are no string literals to worry
        // about in Mizar article bodies.
        if let Some(pos) = line.find("::") {
            out.push_str(&line[..pos]);
            // Preserve the trailing newline if the line had one.
            if line.ends_with('\n') {
                out.push('\n');
            }
        } else {
            out.push_str(line);
        }
    }
    out
}

fn normalize_ws(text: &str) -> String {
    text.split_whitespace().collect::<Vec<_>>().join(" ")
}

fn file_stem(filename: &str) -> String {
    let base = filename.rsplit(['/', '\\']).next().unwrap_or(filename);
    let stem = base.strip_suffix(".miz").unwrap_or(base);
    let cleaned: String = stem
        .chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || c == '_' {
                c
            } else {
                '_'
            }
        })
        .collect();
    if cleaned.is_empty() {
        "mizar".to_owned()
    } else {
        cleaned
    }
}

fn utf8_len(b: u8) -> usize {
    if b < 0x80 {
        1
    } else if b >> 5 == 0b110 {
        2
    } else if b >> 4 == 0b1110 {
        3
    } else if b >> 3 == 0b11110 {
        4
    } else {
        1
    }
}

/// If the whole word `kw` begins at byte offset `i` in `text` (i.e. the
/// preceding char is a non-identifier boundary and the following char is a
/// non-identifier boundary), return the remainder after it.
fn keyword_at<'a>(text: &'a str, i: usize, kw: &str) -> Option<&'a str> {
    if !text.is_char_boundary(i) {
        return None;
    }
    let rest = &text[i..];
    let tail = rest.strip_prefix(kw)?;
    // Preceding boundary: start of text or a non-ident char.
    let prev_ok = i == 0
        || !text[..i]
            .chars()
            .next_back()
            .map(is_ident_char)
            .unwrap_or(false);
    let next_ok = tail
        .chars()
        .next()
        .map(|c| !is_ident_char(c))
        .unwrap_or(true);
    if prev_ok && next_ok {
        Some(tail)
    } else {
        None
    }
}

fn is_ident_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_' || c == '\''
}

/// Find the byte offset of the `theorem` statement end and the offset to
/// resume scanning. The statement runs until either:
///   * a top-level `proof` keyword (the body, which we drop), or
///   * a top-level `;` that terminates the (proofless) theorem.
///
/// Returns `(statement_end_byte, resume_byte)`. When a `proof` is found we
/// skip to its matching `end;` for the resume position.
fn theorem_statement_span(text: &str, start: usize) -> (usize, usize) {
    // Scan word by word for `proof` / `;` at the top level (depth 0).
    let mut depth = 0i32;
    let mut i = start;
    let bytes = text.as_bytes();
    while i < text.len() {
        let c = bytes[i];
        if c == b'(' || c == b'{' || c == b'[' {
            depth += 1;
            i += 1;
            continue;
        }
        if c == b')' || c == b'}' || c == b']' {
            if depth > 0 {
                depth -= 1;
            }
            i += 1;
            continue;
        }
        if depth == 0 {
            if keyword_at(text, i, "proof").is_some() {
                // Statement ends here; skip the proof body to its `end;`.
                let resume = find_block_end(text, i + "proof".len())
                    .map(|e| e + "end;".len())
                    .unwrap_or(text.len());
                return (i, resume);
            }
            if c == b';' {
                return (i, i + 1);
            }
        }
        i += utf8_len(c);
    }
    (text.len(), text.len())
}

/// Given a byte offset just after an opening block keyword (`proof`,
/// `definition`, …), find the matching top-level `end;`, accounting for
/// nested `proof`/`definition`/etc. blocks that also close with `end`.
/// Returns the byte offset of the matching `end` token (such that
/// `text[pos..pos+4] == "end;"` after trimming is conceptually true), or
/// `None` if unbalanced.
fn find_block_end(text: &str, start: usize) -> Option<usize> {
    // Mizar block openers that pair with `end`.
    const OPENERS: &[&str] = &[
        "proof",
        "definition",
        "scheme",
        "registration",
        "notation",
        "case",
        "suppose",
        "hereby",
        "now",
    ];
    let mut depth = 1i32;
    let bytes = text.as_bytes();
    let mut i = start;
    while i < text.len() {
        // `end` (whole word) — may be followed by `;`.
        if keyword_at(text, i, "end").is_some() {
            depth -= 1;
            if depth == 0 {
                // Position of the `end` token. Caller skips `"end;".len()`;
                // tolerate optional whitespace before `;` by reporting this
                // offset and letting the caller advance conservatively.
                return Some(i);
            }
            i += "end".len();
            continue;
        }
        let mut matched = false;
        for opener in OPENERS {
            if keyword_at(text, i, opener).is_some() {
                depth += 1;
                i += opener.len();
                matched = true;
                break;
            }
        }
        if matched {
            continue;
        }
        i += utf8_len(bytes[i]);
    }
    None
}

/// Split a theorem statement into an optional leading label and the formula.
/// A label is a leading `Ident :` that is NOT itself the start of a formula
/// (we only treat it as a label when followed by `:` and the identifier is a
/// plausible label token).
fn split_label(raw: &str) -> (Option<&str>, &str) {
    let trimmed = raw.trim_start();
    // A label is `<ident> :` at the very start. Find the first `:` and check
    // the prefix is a single identifier with no spaces / operators.
    if let Some(colon) = trimmed.find(':') {
        let head = trimmed[..colon].trim();
        // Reject `::=` style or `:` that is part of a soft-type `being`
        // expression: a label head is a single identifier token only.
        let next_is_eq = trimmed[colon + 1..].starts_with('=');
        if !head.is_empty()
            && !next_is_eq
            && head.chars().all(is_ident_char)
            && head
                .chars()
                .next()
                .map(|c| c.is_ascii_alphabetic())
                .unwrap_or(false)
        {
            return (Some(head), trimmed[colon + 1..].trim_start());
        }
    }
    (None, trimmed)
}

/// Parse a `definition … end;` block body, extracting the first
/// `func` / `pred` / `mode` / `attr` pattern and its signature into a
/// [`MizarDecl`]. Returns `None` when no recognizable pattern is found.
fn parse_definition_block(body: &str) -> Option<MizarDecl> {
    // Find the first definitional keyword.
    let body = body.trim();
    let kinds: &[&str] = &["func", "pred", "mode", "attr"];
    let mut best: Option<(usize, &str)> = None;
    for kw in kinds {
        let mut search = 0usize;
        while let Some(rel) = body[search..].find(kw) {
            let at = search + rel;
            if keyword_at(body, at, kw).is_some() {
                if best.map(|(b, _)| at < b).unwrap_or(true) {
                    best = Some((at, kw));
                }
                break;
            }
            search = at + kw.len();
        }
    }
    let (at, kw) = best?;
    let after = &body[at + kw.len()..];
    // The pattern text runs until `means`, `equals`, or the terminating `;`.
    // For `func` we also capture the `-> type` result type.
    let pattern_end = ["means", "equals", ";"]
        .iter()
        .filter_map(|m| keyword_or_punct_pos(after, m))
        .min()
        .unwrap_or(after.len());
    let pattern = after[..pattern_end].trim();
    if pattern.is_empty() {
        return None;
    }
    // Name: the first identifier-like token of the pattern. Mizar functor
    // patterns can be prefix/infix; we take the first alphabetic token as
    // the canonical name (operators like `+` are skipped from the name but
    // the type still carries the structure).
    let name = pattern_name(pattern)?;
    // Type/signature: the result type after `->` for func; otherwise the
    // pattern's argument-typing itself (the `of`/`being` soft types).
    let signature = if let Some(arrow) = pattern.find("->") {
        pattern[arrow + 2..].trim().to_owned()
    } else {
        pattern.to_owned()
    };
    if signature.is_empty() {
        return None;
    }
    Some(MizarDecl {
        name,
        type_repr: signature,
    })
}

/// Position of whole-word keyword `m` (or a literal punctuation like `;`) in
/// `text`, if present.
fn keyword_or_punct_pos(text: &str, m: &str) -> Option<usize> {
    if m == ";" {
        return text.find(';');
    }
    let mut search = 0usize;
    while let Some(rel) = text[search..].find(m) {
        let at = search + rel;
        if keyword_at(text, at, m).is_some() {
            return Some(at);
        }
        search = at + m.len();
    }
    None
}

/// Extract a canonical name from a definition pattern: the first alphabetic
/// identifier token. Returns `None` when none exists.
fn pattern_name(pattern: &str) -> Option<String> {
    for tok in pattern.split(|c: char| !is_ident_char(c)) {
        if !tok.is_empty()
            && tok
                .chars()
                .next()
                .map(|c| c.is_ascii_alphabetic())
                .unwrap_or(false)
        {
            // Skip soft-type connective words that are not real names.
            if matches!(tok, "of" | "being" | "for" | "ex" | "st" | "holds" | "is") {
                continue;
            }
            return Some(tok.to_owned());
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Mizar formula / type → FlatExpr tree.
//
// A small recursive-descent parser over a token stream. Like the Agda
// importer it is deliberately conservative: anything it does not model makes
// it return `None`, and the caller skips the declaration (never a stub).
//
// Grammar (subset we model):
//   formula := "for" binders "holds" formula        (=> Pi over typed binder)
//            | "ex" binders "st" formula             (=> App of Const "ex" head)
//            | impl
//   impl    := disj ("implies" impl)?                (=> Pi / arrow)
//   disj    := conj ("or" conj)*                     (=> App of Const "or")
//   conj    := unary ("&" unary)*                    (=> App of Const "&")
//   unary   := "not" unary | atom
//   atom    := primary (rel primary)?                (=> App of Const rel)
//   primary := term application of identifiers / numbers / ( formula )
// ---------------------------------------------------------------------------

use clean_kernel::flat::FlatExpr;

const NO_LEVELS: u32 = u32::MAX;
const BINDER_DEFAULT: u8 = 0;
const SORT_PROP: u32 = 0;

/// Parse a Mizar statement/type string into `writer`, returning the root
/// expression index. Returns `None` on parse failure, empty input, or any
/// unmodeled construct. On success the entire token stream must be consumed.
pub(crate) fn parse_mizar_formula(src: &str, writer: &mut ShardWriter) -> Option<u32> {
    let toks = lex(src)?;
    if toks.is_empty() {
        return None;
    }
    let mut p = Parser::new(toks, writer);
    let root = p.parse_formula()?;
    if p.pos != p.toks.len() {
        // Trailing unparsed tokens => unmodeled construct => skip.
        return None;
    }
    Some(root)
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Tok {
    Word(String),
    Num(u64),
    LParen,
    RParen,
    Comma,
    /// Relational / equality operators we treat as a binary Const head.
    Op(String),
}

/// Lex a Mizar formula. Returns `None` if a character we cannot model is
/// encountered (e.g. `{` for a Fraenkel term), causing the caller to skip.
fn lex(src: &str) -> Option<Vec<Tok>> {
    let chars: Vec<char> = src.chars().collect();
    let mut out = Vec::new();
    let mut i = 0usize;
    while i < chars.len() {
        let ch = chars[i];
        if ch.is_whitespace() {
            i += 1;
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
            // Fraenkel / scheme / set-builder braces and brackets are not
            // modeled — bail so the whole decl is skipped.
            '{' | '}' | '[' | ']' => return None,
            // Semicolons should have been stripped by the framing logic; a
            // stray one means we over-read. Bail.
            ';' => return None,
            _ => {}
        }
        if ch.is_ascii_digit() {
            let start = i;
            while i < chars.len() && chars[i].is_ascii_digit() {
                i += 1;
            }
            let s: String = chars[start..i].iter().collect();
            match s.parse::<u64>() {
                Ok(n) => out.push(Tok::Num(n)),
                Err(_) => return None,
            }
            continue;
        }
        // Multi-char relational operators first.
        if let Some((op, len)) = match_operator(&chars, i) {
            out.push(Tok::Op(op));
            i += len;
            continue;
        }
        if is_word_start(ch) {
            let start = i;
            while i < chars.len() && is_word_continue(chars[i]) {
                i += 1;
            }
            let w: String = chars[start..i].iter().collect();
            out.push(Tok::Word(w));
            continue;
        }
        // Unknown glyph (operator we do not model, special symbol): bail.
        return None;
    }
    Some(out)
}

fn is_word_start(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_'
}

fn is_word_continue(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_' || c == '\''
}

/// Match a relational/equality operator at `chars[i]`, returning the
/// canonical operator string and its length in chars. Only a small, safe set
/// is modeled; everything else is left for the word/bail path.
fn match_operator(chars: &[char], i: usize) -> Option<(String, usize)> {
    let two: String = chars[i..(i + 2).min(chars.len())].iter().collect();
    match two.as_str() {
        "<=" => return Some(("<=".into(), 2)),
        ">=" => return Some((">=".into(), 2)),
        "<>" => return Some(("<>".into(), 2)),
        "c=" => return Some(("c=".into(), 2)), // subset
        _ => {}
    }
    match chars[i] {
        '=' => Some(("=".into(), 1)),
        '<' => Some(("<".into(), 1)),
        '>' => Some((">".into(), 1)),
        // Conjunction connective `&` (lexed here so `parse_conj` can pick it
        // up as a `Tok::Op("&")`).
        '&' => Some(("&".into(), 1)),
        // Arithmetic operators inside terms: model as binary Const heads.
        '+' => Some(("+".into(), 1)),
        '*' => Some(("*".into(), 1)),
        // A bare `-` could be subtraction; model it.
        '-' => Some(("-".into(), 1)),
        _ => None,
    }
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
    fn peek_word(&self, w: &str) -> bool {
        matches!(self.peek(), Some(Tok::Word(s)) if s == w)
    }
    fn bump(&mut self) -> Option<Tok> {
        let t = self.toks.get(self.pos).cloned()?;
        self.pos += 1;
        Some(t)
    }
    fn eat_word(&mut self, w: &str) -> bool {
        if self.peek_word(w) {
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
    fn const_head(&mut self, name: &str) -> Option<u32> {
        let name_idx = self.writer.add_string(name);
        self.add(FlatExpr::const_ref(name_idx, NO_LEVELS))
    }
    fn unwind(&mut self, n: usize) {
        for _ in 0..n {
            self.bound.pop();
        }
    }

    /// Top-level formula entry.
    fn parse_formula(&mut self) -> Option<u32> {
        if self.peek_word("for") {
            self.bump();
            return self.parse_for_chain();
        }
        if self.peek_word("ex") {
            self.bump();
            return self.parse_ex_chain();
        }
        self.parse_impl()
    }

    /// `for X1, X2, … being T holds P` => nested Pi over typed binders.
    /// Multiple binders may share the soft type. We require an explicit
    /// `being T` and a `holds` body; otherwise bail.
    fn parse_for_chain(&mut self) -> Option<u32> {
        // Collect binder names.
        let mut names = Vec::new();
        loop {
            match self.peek().cloned() {
                Some(Tok::Word(w)) if !is_reserved(&w) => {
                    self.bump();
                    names.push(w);
                }
                _ => break,
            }
            if matches!(self.peek(), Some(Tok::Comma)) {
                self.bump();
                continue;
            }
            break;
        }
        if names.is_empty() {
            return None;
        }
        // `being <type>` is required to reconstruct a faithful binder type.
        if !self.eat_word("being") {
            return None;
        }
        let ty = self.parse_soft_type()?;
        if !self.eat_word("holds") {
            return None;
        }
        // Push binders, parse body, fold into Pis.
        for n in &names {
            self.bound.push(n.clone());
        }
        let body = self.parse_formula();
        self.unwind(names.len());
        let body = body?;
        let mut acc = body;
        for _ in 0..names.len() {
            acc = self.add(FlatExpr::pi(BINDER_DEFAULT, ty, acc))?;
        }
        Some(acc)
    }

    /// `ex X being T st P` => `App (App (Const "ex") T_pred) body`. We model
    /// the existential as an application of a logical `ex` head so that the
    /// type tree is real (no `sort(0)` stub) without claiming a dependent
    /// sigma we cannot faithfully encode. The binder is pushed so `P` can
    /// reference it via a BVar.
    fn parse_ex_chain(&mut self) -> Option<u32> {
        let mut names = Vec::new();
        loop {
            match self.peek().cloned() {
                Some(Tok::Word(w)) if !is_reserved(&w) => {
                    self.bump();
                    names.push(w);
                }
                _ => break,
            }
            if matches!(self.peek(), Some(Tok::Comma)) {
                self.bump();
                continue;
            }
            break;
        }
        if names.is_empty() {
            return None;
        }
        if !self.eat_word("being") {
            return None;
        }
        let ty = self.parse_soft_type()?;
        if !self.eat_word("st") {
            return None;
        }
        for n in &names {
            self.bound.push(n.clone());
        }
        let body = self.parse_formula();
        self.unwind(names.len());
        let body = body?;
        // ex head applied to the binder type and the body predicate.
        let head = self.const_head("ex")?;
        let a1 = self.add(FlatExpr::app(head, ty))?;
        self.add(FlatExpr::app(a1, body))
    }

    /// `disj ("implies" impl)?` — right-associative implication as a Pi
    /// (`A implies B` ≡ `(_ : A) → B`, an anonymous binder).
    fn parse_impl(&mut self) -> Option<u32> {
        let lhs = self.parse_disj()?;
        if self.eat_word("implies") {
            self.bound.push("_".into());
            let rhs = self.parse_impl();
            self.bound.pop();
            let rhs = rhs?;
            return self.add(FlatExpr::pi(BINDER_DEFAULT, lhs, rhs));
        }
        // `iff` => App (App (Const "iff") A) B.
        if self.eat_word("iff") {
            let rhs = self.parse_disj()?;
            let head = self.const_head("iff")?;
            let a1 = self.add(FlatExpr::app(head, lhs))?;
            return self.add(FlatExpr::app(a1, rhs));
        }
        Some(lhs)
    }

    /// `conj ("or" conj)*` => left-folded `App (App (Const "or") a) b`.
    fn parse_disj(&mut self) -> Option<u32> {
        let mut acc = self.parse_conj()?;
        while self.eat_word("or") {
            let rhs = self.parse_conj()?;
            let head = self.const_head("or")?;
            let a1 = self.add(FlatExpr::app(head, acc))?;
            acc = self.add(FlatExpr::app(a1, rhs))?;
        }
        Some(acc)
    }

    /// `unary ("&" unary)*` => left-folded `App (App (Const "and") a) b`.
    fn parse_conj(&mut self) -> Option<u32> {
        let mut acc = self.parse_unary()?;
        while matches!(self.peek(), Some(Tok::Op(o)) if o == "&") || self.peek_word("and") {
            // consume the connective
            self.bump();
            let rhs = self.parse_unary()?;
            let head = self.const_head("and")?;
            let a1 = self.add(FlatExpr::app(head, acc))?;
            acc = self.add(FlatExpr::app(a1, rhs))?;
        }
        Some(acc)
    }

    /// `"not" unary | atom`.
    fn parse_unary(&mut self) -> Option<u32> {
        if self.eat_word("not") {
            let inner = self.parse_unary()?;
            let head = self.const_head("not")?;
            return self.add(FlatExpr::app(head, inner));
        }
        self.parse_atom()
    }

    /// `primary (rel primary)?` — a single relational/predicate atom. We also
    /// recognize the soft-type predicate `t is A` and `t in S` forms.
    fn parse_atom(&mut self) -> Option<u32> {
        // Parenthesized formula.
        if matches!(self.peek(), Some(Tok::LParen)) {
            self.bump();
            let inner = self.parse_formula()?;
            if !matches!(self.bump(), Some(Tok::RParen)) {
                return None;
            }
            return Some(inner);
        }
        let lhs = self.parse_term()?;
        // Relational operator: `=`, `<`, `<=`, `c=`, etc. The conjunction
        // connective `&` is NOT a relation — it is handled by `parse_conj`.
        if let Some(Tok::Op(op)) = self.peek().cloned() {
            if op != "&" {
                self.bump();
                let rhs = self.parse_term()?;
                let head = self.const_head(&rel_name(&op))?;
                let a1 = self.add(FlatExpr::app(head, lhs))?;
                return self.add(FlatExpr::app(a1, rhs));
            }
        }
        // `t in S` membership predicate.
        if self.eat_word("in") {
            let rhs = self.parse_term()?;
            let head = self.const_head("in")?;
            let a1 = self.add(FlatExpr::app(head, lhs))?;
            return self.add(FlatExpr::app(a1, rhs));
        }
        // `t is A` attribute predicate.
        if self.eat_word("is") {
            let rhs = self.parse_term()?;
            let head = self.const_head("is")?;
            let a1 = self.add(FlatExpr::app(head, lhs))?;
            return self.add(FlatExpr::app(a1, rhs));
        }
        // Bare predicate application (e.g. a 0-ary or already-applied pred):
        // accept the term as the atom.
        Some(lhs)
    }

    /// A term: left-associative application of primaries, with binary
    /// arithmetic operators folded as Const heads.
    fn parse_term(&mut self) -> Option<u32> {
        let mut acc = self.parse_primary()?;
        loop {
            // Binary arithmetic operator continuation.
            if let Some(Tok::Op(op)) = self.peek().cloned() {
                if is_arith(&op) {
                    self.bump();
                    let rhs = self.parse_primary()?;
                    let head = self.const_head(&rel_name(&op))?;
                    let a1 = self.add(FlatExpr::app(head, acc))?;
                    acc = self.add(FlatExpr::app(a1, rhs))?;
                    continue;
                }
            }
            break;
        }
        Some(acc)
    }

    /// A primary: identifier (possibly applied to a parenthesized arg list),
    /// number, or parenthesized term. Identifiers resolve to BVar when bound.
    fn parse_primary(&mut self) -> Option<u32> {
        match self.peek().cloned()? {
            Tok::LParen => {
                self.bump();
                let inner = self.parse_formula()?;
                if !matches!(self.bump(), Some(Tok::RParen)) {
                    return None;
                }
                Some(inner)
            }
            Tok::Num(n) => {
                self.bump();
                self.add(FlatExpr::lit_nat(n))
            }
            Tok::Word(w) => {
                if is_reserved(&w) {
                    // A reserved keyword in term position means we mis-parsed
                    // (or the construct is unmodeled). Bail.
                    return None;
                }
                self.bump();
                let mut head = self.emit_name(&w)?;
                // Functor application `f(a, b, …)`.
                if matches!(self.peek(), Some(Tok::LParen)) {
                    self.bump();
                    if !matches!(self.peek(), Some(Tok::RParen)) {
                        loop {
                            let arg = self.parse_term()?;
                            head = self.add(FlatExpr::app(head, arg))?;
                            if matches!(self.peek(), Some(Tok::Comma)) {
                                self.bump();
                                continue;
                            }
                            break;
                        }
                    }
                    if !matches!(self.bump(), Some(Tok::RParen)) {
                        return None;
                    }
                }
                Some(head)
            }
            _ => None,
        }
    }

    fn emit_name(&mut self, name: &str) -> Option<u32> {
        if let Some(pos) = self.bound.iter().rposition(|n| n == name) {
            let depth = self.bound.len() - 1 - pos;
            return self.add(FlatExpr::bvar(depth as u32));
        }
        let name_idx = self.writer.add_string(name);
        self.add(FlatExpr::const_ref(name_idx, NO_LEVELS))
    }

    /// Parse a Mizar soft type as a predicate-shaped expression, e.g.
    /// `set`, `Element of S`, `Subset of S`, `Nat`. We model `T of S` as
    /// `App (Const T) (term S)`; a bare type word as `Const T`. Anything
    /// more exotic bails.
    fn parse_soft_type(&mut self) -> Option<u32> {
        // Type head must be a (non-reserved) word.
        let head_word = match self.peek().cloned() {
            Some(Tok::Word(w)) if !is_reserved(&w) => {
                self.bump();
                w
            }
            _ => return None,
        };
        let mut ty = {
            let name_idx = self.writer.add_string(&head_word);
            self.add(FlatExpr::const_ref(name_idx, NO_LEVELS))?
        };
        // Optional `of <term>` (possibly comma-separated list of args).
        if self.eat_word("of") {
            loop {
                let arg = self.parse_term()?;
                ty = self.add(FlatExpr::app(ty, arg))?;
                if matches!(self.peek(), Some(Tok::Comma)) {
                    self.bump();
                    continue;
                }
                break;
            }
        }
        Some(ty)
    }
}

/// Canonical Const name for an operator token.
fn rel_name(op: &str) -> String {
    match op {
        "=" => "eq".into(),
        "<" => "lt".into(),
        ">" => "gt".into(),
        "<=" => "le".into(),
        ">=" => "ge".into(),
        "<>" => "neq".into(),
        "c=" => "subset".into(),
        "+" => "add".into(),
        "*" => "mul".into(),
        "-" => "sub".into(),
        other => other.into(),
    }
}

fn is_arith(op: &str) -> bool {
    matches!(op, "+" | "*" | "-")
}

/// Reserved Mizar formula keywords that may not appear as plain identifiers
/// in term position; their presence where a term is expected signals an
/// unmodeled construct.
fn is_reserved(w: &str) -> bool {
    matches!(
        w,
        "for"
            | "ex"
            | "holds"
            | "st"
            | "being"
            | "implies"
            | "iff"
            | "or"
            | "and"
            | "not"
            | "is"
            | "in"
            | "of"
            | "proof"
            | "end"
            | "consider"
            | "where"
            | "such"
            | "that"
            | "be"
            | "thesis"
            | "scheme"
    )
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
    fn parse_theorem_keeps_statement_drops_proof_and_handles_comment() {
        let content = "\
environ
 vocabularies XBOOLE_0;
begin
:: a leading comment line
theorem Th1: for x being set holds x = x
proof
  let x be set;
  thus x = x;
end;

definition
  let n be Nat;
  func double(n) -> Nat means
    it = n + n;
end;
";
        let decls = parse_mizar_file(content, "TEST.miz");
        // We expect the theorem statement and the func definition.
        let names: Vec<&str> = decls.iter().map(|d| d.name.as_str()).collect();
        assert!(
            names.contains(&"Th1"),
            "theorem label Th1 not captured: {names:?}"
        );
        assert!(
            names.contains(&"double"),
            "definition func name not captured: {names:?}"
        );
        // The theorem statement must be the formula, not the proof body.
        let th = decls.iter().find(|d| d.name == "Th1").unwrap();
        assert!(
            th.type_repr.contains("holds"),
            "statement lost: {:?}",
            th.type_repr
        );
        assert!(
            !th.type_repr.contains("thus") && !th.type_repr.contains("let x be"),
            "proof body leaked into statement: {:?}",
            th.type_repr
        );
    }

    #[test]
    fn write_shard_emits_real_type_not_litstr_or_sort0() {
        let decls = vec![MizarDecl {
            name: "Th1".into(),
            type_repr: "for x being set holds x = x".into(),
        }];
        let mut w = ShardWriter::new();
        let written = write_mizar_shard(&decls, &mut w);
        assert_eq!(written, 1, "the theorem statement must be written");
        // Real tree => more exprs than constants (the no-stub signature).
        assert!(
            w.expr_count() > w.constant_count(),
            "expected expr_count ({}) > constant_count ({})",
            w.expr_count(),
            w.constant_count()
        );
        // The Pi root must NOT be a bare sort(0): a `for..holds` must build a
        // Pi node, so we have at least a binder type + body + Pi (>= 3 nodes).
        assert!(
            w.expr_count() >= 3,
            "for..holds did not build a real Pi tree: {} nodes",
            w.expr_count()
        );
        // Binder `x` is bound => must resolve to a BVar, not leak as a Const
        // string.
        let ss = strings(&w);
        assert!(
            !ss.iter().any(|s| s == "x"),
            "binder name 'x' leaked into strings {ss:?} — not parsed as Pi/BVar"
        );
    }

    #[test]
    fn for_holds_builds_pi_over_typed_binder() {
        let mut w = ShardWriter::new();
        let root = parse_mizar_formula("for x being set holds x = x", &mut w).expect("parse");
        // set (Const), bvar x, bvar x, eq head, app, app, Pi.
        assert!(w.expr_count() >= 3, "expected a real tree");
        assert_eq!(root, w.expr_count() as u32 - 1, "root is the outer Pi");
        let ss = strings(&w);
        assert!(
            ss.iter().any(|s| s == "set"),
            "type head 'set' missing: {ss:?}"
        );
        assert!(
            ss.iter().any(|s| s == "eq"),
            "eq relation head missing: {ss:?}"
        );
        assert!(!ss.iter().any(|s| s == "x"), "binder x leaked: {ss:?}");
    }

    #[test]
    fn implies_builds_arrow() {
        let mut w = ShardWriter::new();
        let _ = parse_mizar_formula("P implies Q", &mut w).expect("parse");
        // P (Const), Q (Const under the anon binder), Pi.
        assert!(w.expr_count() >= 3, "implies did not build a Pi");
    }

    #[test]
    fn conjunction_and_negation_build_const_apps() {
        let mut w = ShardWriter::new();
        let _ = parse_mizar_formula("not P & Q", &mut w).expect("parse");
        let ss = strings(&w);
        assert!(ss.iter().any(|s| s == "not"), "not head missing: {ss:?}");
        assert!(ss.iter().any(|s| s == "and"), "and head missing: {ss:?}");
    }

    #[test]
    fn ex_builds_application_form() {
        let mut w = ShardWriter::new();
        let _ = parse_mizar_formula("ex x being set st x = x", &mut w).expect("parse");
        let ss = strings(&w);
        assert!(ss.iter().any(|s| s == "ex"), "ex head missing: {ss:?}");
        assert!(!ss.iter().any(|s| s == "x"), "binder x leaked: {ss:?}");
    }

    #[test]
    fn soft_type_element_of_builds_application() {
        let mut w = ShardWriter::new();
        // `Element of S` as a binder soft type.
        let _ = parse_mizar_formula("for y being Element of S holds y = y", &mut w).expect("parse");
        let ss = strings(&w);
        assert!(
            ss.iter().any(|s| s == "Element"),
            "Element type head missing: {ss:?}"
        );
        assert!(ss.iter().any(|s| s == "S"), "S argument missing: {ss:?}");
    }

    #[test]
    fn unmodeled_constructs_are_skipped_not_faked() {
        let mut w = ShardWriter::new();
        // Fraenkel set-builder uses braces — unmodeled, must bail.
        assert!(parse_mizar_formula("{ x where x is set : x = x }", &mut w).is_none());
        // `consider` is a proof-only construct.
        assert!(parse_mizar_formula("consider x such that P", &mut w).is_none());
        // Empty / whitespace.
        assert!(parse_mizar_formula("", &mut w).is_none());
        assert!(parse_mizar_formula("   ", &mut w).is_none());
    }

    #[test]
    fn synthesized_name_when_no_label() {
        let content = "\
begin
theorem for x being set holds x = x;
";
        let decls = parse_mizar_file(content, "ARTICLE.miz");
        assert_eq!(decls.len(), 1);
        assert!(
            decls[0].name.starts_with("ARTICLE__thm"),
            "expected synthesized stable name, got {:?}",
            decls[0].name
        );
    }
}
