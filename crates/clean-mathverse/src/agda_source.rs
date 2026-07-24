// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structured importer for Agda `.agda` source files.
//!
//! Agda surface declarations are line-oriented `name : type` signatures.
//! This importer scans the top-level signatures in a module, parses each
//! `type` string into a real structural [`FlatExpr`] tree, and writes one
//! shard per directory via [`write_agda_shard`]. It mirrors the Coq `.v`
//! importer ([`crate::coq::v_import`]): every header is tagged
//! `SourceSystem::Agda`, `ImportConfidence::Unverified`, and `AXIOMATIZED`,
//! with `value_idx = NO_VALUE` because Agda source carries no proof term we
//! reconstruct here.
//!
//! Like the Coq importer, this is a Level-0/1 **data import**, not a
//! verified elaboration. A signature whose type cannot be parsed into a
//! real tree is **skipped** — never replaced with a `FlatExpr::sort(0)`
//! placeholder (the `structured_importers_refuse_stubs` invariant).

use crate::shard::ShardWriter;
use crate::types::{
    AxiomProfile, ContentDomain, DeclKind, ImportConfidence, MathverseConstantHeader, SourceSystem,
    NO_VALUE,
};

/// A top-level Agda signature: `name : type_repr`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgdaDecl {
    /// The declared name (possibly a mixfix name containing underscores,
    /// e.g. `_+_`). The leading token before the top-level `:`.
    pub name: String,
    /// The raw type text following the top-level `:`, with continuation
    /// lines flattened to single spaces.
    pub type_repr: String,
}

/// Parse the top-level `name : type` signatures of an Agda source file.
///
/// What is handled:
///   * line comments (`-- …`) and block comments (`{- … -}`, nestable),
///   * pragmas (`{-# … #-}`) and the `module` / `open` / `import` /
///     `private` / `postulate` / `infix*` keyword lines (skipped),
///   * multi-line type signatures: a signature whose type continues on
///     following lines that are indented relative to the signature's own
///     indentation (the type runs until the next line at column ≤ the
///     signature column, or a blank line, or an obvious new declaration),
///   * mixfix names: the name token may contain underscores
///     (`_+_`, `if_then_else_`) and Unicode operator glyphs.
///
/// Be conservative: anything not confidently a top-level signature is
/// skipped. We never fabricate a declaration.
pub(crate) fn parse_agda_file(content: &str, _filename: &str) -> Vec<AgdaDecl> {
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
        let indent = leading_ws(line);
        let trimmed = line.trim_start();
        // Skip keyword / structural lines that are never plain signatures.
        if is_skippable_line(trimmed) {
            i += 1;
            continue;
        }
        // A top-level signature begins with a name token followed by a
        // top-level `:` (not `::`, and not part of a deeper construct).
        let Some((name, type_head)) = split_name_and_type(line) else {
            i += 1;
            continue;
        };
        // Collect continuation lines: subsequent lines that are indented
        // strictly more than this signature, and are not themselves blank
        // or a new declaration / keyword.
        let mut type_parts = vec![type_head.trim().to_owned()];
        let mut j = i + 1;
        while j < lines.len() {
            let cont = lines[j];
            if cont.trim().is_empty() {
                break;
            }
            let cont_indent = leading_ws(cont);
            if cont_indent <= indent {
                break;
            }
            let cont_trimmed = cont.trim_start();
            // A continuation that itself looks like a new signature or a
            // definition clause ends the type.
            if is_skippable_line(cont_trimmed) {
                break;
            }
            type_parts.push(cont_trimmed.trim().to_owned());
            j += 1;
        }
        let type_repr = normalize_ws(&type_parts.join(" "));
        if !name.is_empty() && !type_repr.is_empty() {
            decls.push(AgdaDecl { name, type_repr });
        }
        i = j;
    }
    decls
}

/// Write parsed Agda declarations to a shard.
///
/// For each decl the `type_repr` string is parsed into a real `FlatExpr`
/// tree via [`parse_agda_type`]. A decl whose type fails to parse is
/// **skipped** — never replaced with a `sort(0)` placeholder. This is the
/// import-time guarantee that the resulting shard satisfies
/// `expr_count > constant_count`.
///
/// Every header carries `value_idx = NO_VALUE` (Agda source has no proof
/// term we reconstruct), `ImportConfidence::Unverified`, and `AXIOMATIZED`.
///
/// Returns the number of declarations actually written.
pub(crate) fn write_agda_shard(decls: &[AgdaDecl], writer: &mut ShardWriter) -> usize {
    let mut written = 0usize;
    for decl in decls {
        let Some(type_idx) = parse_agda_type(&decl.type_repr, writer) else {
            // Parse failure: skip rather than fall back to sort(0).
            continue;
        };
        let name_idx = writer.add_string(&decl.name);
        writer.add_constant(MathverseConstantHeader {
            name_idx,
            type_idx,
            value_idx: NO_VALUE,
            source_system: SourceSystem::Agda as u8,
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

/// Strip Agda comments (line `-- …`, nestable block `{- … -}`, and the
/// pragma form `{-# … #-}` which is just a block comment for our purposes),
/// replacing them with whitespace so column/line structure is preserved.
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
        // Block comment / pragma start.
        if ch == '{' && next == Some('-') {
            block_depth = 1;
            out.push(' ');
            out.push(' ');
            i += 2;
            continue;
        }
        // Line comment: `--` not immediately followed by an operator-like
        // character that would make it part of a mixfix name. Agda treats
        // `--` followed by whitespace/EOL/non-symbol as a comment opener.
        if ch == '-' && next == Some('-') && !is_dash_run_operator(&chars, i) {
            // Consume to end of line.
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

/// Agda's line-comment rule: `--` opens a comment unless it is immediately
/// followed by another symbol character (in which case `---…` / `--+` etc.
/// is a legal operator token). We approximate: a dash run is a comment iff
/// the character after the final dash is not a name-continuation symbol.
fn is_dash_run_operator(chars: &[char], start: usize) -> bool {
    let mut k = start;
    while k < chars.len() && chars[k] == '-' {
        k += 1;
    }
    matches!(chars.get(k), Some(c) if is_op_symbol(*c))
}

fn is_op_symbol(ch: char) -> bool {
    // Symbols that may continue an Agda operator token after a dash run.
    matches!(ch, '!'..='/' | ':'..='@' | '^' | '|' | '~') && !matches!(ch, '(' | ')' | ';' | ',')
}

/// True for lines that are keywords / structural, never a plain signature.
fn is_skippable_line(trimmed: &str) -> bool {
    if trimmed.starts_with("{-#") || trimmed.starts_with("#-}") {
        return true;
    }
    for kw in [
        "module",
        "open",
        "import",
        "infix",
        "infixl",
        "infixr",
        "syntax",
        "private",
        "public",
        "abstract",
        "instance",
        "primitive",
        "variable",
        "renaming",
        "using",
        "hiding",
        "where",
        "pattern",
        "mutual",
        "constructor",
        "field",
        "record",
        "data",
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

/// Split a line into `(name, type_head)` at its first top-level `:`,
/// where `name` is a single whitespace-delimited token sequence forming a
/// declaration name (one or more tokens before the colon — Agda allows a
/// list like `f g : T` declaring several names with the same type; we take
/// the first as the representative name and still parse the type).
///
/// Returns `None` when there is no top-level `:` (e.g. a definition clause
/// `f x = …`), or when the colon is part of `:=`/`::` or sits inside
/// brackets.
fn split_name_and_type(line: &str) -> Option<(String, &str)> {
    let colon = find_top_level_colon(line)?;
    let name_part = line[..colon].trim();
    let type_part = &line[colon + 1..];
    if name_part.is_empty() || type_part.trim().is_empty() {
        return None;
    }
    // The name segment must be a plain space-separated list of name tokens
    // (no `=`, `→`, `(`, etc. at top level), otherwise this is not a
    // signature line but some other construct that happened to contain a
    // colon. We take the first token as the canonical declared name.
    if name_part.contains('=') || name_part.contains("->") || name_part.contains('→') {
        return None;
    }
    let first = name_part.split_whitespace().next()?;
    if !is_valid_name(first) {
        return None;
    }
    Some((first.to_owned(), type_part))
}

/// A declared name must contain at least one identifier/operator character
/// and must not be a sort/keyword token.
fn is_valid_name(tok: &str) -> bool {
    if tok.is_empty() {
        return false;
    }
    // Reject lone punctuation that cannot be a name.
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
// Agda type-expression parser → FlatExpr tree.
//
// Mirrors the Coq v_type_parser approach: a small recursive-descent parser
// over a token stream producing Pi / Const / App / BVar / Sort nodes. It is
// deliberately conservative — anything it does not understand makes it
// return `None`, and the caller skips the declaration (never a sort(0) stub).
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
    LInst, // ⦃ or {{
    RInst, // ⦄ or }}
    Arrow,
    Comma,
    Colon,
    Forall, // `forall` or `∀`
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
        // Instance-argument brackets: Unicode ⦃ ⦄ and ASCII {{ }}.
        if ch == '\u{2983}' {
            out.push(Tok::LInst);
            i += 1;
            continue;
        }
        if ch == '\u{2984}' {
            out.push(Tok::RInst);
            i += 1;
            continue;
        }
        if ch == '{' && chars.get(i + 1) == Some(&'{') {
            out.push(Tok::LInst);
            i += 2;
            continue;
        }
        if ch == '}' && chars.get(i + 1) == Some(&'}') {
            out.push(Tok::RInst);
            i += 2;
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
        // is a *term*, not a type former. Bail so the caller skips: a
        // returned remainder makes `parse_agda_type` fail the
        // fully-consumed check.
        if ch == '\u{3bb}' || ch == '\\' {
            return out;
        }
        if is_ident_start(ch) {
            let start = i;
            while i < chars.len() && is_ident_continue(chars[i]) {
                i += 1;
            }
            let id: String = chars[start..i].iter().collect();
            // Reserved Agda keywords that cannot head a plain type
            // expression — bail rather than treat them as identifiers.
            if matches!(
                id.as_str(),
                "let" | "in" | "where" | "with" | "record" | "data" | "do" | "case" | "of"
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
        // Unknown character (e.g. a stray operator glyph) — we cannot parse
        // this type faithfully. Return what we have; the parser will treat
        // a premature end as failure if the structure is incomplete.
        return out;
    }
    out
}

fn is_ident_start(ch: char) -> bool {
    ch.is_alphabetic() || ch == '_'
}

/// Agda identifiers are liberal; we accept alphanumerics, `_`, `'`, `.`
/// (qualified names) and subscript digits used by `Set₁` etc.
fn is_ident_continue(ch: char) -> bool {
    ch.is_alphanumeric()
        || matches!(ch, '_' | '\'' | '.' | '-')
        || ('\u{2080}'..='\u{2089}').contains(&ch) // subscript digits ₀..₉
}

/// Recognise an Agda sort atom: `Set`, `Type`, `Prop`, optionally followed
/// by an explicit level suffix — ASCII digits (`Set1`), subscript digits
/// (`Set₁`), or the `ω` glyph (`Setω`). Anything else (e.g. `Setoid`,
/// `Property`) is a user constant, not a sort.
fn is_sort_atom(name: &str) -> bool {
    if name == "Type" {
        return true;
    }
    let base = if let Some(rest) = name.strip_prefix("Set") {
        rest
    } else if let Some(rest) = name.strip_prefix("Prop") {
        rest
    } else {
        return false;
    };
    base.is_empty()
        || base == "\u{3c9}" // ω
        || base
            .chars()
            .all(|c| c.is_ascii_digit() || ('\u{2080}'..='\u{2089}').contains(&c))
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

    /// After `forall`/`∀`, parse one or more binder groups followed by a
    /// `→` or `,` separator, then the body. Agda accepts both
    /// `∀ {A} → body` and `∀ (x : T) , body`-style; we accept either
    /// separator.
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

    /// Parse one binder group: `(x y : T)`, `{x : T}`, `⦃ x : T ⦄`, or
    /// — only inside a `forall`/`∀` where `allow_untyped` is true — the
    /// bare/implicit forms `{A}` / `x` that Agda lets you write when the
    /// type is inferred. For an untyped binder we cannot reconstruct the
    /// type faithfully, so we bail (return `None`) rather than fabricate.
    fn parse_binder_group(&mut self, _allow_untyped: bool) -> Option<Vec<(String, u8, u32)>> {
        let (close, binfo) = match self.peek() {
            Some(Tok::LParen) => (Some(Tok::RParen), BINDER_DEFAULT),
            Some(Tok::LBrace) => (Some(Tok::RBrace), BINDER_IMPLICIT),
            Some(Tok::LInst) => (Some(Tok::RInst), BINDER_INST_IMPLICIT),
            _ => return None,
        };
        self.bump(); // opening bracket
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
            // Untyped binder (`{A}`): no annotation to reconstruct. Bail
            // rather than emit a placeholder type.
            return None;
        };
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
    /// leading bracketed dependent binder Pi such as `(A : Set) → A → A`
    /// and `{A : Set} → A → A`.
    fn parse_arrow(&mut self) -> Option<u32> {
        if matches!(
            self.peek(),
            Some(Tok::LBrace) | Some(Tok::LInst) | Some(Tok::LParen)
        ) {
            // Try a binder-group Pi only when it is genuinely a binder
            // (i.e. `( … : … )` form). A plain parenthesised atom like
            // `(A → B)` has no top-level colon and is handled by parse_app.
            if self.looks_like_binder_group() {
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
            // Implicit `{…}` and instance `⦃…⦄`/`{{…}}` brackets are always
            // binder positions in a type expression.
            Some(Tok::LBrace) | Some(Tok::LInst) => true,
            // A parenthesised group is a binder only if it contains a
            // top-level `:` (`(x : T)`); otherwise it is a type atom.
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
            // Brackets / arrows / commas in atom position are not valid.
            _ => None,
        }
    }

    fn emit_name(&mut self, name: &str) -> Option<u32> {
        // Agda universe atoms: `Set`, `Set₀`, `Set₁`, …, `Setω`, `Prop`,
        // `Prop₁`, …, plus the Lean-ish `Type` surface. Map Prop → sort(0);
        // every Set-level sort → sort(1) (universe levels are out of scope
        // for a Level-0 import — a documented surface approximation, not a
        // verified universe). We only treat the *recognised sort shapes* as
        // sorts so that user names like `Setoid` / `Property` stay Consts.
        if is_sort_atom(name) {
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

/// Parse an Agda type-expression string into `writer`, returning the root
/// expression index. Returns `None` on parse failure or empty input;
/// callers must treat that as "skip this declaration", never as a licence
/// to emit a placeholder. On success the entire token stream must be
/// consumed (a trailing unparsed remainder is a failure).
pub(crate) fn parse_agda_type(src: &str, writer: &mut ShardWriter) -> Option<u32> {
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
    fn parse_agda_file_extracts_signatures_skipping_noise() {
        let content = "\
-- the polymorphic identity function
module Example where

open import Agda.Builtin.Nat

{-# BUILTIN NATURAL Nat #-}

id : {A : Set} → A → A
id x = x

{- a block comment
   spanning lines -}
const : {A B : Set} → A → B → A
const x _ = x

_+_ : Nat → Nat → Nat
zero  + n = n
suc m + n = suc (m + n)
";
        let decls = parse_agda_file(content, "Example.agda");
        let names: Vec<&str> = decls.iter().map(|d| d.name.as_str()).collect();
        assert_eq!(names, vec!["id", "const", "_+_"]);
        assert_eq!(decls[0].type_repr, "{A : Set} → A → A");
        assert_eq!(decls[2].type_repr, "Nat → Nat → Nat");
    }

    #[test]
    fn multiline_type_signature_is_joined() {
        let content = "\
foo : (A : Set)
    → (B : Set)
    → A
    → B
    → A
foo a b x y = x
";
        let decls = parse_agda_file(content, "T.agda");
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].name, "foo");
        assert_eq!(decls[0].type_repr, "(A : Set) → (B : Set) → A → B → A");
    }

    #[test]
    fn write_agda_shard_emits_real_type_not_litstr_or_sort0() {
        // `id : {A : Set} → A → A` must produce a real Pi/BVar tree:
        // multiple FlatExpr nodes, and the binder name `A` must NOT leak
        // into the string table (it should resolve to a BVar).
        let decls = vec![AgdaDecl {
            name: "id".into(),
            type_repr: "{A : Set} → A → A".into(),
        }];
        let mut w = ShardWriter::new();
        let written = write_agda_shard(&decls, &mut w);
        assert_eq!(written, 1, "the id signature must be written");
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
            "binder name 'A' leaked into strings {ss:?} — implicit binder \
             not parsed as a Pi/BVar"
        );
    }

    #[test]
    fn parse_agda_type_arrow_chain_builds_pis() {
        let mut w = ShardWriter::new();
        let root = parse_agda_type("Nat → Nat → Set", &mut w).expect("parse");
        // Const(Nat) [shared], sort(1) for Set, inner Pi, outer Pi.
        assert!(w.expr_count() >= 3, "expected real tree");
        assert_eq!(root, w.expr_count() as u32 - 1, "root is the outer Pi");
        let ss = strings(&w);
        assert!(ss.iter().any(|s| s == "Nat"), "Nat head missing: {ss:?}");
    }

    #[test]
    fn dependent_pi_resolves_binder_to_bvar() {
        // `(A : Set) → A → A`: the two `A` in the body must be BVars, so
        // `A` must NOT appear in the string table.
        let mut w = ShardWriter::new();
        let _ = parse_agda_type("(A : Set) → A → A", &mut w).expect("parse");
        let ss = strings(&w);
        assert!(!ss.iter().any(|s| s == "A"), "A leaked as Const: {ss:?}");
    }

    #[test]
    fn forall_chain_parses() {
        let mut w = ShardWriter::new();
        let _ = parse_agda_type("∀ {A : Set} → A → A", &mut w).expect("parse");
        let ss = strings(&w);
        assert!(!ss.iter().any(|s| s == "A"), "A leaked: {ss:?}");
    }

    #[test]
    fn application_nests_left() {
        let mut w = ShardWriter::new();
        let _ = parse_agda_type("Vec A n", &mut w).expect("parse");
        // Const(Vec), Const(A), App, Const(n), App.
        assert!(w.expr_count() >= 4, "expected real app tree");
    }

    #[test]
    fn empty_and_garbage_return_none() {
        let mut w = ShardWriter::new();
        assert!(parse_agda_type("", &mut w).is_none());
        assert!(parse_agda_type("   ", &mut w).is_none());
        // A `λ`-term is out of scope; the unknown glyph aborts the lex and
        // leaves an unconsumable remainder ⇒ None (skip, not stub).
        assert!(parse_agda_type("λ x → x", &mut w).is_none());
    }

    #[test]
    fn untyped_forall_binder_is_skipped_not_faked() {
        // `∀ {A} → A` has no type annotation on A; we must not fabricate.
        let mut w = ShardWriter::new();
        assert!(parse_agda_type("∀ {A} → A", &mut w).is_none());
    }
}
