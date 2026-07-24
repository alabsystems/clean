// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structured importer for PVS `.pvs` source files.
//!
//! PVS surface declarations live inside a `theory_name: THEORY BEGIN … END
//! theory_name` block. Each top-level form is a `name: <classifier> …`
//! declaration: a type (`T: TYPE`), a constant/function signature
//! (`f(x: nat): nat`, `c: [nat -> nat]`), or a formula
//! (`l: LEMMA <expr>` / `THEOREM` / `AXIOM` / `OBLIGATION`). This importer
//! scans those forms, parses each declared *type* (or, for a formula, its
//! proposition) into a real structural [`FlatExpr`] tree, and writes one
//! shard per directory via [`write_pvs_shard`]. It mirrors the Agda `.agda`
//! importer ([`crate::agda_source`]): every header is tagged
//! `SourceSystem::Pvs`, `ImportConfidence::Unverified`, and `AXIOMATIZED`,
//! with `value_idx = NO_VALUE` because PVS source carries no proof term we
//! reconstruct here.
//!
//! Like the Agda importer, this is a Level-0/1 **data import**, not a
//! verified elaboration. A declaration whose type cannot be parsed into a
//! real tree is **skipped** — never replaced with a `FlatExpr::sort(0)`
//! placeholder (the `structured_importers_refuse_stubs` invariant).

use crate::shard::ShardWriter;
use crate::types::{
    AxiomProfile, ContentDomain, DeclKind, ImportConfidence, MathverseConstantHeader, SourceSystem,
    NO_VALUE,
};

/// The classifier of a parsed PVS declaration, recording how its
/// `type_repr` should be interpreted.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PvsDeclKind {
    /// `name: TYPE` / `TYPE+` / `TYPE = def` — the declared thing is a type;
    /// its own "type" is the `TYPE` universe (a sort).
    Type,
    /// `name(args): T` or `name: T` — an ordinary constant/function whose
    /// type is `type_repr`.
    Const,
    /// `name: LEMMA/THEOREM/AXIOM/… <expr>` — a formula whose type is the
    /// proposition `type_repr`.
    Formula,
}

/// A top-level PVS declaration: `name <args?>: <classifier> type_repr`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PvsDecl {
    /// The declared name (the leading identifier before any argument list
    /// or the top-level `:`).
    pub name: String,
    /// The classification of this declaration.
    pub kind: PvsDeclKind,
    /// The raw type / proposition text to parse into a `FlatExpr`. For a
    /// `TYPE` declaration this is the universe marker (the literal `TYPE`).
    /// For a function with an argument list, the argument types are folded
    /// into a leading arrow chain (`(x: nat): bool` → `nat -> bool`).
    pub type_repr: String,
}

/// Formula keywords: a `name: <KW> <expr>` declaration whose type is the
/// proposition `<expr>`.
const FORMULA_KEYWORDS: &[&str] = &[
    "LEMMA",
    "THEOREM",
    "AXIOM",
    "OBLIGATION",
    "PROPOSITION",
    "COROLLARY",
    "FORMULA",
    "FACT",
    "CONJECTURE",
    "POSTULATE",
    "JUDGEMENT",
    "CLAIM",
];

/// Structural keywords inside a theory body that are never plain
/// declarations (skipped).
const STRUCTURAL_KEYWORDS: &[&str] = &[
    "THEORY",
    "BEGIN",
    "END",
    "IMPORTING",
    "EXPORTING",
    "ASSUMING",
    "ENDASSUMING",
];

/// Parse the top-level declarations of a PVS source file.
///
/// What is handled:
///   * `%` line comments (stripped to whitespace, preserving line structure),
///   * the `THEORY` / `BEGIN` / `END` / `IMPORTING` / `EXPORTING` /
///     `ASSUMING` keyword lines (skipped),
///   * type declarations `T: TYPE` / `TYPE+` / `TYPE = def`,
///   * constant/function declarations `f(args): T` and `c: T`,
///   * formula declarations `l: LEMMA <expr>` / `THEOREM` / `AXIOM` / … .
///
/// A declaration spans from its name to the terminating top-level `;` or, if
/// none, to the start of the next top-level declaration (the next line that
/// begins a `name:` form at the outer level). We are conservative: anything
/// not confidently a declaration is skipped. We never fabricate.
pub fn parse_pvs_file(content: &str, _filename: &str) -> Vec<PvsDecl> {
    let logical = strip_comments(content);
    // Flatten to a single logical stream, then split into declaration units
    // on top-level `;` and on a `name:`-starting line boundary.
    let units = split_declaration_units(&logical);
    let mut decls = Vec::new();
    for unit in units {
        if let Some(decl) = parse_declaration_unit(&unit) {
            decls.push(decl);
        }
    }
    decls
}

/// Write parsed PVS declarations to a shard.
///
/// For each decl the `type_repr` (or, for a `TYPE` declaration, the `TYPE`
/// universe) is parsed into a real `FlatExpr` tree. A decl whose type fails
/// to parse is **skipped** — never replaced with a `sort(0)` placeholder.
/// This is the import-time guarantee that the resulting shard satisfies
/// `expr_count > constant_count`.
///
/// Every header carries `value_idx = NO_VALUE` (PVS source has no proof
/// term we reconstruct), `ImportConfidence::Unverified`, and `AXIOMATIZED`.
///
/// Returns the number of declarations actually written.
pub fn write_pvs_shard(decls: &[PvsDecl], writer: &mut ShardWriter) -> usize {
    let mut written = 0usize;
    for decl in decls {
        let type_idx = match decl.kind {
            // A `TYPE` declaration's own type is the TYPE universe — a sort.
            PvsDeclKind::Type => writer.add_expr(FlatExpr::sort(SORT_TYPE)),
            PvsDeclKind::Const | PvsDeclKind::Formula => {
                match parse_pvs_type(&decl.type_repr, writer) {
                    Some(idx) => idx,
                    // Parse failure: skip rather than fall back to sort(0).
                    None => continue,
                }
            }
        };
        let name_idx = writer.add_string(&decl.name);
        let decl_kind = match decl.kind {
            PvsDeclKind::Formula => DeclKind::Axiom,
            // Types and constants both register as axiomatized constants.
            PvsDeclKind::Type | PvsDeclKind::Const => DeclKind::Axiom,
        };
        writer.add_constant(MathverseConstantHeader {
            name_idx,
            type_idx,
            value_idx: NO_VALUE,
            source_system: SourceSystem::Pvs as u8,
            import_confidence: ImportConfidence::Unverified as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: decl_kind as u8,
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

/// Strip PVS `%` line comments, dropping the comment span (from an unquoted
/// `%` to end of line) while preserving newlines so line structure survives.
/// String literals (`"…"`) are respected so a `%` inside a string is not
/// treated as a comment.
fn strip_comments(content: &str) -> String {
    let mut out = String::with_capacity(content.len());
    for line in content.split_inclusive('\n') {
        let mut in_string = false;
        let mut escaped = false;
        let mut commented = false;
        for ch in line.chars() {
            if commented {
                // Keep the trailing newline, blank the rest.
                if ch == '\n' {
                    out.push('\n');
                }
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
                continue;
            }
            match ch {
                '"' => {
                    in_string = true;
                    out.push(ch);
                }
                '%' => {
                    commented = true;
                }
                _ => out.push(ch),
            }
        }
    }
    out
}

/// Split a comment-stripped theory file into candidate declaration units.
///
/// A unit ends at a top-level `;` (PVS's declaration terminator) or, when a
/// declaration is not `;`-terminated, at the start of the next line that
/// begins a new top-level `name:` declaration form. Structural keyword lines
/// (`THEORY`/`BEGIN`/`END`/`IMPORTING`/…) act as unit boundaries and are
/// dropped.
fn split_declaration_units(logical: &str) -> Vec<String> {
    let lines: Vec<&str> = logical.lines().collect();
    let mut units: Vec<String> = Vec::new();
    let mut current = String::new();
    let flush = |buf: &mut String, units: &mut Vec<String>| {
        let trimmed = buf.trim();
        if !trimmed.is_empty() {
            units.push(trimmed.to_owned());
        }
        buf.clear();
    };
    for raw in lines {
        let trimmed = raw.trim();
        if trimmed.is_empty() {
            continue;
        }
        // A structural keyword line is a boundary; flush and drop the line.
        if is_structural_line(trimmed) {
            flush(&mut current, &mut units);
            // A `name: THEORY` header line contains a `:` but is structural;
            // dropping it is correct. The body declarations follow BEGIN.
            continue;
        }
        // A new top-level declaration starts a fresh unit when the current
        // buffer already holds content and this line opens a `name:` form.
        if !current.is_empty() && starts_new_declaration(trimmed) {
            flush(&mut current, &mut units);
        }
        if !current.is_empty() {
            current.push(' ');
        }
        current.push_str(trimmed);
        // A top-level `;` terminates the declaration.
        if let Some(semi) = find_top_level_semicolon(&current) {
            let (head, _rest) = current.split_at(semi);
            let head = head.trim().to_owned();
            if !head.is_empty() {
                units.push(head);
            }
            current.clear();
        }
    }
    flush(&mut current, &mut units);
    units
}

/// A line is structural iff its first token (up to `:` or whitespace) is a
/// THEORY/BEGIN/END/IMPORTING/EXPORTING/ASSUMING keyword, or it is a
/// `name: THEORY` header.
fn is_structural_line(trimmed: &str) -> bool {
    let upper_first = first_token(trimmed).to_ascii_uppercase();
    if STRUCTURAL_KEYWORDS.contains(&upper_first.as_str()) {
        return true;
    }
    // `theory_name: THEORY [params]` header line.
    if let Some((_name, after)) = split_at_top_colon(trimmed) {
        let after_first = first_token(after.trim()).to_ascii_uppercase();
        if after_first == "THEORY" {
            return true;
        }
    }
    false
}

/// Heuristic: this line opens a new top-level declaration if it has the
/// shape `ident …:` (an identifier, optional argument list, then a
/// top-level `:`) and is not a continuation of a previous declaration.
fn starts_new_declaration(trimmed: &str) -> bool {
    let first = first_token(trimmed);
    if !is_ident_token(first) {
        return false;
    }
    split_at_top_colon(trimmed).is_some()
}

/// Parse a single declaration unit into a [`PvsDecl`], or `None` if it is
/// not a recognisable declaration.
fn parse_declaration_unit(unit: &str) -> Option<PvsDecl> {
    let unit = unit.trim();
    if unit.is_empty() {
        return None;
    }
    // Drop a trailing `;` if present.
    let unit = unit.strip_suffix(';').unwrap_or(unit).trim();
    let (name_part, body) = split_at_top_colon(unit)?;
    let name_part = name_part.trim();
    let body = body.trim();
    if name_part.is_empty() || body.is_empty() {
        return None;
    }
    // The declared name is the leading identifier; an argument list `(…)` may
    // follow it before the colon.
    let name = first_token(name_part);
    if !is_ident_token(name) {
        return None;
    }
    // Skip if the name token is itself a reserved/structural keyword.
    if STRUCTURAL_KEYWORDS.contains(&name.to_ascii_uppercase().as_str()) {
        return None;
    }
    let args = arg_list_after_name(name_part);

    // Classify by the leading token of the body.
    let body_first = first_token(body);
    let body_first_upper = body_first.to_ascii_uppercase();

    // Type declaration: `TYPE`, `TYPE+`, or `TYPE = def`.
    if body_first_upper == "TYPE" || body_first_upper == "TYPE+" {
        return Some(PvsDecl {
            name: name.to_owned(),
            kind: PvsDeclKind::Type,
            type_repr: "TYPE".to_owned(),
        });
    }

    // Formula declaration: a leading formula keyword.
    if FORMULA_KEYWORDS.contains(&body_first_upper.as_str()) {
        let expr = body[body_first.len()..].trim();
        if expr.is_empty() {
            return None;
        }
        return Some(PvsDecl {
            name: name.to_owned(),
            kind: PvsDeclKind::Formula,
            type_repr: expr.to_owned(),
        });
    }

    // Otherwise a constant/function declaration; the body is its type. Fold
    // any argument-list *types* (stripping the `name:` from each binder) into
    // a leading arrow chain `[t1, t2 -> body]`.
    let type_repr = match args.as_deref().map(arg_types_of) {
        Some(Some(arg_types)) if !arg_types.is_empty() => format!("[{arg_types} -> {body}]"),
        // An argument list we cannot decompose into types ⇒ keep the body
        // alone (still a real type) rather than fabricate.
        _ => body.to_owned(),
    };
    Some(PvsDecl {
        name: name.to_owned(),
        kind: PvsDeclKind::Const,
        type_repr,
    })
}

/// Extract the parenthesised argument list immediately following the name
/// (e.g. `f(x: nat, y: nat)` → `Some("x: nat, y: nat")`). Returns `None`
/// when the name is not followed by a `(`.
fn arg_list_after_name(name_part: &str) -> Option<String> {
    let name = first_token(name_part);
    let rest = name_part[name.len()..].trim_start();
    if !rest.starts_with('(') {
        return None;
    }
    // Find the matching close paren.
    let mut depth = 0i32;
    let mut end = None;
    for (i, ch) in rest.char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    end = Some(i);
                    break;
                }
            }
            _ => {}
        }
    }
    let end = end?;
    let inner = rest[1..end].trim();
    if inner.is_empty() {
        return None;
    }
    Some(inner.to_owned())
}

/// Decompose a PVS argument list into a comma-joined list of argument
/// *types*, dropping each binder name. `x: nat, y: nat` → `nat, nat`;
/// `(x, y: nat)` (shared type) → `nat, nat`. Bindings are split on
/// top-level commas; the type of each group is the text after its `:`. A
/// group with no `:` (just a bare type, e.g. `nat`) contributes that type
/// directly. Returns `None` if any group is empty.
///
/// PVS allows a group `x, y: nat` to declare two arguments of the same
/// type; we expand it so the resulting arrow chain has the right arity.
fn arg_types_of(args: &str) -> Option<String> {
    let mut out: Vec<String> = Vec::new();
    for group in split_top_level_commas(args) {
        let group = group.trim();
        if group.is_empty() {
            return None;
        }
        match split_at_top_colon(group) {
            // `names: type` — one type per name (shared-type expansion).
            Some((names, ty)) => {
                let ty = ty.trim();
                if ty.is_empty() {
                    return None;
                }
                let count = names
                    .split(',')
                    .filter(|n| !n.trim().is_empty())
                    .count()
                    .max(1);
                for _ in 0..count {
                    out.push(ty.to_owned());
                }
            }
            // A bare type with no binder name.
            None => out.push(group.to_owned()),
        }
    }
    if out.is_empty() {
        return None;
    }
    Some(out.join(", "))
}

/// Split `text` on top-level commas (depth 0, outside strings/brackets).
fn split_top_level_commas(text: &str) -> Vec<String> {
    let mut parts = Vec::new();
    let mut depth = 0i32;
    let mut in_string = false;
    let mut escaped = false;
    let mut start = 0usize;
    for (idx, ch) in text.char_indices() {
        if in_string {
            if escaped {
                escaped = false;
            } else if ch == '\\' {
                escaped = true;
            } else if ch == '"' {
                in_string = false;
            }
            continue;
        }
        match ch {
            '"' => in_string = true,
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' if depth > 0 => depth -= 1,
            ',' if depth == 0 => {
                parts.push(text[start..idx].to_owned());
                start = idx + 1;
            }
            _ => {}
        }
    }
    parts.push(text[start..].to_owned());
    parts
}

/// The first whitespace/`(`/`,`/`:`-delimited token of `text`.
fn first_token(text: &str) -> &str {
    let text = text.trim_start();
    let end = text
        .char_indices()
        .find(|(_, c)| c.is_whitespace() || matches!(c, '(' | ',' | ':' | '[' | ']' | ')'))
        .map(|(i, _)| i)
        .unwrap_or(text.len());
    &text[..end]
}

/// A token is a valid declaration identifier if it is non-empty and begins
/// with an alphabetic character or underscore.
fn is_ident_token(tok: &str) -> bool {
    let mut chars = tok.chars();
    match chars.next() {
        Some(c) => c.is_alphabetic() || c == '_',
        None => false,
    }
}

/// Split `text` at its first top-level (depth-0, outside strings) `:` that is
/// not part of `:=` or `::`. Returns `(before, after)` excluding the colon.
fn split_at_top_colon(text: &str) -> Option<(&str, &str)> {
    let colon = find_top_level_colon(text)?;
    Some((&text[..colon], &text[colon + 1..]))
}

fn find_top_level_colon(text: &str) -> Option<usize> {
    let mut paren = 0i32;
    let mut bracket = 0i32;
    let mut brace = 0i32;
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
            '[' => bracket += 1,
            ']' if bracket > 0 => bracket -= 1,
            '{' => brace += 1,
            '}' if brace > 0 => brace -= 1,
            ':' if paren == 0 && bracket == 0 && brace == 0 => {
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

fn find_top_level_semicolon(text: &str) -> Option<usize> {
    let mut paren = 0i32;
    let mut bracket = 0i32;
    let mut brace = 0i32;
    let mut in_string = false;
    let mut escaped = false;
    for (idx, ch) in text.char_indices() {
        if in_string {
            if escaped {
                escaped = false;
            } else if ch == '\\' {
                escaped = true;
            } else if ch == '"' {
                in_string = false;
            }
            continue;
        }
        match ch {
            '"' => in_string = true,
            '(' => paren += 1,
            ')' if paren > 0 => paren -= 1,
            '[' => bracket += 1,
            ']' if bracket > 0 => bracket -= 1,
            '{' => brace += 1,
            '}' if brace > 0 => brace -= 1,
            ';' if paren == 0 && bracket == 0 && brace == 0 => return Some(idx),
            _ => {}
        }
    }
    None
}

// ---------------------------------------------------------------------------
// PVS type-expression parser → FlatExpr tree.
//
// Mirrors the Agda type parser: a small recursive-descent parser over a token
// stream producing Pi / Const / App / BVar / Sort nodes. It is deliberately
// conservative — anything it does not understand makes it return `None`, and
// the caller skips the declaration (never a sort(0) stub).
//
// PVS surface notes handled here:
//   * function types are written `[A -> B]` and `[A, B -> C]` (a tuple domain
//     `A, B` curried into `A -> B -> C`);
//   * `[A, B]` (no arrow) is a product type — modelled as an application of a
//     product head over the components (conservative but a real tree);
//   * dependent bindings `(x: T): U` are folded into arrows by the caller;
//   * `TYPE` is the type universe (a sort);
//   * `bool` is the propositional type; everything else alphabetic is a
//     Const reference; numerals are nat literals.
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
    LBracket,
    RBracket,
    Arrow,
    Comma,
    Colon,
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
            out.push(Tok::Arrow);
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
            '[' => {
                out.push(Tok::LBracket);
                i += 1;
                continue;
            }
            ']' => {
                out.push(Tok::RBracket);
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
            while i < chars.len() && is_ident_continue(chars[i]) {
                i += 1;
            }
            let id: String = chars[start..i].iter().collect();
            out.push(Tok::Ident(id));
            continue;
        }
        // Unknown character (a stray operator glyph we do not model). Return
        // what we have; the parser treats a premature/incomplete end as a
        // failure and the caller skips.
        return out;
    }
    out
}

fn is_ident_start(ch: char) -> bool {
    ch.is_alphabetic() || ch == '_'
}

/// PVS identifiers accept alphanumerics, `_`, `?` (predicate suffix), and
/// `.` for qualified theory references.
fn is_ident_continue(ch: char) -> bool {
    ch.is_alphanumeric() || matches!(ch, '_' | '?' | '.')
}

/// Recognise a PVS sort/universe atom. `TYPE` is the type universe; `bool`
/// is the propositional sort. Everything else alphabetic is a user constant.
fn sort_for_atom(name: &str) -> Option<u32> {
    match name {
        "TYPE" | "TYPE+" => Some(SORT_TYPE),
        "bool" | "boolean" => Some(SORT_PROP),
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

    /// `type := arrow` — top level. A function-type bracket `[dom -> cod]`
    /// is handled inside `parse_atom`/`parse_bracket`.
    fn parse_type(&mut self) -> Option<u32> {
        self.parse_arrow()
    }

    /// `arrow := app (-> arrow)?` — right-associative. `A -> B` ≡
    /// `(_ : A) -> B`.
    fn parse_arrow(&mut self) -> Option<u32> {
        let lhs = self.parse_app()?;
        if !self.eat(&Tok::Arrow) {
            return Some(lhs);
        }
        self.bound.push("_".into());
        let rhs = self.parse_arrow();
        self.bound.pop();
        let rhs = rhs?;
        self.add(FlatExpr::pi(BINDER_DEFAULT, lhs, rhs))
    }

    /// Left-associative application: `f(a)(b)` and juxtaposition `f a`.
    /// PVS application uses parentheses, e.g. `list[nat]` (subscript) and
    /// `f(x)`. We treat any following atom as an argument.
    fn parse_app(&mut self) -> Option<u32> {
        let mut head = self.parse_atom()?;
        while matches!(
            self.peek(),
            Some(Tok::Ident(_) | Tok::Nat(_) | Tok::LParen | Tok::LBracket)
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
            Tok::LBracket => self.parse_bracket(),
            Tok::Nat(n) => {
                self.bump();
                self.add(FlatExpr::lit_nat(n))
            }
            Tok::Ident(name) => {
                self.bump();
                self.emit_name(&name)
            }
            // Arrows / commas / closers in atom position are not valid.
            _ => None,
        }
    }

    /// Parse a bracketed type: `[dom -> cod]` (function), `[d1, d2 -> cod]`
    /// (curried multi-arg function), or `[a, b]` (product). The brackets are
    /// consumed; on a malformed bracket we fail (caller skips).
    fn parse_bracket(&mut self) -> Option<u32> {
        if !self.eat(&Tok::LBracket) {
            return None;
        }
        // Parse a comma-separated list of components.
        let mut components = Vec::new();
        components.push(self.parse_arrow()?);
        while self.eat(&Tok::Comma) {
            components.push(self.parse_arrow()?);
        }
        if self.eat(&Tok::Arrow) {
            // Function type: components are the (curried) domains, then the
            // codomain after the arrow.
            let cod = self.parse_arrow()?;
            if !self.eat(&Tok::RBracket) {
                return None;
            }
            // Curry: [d1, d2 -> cod] ≡ d1 -> d2 -> cod. Build right-to-left.
            // (Domains are non-dependent here, so the anonymous binder count
            // is captured by pushing/popping `_` is unnecessary — domain
            // types reference no outer binder introduced by these arrows.)
            let mut acc = cod;
            for dom in components.iter().rev() {
                acc = self.add(FlatExpr::pi(BINDER_DEFAULT, *dom, acc))?;
            }
            Some(acc)
        } else {
            // Product/tuple type `[a, b, …]`. Model as `Tuple a b …`: a
            // Const head applied to each component — a real, non-stub tree.
            if !self.eat(&Tok::RBracket) {
                return None;
            }
            let head_idx = self.writer.add_string("PVS.tuple");
            let mut acc = self.add(FlatExpr::const_ref(head_idx, NO_LEVELS))?;
            for comp in components {
                acc = self.add(FlatExpr::app(acc, comp))?;
            }
            Some(acc)
        }
    }

    fn emit_name(&mut self, name: &str) -> Option<u32> {
        // PVS universe / sort atoms.
        if let Some(sort) = sort_for_atom(name) {
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

/// Parse a PVS type-expression string into `writer`, returning the root
/// expression index. Returns `None` on parse failure or empty input;
/// callers must treat that as "skip this declaration", never as a licence to
/// emit a placeholder. On success the entire token stream must be consumed
/// (a trailing unparsed remainder is a failure).
pub(crate) fn parse_pvs_type(src: &str, writer: &mut ShardWriter) -> Option<u32> {
    let toks = lex(src);
    if toks.is_empty() {
        return None;
    }
    let mut p = Parser::new(toks, writer);
    let root = p.parse_type()?;
    if p.pos != p.toks.len() {
        // Unconsumed tokens mean the type contained a construct we do not
        // model. Skip it rather than emit a partial/placeholder tree.
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
    fn parse_pvs_file_extracts_decls_skipping_structure_and_comments() {
        let content = "\
% a small theory
example: THEORY
BEGIN
  IMPORTING naturals

  T: TYPE

  f: [nat -> nat]   % a function constant

  g(x: nat): nat

  c: nat

  l: LEMMA p
END example
";
        let decls = parse_pvs_file(content, "example.pvs");
        let names: Vec<&str> = decls.iter().map(|d| d.name.as_str()).collect();
        assert_eq!(names, vec!["T", "f", "g", "c", "l"]);
        assert_eq!(decls[0].kind, PvsDeclKind::Type);
        assert_eq!(decls[1].kind, PvsDeclKind::Const);
        assert_eq!(decls[1].type_repr, "[nat -> nat]");
        assert_eq!(decls[2].kind, PvsDeclKind::Const);
        // The arg list is folded into a leading arrow chain.
        assert_eq!(decls[2].type_repr, "[nat -> nat]");
        assert_eq!(decls[3].kind, PvsDeclKind::Const);
        assert_eq!(decls[3].type_repr, "nat");
        assert_eq!(decls[4].kind, PvsDeclKind::Formula);
        assert_eq!(decls[4].type_repr, "p");
    }

    #[test]
    fn write_pvs_shard_emits_real_types_not_litstr_or_sort0() {
        let decls = vec![
            PvsDecl {
                name: "T".into(),
                kind: PvsDeclKind::Type,
                type_repr: "TYPE".into(),
            },
            PvsDecl {
                name: "f".into(),
                kind: PvsDeclKind::Const,
                type_repr: "[nat -> nat]".into(),
            },
            PvsDecl {
                name: "l".into(),
                kind: PvsDeclKind::Formula,
                type_repr: "p".into(),
            },
        ];
        let mut w = ShardWriter::new();
        let written = write_pvs_shard(&decls, &mut w);
        assert_eq!(written, 3, "all three decls must be written");
        // Real trees ⇒ more exprs than constants (the no-stub signature).
        assert!(
            w.expr_count() > w.constant_count(),
            "expected expr_count ({}) > constant_count ({})",
            w.expr_count(),
            w.constant_count()
        );
    }

    #[test]
    fn parse_pvs_type_function_bracket_builds_pi() {
        let mut w = ShardWriter::new();
        let root = parse_pvs_type("[nat -> nat]", &mut w).expect("parse");
        // Const(nat) [shared], Pi.
        assert!(w.expr_count() >= 2, "expected a real Pi tree");
        // Root is the Pi node.
        assert_eq!(root, w.expr_count() as u32 - 1);
        let ss = strings(&w);
        assert!(ss.iter().any(|s| s == "nat"), "nat head missing: {ss:?}");
    }

    #[test]
    fn parse_pvs_type_curried_multi_arg_function() {
        let mut w = ShardWriter::new();
        // [nat, nat -> bool] ≡ nat -> nat -> bool.
        let _ = parse_pvs_type("[nat, nat -> bool]", &mut w).expect("parse");
        // Two Pi nodes + Const(nat) + sort(bool).
        assert!(w.expr_count() >= 3, "expected curried Pi chain");
    }

    #[test]
    fn parse_pvs_type_arrow_chain_builds_pis() {
        let mut w = ShardWriter::new();
        let _ = parse_pvs_type("nat -> nat -> bool", &mut w).expect("parse");
        assert!(w.expr_count() >= 3, "expected real tree");
    }

    #[test]
    fn parse_pvs_type_application_nests_left() {
        let mut w = ShardWriter::new();
        // `list[nat]` — a parametric type application.
        let _ = parse_pvs_type("list[nat]", &mut w).expect("parse");
        assert!(w.expr_count() >= 2, "expected an app tree");
    }

    #[test]
    fn empty_and_garbage_return_none() {
        let mut w = ShardWriter::new();
        assert!(parse_pvs_type("", &mut w).is_none());
        assert!(parse_pvs_type("   ", &mut w).is_none());
        // A dangling arrow has no codomain ⇒ incomplete ⇒ None.
        assert!(parse_pvs_type("nat ->", &mut w).is_none());
        // An unclosed bracket is malformed ⇒ None.
        assert!(parse_pvs_type("[nat -> nat", &mut w).is_none());
    }

    #[test]
    fn type_decl_emits_real_sort_expr_not_litstr() {
        // A `T: TYPE` declaration's type is the TYPE universe — a real
        // `sort` FlatExpr node, never a LitStr placeholder and never a free
        // Const referencing the literal "TYPE". The expr arena must hold the
        // sort node; the string table must not gain a "TYPE" entry.
        let decls = vec![PvsDecl {
            name: "T".into(),
            kind: PvsDeclKind::Type,
            type_repr: "TYPE".into(),
        }];
        let mut w = ShardWriter::new();
        let written = write_pvs_shard(&decls, &mut w);
        assert_eq!(written, 1, "the TYPE decl must be written");
        // A real sort node was emitted into the expr arena.
        assert!(w.expr_count() >= 1, "TYPE decl must emit a real sort expr");
        // The universe marker must NOT leak as a free Const string.
        let ss = strings(&w);
        assert!(
            !ss.iter().any(|s| s == "TYPE"),
            "universe marker 'TYPE' leaked into strings {ss:?} — emitted as a \
             Const instead of a sort"
        );
        // The declared name IS recorded (it is a genuine constant name).
        assert!(ss.iter().any(|s| s == "T"), "decl name 'T' missing: {ss:?}");
    }

    #[test]
    fn mixed_shard_has_more_exprs_than_constants() {
        // The refuse-stub invariant for a realistic shard: a mix of type,
        // const, and formula decls yields expr_count > constant_count even
        // after hash-consing, because the const/formula trees contribute
        // distinct Pi/Const/sort nodes.
        let decls = vec![
            PvsDecl {
                name: "T".into(),
                kind: PvsDeclKind::Type,
                type_repr: "TYPE".into(),
            },
            PvsDecl {
                name: "f".into(),
                kind: PvsDeclKind::Const,
                type_repr: "[nat -> bool]".into(),
            },
            PvsDecl {
                name: "g".into(),
                kind: PvsDeclKind::Const,
                type_repr: "[nat, nat -> bool]".into(),
            },
        ];
        let mut w = ShardWriter::new();
        let written = write_pvs_shard(&decls, &mut w);
        assert_eq!(written, 3);
        assert!(
            w.expr_count() > w.constant_count(),
            "expected expr_count ({}) > constant_count ({})",
            w.expr_count(),
            w.constant_count()
        );
    }

    #[test]
    fn formula_with_unparseable_expr_is_skipped_not_stubbed() {
        // A formula whose proposition cannot be parsed must be skipped, not
        // emitted with a placeholder type.
        let decls = vec![PvsDecl {
            name: "bad".into(),
            kind: PvsDeclKind::Formula,
            // A lambda-ish construct with an unsupported glyph the lexer bails
            // on, leaving an unconsumed remainder.
            type_repr: "FORALL (x): x => x".into(),
        }];
        let mut w = ShardWriter::new();
        let written = write_pvs_shard(&decls, &mut w);
        assert_eq!(written, 0, "unparseable formula must be skipped");
        assert_eq!(w.constant_count(), 0, "no constant should be emitted");
    }
}
