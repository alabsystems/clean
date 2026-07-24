// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structured importer for Twelf / LF `.elf` source files.
//!
//! Twelf surface declarations are top-level statements of the form
//! `name : type.` or `name : type = term.`, each terminated by a top-level
//! `.` (a period that is not nested inside `()`/`{}`, not part of a float,
//! and not part of a qualified identifier). This importer scans those
//! statements, takes the head identifier before the first top-level `:` as
//! the NAME, the text between that `:` and an optional top-level `=` as the
//! TYPE, **drops the `= term` body entirely** (`value_idx = NO_VALUE` — LF
//! source carries no proof term we reconstruct), parses each type string
//! into a real structural [`FlatExpr`] tree, and writes one shard per
//! directory via [`write_twelf_shard`].
//!
//! It mirrors the Agda importer ([`crate::agda_source`]): every header is
//! tagged `SourceSystem::Twelf`, `ImportConfidence::Unverified`, and
//! `AXIOMATIZED`, `DeclKind::Axiom`.
//!
//! Like the Agda importer, this is a Level-0/1 **data import**, not a
//! verified elaboration. A statement whose type cannot be parsed into a
//! real tree — or which is headed by a `%` directive (`%infix`, `%name`,
//! `%mode`, `%block`, `%abbrev`, `%theorem`, …) — is **skipped**, never
//! replaced with a `FlatExpr::sort(0)` placeholder (the
//! `structured_importers_refuse_stubs` invariant).
//!
//! LF type/kind formers handled:
//!   * `->`  non-dependent function space ⇒ `Pi` (anonymous binder),
//!   * `<-`  reverse arrow (`B <- A` ≡ `A -> B`) ⇒ flipped `Pi`,
//!   * `{x:A} B` dependent function space ⇒ `Pi` binding `x` (body uses
//!     `BVar`),
//!   * juxtaposition `f a b` ⇒ left-associative `App`,
//!   * `type` ⇒ `sort(1)` (the LF kind of types),
//!   * `kind` ⇒ `sort(0)`.
//!
//! Anything else (a construct we do not model) makes the parser return
//! `None` and the declaration is dropped.

use crate::shard::ShardWriter;
use crate::types::{
    AxiomProfile, ContentDomain, DeclKind, ImportConfidence, MathverseConstantHeader, SourceSystem,
    NO_VALUE,
};

/// A top-level Twelf statement reduced to `name : type_repr` (the optional
/// `= term` body is already dropped).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TwelfDecl {
    /// The declared name: the head identifier before the first top-level
    /// `:`.
    pub name: String,
    /// The raw type text between the top-level `:` and an optional
    /// top-level `=`, with line breaks flattened to single spaces.
    pub type_repr: String,
}

/// Parse the top-level `name : type[ = term].` statements of a Twelf source
/// file.
///
/// What is handled:
///   * `%…` line comments (to end of line) and `%{ … }%` block comments,
///     stripped (to whitespace) before splitting;
///   * top-level statement termination by a `.` that is not nested in
///     `()`/`{}`, not part of a float (`3.14`), and not part of a qualified
///     identifier (`nat.zero`) — tracked via paren/brace depth and adjacency
///     to identifier/digit characters;
///   * `%`-directive statements (`%name`, `%infix`, `%mode`, `%block`,
///     `%abbrev`, `%theorem`, …) are skipped.
///
/// Be conservative: anything not confidently a `name : type` statement is
/// skipped. We never fabricate a declaration.
pub fn parse_twelf_file(content: &str, _filename: &str) -> Vec<TwelfDecl> {
    let logical = strip_comments(content);
    let mut decls = Vec::new();
    for stmt in split_statements(&logical) {
        let stmt = normalize_ws(&stmt);
        if stmt.is_empty() {
            continue;
        }
        // A `%`-directive statement is never a `name : type` declaration.
        if stmt.starts_with('%') {
            continue;
        }
        let Some(colon) = find_top_level_colon(&stmt) else {
            continue;
        };
        let name_part = stmt[..colon].trim();
        let after_colon = &stmt[colon + 1..];
        // The name segment must be a single plain identifier token.
        let Some(name) = single_name(name_part) else {
            continue;
        };
        // Drop the `= term` body: keep only the text up to a top-level `=`.
        let type_part = match find_top_level_eq(after_colon) {
            Some(eq) => &after_colon[..eq],
            None => after_colon,
        };
        let type_repr = normalize_ws(type_part);
        if !type_repr.is_empty() {
            decls.push(TwelfDecl {
                name: name.to_owned(),
                type_repr,
            });
        }
    }
    decls
}

/// Write parsed Twelf declarations to a shard.
///
/// For each decl the `type_repr` string is parsed into a real `FlatExpr`
/// tree via [`parse_twelf_type`]. A decl whose type fails to parse is
/// **skipped** — never replaced with a `sort(0)` placeholder. This is the
/// import-time guarantee that the resulting shard satisfies
/// `expr_count > constant_count`.
///
/// Every header carries `value_idx = NO_VALUE` (LF source has no proof term
/// we reconstruct), `ImportConfidence::Unverified`, and `AXIOMATIZED`.
///
/// Returns the number of declarations actually written.
pub fn write_twelf_shard(decls: &[TwelfDecl], writer: &mut ShardWriter) -> usize {
    let mut written = 0usize;
    for decl in decls {
        let Some(type_idx) = parse_twelf_type(&decl.type_repr, writer) else {
            // Parse failure: skip rather than fall back to sort(0).
            continue;
        };
        let name_idx = writer.add_string(&decl.name);
        writer.add_constant(MathverseConstantHeader {
            name_idx,
            type_idx,
            value_idx: NO_VALUE,
            source_system: SourceSystem::Twelf as u8,
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

/// Strip Twelf comments — `%…` line comments (to end of line) and
/// `%{ … }%` block comments — replacing them with whitespace so that
/// statement boundaries (`.`) and column structure are preserved.
///
/// A `%` opens a line comment unless immediately followed by `{` (block
/// comment open). Block comments do **not** nest in Twelf; the first `}%`
/// closes. Note: `%name`, `%infix`, … directives are *not* comments — a `%`
/// followed by an identifier letter is a directive and is preserved here
/// (and skipped later as a whole statement). We only treat `%` as a line
/// comment when it is followed by whitespace, EOL, or another `%`, matching
/// Twelf's `% ` comment convention.
fn strip_comments(content: &str) -> String {
    let chars: Vec<char> = content.chars().collect();
    let mut out = String::with_capacity(content.len());
    let mut i = 0usize;
    while i < chars.len() {
        let ch = chars[i];
        let next = chars.get(i + 1).copied();
        // Block comment `%{ … }%`.
        if ch == '%' && next == Some('{') {
            out.push(' ');
            out.push(' ');
            i += 2;
            while i < chars.len() {
                if chars[i] == '}' && chars.get(i + 1) == Some(&'%') {
                    out.push(' ');
                    out.push(' ');
                    i += 2;
                    break;
                }
                out.push(if chars[i] == '\n' { '\n' } else { ' ' });
                i += 1;
            }
            continue;
        }
        // Line comment: `%` followed by whitespace / EOL / `%`. A `%`
        // followed by an identifier character (e.g. `%name`) is a directive,
        // preserved so the statement can be skipped wholesale.
        if ch == '%' && (matches!(next, None | Some('%')) || next.is_some_and(char::is_whitespace))
        {
            while i < chars.len() && chars[i] != '\n' {
                out.push(' ');
                i += 1;
            }
            continue;
        }
        out.push(ch);
        i += 1;
    }
    out
}

/// Split logical (comment-stripped) text into top-level statements at each
/// top-level `.`. A `.` terminates a statement only when it is at paren/brace
/// depth 0, is not flanked by identifier/digit characters (so `nat.zero`
/// qualified ids and `3.14` floats stay intact), and is not part of a `..`
/// run. The terminating `.` is dropped from each returned statement.
fn split_statements(text: &str) -> Vec<String> {
    let chars: Vec<char> = text.chars().collect();
    let mut stmts = Vec::new();
    let mut cur = String::new();
    let mut paren = 0i32;
    let mut brace = 0i32;
    let mut i = 0usize;
    while i < chars.len() {
        let ch = chars[i];
        match ch {
            '(' => paren += 1,
            ')' if paren > 0 => paren -= 1,
            '{' => brace += 1,
            '}' if brace > 0 => brace -= 1,
            _ => {}
        }
        if ch == '.' && paren == 0 && brace == 0 {
            let prev = i.checked_sub(1).and_then(|p| chars.get(p)).copied();
            let next = chars.get(i + 1).copied();
            let glued_id = prev.is_some_and(is_id_char) && next.is_some_and(is_id_char);
            let dot_run = prev == Some('.') || next == Some('.');
            if !glued_id && !dot_run {
                stmts.push(std::mem::take(&mut cur));
                i += 1;
                continue;
            }
        }
        cur.push(ch);
        i += 1;
    }
    if !cur.trim().is_empty() {
        stmts.push(cur);
    }
    stmts
}

/// Characters that may appear inside a Twelf identifier (used to detect a
/// `.` that is glued into a qualified id or a float).
fn is_id_char(ch: char) -> bool {
    ch.is_alphanumeric() || matches!(ch, '_' | '\'' | '-' | '/' | '+' | '*')
}

/// Find the first top-level `:` (depth-0, not `:=`) in `text`.
fn find_top_level_colon(text: &str) -> Option<usize> {
    let mut paren = 0i32;
    let mut brace = 0i32;
    let chars: Vec<(usize, char)> = text.char_indices().collect();
    for (k, &(idx, ch)) in chars.iter().enumerate() {
        match ch {
            '(' => paren += 1,
            ')' if paren > 0 => paren -= 1,
            '{' => brace += 1,
            '}' if brace > 0 => brace -= 1,
            ':' if paren == 0 && brace == 0 => {
                let next = chars.get(k + 1).map(|(_, c)| *c);
                if next != Some('=') {
                    return Some(idx);
                }
            }
            _ => {}
        }
    }
    None
}

/// Find the first top-level `=` (depth-0, not `==`, not preceded by `:` —
/// `:=` was already excluded by the colon scan) in `text`.
fn find_top_level_eq(text: &str) -> Option<usize> {
    let mut paren = 0i32;
    let mut brace = 0i32;
    let chars: Vec<(usize, char)> = text.char_indices().collect();
    for (k, &(idx, ch)) in chars.iter().enumerate() {
        match ch {
            '(' => paren += 1,
            ')' if paren > 0 => paren -= 1,
            '{' => brace += 1,
            '}' if brace > 0 => brace -= 1,
            '=' if paren == 0 && brace == 0 => {
                let next = chars.get(k + 1).map(|(_, c)| *c);
                let prev = k.checked_sub(1).and_then(|p| chars.get(p)).map(|(_, c)| *c);
                if next != Some('=') && prev != Some('=') {
                    return Some(idx);
                }
            }
            _ => {}
        }
    }
    None
}

/// The name segment must be a single plain identifier token (no spaces, no
/// brackets, no operator glyphs). Returns that token or `None`.
fn single_name(name_part: &str) -> Option<&str> {
    let mut it = name_part.split_whitespace();
    let tok = it.next()?;
    if it.next().is_some() {
        return None;
    }
    if !is_valid_name(tok) {
        return None;
    }
    Some(tok)
}

/// A declared name must be a non-empty identifier with no bracket / arrow /
/// colon / equals glyphs.
fn is_valid_name(tok: &str) -> bool {
    !tok.is_empty()
        && tok
            .chars()
            .all(|c| is_id_char(c) || matches!(c, '.' | '!' | '?' | '^' | '~' | '#' | '@'))
        && tok.chars().any(|c| c.is_alphanumeric() || c == '_')
}

fn normalize_ws(text: &str) -> String {
    text.split_whitespace().collect::<Vec<_>>().join(" ")
}

// ---------------------------------------------------------------------------
// Twelf / LF type-expression parser → FlatExpr tree.
//
// Mirrors the Agda parser: a small recursive-descent parser over a token
// stream producing Pi / Const / App / BVar / Sort nodes. It is deliberately
// conservative — anything it does not understand makes it return `None`, and
// the caller skips the declaration (never a sort(0) stub).
//
// Grammar (lowest to highest precedence):
//   type   := arrow
//   arrow  := app ( ('->' arrow) | ('<-' arrow) )?         right-assoc `->`
//           | '{' ident ':' type '}' arrow                 dependent Pi
//   app    := atom atom*                                   left-assoc
//   atom   := ident | '(' type ')' | 'type' | 'kind'
// ---------------------------------------------------------------------------

use clean_kernel::flat::FlatExpr;

const NO_LEVELS: u32 = u32::MAX;
const BINDER_DEFAULT: u8 = 0;
const SORT_TYPE: u32 = 1; // `type`  — the LF kind of object-level types
const SORT_KIND: u32 = 0; // `kind`  — the top of the LF hierarchy

#[derive(Debug, Clone, PartialEq, Eq)]
enum Tok {
    Ident(String),
    LParen,
    RParen,
    LBrace,
    RBrace,
    Colon,
    Arrow,    // ->
    RevArrow, // <-
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
        if ch == '-' && chars.get(i + 1) == Some(&'>') {
            out.push(Tok::Arrow);
            i += 2;
            continue;
        }
        if ch == '<' && chars.get(i + 1) == Some(&'-') {
            out.push(Tok::RevArrow);
            i += 2;
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
            ':' => {
                out.push(Tok::Colon);
                i += 1;
                continue;
            }
            _ => {}
        }
        // `[x:A] M` LF lambda is a *term* former, not a type former; `\` and
        // other unknown glyphs likewise. Bail so the caller skips: the
        // returned partial stream leaves an unconsumable remainder.
        if matches!(ch, '[' | ']' | '\\') {
            return out;
        }
        if is_lf_ident_start(ch) {
            let start = i;
            while i < chars.len() && is_lf_ident_continue(chars[i]) {
                i += 1;
            }
            let id: String = chars[start..i].iter().collect();
            out.push(Tok::Ident(id));
            continue;
        }
        // Unknown character — we cannot parse this type faithfully. Return
        // what we have; the parser treats a premature/garbled end as failure.
        return out;
    }
    out
}

/// LF identifiers are liberal: any non-whitespace, non-reserved character
/// sequence. We accept the common shape used by Twelf signatures.
fn is_lf_ident_start(ch: char) -> bool {
    !ch.is_whitespace()
        && !matches!(
            ch,
            '(' | ')' | '{' | '}' | '[' | ']' | ':' | '.' | '%' | '\\'
        )
}

fn is_lf_ident_continue(ch: char) -> bool {
    // Stop an identifier at characters that begin another token. `-` is
    // allowed inside ids (Twelf permits `is-true`) but a `->`/`<-` arrow is
    // lexed before we get here, so a lone trailing `-` only stays glued when
    // not followed by `>`. We keep it simple: same set as start, minus the
    // arrow-introducing ambiguity handled in `lex`.
    is_lf_ident_start(ch) && ch != '<'
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

    /// `type := dependent-Pi | arrow`.
    fn parse_type(&mut self) -> Option<u32> {
        if matches!(self.peek(), Some(Tok::LBrace)) {
            return self.parse_dependent_pi();
        }
        self.parse_arrow()
    }

    /// `{x : A} B` ⇒ `Pi(x : A, B)`, binding `x` in `B`.
    fn parse_dependent_pi(&mut self) -> Option<u32> {
        self.bump(); // `{`
        let name = match self.bump()? {
            Tok::Ident(s) => s,
            _ => return None,
        };
        if !self.eat(&Tok::Colon) {
            return None;
        }
        let dom = self.parse_type()?;
        if !self.eat(&Tok::RBrace) {
            return None;
        }
        self.bound.push(name);
        let body = self.parse_type();
        self.bound.pop();
        let body = body?;
        self.add(FlatExpr::pi(BINDER_DEFAULT, dom, body))
    }

    /// `arrow := app ( '->' type | '<-' type )?` — right-associative `->`.
    /// `A <- B` is the reverse arrow `B -> A`; we build the flipped `Pi`.
    fn parse_arrow(&mut self) -> Option<u32> {
        let lhs = self.parse_app()?;
        match self.peek() {
            Some(Tok::Arrow) => {
                self.bump();
                // `A -> B` ≡ `(_ : A) -> B`. Push an anonymous binder so de
                // Bruijn indices in `B` account for the new binding level.
                self.bound.push("_".into());
                let rhs = self.parse_type();
                self.bound.pop();
                let rhs = rhs?;
                self.add(FlatExpr::pi(BINDER_DEFAULT, lhs, rhs))
            }
            Some(Tok::RevArrow) => {
                self.bump();
                // `B <- A` ≡ `A -> B`: the RHS `A` is the domain, `lhs` (`B`)
                // is the codomain. The domain does not bind a name visible in
                // `B`, but we still push an anonymous binder so any further
                // arrows in `B` keep correct de Bruijn levels.
                let dom = self.parse_app()?;
                self.bound.push("_".into());
                let cod = self.continue_arrow(lhs);
                self.bound.pop();
                let cod = cod?;
                self.add(FlatExpr::pi(BINDER_DEFAULT, dom, cod))
            }
            _ => Some(lhs),
        }
    }

    /// After a `<-`, the original `lhs` may itself be the head of another
    /// `<-`/`->` chain (`A <- B <- C` ≡ `C -> B -> A`). We continue parsing
    /// trailing reverse/forward arrows whose domains accumulate onto `lhs`.
    /// For simplicity and faithfulness we only fold one more level here; a
    /// remaining unconsumed arrow makes `parse_twelf_type`'s fully-consumed
    /// check fail and the decl is skipped (never fabricated).
    fn continue_arrow(&mut self, head: u32) -> Option<u32> {
        match self.peek() {
            Some(Tok::Arrow) => {
                self.bump();
                self.bound.push("_".into());
                let rhs = self.parse_type();
                self.bound.pop();
                let rhs = rhs?;
                self.add(FlatExpr::pi(BINDER_DEFAULT, head, rhs))
            }
            Some(Tok::RevArrow) => {
                self.bump();
                let dom = self.parse_app()?;
                self.bound.push("_".into());
                let cod = self.continue_arrow(head);
                self.bound.pop();
                let cod = cod?;
                self.add(FlatExpr::pi(BINDER_DEFAULT, dom, cod))
            }
            _ => Some(head),
        }
    }

    /// Left-associative application: `f a b` ≡ `((f a) b)`.
    fn parse_app(&mut self) -> Option<u32> {
        let mut head = self.parse_atom()?;
        while matches!(self.peek(), Some(Tok::Ident(_) | Tok::LParen)) {
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
            Tok::Ident(name) => {
                self.bump();
                self.emit_name(&name)
            }
            // Brackets / arrows / colons in atom position are not valid.
            _ => None,
        }
    }

    fn emit_name(&mut self, name: &str) -> Option<u32> {
        // LF sort atoms: `type` (the kind of object-level types) ⇒ sort(1),
        // `kind` (the top of the hierarchy) ⇒ sort(0). Every other name is a
        // user constant or a bound variable.
        match name {
            "type" => return self.add(FlatExpr::sort(SORT_TYPE)),
            "kind" => return self.add(FlatExpr::sort(SORT_KIND)),
            _ => {}
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

/// Parse a Twelf / LF type-expression string into `writer`, returning the
/// root expression index. Returns `None` on parse failure or empty input;
/// callers must treat that as "skip this declaration", never as a licence to
/// emit a placeholder. On success the entire token stream must be consumed (a
/// trailing unparsed remainder is a failure).
pub(crate) fn parse_twelf_type(src: &str, writer: &mut ShardWriter) -> Option<u32> {
    let toks = lex(src);
    if toks.is_empty() {
        return None;
    }
    let mut p = Parser::new(toks, writer);
    let root = p.parse_type()?;
    if p.pos != p.toks.len() {
        // Unconsumed tokens mean the type contained a construct we do not
        // model (e.g. an LF `[x:A] M` lambda term, leftover arrows). Skip it.
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
    fn parse_twelf_file_extracts_decls_dropping_bodies_and_directives() {
        let content = "\
%{ a block comment
   spanning lines }%
nat : type.
z : nat.
s : nat -> nat.
%name nat N.        % a directive plus a line comment
foo : {x:nat} foo x.
plus : nat -> nat -> nat = z.
";
        let decls = parse_twelf_file(content, "nat.elf");
        let names: Vec<&str> = decls.iter().map(|d| d.name.as_str()).collect();
        // The `%name` directive statement is dropped; `plus`'s `= z` body is
        // dropped but its type is kept.
        assert_eq!(names, vec!["nat", "z", "s", "foo", "plus"]);
        assert_eq!(decls[0].type_repr, "type");
        assert_eq!(decls[2].type_repr, "nat -> nat");
        assert_eq!(decls[3].type_repr, "{x:nat} foo x");
        assert_eq!(
            decls[4].type_repr, "nat -> nat -> nat",
            "the `= z` body must be dropped from `plus`"
        );
    }

    #[test]
    fn directive_statement_is_skipped() {
        let content = "%infix none 5 plus.\nnat : type.\n";
        let decls = parse_twelf_file(content, "t.elf");
        let names: Vec<&str> = decls.iter().map(|d| d.name.as_str()).collect();
        assert_eq!(names, vec!["nat"], "the %infix line must be skipped");
    }

    #[test]
    fn qualified_id_and_float_do_not_split_statements() {
        // A `.` glued inside `nat.zero` or `3.14` must NOT end the statement.
        let content = "c : nat.zero -> foo 3.14.\n";
        let decls = parse_twelf_file(content, "t.elf");
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].name, "c");
        assert_eq!(decls[0].type_repr, "nat.zero -> foo 3.14");
    }

    #[test]
    fn write_twelf_shard_emits_real_types_not_litstr_or_sort0() {
        let decls = parse_twelf_file(
            "nat : type.\nz : nat.\ns : nat -> nat.\nfoo : {x:nat} foo x.\n",
            "nat.elf",
        );
        let mut w = ShardWriter::new();
        let written = write_twelf_shard(&decls, &mut w);
        assert_eq!(written, 4, "all four decls must be written");
        // Real trees ⇒ more exprs than constants (the no-stub signature).
        assert!(
            w.expr_count() > w.constant_count(),
            "expected expr_count ({}) > constant_count ({})",
            w.expr_count(),
            w.constant_count()
        );
        // The dependent binder `x` must resolve to a BVar, not leak as a
        // free Const string.
        let ss = strings(&w);
        assert!(
            !ss.iter().any(|s| s == "x"),
            "binder name 'x' leaked into strings {ss:?} — dependent {{x:A}} \
             not parsed as a Pi/BVar"
        );
    }

    #[test]
    fn type_atom_is_sort_not_litstr() {
        // `nat : type.` ⇒ the type `type` must be `sort(1)`, a real node, and
        // `type` must NOT appear as a string-table entry (no LitStr stub).
        let mut w = ShardWriter::new();
        let root = parse_twelf_type("type", &mut w).expect("parse `type`");
        assert_eq!(w.expr_count(), 1, "exactly one sort node");
        assert_eq!(root, 0);
        let ss = strings(&w);
        assert!(
            !ss.iter().any(|s| s == "type"),
            "`type` leaked as a string: {ss:?} (should be sort(1))"
        );
    }

    #[test]
    fn arrow_chain_builds_pis() {
        let mut w = ShardWriter::new();
        let root = parse_twelf_type("nat -> nat -> nat", &mut w).expect("parse");
        // Const(nat) [shared], inner Pi, outer Pi.
        assert!(w.expr_count() >= 3, "expected real Pi tree");
        assert_eq!(root, w.expr_count() as u32 - 1, "root is the outer Pi");
        let ss = strings(&w);
        assert!(ss.iter().any(|s| s == "nat"), "nat head missing: {ss:?}");
    }

    #[test]
    fn dependent_pi_resolves_binder_to_bvar() {
        // `{x:nat} foo x`: the `x` in the body must be a BVar, so `x` must
        // NOT appear in the string table.
        let mut w = ShardWriter::new();
        let _ = parse_twelf_type("{x:nat} foo x", &mut w).expect("parse");
        let ss = strings(&w);
        assert!(!ss.iter().any(|s| s == "x"), "x leaked as Const: {ss:?}");
        assert!(ss.iter().any(|s| s == "foo"), "foo missing: {ss:?}");
        assert!(ss.iter().any(|s| s == "nat"), "nat missing: {ss:?}");
    }

    #[test]
    fn reverse_arrow_flips_to_pi() {
        // `b <- a` ≡ `a -> b`: domain `a`, codomain `b`. Both appear as
        // Consts and a Pi joins them.
        let mut w = ShardWriter::new();
        let _ = parse_twelf_type("b <- a", &mut w).expect("parse reverse arrow");
        assert!(w.expr_count() >= 3, "expected Const a, Const b, Pi");
        let ss = strings(&w);
        assert!(ss.iter().any(|s| s == "a"), "a missing: {ss:?}");
        assert!(ss.iter().any(|s| s == "b"), "b missing: {ss:?}");
    }

    #[test]
    fn application_nests_left() {
        let mut w = ShardWriter::new();
        let _ = parse_twelf_type("vec a n", &mut w).expect("parse");
        // Const(vec), Const(a), App, Const(n), App.
        assert!(w.expr_count() >= 4, "expected real app tree");
    }

    #[test]
    fn empty_and_lambda_return_none() {
        let mut w = ShardWriter::new();
        assert!(parse_twelf_type("", &mut w).is_none());
        assert!(parse_twelf_type("   ", &mut w).is_none());
        // An LF `[x:A] M` lambda is a term, out of scope; the `[` aborts the
        // lex and leaves an unconsumable remainder ⇒ None (skip, not stub).
        assert!(parse_twelf_type("[x:nat] x", &mut w).is_none());
    }
}
