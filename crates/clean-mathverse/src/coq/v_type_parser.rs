// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Coq/Gallina type-signature parser → `FlatExpr` tree.
//!
//! Translates a Gallina **type expression** string (the text between the
//! top-level `:` and the terminating `.`/`:=`/`Proof` in a
//! `Theorem`/`Lemma`/`Definition`/etc) into a structural [`FlatExpr`]
//! tree written into a [`ShardWriter`]. Returns the index of the root
//! expression on success.
//!
//! Scope: the **structural skeleton** of Gallina type expressions —
//! dependent products (`forall x : T, body`), function arrows
//! (`T -> body`), application (`f a b`), parenthesisation, identifier
//! references, and `Prop`/`Set`/`Type` universe atoms (including the
//! `Type@{...}` level-annotation form). Binders may appear bracketed as
//! `(x : T)` (explicit), `{x : T}` (implicit), or `[x : T]` (generalising
//! / typeclass). The implicitness is recorded on the emitted Pi binder
//! info but does not otherwise change the tree shape.
//!
//! Out of scope (parser returns `None` rather than emit fake data):
//! `match`, `fix`, `let`, `if`/`then`/`else`, proof terms, notation, and
//! anything else that is not a plain type former. When parsing fails the
//! calling importer **skips** the declaration rather than emitting a
//! `sort(0)` placeholder.
//!
//! Universe mapping (documented, not verified): `Prop` → `sort(0)`;
//! `Set` and `Type` → `sort(1)`. Gallina's universe-polymorphic
//! `Type@{u}` / `Type@{u v}` level annotations are consumed and discarded
//! — re-elaborating universe instantiation belongs to the kernel
//! pipeline, not this Level-0/1 data importer.
//!
//! This is a data-import translator, NOT a verified elaboration. The
//! resulting shard is tagged `ImportConfidence::Unverified`.
//!
//! The output is a real structural FlatExpr tree: a one-binder `forall`
//! produces multiple FlatExpr nodes (the binder type, the body subterms,
//! the Pi), not one shared placeholder per constant. That makes the
//! resulting shard pass the `expr_count > constant_count` fidelity check.

use clean_kernel::flat::FlatExpr;

use crate::shard::ShardWriter;

/// `const_ref` levels-list sentinel: "this constant carries no explicit
/// universe instantiation".
const NO_LEVELS: u32 = u32::MAX;

/// Binder-info encodings for `FlatExpr::pi` (mirrors the kernel's
/// 0=Default, 1=Implicit, 3=InstImplicit convention).
const BINDER_DEFAULT: u8 = 0;
const BINDER_IMPLICIT: u8 = 1;
const BINDER_INST_IMPLICIT: u8 = 3;

/// `sort(0)` is `Prop`; `sort(1)` covers `Set`/`Type` at the surface.
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
    LBrack,
    RBrack,
    Arrow,
    Comma,
    Colon,
    /// `:>` coercion marker (a `:` immediately followed by `>`).
    ColonGt,
    Forall,
    Underscore,
    /// One of `= < <= > >= + - * /`, stored under a canonical constant
    /// name (`eq`, `lt`, `add`, …) matching Coq's stdlib head symbols.
    Infix(&'static str, u8),
    /// `Type@{...}` universe annotation, already absorbed by the lexer.
    /// The level text is discarded; only its presence is recorded.
    AtBrace,
    Unknown(char),
}

/// Operator precedences, loosely modelled on Coq's notation scopes.
const MUL_PREC: u8 = 70;
const ADD_PREC: u8 = 65;
const REL_PREC: u8 = 50;

fn lex(src: &str) -> Vec<Tok> {
    let bytes: Vec<char> = src.chars().collect();
    let mut out = Vec::new();
    let mut i = 0usize;
    while i < bytes.len() {
        let ch = bytes[i];
        if ch.is_whitespace() {
            i += 1;
            continue;
        }
        // ASCII "->"
        if ch == '-' && bytes.get(i + 1) == Some(&'>') {
            out.push(Tok::Arrow);
            i += 2;
            continue;
        }
        // ":=" terminates a type signature — stop lexing defensively.
        if ch == ':' && bytes.get(i + 1) == Some(&'=') {
            break;
        }
        // ":>" coercion marker.
        if ch == ':' && bytes.get(i + 1) == Some(&'>') {
            out.push(Tok::ColonGt);
            i += 2;
            continue;
        }
        // Multi-char relations: "<=", ">=", "<>".
        if (ch == '<' || ch == '>') && bytes.get(i + 1) == Some(&'=') {
            out.push(Tok::Infix(if ch == '<' { "le" } else { "ge" }, REL_PREC));
            i += 2;
            continue;
        }
        if ch == '<' && bytes.get(i + 1) == Some(&'>') {
            out.push(Tok::Infix("ne", REL_PREC));
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
            '[' => {
                out.push(Tok::LBrack);
                i += 1;
                continue;
            }
            ']' => {
                out.push(Tok::RBrack);
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
            '=' => {
                out.push(Tok::Infix("eq", REL_PREC));
                i += 1;
                continue;
            }
            '<' => {
                out.push(Tok::Infix("lt", REL_PREC));
                i += 1;
                continue;
            }
            '>' => {
                out.push(Tok::Infix("gt", REL_PREC));
                i += 1;
                continue;
            }
            '+' => {
                out.push(Tok::Infix("add", ADD_PREC));
                i += 1;
                continue;
            }
            '-' => {
                out.push(Tok::Infix("sub", ADD_PREC));
                i += 1;
                continue;
            }
            '*' => {
                out.push(Tok::Infix("mul", MUL_PREC));
                i += 1;
                continue;
            }
            '/' => {
                out.push(Tok::Infix("div", MUL_PREC));
                i += 1;
                continue;
            }
            '@' if bytes.get(i + 1) == Some(&'{') => {
                // `Type@{...}` universe annotation. Skip to the matching
                // `}` and emit a single AtBrace marker.
                let mut j = i + 2;
                let mut depth = 1usize;
                while j < bytes.len() && depth > 0 {
                    match bytes[j] {
                        '{' => depth += 1,
                        '}' => depth -= 1,
                        _ => {}
                    }
                    j += 1;
                }
                out.push(Tok::AtBrace);
                i = j;
                continue;
            }
            '_' if !is_ident_continue(bytes.get(i + 1).copied().unwrap_or(' ')) => {
                out.push(Tok::Underscore);
                i += 1;
                continue;
            }
            _ => {}
        }
        if ch.is_ascii_digit() {
            let start = i;
            while i < bytes.len() && bytes[i].is_ascii_digit() {
                i += 1;
            }
            let s: String = bytes[start..i].iter().collect();
            match s.parse::<u64>() {
                Ok(n) => out.push(Tok::Nat(n)),
                Err(_) => out.push(Tok::Unknown(bytes[start])),
            }
            continue;
        }
        if is_ident_start(ch) {
            let start = i;
            while i < bytes.len() && is_ident_continue(bytes[i]) {
                i += 1;
            }
            let id: String = bytes[start..i].iter().collect();
            if id == "forall" {
                out.push(Tok::Forall);
            } else {
                out.push(Tok::Ident(id));
            }
            continue;
        }
        out.push(Tok::Unknown(ch));
        i += 1;
    }
    out
}

fn is_ident_start(ch: char) -> bool {
    ch.is_ascii_alphabetic() || ch == '_'
}

fn is_ident_continue(ch: char) -> bool {
    ch.is_ascii_alphanumeric() || matches!(ch, '_' | '.' | '\'')
}

struct Parser<'w> {
    toks: Vec<Tok>,
    pos: usize,
    writer: &'w mut ShardWriter,
    /// Stack of in-scope binder names, outermost first. A name's de
    /// Bruijn index is `bound.len() - 1 - position`.
    bound: Vec<String>,
    /// Hard cap on emitted exprs per type — guards pathological inputs.
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

    /// After `forall`, parse one or more binder groups followed by `,`
    /// and the body. Each binder name in each group becomes its own Pi.
    ///
    /// Names are pushed onto the scope stack as each group finishes, so a
    /// later group's binder type can mention an earlier group's name
    /// (`(A : Type) (x : A)` resolves correctly).
    fn parse_forall_chain(&mut self) -> Option<u32> {
        let mut binders: Vec<(u8, u32)> = Vec::new();
        let mut pushed = 0usize;
        loop {
            if matches!(self.peek(), Some(Tok::Comma)) {
                self.bump();
                break;
            }
            if self.peek().is_none() {
                for _ in 0..pushed {
                    self.bound.pop();
                }
                return None;
            }
            let group = match self.parse_binder_group(BINDER_DEFAULT) {
                Some(g) => g,
                None => {
                    for _ in 0..pushed {
                        self.bound.pop();
                    }
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
                for _ in 0..pushed {
                    self.bound.pop();
                }
                return None;
            }
        };
        let mut acc = body;
        for (binfo, ty_idx) in binders.iter().rev() {
            acc = self.add(FlatExpr::pi(*binfo, *ty_idx, acc))?;
        }
        for _ in 0..pushed {
            self.bound.pop();
        }
        Some(acc)
    }

    /// Parse one binder group: `(x y : T)`, `{x : T}`, `[x : T]`, or the
    /// bare `x y : T` form Coq accepts after `forall` without brackets.
    /// Returns `(name, binder_info, type_idx)` for each name. Names share
    /// the group's single type expression.
    fn parse_binder_group(&mut self, default_binfo: u8) -> Option<Vec<(String, u8, u32)>> {
        let (close, binfo) = match self.peek() {
            Some(Tok::LParen) => (Some(Tok::RParen), BINDER_DEFAULT),
            Some(Tok::LBrace) => (Some(Tok::RBrace), BINDER_IMPLICIT),
            Some(Tok::LBrack) => (Some(Tok::RBrack), BINDER_INST_IMPLICIT),
            _ => (None, default_binfo),
        };
        if close.is_some() {
            self.bump(); // consume the opening bracket
        }
        let mut names = Vec::new();
        while matches!(self.peek(), Some(Tok::Ident(_)) | Some(Tok::Underscore)) {
            names.push(self.expect_ident()?);
        }
        if names.is_empty() {
            return None;
        }
        // `:>` coercion in a binder is treated like `:` for type purposes.
        let ty = if matches!(self.peek(), Some(Tok::Colon) | Some(Tok::ColonGt)) {
            self.bump();
            self.parse_type()?
        } else {
            // Untyped binder (`forall x, ...`): no annotation available,
            // so we cannot faithfully reconstruct the type. Bail rather
            // than fabricate a placeholder.
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

    /// `arrow := infix (-> arrow)?` — right-associative. Also handles a
    /// leading bracketed binder Pi such as `{A : Type} -> A -> A`, which
    /// Coq treats as `forall {A : Type}, A -> A`.
    fn parse_arrow(&mut self) -> Option<u32> {
        if matches!(self.peek(), Some(Tok::LBrace) | Some(Tok::LBrack)) {
            let group = self.parse_binder_group(BINDER_DEFAULT)?;
            if !self.eat(&Tok::Arrow) {
                return None;
            }
            let binfos_tys: Vec<(u8, u32)> = group.iter().map(|(_, b, t)| (*b, *t)).collect();
            let n = group.len();
            for (name, _, _) in &group {
                self.bound.push(name.clone());
            }
            let body = self.parse_type();
            for _ in 0..n {
                self.bound.pop();
            }
            let body = body?;
            let mut acc = body;
            for (binfo, ty) in binfos_tys.iter().rev() {
                acc = self.add(FlatExpr::pi(*binfo, *ty, acc))?;
            }
            return Some(acc);
        }
        let lhs = self.parse_infix(0)?;
        if !self.eat(&Tok::Arrow) {
            return Some(lhs);
        }
        // `A -> B` ≡ `forall (_ : A), B`. Push an anonymous binder so de
        // Bruijn indices in `B` account for the new binding level.
        self.bound.push("_".into());
        let rhs = self.parse_type();
        self.bound.pop();
        let rhs = rhs?;
        self.add(FlatExpr::pi(BINDER_DEFAULT, lhs, rhs))
    }

    /// Pratt-style precedence climbing for binary infix operators. Each
    /// `op a b` becomes the application `((op a) b)` where `op` is a free
    /// `Const` reference under its canonical Coq head name.
    fn parse_infix(&mut self, min_prec: u8) -> Option<u32> {
        let mut lhs = self.parse_app()?;
        loop {
            let (op, prec) = match self.peek() {
                Some(Tok::Infix(op, prec)) if *prec >= min_prec => (*op, *prec),
                _ => break,
            };
            self.bump();
            // All infix ops here are left-associative.
            let rhs = self.parse_infix(prec + 1)?;
            let op_name = self.writer.add_string(op);
            let op_const = self.add(FlatExpr::const_ref(op_name, NO_LEVELS))?;
            let app1 = self.add(FlatExpr::app(op_const, lhs))?;
            lhs = self.add(FlatExpr::app(app1, rhs))?;
        }
        Some(lhs)
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
            Tok::LBrace | Tok::LBrack => {
                // A bracket in argument position is not a valid atom in a
                // plain type expression; bail rather than misparse.
                None
            }
            Tok::Underscore => {
                self.bump();
                // Coq hole `_` — emit a Prop-sorted placeholder atom.
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
        // Universe atoms.
        match name {
            "Prop" => return self.add(FlatExpr::sort(SORT_PROP)),
            "Set" => return self.add(FlatExpr::sort(SORT_TYPE)),
            "Type" => {
                // Optional `Type@{...}` annotation or `Type u` level arg.
                if matches!(self.peek(), Some(Tok::AtBrace)) {
                    self.bump();
                }
                return self.add(FlatExpr::sort(SORT_TYPE));
            }
            _ => {}
        }
        // Bound variable: innermost binding wins.
        if let Some(pos) = self.bound.iter().rposition(|n| n == name) {
            let depth = self.bound.len() - 1 - pos;
            return self.add(FlatExpr::bvar(depth as u32));
        }
        // Free (ambient / section / library) name → Const reference.
        let name_idx = self.writer.add_string(name);
        self.add(FlatExpr::const_ref(name_idx, NO_LEVELS))
    }
}

/// Parse a Gallina type signature into `writer`, returning the root
/// expression index. Returns `None` on parse failure or empty input;
/// callers must treat that as "skip this declaration", never as a licence
/// to emit a placeholder.
pub(crate) fn parse_coq_v_type(src: &str, writer: &mut ShardWriter) -> Option<u32> {
    let toks = lex(src);
    if toks.is_empty() {
        return None;
    }
    let mut p = Parser::new(toks, writer);
    p.parse_type()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn count_exprs(src: &str) -> (u32, usize) {
        let mut w = ShardWriter::new();
        let before = w.expr_count();
        let root = parse_coq_v_type(src, &mut w).expect("parse");
        let after = w.expr_count();
        (root, after - before)
    }

    fn strings(w: &ShardWriter) -> Vec<String> {
        (0..w.string_count())
            .map(|i| w.string_at(i as u32).to_owned())
            .collect()
    }

    #[test]
    fn test_parse_coq_v_type_arrow_chain_emits_distinct_pis() {
        // `nat -> nat -> Prop` ≡ `forall _, forall _, Prop`. Post-dedup:
        // Const(nat) [shared], sort(0) for Prop, inner Pi, outer Pi.
        let (_, n) = count_exprs("nat -> nat -> Prop");
        assert!(n >= 4, "expected >= 4 unique exprs, got {n}");
    }

    #[test]
    fn test_parse_coq_v_type_forall_pins_exact_tree() {
        // `forall n : nat, n + 0 = n`. We pin the EXACT FlatExpr arena so
        // a reviewer can audit the tree shape and de Bruijn indexing.
        //
        // Build order (post-dedup, indices are arena positions):
        //   0: Const(nat)          binder type of n
        //   1: BVar(0)             the `n` on the LHS of `+`  [shared]
        //   2: LitNat(0)           the `0`
        //   3: Const(add)
        //   4: App(add, n)         = exprs[3] applied to exprs[1]
        //   5: App((add n), 0)
        //   6: Const(eq)
        //   7: App(eq, (n+0))
        //   8: App((eq (n+0)), n)  reuses BVar(0) at idx 1
        //   9: Pi(default, nat, eq-app)
        let mut w = ShardWriter::new();
        let root = parse_coq_v_type("forall n : nat, n + 0 = n", &mut w).expect("parse");
        // Root is the Pi node.
        assert_eq!(w.expr_count(), 10, "exact node count changed: audit tree");
        assert_eq!(root, 9, "root should be the outermost Pi");
        // Binder name `n` must NOT leak as a free Const into the strings.
        let ss = strings(&w);
        assert!(
            !ss.iter().any(|s| s == "n"),
            "binder name 'n' leaked into string table {ss:?} — should be a BVar"
        );
        // Head symbols are interned as Consts.
        assert!(ss.iter().any(|s| s == "add"), "add missing: {ss:?}");
        assert!(ss.iter().any(|s| s == "eq"), "eq missing: {ss:?}");
        assert!(ss.iter().any(|s| s == "nat"), "nat missing: {ss:?}");
    }

    #[test]
    fn test_parse_coq_v_type_arrow_to_prop_tree() {
        // `nat -> nat -> Prop`. Pin exact arena:
        //   0: Const(nat)   [shared by both binders]
        //   1: sort(1)      Prop? no — Prop is sort(0). Recompute below.
        // Prop → sort(0). Build order:
        //   0: Const(nat)
        //   1: sort(0)      Prop body
        //   2: Pi(default, nat, Prop)         inner arrow `nat -> Prop`
        //   3: Pi(default, nat, inner)        outer arrow
        let mut w = ShardWriter::new();
        let root = parse_coq_v_type("nat -> nat -> Prop", &mut w).expect("parse");
        assert_eq!(w.expr_count(), 4, "exact node count changed: audit tree");
        assert_eq!(root, 3, "root should be the outer Pi");
    }

    #[test]
    fn test_parse_coq_v_type_bvar_resolves_not_const() {
        // `forall n : nat, n` — body `n` must be BVar(0), not free Const.
        // ShardWriter seeds the string table with one empty sentinel, so
        // a clean parse leaves exactly 2 strings (sentinel + "nat"). A
        // leaked "n" would make it 3.
        let mut w = ShardWriter::new();
        let _ = parse_coq_v_type("forall n : nat, n", &mut w).expect("parse");
        assert!(w.expr_count() >= 2, "expected nat/BVar/Pi");
        assert_eq!(
            w.string_count(),
            2,
            "binder name 'n' leaked: {:?}",
            strings(&w)
        );
    }

    #[test]
    fn test_parse_coq_v_type_dependent_forall_resolves_binders() {
        // `forall (A : Type) (x : A), x = x`. The `A` in `(x : A)` and the
        // two `x` in `x = x` must resolve to BVars, not Consts.
        let mut w = ShardWriter::new();
        let _ = parse_coq_v_type("forall (A : Type) (x : A), x = x", &mut w).expect("parse");
        let ss = strings(&w);
        assert!(!ss.iter().any(|s| s == "A"), "A leaked: {ss:?}");
        assert!(!ss.iter().any(|s| s == "x"), "x leaked: {ss:?}");
        assert!(ss.iter().any(|s| s == "eq"), "eq missing: {ss:?}");
    }

    #[test]
    fn test_parse_coq_v_type_application_nests_left() {
        // `id A x` ≡ `((id A) x)` — application is left-nested.
        let (_, n) = count_exprs("id A x");
        // Const(id), Const(A), App(id, A), Const(x), App(..., x) = 5.
        assert!(n >= 4, "expected real app tree, got {n}");
    }

    #[test]
    fn test_parse_coq_v_type_implicit_braces_parse() {
        // `forall {A : Type}, A -> A` — implicit binder records binfo 1.
        let (_, n) = count_exprs("forall {A : Type}, A -> A");
        assert!(n >= 3, "expected real tree, got {n}");
    }

    #[test]
    fn test_parse_coq_v_type_set_and_type_map_to_sort_one() {
        // `Set -> Type` — both map to sort(1); the arrow makes one Pi.
        let (_, n) = count_exprs("Set -> Type");
        assert!(n >= 2, "expected sort + Pi, got {n}");
        let mut w = ShardWriter::new();
        let _ = parse_coq_v_type("Set -> Type", &mut w).expect("parse");
        // sort(1) dedups to a single node shared by both Set and Type.
        // Result: sort(1), Pi = 2 unique exprs.
        assert_eq!(w.expr_count(), 2, "Set and Type should share sort(1)");
    }

    #[test]
    fn test_parse_coq_v_type_universe_annotation_absorbed() {
        // `Type@{u} -> Type@{u}` — the `@{u}` must be absorbed, not lexed
        // into a stray identifier `u`.
        let mut w = ShardWriter::new();
        let _ = parse_coq_v_type("Type@{u} -> Type@{u}", &mut w).expect("parse");
        let ss = strings(&w);
        assert!(
            !ss.iter().any(|s| s == "u"),
            "universe level 'u' leaked into strings: {ss:?}"
        );
    }

    #[test]
    fn test_parse_coq_v_type_qualified_name_is_single_const() {
        // `Nat.add x y` — the dotted head is one Const, not three.
        let mut w = ShardWriter::new();
        let _ = parse_coq_v_type("Nat.add x y", &mut w).expect("parse");
        let ss = strings(&w);
        assert!(
            ss.iter().any(|s| s == "Nat.add"),
            "qualified name not interned as single Const: {ss:?}"
        );
    }

    #[test]
    fn test_parse_coq_v_type_empty_input_returns_none() {
        let mut w = ShardWriter::new();
        assert!(parse_coq_v_type("", &mut w).is_none());
        assert!(parse_coq_v_type("   \t\n ", &mut w).is_none());
    }

    #[test]
    fn test_parse_coq_v_type_untyped_forall_binder_skips() {
        // `forall x, x = x` has no binder annotation; we cannot recover
        // the type faithfully, so we skip rather than fabricate.
        let mut w = ShardWriter::new();
        assert!(
            parse_coq_v_type("forall x, x = x", &mut w).is_none(),
            "untyped forall binder must not be faked"
        );
    }
}
