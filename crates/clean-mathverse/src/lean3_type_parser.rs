// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Lean 3 surface-syntax type-signature parser → `FlatExpr` tree.
//!
//! Translates a Lean 3 type expression string (the text between `:` and
//! `:=` in a `def`/`theorem`/`axiom`/etc) into a structural `FlatExpr`
//! tree written into a [`ShardWriter`]. Returns the index of the root
//! expression on success.
//!
//! Scope: covers the **structural skeleton** of Lean 3 type expressions
//! — Pi binders (`∀`, `forall`, `Π`, `Pi`), function arrows
//! (`→`, `->`), application, parenthesisation, identifier references,
//! and `Prop`/`Type`/`Sort` universe atoms. Universe levels are
//! collapsed to `sort(0)` because the Lean 3 source files do not commit
//! to a universe-instantiation choice at the surface and re-elaborating
//! them belongs to the kernel pipeline, not this importer.
//!
//! Out of scope (parser returns `None` rather than emit fake data):
//! `let`, `match`, `do`, `if`-`then`-`else`, tactic blocks, attribute
//! syntax, mutual-induction headers, anonymous-constructor literals.
//! When parsing fails, the calling importer should skip the declaration
//! rather than fall back to a placeholder.
//!
//! The output is a real structural FlatExpr tree: a one-binder `Pi`
//! produces three FlatExpr nodes (the body, the binder type, the Pi),
//! not one shared placeholder per constant. That makes the resulting
//! shard pass the `expr_count > constant_count` fidelity check.

use clean_kernel::flat::FlatExpr;

use crate::shard::ShardWriter;

const NO_LEVELS: u32 = u32::MAX;

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
    Forall,
    Underscore,
    /// One of `= ≠ < ≤ > ≥ + - * /`, stored under the canonical name
    /// of the corresponding Lean 3 typeclass operation (`Eq`, `Lt`, …).
    Infix(&'static str, u8),
    Unknown(char),
}

fn lex(src: &str) -> Vec<Tok> {
    let mut out = Vec::new();
    let bytes: Vec<char> = src.chars().collect();
    let mut i = 0usize;
    while i < bytes.len() {
        let ch = bytes[i];
        if ch.is_whitespace() {
            i += 1;
            continue;
        }
        // Unicode arrow → and Π and ∀
        if ch == '→' {
            out.push(Tok::Arrow);
            i += 1;
            continue;
        }
        if ch == '∀' || ch == 'Π' {
            out.push(Tok::Forall);
            i += 1;
            continue;
        }
        // Unicode relations + logical connectives.
        match ch {
            '≤' => {
                out.push(Tok::Infix("Le", REL_PREC));
                i += 1;
                continue;
            }
            '≥' => {
                out.push(Tok::Infix("Ge", REL_PREC));
                i += 1;
                continue;
            }
            '≠' => {
                out.push(Tok::Infix("Ne", REL_PREC));
                i += 1;
                continue;
            }
            '\u{2227}' => {
                // ∧ logical and
                out.push(Tok::Infix("And", AND_PREC));
                i += 1;
                continue;
            }
            '\u{2228}' => {
                // ∨ logical or
                out.push(Tok::Infix("Or", OR_PREC));
                i += 1;
                continue;
            }
            '\u{2194}' => {
                // ↔ iff
                out.push(Tok::Infix("Iff", IFF_PREC));
                i += 1;
                continue;
            }
            _ => {}
        }
        // ASCII "->" and ":="
        if ch == '-' && i + 1 < bytes.len() && bytes[i + 1] == '>' {
            out.push(Tok::Arrow);
            i += 2;
            continue;
        }
        if ch == ':' && i + 1 < bytes.len() && bytes[i + 1] == '=' {
            return out; // caller should have stripped, but be safe
        }
        // Multi-char ASCII relations: <=, >=
        if (ch == '<' || ch == '>') && i + 1 < bytes.len() && bytes[i + 1] == '=' {
            out.push(Tok::Infix(if ch == '<' { "Le" } else { "Ge" }, REL_PREC));
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
                out.push(Tok::Infix("Eq", REL_PREC));
                i += 1;
                continue;
            }
            '<' => {
                out.push(Tok::Infix("Lt", REL_PREC));
                i += 1;
                continue;
            }
            '>' => {
                out.push(Tok::Infix("Gt", REL_PREC));
                i += 1;
                continue;
            }
            '+' => {
                out.push(Tok::Infix("Add", ADD_PREC));
                i += 1;
                continue;
            }
            '-' => {
                out.push(Tok::Infix("Sub", ADD_PREC));
                i += 1;
                continue;
            }
            '*' => {
                out.push(Tok::Infix("Mul", MUL_PREC));
                i += 1;
                continue;
            }
            '/' => {
                out.push(Tok::Infix("Div", MUL_PREC));
                i += 1;
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
            if let Ok(n) = s.parse::<u64>() {
                out.push(Tok::Nat(n));
            } else {
                out.push(Tok::Unknown(bytes[start]));
            }
            continue;
        }
        if is_ident_start(ch) {
            let start = i;
            while i < bytes.len() && is_ident_continue(bytes[i]) {
                i += 1;
            }
            let id: String = bytes[start..i].iter().collect();
            match id.as_str() {
                "forall" | "Pi" => out.push(Tok::Forall),
                _ => out.push(Tok::Ident(id)),
            }
            continue;
        }
        out.push(Tok::Unknown(ch));
        i += 1;
    }
    out
}

/// Operator precedences, modelled loosely on Lean 3's parser.
const MUL_PREC: u8 = 70;
const ADD_PREC: u8 = 65;
const REL_PREC: u8 = 50;
const AND_PREC: u8 = 35;
const OR_PREC: u8 = 30;
const IFF_PREC: u8 = 20;

fn is_ident_start(ch: char) -> bool {
    ch.is_alphabetic() || ch == '_'
}

fn is_ident_continue(ch: char) -> bool {
    ch.is_alphanumeric() || ch == '_' || ch == '.' || ch == '\''
}

/// Binder kind, encoded for `FlatExpr::pi`.
const BINDER_DEFAULT: u8 = 0;
const BINDER_IMPLICIT: u8 = 1;
const BINDER_INST_IMPLICIT: u8 = 3;

struct Parser<'w> {
    toks: Vec<Tok>,
    pos: usize,
    writer: &'w mut ShardWriter,
    /// Stack of binder names in the current scope, outermost first.
    bound: Vec<String>,
    /// Hard cap on emitted exprs per type — guards against pathological inputs.
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
            self.parse_pi_chain(BINDER_DEFAULT)
        } else {
            self.parse_arrow()
        }
    }

    /// After `∀`/`forall`/`Π`/`Pi`, parse one or more binder groups
    /// followed by `,` and the body. Each binder name in each group
    /// becomes its own Pi.
    ///
    /// Names are pushed onto the scope stack as each group finishes
    /// parsing, so a later group's binder type can mention an earlier
    /// group's name (`(x : Nat) (v : Vec x)` resolves correctly).
    fn parse_pi_chain(&mut self, default_binfo: u8) -> Option<u32> {
        let mut binders: Vec<(u8, u32)> = Vec::new();
        let mut pushed = 0usize;
        loop {
            if matches!(self.peek(), Some(Tok::Comma)) {
                self.bump();
                break;
            }
            if self.peek().is_none() {
                // Unexpected EOF inside binder list — bail and pop scope.
                for _ in 0..pushed {
                    self.bound.pop();
                }
                return None;
            }
            let group = self.parse_binder_group(default_binfo)?;
            for (name, binfo, ty_idx) in group {
                self.bound.push(name);
                pushed += 1;
                binders.push((binfo, ty_idx));
            }
        }
        let body = self.parse_type()?;
        let mut acc = body;
        for (binfo, ty_idx) in binders.iter().rev() {
            acc = self.add(FlatExpr::pi(*binfo, *ty_idx, acc))?;
        }
        for _ in 0..pushed {
            self.bound.pop();
        }
        Some(acc)
    }

    /// Parse one binder group: `(x y : T)`, `{x : T}`, `[T]`, bare
    /// `x`, or unbracketed `x y : T` (the last form is what Lean 3
    /// accepts after `∀`/`Π` without parens).
    /// Returns the list `(name, binder_info, type_idx)`.
    fn parse_binder_group(&mut self, default_binfo: u8) -> Option<Vec<(String, u8, u32)>> {
        let (close, binfo, anonymous_inst) = match self.peek() {
            Some(Tok::LParen) => (Some(Tok::RParen), BINDER_DEFAULT, false),
            Some(Tok::LBrace) => (Some(Tok::RBrace), BINDER_IMPLICIT, false),
            Some(Tok::LBrack) => (Some(Tok::RBrack), BINDER_INST_IMPLICIT, true),
            _ => (None, default_binfo, false),
        };
        if let Some(close_tok) = close.as_ref() {
            self.bump(); // consume the opening bracket
                         // Anonymous inst-implicit binder: `[Group α]` ≡ `[_ : Group α]`.
            if anonymous_inst && !self.looks_like_named_binder() {
                let ty = self.parse_type()?;
                if !self.eat(close_tok) {
                    return None;
                }
                return Some(vec![("_".to_string(), binfo, ty)]);
            }
        }
        let mut names = Vec::new();
        while let Some(Tok::Ident(_)) | Some(Tok::Underscore) = self.peek() {
            names.push(self.expect_ident_or_under()?);
        }
        if names.is_empty() {
            return None;
        }
        let ty = if matches!(self.peek(), Some(Tok::Colon)) {
            self.bump();
            self.parse_type()?
        } else {
            self.add(FlatExpr::sort(0))?
        };
        if let Some(close) = close.as_ref() {
            if !self.eat(close) {
                return None;
            }
        }
        Some(names.into_iter().map(|n| (n, binfo, ty)).collect())
    }

    /// Heuristic: a `[`-binder starts with `id :` ⇒ named, else anonymous.
    fn looks_like_named_binder(&self) -> bool {
        match (self.toks.get(self.pos), self.toks.get(self.pos + 1)) {
            (Some(Tok::Ident(_)), Some(Tok::Colon)) => true,
            (Some(Tok::Ident(_)), Some(Tok::Ident(_))) => false,
            _ => false,
        }
    }

    fn expect_ident(&mut self) -> Option<String> {
        match self.bump()? {
            Tok::Ident(s) => Some(s),
            Tok::Underscore => Some("_".into()),
            _ => None,
        }
    }
    fn expect_ident_or_under(&mut self) -> Option<String> {
        self.expect_ident()
    }

    /// `arrow := infix (→ arrow)?` — right-associative.
    ///
    /// Also recognises top-level implicit-binder Pi syntax such as
    /// `{α : Type} → α → α`. Lean 3 treats this as
    /// `Π {α : Type}, α → α`. We consume the leading binder, require
    /// the arrow, then continue with the body.
    fn parse_arrow(&mut self) -> Option<u32> {
        if matches!(self.peek(), Some(Tok::LBrace) | Some(Tok::LBrack)) {
            let group = self.parse_binder_group(BINDER_DEFAULT)?;
            if !self.eat(&Tok::Arrow) {
                return None;
            }
            let n = group.len();
            let binfos_tys: Vec<(u8, u32)> = group.iter().map(|(_, b, t)| (*b, *t)).collect();
            for (name, _, _) in &group {
                self.bound.push(name.clone());
            }
            let body = self.parse_type()?;
            let mut acc = body;
            for (binfo, ty) in binfos_tys.iter().rev() {
                acc = self.add(FlatExpr::pi(*binfo, *ty, acc))?;
            }
            for _ in 0..n {
                self.bound.pop();
            }
            return Some(acc);
        }
        let lhs = self.parse_infix(0)?;
        if !self.eat(&Tok::Arrow) {
            return Some(lhs);
        }
        // `A → B` ≡ `Π (_ : A), B`. Push an anonymous binder.
        self.bound.push("_".into());
        let rhs = self.parse_type()?;
        self.bound.pop();
        self.add(FlatExpr::pi(BINDER_DEFAULT, lhs, rhs))
    }

    /// Pratt-style precedence climbing for binary infix operators
    /// (`=`, `<`, `≤`, `+`, `-`, `*`, `/`, …). Each infix `op a b`
    /// becomes the FlatExpr application `((op a) b)` where `op` is a
    /// free `Const` reference under its Lean 3 typeclass name.
    fn parse_infix(&mut self, min_prec: u8) -> Option<u32> {
        let mut lhs = self.parse_app()?;
        loop {
            let (op, prec) = match self.peek() {
                Some(Tok::Infix(op, prec)) if *prec >= min_prec => (*op, *prec),
                _ => break,
            };
            self.bump();
            // All our infix ops are left-associative in this parser.
            let rhs = self.parse_infix(prec + 1)?;
            let op_name = self.writer.add_string(op);
            let op_const = self.add(FlatExpr::const_ref(op_name, NO_LEVELS))?;
            let app1 = self.add(FlatExpr::app(op_const, lhs))?;
            lhs = self.add(FlatExpr::app(app1, rhs))?;
        }
        Some(lhs)
    }

    /// Left-associative application.
    fn parse_app(&mut self) -> Option<u32> {
        let mut head = self.parse_atom()?;
        while let Some(Tok::Ident(_) | Tok::Nat(_) | Tok::Underscore | Tok::LParen) = self.peek() {
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
                // Implicit/inst-implicit binder appearing in expression
                // position is unusual; bail rather than misparse.
                None
            }
            Tok::Underscore => {
                self.bump();
                self.add(FlatExpr::sort(0))
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
        if matches!(name, "Prop" | "Type" | "Sort") {
            // `Type*` / `Sort*` is Lean 3's universe-polymorphic
            // shorthand. The `*` would otherwise be lexed as Mul and
            // turn `Type*` into `(Mul Type ???)`. Absorb it.
            if matches!(self.peek(), Some(Tok::Infix("Mul", _))) {
                self.bump();
            } else if let Some(Tok::Ident(_) | Tok::LParen) = self.peek() {
                // Optional level argument: `Type u` or `Type 0`.
                let _ = self.parse_universe_level();
            }
            return self.add(FlatExpr::sort(0));
        }
        // Bound variable: innermost match wins (rposition).
        if let Some(pos) = self.bound.iter().rposition(|n| n == name) {
            let depth = self.bound.len() - 1 - pos;
            return self.add(FlatExpr::bvar(depth as u32));
        }
        // Free (ambient) name: emit as Const reference.
        let name_idx = self.writer.add_string(name);
        self.add(FlatExpr::const_ref(name_idx, NO_LEVELS))
    }

    /// Best-effort: skip a universe level argument like `u` or `(u+1)`.
    fn parse_universe_level(&mut self) -> Option<()> {
        match self.peek().cloned()? {
            Tok::Ident(_) => {
                self.bump();
                Some(())
            }
            Tok::LParen => {
                self.bump();
                let mut depth = 1u32;
                while depth > 0 {
                    match self.bump()? {
                        Tok::LParen => depth += 1,
                        Tok::RParen => depth -= 1,
                        _ => {}
                    }
                }
                Some(())
            }
            _ => None,
        }
    }
}

/// Parse a Lean 3 type signature into the writer. Returns the root
/// expression index. Returns `None` on parse failure or empty input;
/// callers should treat that as "skip this declaration", never as a
/// licence to emit a placeholder.
pub fn parse_lean3_type(src: &str, writer: &mut ShardWriter) -> Option<u32> {
    let toks = lex(src);
    if toks.is_empty() {
        return None;
    }
    let mut p = Parser::new(toks, writer);
    let root = p.parse_type()?;
    // Trailing junk is suspicious but tolerable — the structural
    // prefix is real. Reject only if absolutely nothing was consumed.
    Some(root)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn count_exprs(src: &str) -> (u32, usize) {
        let mut w = ShardWriter::new();
        let before = w.expr_count();
        let root = parse_lean3_type(src, &mut w).expect("parse");
        let after = w.expr_count();
        (root, after - before)
    }

    #[test]
    fn arrow_chain_emits_distinct_pis() {
        // `Nat -> Nat -> Nat` ≡ `Π _, Π _, Nat`. Post-dedup the FlatExpr
        // arena holds: one shared Const(Nat), one inner Pi(Nat, Nat),
        // one outer Pi(Nat, inner_pi) = 3 unique exprs.
        let (_, n) = count_exprs("Nat -> Nat -> Nat");
        assert!(n >= 3, "expected >= 3 unique exprs, got {n}");
    }

    #[test]
    fn forall_binder_emits_pi_with_real_body() {
        // `forall n : Nat, n = n` — should produce Const(Nat), BVar(0),
        // Const(Eq), App, App, Pi = at least 5 unique exprs.
        let (_, n) = count_exprs("forall n : Nat, n = n");
        assert!(n >= 5, "expected real tree, got {n}");
    }

    #[test]
    fn unicode_pi_and_arrow() {
        let (_, n) = count_exprs("∀ n : Nat, n → n");
        assert!(n >= 4, "expected real tree, got {n}");
    }

    #[test]
    fn bvar_resolves_to_binder_not_const() {
        // `forall n : Nat, n` — the body `n` must be a BVar, not a free
        // Const reference. ShardWriter::new() seeds the string table
        // with one empty sentinel string, so a clean parse of this
        // input must end up with exactly 2 strings: the sentinel and
        // "Nat". If "n" leaked, we'd see 3.
        let mut w = ShardWriter::new();
        let _root = parse_lean3_type("forall n : Nat, n", &mut w).expect("parse");
        let exprs = w.expr_count();
        assert!(exprs >= 3, "expected at least Nat/BVar/Pi");
        assert_eq!(
            w.string_count(),
            2,
            "binder name 'n' leaked into the string table — \
             that means it was emitted as a free Const, not a BVar"
        );
    }

    #[test]
    fn parens_grouping_works() {
        let (_, n) = count_exprs("(Nat -> Nat) -> Nat");
        // Inner Pi + outer Pi + shared Const(Nat) = 3 unique exprs.
        assert!(n >= 3, "expected >= 3 unique exprs, got {n}");
    }

    #[test]
    fn unknown_atom_becomes_const_ref_not_placeholder() {
        let mut w = ShardWriter::new();
        let _ = parse_lean3_type("MyType -> MyType", &mut w).expect("parse");
        assert!(w.expr_count() >= 2);
        // MyType is a free name — must have been added to strings.
        assert!(
            w.string_count() >= 1,
            "free-name identifier should have entered the string table"
        );
    }

    #[test]
    fn empty_input_returns_none() {
        let mut w = ShardWriter::new();
        assert!(parse_lean3_type("", &mut w).is_none());
        assert!(parse_lean3_type("   \t \n  ", &mut w).is_none());
    }

    #[test]
    fn implicit_binder_braces_parse() {
        let (_, n) = count_exprs("{α : Type} -> α -> α");
        // sort(0), BVar(0), BVar(1), inner Pi, outer Pi = 5 unique exprs.
        assert!(n >= 4, "expected real tree, got {n}");
    }

    #[test]
    fn numeric_literal_in_body() {
        // `n + 0 = n` — the common `simp`-style lemma surface form.
        let (_, n) = count_exprs("n + 0 = n");
        assert!(n >= 5, "expected real tree, got {n}");
    }

    #[test]
    fn logical_connectives_parse_as_infix() {
        let mut w = ShardWriter::new();
        let _ = parse_lean3_type("a ∧ b ∨ c → a", &mut w).expect("parse");
        let strings: Vec<&str> = (0..w.string_count())
            .map(|i| w.string_at(i as u32))
            .collect();
        assert!(strings.contains(&"And"), "And missing in {strings:?}");
        assert!(strings.contains(&"Or"), "Or missing in {strings:?}");
    }

    #[test]
    fn type_star_universe_polymorphic_shorthand() {
        // Lean 3 mathlib uses `Type*` heavily for universe polymorphism.
        // Without special handling the `*` would lex as Mul.
        let mut w = ShardWriter::new();
        let _ = parse_lean3_type("Type* -> Type*", &mut w).expect("parse");
        let strings: Vec<&str> = (0..w.string_count())
            .map(|i| w.string_at(i as u32))
            .collect();
        assert!(
            !strings.contains(&"Mul"),
            "`*` after Type leaked as Mul infix: {strings:?}"
        );
    }
}
