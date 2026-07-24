// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Isabelle/Isar HOL term → `FlatExpr` tree.
//!
//! Translates the quoted proposition of an Isar `theorem`/`lemma` (the
//! text inside the `"..."`) into a structural [`FlatExpr`] tree written
//! into a [`ShardWriter`], returning the root expression index. Higher-
//! order HOL terms are the hard part; this module aims at a faithful
//! CORE and **skips** (returns `None`) anything it cannot render exactly,
//! so the caller drops the declaration rather than fabricating data.
//!
//! ## Forms parsed (faithful core)
//!
//! * **Meta-implication** `A ⟹ B` (ASCII `A ==> B`) — right-associative,
//!   encoded as a non-dependent `Pi(default, A, B)`. `B` is parsed under
//!   one extra (anonymous) binder level so de Bruijn indices stay correct.
//! * **Meta-quantifier** `⋀x. P` (ASCII `!!x. P`) — universal over `x`,
//!   encoded as `Pi(default, sort(0), P)` with `x` bound; references to
//!   `x` inside `P` resolve to `BVar`. The binder *type* is unknown at the
//!   surface, so it is recorded as `sort(0)` (a per-binder annotation
//!   slot, NOT the forbidden one-placeholder-per-constant pattern — `P`
//!   is a real translated tree).
//! * **Object quantifiers** `∀x. P` (ASCII `ALL x. P`) and `∃x. P`
//!   (`EX x. P`) — encoded as `App(Const("All"|"Ex"), Lam x. P)`, the HOL
//!   convention where the quantifier is a constant applied to a predicate
//!   abstraction. `x` resolves to `BVar` inside `P`.
//! * **Object connectives** as constant heads applied left-to-right:
//!   `⟶`/`-->` → `implies`, `∧`/`&` → `conj`, `∨`/`|` → `disj`,
//!   `¬`/`~` → `not` (prefix), `=` → `eq`. So `a = b` ⇒
//!   `App(App(Const("eq"), a), b)`.
//! * **Arithmetic / relations**: `+ - * /` → `add sub mul div`;
//!   `< <= > >=` → `lt le gt ge`. Pratt precedence table, all infix ops
//!   left-associative, emitted as curried `Const` applications.
//! * **Application** `f a b` → left-nested `App(App(f, a), b)`.
//! * **Atoms**: identifiers → `BVar` if bound else `Const(name)`; numeric
//!   literals → `lit_nat`; parenthesised subterms recurse.
//!
//! ## Deliberately skipped (parser returns `None`)
//!
//! * Schematic variables `?x` — treated as a *free* `Const("?x")` (the `?`
//!   is kept verbatim in the name so the schematic origin is visible);
//!   this is the one tolerated oddity, documented here rather than skipped.
//! * Type ascriptions `(t :: 'a)` and bare type variables `'a` in term
//!   position — the `:: <type>` tail is stripped and the term kept; a
//!   `'a` appearing where a term atom is expected aborts the parse.
//! * `λ`/`%` lambda abstractions, `let`/`if`/`case`, set-builder `{...}`,
//!   list/tuple syntax, and any unrecognised Unicode/operator — abort.
//!
//! This is a Level-0/1 structural data import, NOT verified elaboration:
//! the tree mirrors the surface syntax but is not type-checked. Callers
//! record `ImportConfidence::Unverified` + `AxiomProfile::AXIOMATIZED`.

use clean_kernel::flat::FlatExpr;

use crate::shard::ShardWriter;

/// `const_ref` levels-list sentinel: this constant carries no universe
/// instantiation (matches the sibling importers' convention).
const NO_LEVELS: u32 = u32::MAX;

/// Ordinary explicit binder-info byte for `Pi`/`Lam`.
const BINDER_DEFAULT: u8 = 0;

/// Unknown binder type placeholder for meta/object quantifiers, whose
/// bound-variable type is not present in the surface proposition.
const SORT_UNKNOWN: u32 = 0;

/// Hard cap on emitted exprs per term — guards pathological inputs. A
/// translation that would exceed it fails (→ skip) rather than run away.
const EXPR_BUDGET: u32 = 8192;

/// Pratt binding powers (higher binds tighter). Meta-implication is the
/// loosest binary form; application (handled separately) is tightest.
const PREC_META_IMP: u8 = 5; // ⟹ / ==>
const PREC_OBJ_IMP: u8 = 10; // ⟶ / -->
const PREC_OR: u8 = 20; // ∨ / |
const PREC_AND: u8 = 30; // ∧ / &
const PREC_REL: u8 = 40; // = < <= > >=
const PREC_ADD: u8 = 50; // + -
const PREC_MUL: u8 = 60; // * /

#[derive(Debug, Clone, PartialEq, Eq)]
enum Tok {
    Ident(String),
    Nat(u64),
    LParen,
    RParen,
    Dot,
    /// `::` type ascription marker.
    ColonColon,
    /// Bare type variable `'a` — only ever appears after `::`; if it
    /// reaches term position the parse aborts.
    TyVar(String),
    /// Meta connectives.
    MetaImp,
    MetaAll,
    /// Object quantifiers.
    ObjAll,
    ObjEx,
    /// Prefix negation `¬` / `~`.
    Not,
    /// Binary infix operator: canonical constant name + binding power +
    /// right-associativity flag.
    Infix(&'static str, u8, bool),
    Unknown,
}

/// Lex the quoted Isar term. Returns `None` on any character the core
/// does not model (so the caller skips the declaration).
fn lex(src: &str) -> Option<Vec<Tok>> {
    let cs: Vec<char> = src.chars().collect();
    let mut out = Vec::new();
    let mut i = 0usize;
    while i < cs.len() {
        let c = cs[i];
        if c.is_whitespace() {
            i += 1;
            continue;
        }
        // Multi-char ASCII operators first.
        if c == '=' && cs.get(i + 1) == Some(&'=') && cs.get(i + 2) == Some(&'>') {
            out.push(Tok::MetaImp);
            i += 3;
            continue;
        }
        if c == '-' && cs.get(i + 1) == Some(&'-') && cs.get(i + 2) == Some(&'>') {
            out.push(Tok::Infix("implies", PREC_OBJ_IMP, true));
            i += 3;
            continue;
        }
        if c == '!' && cs.get(i + 1) == Some(&'!') {
            out.push(Tok::MetaAll);
            i += 2;
            continue;
        }
        if c == ':' && cs.get(i + 1) == Some(&':') {
            out.push(Tok::ColonColon);
            i += 2;
            continue;
        }
        if (c == '<' || c == '>') && cs.get(i + 1) == Some(&'=') {
            out.push(Tok::Infix(
                if c == '<' { "le" } else { "ge" },
                PREC_REL,
                false,
            ));
            i += 2;
            continue;
        }
        // Unicode Isabelle symbols (real UTF-8 in `.thy` sources).
        match c {
            '\u{27F9}' => {
                // ⟹ meta-implication
                out.push(Tok::MetaImp);
                i += 1;
                continue;
            }
            '\u{22C0}' => {
                // ⋀ meta-universal
                out.push(Tok::MetaAll);
                i += 1;
                continue;
            }
            '\u{27F6}' => {
                // ⟶ object implication
                out.push(Tok::Infix("implies", PREC_OBJ_IMP, true));
                i += 1;
                continue;
            }
            '\u{2227}' => {
                // ∧ conjunction
                out.push(Tok::Infix("conj", PREC_AND, true));
                i += 1;
                continue;
            }
            '\u{2228}' => {
                // ∨ disjunction
                out.push(Tok::Infix("disj", PREC_OR, true));
                i += 1;
                continue;
            }
            '\u{00AC}' => {
                // ¬ negation
                out.push(Tok::Not);
                i += 1;
                continue;
            }
            '\u{2200}' => {
                // ∀ object universal
                out.push(Tok::ObjAll);
                i += 1;
                continue;
            }
            '\u{2203}' => {
                // ∃ object existential
                out.push(Tok::ObjEx);
                i += 1;
                continue;
            }
            '\u{2264}' => {
                // ≤
                out.push(Tok::Infix("le", PREC_REL, false));
                i += 1;
                continue;
            }
            '\u{2265}' => {
                // ≥
                out.push(Tok::Infix("ge", PREC_REL, false));
                i += 1;
                continue;
            }
            '\u{2260}' => {
                // ≠
                out.push(Tok::Infix("ne", PREC_REL, false));
                i += 1;
                continue;
            }
            _ => {}
        }
        match c {
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
            '.' => {
                out.push(Tok::Dot);
                i += 1;
                continue;
            }
            '=' => {
                out.push(Tok::Infix("eq", PREC_REL, false));
                i += 1;
                continue;
            }
            '<' => {
                out.push(Tok::Infix("lt", PREC_REL, false));
                i += 1;
                continue;
            }
            '>' => {
                out.push(Tok::Infix("gt", PREC_REL, false));
                i += 1;
                continue;
            }
            '&' => {
                out.push(Tok::Infix("conj", PREC_AND, true));
                i += 1;
                continue;
            }
            '|' => {
                out.push(Tok::Infix("disj", PREC_OR, true));
                i += 1;
                continue;
            }
            '~' => {
                out.push(Tok::Not);
                i += 1;
                continue;
            }
            '+' => {
                out.push(Tok::Infix("add", PREC_ADD, false));
                i += 1;
                continue;
            }
            '-' => {
                out.push(Tok::Infix("sub", PREC_ADD, false));
                i += 1;
                continue;
            }
            '*' => {
                out.push(Tok::Infix("mul", PREC_MUL, false));
                i += 1;
                continue;
            }
            '/' => {
                out.push(Tok::Infix("div", PREC_MUL, false));
                i += 1;
                continue;
            }
            '\'' => {
                // Type variable `'a` — capture and tag. Only valid after `::`.
                let start = i;
                i += 1;
                while i < cs.len() && is_ident_continue(cs[i]) {
                    i += 1;
                }
                let s: String = cs[start..i].iter().collect();
                out.push(Tok::TyVar(s));
                continue;
            }
            _ => {}
        }
        if c.is_ascii_digit() {
            let start = i;
            while i < cs.len() && cs[i].is_ascii_digit() {
                i += 1;
            }
            let s: String = cs[start..i].iter().collect();
            match s.parse::<u64>() {
                Ok(n) => out.push(Tok::Nat(n)),
                Err(_) => return None,
            }
            continue;
        }
        if c == '?' || is_ident_start(c) {
            // `?x` schematic variables keep the leading `?` in the name.
            let start = i;
            if c == '?' {
                i += 1;
            }
            // A schematic `?` with no following identifier char is malformed.
            if c == '?' && (i >= cs.len() || !is_ident_start(cs[i])) {
                return None;
            }
            while i < cs.len() && is_ident_continue(cs[i]) {
                i += 1;
            }
            let id: String = cs[start..i].iter().collect();
            match id.as_str() {
                "ALL" => out.push(Tok::ObjAll),
                "EX" => out.push(Tok::ObjEx),
                _ => out.push(Tok::Ident(id)),
            }
            continue;
        }
        // Anything else is unmodelled — abort the whole term.
        out.push(Tok::Unknown);
        return None;
    }
    Some(out)
}

fn is_ident_start(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_'
}

fn is_ident_continue(c: char) -> bool {
    // NOTE: `.` is deliberately EXCLUDED — in Isar a `.` after a quantifier
    // binder (`⋀x. P`, `∀x. P`) is the body separator, not part of the
    // name. Treating it as a separate `Dot` token keeps binders correct;
    // the cost is that a dotted qualified name (`List.append`) lexes as
    // three tokens and the term is then skipped rather than misparsed.
    c.is_ascii_alphanumeric() || matches!(c, '_' | '\'')
}

struct Parser<'w> {
    toks: Vec<Tok>,
    pos: usize,
    writer: &'w mut ShardWriter,
    /// In-scope binder names, outermost first. A name's de Bruijn index is
    /// `bound.len() - 1 - position` (innermost match wins).
    bound: Vec<String>,
    budget: u32,
}

impl<'w> Parser<'w> {
    fn new(toks: Vec<Tok>, writer: &'w mut ShardWriter) -> Self {
        Self {
            toks,
            pos: 0,
            writer,
            bound: Vec::new(),
            budget: EXPR_BUDGET,
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
        if self.budget == 0 {
            return None;
        }
        self.budget -= 1;
        Some(self.writer.add_expr(e))
    }

    fn const_named(&mut self, name: &str) -> Option<u32> {
        let idx = self.writer.add_string(name);
        self.add(FlatExpr::const_ref(idx, NO_LEVELS))
    }

    /// Entry point: a full proposition is the lowest-precedence expression.
    fn parse_prop(&mut self) -> Option<u32> {
        self.parse_bp(0)
    }

    /// Pratt precedence-climbing parser. Parses a leading prefix/quantifier
    /// then folds in binary operators whose binding power is `>= min_bp`.
    fn parse_bp(&mut self, min_bp: u8) -> Option<u32> {
        let mut lhs = self.parse_prefix()?;
        loop {
            let (name, bp, right_assoc, is_meta_imp) = match self.peek() {
                Some(Tok::MetaImp) if PREC_META_IMP >= min_bp => (None, PREC_META_IMP, true, true),
                Some(Tok::Infix(n, bp, ra)) if *bp >= min_bp => (Some(*n), *bp, *ra, false),
                _ => break,
            };
            self.bump();
            if is_meta_imp {
                // `A ⟹ B` ≡ non-dependent Pi. Parse `B` under one fresh
                // anonymous binder so loose BVars in `B` shift correctly.
                self.bound.push("_".into());
                let rhs = self.parse_bp(PREC_META_IMP); // right-assoc
                self.bound.pop();
                let rhs = rhs?;
                lhs = self.add(FlatExpr::pi(BINDER_DEFAULT, lhs, rhs))?;
                continue;
            }
            let name = name?;
            let next_min = if right_assoc { bp } else { bp + 1 };
            let rhs = self.parse_bp(next_min)?;
            let op = self.const_named(name)?;
            let app1 = self.add(FlatExpr::app(op, lhs))?;
            lhs = self.add(FlatExpr::app(app1, rhs))?;
        }
        Some(lhs)
    }

    /// Prefix forms: quantifiers, negation, then application spine.
    fn parse_prefix(&mut self) -> Option<u32> {
        match self.peek() {
            Some(Tok::MetaAll) => {
                self.bump();
                self.parse_meta_all()
            }
            Some(Tok::ObjAll) => {
                self.bump();
                self.parse_obj_quant("All")
            }
            Some(Tok::ObjEx) => {
                self.bump();
                self.parse_obj_quant("Ex")
            }
            Some(Tok::Not) => {
                self.bump();
                // `¬ P` ≡ `App(Const(not), P)`. Bind tighter than infix.
                let inner = self.parse_prefix()?;
                let op = self.const_named("not")?;
                self.add(FlatExpr::app(op, inner))
            }
            _ => self.parse_app(),
        }
    }

    /// `⋀x y. P` — meta-universal over one or more names, each its own Pi
    /// with `sort(0)` binder type (surface type unknown). Right operand is
    /// the proposition after `.`.
    fn parse_meta_all(&mut self) -> Option<u32> {
        let names = self.parse_binder_names()?;
        if !self.eat(&Tok::Dot) {
            return None;
        }
        let pushed = names.len();
        for n in &names {
            self.bound.push(n.clone());
        }
        let body = self.parse_prop();
        for _ in 0..pushed {
            self.bound.pop();
        }
        let mut acc = body?;
        for _ in 0..pushed {
            let ty = self.add(FlatExpr::sort(SORT_UNKNOWN))?;
            acc = self.add(FlatExpr::pi(BINDER_DEFAULT, ty, acc))?;
        }
        Some(acc)
    }

    /// `∀x y. P` / `∃x y. P` — object quantifier `q` applied to a lambda
    /// abstraction: `App(Const(q), Lam x. … Lam y. P)`. For multiple names
    /// the quantifier is re-applied per binder: `q (λx. q (λy. P))`.
    fn parse_obj_quant(&mut self, q: &str) -> Option<u32> {
        let names = self.parse_binder_names()?;
        if !self.eat(&Tok::Dot) {
            return None;
        }
        let pushed = names.len();
        for n in &names {
            self.bound.push(n.clone());
        }
        let body = self.parse_prop();
        for _ in 0..pushed {
            self.bound.pop();
        }
        let mut acc = body?;
        for _ in 0..pushed {
            let ty = self.add(FlatExpr::sort(SORT_UNKNOWN))?;
            let lam = self.add(FlatExpr::lam(BINDER_DEFAULT, ty, acc))?;
            let op = self.const_named(q)?;
            acc = self.add(FlatExpr::app(op, lam))?;
        }
        Some(acc)
    }

    /// One or more binder names following a quantifier, before the `.`.
    /// A `name :: 'a` type ascription on a binder is consumed and dropped.
    fn parse_binder_names(&mut self) -> Option<Vec<String>> {
        let mut names = Vec::new();
        while let Some(Tok::Ident(_)) = self.peek() {
            let name = match self.bump() {
                Some(Tok::Ident(s)) => s,
                _ => return None,
            };
            names.push(name);
            // Optional `:: type` ascription on this binder.
            if self.eat(&Tok::ColonColon) {
                self.skip_type()?;
            }
        }
        if names.is_empty() {
            None
        } else {
            Some(names)
        }
    }

    /// Left-associative application: `f a b` ≡ `App(App(f, a), b)`.
    fn parse_app(&mut self) -> Option<u32> {
        let mut head = self.parse_atom()?;
        while matches!(self.peek(), Some(Tok::Ident(_) | Tok::Nat(_) | Tok::LParen)) {
            let arg = self.parse_atom()?;
            head = self.add(FlatExpr::app(head, arg))?;
        }
        Some(head)
    }

    fn parse_atom(&mut self) -> Option<u32> {
        match self.peek().cloned()? {
            Tok::LParen => {
                self.bump();
                let inner = self.parse_prop()?;
                // Optional `:: type` ascription inside the parens: strip it.
                if self.eat(&Tok::ColonColon) {
                    self.skip_type()?;
                }
                if !self.eat(&Tok::RParen) {
                    return None;
                }
                Some(inner)
            }
            Tok::Nat(n) => {
                self.bump();
                self.add(FlatExpr::lit_nat(n))
            }
            Tok::Ident(name) => {
                self.bump();
                self.emit_name(&name)
            }
            // Type variables, dangling operators, dots etc. are not atoms.
            _ => None,
        }
    }

    fn emit_name(&mut self, name: &str) -> Option<u32> {
        if let Some(pos) = self.bound.iter().rposition(|n| n == name) {
            let depth = (self.bound.len() - 1 - pos) as u32;
            return self.add(FlatExpr::bvar(depth));
        }
        self.const_named(name)
    }

    /// Consume and discard a type expression after `::`, up to a token that
    /// cannot be part of a type (`.`, `)`, end, or a connective). Type
    /// ascriptions carry no term content for this Level-0/1 import.
    fn skip_type(&mut self) -> Option<()> {
        let mut depth = 0usize;
        while let Some(t) = self.peek() {
            match t {
                Tok::LParen => {
                    depth += 1;
                    self.bump();
                }
                Tok::RParen => {
                    if depth == 0 {
                        break;
                    }
                    depth -= 1;
                    self.bump();
                }
                Tok::Dot if depth == 0 => break,
                Tok::MetaImp if depth == 0 => break,
                Tok::Ident(_) | Tok::TyVar(_) | Tok::Infix(_, _, _) | Tok::ColonColon => {
                    self.bump();
                }
                _ if depth > 0 => {
                    self.bump();
                }
                _ => break,
            }
        }
        Some(())
    }
}

/// Parse the quoted Isar proposition `src` into `writer`, returning the
/// root expression index. Returns `None` on empty input or any
/// unsupported form; callers MUST treat `None` as "skip this declaration"
/// and never emit a placeholder.
pub(crate) fn parse_isabelle_term(src: &str, writer: &mut ShardWriter) -> Option<u32> {
    let toks = lex(src)?;
    if toks.is_empty() {
        return None;
    }
    let mut p = Parser::new(toks, writer);
    let root = p.parse_prop()?;
    // Require the full token stream to be consumed — a trailing tail means
    // we misparsed, so skip rather than emit a partial tree.
    if p.pos != p.toks.len() {
        return None;
    }
    Some(root)
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::flat::FlatTag;

    fn tag_of(w: &ShardWriter, idx: u32) -> FlatTag {
        w.expr_at(idx)
            .expect("expr in range")
            .tag()
            .expect("valid tag")
    }

    fn u32_at(w: &ShardWriter, idx: u32, off: usize) -> u32 {
        w.expr_at(idx)
            .expect("expr in range")
            .read_u32(off)
            .expect("u32")
    }

    fn u64_at(w: &ShardWriter, idx: u32, off: usize) -> u64 {
        w.expr_at(idx)
            .expect("expr in range")
            .read_u64(off)
            .expect("u64")
    }

    fn strings(w: &ShardWriter) -> Vec<String> {
        (0..w.string_count())
            .map(|i| w.string_at(i as u32).to_owned())
            .collect()
    }

    /// PIN the exact arena for `x + 0 = x` (free `x`, no binder).
    ///
    /// Pratt parsing emits the LHS atom of each operator first, so the
    /// add-then-eq shape `(eq (add x 0) x)` lays out (post-dedup) as:
    ///   0: Const(x)            ; LHS of `+`  [shared with RHS of `=`]
    ///   1: LitNat(0)
    ///   2: Const(add)
    ///   3: App(add, x)         ; (App #2 #0)
    ///   4: App((add x), 0)     ; (App #3 #1)   == x + 0
    ///   5: Const(eq)
    ///   6: App(eq, (x+0))      ; (App #5 #4)
    ///   7: App((eq (x+0)), x)  ; (App #6 #0)   ROOT  (reuses Const(x) #0)
    #[test]
    fn test_parse_isabelle_term_x_plus_0_eq_x_exact_tree() {
        let mut w = ShardWriter::new();
        let root = parse_isabelle_term("x + 0 = x", &mut w).expect("parse");
        assert_eq!(root, 7, "root should be the outer eq application");
        assert_eq!(w.expr_count(), 8, "exact node count changed: audit tree");

        // #7 = App((eq (x+0)) #6, x #0)
        assert_eq!(tag_of(&w, 7), FlatTag::App);
        assert_eq!(u32_at(&w, 7, 0), 6);
        assert_eq!(u32_at(&w, 7, 4), 0);

        // #6 = App(eq #5, (x+0) #4)
        assert_eq!(tag_of(&w, 6), FlatTag::App);
        assert_eq!(u32_at(&w, 6, 0), 5);
        assert_eq!(u32_at(&w, 6, 4), 4);

        // #4 = App((add x) #3, 0 #1)
        assert_eq!(tag_of(&w, 4), FlatTag::App);
        assert_eq!(u32_at(&w, 4, 0), 3);
        assert_eq!(u32_at(&w, 4, 4), 1);

        // #3 = App(add #2, x #0)
        assert_eq!(tag_of(&w, 3), FlatTag::App);
        assert_eq!(u32_at(&w, 3, 0), 2);
        assert_eq!(u32_at(&w, 3, 4), 0);

        // Leaves.
        assert_eq!(tag_of(&w, 0), FlatTag::Const);
        assert_eq!(w.string_at(u32_at(&w, 0, 0)), "x");
        assert_eq!(tag_of(&w, 1), FlatTag::LitNat);
        assert_eq!(u64_at(&w, 1, 0), 0);
        assert_eq!(tag_of(&w, 2), FlatTag::Const);
        assert_eq!(w.string_at(u32_at(&w, 2, 0)), "add");
        assert_eq!(tag_of(&w, 5), FlatTag::Const);
        assert_eq!(w.string_at(u32_at(&w, 5, 0)), "eq");
    }

    /// `A ⟹ B` ≡ non-dependent `Pi(default, Const(A), Const(B))`.
    ///
    /// Arena:
    ///   0: Const(A)
    ///   1: Const(B)
    ///   2: Pi(default, ty=#0, body=#1)   ROOT
    #[test]
    fn test_parse_isabelle_term_meta_implication_is_pi() {
        let mut w = ShardWriter::new();
        let root = parse_isabelle_term("A \u{27F9} B", &mut w).expect("parse");
        assert_eq!(w.expr_count(), 3, "exact node count changed: audit tree");
        assert_eq!(root, 2);
        assert_eq!(tag_of(&w, 2), FlatTag::Pi);
        assert_eq!(u32_at(&w, 2, 0) & 0xff, BINDER_DEFAULT as u32);
        assert_eq!(u32_at(&w, 2, 1), 0, "Pi binder type = Const(A)");
        assert_eq!(u32_at(&w, 2, 5), 1, "Pi body = Const(B)");
        assert_eq!(tag_of(&w, 0), FlatTag::Const);
        assert_eq!(w.string_at(u32_at(&w, 0, 0)), "A");
        assert_eq!(tag_of(&w, 1), FlatTag::Const);
        assert_eq!(w.string_at(u32_at(&w, 1, 0)), "B");
    }

    /// ASCII `A ==> B` lexes identically to the Unicode form.
    #[test]
    fn test_parse_isabelle_term_ascii_meta_implication_is_pi() {
        let mut w = ShardWriter::new();
        let root = parse_isabelle_term("A ==> B", &mut w).expect("parse");
        assert_eq!(tag_of(&w, root), FlatTag::Pi);
    }

    /// `⋀x. P x ⟹ Q x` — meta-quantifier binds `x`; both `P x` and `Q x`
    /// reference it as BVar(0). The outer shape is `Pi(sort0, <imp>)` and
    /// the `⟹` inside is another Pi. Crucially `x` must NOT leak as a
    /// free Const into the string table.
    ///
    /// Arena (post-dedup):
    ///   0: Const(P)
    ///   1: BVar(0)            ; the `x` in `P x`  [shared]
    ///   2: App(P, x)          ; (App #0 #1)
    ///   3: Const(Q)
    ///   4: App(Q, x)          ; (App #3 #1)   — but note the meta-imp pushes
    ///        an extra anonymous binder, so the `x` on the RHS is BVar(1).
    ///        See assertions below for the exact indices.
    #[test]
    fn test_parse_isabelle_term_meta_quantifier_binds_bvar() {
        let mut w = ShardWriter::new();
        let root = parse_isabelle_term("\u{22C0}x. P x \u{27F9} Q x", &mut w).expect("parse");

        // `x` must resolve to a BVar, never a free Const.
        let ss = strings(&w);
        assert!(
            !ss.iter().any(|s| s == "x"),
            "binder name `x` leaked as a free Const: {ss:?}"
        );
        assert!(ss.iter().any(|s| s == "P"), "P missing: {ss:?}");
        assert!(ss.iter().any(|s| s == "Q"), "Q missing: {ss:?}");

        // Root is the meta-quantifier Pi(sort0, <meta-imp>).
        assert_eq!(tag_of(&w, root), FlatTag::Pi);
        let binder_ty = u32_at(&w, root, 1);
        assert_eq!(tag_of(&w, binder_ty), FlatTag::Sort);
        let imp = u32_at(&w, root, 5);
        // The body is the `⟹` Pi.
        assert_eq!(tag_of(&w, imp), FlatTag::Pi);

        // LHS of `⟹` is `P x`, with x = BVar(0) (one binder: the ⋀).
        let lhs = u32_at(&w, imp, 1);
        assert_eq!(tag_of(&w, lhs), FlatTag::App);
        let p_x = u32_at(&w, lhs, 4);
        assert_eq!(tag_of(&w, p_x), FlatTag::BVar);
        assert_eq!(u32_at(&w, p_x, 0), 0, "x in `P x` is BVar(0)");

        // RHS of `⟹` is `Q x`. The meta-imp pushed one anonymous binder,
        // so `x` there is BVar(1) (skip past the `_` of the imp).
        let rhs = u32_at(&w, imp, 5);
        assert_eq!(tag_of(&w, rhs), FlatTag::App);
        let q_x = u32_at(&w, rhs, 4);
        assert_eq!(tag_of(&w, q_x), FlatTag::BVar);
        assert_eq!(u32_at(&w, q_x, 0), 1, "x in `Q x` (RHS of ⟹) is BVar(1)");
    }

    #[test]
    fn test_parse_isabelle_term_object_forall_is_const_applied_lambda() {
        // `∀x. P x` → App(Const(All), Lam(sort0, App(Const(P), BVar0))).
        let mut w = ShardWriter::new();
        let root = parse_isabelle_term("\u{2200}x. P x", &mut w).expect("parse");
        assert_eq!(tag_of(&w, root), FlatTag::App);
        let head = u32_at(&w, root, 0);
        assert_eq!(tag_of(&w, head), FlatTag::Const);
        assert_eq!(w.string_at(u32_at(&w, head, 0)), "All");
        let lam = u32_at(&w, root, 4);
        assert_eq!(tag_of(&w, lam), FlatTag::Lam);
        let body = u32_at(&w, lam, 5);
        assert_eq!(tag_of(&w, body), FlatTag::App);
        let arg = u32_at(&w, body, 4);
        assert_eq!(tag_of(&w, arg), FlatTag::BVar);
        assert_eq!(u32_at(&w, arg, 0), 0);
        // `x` must not leak as a free Const.
        assert!(!strings(&w).iter().any(|s| s == "x"));
    }

    #[test]
    fn test_parse_isabelle_term_ascii_quantifier_keywords() {
        // ALL / EX keyword spellings.
        let mut w = ShardWriter::new();
        assert!(parse_isabelle_term("ALL x. P x", &mut w).is_some());
        let mut w2 = ShardWriter::new();
        assert!(parse_isabelle_term("EX x. P x", &mut w2).is_some());
    }

    #[test]
    fn test_parse_isabelle_term_object_connectives() {
        // `a & b | c` parses; `&` binds tighter than `|`.
        let mut w = ShardWriter::new();
        let root = parse_isabelle_term("a & b | c", &mut w).expect("parse");
        // Top operator is disj.
        assert_eq!(tag_of(&w, root), FlatTag::App);
        let head = u32_at(&w, root, 0);
        assert_eq!(tag_of(&w, head), FlatTag::App);
        let op = u32_at(&w, head, 0);
        assert_eq!(w.string_at(u32_at(&w, op, 0)), "disj");
    }

    #[test]
    fn test_parse_isabelle_term_negation_prefix() {
        // `~ a` → App(Const(not), Const(a)).
        let mut w = ShardWriter::new();
        let root = parse_isabelle_term("~ a", &mut w).expect("parse");
        assert_eq!(tag_of(&w, root), FlatTag::App);
        let head = u32_at(&w, root, 0);
        assert_eq!(w.string_at(u32_at(&w, head, 0)), "not");
    }

    #[test]
    fn test_parse_isabelle_term_type_ascription_stripped() {
        // `(x :: nat) = x` — the `:: nat` is dropped, the term is `x = x`.
        let mut w = ShardWriter::new();
        let root = parse_isabelle_term("(x :: nat) = x", &mut w).expect("parse");
        assert_eq!(tag_of(&w, root), FlatTag::App);
        // `nat` must not appear as a term Const (it was a type).
        assert!(
            !strings(&w).iter().any(|s| s == "nat"),
            "type `nat` leaked into the term: {:?}",
            strings(&w)
        );
    }

    #[test]
    fn test_parse_isabelle_term_schematic_var_is_free_const() {
        // `?x = ?x` — schematics kept verbatim as free Consts `?x`.
        let mut w = ShardWriter::new();
        let _ = parse_isabelle_term("?x = ?x", &mut w).expect("parse");
        assert!(
            strings(&w).iter().any(|s| s == "?x"),
            "schematic var not interned as `?x`: {:?}",
            strings(&w)
        );
    }

    #[test]
    fn test_parse_isabelle_term_empty_is_none() {
        let mut w = ShardWriter::new();
        assert!(parse_isabelle_term("", &mut w).is_none());
        assert!(parse_isabelle_term("   ", &mut w).is_none());
    }

    #[test]
    fn test_parse_isabelle_term_lambda_unsupported_skips() {
        // Lambda abstraction is out of scope → skip (None), not fake.
        let mut w = ShardWriter::new();
        assert!(parse_isabelle_term("%x. x", &mut w).is_none());
    }

    #[test]
    fn test_parse_isabelle_term_emits_real_tree_not_placeholder() {
        let mut w = ShardWriter::new();
        let _ = parse_isabelle_term("x + 0 = x", &mut w).expect("parse");
        assert!(w.expr_count() > 3, "expected a real tree");
    }
}
