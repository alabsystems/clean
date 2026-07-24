// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Dafny surface-syntax type parser → `FlatExpr` tree.
//!
//! Translates a Dafny **type expression** string (the text of a
//! parameter type or a return type, e.g. `int`, `seq<int>`,
//! `map<int, bool>`, `T -> U`) into a structural `FlatExpr` tree written
//! into a [`ShardWriter`], and assembles a whole declaration's type as a
//! right-associative arrow from its parameter types to its result type.
//!
//! # What is translated
//!
//! - **Base / named types** (`int`, `nat`, `bool`, `real`, `char`,
//!   `string`, `object`, and any user type name) → `Const(name)`.
//! - **Generic / collection applications**: `seq<T>` ⇒
//!   `App(Const("seq"), T)`; `map<K, V>` ⇒
//!   `App(App(Const("map"), K), V)`. Each `<...>` argument list is
//!   folded left-to-right into nested `App` nodes over the head type,
//!   exactly like a curried type constructor.
//! - **Function types** `T -> U` → `Pi(_ : T, U)` (a non-dependent
//!   arrow), right-associative so `T -> U -> V` is `T -> (U -> V)`.
//! - **Tuples** `(T, U)` → `App(App(Const("Tuple2"), T), U)`, and in
//!   general an n-tuple → `Const("Tuplen")` applied to its components.
//!   A parenthesised single type `(T)` is just `T` (grouping).
//!   A tupled-domain function `(T, U) -> V` therefore parses as
//!   `Tuple2 T U -> V`.
//!
//! # What is NOT translated (parser returns `None` → caller skips)
//!
//! Refinement types (`int | f(x)`), arrow subset/`-->`/`~>` partial and
//! total function arrows beyond the plain `->`, `nat`-style constraints,
//! and any expression-level syntax. `requires` / `ensures` bodies are
//! out of scope by design — only the parameter-types→result arrow is the
//! deliverable. When a type can't be faithfully rendered the parser
//! returns `None`; the importer then **skips** the declaration rather
//! than emitting a `sort(0)` placeholder.
//!
//! Universe choices are not modelled: this is a Level-0/1 data import,
//! NOT a verified elaboration. Type constructors are emitted as free
//! `Const` references under their Dafny surface names.

use clean_kernel::flat::FlatExpr;

use crate::shard::ShardWriter;

/// `levels_list_idx` sentinel meaning "no universe levels".
const NO_LEVELS: u32 = u32::MAX;
/// Non-dependent arrow binder info (`Default`).
const BINDER_DEFAULT: u8 = 0;

#[derive(Debug, Clone, PartialEq, Eq)]
enum Tok {
    Ident(String),
    LParen,
    RParen,
    LAngle,
    RAngle,
    Comma,
    /// `->` total function arrow.
    Arrow,
}

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
            }
            ')' => {
                out.push(Tok::RParen);
                i += 1;
            }
            '<' => {
                out.push(Tok::LAngle);
                i += 1;
            }
            '>' => {
                out.push(Tok::RAngle);
                i += 1;
            }
            ',' => {
                out.push(Tok::Comma);
                i += 1;
            }
            '-' if chars.get(i + 1) == Some(&'>') => {
                out.push(Tok::Arrow);
                i += 2;
            }
            _ if is_ident_start(ch) => {
                let start = i;
                i += 1;
                while i < chars.len() && is_ident_continue(chars[i]) {
                    i += 1;
                }
                out.push(Tok::Ident(chars[start..i].iter().collect()));
            }
            // Any other character (refinement `|`, partial arrows, `?`,
            // bit-vector width digits glued to a name, …) is something
            // we do not faithfully model — refuse the whole type.
            _ => return None,
        }
    }
    Some(out)
}

fn is_ident_start(ch: char) -> bool {
    ch.is_alphabetic() || ch == '_'
}

fn is_ident_continue(ch: char) -> bool {
    ch.is_alphanumeric() || ch == '_' || ch == '.' || ch == '\''
}

struct Parser<'w> {
    toks: Vec<Tok>,
    pos: usize,
    writer: &'w mut ShardWriter,
    /// Hard cap on emitted exprs — guards against pathological inputs.
    expr_budget: u32,
}

impl<'w> Parser<'w> {
    fn new(toks: Vec<Tok>, writer: &'w mut ShardWriter) -> Self {
        Self {
            toks,
            pos: 0,
            writer,
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

    fn const_named(&mut self, name: &str) -> Option<u32> {
        let name_idx = self.writer.add_string(name);
        self.add(FlatExpr::const_ref(name_idx, NO_LEVELS))
    }

    /// `type := arrow`. A full type is a (possibly trivial) right-assoc
    /// arrow chain.
    fn parse_type(&mut self) -> Option<u32> {
        let lhs = self.parse_atom()?;
        if self.eat(&Tok::Arrow) {
            let rhs = self.parse_type()?; // right-associative
            self.add(FlatExpr::pi(BINDER_DEFAULT, lhs, rhs))
        } else {
            Some(lhs)
        }
    }

    /// `atom := ident generic-args? | '(' tuple-or-group ')'`.
    fn parse_atom(&mut self) -> Option<u32> {
        match self.peek().cloned()? {
            Tok::Ident(name) => {
                self.bump();
                let head = self.const_named(&name)?;
                if matches!(self.peek(), Some(Tok::LAngle)) {
                    self.parse_generic_args(head)
                } else {
                    Some(head)
                }
            }
            Tok::LParen => self.parse_paren(),
            _ => None,
        }
    }

    /// `'<' type (',' type)* '>'` applied left-to-right to `head`.
    fn parse_generic_args(&mut self, head: u32) -> Option<u32> {
        if !self.eat(&Tok::LAngle) {
            return None;
        }
        let mut acc = head;
        loop {
            let arg = self.parse_type()?;
            acc = self.add(FlatExpr::app(acc, arg))?;
            if self.eat(&Tok::Comma) {
                continue;
            }
            break;
        }
        if !self.eat(&Tok::RAngle) {
            return None;
        }
        Some(acc)
    }

    /// `'(' type (',' type)* ')'`. One element is a grouping; two or
    /// more form a tuple `Tuplen T0 .. T(n-1)`. Empty `()` is rejected
    /// (Dafny uses it for the unit/`()` return which we don't model).
    fn parse_paren(&mut self) -> Option<u32> {
        if !self.eat(&Tok::LParen) {
            return None;
        }
        let mut elems = Vec::new();
        if !matches!(self.peek(), Some(Tok::RParen)) {
            loop {
                elems.push(self.parse_type()?);
                if self.eat(&Tok::Comma) {
                    continue;
                }
                break;
            }
        }
        if !self.eat(&Tok::RParen) {
            return None;
        }
        match elems.len() {
            0 => None,
            1 => Some(elems[0]),
            n => {
                let head = self.const_named(&format!("Tuple{n}"))?;
                let mut acc = head;
                for elem in elems {
                    acc = self.add(FlatExpr::app(acc, elem))?;
                }
                Some(acc)
            }
        }
    }
}

/// Parse a single Dafny type expression into the writer. Returns the
/// root expression index, or `None` on parse failure / empty input. A
/// `None` means "skip this declaration", never "emit a placeholder".
pub(crate) fn parse_dafny_type(src: &str, writer: &mut ShardWriter) -> Option<u32> {
    let toks = lex(src)?;
    if toks.is_empty() {
        return None;
    }
    let mut p = Parser::new(toks, writer);
    let root = p.parse_type()?;
    // Require the whole token stream to be consumed: a trailing token
    // means the type form is something we did not model faithfully.
    if p.pos != p.toks.len() {
        return None;
    }
    Some(root)
}

/// Assemble a declaration's overall type as the right-associative arrow
/// `P0 -> P1 -> ... -> Result`, where each `Pi` is a parameter type and
/// `Result` is the result type. Every component is parsed via
/// [`parse_dafny_type`]; if any component fails to parse, the whole
/// declaration type is rejected (`None`) so the importer skips it rather
/// than emitting partial/fake structure.
///
/// `params` is the list of parameter-type strings in order; `result` is
/// the result-type string (already chosen per decl kind by the caller —
/// e.g. `Prop` for a lemma, the `returns`/`:` type for a method or
/// function).
pub(crate) fn assemble_decl_type(
    params: &[String],
    result: &str,
    writer: &mut ShardWriter,
) -> Option<u32> {
    let result_idx = parse_dafny_type(result, writer)?;
    let mut param_idxs = Vec::with_capacity(params.len());
    for p in params {
        param_idxs.push(parse_dafny_type(p, writer)?);
    }
    let mut acc = result_idx;
    for ty in param_idxs.into_iter().rev() {
        if writer.expr_count() == 0 {
            return None;
        }
        acc = writer.add_expr(FlatExpr::pi(BINDER_DEFAULT, ty, acc));
    }
    Some(acc)
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::flat::FlatTag;

    /// Read the tag of the expr at `idx`.
    fn tag_at(w: &ShardWriter, idx: u32) -> FlatTag {
        w.expr_at(idx)
            .expect("expr in range")
            .tag()
            .expect("valid tag")
    }

    /// Const at `idx` → its interned name.
    fn const_name(w: &ShardWriter, idx: u32) -> String {
        let e = w.expr_at(idx).expect("expr in range");
        assert_eq!(e.tag().expect("tag"), FlatTag::Const, "expected Const");
        let name_idx = e.read_u32(0).expect("name_idx");
        w.string_at(name_idx).to_string()
    }

    /// App at `idx` → (fn_idx, arg_idx).
    fn app_parts(w: &ShardWriter, idx: u32) -> (u32, u32) {
        let e = w.expr_at(idx).expect("expr in range");
        assert_eq!(e.tag().expect("tag"), FlatTag::App, "expected App");
        (e.read_u32(0).expect("fn"), e.read_u32(4).expect("arg"))
    }

    /// Pi at `idx` → (ty_idx, body_idx).
    fn pi_parts(w: &ShardWriter, idx: u32) -> (u32, u32) {
        let e = w.expr_at(idx).expect("expr in range");
        assert_eq!(e.tag().expect("tag"), FlatTag::Pi, "expected Pi");
        // Pi data layout: u8 binder_info, u32 ty_idx@1, u32 body_idx@5.
        (e.read_u32(1).expect("ty"), e.read_u32(5).expect("body"))
    }

    #[test]
    fn test_parse_dafny_type_base_is_single_const() {
        let mut w = ShardWriter::new();
        let root = parse_dafny_type("int", &mut w).expect("parse int");
        assert_eq!(tag_at(&w, root), FlatTag::Const);
        assert_eq!(const_name(&w, root), "int");
        // Exactly one expr emitted.
        assert_eq!(w.expr_count(), 1);
    }

    #[test]
    fn test_parse_dafny_type_seq_int_is_app_const_const() {
        // seq<int> ⇒ App(Const("seq"), Const("int")).
        let mut w = ShardWriter::new();
        let root = parse_dafny_type("seq<int>", &mut w).expect("parse seq<int>");
        let (head, arg) = app_parts(&w, root);
        assert_eq!(const_name(&w, head), "seq");
        assert_eq!(const_name(&w, arg), "int");
        // Const(seq), Const(int), App = exactly 3 unique exprs.
        assert_eq!(w.expr_count(), 3);
    }

    #[test]
    fn test_parse_dafny_type_map_is_curried_app() {
        // map<int, bool> ⇒ App(App(Const("map"), Const("int")), Const("bool")).
        let mut w = ShardWriter::new();
        let root = parse_dafny_type("map<int, bool>", &mut w).expect("parse map");
        let (inner, bool_arg) = app_parts(&w, root);
        assert_eq!(const_name(&w, bool_arg), "bool");
        let (map_head, int_arg) = app_parts(&w, inner);
        assert_eq!(const_name(&w, map_head), "map");
        assert_eq!(const_name(&w, int_arg), "int");
        // Const(map), Const(int), Const(bool), App(map,int), App(.,bool) = 5.
        assert_eq!(w.expr_count(), 5);
    }

    #[test]
    fn test_parse_dafny_type_arrow_is_pi() {
        // int -> bool ⇒ Pi(int, bool).
        let mut w = ShardWriter::new();
        let root = parse_dafny_type("int -> bool", &mut w).expect("parse arrow");
        let (ty, body) = pi_parts(&w, root);
        assert_eq!(const_name(&w, ty), "int");
        assert_eq!(const_name(&w, body), "bool");
    }

    #[test]
    fn test_parse_dafny_type_arrow_right_associative() {
        // int -> nat -> bool ⇒ Pi(int, Pi(nat, bool)).
        let mut w = ShardWriter::new();
        let root = parse_dafny_type("int -> nat -> bool", &mut w).expect("parse");
        let (a, inner) = pi_parts(&w, root);
        assert_eq!(const_name(&w, a), "int");
        let (b, c) = pi_parts(&w, inner);
        assert_eq!(const_name(&w, b), "nat");
        assert_eq!(const_name(&w, c), "bool");
    }

    #[test]
    fn test_parse_dafny_type_tuple_is_tuple2_app() {
        // (int, bool) ⇒ App(App(Const("Tuple2"), int), bool).
        let mut w = ShardWriter::new();
        let root = parse_dafny_type("(int, bool)", &mut w).expect("parse tuple");
        let (inner, bool_arg) = app_parts(&w, root);
        assert_eq!(const_name(&w, bool_arg), "bool");
        let (head, int_arg) = app_parts(&w, inner);
        assert_eq!(const_name(&w, head), "Tuple2");
        assert_eq!(const_name(&w, int_arg), "int");
    }

    #[test]
    fn test_parse_dafny_type_paren_single_is_grouping() {
        // (int) ⇒ int (grouping, not a 1-tuple).
        let mut w = ShardWriter::new();
        let root = parse_dafny_type("(int)", &mut w).expect("parse group");
        assert_eq!(const_name(&w, root), "int");
        assert_eq!(w.expr_count(), 1);
    }

    #[test]
    fn test_parse_dafny_type_tupled_arrow() {
        // (int, bool) -> nat ⇒ Pi(Tuple2 int bool, nat).
        let mut w = ShardWriter::new();
        let root = parse_dafny_type("(int, bool) -> nat", &mut w).expect("parse");
        let (dom, body) = pi_parts(&w, root);
        assert_eq!(const_name(&w, body), "nat");
        let (inner, b) = app_parts(&w, dom);
        assert_eq!(const_name(&w, b), "bool");
        let (head, a) = app_parts(&w, inner);
        assert_eq!(const_name(&w, head), "Tuple2");
        assert_eq!(const_name(&w, a), "int");
    }

    #[test]
    fn test_parse_dafny_type_rejects_refinement() {
        // Refinement `int | ...` uses `|`, which we do not model.
        let mut w = ShardWriter::new();
        assert!(parse_dafny_type("int | f(x)", &mut w).is_none());
    }

    #[test]
    fn test_parse_dafny_type_empty_is_none() {
        let mut w = ShardWriter::new();
        assert!(parse_dafny_type("", &mut w).is_none());
        assert!(parse_dafny_type("   ", &mut w).is_none());
    }

    #[test]
    fn test_assemble_decl_type_method_int_to_int() {
        // method M(x: int) returns (y: int) ⇒ params [int], result int
        // ⇒ Pi(int, int).
        let mut w = ShardWriter::new();
        let params = vec!["int".to_string()];
        let root = assemble_decl_type(&params, "int", &mut w).expect("assemble");
        let (ty, body) = pi_parts(&w, root);
        assert_eq!(const_name(&w, ty), "int");
        assert_eq!(const_name(&w, body), "int");
        // Const(int) is shared (dedup) → Const(int), Pi = 2 unique exprs.
        assert_eq!(w.expr_count(), 2);
    }

    #[test]
    fn test_assemble_decl_type_two_params_chains_arrows() {
        // params [int, nat], result bool ⇒ Pi(int, Pi(nat, bool)).
        let mut w = ShardWriter::new();
        let params = vec!["int".to_string(), "nat".to_string()];
        let root = assemble_decl_type(&params, "bool", &mut w).expect("assemble");
        let (a, inner) = pi_parts(&w, root);
        assert_eq!(const_name(&w, a), "int");
        let (b, c) = pi_parts(&w, inner);
        assert_eq!(const_name(&w, b), "nat");
        assert_eq!(const_name(&w, c), "bool");
    }

    #[test]
    fn test_assemble_decl_type_lemma_to_prop() {
        // lemma L(x: int) ⇒ params [int], result Prop ⇒ Pi(int, Const("Prop")).
        let mut w = ShardWriter::new();
        let params = vec!["int".to_string()];
        let root = assemble_decl_type(&params, "Prop", &mut w).expect("assemble");
        let (ty, body) = pi_parts(&w, root);
        assert_eq!(const_name(&w, ty), "int");
        assert_eq!(const_name(&w, body), "Prop");
    }

    #[test]
    fn test_assemble_decl_type_no_params_is_result_only() {
        // A nullary decl is just its result type, no Pi wrapper.
        let mut w = ShardWriter::new();
        let root = assemble_decl_type(&[], "bool", &mut w).expect("assemble");
        assert_eq!(const_name(&w, root), "bool");
    }

    #[test]
    fn test_assemble_decl_type_unparseable_param_is_none() {
        let mut w = ShardWriter::new();
        let params = vec!["int | f".to_string()];
        assert!(assemble_decl_type(&params, "int", &mut w).is_none());
    }
}
