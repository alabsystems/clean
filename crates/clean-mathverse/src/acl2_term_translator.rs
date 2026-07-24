// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! ACL2 s-expression → `FlatExpr` term translator.
//!
//! ACL2 is dynamically typed: there is no surface "type signature" the
//! way Lean or Coq has one. The closest faithful analogue for the
//! `.mathverse` shard's `type_idx` slot is the **term shape** of the
//! declaration's logical content:
//!
//! * `(defthm NAME STMT)` / `(defrule NAME STMT)` — the statement
//!   `STMT` is an untyped term (e.g. `(equal (+ 0 x) x)`). We translate
//!   it into a nested-`App` tree over `Const` heads: the call
//!   `(f a b)` becomes `App(App(Const(f), <a>), <b>)`. Numeric literals
//!   become `LitNat`; free symbols become `Const(name)`.
//! * `(defun NAME (a b …) BODY)` — the lambda list `(a b …)` introduces
//!   binders. We translate `BODY` with those names in scope and wrap the
//!   result in nested `Lam`: `Lam a, Lam b, <BODY>`. Symbols matching a
//!   binder resolve to `BVar` (de Bruijn, innermost-first); everything
//!   else is a free `Const`.
//!
//! This is a **Level-0/1 structural data import**, NOT a kernel-verified
//! term: the emitted tree mirrors the surface s-expression but is not
//! type-checked, and ACL2's evaluation semantics are not modelled. The
//! caller records `ImportConfidence::Unverified` +
//! `AxiomProfile::AXIOMATIZED` accordingly.
//!
//! Scope. We translate the common `defthm`/`defrule`/`defun` shapes
//! above. Forms whose body we cannot faithfully render — quoted data
//! (`'(...)` / `` `(...) ``), `defmacro` (macro expansion is not term
//! structure), `defconst` (opaque value), `defstobj` (no logical term),
//! and any form with a malformed/empty body — yield `None`, and the
//! caller **skips** the declaration rather than emit a placeholder. A
//! correct partial translation is preferred over a broad wrong one.
//!
//! Like [`crate::lean3_type_parser`], the output is a real structural
//! tree: `(equal (+ 0 x) x)` under a `defun (x)`-style binder produces
//! several distinct `FlatExpr` nodes, not one shared placeholder per
//! constant, so the resulting shard satisfies
//! `expr_count > constant_count`.

use clean_kernel::flat::FlatExpr;

use crate::shard::ShardWriter;

/// `levels_list_idx` sentinel meaning "this `Const` carries no universe
/// levels" (matches the convention used by `lean3_type_parser`).
const NO_LEVELS: u32 = u32::MAX;

/// `Lam`/`Pi` binder-info byte for an ordinary explicit binder.
const BINDER_DEFAULT: u8 = 0;

/// Hard cap on emitted exprs per declaration. Guards against pathological
/// or deeply nested inputs; a translation that would exceed the budget
/// fails (→ skip) rather than running unbounded.
const EXPR_BUDGET: u32 = 8192;

/// A parsed s-expression: an atom (symbol or number) or a proper list.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Sexp {
    /// A symbol atom, e.g. `equal`, `x`, `+`. Stored verbatim.
    Sym(String),
    /// A non-negative integer literal, e.g. `0`, `42`.
    Nat(u64),
    /// A parenthesised list of sub-forms.
    List(Vec<Sexp>),
}

/// Reader over the raw form characters. Produces [`Sexp`] trees.
///
/// Quote/quasiquote/unquote markers (`'`, `` ` ``, `,`, `,@`, `#`) cause
/// the reader to fail (`None`) for the affected form: quoted data is not
/// term structure and translating it would misrepresent the source.
struct Reader<'a> {
    chars: &'a [char],
    pos: usize,
}

impl<'a> Reader<'a> {
    fn new(chars: &'a [char]) -> Self {
        Self { chars, pos: 0 }
    }

    fn peek(&self) -> Option<char> {
        self.chars.get(self.pos).copied()
    }

    fn bump(&mut self) -> Option<char> {
        let c = self.chars.get(self.pos).copied()?;
        self.pos += 1;
        Some(c)
    }

    fn skip_ws(&mut self) {
        while let Some(c) = self.peek() {
            if c.is_whitespace() {
                self.pos += 1;
            } else {
                break;
            }
        }
    }

    /// Read a single s-expression, or `None` on EOF / unsupported syntax.
    fn read(&mut self) -> Option<Sexp> {
        self.skip_ws();
        match self.peek()? {
            '(' => self.read_list(),
            ')' => None,
            // Reader macros for quoted/structured data are not term
            // structure — bail so the caller skips this declaration.
            '\'' | '`' | ',' | '#' => None,
            '"' => None, // string literals: out of scope, skip the form.
            _ => self.read_atom(),
        }
    }

    fn read_list(&mut self) -> Option<Sexp> {
        // Consume the opening '('.
        if self.bump()? != '(' {
            return None;
        }
        let mut items = Vec::new();
        loop {
            self.skip_ws();
            match self.peek()? {
                ')' => {
                    self.pos += 1;
                    return Some(Sexp::List(items));
                }
                '\'' | '`' | ',' | '#' | '"' => return None,
                _ => items.push(self.read()?),
            }
        }
    }

    fn read_atom(&mut self) -> Option<Sexp> {
        let start = self.pos;
        while let Some(c) = self.peek() {
            if c.is_whitespace() || c == '(' || c == ')' {
                break;
            }
            // A reader-macro char embedded in an atom (e.g. `a'b`) is
            // unusual; treat it as a terminator so we don't silently
            // swallow quoting semantics.
            if matches!(c, '\'' | '`' | ',' | '"') {
                break;
            }
            self.pos += 1;
        }
        if self.pos == start {
            return None;
        }
        let text: String = self.chars[start..self.pos].iter().collect();
        Some(atom_from_text(&text))
    }
}

/// Classify a bare atom token as a numeric literal or a symbol.
fn atom_from_text(text: &str) -> Sexp {
    if let Ok(n) = text.parse::<u64>() {
        Sexp::Nat(n)
    } else {
        Sexp::Sym(text.to_owned())
    }
}

/// Translator state: the writer plus the current binder scope and budget.
struct Translator<'w> {
    writer: &'w mut ShardWriter,
    /// Binder names in scope, outermost first. Innermost match wins, so a
    /// symbol's de Bruijn index is `len - 1 - rposition`.
    bound: Vec<String>,
    budget: u32,
}

impl<'w> Translator<'w> {
    fn new(writer: &'w mut ShardWriter) -> Self {
        Self {
            writer,
            bound: Vec::new(),
            budget: EXPR_BUDGET,
        }
    }

    fn add(&mut self, e: FlatExpr) -> Option<u32> {
        if self.budget == 0 {
            return None;
        }
        self.budget -= 1;
        Some(self.writer.add_expr(e))
    }

    /// Translate one term s-expression into a `FlatExpr` tree, returning
    /// the root index.
    fn term(&mut self, sexp: &Sexp) -> Option<u32> {
        match sexp {
            Sexp::Nat(n) => self.add(FlatExpr::lit_nat(*n)),
            Sexp::Sym(name) => self.symbol(name),
            Sexp::List(items) => self.application(items),
        }
    }

    /// A symbol resolves to a `BVar` if it is bound, else a free `Const`.
    fn symbol(&mut self, name: &str) -> Option<u32> {
        if let Some(pos) = self.bound.iter().rposition(|n| n == name) {
            let depth = (self.bound.len() - 1 - pos) as u32;
            return self.add(FlatExpr::bvar(depth));
        }
        let name_idx = self.writer.add_string(name);
        self.add(FlatExpr::const_ref(name_idx, NO_LEVELS))
    }

    /// A list `(head a b …)` translates to left-nested application
    /// `App(App(App(<head>, <a>), <b>), …)`. The head is itself a term
    /// (usually a symbol, occasionally a nested list), so higher-order
    /// applications survive. An empty list `()` (ACL2 `nil`) becomes the
    /// free constant `nil`.
    fn application(&mut self, items: &[Sexp]) -> Option<u32> {
        let Some((head, args)) = items.split_first() else {
            // `()` ≡ nil.
            let nil_idx = self.writer.add_string("nil");
            return self.add(FlatExpr::const_ref(nil_idx, NO_LEVELS));
        };
        let mut acc = self.term(head)?;
        for arg in args {
            let arg_idx = self.term(arg)?;
            acc = self.add(FlatExpr::app(acc, arg_idx))?;
        }
        Some(acc)
    }

    /// Translate a `defun` lambda list + body into nested lambdas.
    ///
    /// `(a b …)` introduces binders left-to-right; `BODY` is translated
    /// with them in scope. The result is `Lam a, Lam b, …, <BODY>`. Each
    /// binder's type is left as `sort(0)` (ACL2 has no surface type to
    /// record) — note this is a per-binder annotation slot, NOT the
    /// forbidden one-shared-placeholder-per-constant antipattern: the
    /// lambda bodies are real translated trees.
    fn lambda(&mut self, params: &[String], body: &Sexp) -> Option<u32> {
        for p in params {
            self.bound.push(p.clone());
        }
        let body_idx = self.term(body);
        for _ in params {
            self.bound.pop();
        }
        let mut acc = body_idx?;
        for _ in params.iter().rev() {
            let ty = self.add(FlatExpr::sort(0))?;
            acc = self.add(FlatExpr::lam(BINDER_DEFAULT, ty, acc))?;
        }
        Some(acc)
    }
}

/// Translate the logical content of an ACL2 form into a `FlatExpr` tree,
/// returning the root index. Returns `None` when the form's body cannot
/// be faithfully translated; callers must then **skip** the declaration
/// (never emit a placeholder).
///
/// `form` is the full raw form text, e.g.
/// `(defthm foo (equal (+ 0 x) x))` or `(defun double (x) (* 2 x))`.
pub(crate) fn translate_acl2_form(form: &str, writer: &mut ShardWriter) -> Option<u32> {
    let chars: Vec<char> = form.chars().collect();
    let mut reader = Reader::new(&chars);
    let top = reader.read()?;
    let Sexp::List(items) = top else {
        return None;
    };
    let head = match items.first() {
        Some(Sexp::Sym(h)) => h.as_str(),
        _ => return None,
    };
    let mut tr = Translator::new(writer);
    match head {
        // `(defthm NAME STMT ...)` / `(defrule NAME STMT ...)`: the third
        // element is the statement term. Trailing :hints/:rule-classes
        // keyword args are ignored — only the statement is the deliverable.
        "defthm" | "defrule" => {
            let stmt = items.get(2)?;
            tr.term(stmt)
        }
        // `(defun NAME (params...) BODY)`: element 2 is the lambda list,
        // element 3 is the body. (Declare forms / docstrings between the
        // arglist and body are not handled; such a defun is skipped.)
        "defun" => {
            let Sexp::List(arglist) = items.get(2)? else {
                return None;
            };
            let params = arglist
                .iter()
                .map(|s| match s {
                    Sexp::Sym(name) => Some(name.clone()),
                    _ => None,
                })
                .collect::<Option<Vec<_>>>()?;
            let body = items.get(3)?;
            tr.lambda(&params, body)
        }
        // defmacro / defconst / defstobj and anything else: no faithful
        // term translation. Skip.
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::flat::FlatTag;

    /// Decode an expr index back into a readable shape for assertions.
    fn tag_of(w: &ShardWriter, idx: u32) -> FlatTag {
        w.expr_at(idx)
            .expect("expr in range")
            .tag()
            .expect("valid tag")
    }

    /// Read a u32 field from the expr at `idx`.
    fn field_u32(w: &ShardWriter, idx: u32, off: usize) -> u32 {
        w.expr_at(idx)
            .expect("expr in range")
            .read_u32(off)
            .expect("u32")
    }

    /// Read a u64 field from the expr at `idx`.
    fn field_u64(w: &ShardWriter, idx: u32, off: usize) -> u64 {
        w.expr_at(idx)
            .expect("expr in range")
            .read_u64(off)
            .expect("u64")
    }

    #[test]
    fn reader_parses_nested_list() {
        let chars: Vec<char> = "(equal (+ 0 x) x)".chars().collect();
        let mut r = Reader::new(&chars);
        let sexp = r.read().expect("parse");
        assert_eq!(
            sexp,
            Sexp::List(vec![
                Sexp::Sym("equal".into()),
                Sexp::List(vec![
                    Sexp::Sym("+".into()),
                    Sexp::Nat(0),
                    Sexp::Sym("x".into()),
                ]),
                Sexp::Sym("x".into()),
            ])
        );
    }

    #[test]
    fn reader_rejects_quoted_data() {
        let chars: Vec<char> = "(equal '(a b) x)".chars().collect();
        let mut r = Reader::new(&chars);
        assert!(r.read().is_none(), "quoted list must abort the read");
    }

    /// PIN the exact FlatExpr tree for `(equal (+ 0 x) x)` translated as a
    /// free-standing statement (no enclosing defun, so x is a free Const).
    ///
    /// Expected arena (post-dedup, in add order):
    ///   0: Const(equal)
    ///   1: Const(+)
    ///   2: LitNat(0)
    ///   3: App(+, 0)              ; (App #1 #2)
    ///   4: Const(x)
    ///   5: App((+ 0), x)          ; (App #3 #4)   == (+ 0 x)
    ///   6: App(equal, (+ 0 x))    ; (App #0 #5)
    ///   7: App((equal (+ 0 x)), x); (App #6 #4)   ROOT
    #[test]
    fn equal_plus_zero_x_x_exact_tree() {
        let mut w = ShardWriter::new();
        let root = translate_acl2_form("(defthm t1 (equal (+ 0 x) x))", &mut w).expect("translate");

        // Root is the outer App.
        assert_eq!(root, 7);
        assert_eq!(tag_of(&w, 7), FlatTag::App);
        // (equal (+ 0 x)) applied to x.
        assert_eq!(field_u32(&w, 7, 0), 6); // fn = #6
        assert_eq!(field_u32(&w, 7, 4), 4); // arg = Const(x) #4

        // #6 = App(Const(equal) #0, (+ 0 x) #5)
        assert_eq!(tag_of(&w, 6), FlatTag::App);
        assert_eq!(field_u32(&w, 6, 0), 0);
        assert_eq!(field_u32(&w, 6, 4), 5);

        // #5 = App((+ 0) #3, x #4)
        assert_eq!(tag_of(&w, 5), FlatTag::App);
        assert_eq!(field_u32(&w, 5, 0), 3);
        assert_eq!(field_u32(&w, 5, 4), 4);

        // #3 = App(+ #1, 0 #2)
        assert_eq!(tag_of(&w, 3), FlatTag::App);
        assert_eq!(field_u32(&w, 3, 0), 1);
        assert_eq!(field_u32(&w, 3, 4), 2);

        // Leaf atoms.
        assert_eq!(tag_of(&w, 0), FlatTag::Const);
        assert_eq!(tag_of(&w, 1), FlatTag::Const);
        assert_eq!(tag_of(&w, 2), FlatTag::LitNat);
        assert_eq!(field_u64(&w, 2, 0), 0);
        assert_eq!(tag_of(&w, 4), FlatTag::Const);

        // Const names: equal, +, x (in add order after the empty sentinel).
        assert_eq!(w.string_at(field_u32(&w, 0, 0)), "equal");
        assert_eq!(w.string_at(field_u32(&w, 1, 0)), "+");
        assert_eq!(w.string_at(field_u32(&w, 4, 0)), "x");
    }

    #[test]
    fn defun_binds_params_as_bvars() {
        // (defun double (x) (* 2 x)) → Lam (sort0) (App (App (Const *) 2) (BVar 0))
        let mut w = ShardWriter::new();
        let root = translate_acl2_form("(defun double (x) (* 2 x))", &mut w).expect("translate");

        // Root is a Lam.
        assert_eq!(tag_of(&w, root), FlatTag::Lam);
        let body_idx = field_u32(&w, root, 5); // Lam body at offset 5
        assert_eq!(tag_of(&w, body_idx), FlatTag::App);

        // The inner argument `x` must be a BVar(0), NOT a free Const.
        let arg_idx = field_u32(&w, body_idx, 4);
        assert_eq!(tag_of(&w, arg_idx), FlatTag::BVar);
        assert_eq!(field_u32(&w, arg_idx, 0), 0);

        // `x` must not leak into the string table as a free Const name.
        let strings: Vec<&str> = (0..w.string_count())
            .map(|i| w.string_at(i as u32))
            .collect();
        assert!(
            !strings.contains(&"x"),
            "binder `x` leaked as a free Const: {strings:?}"
        );
    }

    #[test]
    fn defun_two_params_distinct_de_bruijn() {
        // (defun f (x y) (cons x y)) — inside the body, y is BVar(0)
        // (innermost) and x is BVar(1).
        let mut w = ShardWriter::new();
        let root = translate_acl2_form("(defun f (x y) (cons x y))", &mut w).expect("translate");

        // Lam x, Lam y, body.
        assert_eq!(tag_of(&w, root), FlatTag::Lam);
        let inner_lam = field_u32(&w, root, 5);
        assert_eq!(tag_of(&w, inner_lam), FlatTag::Lam);
        let body = field_u32(&w, inner_lam, 5);

        // body = App(App(cons, x), y); arg is y = BVar(0).
        assert_eq!(tag_of(&w, body), FlatTag::App);
        let y_idx = field_u32(&w, body, 4);
        assert_eq!(tag_of(&w, y_idx), FlatTag::BVar);
        assert_eq!(field_u32(&w, y_idx, 0), 0);

        // inner App's fn = App(cons, x); x = BVar(1).
        let cons_x = field_u32(&w, body, 0);
        let x_idx = field_u32(&w, cons_x, 4);
        assert_eq!(tag_of(&w, x_idx), FlatTag::BVar);
        assert_eq!(field_u32(&w, x_idx, 0), 1);
    }

    #[test]
    fn unsupported_forms_return_none() {
        let mut w = ShardWriter::new();
        // defmacro / defconst / defstobj: no faithful term.
        assert!(translate_acl2_form("(defmacro m (x) `(list ,x))", &mut w).is_none());
        assert!(translate_acl2_form("(defconst *c* 42)", &mut w).is_none());
        assert!(translate_acl2_form("(defstobj st)", &mut w).is_none());
        // defthm whose statement is quoted data.
        assert!(translate_acl2_form("(defthm q (equal '(a) '(a)))", &mut w).is_none());
        // Malformed: missing statement.
        assert!(translate_acl2_form("(defthm only-name)", &mut w).is_none());
    }

    #[test]
    fn produces_more_exprs_than_one() {
        // Sanity: a real tree, not a single placeholder.
        let mut w = ShardWriter::new();
        let _ = translate_acl2_form("(defthm t1 (equal (+ 0 x) x))", &mut w).expect("translate");
        assert!(
            w.expr_count() >= 5,
            "expected a real tree, got {}",
            w.expr_count()
        );
    }
}
