// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Parser tests for the Lean 4.8 TERM, pattern and `do` forms trust-ir's
//! `lean/trust_ir-semantics` package uses and Clean used to fail to parser
//! recovery (each row's source shape is quoted from that package):
//!
//! - `exists x, p` — Lean's ASCII `∃` over `explicitBinders`;
//! - `.partial` — a keyword-spelled name after a glued `.` is an identifier;
//! - `| n => open Classical in …` — the term `open … in` as an equation body;
//! - `c@(.agg n)` — a named pattern glued in argument position;
//! - `else ⏎ if` in `do` — a block, never an `else if` chain;
//! - a string, interpolated-string, list or array literal as an implicit
//!   `let` body on the next line.
//!
//! The tactic forms are in `tests_tactic_alt_syntax.rs`, whose helpers these
//! share. Every accepting row has a twin that Lean 4.8 also refuses.

#![allow(clippy::unwrap_used)]

use super::tests_tactic_alt_syntax::{assert_refused, decls_of, name, raw_count};
use super::*;
use crate::surface::DoElem;

// --- `exists x, p` -------------------------------------------------------

fn statement_of(src: &str) -> SurfaceExpr {
    let decls = decls_of(src);
    assert_eq!(
        raw_count(&decls),
        0,
        "no parser recovery expected: {decls:#?}"
    );
    match &decls[0] {
        SurfaceDecl::Theorem { ty, .. } => ty.as_ref().clone(),
        other => panic!("expected a theorem, got {other:?}"),
    }
}

fn exists_binders(expr: &SurfaceExpr) -> Vec<crate::SurfaceName> {
    let mut names = Vec::new();
    let mut cur = expr;
    while let SurfaceExpr::App(_, head, args) = cur {
        let SurfaceExpr::Ident(_, head_name) = head.as_ref() else {
            break;
        };
        if *head_name != name("Exists") {
            break;
        }
        let SurfaceExpr::Lambda(_, binders, body) = &args[0].expr else {
            panic!("Exists takes a lambda, got {:?}", args[0].expr);
        };
        names.extend(binders.iter().map(|b| b.name.clone()));
        cur = body;
    }
    names
}

#[test]
fn test_exists_keyword_unbracketed_binders_desugar_to_exists() {
    let ty = statement_of("theorem t : exists result, result = 0 := ⟨0, rfl⟩\n");
    assert_eq!(exists_binders(&ty), vec![name("result")]);
    let ty = statement_of("theorem t : exists r1 r2 : Nat, r1 = r2 := ⟨0, 0, rfl⟩\n");
    assert_eq!(exists_binders(&ty), vec![name("r1"), name("r2")]);
}

#[test]
fn test_exists_keyword_bracketed_binders_desugar_to_exists() {
    let ty = statement_of("theorem t : exists (env : Nat) (k : Nat), env = k := ⟨0, 0, rfl⟩\n");
    assert_eq!(exists_binders(&ty), vec![name("env"), name("k")]);
}

#[test]
fn test_exists_keyword_inside_disjunction_and_hypothesis() {
    // `(exists result, … = .ok result) \/ (exists e, … = .error e)` and
    // `(hDef : exists v, s.lookupValue operand = some v)` (MetaTheorems.lean).
    statement_of(
        "theorem t (n : Nat) (hDef : exists v, v = n) : (exists r, r = n) ∨ (exists e, e = n) := \
         Or.inl hDef\n",
    );
}

#[test]
fn test_exists_keyword_refuses_what_explicit_binders_refuse() {
    // `explicitBinders` has no binder predicate, no implicit/instance
    // bracket, and a bracketed group always carries its type.
    for (src, what) in [
        (
            "theorem t : exists x > 0, x = 1 := ⟨1, rfl⟩\n",
            "`exists x > 0, …`",
        ),
        (
            "theorem t : exists {x : Nat}, x = 1 := ⟨1, rfl⟩\n",
            "`exists {x}, …`",
        ),
        (
            "theorem t : exists (x), x = 1 := ⟨1, rfl⟩\n",
            "`exists (x), …`",
        ),
        (
            "theorem t : exists, True := trivial\n",
            "`exists` with no binder",
        ),
    ] {
        assert_refused(src, what);
    }
}

#[test]
fn test_exists_keyword_in_argument_position_is_refused() {
    // `exists` is a `leadPrec` term (no precedence on a non-atom-like
    // `macro`), and an application argument parses at `argPrec`. Pinned
    // Lean 4.8.0: `example : id exists x : Nat, x = x := ⟨0, rfl⟩` fails
    // "unexpected token 'exists'; expected ':=', 'where' or '|'".
    for (src, what) in [
        (
            "theorem t : id exists x : Nat, x = x := ⟨0, rfl⟩\n",
            "`id exists x : Nat, …`",
        ),
        (
            "theorem t (f : Prop → Prop → Prop) (h : f True (exists x : Nat, x = x)) : \
             f True exists x : Nat, x = x := h\n",
            "`f True exists x : Nat, …`",
        ),
    ] {
        assert_refused(src, what);
    }
    // The twin Lean accepts: the same binder as a parenthesized argument.
    let ty = statement_of("theorem t : id (exists x : Nat, x = x) := ⟨0, rfl⟩\n");
    let SurfaceExpr::App(_, _, args) = &ty else {
        panic!("expected `id (…)`, got {ty:?}");
    };
    let arg = match &args[0].expr {
        SurfaceExpr::Paren(_, inner) => inner.as_ref(),
        other => other,
    };
    assert_eq!(exists_binders(arg), vec![name("x")]);
}

/// The value of the single `def`/`theorem` in `src`, asserting no recovery.
fn value_of(src: &str) -> SurfaceExpr {
    let decls = decls_of(src);
    assert_eq!(
        raw_count(&decls),
        0,
        "no parser recovery expected: {decls:#?}"
    );
    match &decls[0] {
        SurfaceDecl::Def { val, .. } => val.as_ref().clone(),
        SurfaceDecl::Theorem { proof, .. } => proof.as_ref().clone(),
        other => panic!("expected a def or theorem, got {other:?}"),
    }
}

#[test]
fn test_lead_prec_terms_in_argument_position_are_refused() {
    // The `leadPrec` class `exists` belongs to (`starts_lead_prec_term_at`):
    // pinned Lean 4.8.0 refuses each of these ("type mismatch `id`", then
    // "unexpected token").
    for (src, what) in [
        ("theorem t : id ∃ x : Nat, x = x := ⟨0, rfl⟩\n", "`id ∃ …`"),
        (
            "theorem t : id ∀ x : Nat, x = x := fun _ => rfl\n",
            "`id ∀ …`",
        ),
        ("def t : Type := id Σ x : Nat, Fin x\n", "`id Σ …`"),
        ("def t : Type := id Σ' x : Nat, Fin x\n", "`id Σ' …`"),
        ("def t : Nat := id if True then 1 else 2\n", "`id if …`"),
        ("def t : Nat := id match 1 with | _ => 2\n", "`id match …`"),
        ("def t : Nat := id show Nat from 1\n", "`id show …`"),
        ("theorem t : True := id by trivial\n", "`id by …`"),
    ] {
        assert_refused(src, what);
    }
}

#[test]
fn test_lead_prec_terms_parenthesized_and_max_prec_terms_are_arguments() {
    // The twins pinned Lean 4.8.0 accepts: the same terms parenthesized or
    // after `<|`, and the leading terms that ARE arguments (`fun` is
    // `maxPrec`, `do` is `argPrec`, `¬` is `notation:max`).
    for src in [
        "theorem t : id (∀ x : Nat, x = x) := fun _ => rfl\n",
        "def t : Nat := id (if True then 1 else 2)\n",
        "theorem t : True := id (by trivial)\n",
        "theorem t : True := id <| by trivial\n",
    ] {
        let decls = decls_of(src);
        assert_eq!(raw_count(&decls), 0, "{src} must parse: {decls:#?}");
    }
    for (src, what) in [
        ("def t : Nat → Nat := id fun x => x\n", "`fun`"),
        ("def t : Id Nat := id do pure 1\n", "`do`"),
        ("def t : Prop := id ¬True\n", "`¬`"),
    ] {
        let value = value_of(src);
        let SurfaceExpr::App(_, head, args) = &value else {
            panic!("{what} must be an argument of `id`, got {value:?}");
        };
        assert!(
            matches!(head.as_ref(), SurfaceExpr::Ident(_, n) if *n == name("id"))
                && args.len() == 1,
            "{what} must be the one argument of `id`, got {value:?}"
        );
    }
}

// --- `.partial` ----------------------------------------------------------

#[test]
fn test_keyword_spelled_constructor_after_dot_is_a_name() {
    let decls = decls_of(
        "inductive V where\n  | «partial» : Nat → V\n  | other : V\n\n\
         def V.isPartial : V → Bool\n  | .partial _ => true\n  | _ => false\n\n\
         def V.mk0 : V := V.partial 0\n\ndef V.mk1 : V := .partial 1\n",
    );
    assert_eq!(raw_count(&decls), 0, "{decls:#?}");
    // `partial def` is still the modifier.
    let decls = decls_of("partial def loop (n : Nat) : Nat := loop n\n");
    assert!(
        matches!(&decls[0], SurfaceDecl::Def { modifiers, .. } if modifiers.is_partial),
        "{decls:#?}"
    );
}

#[test]
fn test_bare_keyword_constructor_name_is_still_refused() {
    // Lean 4.8: `| partial : Nat → V` is "expected token" — the keyword needs
    // its `«partial»` escape in declaration position.
    assert_refused(
        "inductive V where\n  | partial : Nat → V\n  | other : V\n",
        "`| partial : Nat → V`",
    );
}

// --- `open … in` as an equation body -------------------------------------

#[test]
fn test_open_in_term_as_equation_arm_body() {
    let decls = decls_of(
        "noncomputable def pick : Nat → Nat\n  | n =>\n    open Classical in\n    \
         if n = 0 then 1 else n\n",
    );
    assert_eq!(raw_count(&decls), 0, "{decls:#?}");
}

#[test]
fn test_open_without_in_as_equation_arm_body_is_refused() {
    assert_refused(
        "noncomputable def pick : Nat → Nat\n  | n =>\n    open Classical\n    \
         if n = 0 then 1 else n\n",
        "`open Classical` with no `in` as an equation body",
    );
}

// --- named pattern in argument position ----------------------------------

#[test]
fn test_anonymous_constructor_as_match_constructor_argument() {
    // The original SemRBoolBodyChecker checks a decoded function signature
    // with this nested pattern. The anonymous constructor is ONE argument
    // to `some`; its fields must not become more arguments to `some`.
    let expr = Parser::parse_expr(
        "match value with | some ⟨[.bool, .bool], [.bool], false⟩ => true | none => false",
    )
    .unwrap();
    let SurfaceExpr::Match(_, _, _, arms) = expr else {
        panic!("expected match");
    };
    assert_eq!(arms.len(), 2);
    let SurfacePattern::Ctor(head, args) = &arms[0].pattern else {
        panic!("expected some constructor: {:?}", arms[0].pattern);
    };
    assert_eq!(head.to_string(), "some");
    assert_eq!(args.len(), 1);
    let SurfacePattern::Ctor(tuple, fields) = &args[0] else {
        panic!("expected anonymous constructor: {:?}", args[0]);
    };
    assert_eq!(tuple.to_string(), "Prod.mk");
    assert_eq!(fields.len(), 2);
    assert!(matches!(&fields[1], SurfacePattern::Ctor(name, tail)
        if name.to_string() == "Prod.mk" && tail.len() == 2));
}

#[test]
fn test_unclosed_anonymous_match_constructor_argument_is_refused() {
    assert!(Parser::parse_expr("match value with | some ⟨a, b => a").is_err());
}

#[test]
fn test_named_pattern_glued_in_constructor_argument() {
    let decls = decls_of("def size : I → Nat\n  | .const _ c@(.agg n) => n\n  | _ => 0\n");
    assert_eq!(raw_count(&decls), 0, "{decls:#?}");
}

#[test]
fn test_named_pattern_with_spaced_at_is_refused() {
    // Lean 4.8: "invalid pattern" — `namedPattern` is `checkNoWsBefore "@"`.
    assert_refused(
        "def size : I → Nat\n  | .const _ c @(.agg n) => n\n  | _ => 0\n",
        "`c @(.agg n)`",
    );
}

// --- `else ⏎ if` in `do` is a block, not a chain -------------------------

#[test]
fn test_do_else_block_starting_with_if_keeps_its_statements() {
    let decls = decls_of(
        "def h4 (n : Nat) (e : Except String Nat) : Except String Nat := do\n  \
         if n == 0 then\n    pure 0\n  else\n    if n == 1 then\n      throw \"one\"\n    \
         let k ← e\n    if k != 0 then\n      throw \"nz\"\n    pure (k + 1)\n",
    );
    assert_eq!(raw_count(&decls), 0, "{decls:#?}");
}

// --- literal let bodies --------------------------------------------------

#[test]
fn test_let_body_on_next_line_may_be_a_string_or_list_literal() {
    for src in [
        "def sval (n : Nat) : String :=\n  let d := toString n\n  \"v:\" ++ d\n",
        "def sval (n : Nat) : String :=\n  let d := toString n\n  s!\"v:{d}\"\n",
        "def sval (n : Nat) : List Nat :=\n  let d := n\n  [d, d]\n",
        "def sval (n : Nat) : Array Nat :=\n  let d := n\n  #[d, d]\n",
    ] {
        let decls = decls_of(src);
        assert_eq!(raw_count(&decls), 0, "{src}: {decls:#?}");
    }
}

#[test]
fn test_let_body_literal_indented_past_the_let_is_an_argument() {
    // A literal indented PAST the `let` continues the value (`checkColGt`):
    // Lean reads `let d := Array.mkArray 1 #[n]` and then finds no body
    // ("unexpected end of input"), so the next-line literal is a body only
    // once the value has stopped.
    assert_refused(
        "def arr2 (n : Nat) : Array Nat :=\n  let d := Array.mkArray 1\n    #[n]\n",
        "a deeper `#[n]` read as the let body",
    );
}

/// The statements of the first `do` block in the body of the single
/// definition in `src`, asserting no recovery.
fn do_elems_of(src: &str) -> Vec<DoElem> {
    fn first_do(expr: &SurfaceExpr) -> Option<&Vec<DoElem>> {
        match expr {
            SurfaceExpr::Do(_, elems) => Some(elems),
            SurfaceExpr::App(_, head, args) => {
                first_do(head).or_else(|| args.iter().find_map(|arg| first_do(&arg.expr)))
            }
            SurfaceExpr::Paren(_, inner) => first_do(inner),
            _ => None,
        }
    }
    let decls = decls_of(src);
    assert_eq!(
        raw_count(&decls),
        0,
        "no parser recovery expected: {decls:#?}"
    );
    let SurfaceDecl::Def { val, .. } = &decls[0] else {
        panic!("expected a def, got {:?}", decls[0]);
    };
    first_do(val)
        .unwrap_or_else(|| panic!("expected a `do` block, got {val:?}"))
        .clone()
}

#[test]
fn test_do_else_block_at_the_if_column_owns_the_rest_of_the_block() {
    // The inner `if` sits at the OUTER `if`'s column. Lean 4.8 still reads
    // `else ⏎ if` as a block, never a chain, and the block's `doSeq` takes
    // every statement at or right of its first one: `x := x + 10` and
    // `return x` are in the `else` block, so the outer block ends with the
    // `if` (pinned Lean then refuses the definition: the `then` branch
    // `x := 1` is its last statement and is not a `Nat`).
    let elems = do_elems_of(
        "def g (a b : Bool) : Nat := Id.run do\n  let mut x := 0\n  if a then\n    x := 1\n  \
         else\n  if b then\n    x := 2\n  x := x + 10\n  return x\n",
    );
    assert_eq!(elems.len(), 2, "`let mut` and the `if`: {elems:#?}");
    let DoElem::If(_, _, then_branch, Some(else_branch)) = &elems[1] else {
        panic!("expected an `if … else …`, got {:?}", elems[1]);
    };
    assert_eq!(then_branch.len(), 1, "{then_branch:#?}");
    assert_eq!(
        else_branch.len(),
        3,
        "the inner `if` and both later statements: {else_branch:#?}"
    );
    assert!(
        matches!(else_branch[0], DoElem::If(_, _, _, None)),
        "the block starts with the inner `if`: {:?}",
        else_branch[0]
    );
}
