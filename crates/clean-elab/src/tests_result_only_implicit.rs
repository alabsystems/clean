// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression coverage for result-only-implicit expected-type propagation.
//!
//! Exemplar: `Or.inl h : p ∨ q`. `Or.inl` has type
//! `{a b : Prop} → a → Or a b` — the type parameters `a`/`b` are *implicit*
//! and `b` appears only in the result `Or a b`. Two independent gaps had to be
//! closed:
//!
//! 1. **Kernel constructor binder-info (FIX A).** `Or.inl`/`Or.inr`/`And.intro`/
//!    `Iff.intro` were built with their `a b : Prop` type-parameter binders set
//!    to `BinderInfo::Default` instead of `Implicit`. With explicit binders,
//!    `Or.inl h` matched `h : p` against the first binder `a : Prop` (= a Sort),
//!    producing a `TypeMismatch`. Real Lean makes those binders implicit
//!    (consistent with the already-implicit `And.left`/`And.right`/
//!    `Exists.intro`).
//!
//! 2. **Elaborator result-only-implicit propagation (FIX B).** Even with
//!    implicit binders, `Or.inl rfl : x = x ∨ False` leaked free variables:
//!    `rfl` does not itself pin `?a`, and `?b` appears only in the result. The
//!    post-hoc final unify (`apply_implicit_to_expected_type`) ran too late and
//!    against an already-mis-assigned `?a`. The pre-arg expected-result
//!    unification gate now also fires when an expected type is present, is not a
//!    Sort/Prop, and the application's result type still contains unsolved
//!    metavariables — mirroring Lean's `propagateExpectedType` (App.lean:414,
//!    with the Prop-skip guard at App.lean:444).

use crate::elaborate_decl_and_register;
use clean_kernel::{Environment, Name};
use clean_parser::parse_file;

fn elab_all_and_assert_ok(code: &str, expected_name: &str) {
    let mut env = Environment::with_prelude();
    let decls = parse_file(code).expect("should parse");
    let mut outcomes: Vec<String> = Vec::new();
    for (i, decl) in decls.iter().enumerate() {
        if let clean_parser::SurfaceDecl::RawDecl { content, span } = decl {
            panic!("decl {i} fell through to RawDecl; content={content:?}, span={span:?}");
        }
        match elaborate_decl_and_register(&mut env, decl) {
            Ok(_) => outcomes.push(format!("decl {i}: OK")),
            Err(e) => outcomes.push(format!("decl {i}: ERR = {e:?}")),
        }
    }
    let any_err = outcomes.iter().any(|o| o.contains("ERR"));
    assert!(!any_err, "elaboration errors: {outcomes:#?}");
    assert!(
        env.get_const(&Name::from_string(expected_name)).is_some(),
        "{expected_name} should be registered (outcomes: {outcomes:#?})"
    );
}

/// Assert that the LAST declaration in `code` fails to elaborate-and-register
/// (the wrong-term cases). Earlier decls are allowed to succeed.
fn elab_last_and_assert_err(code: &str) {
    let mut env = Environment::with_prelude();
    let decls = parse_file(code).expect("should parse");
    let n = decls.len();
    let mut last_outcome = String::from("<no decls>");
    for (i, decl) in decls.iter().enumerate() {
        if let clean_parser::SurfaceDecl::RawDecl { .. } = decl {
            // A parser-recovered raw decl counts as "not accepted".
            last_outcome = format!("decl {i}: RawDecl");
            continue;
        }
        let r = elaborate_decl_and_register(&mut env, decl);
        if i == n - 1 {
            last_outcome = format!("decl {i}: {r:?}");
            assert!(
                r.is_err(),
                "wrong term should NOT elaborate, but got Ok: {last_outcome}"
            );
        }
    }
    let _ = last_outcome;
}

#[test]
fn test_or_inl_explicit_hyp() {
    elab_all_and_assert_ok("theorem t (p q : Prop) (h : p) : p ∨ q := Or.inl h\n", "t");
}

#[test]
fn test_or_inr_explicit_hyp() {
    elab_all_and_assert_ok("theorem t (p q : Prop) (h : q) : p ∨ q := Or.inr h\n", "t");
}

#[test]
fn test_or_inl_at_explicit() {
    elab_all_and_assert_ok(
        "theorem t (p q : Prop) (h : p) : p ∨ q := @Or.inl p q h\n",
        "t",
    );
}

#[test]
fn test_or_inl_rfl_result_only_implicit() {
    // The deep case: `rfl` does not pin `?a`; `?b := False` is result-only.
    elab_all_and_assert_ok("theorem t (x : Nat) : x = x ∨ False := Or.inl rfl\n", "t");
}

#[test]
fn test_or_inl_by_exact() {
    elab_all_and_assert_ok(
        "theorem t (p q : Prop) (h : p) : p ∨ q := by exact Or.inl h\n",
        "t",
    );
}

#[test]
fn test_or_left_tactic_still_works() {
    elab_all_and_assert_ok(
        "theorem t (p q : Prop) (h : p) : p ∨ q := by left; exact h\n",
        "t",
    );
}

#[test]
fn test_and_intro_result_only_implicit() {
    elab_all_and_assert_ok(
        "theorem t (p q : Prop) (ha : p) (hb : q) : p ∧ q := And.intro ha hb\n",
        "t",
    );
}

#[test]
fn test_iff_intro_result_only_implicit() {
    elab_all_and_assert_ok(
        "theorem t (p : Prop) (h : p) : p ↔ p := Iff.intro (fun x => x) (fun x => x)\n",
        "t",
    );
}

#[test]
fn test_wrong_or_inl_prop_arg_fails() {
    // `Or.inl q` — `q : Prop` is not a proof of `p`; must be rejected.
    elab_last_and_assert_err("theorem t (p q : Prop) (h : p) : p ∨ q := Or.inl q\n");
}

#[test]
fn test_wrong_or_inl_wrong_side_fails() {
    // `h : p` cannot be the LEFT of `q ∨ p`; must be rejected.
    elab_last_and_assert_err("theorem t (p q : Prop) (h : p) : q ∨ p := Or.inl h\n");
}
