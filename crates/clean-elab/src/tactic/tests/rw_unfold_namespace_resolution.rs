// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `rw` and `unfold` resolve a global name the way the TERM elaborator does.
//!
//! Both took the name the user typed and handed it straight to
//! `env.get_const`. Inside a namespace, or after an `open`, that fails on a
//! lemma the term elaborator resolves without trouble — Lean's
//! `resolveGlobalName` tries the current namespace outward, then each open
//! namespace, then the root name, and neither tactic did any of it.
//!
//! `simp` was given exactly this fix (`simp::lemmas::resolve_extra_lemma_name`,
//! for `simp [add_zero]` after `open Nat`) and its siblings never got it. The
//! resolver now lives once, beside `ProofState`, as
//! `tactic::core::resolve_global_name`.
//!
//! Measured cost of the gap: the 2026-08-25 source-elab corpus reports
//! `hypothesis not found: not_injective_iff` on `Function.not_injective_const`,
//! where `Function.not_injective_iff` is the IMMEDIATELY PRECEDING declaration
//! in the same file
//! (`docs/analysis/srcelab-bucket-decomposition-2026-08-28.md` §3.2).
//!
//! Negative control, measured before this landed: with the resolver call
//! reverted to `Name::from_string(name)`, `rw_short_name` below fails with
//! `unknown identifier: ab`, and the file goes 3 passed / 1 failed.

use clean_kernel::Environment;
use clean_parser::parse_file;

use crate::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};

/// Elaborate every declaration in `code` against one fresh prelude env and
/// return how many produced a kernel-registered result.
#[track_caller]
fn elab_all_ok(code: &str, what: &str) {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(code).expect("parse_file should succeed");
    assert!(!decls.is_empty(), "{what}: nothing parsed");
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let result = elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx);
        assert!(result.is_ok(), "{what}: a declaration failed: {result:?}");
    }
}

/// `rw [ab]` inside `namespace Foo`, where the lemma is `Foo.ab`.
///
/// This is the corpus shape reduced to the builtin prelude: a short name whose
/// only resolution is through the enclosing namespace.
#[test]
fn test_rw_resolves_a_short_name_through_the_enclosing_namespace() {
    elab_all_ok(
        r"
namespace Foo
axiom A : Prop
axiom B : Prop
axiom ab : A = B
theorem rw_short_name (h : A) : B := by rw [← ab]; exact h
end Foo
",
        "rw with a same-namespace short name",
    );
}

/// The already-qualified spelling must keep working — the resolver widens which
/// spellings reach a constant, it does not move which constant is found.
#[test]
fn test_rw_still_resolves_a_fully_qualified_name() {
    elab_all_ok(
        r"
namespace Bar
axiom A : Prop
axiom B : Prop
axiom ab : A = B
end Bar

theorem rw_qualified (h : Bar.A) : Bar.B := by rw [← Bar.ab]; exact h
",
        "rw with a fully qualified name from outside the namespace",
    );
}

/// `unfold` had the same bare lookup, at both of its entry points.
#[test]
fn test_unfold_resolves_a_short_name_through_the_enclosing_namespace() {
    elab_all_ok(
        r"
namespace Baz
def two : Nat := 2
theorem unfold_short_name : two = 2 := by unfold two
end Baz
",
        "unfold with a same-namespace short name",
    );
}

/// A name that resolves NOWHERE is an unknown identifier, not a missing
/// hypothesis.
///
/// `rw` reported `HypothesisNotFound` here, which sends a reader to inspect a
/// local context that was never the problem — the same category error the
/// `assumption` split fixed. Both spellings were tried and neither exists.
#[test]
fn test_rw_on_an_unresolvable_name_reports_an_unknown_identifier() {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(
        r"
axiom A : Prop
theorem rw_missing (h : A) : A := by rw [no_such_lemma_anywhere]
",
    )
    .expect("parse_file should succeed");
    let mut last = None;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        last = Some(elaborate_decl_and_register_with_context(
            &mut env,
            &processed,
            &mut file_ctx,
        ));
    }
    let text = match last.expect("at least one declaration") {
        Err(err) => err.to_string(),
        Ok(ok) => panic!("expected a failure, got {ok:?}"),
    };
    assert!(
        text.contains("unknown identifier"),
        "an unresolvable name is an unknown identifier, got: {text}"
    );
    assert!(
        !text.contains("hypothesis not found"),
        "nothing about a local hypothesis was wrong here, got: {text}"
    );
}

/// The elaborated theorem is still kernel-checked — resolution widened
/// spellings, not what may be proved.
#[test]
fn test_namespace_resolved_rewrite_still_produces_a_registered_theorem() {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(
        r"
namespace Qux
axiom A : Prop
axiom B : Prop
axiom ab : A = B
theorem resolved (h : A) : B := by rw [← ab]; exact h
end Qux
",
    )
    .expect("parse_file should succeed");
    let mut last = None;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        last = Some(elaborate_decl_and_register_with_context(
            &mut env,
            &processed,
            &mut file_ctx,
        ));
    }
    // A `namespace … end` block elaborates as ONE `Multiple`, so the theorem is
    // inside it rather than at the top. Reaching in is the stronger assertion
    // anyway: it lets the proof term itself be checked, and a `sorry` would be
    // invisible to a shape-only match.
    let Some(Ok(ElabResult::Multiple(decls))) = last else {
        panic!("expected a namespace block to elaborate as Multiple, got {last:?}");
    };
    let theorem = decls
        .iter()
        .find(
            |d| matches!(d, ElabResult::Theorem { name, .. } if name.to_string() == "Qux.resolved"),
        )
        .expect("the namespace block must register `Qux.resolved`");
    let ElabResult::Theorem { proof, .. } = theorem else {
        unreachable!("filtered to Theorem above");
    };
    let rendered = crate::error_render::term(proof);
    assert!(
        rendered.contains("Eq.subst"),
        "the rewrite must build a real `Eq.subst` proof, got: {rendered}"
    );
    assert!(
        !rendered.contains("sorry"),
        "the proof must not be a sorry, got: {rendered}"
    );
}
