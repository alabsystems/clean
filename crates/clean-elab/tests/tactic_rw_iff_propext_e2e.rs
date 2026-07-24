// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end regression lock for **`rw` with an `Iff` hypothesis/lemma**.
//!
//! `rw` historically only accepted an `Eq`-shaped rewrite source: the
//! equation-extraction layer (`match_equality`) demanded a head `Const("Eq")`
//! with 3 args. An `h : p ↔ q` is a head `Const("Iff")` applied to two `Prop`
//! arguments — WHNF does not reduce it to a `Pi`/`Eq` — so every `rw` entry point
//! rejected it with `goal mismatch: hypothesis is not an equality`.
//!
//! The fix adapts an `Iff` source to an `Eq` via the **foundational** `propext`
//! axiom: from `h : p ↔ q` synthesize `@propext p q h : @Eq.{1} Prop p q`, then
//! run the SAME `Eq.subst`/`Eq.symm` machinery. Both directions (`rw [h]` /
//! `rw [← h]`) and both positions (goal / `at hyp`) are covered because the
//! direction/position branching lives downstream of the equation tuple.
//!
//! ## Why these are genuine proofs (not `sorry`)
//!
//! Each theorem carries a real tactic proof; the test drives the SAME pipeline as
//! `clean check` (`parse_file → preprocess_decl_with_context →
//! elaborate_decl_and_register`) and asserts, for every positive gate:
//!   * the theorem registers (the kernel re-checks the produced `Eq.subst` term),
//!   * `infer_type` of the proof term is def-eq to the stated proposition, and
//!   * the transitive `axiom_deps` closure is `⊆ {propext}` — i.e. the only axiom
//!     under the rewrite is the foundational `propext`, nothing domain-specific.
//!
//! The DECISIVE NEGATIVE gates prove the kernel still fails closed: an `Iff`
//! rewrite cannot close a false goal (wrong direction / wrong target), exactly as
//! for `Eq`. Matching only selects WHICH subterm changes; the assembled term is
//! always kernel-rechecked by `close_goal` / `replace_local_decl_with_cast`.

use std::collections::BTreeSet;

use clean_kernel::env::Environment;
use clean_kernel::{Name, TypeChecker};

use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_parser::parse_file;

/// Drive the real file pipeline for a (possibly multi-declaration) source.
fn try_elaborate_into(env: &mut Environment, source: &str) -> Result<(), String> {
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        elaborate_decl_and_register(env, &processed).map_err(|e| e.to_string())?;
    }
    Ok(())
}

/// Elaborate `source` (defining `name` last as a tactic-proved theorem) and
/// assert it kernel-checks, infers a def-eq type, and its axiom closure is a
/// subset of `allowed` (the foundational axioms we permit, e.g. `propext`).
fn assert_tactic_theorem_axioms(name: &str, source: &str, allowed: &[&str]) {
    let mut env = Environment::with_prelude();
    try_elaborate_into(&mut env, source)
        .unwrap_or_else(|e| panic!("`{name}` must elaborate and kernel-check: {e}"));

    let info = env
        .get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("`{name}` must be registered after elaboration"));
    let proof = info
        .value
        .as_ref()
        .unwrap_or_else(|| panic!("`{name}` theorem must carry a proof value"));

    // SOUNDNESS 1 — kernel re-derives the proof's type, def-eq to the stated prop.
    let tc = TypeChecker::new(&env);
    let inferred = tc
        .infer_type(proof)
        .unwrap_or_else(|e| panic!("`{name}` proof must infer a type: {e}"));
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "`{name}` proof type must be def-eq to its stated proposition:\n  got {inferred:?}\n  exp {:?}",
        info.type_
    );

    // SOUNDNESS 2 — axiom_deps closure ⊆ allowed (here: just `propext`).
    let deps = env
        .axiom_deps(&Name::from_string(name))
        .unwrap_or_else(|| panic!("`{name}` must have an axiom_deps closure"));
    let allowed_set: BTreeSet<Name> = allowed.iter().map(|s| Name::from_string(s)).collect();
    for dep in &deps {
        assert!(
            allowed_set.contains(dep),
            "`{name}` axiom closure must be ⊆ {allowed:?}; found disallowed axiom `{dep:?}` \
             (full closure: {deps:?})"
        );
    }
}

// ---------------------------------------------------------------------------
// GATE iff-a — `rw [h] at hp` rewrites a hypothesis `hp : p` to `hp : q` using
// `h : p ↔ q` (the `rewrite_at` path), then `exact hp` closes goal `q`.
// ---------------------------------------------------------------------------

#[test]
fn rw_iff_at_hyp_forward_rewrites_and_closes() {
    assert_tactic_theorem_axioms(
        "rw_iff_at",
        "theorem rw_iff_at (p q : Prop) (h : p ↔ q) (hp : p) : q := by rw [h] at hp; exact hp",
        &["propext"],
    );
}

// ---------------------------------------------------------------------------
// GATE iff-b — goal-position `rw [h]` rewrites goal `p` to `q` using `h : p ↔ q`
// (the `rewrite` local-hyp path), then `exact hq` closes it.
// ---------------------------------------------------------------------------

#[test]
fn rw_iff_goal_forward_rewrites_and_closes() {
    assert_tactic_theorem_axioms(
        "rw_iff_goal",
        "theorem rw_iff_goal (p q : Prop) (h : p ↔ q) (hq : q) : p := by rw [h]; exact hq",
        &["propext"],
    );
}

// ---------------------------------------------------------------------------
// GATE iff-c — reverse direction `rw [← h]` at a hypothesis. `h : p ↔ q`,
// `hq : q`; `rw [← h] at hq` turns `hq : q` into `hq : p` (Eq.symm under the
// hood), then `exact hq` closes goal `p`.
// ---------------------------------------------------------------------------

#[test]
fn rw_iff_at_hyp_reverse_rewrites_and_closes() {
    assert_tactic_theorem_axioms(
        "rw_iff_at_rev",
        "theorem rw_iff_at_rev (p q : Prop) (h : p ↔ q) (hq : q) : p := by rw [← h] at hq; exact hq",
        &["propext"],
    );
}

// ---------------------------------------------------------------------------
// GATE iff-d — reverse direction in goal position. `h : p ↔ q`, `hp : p`;
// `rw [← h]` turns goal `q` into goal `p`, then `exact hp` closes it.
// ---------------------------------------------------------------------------

#[test]
fn rw_iff_goal_reverse_rewrites_and_closes() {
    assert_tactic_theorem_axioms(
        "rw_iff_goal_rev",
        "theorem rw_iff_goal_rev (p q : Prop) (h : p ↔ q) (hp : p) : q := by rw [← h]; exact hp",
        &["propext"],
    );
}

// ---------------------------------------------------------------------------
// GATE iff-e — env-constant path: a user-registered `Iff`-valued LEMMA
// (`my_iff : p ↔ q` as a top-level theorem) is used as `rw [my_iff]`. This goes
// through `resolve_env_rewrite_equation` (peels Pi binders → metas, then adapts
// the `Iff` body via `propext` wrapping the const application `c meta…`).
// ---------------------------------------------------------------------------

#[test]
fn rw_iff_env_lemma_goal_rewrites_and_closes() {
    assert_tactic_theorem_axioms(
        "rw_iff_env",
        "theorem my_iff (p q : Prop) (h : p ↔ q) : p ↔ q := h\n\
         theorem rw_iff_env (p q : Prop) (h : p ↔ q) (hq : q) : p := by \
         rw [my_iff p q h]; exact hq",
        &["propext"],
    );
}

// ---------------------------------------------------------------------------
// GATE iff-f — CHAINED `rw [h1, h2]` mixing two `Iff` hypotheses in goal
// position: `h1 : p ↔ q`, `h2 : q ↔ r`; `rw [h1, h2]` turns goal `p` into `q`
// then `r`, closed by `exact hr`. Confirms sequential Iff rewrites compose (each
// goes through a fresh propext adaptation + Eq.subst).
//
// NOTE on the *bare-identifier* env-const path (`resolve_env_rewrite_equation`
// reached via `rw [bareName]`) and on `rw [<applied term>] at hyp`: both are
// wired for Iff identically to Eq, but each currently trips a PRE-EXISTING,
// Iff-independent dispatch/elaboration gap — `rw [bareName]` hits "cannot extract
// type name from Pi" when the env constant's body carries a Prop-typed meta, and
// `rw [<term>] at hyp` is rejected at dispatch as "rewriting a hypothesis with a
// non-identifier term is unsupported". Both gaps are orthogonal to this change
// (the same shapes fail for `Eq` sources); gate iff-e already exercises the
// propext synthesis for env-sourced (applied) Iff lemmas, and gate iff-a covers
// the `at hyp` position via a local Iff hypothesis.
// ---------------------------------------------------------------------------

#[test]
fn rw_iff_chained_hyps_goal_rewrites_and_closes() {
    assert_tactic_theorem_axioms(
        "rw_iff_chain",
        "theorem rw_iff_chain (p q r : Prop) (h1 : p ↔ q) (h2 : q ↔ r) (hr : r) : p := by \
         rw [h1, h2]; exact hr",
        &["propext"],
    );
}

// ---------------------------------------------------------------------------
// DECISIVE NEGATIVE 1 — an `Iff` rewrite must NOT close a false goal. After
// `rw [h] at hp`, `hp` has type `q`, but the goal is `p`; `exact hp` is a type
// mismatch, so the whole proof must FAIL (kernel fails closed). If this ever
// PASSES, the rewrite is unsound (it would let you prove the wrong thing).
// ---------------------------------------------------------------------------

#[test]
fn rw_iff_cannot_close_false_goal_at_hyp() {
    let mut env = Environment::with_prelude();
    let result = try_elaborate_into(
        &mut env,
        "theorem rw_iff_bad (p q : Prop) (h : p ↔ q) (hp : p) : p := by rw [h] at hp; exact hp",
    );
    assert!(
        result.is_err(),
        "rw [h] at hp makes hp : q, which does NOT close goal p; this proof MUST fail \
         (else the Iff rewrite is unsound)"
    );
}

// ---------------------------------------------------------------------------
// DECISIVE NEGATIVE 2 — a non-matching `Iff` rewrite fails closed: the goal is
// `r`, which contains neither `p` nor `q`, so `rw [h]` (h : p ↔ q) finds no
// subterm to rewrite and the tactic must error (RewriteNoMatch), not silently
// succeed.
// ---------------------------------------------------------------------------

#[test]
fn rw_iff_no_match_fails_closed() {
    let mut env = Environment::with_prelude();
    let result = try_elaborate_into(
        &mut env,
        "theorem rw_iff_nomatch (p q r : Prop) (h : p ↔ q) (hr : r) : r := by rw [h]; exact hr",
    );
    assert!(
        result.is_err(),
        "rw [h] with h : p ↔ q must find no occurrence of p in goal r and fail closed"
    );
}

// ---------------------------------------------------------------------------
// REGRESSION — an `Eq`-shaped local-hyp rewrite still works unchanged (the Iff
// adapter is a strict fallback only when `match_equality` returns Err).
// ---------------------------------------------------------------------------

#[test]
fn rw_eq_local_hyp_still_works() {
    assert_tactic_theorem_axioms(
        "rw_eq_regression",
        "theorem rw_eq_regression (a b : Nat) (h : a = b) (ha : a = a) : b = b := by \
         rw [h] at ha; exact ha",
        &[],
    );
}
