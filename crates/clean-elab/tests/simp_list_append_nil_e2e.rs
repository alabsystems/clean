// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end regression lock for **`simp` closing `xs ++ [] = xs`** via the
//! kernel-proved, axiom-free `List.append_nil` lemma wired into the builtin simp
//! set.
//!
//! ## The gap this guards
//!
//! `List.append` recurses on its FIRST argument, so `[] ++ xs` ι-reduces to `xs`
//! (the reducing direction closes by `rfl`/`simp` with no lemma). But `xs ++ []`
//! with a symbolic `xs` is STUCK on the recursion target — it needs genuine
//! induction. Before this change `List.append_nil` was NOT registered in the
//! kernel environment at all, so `xs ++ [] = xs := by simp` returned NoProgress.
//!
//! The surface goal `xs ++ [] = xs` desugars (through `Environment::with_prelude`)
//! to an `@HAppend.hAppend (List α) (List α) (List α) … xs (@List.nil α)`
//! typeclass-projection spine. The builtin simp lemma `List.append_nil` is stated
//! over the BARE op head `@List.append ?α ?xs (@List.nil ?α)`. simp's
//! `reduce_op_projection_head` peels the `HAppend.hAppend` projection to expose
//! bare `List.append` before unifying — the exact mechanism by which the
//! bare-`Nat.add` Nat lemmas match `HAdd`-headed goals.
//!
//! ## Why a pass here is a genuine proof (not `sorry` / an axiom)
//!
//! Each PASS gate drives the SAME pipeline as `clean check`
//! (`parse_file → preprocess_decl_with_context → elaborate_decl_and_register`)
//! and asserts the theorem registers (kernel re-checks the simp-built proof),
//! that the proof term's `infer_type` is def-eq to the stated proposition, and
//! that the transitive `axiom_deps` closure is **empty**. `List.append_nil`
//! itself is a `List.rec` induction proof (closure `List.rec` + `congrArg` +
//! `Eq.refl`, all FOUNDATIONAL).
//!
//! ## Soundness backstop (the FALSE-simp gates)
//!
//! `xs ++ ys = xs` (symbolic `ys`) and `xs ++ [] = []` are FALSE. The pattern's
//! 2nd append arg is literally `@List.nil ?α`, so it cannot unify against a
//! symbolic `ys`, and its RHS is the 1st arg `?xs`, so it never produces `[]`.
//! These MUST NOT close: the gates assert that elaboration *fails* (no proof
//! registered).

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

/// Elaborate `source` (which must define `name` last as a tactic-proved theorem)
/// and assert it elaborates + kernel-checks, infers a def-eq type, and is
/// axiom-free.
fn assert_tactic_theorem(name: &str, source: &str) {
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

    // SOUNDNESS 1 — infer_type: the kernel re-derives the proof's type and it is
    // def-eq to the stated proposition.
    let tc = TypeChecker::new(&env);
    let inferred = tc
        .infer_type(proof)
        .unwrap_or_else(|e| panic!("`{name}` proof must infer a type: {e}"));
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "`{name}` proof type must be def-eq to its stated proposition:\n  got {inferred:?}\n  exp {:?}",
        info.type_
    );

    // SOUNDNESS 2 — empty axiom_deps closure: no sorry/axiom underneath.
    let deps = env
        .axiom_deps(&Name::from_string(name))
        .unwrap_or_else(|| panic!("`{name}` must have an axiom_deps closure"));
    assert!(
        deps.is_empty(),
        "`{name}` must be axiom-free (genuine tactic proof, no sorry/axiom); got {deps:?}"
    );
}

/// Assert the FALSE theorem `source` does NOT elaborate-and-register.
fn assert_false_theorem_rejected(name: &str, source: &str) {
    let mut env = Environment::with_prelude();
    match try_elaborate_into(&mut env, source) {
        Err(_) => {} // expected: simp could not (soundly) close the false goal.
        Ok(()) => {
            if let Some(info) = env.get_const(&Name::from_string(name)) {
                assert!(
                    info.value.is_none(),
                    "FALSE goal `{name}` must NOT be closed by simp, but a proof was registered"
                );
            }
        }
    }
}

// ---------------------------------------------------------------------------
// PASS gates — `xs ++ [] = xs` now closes for both a variable element type and a
// concrete one, and the reducing direction `[] ++ xs = xs` keeps closing.
// ---------------------------------------------------------------------------

#[test]
fn simp_append_nil_polymorphic_closes() {
    assert_tactic_theorem(
        "append_nil_poly",
        "theorem append_nil_poly {α : Type} (xs : List α) : xs ++ [] = xs := by simp",
    );
}

#[test]
fn simp_append_nil_concrete_closes() {
    assert_tactic_theorem(
        "append_nil_concrete",
        "theorem append_nil_concrete (xs : List Nat) : xs ++ [] = xs := by simp",
    );
}

#[test]
fn simp_nil_append_reducing_direction_still_closes() {
    assert_tactic_theorem(
        "nil_append_poly",
        "theorem nil_append_poly {α : Type} (xs : List α) : [] ++ xs = xs := by simp",
    );
}

// ---------------------------------------------------------------------------
// SOUNDNESS gates — FALSE goals must NOT be closed by simp.
// ---------------------------------------------------------------------------

#[test]
fn simp_false_append_symbolic_tail_is_rejected() {
    assert_false_theorem_rejected(
        "false_append_symbolic",
        "theorem false_append_symbolic {α : Type} (xs ys : List α) : xs ++ ys = xs := by simp",
    );
}

#[test]
fn simp_false_append_nil_equals_nil_is_rejected() {
    assert_false_theorem_rejected(
        "false_append_nil_eq_nil",
        "theorem false_append_nil_eq_nil {α : Type} (xs : List α) : xs ++ [] = [] := by simp",
    );
}

#[test]
fn simp_false_nil_append_equals_nil_is_rejected() {
    assert_false_theorem_rejected(
        "false_nil_append_eq_nil",
        "theorem false_nil_append_eq_nil {α : Type} (xs : List α) : [] ++ xs = [] := by simp",
    );
}
