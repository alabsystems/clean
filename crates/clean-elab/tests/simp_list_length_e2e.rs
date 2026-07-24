// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end regression lock for **`simp` evaluating `List.length`** over the
//! three shapes that appear in `(xs ++ ys).length = xs.length + ys.length`, via
//! the kernel-proved, axiom-free lemmas `List.length_nil`, `List.length_cons`,
//! and `List.length_append` wired into the builtin simp set.
//!
//! ## The gap this guards
//!
//! `List.length` recurses on the list, so `(x::xs).length` ι-reduces but
//! `(xs ++ ys).length` with a symbolic `xs` is STUCK on the recursion target —
//! it needs genuine induction. Before this change `List.length_append` was NOT
//! registered anywhere, so `(xs ++ ys).length = xs.length + ys.length := by simp`
//! returned `NoProgress`.
//!
//! The surface goal desugars (through `Environment::with_prelude`) to
//! `HAppend.hAppend`/`HAdd.hAdd` typeclass-projection spines. The builtin simp
//! lemmas are stated over the BARE op heads (`@List.length ?α (@List.append …)`,
//! RHS bare `@Nat.add …`). simp's `reduce_op_projection_head` peels the `HAppend`
//! / `HAdd` projections off the goal before unifying — the exact mechanism by
//! which the bare-`Nat.add` Nat lemmas and `List.append_nil` already match.
//!
//! ## Why a pass here is a genuine proof (not `sorry` / an axiom)
//!
//! Each PASS gate drives the SAME pipeline as `clean check`
//! (`parse_file → preprocess_decl_with_context → elaborate_decl_and_register`)
//! and asserts the theorem registers (kernel re-checks the simp-built proof),
//! that the proof term's `infer_type` is def-eq to the stated proposition, and
//! that the transitive `axiom_deps` closure is **empty**. `List.length_append`
//! itself is a `List.rec` induction proof (closure `List.rec` + `congrArg` +
//! `Eq.refl`/`Eq.symm`/`Eq.trans` + `Nat.zero_add`/`Nat.succ_add`, all
//! FOUNDATIONAL); `length_nil`/`length_cons` close by `Eq.refl`.
//!
//! ## Soundness backstop (the FALSE-simp gates)
//!
//! `(xs ++ ys).length = xs.length` and `… = ys.length` are FALSE (unless the
//! other operand is empty). These MUST NOT close: the gates assert that
//! elaboration *fails* (no proof registered).

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
// PASS gates — the PRIMARY length_append goal closes for a variable element
// type, plus the base-lemma shapes.
// ---------------------------------------------------------------------------

#[test]
fn simp_length_append_polymorphic_closes() {
    assert_tactic_theorem(
        "length_append_poly",
        "theorem length_append_poly {α : Type} (xs ys : List α) : \
         (xs ++ ys).length = xs.length + ys.length := by simp",
    );
}

#[test]
fn simp_length_append_concrete_closes() {
    assert_tactic_theorem(
        "length_append_concrete",
        "theorem length_append_concrete (xs ys : List Nat) : \
         (xs ++ ys).length = xs.length + ys.length := by simp",
    );
}

#[test]
fn simp_length_nil_closes() {
    assert_tactic_theorem(
        "length_nil_poly",
        "theorem length_nil_poly {α : Type} : ([] : List α).length = 0 := by simp",
    );
}

#[test]
fn simp_length_cons_closes() {
    assert_tactic_theorem(
        "length_cons_poly",
        "theorem length_cons_poly {α : Type} (x : α) (xs : List α) : \
         (x :: xs).length = xs.length + 1 := by simp",
    );
}

// ---------------------------------------------------------------------------
// SOUNDNESS gates — FALSE goals must NOT be closed by simp.
// ---------------------------------------------------------------------------

#[test]
fn simp_false_length_append_equals_left_is_rejected() {
    assert_false_theorem_rejected(
        "false_length_append_left",
        "theorem false_length_append_left {α : Type} (xs ys : List α) : \
         (xs ++ ys).length = xs.length := by simp",
    );
}

#[test]
fn simp_false_length_append_equals_right_is_rejected() {
    assert_false_theorem_rejected(
        "false_length_append_right",
        "theorem false_length_append_right {α : Type} (xs ys : List α) : \
         (xs ++ ys).length = ys.length := by simp",
    );
}
