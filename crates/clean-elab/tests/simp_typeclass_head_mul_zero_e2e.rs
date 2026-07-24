// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end regression lock for **`simp` matching typeclass-headed goals
//! against bare-head `Nat.*` lemmas** (the `Nat.mul_zero` / `Nat.zero_mul`
//! discrimination-tree head-keying fix).
//!
//! ## The gap this guards
//!
//! A surface goal `n * 0 = 0` desugars (through `Environment::with_prelude`) to
//!
//! ```text
//! @Eq Nat (@HMul.hMul Nat Nat Nat (HMul.mk … Nat.mul) n 0) 0
//! ```
//!
//! The builtin simp lemma `Nat.mul_zero` is stated over the BARE op head
//! (`Nat.mul ?n 0`). Previously simp's discrimination-tree key path ran a FULL
//! `whnf` on the goal subterm `@HMul.hMul … n 0`, which projects through the
//! instance to `Nat.mul`, δ-unfolds it, and ι-reduces `Nat.mul n 0` all the way
//! to the degenerate ground key `Nat.zero` — erasing the operator head. The
//! lemma LHS collapsed to the same `Nat.zero` key at insert, so simp retrieved
//! `Nat.mul_zero` and then mis-unified it against the *un-reduced* `HMul.hMul`
//! spine, mis-binding `?n` and assembling a malformed proof that only the kernel
//! `add_decl` rejected (a `TypeMismatch`) — by which point simp had already lost
//! the chance to fall through.
//!
//! The fix peels EXACTLY the typeclass-projection layer (exposing `Nat.mul n 0`
//! without ι-reducing the operands) at both the discr-tree key sites and the
//! simp matcher, so the lemma LHS and the goal subterm meet at the `Nat.mul`
//! head and the unifier binds `?n ↦ n` correctly. The existing def-eq guard then
//! validates the genuinely-def-eq match and the kernel re-checks the proof.
//!
//! ## Why a pass here is a genuine proof (not `sorry` / an axiom)
//!
//! Each PASS gate drives the SAME pipeline as `clean check`
//! (`parse_file → preprocess_decl_with_context → elaborate_decl_and_register`)
//! and asserts that the theorem registers (kernel re-checks the produced proof),
//! that the proof term's `infer_type` is def-eq to the stated proposition, and
//! that the transitive `axiom_deps` closure is **empty**.
//!
//! ## Soundness backstop (the FALSE-simp gates)
//!
//! `n * 0 = 1 := by simp` and `n * 1 = 0 := by simp` are FALSE. The fix only
//! makes MORE candidates reachable; every candidate rewrite must still produce a
//! proof whose type is def-eq to `goal`, or it is rejected by the in-tactic
//! def-eq guard and ultimately by the kernel. So these MUST NOT close: the gates
//! assert that elaboration *fails* (no proof is registered).

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
/// and assert:
///   * it elaborates + kernel-checks through the real file pipeline,
///   * `name`'s proof term `infer_type`s to a type def-eq to its proposition,
///   * `name` has an EMPTY `axiom_deps` closure (sorry-free, axiom-free).
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
    // def-eq to the stated proposition (the kernel re-check of the simp-built
    // rewrite term).
    let tc = TypeChecker::new(&env);
    let inferred = tc
        .infer_type(proof)
        .unwrap_or_else(|e| panic!("`{name}` proof must infer a type: {e}"));
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "`{name}` proof type must be def-eq to its stated proposition:\n  got {inferred:?}\n  exp {:?}",
        info.type_
    );

    // SOUNDNESS 2 — empty axiom_deps closure: no `sorry`/`sorryAx`/fabricated
    // axiom anywhere underneath the tactic-built proof term.
    let deps = env
        .axiom_deps(&Name::from_string(name))
        .unwrap_or_else(|| panic!("`{name}` must have an axiom_deps closure"));
    assert!(
        deps.is_empty(),
        "`{name}` must be axiom-free (genuine tactic proof, no sorry/axiom); got {deps:?}"
    );
}

/// Assert the FALSE theorem `source` does NOT elaborate-and-register: either the
/// pipeline errors, or (defensively) no registered `name` carries a proof value.
/// This is the soundness backstop — a false `simp` must never close a goal.
fn assert_false_theorem_rejected(name: &str, source: &str) {
    let mut env = Environment::with_prelude();
    match try_elaborate_into(&mut env, source) {
        Err(_) => {} // expected: simp could not (soundly) close the false goal.
        Ok(()) => {
            // If the pipeline reported success, there must be NO usable proof:
            // a registered theorem with a kernel-valid proof of a false prop
            // would be a soundness breach.
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
// PASS gates — the previously-broken typeclass-headed `* 0` shapes now close,
// plus the controls (`+ 0`, `* 1`) that must keep working.
// ---------------------------------------------------------------------------

#[test]
fn simp_mul_zero_right_typeclass_head_closes() {
    assert_tactic_theorem(
        "mul_zero_r",
        "theorem mul_zero_r (n : Nat) : n * 0 = 0 := by simp",
    );
}

#[test]
fn simp_mul_zero_left_typeclass_head_closes() {
    assert_tactic_theorem(
        "mul_zero_l",
        "theorem mul_zero_l (n : Nat) : 0 * n = 0 := by simp",
    );
}

#[test]
fn simp_add_zero_right_still_closes() {
    assert_tactic_theorem(
        "add_zero_r",
        "theorem add_zero_r (n : Nat) : n + 0 = n := by simp",
    );
}

#[test]
fn simp_add_zero_left_still_closes() {
    assert_tactic_theorem(
        "add_zero_l",
        "theorem add_zero_l (n : Nat) : 0 + n = n := by simp",
    );
}

#[test]
fn simp_mul_one_right_still_closes() {
    assert_tactic_theorem(
        "mul_one_r",
        "theorem mul_one_r (n : Nat) : n * 1 = n := by simp",
    );
}

#[test]
fn simp_mul_one_left_still_closes() {
    assert_tactic_theorem(
        "mul_one_l",
        "theorem mul_one_l (n : Nat) : 1 * n = n := by simp",
    );
}

// ---------------------------------------------------------------------------
// SOUNDNESS gates — FALSE goals must NOT be closed by simp. The matcher fix only
// surfaces more candidates; the def-eq guard + kernel re-check still reject any
// non-def-eq rewrite.
// ---------------------------------------------------------------------------

#[test]
fn simp_false_mul_zero_equals_one_is_rejected() {
    assert_false_theorem_rejected(
        "false_mul_zero_one",
        "theorem false_mul_zero_one (n : Nat) : n * 0 = 1 := by simp",
    );
}

#[test]
fn simp_false_mul_one_equals_zero_is_rejected() {
    assert_false_theorem_rejected(
        "false_mul_one_zero",
        "theorem false_mul_one_zero (n : Nat) : n * 1 = 0 := by simp",
    );
}
