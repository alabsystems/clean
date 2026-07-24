// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end regression lock for **decidable `if` reduction on concrete literals**
//! (Track M).
//!
//! ## The gap this guards
//!
//! A `def`/`theorem` over an `if` whose condition is a *concrete, decidable* Nat
//! relation must reduce to the chosen branch in the kernel, so an `rfl`/`Eq.refl`
//! proof of the branch value type-checks:
//!
//! ```text
//! theorem g1 : (if (1 ≤ 2) then 1 else 0) = 1 := rfl
//! theorem g2 : (if (3 < 2) then 1 else 0) = 0 := rfl
//! theorem g3 : (if (1 = 1) then 7 else 9) = 7 := rfl
//! ```
//!
//! Each surface `if c then t else e` elaborates (see `elab_if`) to
//! `@ite α c <Decidable inst> t e`, where the elaborator resolves the concrete
//! `Decidable` instance (`Nat.decLe 1 2`, `Nat.decLt 3 2`, `Nat.decEq 1 1`).
//! Kernel WHNF must then:
//!   1. fire the axiom-free native reducer on the instance, producing a real
//!      `@Decidable.isTrue/isFalse <proof>` constructor application;
//!   2. iota-reduce `ite` (which is `Decidable.rec`-based) on that constructor to
//!      the chosen branch.
//!
//! If either step is missing, the kernel leaves `ite … = <branch>` stuck and the
//! `rfl` is rejected with a constructor/`Discriminant` mismatch.
//!
//! ## Why this is a genuine `rfl` (not a `sorry` / axiom)
//!
//! These theorems carry **no** tactic and **no** axiom — only `rfl`, forced
//! entirely by kernel reduction. Each test below additionally asserts:
//!   * the theorem registers (kernel re-checks the `rfl` proof),
//!   * `infer_type` of the proof term is def-eq to the stated proposition, and
//!   * the transitive `axiom_deps` closure is **empty** (no `sorry`/`sorryAx`/
//!     fabricated axiom anywhere underneath — the native reducers and the
//!     `Nat.decLe/decLt/decEq` instances are all axiom-free).
//!
//! A *negative control* (`bad`) shows the reduction is not vacuous: a FALSE branch
//! claim is rejected — the `if` really computes its branch value, it does not
//! accept everything.
//!
//! The test drives the SAME pipeline as `clean check`
//! (`parse_file → preprocess_decl_with_context → elaborate_decl_and_register`),
//! so a pass here matches an observable `clean check` pass on surface syntax.

use clean_kernel::env::Environment;
use clean_kernel::{Name, TypeChecker};

use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_parser::parse_file;

/// Drive the real file pipeline for a single-declaration source, returning the
/// per-decl elaboration result (so negative controls can assert rejection).
fn try_elaborate_into(env: &mut Environment, source: &str) -> Result<(), String> {
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        elaborate_decl_and_register(env, &processed).map_err(|e| e.to_string())?;
    }
    Ok(())
}

/// Assert a single `theorem <name> : <prop> := rfl` over a decidable `if`:
///   * elaborates + kernel-checks through the real file pipeline,
///   * its proof term `infer_type`s to a type def-eq to the stated proposition,
///   * has an EMPTY `axiom_deps` closure (pure reduction, no `sorry`/axiom).
fn assert_decidable_if_theorem(name: &str, source: &str) {
    let mut env = Environment::with_prelude();
    try_elaborate_into(&mut env, source)
        .unwrap_or_else(|e| panic!("`{name}` must elaborate and kernel-check `rfl`: {e}"));

    let info = env
        .get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("`{name}` must be registered after elaboration"));
    let proof = info
        .value
        .as_ref()
        .unwrap_or_else(|| panic!("`{name}` theorem must carry a proof value"));

    // SOUNDNESS 1 — infer_type: the kernel re-derives the proof's type and it is
    // def-eq to the stated proposition (the `… = <branch>` Eq). This is exactly
    // the check that forces the `if`/`ite` to reduce to its branch.
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
    // axiom anywhere underneath. The whole reduction (native Decidable reducer →
    // `Decidable.isTrue/isFalse` → `ite` iota) is axiom-free.
    let deps = env
        .axiom_deps(&Name::from_string(name))
        .unwrap_or_else(|| panic!("`{name}` must have an axiom_deps closure"));
    assert!(
        deps.is_empty(),
        "`{name}` must be axiom-free (pure reduction, no sorry/axiom); got {deps:?}"
    );
}

// ---------------------------------------------------------------------------
// GATE g1 — `≤` true branch:  if (1 ≤ 2) then 1 else 0  ==  1
// Drives Nat.decLe 1 2 ==> Decidable.isTrue, then ite ==> then-branch.
// ---------------------------------------------------------------------------

#[test]
fn decidable_if_le_true_branch_reduces() {
    assert_decidable_if_theorem("g1", "theorem g1 : (if (1 ≤ 2) then 1 else 0) = 1 := rfl");
}

// ---------------------------------------------------------------------------
// GATE g2 — `<` false branch:  if (3 < 2) then 1 else 0  ==  0
// Drives Nat.decLt 3 2 ==> Decidable.isFalse, then ite ==> else-branch.
// ---------------------------------------------------------------------------

#[test]
fn decidable_if_lt_false_branch_reduces() {
    assert_decidable_if_theorem("g2", "theorem g2 : (if (3 < 2) then 1 else 0) = 0 := rfl");
}

// ---------------------------------------------------------------------------
// GATE g3 — `=` true branch:  if (1 = 1) then 7 else 9  ==  7
// Drives Nat.decEq 1 1 ==> Decidable.isTrue, then ite ==> then-branch.
// ---------------------------------------------------------------------------

#[test]
fn decidable_if_eq_true_branch_reduces() {
    assert_decidable_if_theorem("g3", "theorem g3 : (if (1 = 1) then 7 else 9) = 7 := rfl");
}

// ---------------------------------------------------------------------------
// EXTRA COVERAGE — the opposite branches, to pin both isTrue and isFalse paths
// of each relation (and a `=` false branch via Nat.decEq isFalse).
// ---------------------------------------------------------------------------

#[test]
fn decidable_if_le_false_branch_reduces() {
    assert_decidable_if_theorem("g4", "theorem g4 : (if (5 ≤ 3) then 1 else 0) = 0 := rfl");
}

#[test]
fn decidable_if_lt_true_branch_reduces() {
    assert_decidable_if_theorem("g5", "theorem g5 : (if (2 < 5) then 1 else 0) = 1 := rfl");
}

#[test]
fn decidable_if_eq_false_branch_reduces() {
    assert_decidable_if_theorem("g6", "theorem g6 : (if (7 = 8) then 1 else 2) = 2 := rfl");
}

// ---------------------------------------------------------------------------
// NEGATIVE CONTROL — the reduction is NOT vacuous. A FALSE branch claim must be
// REJECTED: `if (1 ≤ 2) then 1 else 0` genuinely reduces to `1`, so asserting it
// equals `0` via `rfl` must fail to kernel-check (the proof must not register).
// ---------------------------------------------------------------------------

#[test]
fn decidable_if_wrong_branch_is_rejected() {
    let mut env = Environment::with_prelude();
    let result = try_elaborate_into(
        &mut env,
        "theorem bad : (if (1 ≤ 2) then 1 else 0) = 0 := rfl",
    );
    assert!(
        result.is_err(),
        "`if (1 ≤ 2) then 1 else 0` reduces to 1; claiming `= 0` by rfl must be rejected"
    );
    assert!(
        env.get_const(&Name::from_string("bad")).is_none(),
        "the rejected `bad` theorem must not be registered"
    );
}
