// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end: `simp` REWRITING with an IMPORTED simp lemma.
//!
//! This is the simp analogue of the import -> elaborate -> reduce chain that the
//! match (B43) and structure-projection (B44) probes pinned. The pieces involved
//! are exercised together for the first time here:
//!
//! 1. `.olean` loading (`clean_olean::load_olean_file`) registers an imported
//!    inductive (`MyBool`), its constructors, eliminators, and the Lean-compiled
//!    `myNot : MyBool -> MyBool`.
//! 2. An equation theorem `myNot_true : myNot MyBool.myTrue = MyBool.myFalse` is
//!    registered as a fully-formed kernel `Declaration::Theorem` — exactly the
//!    shape a Lean-compiled imported theorem has: a baked-in proof term
//!    (`@Eq.refl MyBool MyBool.myFalse`) that the kernel accepts because the
//!    imported recursor reduces `myNot myTrue` to `myFalse`. It is genuinely
//!    *sorry-free, axiom-free* and references only imported constants.
//! 3. That theorem is registered as a simp lemma via the **exact API the `.olean`
//!    import simp-lemma bridge uses** —
//!    `Environment::register_simp_lemma(name, SimpPriority)` (see
//!    `clean-olean/src/import/load_register.rs::register_simp_lemmas_from_extension`,
//!    which re-registers each imported `@[simp]` entry through this same call). So
//!    from `simp`'s point of view this lemma is indistinguishable from one that
//!    arrived through `simpExtension` in a real `.olean`.
//! 4. In a *fresh* `ProofState`, a goal the imported simp lemma should
//!    rewrite-and-close is set, `simp` is run, and we assert the goal is **closed**
//!    (`state.goals().is_empty()`), the produced proof **kernel-checks**
//!    (`verify_proof`), **references the imported lemma `myNot_true`** (so the
//!    rewrite actually fired — it is not a coincidental `rfl` closure), and is
//!    **sorry-free with `trusted_axiom_count == 0`**.
//!
//! The probe question: does the simp engine actually APPLY an imported simp lemma
//! end to end (rewrite the goal and close it with a real proof term that *uses*
//! the lemma), or does the import bridge merely make the lemma *name* visible to
//! `get_simp_lemmas()` without the rewrite firing? The answer (locked in below):
//! `simp` collects the imported lemma from the kernel registry
//! (`collect_registry_lemmas`), unifies its LHS against the goal, rewrites through
//! the imported constructors, and produces a fully verified, axiom-free proof
//! whose term contains `myNot_true` (alongside `Eq.mpr`/`congrArg`), confirming
//! the lemma is genuinely applied rather than only resolved.
//!
//! Why imported lemmas could differ from native ones (the B43/B44 hazard): a
//! registry simp lemma is stored with `proof_expr: None`, so the rewrite proof is
//! reconstructed in `simp/expr.rs::try_apply_simp_lemma_with_proof` as
//! `lemma.name` applied to the matched binder arguments. The imported lemma here
//! is monomorphic (no leading binders), so the reconstructed proof is exactly the
//! imported theorem constant — which must itself type-check against the imported
//! `myNot`/constructors. This test confirms that whole chain, not just name
//! resolution.

use clean_elab::tactic::{simp, Goal, ProofState, SimpConfig};
use clean_kernel::env::{Declaration, DeclarationTrustSummary, Environment, SimpPriority};
use clean_kernel::{Expr, Level, Name};
use clean_olean::load_olean_file;
use std::path::PathBuf;

/// Absolute path to the checked-in `MyBool` inductive `.olean` fixture, which
/// also ships the Lean-compiled `myNot : MyBool -> MyBool`.
fn inductive_fixture_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/olean/v4.13.0/custom/Inductive.olean")
}

/// Load the `MyBool` fixture into a fresh environment.
///
/// The custom `Inductive.olean` fixture is a minimal module that ships
/// `MyBool` + constructors + eliminators + the Lean-compiled `myNot`, but not
/// the `Eq` machinery. We initialize `Eq` (which gives `Eq`, `Eq.refl`, `rfl`,
/// `Eq.symm`, `Eq.trans`, congruence lemmas) so the elaborated equation lemma
/// and the equality goal have the kernel `Eq` they refer to. This mirrors a
/// real import where `Init` (carrying `Eq`) is loaded before any user module.
fn load_mybool_env() -> Environment {
    let path = inductive_fixture_path();
    let mut env = Environment::default();
    let summary = load_olean_file(&mut env, &path)
        .unwrap_or_else(|e| panic!("loading {} should succeed: {e}", path.display()));
    assert!(
        summary.added_constants > 0,
        "fixture should add constants to the environment"
    );
    env.init_eq().expect("Eq machinery should initialize");
    env
}

fn const_(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

/// `@Eq MyBool lhs rhs` (`MyBool : Type`, so the `Eq` universe level is `1`).
fn mybool_eq(lhs: Expr, rhs: Expr) -> Expr {
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    Expr::app(Expr::app(Expr::app(eq, const_("MyBool")), lhs), rhs)
}

/// `@Eq.refl MyBool value` — the canonical `rfl` proof of `value = value`.
/// (`MyBool : Type`, so `Eq.refl`'s universe level is `1`.)
fn mybool_eq_refl(value: Expr) -> Expr {
    let refl = Expr::const_(
        Name::from_string("Eq.refl"),
        vec![Level::succ(Level::zero())],
    );
    Expr::app(Expr::app(refl, const_("MyBool")), value)
}

/// Register the sorry-free equation theorem
/// `myNot_true : myNot MyBool.myTrue = MyBool.myFalse` directly as a kernel
/// `Declaration::Theorem`, exactly as a Lean-compiled imported theorem would
/// appear: a fully-formed kernel declaration whose proof term is baked in (here
/// `@Eq.refl MyBool MyBool.myFalse`).
///
/// The proof kernel-checks because `myNot MyBool.myTrue` is definitionally equal
/// to `MyBool.myFalse` (it reduces through the *imported* recursor — independently
/// pinned by the match probe's
/// `test_imported_lean_compiled_def_reduces_via_imported_recursor`). So `Eq.refl`
/// at `MyBool.myFalse` inhabits `myNot MyBool.myTrue = MyBool.myFalse`. This is a
/// genuine proof referencing only imported constants, not an axiom restatement.
fn register_imported_eq_theorem(env: &mut Environment) {
    let lhs = Expr::app(const_("myNot"), const_("MyBool.myTrue"));
    let rhs = const_("MyBool.myFalse");
    let type_ = mybool_eq(lhs, rhs.clone());
    // rfl proof: @Eq.refl MyBool MyBool.myFalse : MyBool.myFalse = MyBool.myFalse,
    // which the kernel accepts at type (myNot myTrue = myFalse) by def-eq.
    let value = mybool_eq_refl(rhs);
    env.add_decl(Declaration::Theorem {
        name: Name::from_string("myNot_true"),
        level_params: vec![],
        type_,
        value,
    })
    .expect("imported-style equation theorem myNot_true should kernel-check and register");
}

/// Build an environment that has the imported `MyBool`/`myNot` plus a
/// clean-elab-elaborated, sorry-free equation theorem
/// `myNot_true : myNot MyBool.myTrue = MyBool.myFalse`, registered as a simp
/// lemma through the import bridge's `register_simp_lemma` API.
fn env_with_imported_simp_lemma() -> Environment {
    let mut env = load_mybool_env();

    // A genuine sorry-free, axiom-free equation lemma about the IMPORTED `myNot`.
    register_imported_eq_theorem(&mut env);

    // Sanity: the lemma is itself sorry-free and axiom-free,
    // so any proof simp builds *out of it* can only be clean if the engine wires
    // it in soundly.
    let lemma_info = env
        .get_const(&Name::from_string("myNot_true"))
        .expect("myNot_true should be registered after elaboration");
    let lemma_trust = lemma_info.trust_summary();
    assert!(
        lemma_trust.is_fully_verified(),
        "the imported-lemma equation myNot_true must itself be sorry-free and \
         axiom-free, got {lemma_trust:?}"
    );

    // Register it exactly the way `.olean` import does: re-publish into the
    // kernel simp registry so `get_simp_lemmas()` (which the simp engine reads)
    // returns it. This is the surface the import simp-lemma bridge drives.
    env.register_simp_lemma(Name::from_string("myNot_true"), SimpPriority::Default);
    assert!(
        env.is_simp_lemma(&Name::from_string("myNot_true")),
        "myNot_true must be visible in the kernel simp registry after the bridge"
    );

    env
}

/// Assert the proof of a completed proof state:
/// 1. kernel-checks against `root_goal` (the goal as it stood before simp ran),
/// 2. **references the imported lemma `myNot_true`** — proving the rewrite
///    actually fired and the closure is not a coincidental `rfl` (the goal here
///    is also definitionally closable, so without this check `simp` could close
///    it without ever touching the imported lemma), and
/// 3. is sorry-free with `trusted_axiom_count == 0`.
fn assert_proof_verified_and_clean(state: &ProofState, root_goal: &Goal) {
    let proof = state
        .closed_proof()
        .expect("a completed simp proof state must yield a closed proof term");

    // The proof must kernel-check against the original goal target.
    let _cert = state
        .verify_proof(root_goal, &proof)
        .unwrap_or_else(|e| panic!("simp's imported-lemma proof must kernel-check: {e:?}"));

    // The decisive signal that the IMPORTED lemma was applied (not just resolved,
    // and not bypassed by a pure def-eq `rfl`): its name appears in the proof term.
    let constants = proof.collect_constants();
    assert!(
        constants.contains(&Name::from_string("myNot_true")),
        "simp's proof must reference the imported lemma myNot_true (proving the \
         rewrite fired, not a coincidental rfl), but the proof references: {constants:?}"
    );

    let trust = DeclarationTrustSummary::from_expr(&proof);
    assert!(
        !trust.has_sorry(),
        "the simp proof built from an imported lemma must be sorry-free, got {trust:?}"
    );
    assert_eq!(
        trust.trusted_axiom_count(),
        0,
        "the simp proof built from an imported lemma must carry no trusted axioms, got {trust:?}"
    );
}

// =============================================================================
// Test 1: simp CLOSES a goal directly matching the imported simp lemma's LHS.
//
// Goal: myNot MyBool.myTrue = MyBool.myFalse
// Imported @[simp] lemma: myNot_true : myNot MyBool.myTrue = MyBool.myFalse
//
// simp must rewrite `myNot MyBool.myTrue` -> `MyBool.myFalse`, producing
// `MyBool.myFalse = MyBool.myFalse`, then close by rfl. This proves the import
// bridge does not merely surface the lemma NAME — the rewrite actually fires and
// closes with a verified, axiom-free proof.
// =============================================================================

#[test]
fn test_simp_closes_goal_with_imported_simp_lemma() {
    let env = env_with_imported_simp_lemma();

    let goal = mybool_eq(
        Expr::app(const_("myNot"), const_("MyBool.myTrue")),
        const_("MyBool.myFalse"),
    );
    let mut state = ProofState::new(env, goal);
    // Capture the root goal as it stands before simp so we can kernel-check the
    // produced proof against the original target after closure.
    let root_goal = state
        .goals()
        .front()
        .cloned()
        .expect("fresh proof state has exactly one goal");

    let result = simp(&mut state, SimpConfig::new());
    assert!(
        result.is_ok(),
        "simp should close `myNot myTrue = myFalse` using the imported simp lemma, got: {result:?}"
    );
    assert!(
        state.goals().is_empty(),
        "simp must CLOSE the goal with the imported simp lemma, but {} goal(s) remain",
        state.goals().len()
    );

    assert_proof_verified_and_clean(&state, &root_goal);
}

// =============================================================================
// Test 2: simp REWRITES the imported lemma's LHS inside a larger goal and closes.
//
// Goal: myNot (myNot MyBool.myTrue) = myNot MyBool.myFalse
//
// The imported lemma rewrites the inner `myNot MyBool.myTrue` -> `MyBool.myFalse`
// on the LHS, giving `myNot MyBool.myFalse = myNot MyBool.myFalse`, closed by rfl.
// This confirms the imported lemma fires at a SUBTERM (via congruence), not only
// when it is the whole goal — i.e. genuine rewriting, not coincidental rfl.
// =============================================================================

#[test]
fn test_simp_rewrites_imported_lemma_at_subterm_and_closes() {
    let env = env_with_imported_simp_lemma();

    // LHS: myNot (myNot MyBool.myTrue); RHS: myNot MyBool.myFalse.
    let inner = Expr::app(const_("myNot"), const_("MyBool.myTrue"));
    let lhs = Expr::app(const_("myNot"), inner);
    let rhs = Expr::app(const_("myNot"), const_("MyBool.myFalse"));
    let goal = mybool_eq(lhs, rhs);
    let mut state = ProofState::new(env, goal);
    let root_goal = state
        .goals()
        .front()
        .cloned()
        .expect("fresh proof state has exactly one goal");

    let result = simp(&mut state, SimpConfig::new());
    assert!(
        result.is_ok(),
        "simp should rewrite the imported lemma at a subterm and close, got: {result:?}"
    );
    assert!(
        state.goals().is_empty(),
        "simp must close the subterm-rewrite goal, but {} goal(s) remain",
        state.goals().len()
    );

    assert_proof_verified_and_clean(&state, &root_goal);
}

// =============================================================================
// Test 3: control — without the imported simp lemma REGISTERED, simp never uses
// it. Whatever simp does to the goal (it is definitionally closable, so a pure
// `rfl` may close it), the resulting proof must NOT reference `myNot_true`. This
// isolates the `myNot_true` reference asserted in Tests 1/2 specifically to the
// `register_simp_lemma` bridge: the lemma is only applied because it was
// registered, not because the goal happens to mention `myNot`.
// =============================================================================

#[test]
fn test_simp_without_registration_does_not_use_imported_lemma() {
    // Same environment (the theorem exists as a constant), but WITHOUT registering
    // myNot_true as a simp lemma.
    let mut env = load_mybool_env();
    register_imported_eq_theorem(&mut env);
    // Deliberately do NOT call register_simp_lemma here.
    assert!(
        !env.is_simp_lemma(&Name::from_string("myNot_true")),
        "control precondition: myNot_true must NOT be a registered simp lemma here"
    );

    let goal = mybool_eq(
        Expr::app(const_("myNot"), const_("MyBool.myTrue")),
        const_("MyBool.myFalse"),
    );
    let mut state = ProofState::new(env, goal);

    // simp may close the goal definitionally (rfl sees `myNot myTrue` def-eq to
    // `myFalse`) or make no progress — either is fine. The invariant is that an
    // UNREGISTERED lemma is never applied, so if a proof is produced it must not
    // mention `myNot_true`.
    let _ = simp(&mut state, SimpConfig::new());
    if let Some(proof) = state.closed_proof() {
        let constants = proof.collect_constants();
        assert!(
            !constants.contains(&Name::from_string("myNot_true")),
            "an unregistered simp lemma must never appear in simp's proof, but it did: {constants:?}"
        );
    }
}
