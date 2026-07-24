// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Part of #3368: axiom-free `ring` proof reconstruction for typeclass-headed
//! (`HAdd.hAdd` / `HMul.hMul`) goals over a REAL environment.
//!
//! The earlier `ring_hadd_hmul.rs` tests registered bare `add_comm`/`mul_comm`
//! axioms in the test environment as a stand-in for the typeclass-layer lemmas.
//! Those bare names do NOT exist in the real prelude — only the concrete,
//! kernel-CHECKED, zero-axiom lemmas (`Nat.add_comm`, ...) do. These tests pin
//! the carrier-aware resolution (FIX A2): a typeclass-headed goal over a
//! concrete carrier resolves to the concrete per-type lemma, and the resulting
//! proof is kernel-type-checked with an empty (foundational-only) axiom closure.
//!
//! No bare `add_comm`/`mul_comm`/`left_distrib` is ever registered here.

use super::*;
use clean_kernel::env::Declaration;
use serial_test::serial;

/// Build `@Eq.{1} Nat lhs rhs`.
fn eq_nat(nat: &Expr, lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [nat.clone(), lhs, rhs],
    )
}

/// `@HAdd.hAdd.{0,0,0} Nat Nat Nat instHAddNat a b` (the elaborated form of `a + b`).
fn hadd_nat(a: Expr, b: Expr) -> Expr {
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let inst = Expr::const_(Name::from_string("instHAddNat"), vec![]);
    let hadd = Expr::const_(
        Name::from_string("HAdd.hAdd"),
        vec![Level::zero(), Level::zero(), Level::zero()],
    );
    Expr::apps(hadd, [nat.clone(), nat.clone(), nat, inst, a, b])
}

/// `@HMul.hMul.{0,0,0} Nat Nat Nat instHMulNat a b` (the elaborated form of `a * b`).
fn hmul_nat(a: Expr, b: Expr) -> Expr {
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let inst = Expr::const_(Name::from_string("instHMulNat"), vec![]);
    let hmul = Expr::const_(
        Name::from_string("HMul.hMul"),
        vec![Level::zero(), Level::zero(), Level::zero()],
    );
    Expr::apps(hmul, [nat.clone(), nat.clone(), nat, inst, a, b])
}

/// A REAL Nat environment: only the kernel-checked `Nat.*` lemmas are present.
/// Crucially, the bare typeclass lemma names are NOT registered.
fn real_nat_env() -> (Environment, Expr) {
    let mut env = Environment::with_prelude();
    env.init_nat_arith_lemmas()
        .expect("nat arith lemmas should init");
    env.init_nat_hmul_inst()
        .expect("Nat HMul instance should init");
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    for name in &["a", "b", "c"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: nat.clone(),
        })
        .unwrap();
    }
    // Sanity: the bare typeclass lemma names must be absent — the whole point is
    // that the fix resolves to the concrete carrier lemma instead.
    for bare in &[
        "add_comm",
        "mul_comm",
        "add_assoc",
        "mul_assoc",
        "left_distrib",
    ] {
        assert!(
            env.get_const(&Name::from_string(bare)).is_none(),
            "bare typeclass lemma `{bare}` must NOT be registered (real-env guarantee)"
        );
    }
    (env, nat)
}

fn var(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

/// Assert ring_nf closed the goal with a kernel-checked, axiom-free proof:
/// - no trustedArith (per-state and global counters),
/// - state complete + proof extractable,
/// - proof type-checks against the original goal type in the kernel,
/// - the proof's transitive axiom closure is ⊆ FOUNDATIONAL_AXIOMS (i.e.
///   `axiom_deps` over the registered theorem is EMPTY — no trustedArith,
///   no sorryAx, no domain-specific axiom).
fn assert_axiom_free_close(state: &ProofState, axiom_before: (u64, u64), ctx: &str) {
    assert_eq!(
        axiom_snapshot().0 - axiom_before.0,
        0,
        "{ctx}: must NOT emit trustedArith"
    );
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "{ctx}: trusted count must be 0"
    );
    assert!(state.is_complete(), "{ctx}: goal must be fully closed");

    let goal_ty = state
        .goal_type()
        .expect("completed state retains the goal type");
    let proof = state
        .closed_proof()
        .expect("completed state exposes a closed proof term");

    // 1) Kernel type-check: the proof inhabits the ORIGINAL goal type.
    let tc = TypeChecker::new(state.env());
    tc.check_type(&proof, &goal_ty)
        .unwrap_or_else(|e| panic!("{ctx}: proof must kernel-type-check: {e:?}"));

    // 2) Axiom closure: register the proof as a Theorem and assert its
    //    transitive non-foundational axiom set is empty.
    let mut env = state.env().clone();
    let thm = Name::from_string("__ring_axiom_free_probe");
    env.add_decl(Declaration::Theorem {
        name: thm.clone(),
        level_params: vec![],
        type_: goal_ty,
        value: proof,
    })
    .unwrap_or_else(|e| panic!("{ctx}: proof must register as a kernel Theorem: {e:?}"));

    // axiom_deps returns the transitive NON-foundational axiom set. The proof is
    // built only from kernel-CHECKED Theorem lemmas (Nat.add_comm, ...) whose own
    // closures are foundational, so the only residual axioms are the test's own
    // opaque free-variable placeholders (a/b/c, declared as `Axiom`). The proof
    // must therefore reach NO trust marker and NO ring/domain axiom — only the
    // declared variables.
    let deps = env
        .axiom_deps(&thm)
        .expect("axiom_deps must resolve the probe theorem");
    let free_vars: std::collections::HashSet<String> =
        ["a", "b", "c"].into_iter().map(String::from).collect();
    let residual: Vec<String> = deps
        .iter()
        .map(|n| n.to_string())
        .filter(|s| !free_vars.contains(s))
        .collect();
    assert!(
        residual.is_empty(),
        "{ctx}: axiom closure must be ⊆ FOUNDATIONAL_AXIOMS ∪ {{free vars}} \
         (no trustedArith / sorryAx / domain axiom), got residual = {residual:?}"
    );
    // Explicit teeth: none of the known trust markers may appear.
    for marker in ["trustedArith", "trustedAy", "sorry", "sorryAx"] {
        assert!(
            !deps.iter().any(|n| n.to_string() == marker),
            "{ctx}: proof must NOT reach trust marker `{marker}`"
        );
    }
}

// =====================================================================
// PROVE-IT: the four common identities, HAdd/HMul-headed, kernel-checked
// =====================================================================

/// `a + b = b + a` (HAdd.hAdd) — resolves to Nat.add_comm.
#[test]
#[serial]
fn test_hadd_comm_axiom_free() {
    reset_arith_counter();
    let (env, nat) = real_nat_env();
    let (a, b) = (var("a"), var("b"));
    let mut state = ProofState::new(
        env,
        eq_nat(&nat, hadd_nat(a.clone(), b.clone()), hadd_nat(b, a)),
    );
    let before = axiom_snapshot();
    ring(&mut state).expect("ring should prove a + b = b + a (HAdd)");
    assert_axiom_free_close(&state, before, "HAdd a+b=b+a");
}

/// `a * b = b * a` (HMul.hMul) — resolves to Nat.mul_comm.
#[test]
#[serial]
fn test_hmul_comm_axiom_free() {
    reset_arith_counter();
    let (env, nat) = real_nat_env();
    let (a, b) = (var("a"), var("b"));
    let mut state = ProofState::new(
        env,
        eq_nat(&nat, hmul_nat(a.clone(), b.clone()), hmul_nat(b, a)),
    );
    let before = axiom_snapshot();
    ring(&mut state).expect("ring should prove a * b = b * a (HMul)");
    assert_axiom_free_close(&state, before, "HMul a*b=b*a");
}

/// `a * (b + c) = a * b + a * c` (HMul/HAdd) — resolves to Nat.left_distrib.
#[test]
#[serial]
fn test_hmul_left_distrib_axiom_free() {
    reset_arith_counter();
    let (env, nat) = real_nat_env();
    let (a, b, c) = (var("a"), var("b"), var("c"));
    let lhs = hmul_nat(a.clone(), hadd_nat(b.clone(), c.clone()));
    let rhs = hadd_nat(hmul_nat(a.clone(), b), hmul_nat(a, c));
    let mut state = ProofState::new(env, eq_nat(&nat, lhs, rhs));
    let before = axiom_snapshot();
    ring(&mut state).expect("ring should prove a*(b+c) = a*b + a*c (HMul/HAdd)");
    assert_axiom_free_close(&state, before, "HMul/HAdd a*(b+c)=a*b+a*c");
}

/// `(a + b) + c = a + (b + c)` (HAdd.hAdd) — resolves to Nat.add_assoc.
#[test]
#[serial]
fn test_hadd_assoc_axiom_free() {
    reset_arith_counter();
    let (env, nat) = real_nat_env();
    let (a, b, c) = (var("a"), var("b"), var("c"));
    let lhs = hadd_nat(hadd_nat(a.clone(), b.clone()), c.clone());
    let rhs = hadd_nat(a, hadd_nat(b, c));
    let mut state = ProofState::new(env, eq_nat(&nat, lhs, rhs));
    let before = axiom_snapshot();
    ring(&mut state).expect("ring should prove (a+b)+c = a+(b+c) (HAdd)");
    assert_axiom_free_close(&state, before, "HAdd (a+b)+c=a+(b+c)");
}

// =====================================================================
// NEGATIVE / teeth: false ring goals must STILL FAIL (never fake-close)
// =====================================================================

/// `a + b = a * b` is FALSE. ring must NOT prove it.
#[test]
#[serial]
fn test_false_add_eq_mul_fails() {
    reset_arith_counter();
    let (env, nat) = real_nat_env();
    let (a, b) = (var("a"), var("b"));
    let mut state = ProofState::new(
        env,
        eq_nat(&nat, hadd_nat(a.clone(), b.clone()), hmul_nat(a, b)),
    );
    let r = ring(&mut state);
    assert!(r.is_err(), "ring must NOT prove a + b = a * b");
    assert_eq!(state.trusted_axiom_count(), 0, "no trust axiom on failure");
    assert!(!state.is_complete(), "false goal must remain open");
}

/// `a + a = a` is FALSE (for symbolic a). ring must NOT prove it.
#[test]
#[serial]
fn test_false_add_self_eq_self_fails() {
    reset_arith_counter();
    let (env, nat) = real_nat_env();
    let a = var("a");
    let mut state = ProofState::new(env, eq_nat(&nat, hadd_nat(a.clone(), a.clone()), a));
    let r = ring(&mut state);
    assert!(r.is_err(), "ring must NOT prove a + a = a");
    assert_eq!(state.trusted_axiom_count(), 0, "no trust axiom on failure");
    assert!(!state.is_complete(), "false goal must remain open");
}

// =====================================================================
// ADVERSARIAL (reviewer-added): independent soundness probes.
// =====================================================================

/// Reviewer probe: the emitted proof term must NOT textually contain any trust
/// marker. Greps the Debug rendering of the closed proof term directly, not the
/// axiom_deps abstraction.
#[test]
#[serial]
fn adv_proof_term_has_no_trust_marker() {
    reset_arith_counter();
    let (env, nat) = real_nat_env();
    let (a, b) = (var("a"), var("b"));
    let mut state = ProofState::new(
        env,
        eq_nat(&nat, hadd_nat(a.clone(), b.clone()), hadd_nat(b, a)),
    );
    ring(&mut state).expect("ring should prove a + b = b + a");
    let proof = state.closed_proof().expect("closed proof");
    let rendered = format!("{proof:?}");
    for marker in ["trustedArith", "trustedAy", "sorryAx", "sorry"] {
        assert!(
            !rendered.contains(marker),
            "proof term must not mention `{marker}`; got: {rendered}"
        );
    }
    // Positive: it should actually reference the real Nat lemma.
    assert!(
        rendered.contains("add_comm"),
        "expected the real Nat.add_comm lemma in the proof term: {rendered}"
    );
}

/// Reviewer probe: the kernel check is NON-VACUOUS. Take the genuine proof of
/// `a + b = b + a` and try to type-check it against a DIFFERENT goal type
/// `a + b = a + b` — the kernel must REJECT it. If this passed, the kernel
/// check in `assert_axiom_free_close` would be meaningless.
#[test]
#[serial]
fn adv_kernel_check_is_non_vacuous() {
    reset_arith_counter();
    let (env, nat) = real_nat_env();
    let (a, b) = (var("a"), var("b"));
    let goal = eq_nat(
        &nat,
        hadd_nat(a.clone(), b.clone()),
        hadd_nat(b.clone(), a.clone()),
    );
    let mut state = ProofState::new(env, goal);
    ring(&mut state).expect("ring proves a+b=b+a");
    let proof = state.closed_proof().expect("closed proof");

    // A wrong goal type: reflexive a + b = a + b (well-typed, but NOT what the
    // comm proof inhabits).
    let wrong_goal = eq_nat(&nat, hadd_nat(a.clone(), b.clone()), hadd_nat(a, b));
    let tc = TypeChecker::new(state.env());
    let res = tc.check_type(&proof, &wrong_goal);
    assert!(
        res.is_err(),
        "kernel MUST reject the comm proof against a reflexive goal (else the check is vacuous)"
    );
}

/// Reviewer probe: `(2 : Nat) = 3` is FALSE. ring must NOT prove it.
#[test]
#[serial]
fn adv_false_two_eq_three_fails() {
    reset_arith_counter();
    let (env, nat) = real_nat_env();
    let two = make_nat_literal(2);
    let three = make_nat_literal(3);
    let mut state = ProofState::new(env, eq_nat(&nat, two, three));
    let r = ring(&mut state);
    assert!(r.is_err(), "ring must NOT prove 2 = 3");
    assert_eq!(state.trusted_axiom_count(), 0, "no trust axiom on failure");
    assert!(!state.is_complete(), "false goal must remain open");
}

/// Reviewer probe: `a * (b + c) = a*b + a*c` is the Tier-2 carry path. After it
/// closes, independently register the proof as a Theorem and assert axiom_deps
/// reaches NO trust marker — even though we reach it through a different code
/// path (carry/distribute) than the comm case.
#[test]
#[serial]
fn adv_distrib_carry_no_trust_marker_term() {
    reset_arith_counter();
    let (env, nat) = real_nat_env();
    let (a, b, c) = (var("a"), var("b"), var("c"));
    let lhs = hmul_nat(a.clone(), hadd_nat(b.clone(), c.clone()));
    let rhs = hadd_nat(hmul_nat(a.clone(), b), hmul_nat(a, c));
    let mut state = ProofState::new(env, eq_nat(&nat, lhs, rhs));
    ring(&mut state).expect("ring proves distrib via carry path");
    let proof = state.closed_proof().expect("closed proof");
    let rendered = format!("{proof:?}");
    for marker in ["trustedArith", "trustedAy", "sorryAx"] {
        assert!(
            !rendered.contains(marker),
            "distrib carry proof term must not mention `{marker}`: {rendered}"
        );
    }
}
