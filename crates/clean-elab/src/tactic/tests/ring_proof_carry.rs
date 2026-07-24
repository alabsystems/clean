// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unit tests for ring_proof_carry.rs proof construction (#2501).
//!
//! Tests the proof-carry normalizer at the function level, verifying:
//! - `ring_normalize_with_proof` produces correct proofs for each case
//! - `combine_side_proofs` handles all 4 branches
//! - `collect_op_terms` flattens correctly
//! - Identity/annihilator elimination produces kernel-valid proofs
//! - Distribution produces kernel-valid proofs
//! - All proofs pass kernel type-checking via checked `close_goal`

use super::*;
use clean_kernel::env::Declaration;
use serial_test::serial;

/// Shared environment: Nat with arithmetic lemmas + symbolic variables a, b, c.
fn proof_carry_env() -> (Environment, Expr) {
    let mut env = Environment::with_prelude();
    env.init_nat_arith_lemmas().unwrap();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    for name in &["a", "b", "c"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: nat.clone(),
        })
        .unwrap();
    }
    (env, nat)
}

fn nat_zero() -> Expr {
    Expr::const_(Name::from_string("Nat.zero"), vec![])
}

fn nat_add(a: Expr, b: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Nat.add"), vec![]), a),
        b,
    )
}

fn nat_mul(a: Expr, b: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Nat.mul"), vec![]), a),
        b,
    )
}

fn var(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn assert_kernel_valid_closed_proof(state: &ProofState, context: &str) {
    let goal_ty = state
        .goal_type()
        .expect("completed proof state should retain the original goal type");
    let proof = state
        .closed_proof()
        .expect("completed proof state should expose a closed proof term");
    let tc = TypeChecker::new(state.env());
    assert!(
        tc.check_type(&proof, &goal_ty).is_ok(),
        "{context}: closed proof must type-check against the original goal"
    );
}

fn assert_ring_nf_closed_clean(state: &ProofState, axiom_before: (u64, u64), context: &str) {
    assert_eq!(
        axiom_snapshot().0 - axiom_before.0,
        0,
        "{context}: should NOT use trustedArith"
    );
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "{context}: per-state trusted count should stay at 0"
    );
    let ledger = state.trust_ledger();
    assert_eq!(
        ledger.trusted_arith_count, 0,
        "{context}: trustedArith ledger should stay at 0"
    );
    assert_eq!(
        ledger.sorry_count, 0,
        "{context}: sorry ledger should stay at 0"
    );
    assert_eq!(
        ledger.trusted_ay_count, 0,
        "{context}: trustedAy ledger should stay at 0"
    );
    assert!(
        state.is_complete(),
        "{context}: goal should be fully closed"
    );
    assert!(
        state.proof_term().is_some(),
        "{context}: proof_term() should be extractable"
    );
    assert_kernel_valid_closed_proof(state, context);
}

// =============================================================================
// collect_op_terms
// =============================================================================

/// collect_op_terms: atom returns a single-element list.
#[test]
fn test_collect_op_terms_atom() {
    use super::super::ring_proof_carry::collect_op_terms;
    let a = var("a");
    let terms = collect_op_terms(&a, "Nat.add");
    assert_eq!(terms.len(), 1, "atom should produce 1 term");
}

/// collect_op_terms: left-associated chain Nat.add(Nat.add(a, b), c) flattens to [a, b, c].
#[test]
fn test_collect_op_terms_left_assoc_chain() {
    use super::super::ring_proof_carry::collect_op_terms;
    let a = var("a");
    let b = var("b");
    let c = var("c");
    let inner = nat_add(a, b);
    let chain = nat_add(inner, c);
    let terms = collect_op_terms(&chain, "Nat.add");
    assert_eq!(terms.len(), 3, "left-assoc chain should flatten to 3 terms");
}

/// collect_op_terms: right-associated chain Nat.add(a, Nat.add(b, c)) produces [a, Nat.add(b,c)].
/// This is expected behavior — right branches are not recursively flattened by collect_op_terms.
/// The flatten_right_assoc proof handles re-association separately.
#[test]
fn test_collect_op_terms_right_assoc_not_flattened() {
    use super::super::ring_proof_carry::collect_op_terms;
    let a = var("a");
    let b = var("b");
    let c = var("c");
    let inner = nat_add(b, c);
    let chain = nat_add(a, inner);
    let terms = collect_op_terms(&chain, "Nat.add");
    assert_eq!(
        terms.len(),
        2,
        "right-assoc chain should NOT be recursively flattened"
    );
}

/// collect_op_terms: mismatched op name treats expression as atom.
#[test]
fn test_collect_op_terms_wrong_op() {
    use super::super::ring_proof_carry::collect_op_terms;
    let a = var("a");
    let b = var("b");
    let add = nat_add(a, b);
    let terms = collect_op_terms(&add, "Nat.mul");
    assert_eq!(terms.len(), 1, "wrong op should treat expr as atom");
}

// =============================================================================
// ring_normalize_with_proof: atom cases
// =============================================================================

/// Atom normalization: non-operator expression returns itself with no proof.
#[test]
fn test_normalize_atom_no_proof() {
    use super::super::ring_proof_carry::ring_normalize_with_proof;
    let (env, _nat) = proof_carry_env();
    let state = ProofState::new(env, Expr::sort(Level::zero()));
    let goal = state.current_goal().unwrap().clone();

    let a = var("a");
    let result = ring_normalize_with_proof(&state, &goal, &a);
    assert!(result.is_some(), "atom should normalize");
    let r = result.unwrap();
    assert!(r.proof.is_none(), "atom should have no proof (def-eq)");
}

/// Operator with no simplification: Nat.add a b returns with no proof when
/// children are already in canonical order and no identity/distribution applies.
#[test]
fn test_normalize_simple_add_no_simplification() {
    use super::super::ring_proof_carry::ring_normalize_with_proof;
    let (env, _nat) = proof_carry_env();
    let state = ProofState::new(env, Expr::sort(Level::zero()));
    let goal = state.current_goal().unwrap().clone();

    let a = var("a");
    let b = var("b");
    let expr = nat_add(a, b);
    let result = ring_normalize_with_proof(&state, &goal, &expr);
    assert!(result.is_some(), "simple add should normalize");
}

// =============================================================================
// Identity elimination via ring_nf (kernel-checked)
// =============================================================================

/// ring_nf with both-sides-proof: `(a + 0) + b = b + a` exercises
/// combine_side_proofs (Some(lp), Some(rp)) branch — both sides normalize
/// with proof terms that must be chained via eq_trans + eq_symm.
#[test]
#[serial]
fn test_ring_nf_both_sides_proof_carry() {
    reset_arith_counter();
    let (env, nat) = proof_carry_env();
    let a = var("a");
    let b = var("b");

    // LHS: (a + 0) + b — needs identity elim on a+0, then reorder
    let lhs = nat_add(nat_add(a.clone(), nat_zero()), b.clone());
    // RHS: b + a — needs reorder
    let rhs = nat_add(b, a);

    let mut state = ProofState::new(env, make_eq(nat, lhs, rhs));
    let axiom_before = axiom_snapshot();

    ring_nf(&mut state).expect("ring_nf should close the both-sides proof-carry goal");

    assert_ring_nf_closed_clean(&state, axiom_before, "both-sides proof carry");
}

/// ring_nf: `a + 0 = a` — LHS normalizes with proof, RHS is unchanged.
/// Exercises combine_side_proofs (Some(lp), None) branch.
#[test]
#[serial]
fn test_ring_nf_lhs_only_proof_carry() {
    reset_arith_counter();
    let (env, nat) = proof_carry_env();
    let a = var("a");

    let lhs = nat_add(a.clone(), nat_zero());
    let rhs = a;

    let mut state = ProofState::new(env, make_eq(nat, lhs, rhs));
    let axiom_before = axiom_snapshot();

    ring_nf(&mut state).expect("ring_nf should close add_zero identity");

    assert_ring_nf_closed_clean(&state, axiom_before, "lhs-only proof carry");
}

/// ring_nf: `a = a + 0` — RHS normalizes with proof, LHS is unchanged.
/// Exercises combine_side_proofs (None, Some(rp)) branch via eq_symm.
#[test]
#[serial]
fn test_ring_nf_rhs_only_proof_carry() {
    reset_arith_counter();
    let (env, nat) = proof_carry_env();
    let a = var("a");

    let lhs = a.clone();
    let rhs = nat_add(a, nat_zero());

    let mut state = ProofState::new(env, make_eq(nat, lhs, rhs));
    let axiom_before = axiom_snapshot();

    ring_nf(&mut state).expect("ring_nf should close reverse add_zero via Eq.symm");

    assert_ring_nf_closed_clean(&state, axiom_before, "rhs-only proof carry");
}

/// ring_nf: `a = a` — neither side changes.
/// Exercises combine_side_proofs (None, None) branch via eq_refl.
#[test]
#[serial]
fn test_ring_nf_neither_side_proof_carry() {
    reset_arith_counter();
    let (env, nat) = proof_carry_env();
    let a = var("a");

    let mut state = ProofState::new(env, make_eq(nat, a.clone(), a));
    let axiom_before = axiom_snapshot();

    ring_nf(&mut state).expect("ring_nf should close trivial equality");

    assert_ring_nf_closed_clean(&state, axiom_before, "neither-side proof carry");
}

// =============================================================================
// Annihilator cases (mul_zero, zero_mul)
// =============================================================================

/// ring_nf: `a * 0 + b = b` — annihilator in sub-expression.
/// Exercises try_identity_elim annihilator path + combine_side_proofs.
#[test]
#[serial]
fn test_ring_nf_annihilator_in_subexpr() {
    reset_arith_counter();
    let (env, nat) = proof_carry_env();
    let a = var("a");
    let b = var("b");

    // LHS: Nat.add(Nat.mul(a, 0), b) — mul(a,0) annihilates to 0, then 0+b = b
    let lhs = nat_add(nat_mul(a, nat_zero()), b.clone());
    let rhs = b;

    let mut state = ProofState::new(env, make_eq(nat, lhs, rhs));
    let axiom_before = axiom_snapshot();

    ring_nf(&mut state).expect("ring_nf should close the annihilator-in-subexpression goal");

    assert_ring_nf_closed_clean(&state, axiom_before, "annihilator in sub-expression");
}

// =============================================================================
// Distribution cases
// =============================================================================

/// ring_nf: `a * (b + c) = a * b + a * c` — left distribution.
/// Exercises try_left_distrib path.
#[test]
#[serial]
fn test_ring_nf_left_distrib_proof_carry() {
    reset_arith_counter();
    let (env, nat) = proof_carry_env();
    let a = var("a");
    let b = var("b");
    let c = var("c");

    let lhs = nat_mul(a.clone(), nat_add(b.clone(), c.clone()));
    let rhs = nat_add(nat_mul(a.clone(), b), nat_mul(a, c));

    let mut state = ProofState::new(env, make_eq(nat, lhs, rhs));
    let axiom_before = axiom_snapshot();

    ring_nf(&mut state).expect("ring_nf should close the left-distribution goal");

    assert_ring_nf_closed_clean(&state, axiom_before, "left distribution proof carry");
}

/// ring_nf: `(a + b) * c = a * c + b * c` — right distribution.
/// Exercises try_right_distrib path.
#[test]
#[serial]
fn test_ring_nf_right_distrib_proof_carry() {
    reset_arith_counter();
    let (env, nat) = proof_carry_env();
    let a = var("a");
    let b = var("b");
    let c = var("c");

    let lhs = nat_mul(nat_add(a.clone(), b.clone()), c.clone());
    let rhs = nat_add(nat_mul(a, c.clone()), nat_mul(b, c));

    let mut state = ProofState::new(env, make_eq(nat, lhs, rhs));
    let axiom_before = axiom_snapshot();

    ring_nf(&mut state).expect("ring_nf should close the right-distribution goal");

    assert_ring_nf_closed_clean(&state, axiom_before, "right distribution proof carry");
}

// =============================================================================
// Sorting / commutativity
// =============================================================================

/// ring_nf: `b + a = a + b` — commutativity requires sorting proof.
/// Exercises merge_sorted_chains + bubble_sort_chain in ring_proof_sort.
#[test]
#[serial]
fn test_ring_nf_commutativity_proof_carry() {
    reset_arith_counter();
    let (env, nat) = proof_carry_env();
    let a = var("a");
    let b = var("b");

    let lhs = nat_add(b.clone(), a.clone());
    let rhs = nat_add(a, b);

    let mut state = ProofState::new(env, make_eq(nat, lhs, rhs));
    let axiom_before = axiom_snapshot();

    ring_nf(&mut state).expect("ring_nf should close the commutativity proof-carry goal");

    assert_ring_nf_closed_clean(&state, axiom_before, "commutativity proof carry");
}

/// ring_nf: `c + a + b = a + b + c` — 3-term reorder.
/// Exercises deeper bubble sort paths with congruence lifting.
#[test]
#[serial]
fn test_ring_nf_three_term_reorder_proof_carry() {
    reset_arith_counter();
    let (env, nat) = proof_carry_env();
    let a = var("a");
    let b = var("b");
    let c = var("c");

    let lhs = nat_add(nat_add(c.clone(), a.clone()), b.clone());
    let rhs = nat_add(nat_add(a, b), c);

    let mut state = ProofState::new(env, make_eq(nat, lhs, rhs));
    let axiom_before = axiom_snapshot();

    ring_nf(&mut state).expect("ring_nf should close the three-term reorder goal");

    assert_ring_nf_closed_clean(&state, axiom_before, "three-term reorder proof carry");
}

// =============================================================================
// chain_optional unit tests
// =============================================================================

/// chain_optional: (None, None) → None.
#[test]
fn test_chain_optional_none_none() {
    use super::super::ring_proof_carry::chain_optional;
    let (env, _nat) = proof_carry_env();
    let state = ProofState::new(env, Expr::sort(Level::zero()));
    let goal = state.current_goal().unwrap().clone();

    let result = chain_optional(&state, &goal, None, None);
    assert!(result.is_none(), "(None, None) should yield None");
}

/// chain_optional: (Some(p), None) → Some(p).
#[test]
fn test_chain_optional_some_none() {
    use super::super::ring_proof_carry::chain_optional;
    let (env, _nat) = proof_carry_env();
    let state = ProofState::new(env, Expr::sort(Level::zero()));
    let goal = state.current_goal().unwrap().clone();

    let dummy_proof = Expr::const_(Name::from_string("dummy"), vec![]);
    let result = chain_optional(&state, &goal, Some(dummy_proof.clone()), None);
    assert!(result.is_some(), "(Some, None) should yield Some");
}

/// chain_optional: (None, Some(p)) → Some(p).
#[test]
fn test_chain_optional_none_some() {
    use super::super::ring_proof_carry::chain_optional;
    let (env, _nat) = proof_carry_env();
    let state = ProofState::new(env, Expr::sort(Level::zero()));
    let goal = state.current_goal().unwrap().clone();

    let dummy_proof = Expr::const_(Name::from_string("dummy"), vec![]);
    let result = chain_optional(&state, &goal, None, Some(dummy_proof.clone()));
    assert!(result.is_some(), "(None, Some) should yield Some");
}

// =============================================================================
// Coefficient-merging (#ring-coeff-merge): x + x → 2*x fusion
// =============================================================================

/// `a + a = 2*a` — minimal coefficient-merge case.
#[test]
#[serial]
fn test_ring_coeff_merge_add_self() {
    reset_arith_counter();
    let (env, nat) = proof_carry_env();
    let a = var("a");
    let two = super::super::finite_cases::make_nat_literal(2);
    let lhs = nat_add(a.clone(), a.clone());
    let rhs = nat_mul(two, a);
    let mut state = ProofState::new(env, make_eq(nat, lhs, rhs));
    let before = axiom_snapshot();
    ring_nf(&mut state).expect("ring_nf should prove a + a = 2*a");
    assert_ring_nf_closed_clean(&state, before, "a+a=2*a coeff merge");
}

/// `(a+b)*(a+b) = a*a + 2*a*b + b*b` — the binomial-square fusion.
#[test]
#[serial]
fn test_ring_coeff_merge_binomial_square() {
    reset_arith_counter();
    let (env, nat) = proof_carry_env();
    let a = var("a");
    let b = var("b");
    let two = super::super::finite_cases::make_nat_literal(2);
    let lhs = nat_mul(nat_add(a.clone(), b.clone()), nat_add(a.clone(), b.clone()));
    // a*a + 2*a*b + b*b  (2*a*b parses as (2*a)*b)
    let rhs = nat_add(
        nat_add(
            nat_mul(a.clone(), a.clone()),
            nat_mul(nat_mul(two, a.clone()), b.clone()),
        ),
        nat_mul(b.clone(), b.clone()),
    );
    let mut state = ProofState::new(env, make_eq(nat, lhs, rhs));
    let before = axiom_snapshot();
    ring_nf(&mut state).expect("ring_nf should prove the binomial square");
    assert_ring_nf_closed_clean(&state, before, "binomial square coeff merge");
}

/// Reordered RHS: `(a+b)*(a+b) = a*a + b*b + 2*a*b`.
#[test]
#[serial]
fn test_ring_coeff_merge_binomial_reordered() {
    reset_arith_counter();
    let (env, nat) = proof_carry_env();
    let a = var("a");
    let b = var("b");
    let two = super::super::finite_cases::make_nat_literal(2);
    let lhs = nat_mul(nat_add(a.clone(), b.clone()), nat_add(a.clone(), b.clone()));
    // a*a + b*b + 2*a*b
    let rhs = nat_add(
        nat_add(nat_mul(a.clone(), a.clone()), nat_mul(b.clone(), b.clone())),
        nat_mul(nat_mul(two, a.clone()), b.clone()),
    );
    let mut state = ProofState::new(env, make_eq(nat, lhs, rhs));
    let before = axiom_snapshot();
    ring_nf(&mut state).expect("ring_nf should prove the reordered binomial square");
    assert_ring_nf_closed_clean(&state, before, "binomial square reordered");
}

/// NEGATIVE: `(a+b)*(a+b) = a*a + a*b + b*b` (missing coefficient) must FAIL.
#[test]
#[serial]
fn test_ring_coeff_merge_missing_coeff_fails() {
    reset_arith_counter();
    let (env, nat) = proof_carry_env();
    let a = var("a");
    let b = var("b");
    let lhs = nat_mul(nat_add(a.clone(), b.clone()), nat_add(a.clone(), b.clone()));
    let rhs = nat_add(
        nat_add(nat_mul(a.clone(), a.clone()), nat_mul(a.clone(), b.clone())),
        nat_mul(b.clone(), b.clone()),
    );
    let mut state = ProofState::new(env, make_eq(nat, lhs, rhs));
    let r = ring_nf(&mut state);
    assert!(
        r.is_err(),
        "ring must NOT prove the missing-coefficient (false) goal"
    );
    assert_eq!(state.trusted_axiom_count(), 0, "no trust axiom on failure");
    assert!(!state.is_complete(), "false goal must remain open");
}

/// NEGATIVE: `a + a = 3*a` must FAIL.
#[test]
#[serial]
fn test_ring_coeff_merge_wrong_coeff_fails() {
    reset_arith_counter();
    let (env, nat) = proof_carry_env();
    let a = var("a");
    let three = super::super::finite_cases::make_nat_literal(3);
    let lhs = nat_add(a.clone(), a.clone());
    let rhs = nat_mul(three, a);
    let mut state = ProofState::new(env, make_eq(nat, lhs, rhs));
    let r = ring_nf(&mut state);
    assert!(r.is_err(), "ring must NOT prove a + a = 3*a");
    assert_eq!(state.trusted_axiom_count(), 0, "no trust axiom on failure");
    assert!(!state.is_complete(), "false goal must remain open");
}
