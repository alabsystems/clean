// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! E2e tests for additive and scaled combination paths (#2493, #302).
//!
//! These exercise `build_add_le_add_proof` and `build_scaled_proof` in
//! `arith_linarith_proof.rs` — the non-chain combination paths that were
//! previously returning `None` for 3+ hypotheses or mixed scaling.
//!
//! The chain closer (`build_chain_proof`) cannot handle these cases because
//! the hypothesis endpoints don't match for transitivity. The additive
//! combiner sums all LHS and RHS terms via `SortLeAcc::combine`, producing
//! a single accumulated bound that the Int contradiction closer evaluates
//! concretely.

use super::support::*;
use super::*;

/// 3 concrete Int LE hypotheses with no chainable endpoints.
///
/// - h1: Int.ofNat(5) ≤ Int.ofNat(2)
/// - h2: Int.ofNat(3) ≤ Int.ofNat(1)
/// - h3: Int.ofNat(4) ≤ Int.ofNat(0)
///
/// Chain fails: endpoints {5,3,4} and {2,1,0} have no matches.
/// Additive: (5+3+4) ≤ (2+1+0) → 12 ≤ 3 → contradiction via Int closer.
fn mk_lia_additive_three_hyps_case() -> ArithmeticE2eCase {
    let env = mk_env_for_int_arith();
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let five = mk_int_ofnat(5);
    let two = mk_int_ofnat(2);
    let three = mk_int_ofnat(3);
    let one = mk_int_ofnat(1);
    let four = mk_int_ofnat(4);
    let zero = mk_int_ofnat(0);

    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let ay_five = terms.mk_var("const5", Sort::Int);
    let ay_two = terms.mk_var("const2", Sort::Int);
    let ay_three = terms.mk_var("const3", Sort::Int);
    let ay_one = terms.mk_var("const1", Sort::Int);
    let ay_four = terms.mk_var("const4", Sort::Int);
    let ay_zero = terms.mk_var("const0", Sort::Int);

    map.register_var("const5", five.clone(), int_ty.clone());
    map.register_var("const2", two.clone(), int_ty.clone());
    map.register_var("const3", three.clone(), int_ty.clone());
    map.register_var("const1", one.clone(), int_ty.clone());
    map.register_var("const4", four.clone(), int_ty.clone());
    map.register_var("const0", zero.clone(), int_ty);

    let le_5_2 = terms.mk_le(ay_five, ay_two);
    let le_3_1 = terms.mk_le(ay_three, ay_one);
    let le_4_0 = terms.mk_le(ay_four, ay_zero);
    let not_le_5_2 = terms.mk_not(le_5_2);
    let not_le_3_1 = terms.mk_not(le_3_1);
    let not_le_4_0 = terms.mk_not(le_4_0);

    let le_5_2_prop = mk_le_int(&five, &two);
    let le_3_1_prop = mk_le_int(&three, &one);
    let le_4_0_prop = mk_le_int(&four, &zero);

    let h1_id = FVarId::new(10);
    let h2_id = FVarId::new(11);
    let h3_id = FVarId::new(12);
    map.register_hypothesis("h_5_le_2", h1_id, Expr::fvar(h1_id), le_5_2_prop.clone());
    map.register_hypothesis("h_3_le_1", h2_id, Expr::fvar(h2_id), le_3_1_prop.clone());
    map.register_hypothesis("h_4_le_0", h3_id, Expr::fvar(h3_id), le_4_0_prop.clone());

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1, 1]);
    let s0 = proof.add_theory_lemma_with_farkas_and_kind(
        "LIA",
        vec![not_le_5_2, not_le_3_1, not_le_4_0],
        farkas,
        TheoryLemmaKind::LiaGeneric,
    );
    let s1 = proof.add_assume(le_5_2, None);
    let s2 = proof.add_resolution(vec![not_le_3_1, not_le_4_0], not_le_5_2, s0, s1);
    let s3 = proof.add_assume(le_3_1, None);
    let s4 = proof.add_resolution(vec![not_le_4_0], not_le_3_1, s2, s3);
    let s5 = proof.add_assume(le_4_0, None);
    proof.add_resolution(vec![], not_le_4_0, s4, s5);

    ArithmeticE2eCase {
        env,
        terms,
        map,
        proof,
        neg_goal: negated_false_goal(),
        hyps: vec![
            (h1_id, "h_5_le_2", le_5_2_prop),
            (h2_id, "h_3_le_1", le_3_1_prop),
            (h3_id, "h_4_le_0", le_4_0_prop),
        ],
        context: "LIA additive 3-hypothesis non-chain e2e (#2493)",
    }
}

/// Mixed scaled Int combination: coeff [2, 1].
///
/// - h1: Int.ofNat(3) ≤ Int.ofNat(1), coeff 2 → scaled to (3+3) ≤ (1+1)
/// - h2: Int.ofNat(2) ≤ Int.ofNat(0), coeff 1 → unscaled (2) ≤ (0)
///
/// Combined: ((3+3)+2) ≤ ((1+1)+0) → 8 ≤ 2 → contradiction via Int closer.
fn mk_lia_scaled_mixed_case() -> ArithmeticE2eCase {
    let env = mk_env_for_int_arith();
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let three = mk_int_ofnat(3);
    let one = mk_int_ofnat(1);
    let two = mk_int_ofnat(2);
    let zero = mk_int_ofnat(0);

    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let ay_three = terms.mk_var("const3", Sort::Int);
    let ay_one = terms.mk_var("const1", Sort::Int);
    let ay_two = terms.mk_var("const2", Sort::Int);
    let ay_zero = terms.mk_var("const0", Sort::Int);

    map.register_var("const3", three.clone(), int_ty.clone());
    map.register_var("const1", one.clone(), int_ty.clone());
    map.register_var("const2", two.clone(), int_ty.clone());
    map.register_var("const0", zero.clone(), int_ty);

    let le_3_1 = terms.mk_le(ay_three, ay_one);
    let le_2_0 = terms.mk_le(ay_two, ay_zero);
    let not_le_3_1 = terms.mk_not(le_3_1);
    let not_le_2_0 = terms.mk_not(le_2_0);

    let le_3_1_prop = mk_le_int(&three, &one);
    let le_2_0_prop = mk_le_int(&two, &zero);

    let h1_id = FVarId::new(10);
    let h2_id = FVarId::new(11);
    map.register_hypothesis("h_3_le_1", h1_id, Expr::fvar(h1_id), le_3_1_prop.clone());
    map.register_hypothesis("h_2_le_0", h2_id, Expr::fvar(h2_id), le_2_0_prop.clone());

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[2, 1]);
    let s0 = proof.add_theory_lemma_with_farkas_and_kind(
        "LIA",
        vec![not_le_3_1, not_le_2_0],
        farkas,
        TheoryLemmaKind::LiaGeneric,
    );
    let s1 = proof.add_assume(le_3_1, None);
    let s2 = proof.add_resolution(vec![not_le_2_0], not_le_3_1, s0, s1);
    let s3 = proof.add_assume(le_2_0, None);
    proof.add_resolution(vec![], not_le_2_0, s2, s3);

    ArithmeticE2eCase {
        env,
        terms,
        map,
        proof,
        neg_goal: negated_false_goal(),
        hyps: vec![
            (h1_id, "h_3_le_1", le_3_1_prop),
            (h2_id, "h_2_le_0", le_2_0_prop),
        ],
        context: "LIA scaled mixed (coeff [2,1]) e2e (#2493)",
    }
}

#[test]
fn test_e2e_lia_additive_three_hyps_type_checks() {
    let case = mk_lia_additive_three_hyps_case();
    let result = attempt_reconstruction(&case.proof, &case.terms, &case.map, &case.neg_goal);
    assert_eq!(
        result.stats.trust_boundary_steps, 1,
        "theory lemma should hit trust boundary: {:?}",
        result.stats
    );
    assert!(
        result.trust_subterm_count > 0,
        "proof should carry trust debt from the synthesized trust sub-term"
    );
}

#[test]
fn test_e2e_lia_scaled_mixed_type_checks() {
    let case = mk_lia_scaled_mixed_case();
    let result = attempt_reconstruction(&case.proof, &case.terms, &case.map, &case.neg_goal);
    assert_eq!(
        result.stats.trust_boundary_steps, 1,
        "theory lemma should hit trust boundary: {:?}",
        result.stats
    );
    assert!(
        result.trust_subterm_count > 0,
        "proof should carry trust debt from the synthesized trust sub-term"
    );
}
