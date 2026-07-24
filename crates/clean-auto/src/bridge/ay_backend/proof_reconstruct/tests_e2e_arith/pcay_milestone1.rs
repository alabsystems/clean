// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof-carrying-ay milestone 1: the roadmap's `x > 10 ∧ x < 5` QF_LIA UNSAT
//! fixture, certified end-to-end through the PUBLIC composer
//! [`reconstruct_and_certify_ay_proof`] — native reconstruction of ay's
//! structured proof into a kernel term, then the real kernel
//! `check_type(_, False)`. Carcara is NOT on this path.
//!
//! POSITIVE: the fixture certifies with `trust_count == 0` — soundness reduces
//! to the Clean kernel, retiring `trustedAy` for this obligation.
//!
//! NEGATIVE (fail-closed): a WRONG proof (a bogus theory lemma that does not
//! actually close the clause) must NOT certify.

use super::support::*;
use super::*;
use crate::bridge::ay_backend::proof_reconstruct::certified_proof::reconstruct_and_certify_ay_proof;

/// Keep the arithmetic variable in the local context.  Modelling it as a
/// top-level axiom makes an otherwise kernel-valid open proof fail the
/// certification authority audit, because arbitrary data axioms are not part
/// of Clean's foundational base.
fn test_x_fvar_id() -> FVarId {
    FVarId::new(9)
}

/// Build the ay structured proof for `10 < x`, `x < 5` using genuine ay integer
/// CONSTANTS (`mk_int`) — the shape a real ay QF_LIA refutation emits.
///
/// UNSAT: `10 < x < 5` chains to `10 < 5`, which the concrete-Int chain closer
/// discharges via `NonNeg.casesOn` — a kernel term with NO `trustedAy`.
fn mk_x_gt10_lt5_case() -> ArithmeticE2eCase {
    let env = mk_env_for_int_arith();
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let ten = mk_int_ofnat(10);
    let five = mk_int_ofnat(5);
    let test_x = Expr::fvar(test_x_fvar_id());

    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let ay_ten = terms.mk_int(num_bigint::BigInt::from(10));
    let ay_five = terms.mk_int(num_bigint::BigInt::from(5));
    let ay_x = terms.mk_var("testX", Sort::Int);

    map.register_var("testX", test_x.clone(), int_ty.clone());

    let lt_10x = terms.mk_lt(ay_ten, ay_x);
    let lt_x5 = terms.mk_lt(ay_x, ay_five);
    let not_lt_10x = terms.mk_not(lt_10x);
    let not_lt_x5 = terms.mk_not(lt_x5);

    let lt_10x_prop = mk_lt_int(&ten, &test_x);
    let lt_x5_prop = mk_lt_int(&test_x, &five);

    let h1_id = FVarId::new(10);
    let h2_id = FVarId::new(11);
    map.register_hypothesis("h_10_lt_x", h1_id, Expr::fvar(h1_id), lt_10x_prop.clone());
    map.register_hypothesis("h_x_lt_5", h2_id, Expr::fvar(h2_id), lt_x5_prop.clone());

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    let s0 = proof.add_theory_lemma_with_farkas_and_kind(
        "LIA",
        vec![not_lt_10x, not_lt_x5],
        farkas,
        TheoryLemmaKind::LiaGeneric,
    );
    let s1 = proof.add_assume(lt_10x, None);
    let s2 = proof.add_resolution(vec![not_lt_x5], not_lt_10x, s0, s1);
    let s3 = proof.add_assume(lt_x5, None);
    proof.add_resolution(vec![], not_lt_x5, s2, s3);

    ArithmeticE2eCase {
        env,
        terms,
        map,
        proof,
        neg_goal: negated_false_goal(),
        hyps: vec![
            (h1_id, "h_10_lt_x", lt_10x_prop),
            (h2_id, "h_x_lt_5", lt_x5_prop),
        ],
        context: "pcay-m1 x>10 && x<5",
    }
}

/// POSITIVE: the milestone-1 LIA fixture certifies via the kernel with
/// `trust_count == 0` (no `trustedAy`, no Carcara).
#[test]
fn test_pcay_m1_x_gt10_lt5_certifies_zero_trust() {
    let case = mk_x_gt10_lt5_case();

    // Zero-trust NATIVE reconstruction: no trust boundary, no trust sub-term.
    let result = attempt_reconstruction(&case.proof, &case.terms, &case.map, &case.neg_goal);
    assert_zero_trust_reconstruction(&result, case.context);

    let mut ctx = LocalContext::new();
    ctx.push_with_id(
        test_x_fvar_id(),
        Name::from_string("testX"),
        Expr::const_(Name::from_string("Int"), vec![]),
        BinderInfo::Default,
    );
    for (id, name, prop) in &case.hyps {
        ctx.push_with_id(
            *id,
            Name::from_string(name),
            prop.clone(),
            BinderInfo::Default,
        );
    }

    let payload = reconstruct_and_certify_ay_proof(
        &case.proof,
        &case.terms,
        &case.map,
        &case.neg_goal,
        &case.env,
        &ctx,
    )
    .expect("x>10 && x<5 must certify through the Clean kernel");

    assert_eq!(
        payload.trust_count, 0,
        "milestone-1 LIA UNSAT must be kernel-Certified with ZERO trust in ay"
    );
    assert!(
        !payload.term_bytes.is_empty(),
        "certified payload must carry the serialized kernel term"
    );
}

/// NEGATIVE (fail-closed): a WRONG proof — the theory-lemma clause claims
/// `¬(10 < x) ∨ ¬(x < 5)` is a tautology while the resolution actually leaves a
/// non-empty clause (we drop the second resolution so the root is NOT the empty
/// clause) — must NOT certify. The honest pre-certification verdict survives.
#[test]
fn test_pcay_m1_incomplete_proof_is_not_certified() {
    let mut case = mk_x_gt10_lt5_case();

    // Rebuild a proof whose final step does NOT derive the empty clause: stop
    // after one resolution, leaving `¬(x < 5)` unresolved.
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let ten = mk_int_ofnat(10);
    let five = mk_int_ofnat(5);
    let test_x = Expr::fvar(test_x_fvar_id());
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();
    let ay_ten = terms.mk_int(num_bigint::BigInt::from(10));
    let ay_five = terms.mk_int(num_bigint::BigInt::from(5));
    let ay_x = terms.mk_var("testX", Sort::Int);
    map.register_var("testX", test_x.clone(), int_ty.clone());
    let lt_10x = terms.mk_lt(ay_ten, ay_x);
    let lt_x5 = terms.mk_lt(ay_x, ay_five);
    let not_lt_10x = terms.mk_not(lt_10x);
    let not_lt_x5 = terms.mk_not(lt_x5);
    let h1_id = FVarId::new(10);
    let h2_id = FVarId::new(11);
    map.register_hypothesis(
        "h_10_lt_x",
        h1_id,
        Expr::fvar(h1_id),
        mk_lt_int(&ten, &test_x),
    );
    map.register_hypothesis(
        "h_x_lt_5",
        h2_id,
        Expr::fvar(h2_id),
        mk_lt_int(&test_x, &five),
    );
    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    let s0 = proof.add_theory_lemma_with_farkas_and_kind(
        "LIA",
        vec![not_lt_10x, not_lt_x5],
        farkas,
        TheoryLemmaKind::LiaGeneric,
    );
    let s1 = proof.add_assume(lt_10x, None);
    // Only ONE resolution: the root still carries `¬(x < 5)` — NOT empty.
    proof.add_resolution(vec![not_lt_x5], not_lt_10x, s0, s1);
    case.proof = proof;
    case.terms = terms;
    case.map = map;

    let mut ctx = LocalContext::new();
    ctx.push_with_id(
        test_x_fvar_id(),
        Name::from_string("testX"),
        int_ty,
        BinderInfo::Default,
    );
    ctx.push_with_id(
        h1_id,
        Name::from_string("h_10_lt_x"),
        mk_lt_int(&ten, &test_x),
        BinderInfo::Default,
    );
    ctx.push_with_id(
        h2_id,
        Name::from_string("h_x_lt_5"),
        mk_lt_int(&test_x, &five),
        BinderInfo::Default,
    );

    let outcome = reconstruct_and_certify_ay_proof(
        &case.proof,
        &case.terms,
        &case.map,
        &case.neg_goal,
        &case.env,
        &ctx,
    );
    assert!(
        outcome.is_err(),
        "an incomplete proof (root not the empty clause) must FAIL-CLOSED, never certify: {outcome:?}"
    );
}
