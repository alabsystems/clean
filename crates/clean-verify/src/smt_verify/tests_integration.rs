// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end integration tests for the SMT proof verification pipeline.
//!
//! Each test constructs a complete `SmtProofDag` with assumptions, theory
//! lemmas, and resolution steps, then runs `verify_smt_proof()` to check
//! the full 3-phase pipeline: structural validation, semantic checking, and
//! terminal empty-clause verification.

use super::dag::{
    LiaDetail, SmtProofDag, SmtProofStep, SmtSort, SmtStepId, SmtSymbol, SmtTerm, SmtTermId,
    SmtTheory, TheoryLemmaDetail,
};
use super::trust::SmtVerifyError;
use super::{verify_smt_proof, VerifyMode};

// ── Helpers ──────────────────────────────────────────────────────────────

/// Build `(op lhs rhs)` as a function application term.
fn add_binop(dag: &mut SmtProofDag, op: &str, lhs: SmtTermId, rhs: SmtTermId) -> SmtTermId {
    dag.add_term(SmtTerm::App(
        SmtSymbol::Named(op.to_string()),
        vec![lhs, rhs],
    ))
}

/// Build `(= lhs rhs)`.
fn make_eq(dag: &mut SmtProofDag, lhs: SmtTermId, rhs: SmtTermId) -> SmtTermId {
    add_binop(dag, "=", lhs, rhs)
}

/// Build `(f arg)` — unary function application.
fn make_app1(dag: &mut SmtProofDag, f: &str, arg: SmtTermId) -> SmtTermId {
    dag.add_term(SmtTerm::App(SmtSymbol::Named(f.to_string()), vec![arg]))
}

// ═════════════════════════════════════════════════════════════════════════
// 1. LRA Integration Tests
// ═════════════════════════════════════════════════════════════════════════

#[test]
fn test_lra_simple_bound_conflict_x_ge_0_x_le_neg1() {
    // UNSAT: x >= 0 AND x <= -1
    //
    // Proof structure:
    //   s0: assume (>= x 0)         — clause: [(>= x 0)]
    //   s1: assume (<= x -1)        — clause: [(<= x -1)]
    //   s2: LRA Farkas lemma        — clause: [not(>= x 0), not(<= x -1)]
    //       Conflict: x >= 0 AND x <= -1
    //       Farkas: 1*(x >= 0) + 1*(x <= -1)
    //         => -(x-0) + (x-(-1)) <= 0  ...  i.e., -x + x + 1 <= 0 => 1 <= 0 contradiction
    //   s3: resolve s0 + s2 on (>= x 0) => [not(<= x -1)]
    //   s4: resolve s1 + s3 on (<= x -1) => []

    let mut dag = SmtProofDag::new();
    dag.declare("x".to_string(), SmtSort::Real);

    let x = dag.add_term(SmtTerm::Var("x".to_string(), SmtSort::Real));
    let zero = dag.add_term(SmtTerm::Int(0));
    let neg_one = dag.add_term(SmtTerm::Int(-1));

    let ge_x_0 = add_binop(&mut dag, ">=", x, zero);
    let le_x_neg1 = add_binop(&mut dag, "<=", x, neg_one);
    let not_ge_x_0 = dag.add_term(SmtTerm::Not(ge_x_0));
    let not_le_x_neg1 = dag.add_term(SmtTerm::Not(le_x_neg1));

    // Steps
    let s0 = dag.add_step(SmtProofStep::Assume(ge_x_0));
    let s1 = dag.add_step(SmtProofStep::Assume(le_x_neg1));

    // LRA Farkas lemma: clause = [not(>= x 0), not(<= x -1)]
    // Conflict (negation of clause): (>= x 0) AND (<= x -1)
    // Farkas coefficients: (1,1) for each inequality.
    let s2 = dag.add_step(SmtProofStep::TheoryLemma {
        theory: SmtTheory::Lra,
        kind: TheoryLemmaDetail::LraFarkas {
            coefficients: vec![(1, 1), (1, 1)],
        },
        clause: vec![not_ge_x_0, not_le_x_neg1],
    });

    // Resolve s0 + s2 on ge_x_0 => [not_le_x_neg1]
    let s3 = dag.add_step(SmtProofStep::Resolution {
        clause: vec![not_le_x_neg1],
        premises: vec![s0, s2],
        pivot: Some(ge_x_0),
    });

    // Resolve s1 + s3 on le_x_neg1 => []
    dag.add_step(SmtProofStep::Resolution {
        clause: vec![],
        premises: vec![s1, s3],
        pivot: Some(le_x_neg1),
    });

    let result = verify_smt_proof(&dag, VerifyMode::Strict);
    assert!(
        result.valid,
        "LRA bound conflict proof should be valid: {:?}",
        result.first_error
    );
    assert!(result.stats.is_fully_verified());
    assert_eq!(
        result.stats.theory_lemma_counts.get(&SmtTheory::Lra),
        Some(&1),
    );
    assert_eq!(result.stats.kernel_verified, 3); // 1 LRA + 2 resolutions
    assert_eq!(result.stats.axiomatic, 2); // 2 assumptions
}

#[test]
fn test_lra_farkas_two_variable_combination() {
    // UNSAT: x + y >= 1, x <= 0, y <= 0
    //
    // Farkas combination with coefficients (1, 1, 1):
    //   1*(x+y >= 1) + 1*(x <= 0) + 1*(y <= 0)
    //   Conflict: (x+y >= 1) AND (x <= 0) AND (y <= 0)
    //   Normalize: -(x+y) + 1 <= 0 AND x <= 0 AND y <= 0
    //   Sum: -x - y + 1 + x + y = 1 <= 0 => contradiction
    //
    // Blocking clause: [not(>= (+ x y) 1), not(<= x 0), not(<= y 0)]

    let mut dag = SmtProofDag::new();
    dag.declare("x".to_string(), SmtSort::Real);
    dag.declare("y".to_string(), SmtSort::Real);

    let x = dag.add_term(SmtTerm::Var("x".to_string(), SmtSort::Real));
    let y = dag.add_term(SmtTerm::Var("y".to_string(), SmtSort::Real));
    let zero = dag.add_term(SmtTerm::Int(0));
    let one = dag.add_term(SmtTerm::Int(1));

    let x_plus_y = add_binop(&mut dag, "+", x, y);
    let ge_xy_1 = add_binop(&mut dag, ">=", x_plus_y, one);
    let le_x_0 = add_binop(&mut dag, "<=", x, zero);
    let le_y_0 = add_binop(&mut dag, "<=", y, zero);

    let not_ge_xy_1 = dag.add_term(SmtTerm::Not(ge_xy_1));
    let not_le_x_0 = dag.add_term(SmtTerm::Not(le_x_0));
    let not_le_y_0 = dag.add_term(SmtTerm::Not(le_y_0));

    // Assumptions
    let s0 = dag.add_step(SmtProofStep::Assume(ge_xy_1));
    let s1 = dag.add_step(SmtProofStep::Assume(le_x_0));
    let s2 = dag.add_step(SmtProofStep::Assume(le_y_0));

    // LRA Farkas lemma with coefficients (1,1) each
    let s3 = dag.add_step(SmtProofStep::TheoryLemma {
        theory: SmtTheory::Lra,
        kind: TheoryLemmaDetail::LraFarkas {
            coefficients: vec![(1, 1), (1, 1), (1, 1)],
        },
        clause: vec![not_ge_xy_1, not_le_x_0, not_le_y_0],
    });

    // Resolve s0 + s3 on ge_xy_1 => [not_le_x_0, not_le_y_0]
    let s4 = dag.add_step(SmtProofStep::Resolution {
        clause: vec![not_le_x_0, not_le_y_0],
        premises: vec![s0, s3],
        pivot: Some(ge_xy_1),
    });

    // Resolve s1 + s4 on le_x_0 => [not_le_y_0]
    let s5 = dag.add_step(SmtProofStep::Resolution {
        clause: vec![not_le_y_0],
        premises: vec![s1, s4],
        pivot: Some(le_x_0),
    });

    // Resolve s2 + s5 on le_y_0 => []
    dag.add_step(SmtProofStep::Resolution {
        clause: vec![],
        premises: vec![s2, s5],
        pivot: Some(le_y_0),
    });

    let result = verify_smt_proof(&dag, VerifyMode::Strict);
    assert!(
        result.valid,
        "LRA Farkas 2-variable proof should be valid: {:?}",
        result.first_error
    );
    assert!(result.stats.is_fully_verified());
    assert_eq!(
        result.stats.theory_lemma_counts.get(&SmtTheory::Lra),
        Some(&1),
    );
}

// ═════════════════════════════════════════════════════════════════════════
// 2. LIA Integration Tests
// ═════════════════════════════════════════════════════════════════════════

#[test]
fn test_lia_simple_bound_conflict() {
    // UNSAT: x >= 1 AND x <= -1 (integers)
    //
    // Blocking clause: [not(>= x 1), not(<= x -1)]
    // Conflict: x >= 1 AND x <= -1
    // Normalized:
    //   not(>= x 1): conflict is (x >= 1) => -x + 1 <= 0
    //   not(<= x -1): conflict is (x <= -1) => x + 1 <= 0
    // Sum: (-x + x) + (1 + 1) = 2 <= 0 => contradiction!

    let mut dag = SmtProofDag::new();
    dag.declare("x".to_string(), SmtSort::Int);

    let x = dag.add_term(SmtTerm::Var("x".to_string(), SmtSort::Int));
    let one = dag.add_term(SmtTerm::Int(1));
    let neg_one = dag.add_term(SmtTerm::Int(-1));

    let ge_x_1 = add_binop(&mut dag, ">=", x, one);
    let le_x_neg1 = add_binop(&mut dag, "<=", x, neg_one);
    let not_ge_x_1 = dag.add_term(SmtTerm::Not(ge_x_1));
    let not_le_x_neg1 = dag.add_term(SmtTerm::Not(le_x_neg1));

    let s0 = dag.add_step(SmtProofStep::Assume(ge_x_1));
    let s1 = dag.add_step(SmtProofStep::Assume(le_x_neg1));

    let s2 = dag.add_step(SmtProofStep::TheoryLemma {
        theory: SmtTheory::Lia,
        kind: TheoryLemmaDetail::LiaGeneric {
            annotation: LiaDetail::FarkasOnly,
            coefficients: Some(vec![1, 1]),
        },
        clause: vec![not_ge_x_1, not_le_x_neg1],
    });

    let s3 = dag.add_step(SmtProofStep::Resolution {
        clause: vec![not_le_x_neg1],
        premises: vec![s0, s2],
        pivot: Some(ge_x_1),
    });

    dag.add_step(SmtProofStep::Resolution {
        clause: vec![],
        premises: vec![s1, s3],
        pivot: Some(le_x_neg1),
    });

    let result = verify_smt_proof(&dag, VerifyMode::Strict);
    assert!(
        result.valid,
        "LIA bound conflict proof should be valid: {:?}",
        result.first_error
    );
    assert!(result.stats.is_fully_verified());
    assert_eq!(
        result.stats.theory_lemma_counts.get(&SmtTheory::Lia),
        Some(&1),
    );
}

#[test]
fn test_lia_gcd_tightening() {
    // UNSAT: 2x >= 3 AND 2x <= 0
    //
    // GCD tightening:
    //   2x >= 3 => -2x + 3 <= 0 => after GCD(2): -x + floor(3/2) = -x + 1 <= 0
    //   2x <= 0 => 2x <= 0       => after GCD(2): x <= 0
    // Sum: (-x + x) + (1 + 0) = 1 <= 0 => contradiction!
    //
    // Blocking clause: [not(>= (* 2 x) 3), not(<= (* 2 x) 0)]

    let mut dag = SmtProofDag::new();
    dag.declare("x".to_string(), SmtSort::Int);

    let x = dag.add_term(SmtTerm::Var("x".to_string(), SmtSort::Int));
    let two = dag.add_term(SmtTerm::Int(2));
    let three = dag.add_term(SmtTerm::Int(3));
    let zero = dag.add_term(SmtTerm::Int(0));
    let two_x = add_binop(&mut dag, "*", two, x);

    let ge_2x_3 = add_binop(&mut dag, ">=", two_x, three);
    let le_2x_0 = add_binop(&mut dag, "<=", two_x, zero);
    let not_ge_2x_3 = dag.add_term(SmtTerm::Not(ge_2x_3));
    let not_le_2x_0 = dag.add_term(SmtTerm::Not(le_2x_0));

    let s0 = dag.add_step(SmtProofStep::Assume(ge_2x_3));
    let s1 = dag.add_step(SmtProofStep::Assume(le_2x_0));

    let s2 = dag.add_step(SmtProofStep::TheoryLemma {
        theory: SmtTheory::Lia,
        kind: TheoryLemmaDetail::LiaGeneric {
            annotation: LiaDetail::CuttingPlane { divisor: 2 },
            coefficients: Some(vec![1, 1]),
        },
        clause: vec![not_ge_2x_3, not_le_2x_0],
    });

    let s3 = dag.add_step(SmtProofStep::Resolution {
        clause: vec![not_le_2x_0],
        premises: vec![s0, s2],
        pivot: Some(ge_2x_3),
    });

    dag.add_step(SmtProofStep::Resolution {
        clause: vec![],
        premises: vec![s1, s3],
        pivot: Some(le_2x_0),
    });

    let result = verify_smt_proof(&dag, VerifyMode::Strict);
    assert!(
        result.valid,
        "LIA GCD tightening proof should be valid: {:?}",
        result.first_error
    );
    assert!(result.stats.is_fully_verified());
}

#[test]
fn test_lia_two_variable_bound_conflict() {
    // UNSAT: x + y >= 3 AND x <= 0 AND y <= 0 (integers)
    //
    // Same logic as the LRA 2-variable test but via LIA.
    // Normalized conflict:
    //   -(x+y) + 3 <= 0 (from x+y >= 3) => after int tightening: -x -y + 3 <= 0
    //   x <= 0
    //   y <= 0
    // Sum: (-x+x) + (-y+y) + 3 = 3 <= 0 => contradiction

    let mut dag = SmtProofDag::new();
    dag.declare("x".to_string(), SmtSort::Int);
    dag.declare("y".to_string(), SmtSort::Int);

    let x = dag.add_term(SmtTerm::Var("x".to_string(), SmtSort::Int));
    let y = dag.add_term(SmtTerm::Var("y".to_string(), SmtSort::Int));
    let zero = dag.add_term(SmtTerm::Int(0));
    let three = dag.add_term(SmtTerm::Int(3));
    let x_plus_y = add_binop(&mut dag, "+", x, y);

    let ge_xy_3 = add_binop(&mut dag, ">=", x_plus_y, three);
    let le_x_0 = add_binop(&mut dag, "<=", x, zero);
    let le_y_0 = add_binop(&mut dag, "<=", y, zero);
    let not_ge_xy_3 = dag.add_term(SmtTerm::Not(ge_xy_3));
    let not_le_x_0 = dag.add_term(SmtTerm::Not(le_x_0));
    let not_le_y_0 = dag.add_term(SmtTerm::Not(le_y_0));

    let s0 = dag.add_step(SmtProofStep::Assume(ge_xy_3));
    let s1 = dag.add_step(SmtProofStep::Assume(le_x_0));
    let s2 = dag.add_step(SmtProofStep::Assume(le_y_0));

    let s3 = dag.add_step(SmtProofStep::TheoryLemma {
        theory: SmtTheory::Lia,
        kind: TheoryLemmaDetail::LiaGeneric {
            annotation: LiaDetail::FarkasOnly,
            coefficients: Some(vec![1, 1, 1]),
        },
        clause: vec![not_ge_xy_3, not_le_x_0, not_le_y_0],
    });

    let s4 = dag.add_step(SmtProofStep::Resolution {
        clause: vec![not_le_x_0, not_le_y_0],
        premises: vec![s0, s3],
        pivot: Some(ge_xy_3),
    });

    let s5 = dag.add_step(SmtProofStep::Resolution {
        clause: vec![not_le_y_0],
        premises: vec![s1, s4],
        pivot: Some(le_x_0),
    });

    dag.add_step(SmtProofStep::Resolution {
        clause: vec![],
        premises: vec![s2, s5],
        pivot: Some(le_y_0),
    });

    let result = verify_smt_proof(&dag, VerifyMode::Strict);
    assert!(
        result.valid,
        "LIA 2-variable proof should be valid: {:?}",
        result.first_error
    );
    assert!(result.stats.is_fully_verified());
}

// ═════════════════════════════════════════════════════════════════════════
// 3. EUF Integration Tests
// ═════════════════════════════════════════════════════════════════════════

#[test]
fn test_euf_congruence_f_a_neq_f_b() {
    // UNSAT: a = b, f(a) != f(b)
    //
    // Proof:
    //   s0: assume (= a b)
    //   s1: assume (not (= (f a) (f b)))
    //   s2: EufCongruent lemma: clause = [not(= a b), (= (f a) (f b))]
    //   s3: resolve s0 + s2 on (= a b) => [(= (f a) (f b))]
    //   s4: resolve s1 + s3 on (= (f a) (f b)) => []

    let mut dag = SmtProofDag::new();
    dag.declare("a".to_string(), SmtSort::Int);
    dag.declare("b".to_string(), SmtSort::Int);

    let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Int));
    let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Int));
    let fa = make_app1(&mut dag, "f", a);
    let fb = make_app1(&mut dag, "f", b);

    let eq_ab = make_eq(&mut dag, a, b);
    let eq_fa_fb = make_eq(&mut dag, fa, fb);
    let not_eq_ab = dag.add_term(SmtTerm::Not(eq_ab));
    let not_eq_fa_fb = dag.add_term(SmtTerm::Not(eq_fa_fb));

    let s0 = dag.add_step(SmtProofStep::Assume(eq_ab));
    let s1 = dag.add_step(SmtProofStep::Assume(not_eq_fa_fb));

    let s2 = dag.add_step(SmtProofStep::TheoryLemma {
        theory: SmtTheory::Euf,
        kind: TheoryLemmaDetail::EufCongruent,
        clause: vec![not_eq_ab, eq_fa_fb],
    });

    let s3 = dag.add_step(SmtProofStep::Resolution {
        clause: vec![eq_fa_fb],
        premises: vec![s0, s2],
        pivot: Some(eq_ab),
    });

    dag.add_step(SmtProofStep::Resolution {
        clause: vec![],
        premises: vec![s1, s3],
        pivot: Some(eq_fa_fb),
    });

    let result = verify_smt_proof(&dag, VerifyMode::Strict);
    assert!(
        result.valid,
        "EUF congruence proof should be valid: {:?}",
        result.first_error
    );
    assert!(result.stats.is_fully_verified());
    assert_eq!(
        result.stats.theory_lemma_counts.get(&SmtTheory::Euf),
        Some(&1),
    );
}

#[test]
fn test_euf_transitivity_a_eq_b_b_eq_c_a_neq_c() {
    // UNSAT: a = b, b = c, a != c
    //
    // Proof:
    //   s0: assume (= a b)
    //   s1: assume (= b c)
    //   s2: assume (not (= a c))
    //   s3: EufTransitive lemma: [not(= a b), not(= b c), (= a c)]
    //   s4: resolve s0 + s3 on (= a b) => [not(= b c), (= a c)]
    //   s5: resolve s1 + s4 on (= b c) => [(= a c)]
    //   s6: resolve s2 + s5 on (= a c) => []

    let mut dag = SmtProofDag::new();
    let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Int));
    let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Int));
    let c = dag.add_term(SmtTerm::Var("c".to_string(), SmtSort::Int));

    let eq_ab = make_eq(&mut dag, a, b);
    let eq_bc = make_eq(&mut dag, b, c);
    let eq_ac = make_eq(&mut dag, a, c);
    let not_eq_ab = dag.add_term(SmtTerm::Not(eq_ab));
    let not_eq_bc = dag.add_term(SmtTerm::Not(eq_bc));
    let not_eq_ac = dag.add_term(SmtTerm::Not(eq_ac));

    let s0 = dag.add_step(SmtProofStep::Assume(eq_ab));
    let s1 = dag.add_step(SmtProofStep::Assume(eq_bc));
    let s2 = dag.add_step(SmtProofStep::Assume(not_eq_ac));

    let s3 = dag.add_step(SmtProofStep::TheoryLemma {
        theory: SmtTheory::Euf,
        kind: TheoryLemmaDetail::EufTransitive,
        clause: vec![not_eq_ab, not_eq_bc, eq_ac],
    });

    let s4 = dag.add_step(SmtProofStep::Resolution {
        clause: vec![not_eq_bc, eq_ac],
        premises: vec![s0, s3],
        pivot: Some(eq_ab),
    });

    let s5 = dag.add_step(SmtProofStep::Resolution {
        clause: vec![eq_ac],
        premises: vec![s1, s4],
        pivot: Some(eq_bc),
    });

    dag.add_step(SmtProofStep::Resolution {
        clause: vec![],
        premises: vec![s2, s5],
        pivot: Some(eq_ac),
    });

    let result = verify_smt_proof(&dag, VerifyMode::Strict);
    assert!(
        result.valid,
        "EUF transitivity proof should be valid: {:?}",
        result.first_error
    );
    assert!(result.stats.is_fully_verified());
}

#[test]
fn test_euf_generic_congruence_closure() {
    // UNSAT: a = b, f(a) != f(b) — via EufGeneric (congruence closure checker)
    //
    // Same problem as test_euf_congruence_f_a_neq_f_b but uses EufGeneric
    // which exercises the full congruence closure algorithm.

    let mut dag = SmtProofDag::new();
    let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Int));
    let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Int));
    let fa = make_app1(&mut dag, "f", a);
    let fb = make_app1(&mut dag, "f", b);

    let eq_ab = make_eq(&mut dag, a, b);
    let eq_fa_fb = make_eq(&mut dag, fa, fb);
    let not_eq_ab = dag.add_term(SmtTerm::Not(eq_ab));
    let not_eq_fa_fb = dag.add_term(SmtTerm::Not(eq_fa_fb));

    let s0 = dag.add_step(SmtProofStep::Assume(eq_ab));
    let s1 = dag.add_step(SmtProofStep::Assume(not_eq_fa_fb));

    let s2 = dag.add_step(SmtProofStep::TheoryLemma {
        theory: SmtTheory::Euf,
        kind: TheoryLemmaDetail::EufGeneric,
        clause: vec![not_eq_ab, eq_fa_fb],
    });

    let s3 = dag.add_step(SmtProofStep::Resolution {
        clause: vec![eq_fa_fb],
        premises: vec![s0, s2],
        pivot: Some(eq_ab),
    });

    dag.add_step(SmtProofStep::Resolution {
        clause: vec![],
        premises: vec![s1, s3],
        pivot: Some(eq_fa_fb),
    });

    let result = verify_smt_proof(&dag, VerifyMode::Strict);
    assert!(
        result.valid,
        "EUF generic congruence closure proof should be valid: {:?}",
        result.first_error
    );
    assert!(result.stats.is_fully_verified());
}

#[test]
fn test_euf_nested_congruence_f_f_a_neq_f_f_b() {
    // UNSAT: a = b, f(f(a)) != f(f(b))
    //
    // Uses EufGeneric. The congruence closure should propagate:
    //   a ~ b => f(a) ~ f(b) => f(f(a)) ~ f(f(b)) => violates disequality.

    let mut dag = SmtProofDag::new();
    let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Int));
    let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Int));
    let fa = make_app1(&mut dag, "f", a);
    let fb = make_app1(&mut dag, "f", b);
    let ffa = make_app1(&mut dag, "f", fa);
    let ffb = make_app1(&mut dag, "f", fb);

    let eq_ab = make_eq(&mut dag, a, b);
    let eq_ffa_ffb = make_eq(&mut dag, ffa, ffb);
    let not_eq_ab = dag.add_term(SmtTerm::Not(eq_ab));
    let not_eq_ffa_ffb = dag.add_term(SmtTerm::Not(eq_ffa_ffb));

    let s0 = dag.add_step(SmtProofStep::Assume(eq_ab));
    let s1 = dag.add_step(SmtProofStep::Assume(not_eq_ffa_ffb));

    let s2 = dag.add_step(SmtProofStep::TheoryLemma {
        theory: SmtTheory::Euf,
        kind: TheoryLemmaDetail::EufGeneric,
        clause: vec![not_eq_ab, eq_ffa_ffb],
    });

    let s3 = dag.add_step(SmtProofStep::Resolution {
        clause: vec![eq_ffa_ffb],
        premises: vec![s0, s2],
        pivot: Some(eq_ab),
    });

    dag.add_step(SmtProofStep::Resolution {
        clause: vec![],
        premises: vec![s1, s3],
        pivot: Some(eq_ffa_ffb),
    });

    let result = verify_smt_proof(&dag, VerifyMode::Strict);
    assert!(
        result.valid,
        "EUF nested congruence proof should be valid: {:?}",
        result.first_error
    );
    assert!(result.stats.is_fully_verified());
}

// ═════════════════════════════════════════════════════════════════════════
// 4. Mixed Theory Tests
// ═════════════════════════════════════════════════════════════════════════

#[test]
fn test_mixed_euf_lra_two_theory_lemmas() {
    // UNSAT: f(x) = y, x >= 0, y <= -1
    //
    // This requires two theory lemmas:
    //   1. EUF lemma: not(= f(x) y), not(= y z) => (= f(x) z) — not quite.
    //
    // Simpler mixed-theory scenario:
    //   Assume: (= a b), (>= a 0), (<= b -1)
    //   EUF gives us: a = b, so we know a and b refer to the same value.
    //   LRA gives us: a >= 0 AND b <= -1 is UNSAT given a = b.
    //
    // Proof:
    //   s0: assume (= a b)
    //   s1: assume (>= a 0)
    //   s2: assume (<= b -1)
    //   s3: EufTransitive: [not(= a b), (= a b)] — trivial, not useful
    //
    // Actually, let's do a proper mixed theory proof:
    //   Assume: a = b, a >= 0, b <= -1
    //   The conflict is in LRA once we substitute b for a (or vice versa).
    //
    // In practice, the solver would produce:
    //   s3: LRA lemma: [not(>= a 0), not(<= a -1)] — bounds conflict on "a"
    //   But we assumed (<= b -1), not (<= a -1).
    //
    // Better approach: two separate theory lemmas combined via resolution.
    //   s3: EUF transitive: [not(= a b), (= a b)]  — no, that's trivial
    //
    // A realistic mixed proof:
    //   Assume: (= a b), (>= a 1), (<= b 0)
    //   s3: EUF congruent_pred or just use: the solver infers (>= b 1) from
    //       (= a b) and (>= a 1) via equality substitution.
    //   But SMT proofs handle this via:
    //     s3: EUF lemma: not(= a b) OR not(>= a 1) OR (>= b 1)
    //         [because if a=b and a>=1, then b>=1]
    //     s4: LRA: not(>= b 1) OR not(<= b 0)
    //         [because b>=1 and b<=0 is contradictory]
    //     Then resolve everything to empty.
    //
    // But EUF congruent_pred checks predicates, not general substitution.
    // Let's use an approach that works with the existing checkers:
    //
    // We'll combine an EUF generic lemma with an LRA Farkas lemma.
    // Assume: a = b, a >= 1, b <= 0
    // Two lemmas:
    //   EUF: not(= a b), not(>= a 1), (>= b 1)   — EufCongruentPred-style
    //   LRA: not(>= b 1), not(<= b 0)              — Farkas: b >= 1, b <= 0
    //
    // Actually EufCongruentPred operates on predicate symbols, not on >= directly.
    // Let's use a simpler approach with resolution:
    //
    // Assume: p, not_p
    // p comes from EUF, not_p comes from LRA.

    // Let's keep it simple: prove UNSAT by having an EUF lemma and an LRA lemma
    // where each derives part of the contradiction, and resolution ties them together.
    //
    // Proof of: a = b, f(a) != f(b), x >= 0, x <= -1
    //   s0: assume (= a b)
    //   s1: assume (not (= f(a) f(b)))
    //   s2: assume (>= x 0)
    //   s3: assume (<= x -1)
    //   s4: EUF congruent: [not(= a b), (= f(a) f(b))]
    //   s5: LRA Farkas: [not(>= x 0), not(<= x -1)]
    //   s6: resolve s0 + s4 on (= a b) => [(= f(a) f(b))]
    //   s7: resolve s1 + s6 on (= f(a) f(b)) => []  -- wait, this already derives empty.
    //   Actually s7 derives empty from EUF alone. We need both theories involved.
    //
    // Better: interleave the theories.
    // Let's use a proof where resolution combines lemmas from both theories:
    //
    // Assume: (= a b), (>= a 0), (<= b -1)
    // s3: EUF transitive: [not(= a b), (= a b)] — identity, useless
    //
    // Ok, the simplest mixed-theory proof that MUST use both:
    // We'll have TWO independent sources of contradiction feeding into the same
    // resolution chain, each from different theories. The final empty clause
    // comes from resolving the EUF sub-proof with the LRA sub-proof.
    //
    // Proof of: a = b, f(a) != f(b), x >= 0, x <= -1
    // where p = (= f(a) f(b)) and q = (>= x 0), r = (<= x -1)
    //
    // s0: assume p_disguised = (= a b)  -> {(= a b)}
    // s1: assume not_p_disguised = not(= f(a) f(b)) -> {not(= f(a) f(b))}
    // s2: assume (>= x 0) -> {(>= x 0)}
    // s3: assume (<= x -1) -> {(<= x -1)}
    // s4: EUF congruent: {not(= a b), (= f(a) f(b))}
    // s5: LRA Farkas: {not(>= x 0), not(<= x -1)}
    // s6: resolve s0 + s4 on (= a b) => {(= f(a) f(b))}
    // s7: resolve s1 + s6 on (= f(a) f(b)) => {} -- already empty, doesn't use LRA.
    //
    // The issue is these are independent sub-problems. A truly mixed proof needs
    // the two theories to interact. But for a pipeline integration test, having
    // both theory lemma types in the same proof DAG is what matters.
    // Let's just test that a proof with BOTH an EUF lemma and an LRA lemma
    // verifies correctly through the pipeline.

    let mut dag = SmtProofDag::new();

    // EUF part
    let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Int));
    let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Int));
    let fa = make_app1(&mut dag, "f", a);
    let fb = make_app1(&mut dag, "f", b);
    let eq_ab = make_eq(&mut dag, a, b);
    let eq_fa_fb = make_eq(&mut dag, fa, fb);
    let not_eq_ab = dag.add_term(SmtTerm::Not(eq_ab));
    let not_eq_fa_fb = dag.add_term(SmtTerm::Not(eq_fa_fb));

    // LRA part
    let x = dag.add_term(SmtTerm::Var("x".to_string(), SmtSort::Real));
    let zero = dag.add_term(SmtTerm::Int(0));
    let neg_one = dag.add_term(SmtTerm::Int(-1));
    let ge_x_0 = add_binop(&mut dag, ">=", x, zero);
    let le_x_neg1 = add_binop(&mut dag, "<=", x, neg_one);
    let not_ge_x_0 = dag.add_term(SmtTerm::Not(ge_x_0));
    let not_le_x_neg1 = dag.add_term(SmtTerm::Not(le_x_neg1));

    // We'll make an "or" term to bridge: the overall conflict is:
    //   (= a b) AND not(= f(a) f(b)) AND (>= x 0) AND (<= x -1)
    // We prove empty by combining EUF and LRA sub-derivations.

    let s0 = dag.add_step(SmtProofStep::Assume(eq_ab)); // {eq_ab}
    let _s1 = dag.add_step(SmtProofStep::Assume(not_eq_fa_fb)); // {not_eq_fa_fb}
    let s2 = dag.add_step(SmtProofStep::Assume(ge_x_0)); // {ge_x_0}
    let s3 = dag.add_step(SmtProofStep::Assume(le_x_neg1)); // {le_x_neg1}

    // EUF congruent lemma: [not(= a b), (= f(a) f(b))]
    let s4 = dag.add_step(SmtProofStep::TheoryLemma {
        theory: SmtTheory::Euf,
        kind: TheoryLemmaDetail::EufCongruent,
        clause: vec![not_eq_ab, eq_fa_fb],
    });

    // LRA Farkas lemma: [not(>= x 0), not(<= x -1)]
    let s5 = dag.add_step(SmtProofStep::TheoryLemma {
        theory: SmtTheory::Lra,
        kind: TheoryLemmaDetail::LraFarkas {
            coefficients: vec![(1, 1), (1, 1)],
        },
        clause: vec![not_ge_x_0, not_le_x_neg1],
    });

    // Resolve s0 + s4 on eq_ab => {eq_fa_fb}
    let _s6 = dag.add_step(SmtProofStep::Resolution {
        clause: vec![eq_fa_fb],
        premises: vec![s0, s4],
        pivot: Some(eq_ab),
    });

    // Resolve s1 + s6 on eq_fa_fb => {} (EUF empty clause)
    // Wait, s1 has not_eq_fa_fb, s6 has eq_fa_fb. Resolving gives empty.
    // But we still need to use the LRA part. In a real proof, if EITHER sub-problem
    // is UNSAT, the whole thing is UNSAT. The pipeline should handle this:
    // the terminal step derives empty.
    //
    // However, the LRA sub-proof also needs to terminate. Let's chain both:
    // We need the LAST step to be the terminal empty clause.

    // EUF sub-derivation: resolve to get EUF contradiction
    // s7 will resolve but we need the final step to be empty.
    // Let's just have s7 be the final resolution:

    // Actually, let me restructure. We can derive empty from the EUF path,
    // and separately from the LRA path, and use chain resolution.
    // OR just have the LRA path derive empty last.

    // Simpler: resolve EUF to empty, then use LRA + LRA to derive empty again,
    // and we just check the last derived clause is empty.
    // Any step deriving empty makes the proof valid.

    // Let me just make the LRA empty clause be the LAST step:

    // s6: resolve s0 + s4 on eq_ab => {eq_fa_fb}
    // Already defined above (s6).

    // s7: resolve s2 + s5 on ge_x_0 => {not_le_x_neg1}
    let s7 = dag.add_step(SmtProofStep::Resolution {
        clause: vec![not_le_x_neg1],
        premises: vec![s2, s5],
        pivot: Some(ge_x_0),
    });

    // s8: resolve s3 + s7 on le_x_neg1 => []
    dag.add_step(SmtProofStep::Resolution {
        clause: vec![],
        premises: vec![s3, s7],
        pivot: Some(le_x_neg1),
    });

    let result = verify_smt_proof(&dag, VerifyMode::Strict);
    assert!(
        result.valid,
        "Mixed EUF+LRA proof should be valid: {:?}",
        result.first_error
    );
    assert!(result.stats.is_fully_verified());

    // Both theory lemma types should be counted.
    assert_eq!(
        result.stats.theory_lemma_counts.get(&SmtTheory::Euf),
        Some(&1),
    );
    assert_eq!(
        result.stats.theory_lemma_counts.get(&SmtTheory::Lra),
        Some(&1),
    );
}

#[test]
fn test_mixed_euf_lia_resolution_combining_lemmas() {
    // Proof using EUF transitivity AND LIA bound conflict, both in the same DAG.
    // Problem: a = b, b = c, a != c, x >= 1, x <= -1
    //
    // EUF sub-proof: a = b, b = c => a = c  (contradicts a != c)
    // LIA sub-proof: x >= 1, x <= -1 is UNSAT
    //
    // Proof DAG with terminal empty clause from LIA path (last step).

    let mut dag = SmtProofDag::new();

    // EUF terms
    let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Int));
    let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Int));
    let c = dag.add_term(SmtTerm::Var("c".to_string(), SmtSort::Int));
    let eq_ab = make_eq(&mut dag, a, b);
    let eq_bc = make_eq(&mut dag, b, c);
    let eq_ac = make_eq(&mut dag, a, c);
    let not_eq_ab = dag.add_term(SmtTerm::Not(eq_ab));
    let not_eq_bc = dag.add_term(SmtTerm::Not(eq_bc));
    let not_eq_ac = dag.add_term(SmtTerm::Not(eq_ac));

    // LIA terms
    let x = dag.add_term(SmtTerm::Var("x".to_string(), SmtSort::Int));
    let one = dag.add_term(SmtTerm::Int(1));
    let neg_one = dag.add_term(SmtTerm::Int(-1));
    let ge_x_1 = add_binop(&mut dag, ">=", x, one);
    let le_x_neg1 = add_binop(&mut dag, "<=", x, neg_one);
    let not_ge_x_1 = dag.add_term(SmtTerm::Not(ge_x_1));
    let not_le_x_neg1 = dag.add_term(SmtTerm::Not(le_x_neg1));

    // Assumptions
    let s0 = dag.add_step(SmtProofStep::Assume(eq_ab));
    let s1 = dag.add_step(SmtProofStep::Assume(eq_bc));
    let s2 = dag.add_step(SmtProofStep::Assume(not_eq_ac));
    let s3 = dag.add_step(SmtProofStep::Assume(ge_x_1));
    let s4 = dag.add_step(SmtProofStep::Assume(le_x_neg1));

    // EUF transitive: [not(= a b), not(= b c), (= a c)]
    let s5 = dag.add_step(SmtProofStep::TheoryLemma {
        theory: SmtTheory::Euf,
        kind: TheoryLemmaDetail::EufTransitive,
        clause: vec![not_eq_ab, not_eq_bc, eq_ac],
    });

    // LIA lemma: [not(>= x 1), not(<= x -1)]
    let s6 = dag.add_step(SmtProofStep::TheoryLemma {
        theory: SmtTheory::Lia,
        kind: TheoryLemmaDetail::LiaGeneric {
            annotation: LiaDetail::FarkasOnly,
            coefficients: Some(vec![1, 1]),
        },
        clause: vec![not_ge_x_1, not_le_x_neg1],
    });

    // EUF resolution chain
    let s7 = dag.add_step(SmtProofStep::Resolution {
        clause: vec![not_eq_bc, eq_ac],
        premises: vec![s0, s5],
        pivot: Some(eq_ab),
    });
    let s8 = dag.add_step(SmtProofStep::Resolution {
        clause: vec![eq_ac],
        premises: vec![s1, s7],
        pivot: Some(eq_bc),
    });
    // EUF empty (not the terminal step):
    let _s9 = dag.add_step(SmtProofStep::Resolution {
        clause: vec![],
        premises: vec![s2, s8],
        pivot: Some(eq_ac),
    });

    // LIA resolution chain (terminal)
    let s10 = dag.add_step(SmtProofStep::Resolution {
        clause: vec![not_le_x_neg1],
        premises: vec![s3, s6],
        pivot: Some(ge_x_1),
    });
    dag.add_step(SmtProofStep::Resolution {
        clause: vec![],
        premises: vec![s4, s10],
        pivot: Some(le_x_neg1),
    });

    let result = verify_smt_proof(&dag, VerifyMode::Strict);
    assert!(
        result.valid,
        "Mixed EUF+LIA proof should be valid: {:?}",
        result.first_error
    );
    assert!(result.stats.is_fully_verified());
    assert_eq!(
        result.stats.theory_lemma_counts.get(&SmtTheory::Euf),
        Some(&1),
    );
    assert_eq!(
        result.stats.theory_lemma_counts.get(&SmtTheory::Lia),
        Some(&1),
    );
}

// ═════════════════════════════════════════════════════════════════════════
// 5. Invalid Proof Tests
// ═════════════════════════════════════════════════════════════════════════

#[test]
fn test_invalid_proof_no_empty_clause() {
    // A "proof" that never derives the empty clause should be rejected.
    let mut dag = SmtProofDag::new();
    let p = dag.add_term(SmtTerm::Var("p".to_string(), SmtSort::Bool));
    let q = dag.add_term(SmtTerm::Var("q".to_string(), SmtSort::Bool));

    dag.add_step(SmtProofStep::Assume(p));
    dag.add_step(SmtProofStep::Assume(q));
    // No resolution to empty.

    let result = verify_smt_proof(&dag, VerifyMode::Permissive);
    assert!(
        !result.valid,
        "proof without empty clause should be invalid"
    );
    assert!(matches!(
        result.first_error,
        Some(SmtVerifyError::FinalClauseNotEmpty { .. })
    ));
}

#[test]
fn test_invalid_lra_farkas_wrong_coefficients() {
    // An LRA Farkas lemma with wrong coefficients should fail verification.
    // Conflict: x >= 0 AND x <= -1 (correct Farkas: 1,1)
    // We'll provide wrong coefficients (1,0) which won't yield a contradiction.

    let mut dag = SmtProofDag::new();
    let x = dag.add_term(SmtTerm::Var("x".to_string(), SmtSort::Real));
    let zero = dag.add_term(SmtTerm::Int(0));
    let neg_one = dag.add_term(SmtTerm::Int(-1));

    let ge_x_0 = add_binop(&mut dag, ">=", x, zero);
    let le_x_neg1 = add_binop(&mut dag, "<=", x, neg_one);
    let not_ge_x_0 = dag.add_term(SmtTerm::Not(ge_x_0));
    let not_le_x_neg1 = dag.add_term(SmtTerm::Not(le_x_neg1));

    let s0 = dag.add_step(SmtProofStep::Assume(ge_x_0));
    let s1 = dag.add_step(SmtProofStep::Assume(le_x_neg1));

    // Wrong coefficients: (1,0) ignores the second inequality.
    let s2 = dag.add_step(SmtProofStep::TheoryLemma {
        theory: SmtTheory::Lra,
        kind: TheoryLemmaDetail::LraFarkas {
            coefficients: vec![(1, 1), (0, 1)],
        },
        clause: vec![not_ge_x_0, not_le_x_neg1],
    });

    let s3 = dag.add_step(SmtProofStep::Resolution {
        clause: vec![not_le_x_neg1],
        premises: vec![s0, s2],
        pivot: Some(ge_x_0),
    });

    dag.add_step(SmtProofStep::Resolution {
        clause: vec![],
        premises: vec![s1, s3],
        pivot: Some(le_x_neg1),
    });

    let result = verify_smt_proof(&dag, VerifyMode::Strict);
    // The LRA lemma should fail (Trusted), so strict mode rejects.
    assert!(
        !result.valid,
        "LRA proof with wrong Farkas coefficients should be invalid in strict mode"
    );

    // In permissive mode, it should still accept (Trusted step is allowed).
    let result_permissive = verify_smt_proof(&dag, VerifyMode::Permissive);
    assert!(
        result_permissive.valid,
        "LRA proof with wrong coefficients should be accepted in permissive mode (trusted)"
    );
    assert!(!result_permissive.stats.is_fully_verified());
    assert!(result_permissive.stats.trusted > 0);
}

#[test]
fn test_invalid_resolution_wrong_pivot() {
    // A resolution step claiming the wrong result should be rejected.
    // Premises: {p}, {not(p)} => resolution should give {}, but we claim {q}.

    let mut dag = SmtProofDag::new();
    let p = dag.add_term(SmtTerm::Var("p".to_string(), SmtSort::Bool));
    let q = dag.add_term(SmtTerm::Var("q".to_string(), SmtSort::Bool));
    let not_p = dag.add_term(SmtTerm::Not(p));

    let s0 = dag.add_step(SmtProofStep::Assume(p));
    let s1 = dag.add_step(SmtProofStep::Assume(not_p));

    // Tampered resolution: claim result is {q} instead of {}.
    dag.add_step(SmtProofStep::Resolution {
        clause: vec![q],
        premises: vec![s0, s1],
        pivot: Some(p),
    });

    let result = verify_smt_proof(&dag, VerifyMode::Permissive);
    // The resolution result is wrong AND the terminal clause is not empty.
    assert!(
        !result.valid,
        "resolution with wrong result should be invalid"
    );
}

#[test]
fn test_invalid_resolution_fabricated_literal() {
    // A resolution step that introduces a literal not in any premise is invalid.
    // Premises: {p, q}, {not(p)} => correct result: {q}
    // We claim {q, r} where r was never in any premise.

    let mut dag = SmtProofDag::new();
    let p = dag.add_term(SmtTerm::Var("p".to_string(), SmtSort::Bool));
    let q = dag.add_term(SmtTerm::Var("q".to_string(), SmtSort::Bool));
    let _r = dag.add_term(SmtTerm::Var("r".to_string(), SmtSort::Bool));
    let not_p = dag.add_term(SmtTerm::Not(p));

    let _s0 = dag.add_step(SmtProofStep::Assume(p));
    let s0b = dag.add_step(SmtProofStep::TheoryLemma {
        theory: SmtTheory::Core,
        kind: TheoryLemmaDetail::Generic,
        clause: vec![p, q],
    });
    let s1 = dag.add_step(SmtProofStep::Assume(not_p));

    // Claim result is {} via resolution of {p,q} and {not(p)}, but result
    // should be {q}, not empty.
    dag.add_step(SmtProofStep::Resolution {
        clause: vec![],
        premises: vec![s0b, s1],
        pivot: Some(p),
    });

    let _result = verify_smt_proof(&dag, VerifyMode::Permissive);
    // Resolution result mismatch: resolvent should be {q}, not {}.
    // The step should be marked as Trusted (mismatch).
    // The terminal clause IS empty, but it was derived incorrectly.
    // However, the pipeline checks resolution correctness per-step and
    // the result.valid depends on whether the step is trusted + mode.
    // In permissive mode, the trusted resolution is allowed but the
    // core Generic theory lemma also generates a Trust step.
    // Overall the proof "passes" in permissive mode because it has an empty
    // terminal clause and permissive mode accepts trust steps.
    //
    // In strict mode, it should fail.
    let result_strict = verify_smt_proof(&dag, VerifyMode::Strict);
    assert!(
        !result_strict.valid,
        "fabricated resolution should fail in strict mode"
    );
}

#[test]
fn test_invalid_euf_congruent_wrong_function_symbols() {
    // EUF congruent lemma where the function symbols don't match.
    // Claim: not(= a b) => (= f(a) g(b)) — this is WRONG because f != g.

    let mut dag = SmtProofDag::new();
    let a = dag.add_term(SmtTerm::Var("a".to_string(), SmtSort::Int));
    let b = dag.add_term(SmtTerm::Var("b".to_string(), SmtSort::Int));
    let fa = make_app1(&mut dag, "f", a);
    let gb = make_app1(&mut dag, "g", b);

    let eq_ab = make_eq(&mut dag, a, b);
    let eq_fa_gb = make_eq(&mut dag, fa, gb);
    let not_eq_ab = dag.add_term(SmtTerm::Not(eq_ab));
    let not_eq_fa_gb = dag.add_term(SmtTerm::Not(eq_fa_gb));

    let s0 = dag.add_step(SmtProofStep::Assume(eq_ab));
    let s1 = dag.add_step(SmtProofStep::Assume(not_eq_fa_gb));

    // Bad EUF congruent: claims f(a) = g(b) from a = b, but f != g.
    let s2 = dag.add_step(SmtProofStep::TheoryLemma {
        theory: SmtTheory::Euf,
        kind: TheoryLemmaDetail::EufCongruent,
        clause: vec![not_eq_ab, eq_fa_gb],
    });

    let s3 = dag.add_step(SmtProofStep::Resolution {
        clause: vec![eq_fa_gb],
        premises: vec![s0, s2],
        pivot: Some(eq_ab),
    });

    dag.add_step(SmtProofStep::Resolution {
        clause: vec![],
        premises: vec![s1, s3],
        pivot: Some(eq_fa_gb),
    });

    // In strict mode, the bad EUF congruent step should be Trusted (rejected).
    let result = verify_smt_proof(&dag, VerifyMode::Strict);
    assert!(
        !result.valid,
        "EUF congruent with wrong function symbols should be invalid in strict mode"
    );
}

#[test]
fn test_invalid_lra_negative_farkas_coefficient() {
    // Farkas coefficients must be non-negative. A negative coefficient should
    // cause the LRA checker to reject the lemma.

    let mut dag = SmtProofDag::new();
    let x = dag.add_term(SmtTerm::Var("x".to_string(), SmtSort::Real));
    let zero = dag.add_term(SmtTerm::Int(0));
    let neg_one = dag.add_term(SmtTerm::Int(-1));

    let ge_x_0 = add_binop(&mut dag, ">=", x, zero);
    let le_x_neg1 = add_binop(&mut dag, "<=", x, neg_one);
    let not_ge_x_0 = dag.add_term(SmtTerm::Not(ge_x_0));
    let not_le_x_neg1 = dag.add_term(SmtTerm::Not(le_x_neg1));

    let s0 = dag.add_step(SmtProofStep::Assume(ge_x_0));
    let s1 = dag.add_step(SmtProofStep::Assume(le_x_neg1));

    // Negative Farkas coefficient: (-1, 1)
    let s2 = dag.add_step(SmtProofStep::TheoryLemma {
        theory: SmtTheory::Lra,
        kind: TheoryLemmaDetail::LraFarkas {
            coefficients: vec![(-1, 1), (1, 1)],
        },
        clause: vec![not_ge_x_0, not_le_x_neg1],
    });

    let s3 = dag.add_step(SmtProofStep::Resolution {
        clause: vec![not_le_x_neg1],
        premises: vec![s0, s2],
        pivot: Some(ge_x_0),
    });

    dag.add_step(SmtProofStep::Resolution {
        clause: vec![],
        premises: vec![s1, s3],
        pivot: Some(le_x_neg1),
    });

    let result = verify_smt_proof(&dag, VerifyMode::Strict);
    assert!(
        !result.valid,
        "negative Farkas coefficient should be rejected in strict mode"
    );
}

#[test]
fn test_invalid_lia_wrong_coefficients() {
    // LIA Farkas with coefficients that don't yield a contradiction.
    // Conflict: x >= 1 AND x <= -1
    // Correct coefficients: (1, 1) => sum = 2 > 0 => contradiction.
    // Wrong coefficients: (1, 0) => sum = 1*(- x + 1) + 0*(...) = -x + 1 <= 0
    //   which is NOT a contradiction (variable doesn't cancel).

    let mut dag = SmtProofDag::new();
    let x = dag.add_term(SmtTerm::Var("x".to_string(), SmtSort::Int));
    let one = dag.add_term(SmtTerm::Int(1));
    let neg_one = dag.add_term(SmtTerm::Int(-1));

    let ge_x_1 = add_binop(&mut dag, ">=", x, one);
    let le_x_neg1 = add_binop(&mut dag, "<=", x, neg_one);
    let not_ge_x_1 = dag.add_term(SmtTerm::Not(ge_x_1));
    let not_le_x_neg1 = dag.add_term(SmtTerm::Not(le_x_neg1));

    let s0 = dag.add_step(SmtProofStep::Assume(ge_x_1));
    let s1 = dag.add_step(SmtProofStep::Assume(le_x_neg1));

    let s2 = dag.add_step(SmtProofStep::TheoryLemma {
        theory: SmtTheory::Lia,
        kind: TheoryLemmaDetail::LiaGeneric {
            annotation: LiaDetail::FarkasOnly,
            coefficients: Some(vec![1, 0]), // Wrong: ignores second inequality
        },
        clause: vec![not_ge_x_1, not_le_x_neg1],
    });

    let s3 = dag.add_step(SmtProofStep::Resolution {
        clause: vec![not_le_x_neg1],
        premises: vec![s0, s2],
        pivot: Some(ge_x_1),
    });

    dag.add_step(SmtProofStep::Resolution {
        clause: vec![],
        premises: vec![s1, s3],
        pivot: Some(le_x_neg1),
    });

    let result = verify_smt_proof(&dag, VerifyMode::Strict);
    assert!(
        !result.valid,
        "LIA with wrong coefficients should be invalid in strict mode"
    );
}

#[test]
fn test_invalid_structural_premise_forward_reference() {
    // A proof where step 0 references step 1 (forward reference) should fail
    // structural validation.

    let mut dag = SmtProofDag::new();
    let p = dag.add_term(SmtTerm::Var("p".to_string(), SmtSort::Bool));

    // Step 0 references step 1 as a premise (forward reference).
    dag.add_step(SmtProofStep::Resolution {
        clause: vec![],
        premises: vec![SmtStepId(1)],
        pivot: None,
    });
    dag.add_step(SmtProofStep::Assume(p));

    let result = verify_smt_proof(&dag, VerifyMode::Permissive);
    assert!(
        !result.valid,
        "forward reference should fail structural validation"
    );
    assert!(matches!(
        result.first_error,
        Some(SmtVerifyError::NonPriorPremise { .. })
    ));
}

#[test]
fn test_invalid_structural_out_of_range_premise() {
    // A proof with a premise reference beyond the DAG size.

    let mut dag = SmtProofDag::new();
    let p = dag.add_term(SmtTerm::Var("p".to_string(), SmtSort::Bool));

    dag.add_step(SmtProofStep::Assume(p));
    dag.add_step(SmtProofStep::Resolution {
        clause: vec![],
        premises: vec![SmtStepId(99)],
        pivot: None,
    });

    let result = verify_smt_proof(&dag, VerifyMode::Permissive);
    assert!(!result.valid, "out-of-range premise should fail");
    assert!(matches!(
        result.first_error,
        Some(SmtVerifyError::MissingPremise { .. })
    ));
}

// ═════════════════════════════════════════════════════════════════════════
// 6. Verification Stats / Coverage Tests
// ═════════════════════════════════════════════════════════════════════════

#[test]
fn test_stats_verification_coverage_fully_verified() {
    // A simple proof where every step is kernel-verified or axiomatic.
    let mut dag = SmtProofDag::new();
    let p = dag.add_term(SmtTerm::Var("p".to_string(), SmtSort::Bool));
    let not_p = dag.add_term(SmtTerm::Not(p));

    let s0 = dag.add_step(SmtProofStep::Assume(p));
    let s1 = dag.add_step(SmtProofStep::Assume(not_p));
    dag.add_step(SmtProofStep::Resolution {
        clause: vec![],
        premises: vec![s0, s1],
        pivot: Some(p),
    });

    let result = verify_smt_proof(&dag, VerifyMode::Permissive);
    assert!(result.valid);
    assert!((result.stats.verification_coverage() - 1.0).abs() < f64::EPSILON);
    assert!(result.stats.is_fully_verified());
    assert_eq!(result.stats.total_steps, 3);
    assert_eq!(result.stats.axiomatic, 2);
    assert_eq!(result.stats.kernel_verified, 1);
    assert_eq!(result.stats.structurally_accepted, 0);
    assert_eq!(result.stats.trusted, 0);
}

#[test]
fn test_stats_mixed_trust_levels() {
    // A proof with a Generic theory lemma (Trusted) alongside verified steps.
    let mut dag = SmtProofDag::new();
    let p = dag.add_term(SmtTerm::Var("p".to_string(), SmtSort::Bool));
    let not_p = dag.add_term(SmtTerm::Not(p));

    let s0 = dag.add_step(SmtProofStep::Assume(p));
    let s1 = dag.add_step(SmtProofStep::TheoryLemma {
        theory: SmtTheory::Core,
        kind: TheoryLemmaDetail::Generic,
        clause: vec![not_p],
    });
    dag.add_step(SmtProofStep::Resolution {
        clause: vec![],
        premises: vec![s0, s1],
        pivot: Some(p),
    });

    let result = verify_smt_proof(&dag, VerifyMode::Permissive);
    assert!(result.valid);
    assert!(!result.stats.is_fully_verified());
    assert_eq!(result.stats.trusted, 1);
    assert!(result.stats.verification_coverage() < 1.0);
}

#[test]
fn test_permissive_mode_accepts_trusted_steps() {
    // In permissive mode, trusted steps are allowed.
    let mut dag = SmtProofDag::new();
    let p = dag.add_term(SmtTerm::Var("p".to_string(), SmtSort::Bool));
    let not_p = dag.add_term(SmtTerm::Not(p));

    let s0 = dag.add_step(SmtProofStep::Assume(p));
    let s1 = dag.add_step(SmtProofStep::TheoryLemma {
        theory: SmtTheory::Core,
        kind: TheoryLemmaDetail::Generic,
        clause: vec![not_p],
    });
    dag.add_step(SmtProofStep::Resolution {
        clause: vec![],
        premises: vec![s0, s1],
        pivot: Some(p),
    });

    let result_permissive = verify_smt_proof(&dag, VerifyMode::Permissive);
    assert!(result_permissive.valid);

    let result_strict = verify_smt_proof(&dag, VerifyMode::Strict);
    assert!(!result_strict.valid);
    assert!(matches!(
        result_strict.first_error,
        Some(SmtVerifyError::TrustStep { .. })
    ));
}
