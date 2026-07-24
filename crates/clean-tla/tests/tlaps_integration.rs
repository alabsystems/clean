// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! TLAPS Obligation Integration Tests
//!
//! Copyright 2026 Andrew Yates
//! Licensed under Apache-2.0

use clean_tla::obligation::TlaDeclare;
use clean_tla::tactic::prove_tla_obligation;
use clean_tla::{TlaFormula, TlaHypothesis, TlaObligation};

#[test]
fn test_tlaps_obligation_always_true_with_hypotheses_and_declares() {
    // Model a TLAPS-style sequent with both declarations and hypotheses:
    //   CONSTANT C, VARIABLE x, h1: TRUE ⊢ []TRUE
    let obligation = TlaObligation {
        module: "TLAPSIntegration".to_string(),
        line: Some(1),
        declares: vec![
            TlaDeclare::Constant {
                name: "C".to_string(),
                arity: 0,
            },
            TlaDeclare::Variable {
                name: "x".to_string(),
            },
        ],
        hypotheses: vec![TlaHypothesis {
            name: "h1".to_string(),
            formula: TlaFormula::True,
        }],
        goal: TlaFormula::Always(Box::new(TlaFormula::True)),
        tactic_hint: None,
    };

    // TLAPS integration expects obligations to arrive serialized.
    let encoded = serde_json::to_string(&obligation).expect("serialize obligation");
    let decoded: TlaObligation = serde_json::from_str(&encoded).expect("deserialize obligation");

    let result = prove_tla_obligation(&decoded);
    assert!(result.proved, "expected proof success, got: {result:?}");
}

#[test]
fn test_tlaps_obligation_eventually_true_with_multiple_hypotheses() {
    // Model a TLAPS-style sequent:
    //   h1: TRUE, h2: TRUE ⊢ <>TRUE
    let obligation = TlaObligation {
        module: "TLAPSIntegration".to_string(),
        line: Some(2),
        declares: vec![],
        hypotheses: vec![
            TlaHypothesis {
                name: "h1".to_string(),
                formula: TlaFormula::True,
            },
            TlaHypothesis {
                name: "h2".to_string(),
                formula: TlaFormula::True,
            },
        ],
        goal: TlaFormula::Eventually(Box::new(TlaFormula::True)),
        tactic_hint: None,
    };

    let encoded = serde_json::to_string(&obligation).expect("serialize obligation");
    let decoded: TlaObligation = serde_json::from_str(&encoded).expect("deserialize obligation");

    let result = prove_tla_obligation(&decoded);
    assert!(result.proved, "expected proof success, got: {result:?}");
}

#[test]
fn test_tlaps_obligation_unprovable_always_false() {
    // □FALSE is unprovable - the system should return proved: false
    let obligation = TlaObligation {
        module: "TLAPSIntegration".to_string(),
        line: Some(3),
        declares: vec![],
        hypotheses: vec![],
        goal: TlaFormula::Always(Box::new(TlaFormula::False)),
        tactic_hint: None,
    };

    let result = prove_tla_obligation(&obligation);
    assert!(
        !result.proved,
        "expected proof failure for □FALSE, got: {result:?}"
    );
    assert!(
        result.certificate.is_none(),
        "unprovable goal should not have certificate"
    );
}

#[test]
fn test_tlaps_obligation_eventually_false_unprovable() {
    // ◇FALSE is unprovable - the system should return proved: false
    let obligation = TlaObligation {
        module: "TLAPSIntegration".to_string(),
        line: Some(4),
        declares: vec![],
        hypotheses: vec![],
        goal: TlaFormula::Eventually(Box::new(TlaFormula::False)),
        tactic_hint: None,
    };

    let result = prove_tla_obligation(&obligation);
    assert!(
        !result.proved,
        "expected proof failure for ◇FALSE, got: {result:?}"
    );
}

#[test]
fn test_tlaps_obligation_minimal_empty_context() {
    // Minimal obligation: prove □TRUE with no declarations or hypotheses
    // Note: Plain TRUE without temporal wrapper goes through auto tactic
    // which doesn't have trivial TRUE handling yet - use □TRUE instead
    let obligation = TlaObligation {
        module: "Minimal".to_string(),
        line: None,
        declares: vec![],
        hypotheses: vec![],
        goal: TlaFormula::Always(Box::new(TlaFormula::True)),
        tactic_hint: None,
    };

    let result = prove_tla_obligation(&obligation);
    assert!(
        result.proved,
        "□TRUE should be provable with empty context, got: {result:?}"
    );
}

#[test]
fn test_tlaps_obligation_json_roundtrip_complex() {
    // Complex obligation with all fields - verify JSON serialization preserves structure
    // Note: Using □TRUE goal which is known provable by temporal tactic
    let obligation = TlaObligation {
        module: "ComplexRoundtrip".to_string(),
        line: Some(42),
        declares: vec![
            TlaDeclare::Constant {
                name: "N".to_string(),
                arity: 2,
            },
            TlaDeclare::Variable {
                name: "state".to_string(),
            },
        ],
        hypotheses: vec![
            TlaHypothesis {
                name: "h1".to_string(),
                formula: TlaFormula::Always(Box::new(TlaFormula::True)),
            },
            TlaHypothesis {
                name: "h2".to_string(),
                formula: TlaFormula::Eventually(Box::new(TlaFormula::True)),
            },
        ],
        goal: TlaFormula::Always(Box::new(TlaFormula::True)),
        tactic_hint: Some("temporal".to_string()),
    };

    // Verify JSON roundtrip
    let json = serde_json::to_string_pretty(&obligation).expect("serialize");
    let decoded: TlaObligation = serde_json::from_str(&json).expect("deserialize");

    assert_eq!(decoded.module, "ComplexRoundtrip");
    assert_eq!(decoded.line, Some(42));
    assert_eq!(decoded.declares.len(), 2);
    assert_eq!(decoded.hypotheses.len(), 2);
    assert_eq!(decoded.tactic_hint.as_deref(), Some("temporal"));

    // Prove it
    let result = prove_tla_obligation(&decoded);
    assert!(
        result.proved,
        "TRUE ~> TRUE should be provable, got: {result:?}"
    );
}

#[test]
fn test_tlaps_obligation_leads_to_reflexive() {
    // P ~> P should be provable by reflexivity
    let obligation = TlaObligation {
        module: "LeadsToReflexive".to_string(),
        line: Some(5),
        declares: vec![],
        hypotheses: vec![],
        goal: TlaFormula::LeadsTo(
            Box::new(TlaFormula::Expr(clean_tla::encoding::TlaExpr::Const(
                "P".to_string(),
            ))),
            Box::new(TlaFormula::Expr(clean_tla::encoding::TlaExpr::Const(
                "P".to_string(),
            ))),
        ),
        tactic_hint: None,
    };

    let result = prove_tla_obligation(&obligation);
    assert!(
        result.proved,
        "P ~> P should be provable by reflexivity, got: {result:?}"
    );
    let cert = result.certificate.as_deref().unwrap_or_default();
    assert!(
        cert.contains("leads_to_reflexivity"),
        "expected leads_to_reflexivity in certificate, got: {result:?}"
    );
}

#[test]
fn test_tlaps_obligation_leads_to_true_consequent() {
    // P ~> True should always be provable since ◇True ≡ True
    let obligation = TlaObligation {
        module: "LeadsToTrueConsequent".to_string(),
        line: Some(6),
        declares: vec![],
        hypotheses: vec![],
        goal: TlaFormula::LeadsTo(
            Box::new(TlaFormula::Expr(clean_tla::encoding::TlaExpr::Const(
                "P".to_string(),
            ))),
            Box::new(TlaFormula::True),
        ),
        tactic_hint: None,
    };

    let result = prove_tla_obligation(&obligation);
    assert!(
        result.proved,
        "P ~> True should be provable, got: {result:?}"
    );
}

#[test]
fn test_tlaps_obligation_leads_to_false_antecedent() {
    // False ~> Q is vacuously true
    let obligation = TlaObligation {
        module: "LeadsToFalseAntecedent".to_string(),
        line: Some(7),
        declares: vec![],
        hypotheses: vec![],
        goal: TlaFormula::LeadsTo(
            Box::new(TlaFormula::False),
            Box::new(TlaFormula::Expr(clean_tla::encoding::TlaExpr::Const(
                "Q".to_string(),
            ))),
        ),
        tactic_hint: None,
    };

    let result = prove_tla_obligation(&obligation);
    assert!(
        result.proved,
        "False ~> Q should be provable (vacuously true), got: {result:?}"
    );
}

#[test]
fn test_tlaps_obligation_leads_to_with_hypotheses() {
    // Test leads-to with hypotheses in context
    let obligation = TlaObligation {
        module: "LeadsToWithHyps".to_string(),
        line: Some(8),
        declares: vec![],
        hypotheses: vec![TlaHypothesis {
            name: "h1".to_string(),
            formula: TlaFormula::Always(Box::new(TlaFormula::True)),
        }],
        goal: TlaFormula::LeadsTo(Box::new(TlaFormula::True), Box::new(TlaFormula::True)),
        tactic_hint: Some("temporal".to_string()),
    };

    let result = prove_tla_obligation(&obligation);
    assert!(
        result.proved,
        "True ~> True with hypotheses should be provable, got: {result:?}"
    );
}

#[test]
fn test_tlaps_obligation_leads_to_nontrivial_unprovable() {
    // P ~> Q where P and Q are distinct and non-trivial should NOT be provable
    // (without additional hypotheses)
    let obligation = TlaObligation {
        module: "LeadsToNontrivial".to_string(),
        line: Some(9),
        declares: vec![],
        hypotheses: vec![],
        goal: TlaFormula::LeadsTo(
            Box::new(TlaFormula::Expr(clean_tla::encoding::TlaExpr::Const(
                "P".to_string(),
            ))),
            Box::new(TlaFormula::Expr(clean_tla::encoding::TlaExpr::Const(
                "Q".to_string(),
            ))),
        ),
        tactic_hint: None,
    };

    let result = prove_tla_obligation(&obligation);
    assert!(
        !result.proved,
        "P ~> Q (distinct, non-trivial) should NOT be provable without hypotheses, got: {result:?}"
    );
}

#[test]
fn test_tlaps_obligation_leads_to_lt_to_eq_without_fairness_is_not_proved() {
    // SOUNDNESS (corrected 2026-07-01): this obligation is
    // `x < MAX ~> x = MAX` with NO fairness hypothesis, NO next-state action,
    // and NO hypotheses at all. It is genuinely FALSE: a stuttering behaviour
    // that holds `x < MAX` forever satisfies the (empty) spec yet never reaches
    // `x = MAX`, so `x < MAX` does not lead to `x = MAX`.
    //
    // The prior version of this test asserted `proved == true` via a
    // `progress_measure` "bounded descent" pattern match — a confirmed
    // false-proof hole (see docs/SOUNDNESS_FINDINGS_CLEAN_TLA_2026-07.md). The
    // progress-measure rule is now fail-closed: without the action + fairness
    // to discharge the well-founded-progress obligation it must not certify
    // liveness. A genuine proof of this liveness requires the spec's fairness
    // assumption to be present in the obligation, which it is not here.
    use clean_tla::encoding::{TlaCmpOp, TlaExpr};

    let x_lt_max = TlaFormula::Expr(TlaExpr::Cmp(
        TlaCmpOp::Lt,
        Box::new(TlaExpr::Var("x".to_string())),
        Box::new(TlaExpr::Const("MAX".to_string())),
    ));
    let x_eq_max = TlaFormula::Eq(
        Box::new(TlaExpr::Var("x".to_string())),
        Box::new(TlaExpr::Const("MAX".to_string())),
    );

    let obligation = TlaObligation {
        module: "EnabledFairness".to_string(),
        line: Some(40),
        declares: vec![
            TlaDeclare::Constant {
                name: "MAX".to_string(),
                arity: 0,
            },
            TlaDeclare::Variable {
                name: "x".to_string(),
            },
        ],
        hypotheses: vec![],
        goal: TlaFormula::LeadsTo(Box::new(x_lt_max), Box::new(x_eq_max)),
        tactic_hint: Some("temporal".to_string()),
    };

    let result = prove_tla_obligation(&obligation);
    assert!(
        !result.proved,
        "SOUNDNESS: x < MAX ~> x = MAX without fairness must NOT be proved, got: {result:?}"
    );
}

#[test]
fn test_tlaps_obligation_leads_to_neq_to_eq_without_fairness_is_not_proved() {
    // SOUNDNESS (corrected 2026-07-01): `x ≠ MAX ~> x = MAX` with no fairness /
    // action / hypotheses is genuinely FALSE for the same reason as the `<`
    // variant above (stuttering keeps `x ≠ MAX` forever). The former assertion
    // of `proved == true` via a `distance`-method progress measure was a
    // false-proof; the progress-measure rule is now fail-closed.
    use clean_tla::encoding::TlaExpr;

    let x_eq_max = TlaFormula::Eq(
        Box::new(TlaExpr::Var("x".to_string())),
        Box::new(TlaExpr::Const("MAX".to_string())),
    );
    let x_neq_max = TlaFormula::Not(Box::new(x_eq_max.clone()));

    let obligation = TlaObligation {
        module: "EnabledFairness".to_string(),
        line: Some(40),
        declares: vec![
            TlaDeclare::Constant {
                name: "MAX".to_string(),
                arity: 0,
            },
            TlaDeclare::Variable {
                name: "x".to_string(),
            },
        ],
        hypotheses: vec![],
        goal: TlaFormula::LeadsTo(Box::new(x_neq_max), Box::new(x_eq_max)),
        tactic_hint: Some("temporal".to_string()),
    };

    let result = prove_tla_obligation(&obligation);
    assert!(
        !result.proved,
        "SOUNDNESS: x ≠ MAX ~> x = MAX without fairness must NOT be proved, got: {result:?}"
    );
}

// ================================================================
// Natural Number Induction Integration Tests
// ================================================================

#[test]
fn test_tlaps_obligation_nat_induction_trivial() {
    // ∀n ∈ Nat : TRUE should be provable
    // This tests that nat_induction tactic is selected for ForallIn over Nat
    let obligation = TlaObligation {
        module: "NatInductionTrivial".to_string(),
        line: Some(10),
        declares: vec![],
        hypotheses: vec![],
        goal: TlaFormula::ForallIn(
            "n".to_string(),
            Box::new(clean_tla::encoding::TlaExpr::Nat),
            Box::new(TlaFormula::True),
        ),
        tactic_hint: None,
    };

    let result = prove_tla_obligation(&obligation);
    // nat_induction should be tried
    assert!(
        result.tactics_tried.contains(&"nat_induction".to_string()),
        "nat_induction should be tried for ∀n ∈ Nat : TRUE, got: {:?}",
        result.tactics_tried
    );
}

#[test]
fn test_tlaps_obligation_nat_induction_with_tactic_hint() {
    // ∀n ∈ Nat : TRUE with explicit induction hint
    let obligation = TlaObligation {
        module: "NatInductionHint".to_string(),
        line: Some(11),
        declares: vec![],
        hypotheses: vec![],
        goal: TlaFormula::ForallIn(
            "n".to_string(),
            Box::new(clean_tla::encoding::TlaExpr::Nat),
            Box::new(TlaFormula::True),
        ),
        tactic_hint: Some("induction".to_string()),
    };

    let result = prove_tla_obligation(&obligation);
    assert!(
        result.tactics_tried.contains(&"nat_induction".to_string()),
        "nat_induction should be tried with induction hint"
    );
}

#[test]
fn test_tlaps_obligation_nat_induction_json_roundtrip() {
    // Verify Nat induction obligation serializes correctly
    let obligation = TlaObligation {
        module: "NatInductionRoundtrip".to_string(),
        line: Some(12),
        declares: vec![TlaDeclare::Constant {
            name: "P".to_string(),
            arity: 1, // P is a predicate on Nat
        }],
        hypotheses: vec![
            TlaHypothesis {
                name: "base".to_string(),
                formula: TlaFormula::True, // P(0) hypothesis
            },
            TlaHypothesis {
                name: "step".to_string(),
                formula: TlaFormula::True, // ∀n. P(n) → P(n+1) hypothesis
            },
        ],
        goal: TlaFormula::ForallIn(
            "n".to_string(),
            Box::new(clean_tla::encoding::TlaExpr::Nat),
            Box::new(TlaFormula::True), // P(n) simplified to TRUE for this test
        ),
        tactic_hint: Some("induction".to_string()),
    };

    // JSON roundtrip
    let json = serde_json::to_string_pretty(&obligation).expect("serialize");
    let decoded: TlaObligation = serde_json::from_str(&json).expect("deserialize");

    assert_eq!(decoded.module, "NatInductionRoundtrip");
    assert_eq!(decoded.declares.len(), 1);
    assert_eq!(decoded.hypotheses.len(), 2);

    // Goal should be ForallIn over Nat
    if let TlaFormula::ForallIn(var, set, _body) = &decoded.goal {
        assert_eq!(var, "n");
        assert!(matches!(set.as_ref(), clean_tla::encoding::TlaExpr::Nat));
    } else {
        panic!("Expected ForallIn goal");
    }
}

// ================================================================
// Sum Formula Test (matches sum_formula.json benchmark)
// ================================================================

#[test]
fn test_sum_formula_with_hypotheses() {
    use clean_tla::encoding::{TlaArithOp, TlaExpr};

    // This test mirrors benchmarks/tlaps/nat_induction/sum_formula.json
    //
    // declares: constant sum (arity 1)
    // hypotheses:
    //   sum_def_0: sum(0) = 0
    //   sum_def_succ: ∀k ∈ Nat : sum(k+1) = sum(k) + (k+1)
    // goal: ∀n ∈ Nat : sum(n) = n * (n+1) / 2

    let obligation = TlaObligation {
        module: "SumFormulaTest".to_string(),
        line: Some(1),
        declares: vec![TlaDeclare::Constant {
            name: "sum".to_string(),
            arity: 1,
        }],
        hypotheses: vec![
            // sum_def_0: sum(0) = 0
            TlaHypothesis {
                name: "sum_def_0".to_string(),
                formula: TlaFormula::Eq(
                    Box::new(TlaExpr::OpApply("sum".to_string(), vec![TlaExpr::Int(0)])),
                    Box::new(TlaExpr::Int(0)),
                ),
            },
            // sum_def_succ: ∀k ∈ Nat : sum(k+1) = sum(k) + (k+1)
            TlaHypothesis {
                name: "sum_def_succ".to_string(),
                formula: TlaFormula::ForallIn(
                    "k".to_string(),
                    Box::new(TlaExpr::Nat),
                    Box::new(TlaFormula::Eq(
                        Box::new(TlaExpr::OpApply(
                            "sum".to_string(),
                            vec![TlaExpr::Arith(
                                TlaArithOp::Add,
                                Box::new(TlaExpr::Var("k".to_string())),
                                Box::new(TlaExpr::Int(1)),
                            )],
                        )),
                        Box::new(TlaExpr::Arith(
                            TlaArithOp::Add,
                            Box::new(TlaExpr::OpApply(
                                "sum".to_string(),
                                vec![TlaExpr::Var("k".to_string())],
                            )),
                            Box::new(TlaExpr::Arith(
                                TlaArithOp::Add,
                                Box::new(TlaExpr::Var("k".to_string())),
                                Box::new(TlaExpr::Int(1)),
                            )),
                        )),
                    )),
                ),
            },
        ],
        // goal: ∀n ∈ Nat : sum(n) = n * (n+1) / 2
        goal: TlaFormula::ForallIn(
            "n".to_string(),
            Box::new(TlaExpr::Nat),
            Box::new(TlaFormula::Eq(
                Box::new(TlaExpr::OpApply(
                    "sum".to_string(),
                    vec![TlaExpr::Var("n".to_string())],
                )),
                Box::new(TlaExpr::Arith(
                    TlaArithOp::Div,
                    Box::new(TlaExpr::Arith(
                        TlaArithOp::Mul,
                        Box::new(TlaExpr::Var("n".to_string())),
                        Box::new(TlaExpr::Arith(
                            TlaArithOp::Add,
                            Box::new(TlaExpr::Var("n".to_string())),
                            Box::new(TlaExpr::Int(1)),
                        )),
                    )),
                    Box::new(TlaExpr::Int(2)),
                )),
            )),
        ),
        tactic_hint: Some("induction".to_string()),
    };

    // Use traced version to see what's happening
    let result = clean_tla::tactic::prove_tla_obligation_traced(&obligation);

    // Debug output
    eprintln!("=== Sum Formula Test Results ===");
    eprintln!("Tactics tried: {:?}", result.tactics_tried);
    eprintln!("Proved: {}", result.proved);
    if let Some(ref err) = result.error {
        eprintln!("Error: {}", err);
    }
    if let Some(ref cert) = result.certificate {
        eprintln!("Certificate: {}", cert);
    }

    // nat_induction should be tried
    assert!(
        result.tactics_tried.contains(&"nat_induction".to_string()),
        "nat_induction should be tried for sum_formula"
    );

    // This should prove the base case at least
    // For now, document whether it succeeds or fails
    if !result.proved {
        eprintln!(
            "NOTE: sum_formula not fully proved - this is expected until step case is implemented"
        );
    }
}

// ================================================================
// Arithmetic Property Integration Tests
// Tests based on common NaturalsInduction.tla theorems
// ================================================================

#[test]
fn test_arith_n_plus_zero() {
    use clean_tla::encoding::{TlaArithOp, TlaExpr};

    // ∀n ∈ Nat : n + 0 = n
    // This is Nat.add_zero in Lean/Mathlib
    let obligation = TlaObligation {
        module: "NaturalsInduction".to_string(),
        line: Some(100),
        declares: vec![],
        hypotheses: vec![],
        goal: TlaFormula::ForallIn(
            "n".to_string(),
            Box::new(TlaExpr::Nat),
            Box::new(TlaFormula::Eq(
                Box::new(TlaExpr::Arith(
                    TlaArithOp::Add,
                    Box::new(TlaExpr::Var("n".to_string())),
                    Box::new(TlaExpr::Int(0)),
                )),
                Box::new(TlaExpr::Var("n".to_string())),
            )),
        ),
        tactic_hint: Some("induction".to_string()),
    };

    let result = prove_tla_obligation(&obligation);

    // nat_induction should be tried
    assert!(
        result.tactics_tried.contains(&"nat_induction".to_string()),
        "nat_induction should be tried for n + 0 = n, got: {:?}",
        result.tactics_tried
    );
}

#[test]
fn test_arith_zero_plus_n() {
    use clean_tla::encoding::{TlaArithOp, TlaExpr};

    // ∀n ∈ Nat : 0 + n = n
    // This is Nat.zero_add in Lean/Mathlib
    let obligation = TlaObligation {
        module: "NaturalsInduction".to_string(),
        line: Some(101),
        declares: vec![],
        hypotheses: vec![],
        goal: TlaFormula::ForallIn(
            "n".to_string(),
            Box::new(TlaExpr::Nat),
            Box::new(TlaFormula::Eq(
                Box::new(TlaExpr::Arith(
                    TlaArithOp::Add,
                    Box::new(TlaExpr::Int(0)),
                    Box::new(TlaExpr::Var("n".to_string())),
                )),
                Box::new(TlaExpr::Var("n".to_string())),
            )),
        ),
        tactic_hint: Some("induction".to_string()),
    };

    let result = prove_tla_obligation(&obligation);

    assert!(
        result.tactics_tried.contains(&"nat_induction".to_string()),
        "nat_induction should be tried for 0 + n = n, got: {:?}",
        result.tactics_tried
    );
}

#[test]
fn test_arith_n_mul_one() {
    use clean_tla::encoding::{TlaArithOp, TlaExpr};

    // ∀n ∈ Nat : n * 1 = n
    // This is Nat.mul_one in Lean/Mathlib
    let obligation = TlaObligation {
        module: "NaturalsInduction".to_string(),
        line: Some(102),
        declares: vec![],
        hypotheses: vec![],
        goal: TlaFormula::ForallIn(
            "n".to_string(),
            Box::new(TlaExpr::Nat),
            Box::new(TlaFormula::Eq(
                Box::new(TlaExpr::Arith(
                    TlaArithOp::Mul,
                    Box::new(TlaExpr::Var("n".to_string())),
                    Box::new(TlaExpr::Int(1)),
                )),
                Box::new(TlaExpr::Var("n".to_string())),
            )),
        ),
        tactic_hint: Some("induction".to_string()),
    };

    let result = prove_tla_obligation(&obligation);

    assert!(
        result.tactics_tried.contains(&"nat_induction".to_string()),
        "nat_induction should be tried for n * 1 = n, got: {:?}",
        result.tactics_tried
    );
}

#[test]
fn test_arith_n_mul_zero() {
    use clean_tla::encoding::{TlaArithOp, TlaExpr};

    // ∀n ∈ Nat : n * 0 = 0
    // This is Nat.mul_zero in Lean/Mathlib
    let obligation = TlaObligation {
        module: "NaturalsInduction".to_string(),
        line: Some(103),
        declares: vec![],
        hypotheses: vec![],
        goal: TlaFormula::ForallIn(
            "n".to_string(),
            Box::new(TlaExpr::Nat),
            Box::new(TlaFormula::Eq(
                Box::new(TlaExpr::Arith(
                    TlaArithOp::Mul,
                    Box::new(TlaExpr::Var("n".to_string())),
                    Box::new(TlaExpr::Int(0)),
                )),
                Box::new(TlaExpr::Int(0)),
            )),
        ),
        tactic_hint: Some("induction".to_string()),
    };

    let result = prove_tla_obligation(&obligation);

    assert!(
        result.tactics_tried.contains(&"nat_induction".to_string()),
        "nat_induction should be tried for n * 0 = 0, got: {:?}",
        result.tactics_tried
    );
}

#[test]
fn test_arith_n_ge_zero() {
    use clean_tla::encoding::{TlaCmpOp, TlaExpr};

    // ∀n ∈ Nat : n ≥ 0
    // This is Nat.zero_le in Lean/Mathlib
    let obligation = TlaObligation {
        module: "NaturalsInduction".to_string(),
        line: Some(104),
        declares: vec![],
        hypotheses: vec![],
        goal: TlaFormula::ForallIn(
            "n".to_string(),
            Box::new(TlaExpr::Nat),
            Box::new(TlaFormula::Expr(TlaExpr::Cmp(
                TlaCmpOp::Ge,
                Box::new(TlaExpr::Var("n".to_string())),
                Box::new(TlaExpr::Int(0)),
            ))),
        ),
        tactic_hint: Some("induction".to_string()),
    };

    let result = prove_tla_obligation(&obligation);

    assert!(
        result.tactics_tried.contains(&"nat_induction".to_string()),
        "nat_induction should be tried for n ≥ 0, got: {:?}",
        result.tactics_tried
    );
}

// ================================================================
// Well-Founded Induction Integration Tests
// ================================================================

#[test]
fn test_wf_induction_nat_set() {
    use clean_tla::encoding::TlaExpr;

    // ∀n ∈ Nat : True using WF induction path
    // The WF tactic should recognize TLA.Nat and use Nat.lt relation
    let obligation = TlaObligation {
        module: "WellFoundedNat".to_string(),
        line: Some(200),
        declares: vec![],
        hypotheses: vec![],
        goal: TlaFormula::ForallIn(
            "n".to_string(),
            Box::new(TlaExpr::Nat),
            Box::new(TlaFormula::True),
        ),
        tactic_hint: None, // Let it auto-select
    };

    let result = prove_tla_obligation(&obligation);

    // Should try either nat_induction or wf_induction
    assert!(
        result.tactics_tried.contains(&"nat_induction".to_string())
            || result.tactics_tried.contains(&"wf_induction".to_string()),
        "induction tactic should be tried, got: {:?}",
        result.tactics_tried
    );
}

#[test]
fn test_wf_induction_generic_set() {
    use clean_tla::encoding::TlaExpr;

    // ∀x ∈ S : True for generic set S
    // WF induction should apply with generic WF relation
    let obligation = TlaObligation {
        module: "WellFoundedGeneric".to_string(),
        line: Some(201),
        declares: vec![TlaDeclare::Constant {
            name: "S".to_string(),
            arity: 0,
        }],
        hypotheses: vec![],
        goal: TlaFormula::ForallIn(
            "x".to_string(),
            Box::new(TlaExpr::Const("S".to_string())),
            Box::new(TlaFormula::True),
        ),
        tactic_hint: None,
    };

    let result = prove_tla_obligation(&obligation);

    // For generic sets, wf_induction should be tried via auto
    assert!(
        !result.tactics_tried.is_empty(),
        "should try some tactics, got: {:?}",
        result.tactics_tried
    );
}

#[test]
fn test_combined_induction_temporal() {
    use clean_tla::encoding::TlaExpr;

    // □(∀n ∈ Nat : True)
    // Combines temporal and induction reasoning
    let obligation = TlaObligation {
        module: "CombinedInductionTemporal".to_string(),
        line: Some(300),
        declares: vec![],
        hypotheses: vec![],
        goal: TlaFormula::Always(Box::new(TlaFormula::ForallIn(
            "n".to_string(),
            Box::new(TlaExpr::Nat),
            Box::new(TlaFormula::True),
        ))),
        tactic_hint: None,
    };

    let result = prove_tla_obligation(&obligation);

    // Should try temporal tactics
    assert!(
        result
            .tactics_tried
            .contains(&"unfold_temporal".to_string()),
        "temporal tactics should be tried, got: {:?}",
        result.tactics_tried
    );
}

// ================================================================
// Biconditional (Iff) Tests - Root Cause Analysis for #67
// ================================================================

/// Regression guard: Iff reflexivity (TRUE ↔ TRUE) requires Iff.intro
///
/// HISTORY: This was a canary test documenting missing Iff.intro (#67).
/// TlaTacticEngine::new() now calls env.init_iff(), so this passes.
#[test]
fn test_iff_reflexivity_true_true() {
    // Simplest possible biconditional: TRUE ↔ TRUE
    let obligation = TlaObligation {
        module: "IffTest".to_string(),
        line: Some(1),
        declares: vec![],
        hypotheses: vec![],
        goal: TlaFormula::Iff(Box::new(TlaFormula::True), Box::new(TlaFormula::True)),
        tactic_hint: Some("auto".to_string()),
    };

    let result = prove_tla_obligation(&obligation);

    // Iff.intro is now available in the environment (Part of #67)
    assert!(
        result.proved,
        "Iff reflexivity (TRUE ↔ TRUE) should pass with Iff.intro available: {:?}",
        result
    );
}

/// Discriminating test: `FALSE ↔ FALSE` PASSES via superposition
///
/// This test documents that some Iff goals can be proved without Iff.intro
/// via the superposition prover (likely through CNF/SMT reasoning).
#[test]
fn test_iff_false_false_passes_via_superposition() {
    let obligation = TlaObligation {
        module: "IffTest".to_string(),
        line: Some(2),
        declares: vec![],
        hypotheses: vec![],
        goal: TlaFormula::Iff(Box::new(TlaFormula::False), Box::new(TlaFormula::False)),
        tactic_hint: Some("auto".to_string()),
    };

    let result = prove_tla_obligation(&obligation);

    // This passes via superposition or simp, not tauto's split_
    // The solver treats Iff semantically
    assert!(
        result.proved,
        "Iff (FALSE ↔ FALSE) should be proved: {:?}",
        result
    );

    // Document which tactic succeeded (for tracking)
    println!(
        "FALSE ↔ FALSE proved via: {:?}, certificate: {:?}",
        result.tactics_tried, result.certificate
    );
}

/// Discriminating test: `(TRUE → TRUE) ↔ (TRUE → TRUE)` PASSES via superposition
///
/// Simple implication equivalence - passes via superposition
#[test]
fn test_iff_impl_passes_via_superposition() {
    let obligation = TlaObligation {
        module: "IffTest".to_string(),
        line: Some(3),
        declares: vec![],
        hypotheses: vec![],
        goal: TlaFormula::Iff(
            Box::new(TlaFormula::Implies(
                Box::new(TlaFormula::True),
                Box::new(TlaFormula::True),
            )),
            Box::new(TlaFormula::Implies(
                Box::new(TlaFormula::True),
                Box::new(TlaFormula::True),
            )),
        ),
        tactic_hint: Some("auto".to_string()),
    };

    let result = prove_tla_obligation(&obligation);

    // This passes via superposition
    assert!(
        result.proved,
        "Iff with implications passes via superposition: {:?}",
        result
    );
}

/// Test verifying the exact mechanism: split_ on Iff without Iff.intro
///
/// This test constructs an Iff goal manually and verifies Iff.intro presence.
#[test]
fn test_iff_intro_missing_in_default_env() {
    use clean_kernel::env::Environment;
    use clean_kernel::name::Name;

    // Create empty environment (like TlaTacticEngine::new() does)
    let env = Environment::new();

    // Check that Iff.intro is NOT in the environment
    let iff_intro_name = Name::from_string("Iff.intro");
    assert!(
        env.get_const(&iff_intro_name).is_none(),
        "Empty environment should not have Iff.intro - this is the root cause of #67"
    );

    // Also verify Iff itself is missing
    let iff_name = Name::from_string("Iff");
    assert!(
        env.get_const(&iff_name).is_none(),
        "Empty environment should not have Iff type"
    );
}

/// Test showing that initialized environment DOES have Iff.intro
#[test]
fn test_iff_intro_present_after_init() {
    use clean_kernel::env::Environment;
    use clean_kernel::name::Name;

    // Create environment WITH init_iff
    let mut env_with_iff = Environment::new();
    env_with_iff.init_iff().expect("init_iff should succeed");

    // Verify Iff.intro IS in the initialized environment
    let iff_intro_name = Name::from_string("Iff.intro");
    assert!(
        env_with_iff.get_const(&iff_intro_name).is_some(),
        "Initialized environment should have Iff.intro"
    );

    // Also verify Iff.mp and Iff.mpr
    let iff_mp_name = Name::from_string("Iff.mp");
    let iff_mpr_name = Name::from_string("Iff.mpr");
    assert!(
        env_with_iff.get_const(&iff_mp_name).is_some(),
        "Initialized environment should have Iff.mp"
    );
    assert!(
        env_with_iff.get_const(&iff_mpr_name).is_some(),
        "Initialized environment should have Iff.mpr"
    );
}

// ================================================================
// Remaining Auto Benchmark Failures - Canary Tests
// ================================================================

/// Regression guard: conjunction_intro (h_p: P, h_q: Q ⊢ P ∧ Q)
///
/// HISTORY: This was a canary test documenting incorrect BVar lifting in hypothesis
/// types (#67). The fix lifts each hypothesis type by the number of inner hypotheses.
#[test]
fn test_conjunction_intro() {
    use clean_tla::encoding::TlaExpr;

    let obligation = TlaObligation {
        module: "PropositionalTest".to_string(),
        line: Some(1),
        declares: vec![
            TlaDeclare::Prop {
                name: "P".to_string(),
            },
            TlaDeclare::Prop {
                name: "Q".to_string(),
            },
        ],
        hypotheses: vec![
            TlaHypothesis {
                name: "h_p".to_string(),
                formula: TlaFormula::Expr(TlaExpr::Var("P".to_string())),
            },
            TlaHypothesis {
                name: "h_q".to_string(),
                formula: TlaFormula::Expr(TlaExpr::Var("Q".to_string())),
            },
        ],
        goal: TlaFormula::And(
            Box::new(TlaFormula::Expr(TlaExpr::Var("P".to_string()))),
            Box::new(TlaFormula::Expr(TlaExpr::Var("Q".to_string()))),
        ),
        tactic_hint: Some("auto".to_string()),
    };

    let result = prove_tla_obligation(&obligation);

    // Fixed: hypothesis types now correctly lifted (Part of #67)
    assert!(
        result.proved,
        "conjunction_intro (h_p: P, h_q: Q ⊢ P ∧ Q) should pass: {:?}",
        result
    );
}
