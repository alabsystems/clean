// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Cross-validation tests: run the SAME formulas through both SmtBridge (built-in)
//! and AyBackend, comparing results for agreement.
//!
//! Addresses #1304: No cross-validation between built-in and ay solver paths.
//!
//! Strategy: Build (hypotheses, goal) pairs as kernel `Expr` using FVars.
//! - SmtBridge: add_hypothesis_with_fvar -> prove(goal)
//! - AyBackend: register FVars -> translate+assert hypotheses -> negate goal -> check_sat
//!
//! We compare tri-state outcomes: PROVABLE / REFUTED / UNKNOWN.
//! Both solvers must agree (modulo one returning Unknown where the other succeeds).

#[cfg(feature = "ay-smt")]
use super::super::ay_backend::{AyBackend, AyLogic};
use super::super::*;
use super::test_helpers::{make_eq, setup_env};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SolverOutcome {
    Provable,
    Refuted,
    Unknown,
}

/// Which SMT theory the test case exercises. Controls AyBackend logic selection.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Theory {
    /// Equality + uninterpreted functions (QF_UF)
    Euf,
    /// Linear integer arithmetic with comparisons (QF_LIA)
    Lia,
}

fn classify_bridge_result(result: &SmtVerificationResult) -> SolverOutcome {
    match result {
        SmtVerificationResult::Verified(_) | SmtVerificationResult::Unverified { .. } => {
            SolverOutcome::Provable
        }
        SmtVerificationResult::Refuted(_) => SolverOutcome::Refuted,
        SmtVerificationResult::Unknown(_) => SolverOutcome::Unknown,
    }
}

struct CrossValidationCase {
    name: &'static str,
    theory: Theory,
    /// FVar IDs for constants and functions, used by AyBackend registration.
    fvar_ids: Vec<FVarId>,
    /// FVar IDs for uninterpreted functions (subset of fvar_ids).
    ///
    /// Populated by every case row (the UF rows carry real ids) but not yet
    /// consumed by the AyBackend registration helper, which currently registers
    /// from `fvar_ids` alone. Kept so the UF rows stay declarative — awaiting
    /// production wiring — 2026-07-31.
    #[allow(dead_code)]
    func_ids: Vec<FVarId>,
    hypotheses: Vec<(Expr, FVarId)>,
    goal: Expr,
    expected: SolverOutcome,
}

fn make_eq_fvar(lhs: Expr, rhs: Expr) -> Expr {
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    make_eq(a_ty, lhs, rhs)
}

fn build_fvar_app(fvar_id: FVarId, args: &[Expr]) -> Expr {
    let mut result = Expr::fvar(fvar_id);
    for arg in args {
        result = Expr::app(result, arg.clone());
    }
    result
}

fn make_nat_le(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Nat.le"), vec![]), lhs),
        rhs,
    )
}

fn make_nat_lt(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Nat.lt"), vec![]), lhs),
        rhs,
    )
}

fn make_eq_nat(lhs: Expr, rhs: Expr) -> Expr {
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    make_eq(nat_ty, lhs, rhs)
}

fn equality_cases() -> Vec<CrossValidationCase> {
    let a_id = FVarId::new(100);
    let b_id = FVarId::new(101);
    let c_id = FVarId::new(102);
    let a = Expr::fvar(a_id);
    let b = Expr::fvar(b_id);
    let c = Expr::fvar(c_id);

    vec![
        CrossValidationCase {
            name: "reflexivity",
            theory: Theory::Euf,
            fvar_ids: vec![a_id],
            func_ids: vec![],
            hypotheses: vec![],
            goal: make_eq_fvar(a.clone(), a.clone()),
            expected: SolverOutcome::Provable,
        },
        CrossValidationCase {
            name: "symmetry",
            theory: Theory::Euf,
            fvar_ids: vec![a_id, b_id],
            func_ids: vec![],
            hypotheses: vec![(make_eq_fvar(a.clone(), b.clone()), FVarId::new(300))],
            goal: make_eq_fvar(b.clone(), a.clone()),
            expected: SolverOutcome::Provable,
        },
        CrossValidationCase {
            name: "transitivity",
            theory: Theory::Euf,
            fvar_ids: vec![a_id, b_id, c_id],
            func_ids: vec![],
            hypotheses: vec![
                (make_eq_fvar(a.clone(), b.clone()), FVarId::new(300)),
                (make_eq_fvar(b.clone(), c.clone()), FVarId::new(301)),
            ],
            goal: make_eq_fvar(a.clone(), c.clone()),
            expected: SolverOutcome::Provable,
        },
        CrossValidationCase {
            name: "transitivity_reversed",
            theory: Theory::Euf,
            fvar_ids: vec![a_id, b_id, c_id],
            func_ids: vec![],
            hypotheses: vec![
                (make_eq_fvar(a.clone(), b.clone()), FVarId::new(300)),
                (make_eq_fvar(b.clone(), c.clone()), FVarId::new(301)),
            ],
            goal: make_eq_fvar(c, a),
            expected: SolverOutcome::Provable,
        },
        CrossValidationCase {
            name: "unprovable_distinct_eq",
            theory: Theory::Euf,
            fvar_ids: vec![a_id, b_id],
            func_ids: vec![],
            hypotheses: vec![],
            goal: make_eq_fvar(b, Expr::fvar(a_id)),
            expected: SolverOutcome::Refuted,
        },
    ]
}

fn congruence_cases() -> Vec<CrossValidationCase> {
    let a_id = FVarId::new(100);
    let b_id = FVarId::new(101);
    let f_id = FVarId::new(200);
    let a = Expr::fvar(a_id);
    let b = Expr::fvar(b_id);

    vec![
        CrossValidationCase {
            name: "congruence",
            theory: Theory::Euf,
            fvar_ids: vec![a_id, b_id, f_id],
            func_ids: vec![f_id],
            hypotheses: vec![(make_eq_fvar(a.clone(), b.clone()), FVarId::new(300))],
            goal: make_eq_fvar(
                build_fvar_app(f_id, std::slice::from_ref(&a)),
                build_fvar_app(f_id, std::slice::from_ref(&b)),
            ),
            expected: SolverOutcome::Provable,
        },
        CrossValidationCase {
            name: "nested_congruence",
            theory: Theory::Euf,
            fvar_ids: vec![a_id, b_id, f_id],
            func_ids: vec![f_id],
            hypotheses: vec![(make_eq_fvar(a.clone(), b.clone()), FVarId::new(300))],
            goal: make_eq_fvar(
                build_fvar_app(
                    f_id,
                    std::slice::from_ref(&build_fvar_app(f_id, std::slice::from_ref(&a))),
                ),
                build_fvar_app(
                    f_id,
                    std::slice::from_ref(&build_fvar_app(f_id, std::slice::from_ref(&b))),
                ),
            ),
            expected: SolverOutcome::Provable,
        },
    ]
}

/// Arithmetic comparison cases: Nat.le/Nat.lt on integer-valued FVars.
///
/// Tests that comparison reasoning (reflexivity, transitivity, antisymmetry)
/// produces identical results through both solver paths.
fn arithmetic_comparison_cases() -> Vec<CrossValidationCase> {
    let a_id = FVarId::new(100);
    let b_id = FVarId::new(101);
    let c_id = FVarId::new(102);
    let a = Expr::fvar(a_id);
    let b = Expr::fvar(b_id);
    let c = Expr::fvar(c_id);

    vec![
        CrossValidationCase {
            name: "le_reflexivity",
            theory: Theory::Lia,
            fvar_ids: vec![a_id],
            func_ids: vec![],
            hypotheses: vec![],
            goal: make_nat_le(a.clone(), a.clone()),
            expected: SolverOutcome::Provable,
        },
        CrossValidationCase {
            name: "le_transitivity",
            theory: Theory::Lia,
            fvar_ids: vec![a_id, b_id, c_id],
            func_ids: vec![],
            hypotheses: vec![
                (make_nat_le(a.clone(), b.clone()), FVarId::new(300)),
                (make_nat_le(b.clone(), c.clone()), FVarId::new(301)),
            ],
            goal: make_nat_le(a.clone(), c.clone()),
            expected: SolverOutcome::Provable,
        },
        CrossValidationCase {
            name: "lt_le_transitivity",
            theory: Theory::Lia,
            fvar_ids: vec![a_id, b_id, c_id],
            func_ids: vec![],
            hypotheses: vec![
                (make_nat_lt(a.clone(), b.clone()), FVarId::new(300)),
                (make_nat_le(b.clone(), c.clone()), FVarId::new(301)),
            ],
            goal: make_nat_lt(a.clone(), c.clone()),
            expected: SolverOutcome::Provable,
        },
        CrossValidationCase {
            name: "lt_implies_le",
            theory: Theory::Lia,
            fvar_ids: vec![a_id, b_id],
            func_ids: vec![],
            hypotheses: vec![(make_nat_lt(a.clone(), b.clone()), FVarId::new(302))],
            goal: make_nat_le(a.clone(), b.clone()),
            expected: SolverOutcome::Provable,
        },
        CrossValidationCase {
            name: "le_antisymmetry",
            theory: Theory::Lia,
            fvar_ids: vec![a_id, b_id],
            func_ids: vec![],
            hypotheses: vec![
                (make_nat_le(a.clone(), b.clone()), FVarId::new(300)),
                (make_nat_le(b.clone(), a.clone()), FVarId::new(301)),
            ],
            goal: make_eq_nat(a.clone(), b.clone()),
            expected: SolverOutcome::Provable,
        },
        CrossValidationCase {
            name: "unprovable_lt",
            theory: Theory::Lia,
            fvar_ids: vec![a_id, b_id],
            func_ids: vec![],
            hypotheses: vec![],
            goal: make_nat_lt(a, b),
            expected: SolverOutcome::Refuted,
        },
    ]
}

// NOTE: Array theory cross-validation at the Expr level is not feasible.
// SmtBridge translates select/store Exprs via bridge/translate/term_lowering.rs,
// but AyBackend's translate_atom_const_app rejects them as unknown constants.
// AyBackend supports arrays at the ay Term level (fresh_array/store/select
// methods) but not through the Lean Expr translation pipeline. Future work: add
// array Expr handling to AyBackend translate_app, then add array cross-validation
// cases here.

fn build_test_cases() -> Vec<CrossValidationCase> {
    let mut cases = equality_cases();
    cases.extend(congruence_cases());
    cases.extend(arithmetic_comparison_cases());
    cases
}

// =========================================================================
// SmtBridge-only tests (always available)
// =========================================================================

#[test]
fn test_cross_validation_bridge_only() {
    let env = setup_env();

    for case in build_test_cases() {
        let mut bridge = SmtBridge::new(&env);

        for (hyp, fvar) in &case.hypotheses {
            bridge
                .add_hypothesis_with_fvar(hyp, Some(*fvar))
                .unwrap_or_else(|e| panic!("[{}] add_hypothesis failed: {e}", case.name));
        }

        let result = bridge
            .prove(&case.goal)
            .unwrap_or_else(|e| panic!("[{}] prove failed: {e}", case.name));

        let outcome = classify_bridge_result(&result);
        assert_eq!(
            outcome, case.expected,
            "[{}] SmtBridge: expected {:?}, got {:?} (result: {:?})",
            case.name, case.expected, outcome, result
        );

        let requires_verified = matches!(
            case.name,
            "le_reflexivity"
                | "le_transitivity"
                | "lt_le_transitivity"
                | "lt_implies_le"
                | "le_antisymmetry"
        );
        if requires_verified {
            assert!(
                result.is_verified(),
                "[{}] arithmetic bridge case should be kernel-verified, got {:?}",
                case.name,
                result
            );
        }
    }
}

// =========================================================================
// AyBackend-only tests (feature-gated)
// =========================================================================

#[cfg(feature = "ay-smt")]
fn run_ay_case(case: &CrossValidationCase) -> SolverOutcome {
    let logic = match case.theory {
        Theory::Euf => AyLogic::QfUf,
        Theory::Lia => AyLogic::QfLia,
    };
    let mut backend = AyBackend::new(logic);

    for &fvar in &case.fvar_ids {
        backend.register_fvar_int(fvar);
    }

    for (hyp, _fvar) in &case.hypotheses {
        let term = backend
            .translate_expr(hyp)
            .unwrap_or_else(|e| panic!("[{}] ay translate hyp failed: {e}", case.name));
        backend.assert_term(term);
    }

    let goal_term = backend
        .translate_expr(&case.goal)
        .unwrap_or_else(|e| panic!("[{}] ay translate goal failed: {e}", case.name));
    let neg_goal = backend.not(goal_term);
    backend.assert_term(neg_goal);

    let report = backend.check_sat();
    if report.is_unsat() {
        SolverOutcome::Provable
    } else if report.is_sat() {
        SolverOutcome::Refuted
    } else {
        SolverOutcome::Unknown
    }
}

#[cfg(feature = "ay-smt")]
#[test]
fn test_cross_validation_ay_only() {
    for case in build_test_cases() {
        let outcome = run_ay_case(&case);
        assert_eq!(
            outcome, case.expected,
            "[{}] AyBackend: expected {:?}, got {:?}",
            case.name, case.expected, outcome
        );
    }
}

// =========================================================================
// Cross-validation: compare both solvers on the same formulas
// =========================================================================

#[cfg(feature = "ay-smt")]
#[test]
fn test_cross_validation_agreement() {
    let env = setup_env();

    for case in build_test_cases() {
        let mut bridge = SmtBridge::new(&env);
        for (hyp, fvar) in &case.hypotheses {
            bridge
                .add_hypothesis_with_fvar(hyp, Some(*fvar))
                .unwrap_or_else(|e| panic!("[{}] bridge add_hypothesis failed: {e}", case.name));
        }
        let bridge_result = bridge
            .prove(&case.goal)
            .unwrap_or_else(|e| panic!("[{}] bridge prove failed: {e}", case.name));
        let bridge_outcome = classify_bridge_result(&bridge_result);

        let ay_outcome = run_ay_case(&case);

        // Both must agree (except when one returns Unknown)
        if bridge_outcome != SolverOutcome::Unknown && ay_outcome != SolverOutcome::Unknown {
            assert_eq!(
                bridge_outcome, ay_outcome,
                "[{}] DISAGREEMENT: SmtBridge={:?} vs AyBackend={:?}",
                case.name, bridge_outcome, ay_outcome
            );
        }

        if bridge_outcome != SolverOutcome::Unknown {
            assert_eq!(
                bridge_outcome, case.expected,
                "[{}] SmtBridge: expected {:?}, got {:?}",
                case.name, case.expected, bridge_outcome
            );
        }
        if ay_outcome != SolverOutcome::Unknown {
            assert_eq!(
                ay_outcome, case.expected,
                "[{}] AyBackend: expected {:?}, got {:?}",
                case.name, case.expected, ay_outcome
            );
        }
    }
}
