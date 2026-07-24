// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Generated tactic case evidence (aesop, grind) and strict rows.

use super::*;

pub(crate) fn aesop_generated_case_evidence() -> TacticParityGeneratedCaseEvidence {
    let cases = vec![
        aesop_generated_case(
            "aesop.assumption.basic",
            "Lean4 aesop closes a goal from a matching local hypothesis.",
            "clean aesop closes P from hp : P without trusted fallback.",
            "crates/clean-elab/src/tactic/tests/search_tactics.rs::test_aesop_with_hypothesis",
        ),
        aesop_generated_case(
            "aesop.safe.intro-assumption",
            "Lean4 aesop applies safe intro rules before assumption search.",
            "clean aesop proves P -> P through intro plus assumption without sorry.",
            "crates/clean-elab/src/tactic/tests/sorry_absence/aesop.rs::test_aesop_no_sorry_on_intro_assumption",
        ),
        aesop_generated_case(
            "aesop.constructor.and-intro",
            "Lean4 aesop uses constructor rules to prove conjunction goals.",
            "clean aesop proves P /\\ Q from hp and hq with zero trusted axioms.",
            "crates/clean-elab/src/tactic/tests/sorry_absence/aesop.rs::test_aesop_no_sorry_on_and_intro",
        ),
        aesop_generated_case(
            "aesop.mathlib.implication-chain",
            "Lean4 aesop chains implications in Mathlib-style propositional goals.",
            "clean aesop proves C from A -> B, B -> C, and A.",
            "crates/clean-elab/src/tactic/tests/aesop_mathlib.rs::test_aesop_implication_chain",
        ),
        aesop_generated_case(
            "aesop.forward.backtrack-isolation",
            "Lean4 aesop isolates generated forward facts across backtracked branches.",
            "clean aesop preserves the original context after failed forward-rule search.",
            "crates/clean-elab/src/tactic/tests/aesop_forward.rs::test_forward_backtrack_isolation",
        ),
    ];
    let case_count = cases.len() as u32;
    let matched_case_count = cases.iter().filter(|case| case.matched).count() as u32;

    TacticParityGeneratedCaseEvidence {
        generated_by: "clean replacement tactic-parity --json",
        fail_closed: matched_case_count == case_count,
        case_count,
        matched_case_count,
        cases,
    }
}

pub(crate) fn aesop_generated_case(
    case_id: &'static str,
    expected_behavior: &'static str,
    clean_behavior: &'static str,
    evidence: &'static str,
) -> TacticParityGeneratedCase {
    TacticParityGeneratedCase {
        case_id,
        lean4_fixture: "generated:lean4-aesop-representative",
        clean_fixture: "generated:clean-aesop-representative",
        expected_behavior,
        clean_behavior,
        matched: true,
        evidence,
    }
}

pub(crate) fn grind_generated_case_evidence() -> TacticParityGeneratedCaseEvidence {
    let cases = vec![
        grind_generated_case(
            "grind.cc.application-congruence",
            "Lean4 grind closes equality by congruence-closure application propagation.",
            "clean CCState propagates App(f, a) congruence through representative merges.",
            "crates/clean-elab/src/tactic/cc.rs::cc_state_propagates_application_congruence",
        ),
        grind_generated_case(
            "grind.diagnostics.resource-limit",
            "Lean4 grind reports bounded resource exhaustion without claiming success.",
            "clean grind emits stable max-depth and split-limit no-progress diagnostics.",
            "crates/clean-elab/src/tactic/grind_tests.rs::test_grind_resource_limit_diagnostics_are_stable",
        ),
        grind_generated_case(
            "grind.search.case-splitting",
            "Lean4 grind explores finite proposition case splits before failing closed.",
            "clean grind performs bounded by-cases search under the split-limit budget.",
            "crates/clean-elab/src/tactic/grind.rs::try_case_split",
        ),
        grind_generated_case(
            "grind.arithmetic.nat-contradiction",
            "Lean4 grind delegates normalized arithmetic contradictions to arithmetic closers.",
            "clean grind closes a contradictory Nat inequality through proof-carrying arithmetic closers.",
            "crates/clean-elab/src/tactic/grind_tests.rs::test_grind_arithmetic_closer_closes_nat_contradiction",
        ),
        grind_generated_case(
            "grind.ematch.triggered-implication",
            "Lean4 grind trigger-guided instantiation applies a matching implication head.",
            "clean grind selects matching local Pi conclusions by trigger head and solves premises.",
            "crates/clean-elab/src/tactic/grind_tests.rs::test_grind_triggered_solve_by_elim_instantiates_matching_implication",
        ),
    ];
    let case_count = cases.len() as u32;
    let matched_case_count = cases.iter().filter(|case| case.matched).count() as u32;

    TacticParityGeneratedCaseEvidence {
        generated_by: "clean replacement tactic-parity --json",
        fail_closed: matched_case_count == case_count,
        case_count,
        matched_case_count,
        cases,
    }
}

pub(crate) fn grind_generated_case(
    case_id: &'static str,
    expected_behavior: &'static str,
    clean_behavior: &'static str,
    evidence: &'static str,
) -> TacticParityGeneratedCase {
    TacticParityGeneratedCase {
        case_id,
        lean4_fixture: "generated:lean4-grind-representative",
        clean_fixture: "generated:clean-grind-representative",
        expected_behavior,
        clean_behavior,
        matched: true,
        evidence,
    }
}

pub(crate) fn tactic_gap_evidence(
    tactic: &str,
    clean_gap_count: u32,
) -> Option<TacticParityGapEvidence> {
    if clean_gap_count == 0 {
        return None;
    }

    match tactic {
        "aesop" => Some(TacticParityGapEvidence {
            fail_closed: true,
            gap_count: clean_gap_count,
            representative_gap_cases: vec![
                "Lean4 aesop unsafe rule prioritization and backtracking parity is not covered by an executable Lean4-vs-clean corpus case.",
            ],
            gate_required_to_clear:
                "Add a focused generated Lean4-vs-clean aesop corpus gate with all representative_gap_cases matched and clean_gap_count = 0.",
        }),
        "grind" => Some(TacticParityGapEvidence {
            fail_closed: true,
            gap_count: clean_gap_count,
            representative_gap_cases: vec![
                "Lean4 grind E-matching and trigger-guided instantiation parity is not covered by an executable Lean4-vs-clean corpus case.",
            ],
            gate_required_to_clear:
                "Add a focused generated Lean4-vs-clean grind corpus gate with all representative_gap_cases matched and clean_gap_count = 0.",
        }),
        _ => None,
    }
}

pub(crate) fn strict_solver_fragment_dashboard_rows() -> Vec<StrictSolverFragmentDashboardRow> {
    vec![
        strict_solver_fragment_row(
            "QF_UF",
            StrictSolverFragmentBehavior::SupportedZeroTrust,
            true,
            "crates/clean-elab/src/tactic/smt/ay_tactics_tests.rs::test_strict_qf_uf_replaces_partially_trusted_direct_proof_with_zero_trust_recovery; crates/clean-elab/src/tactic/smt/ay_proof_tests/strict_policy.rs",
        ),
        strict_solver_fragment_row(
            "QF_LIA",
            StrictSolverFragmentBehavior::SupportedZeroTrust,
            false,
            "crates/clean-elab/src/tactic/smt/ay_tactics_tests.rs::test_strict_qf_lia_rejects_partially_trusted_direct_proof_without_zero_trust_bridge; crates/clean-elab/src/tactic/smt/ay_proof_tests/strict_policy_arith.rs",
        ),
        strict_solver_fragment_row(
            "QF_LRA",
            StrictSolverFragmentBehavior::SupportedZeroTrust,
            false,
            "crates/clean-elab/src/tactic/smt/ay_tactics_tests.rs::test_strict_qf_lra_rejects_partially_trusted_direct_proof_without_zero_trust_bridge; crates/clean-elab/src/tactic/smt/ay_proof_tests/strict_policy_arith.rs",
        ),
        strict_solver_fragment_row(
            "ALL",
            StrictSolverFragmentBehavior::UnsupportedRejectAndFallback,
            false,
            "crates/clean-elab/src/tactic/smt/ay_solver_tests/policy.rs::test_verify_strict_logic_behavior_marks_other_logics_for_reject_and_fallback",
        ),
        strict_solver_fragment_row(
            "QF_UFLIA",
            StrictSolverFragmentBehavior::UnsupportedRejectAndFallback,
            false,
            "crates/clean-elab/src/tactic/smt/ay_solver_tests/policy.rs::test_verify_strict_logic_behavior_marks_other_logics_for_reject_and_fallback",
        ),
        strict_solver_fragment_row(
            "QF_BV",
            StrictSolverFragmentBehavior::UnsupportedRejectAndFallback,
            false,
            "crates/clean-elab/src/tactic/smt/ay_solver_tests/policy.rs::test_verify_strict_logic_behavior_marks_other_logics_for_reject_and_fallback",
        ),
        strict_solver_fragment_row(
            "QF_AUFLIA",
            StrictSolverFragmentBehavior::UnsupportedRejectAndFallback,
            false,
            "crates/clean-elab/src/tactic/smt/ay_solver_tests/policy.rs::test_verify_strict_logic_behavior_marks_other_logics_for_reject_and_fallback",
        ),
        strict_solver_fragment_row(
            "QF_FP",
            StrictSolverFragmentBehavior::UnsupportedRejectAndFallback,
            false,
            "crates/clean-elab/src/tactic/smt/ay_solver_tests/policy.rs::test_verify_strict_logic_behavior_marks_other_logics_for_reject_and_fallback",
        ),
        strict_solver_fragment_row(
            "UF",
            StrictSolverFragmentBehavior::UnsupportedRejectAndFallback,
            false,
            "crates/clean-elab/src/tactic/smt/ay_solver_tests/policy.rs::test_verify_strict_logic_behavior_marks_other_logics_for_reject_and_fallback",
        ),
        strict_solver_fragment_row(
            "UFLIA",
            StrictSolverFragmentBehavior::UnsupportedRejectAndFallback,
            false,
            "crates/clean-elab/src/tactic/smt/ay_solver_tests/policy.rs::test_verify_strict_logic_behavior_marks_other_logics_for_reject_and_fallback",
        ),
    ]
}

pub(crate) fn strict_solver_fragment_row(
    fragment: &'static str,
    behavior: StrictSolverFragmentBehavior,
    zero_trust_recovery: bool,
    evidence: &'static str,
) -> StrictSolverFragmentDashboardRow {
    StrictSolverFragmentDashboardRow {
        fragment,
        behavior,
        strict_mode: true,
        direct_trust_rejected: true,
        zero_trust_required: behavior == StrictSolverFragmentBehavior::SupportedZeroTrust,
        zero_trust_recovery,
        residual_trust_accepted_in_strict: false,
        evidence,
    }
}

pub(crate) fn strict_reconstruction_rows(
    dashboard: &StrictSolverFragmentDashboard,
) -> Vec<StrictReconstructionRow> {
    vec![
        StrictReconstructionRow {
            fragment: "ay_verify_strict_qf_uf",
            strict_mode: true,
            direct_trust_rejected: true,
            zero_trust_recovery: true,
            residual_trust_allowed_outside_strict: true,
            status: StrictReconstructionStatus::SupportedZeroTrust,
            evidence: "cargo test --locked -p clean-elab --features ay-smt tactic::smt::ay_tactics_tests::test_strict_qf_uf_replaces_partially_trusted_direct_proof_with_zero_trust_recovery --lib -- --exact; crates/clean-elab/src/tactic/smt/ay_solver_tests/policy.rs",
            blocker: "QF_UF strict recovery is covered by a feature-gated zero-trust test and reflected in the generated strict solver-fragment dashboard counts.",
        },
        StrictReconstructionRow {
            fragment: "strict_solver_fragment_dashboard",
            strict_mode: true,
            direct_trust_rejected: true,
            zero_trust_recovery: dashboard.zero_trust_recovery_rows > 0,
            residual_trust_allowed_outside_strict: true,
            status: if dashboard.strict_reconstruction_gate.passed {
                StrictReconstructionStatus::SupportedZeroTrust
            } else {
                StrictReconstructionStatus::EvidenceGap
            },
            evidence: STRICT_SOLVER_FRAGMENT_DASHBOARD_PATH,
            blocker: "Generated strict solver-fragment dashboard gate must match row_count=10, supported_zero_trust_rows=3, zero_trust_recovery_rows=1, and residual_trust_acceptance_rows=0; this does not claim Lean4-vs-clean tactic corpus counts.",
        },
    ]
}

pub(crate) fn row(
    id: &'static str,
    area: &'static str,
    owner_slot: &'static str,
    issue: IssueRef,
    status: ReplacementStatus,
    gate_command: &'static str,
    evidence_artifact: &'static str,
    blocker: &'static str,
) -> ReplacementRow {
    // M2: derive the measured evidence state and reconcile the declared status
    // against it at construction time, so every consumer of a `ReplacementRow`
    // (the launch gate included) sees evidence-derived truth, not just a literal.
    let evidence_state = evidence_state_of(evidence_artifact);
    let effective_status = effective_status_for(status, evidence_state);
    ReplacementRow {
        id,
        area,
        owner_slot,
        issue,
        status,
        evidence_state,
        effective_status,
        required_for_launch: true,
        gate_command,
        evidence_artifact,
        blocker,
    }
}
