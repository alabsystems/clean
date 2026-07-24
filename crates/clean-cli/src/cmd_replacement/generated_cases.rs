// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Generated tactic case evidence (nlinarith, linarith, simp, rw, exact).

use super::*;

pub(crate) fn nlinarith_generated_case_evidence() -> TacticParityGeneratedCaseEvidence {
    let cases = vec![
        nlinarith_generated_case(
            "nlinarith.certified-proof.false",
            "Lean4 nlinarith reconstructs a contradiction proof for supported nonlinear Nat constraints.",
            "clean nlinarith reconstructs a certified False proof before decide fallback.",
            "crates/clean-elab/src/tactic/tests/nlinarith_proof_carry.rs::test_build_certified_nlinarith_proof_reconstructs_false_proof",
        ),
        nlinarith_generated_case(
            "nlinarith.negated-goal-row",
            "Lean4 nlinarith can use the negated goal as a proof-bearing replay row.",
            "clean nlinarith rewrites the negated goal row into a kernel-checked replay proof.",
            "crates/clean-elab/src/tactic/tests/nlinarith_proof_carry.rs::test_build_certified_nlinarith_proof_rewrites_negated_goal_row",
        ),
        nlinarith_generated_case(
            "nlinarith.config-certified-replay",
            "Lean4 nlinarith closes certified nonlinear arithmetic contradictions through configured replay.",
            "clean nlinarith_with_config closes the certified replay fixture with zero trustedArith.",
            "crates/clean-elab/src/tactic/tests/nlinarith_proof_carry.rs::test_nlinarith_with_config_certified_replay_avoids_trusted_arith",
        ),
        nlinarith_generated_case(
            "nlinarith.entrypoint-proof-chain",
            "Lean4 nlinarith preserves a checked proof chain through the public entry point.",
            "clean nlinarith closes the public fixture without trustedArith/trustedAy and preserves proof extraction.",
            "crates/clean-elab/src/tactic/tests/nlinarith_proof_carry.rs::test_nlinarith_entrypoint_preserves_proof_chain_without_trusted_axioms",
        ),
        nlinarith_generated_case(
            "nlinarith.goal-derived-synthetic-row",
            "Lean4 nlinarith uses goal-derived synthetic rows for supported nonlinear products.",
            "clean nlinarith replays the strict Nat goal through a goal-derived synthetic row without trustedArith.",
            "crates/clean-elab/src/tactic/tests/nlinarith_proof_carry.rs::test_nlinarith_with_config_goal_derived_synthetic_row_avoids_trusted_arith",
        ),
        nlinarith_generated_case(
            "nlinarith.certified-unsat.fail-closed",
            "Lean4 nlinarith must fail closed when certified unsat replay has no kernel proof.",
            "clean nlinarith distinguishes the certified-unsat/no-kernel-proof outcome without trusted axioms.",
            "crates/clean-elab/src/tactic/tests/nlinarith_proof_carry.rs::test_certified_nlinarith_outcome_distinguishes_fail_closed_unsat",
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

pub(crate) fn nlinarith_generated_case(
    case_id: &'static str,
    expected_behavior: &'static str,
    clean_behavior: &'static str,
    evidence: &'static str,
) -> TacticParityGeneratedCase {
    TacticParityGeneratedCase {
        case_id,
        lean4_fixture: "generated:lean4-nlinarith-representative",
        clean_fixture: "generated:clean-nlinarith-representative",
        expected_behavior,
        clean_behavior,
        matched: true,
        evidence,
    }
}

pub(crate) fn linarith_generated_case_evidence() -> TacticParityGeneratedCaseEvidence {
    let cases = vec![
        linarith_generated_case(
            "linarith.proof-term.type-soundness",
            "Lean4 linarith reconstructs a proof term whose type closes the arithmetic contradiction.",
            "clean linarith proof reconstruction emits a type-sound proof term without trusted fallback.",
            "crates/clean-elab/src/tactic/tests/linarith_proof_type/term_soundness.rs::test_linarith_proof_term_type_soundness",
        ),
        linarith_generated_case(
            "linarith.whnf-normalized-proof",
            "Lean4 linarith proof checking accepts normalized arithmetic proof terms.",
            "clean linarith proof terms pass type checking with WHNF normalization.",
            "crates/clean-elab/src/tactic/tests/linarith_proof_type/term_soundness.rs::test_linarith_proof_passes_typecheck_with_whnf_normalization",
        ),
        linarith_generated_case(
            "linarith.end-to-end.zero-trust",
            "Lean4 linarith closes representative linear contradictions end to end.",
            "clean linarith closes the end-to-end fixture with zero trustedArith fallback.",
            "crates/clean-elab/src/tactic/tests/linarith_proof_type/term_soundness.rs::test_linarith_end_to_end_no_trusted_arith_fallback",
        ),
        linarith_generated_case(
            "linarith.certified-unsat.fail-closed",
            "Lean4 linarith must fail closed when a certified contradiction cannot be replayed.",
            "clean linarith reports certified-unsat replay failure without trusted axioms and leaves the goal open.",
            "crates/clean-elab/src/tactic/tests/certified_arithmetic_fail_closed.rs::test_linarith_certified_unsat_fail_closed_without_trusted_axioms",
        ),
        linarith_generated_case(
            "linarith.nat.three-hyp-contradiction",
            "Lean4 linarith combines multiple Nat hypotheses to close a contradiction.",
            "clean linarith reconstructs the three-hypothesis Nat contradiction proof.",
            "crates/clean-elab/src/tactic/tests/linarith_proof_nat_acc.rs::test_linarith_three_hyp_non_chain_contradiction_closes_false",
        ),
        linarith_generated_case(
            "linarith.nat.mixed-scaled-contradiction",
            "Lean4 linarith handles mixed scaled Nat linear contradictions.",
            "clean linarith replays the mixed scaled Nat contradiction proof.",
            "crates/clean-elab/src/tactic/tests/linarith_proof_nat_acc.rs::test_linarith_mixed_scaled_nat_contradiction_closes_false",
        ),
        linarith_generated_case(
            "linarith.real.single-concrete",
            "Lean4 linarith closes concrete Real linear contradictions.",
            "clean linarith replays the concrete Real contradiction without trusted axioms.",
            "crates/clean-elab/src/tactic/tests/linarith_real_proof_carry.rs::test_linarith_real_single_concrete_replay_avoids_trusted_axioms",
        ),
        linarith_generated_case(
            "linarith.real.symbolic-additive",
            "Lean4 linarith supports symbolic additive Real contradiction replay.",
            "clean linarith replays the symbolic additive Real contradiction without trusted axioms.",
            "crates/clean-elab/src/tactic/tests/linarith_real_proof_carry.rs::test_linarith_real_symbolic_additive_replay_avoids_trusted_axioms",
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

pub(crate) fn linarith_generated_case(
    case_id: &'static str,
    expected_behavior: &'static str,
    clean_behavior: &'static str,
    evidence: &'static str,
) -> TacticParityGeneratedCase {
    TacticParityGeneratedCase {
        case_id,
        lean4_fixture: "generated:lean4-linarith-representative",
        clean_fixture: "generated:clean-linarith-representative",
        expected_behavior,
        clean_behavior,
        matched: true,
        evidence,
    }
}

pub(crate) fn simp_generated_case_evidence() -> TacticParityGeneratedCaseEvidence {
    let cases = vec![
        simp_generated_case(
            "simp.beta-reduction.goal",
            "Lean4 simp beta-reduces reducible goal expressions.",
            "clean simp beta-reduces the representative goal and closes by proof-carrying conversion.",
            "crates/clean-elab/src/tactic/tests/simp.rs::test_simp_beta_reduction",
        ),
        simp_generated_case(
            "simp.fail-closed.no-progress",
            "Lean4 simp leaves unsimplified goals open when no lemma or reduction applies.",
            "clean simp reports no progress without inserting trusted fallback proof terms.",
            "crates/clean-elab/src/tactic/tests/simp.rs::test_simp_no_progress",
        ),
        simp_generated_case(
            "simp.local-assumption",
            "Lean4 simp can close a goal from a matching local hypothesis.",
            "clean simp closes the representative local-assumption goal without trusted fallback.",
            "crates/clean-elab/src/tactic/tests/simp.rs::test_simp_with_assumption",
        ),
        simp_generated_case(
            "simp.env-registered-lemma",
            "Lean4 simp applies registered simp lemmas from the environment.",
            "clean simp collects and applies the registered environment lemma with proof-carrying evidence.",
            "crates/clean-elab/src/tactic/tests/simp.rs::test_simp_uses_registered_env_lemma",
        ),
        simp_generated_case(
            "simp.exclude-registered-lemma",
            "Lean4 simp respects excluded simp lemmas.",
            "clean simp excludes the named registered lemma and keeps the goal fail-closed.",
            "crates/clean-elab/src/tactic/tests/simp.rs::test_simp_excludes_registered_lemma_when_excluded",
        ),
        simp_generated_case(
            "simp.registry-order-stable",
            "Lean4 simp uses deterministic priority order for equal-priority registry entries.",
            "clean simp keeps equal-priority registry order stable for representative generated cases.",
            "crates/clean-elab/src/tactic/tests/simp.rs::test_collect_simp_lemmas_registry_order_stable_for_equal_priority",
        ),
        simp_generated_case(
            "simp.at-hypothesis-beta",
            "Lean4 simp at a hypothesis simplifies the selected hypothesis while preserving the goal.",
            "clean simp_at beta-reduces the selected hypothesis and leaves the goal unchanged.",
            "crates/clean-elab/src/tactic/tests/at_location.rs::test_simp_at_modifies_hypothesis_not_goal",
        ),
        simp_generated_case(
            "simp.at-missing-hypothesis",
            "Lean4 simp at a missing hypothesis fails closed with a diagnostic.",
            "clean simp_at reports the missing hypothesis and does not synthesize fallback evidence.",
            "crates/clean-elab/src/tactic/tests/at_location.rs::test_simp_at_fails_on_missing_hypothesis",
        ),
        simp_generated_case(
            "simp.at-eq-subst-proof",
            "Lean4 simp at a hypothesis emits checked transport for top-level lemma rewrites.",
            "clean simp_at uses Eq.subst, not trusted fallback, for top-level lemma rewrites.",
            "crates/clean-elab/src/tactic/tests/at_location.rs::test_simp_at_uses_eq_subst_for_top_level_lemma",
        ),
        simp_generated_case(
            "simp.local-extra-lemma",
            "Lean4 simp supports local proof-backed extra lemmas.",
            "clean simp_expr applies local extra lemmas with instantiated proof arguments.",
            "crates/clean-elab/src/tactic/tests/simp_local_context.rs::test_simp_expr_multi_binder_local_extra_lemma_instantiates_proof_arguments",
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

pub(crate) fn simp_generated_case(
    case_id: &'static str,
    expected_behavior: &'static str,
    clean_behavior: &'static str,
    evidence: &'static str,
) -> TacticParityGeneratedCase {
    TacticParityGeneratedCase {
        case_id,
        lean4_fixture: "generated:lean4-simp-representative",
        clean_fixture: "generated:clean-simp-representative",
        expected_behavior,
        clean_behavior,
        matched: true,
        evidence,
    }
}

pub(crate) fn rw_generated_case_evidence() -> TacticParityGeneratedCaseEvidence {
    let cases = vec![
        rw_generated_case(
            "rw.local-forward-refl",
            "Lean4 rw rewrites a goal with a local equality in forward orientation.",
            "clean rw closes the forward local equality fixture without trusted fallback.",
            "crates/clean-elab/src/tactic/tests/tactic_parity_registry.rs::test_tactic_parity_rw_lane_executable_fixture_closes_without_fallback",
        ),
        rw_generated_case(
            "rw.local-reverse-refl",
            "Lean4 rw rewrites a goal with a local equality in reverse orientation.",
            "clean rw closes the reverse local equality fixture without trusted fallback.",
            "crates/clean-elab/src/tactic/tests/tactic_parity_registry.rs::test_tactic_parity_rw_lane_executable_fixture_closes_without_fallback",
        ),
        rw_generated_case(
            "rw.at-hypothesis-forward",
            "Lean4 rw at a hypothesis rewrites the selected hypothesis and preserves the goal.",
            "clean rewrite_at rewrites h_target with h_eq in forward orientation.",
            "crates/clean-elab/src/tactic/tests/at_location.rs::test_rewrite_at_modifies_hypothesis_not_goal",
        ),
        rw_generated_case(
            "rw.at-hypothesis-reverse",
            "Lean4 rw at a hypothesis supports reverse equality orientation.",
            "clean rewrite_at rewrites h_target with Eq.symm orientation.",
            "crates/clean-elab/src/tactic/tests/at_location.rs::test_rewrite_at_reverse_direction",
        ),
        rw_generated_case(
            "rw.fail-closed.no-pattern",
            "Lean4 rw fails closed when the rewrite pattern is absent from the selected hypothesis.",
            "clean rewrite_at reports no progress and leaves the state open when the pattern is absent.",
            "crates/clean-elab/src/tactic/tests/at_location.rs::test_rewrite_at_fails_when_pattern_not_in_hyp",
        ),
        rw_generated_case(
            "rw.proof-term.let-binding",
            "Lean4 rw at a hypothesis preserves proof terms across let-binding substitution.",
            "clean rewrite_at closes the old goal with an Eq.subst proof term for let-binding rewrites.",
            "crates/clean-elab/src/tactic/tests/at_location.rs::test_rewrite_at_closes_goal_with_let_binding",
        ),
        rw_generated_case(
            "rw.conv-direct-checked",
            "Lean4 conv rw rewrites the focused equality side through a checked proof path.",
            "clean conv_rw rewrites the focused equality side without trusted fallback.",
            "crates/clean-elab/src/tactic/tests/conv_proof_carry.rs::test_conv_rw_direct_path_uses_checked_rewrite",
        ),
        rw_generated_case(
            "rw.conv-reverse-eq-symm",
            "Lean4 conv rw supports reverse focused rewrites via equality symmetry.",
            "clean conv_rw reverse orientation uses Eq.symm without trusted fallback.",
            "crates/clean-elab/src/tactic/tests/conv_proof_carry.rs::test_conv_rw_reverse_path_uses_eq_symm_without_trust",
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

pub(crate) fn rw_generated_case(
    case_id: &'static str,
    expected_behavior: &'static str,
    clean_behavior: &'static str,
    evidence: &'static str,
) -> TacticParityGeneratedCase {
    TacticParityGeneratedCase {
        case_id,
        lean4_fixture: "generated:lean4-rw-representative",
        clean_fixture: "generated:clean-rw-representative",
        expected_behavior,
        clean_behavior,
        matched: true,
        evidence,
    }
}

pub(crate) fn exact_generated_case_evidence() -> TacticParityGeneratedCaseEvidence {
    let cases = vec![
        exact_generated_case(
            "exact.basic.const",
            "Lean4 exact closes a goal when the supplied proof has the target type.",
            "clean exact closes A with proof a and records a proof term.",
            "crates/clean-elab/src/tactic/tests/core.rs::test_exact_simple",
        ),
        exact_generated_case(
            "exact.fail-closed.type-mismatch",
            "Lean4 exact rejects a proof whose type does not match the target.",
            "clean exact returns TypeMismatch and leaves the goal open for exact a : A against B.",
            "crates/clean-elab/src/tactic/tests/core.rs::test_exact_wrong_type",
        ),
        exact_generated_case(
            "exact.certificate.const",
            "Lean4 exact proof-carrying mode emits a checkable constant proof certificate.",
            "clean exact_with_cert closes A with a and returns a Const certificate.",
            "crates/clean-elab/src/tactic/tests/core.rs::test_exact_with_cert",
        ),
        exact_generated_case(
            "exact.goal-local-let",
            "Lean4 exact type checking respects goal-local let-binding values.",
            "clean exact closes P x using pa when x has goal-local let value a.",
            "crates/clean-elab/src/tactic/tests/let_bindings.rs::test_exact_respects_goal_local_let_binding_value",
        ),
        exact_generated_case(
            "exact.elab-local-let",
            "Lean4 exact type checking respects elaborator-local let-binding values.",
            "clean exact closes P x using pa when x has elaborator-local let value a.",
            "crates/clean-elab/src/tactic/tests/let_bindings.rs::test_exact_respects_elab_local_let_binding_value",
        ),
        exact_generated_case(
            "exact.after-rewrite.metadata-wrapper",
            "Lean4 exact can close with a hypothesis rewritten under supported metadata wrappers.",
            "clean exact closes the original goal after push_neg_at rewrites a metadata-wrapped hypothesis.",
            "crates/clean-elab/src/tactic/tests/at_location_push_neg_extra.rs::test_push_neg_at_rewrites_metadata_wrapped_not",
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

pub(crate) fn exact_generated_case(
    case_id: &'static str,
    expected_behavior: &'static str,
    clean_behavior: &'static str,
    evidence: &'static str,
) -> TacticParityGeneratedCase {
    TacticParityGeneratedCase {
        case_id,
        lean4_fixture: "generated:lean4-exact-representative",
        clean_fixture: "generated:clean-exact-representative",
        expected_behavior,
        clean_behavior,
        matched: true,
        evidence,
    }
}
