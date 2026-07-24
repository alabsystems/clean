// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::super::proof_reconstruct::ReconstructionStats;
use super::*;
use clean_kernel::BinderInfo;

fn mk_raw_result(proof_term: Option<Expr>) -> ReconstructionResult {
    ReconstructionResult {
        proof_term,
        negated_goal_fvar: None,
        compound_witness_fvars: Vec::new(),
        derives_empty_clause: true,
        trust_subterm_count: 0,
        residual: ResidualTrustSummary::empty(),
        stats: ReconstructionStats::default(),
    }
}

fn mk_trusted_ay_pair() -> Expr {
    let trusted = || Expr::const_(Name::from_string("trustedAy"), vec![]);
    Expr::app(trusted(), trusted())
}

fn mk_trusted_ay_single() -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("trustedAy"), vec![]),
        Expr::const_(Name::from_string("TrustProp"), vec![]),
    )
}

#[test]
fn test_accept_kernel_reconstruction_candidate_rejects_compound_witnesses() {
    let mut raw = mk_raw_result(Some(Expr::const_(Name::from_string("proof"), vec![])));
    raw.compound_witness_fvars.push((
        FVarId::new(7),
        Expr::const_(Name::from_string("WitnessProp"), vec![]),
    ));

    assert!(
        accept_kernel_reconstruction_candidate(raw, TrustBudget::Unlimited).is_none(),
        "compound witness FVars should reject the raw reconstruction"
    );
}

#[test]
fn test_accept_kernel_reconstruction_candidate_rejects_non_empty_clause() {
    let mut raw = mk_raw_result(Some(Expr::const_(Name::from_string("proof"), vec![])));
    raw.derives_empty_clause = false;

    assert!(
        accept_kernel_reconstruction_candidate(raw, TrustBudget::Unlimited).is_none(),
        "non-empty final clauses should reject the raw reconstruction"
    );
}

#[test]
fn test_accept_kernel_reconstruction_candidate_recounts_embedded_trusted_ay_terms() {
    let proof_term = mk_trusted_ay_pair();
    let actual_trust_subterm_count = count_embedded_trusted_ay_terms(&proof_term);
    let mut raw = mk_raw_result(Some(proof_term));
    raw.trust_subterm_count = actual_trust_subterm_count.saturating_sub(1);

    let accepted = accept_kernel_reconstruction_candidate(raw, TrustBudget::Unlimited)
        .expect("closed empty-clause proof should still be accepted");
    assert_eq!(
        accepted.quality.trust_count(),
        actual_trust_subterm_count,
        "accepted candidate should recompute the exact trustedAy sub-term count"
    );
    assert_eq!(
        count_embedded_trusted_ay_terms(&accepted.refutation),
        actual_trust_subterm_count,
        "accepted refutation should preserve the trustedAy sub-terms it recounts"
    );
}

#[test]
fn test_reconstruction_quality_from_trust_count() {
    assert_eq!(
        ReconstructionQuality::from_trust_count(0),
        ReconstructionQuality::FullyVerified,
    );
    assert!(ReconstructionQuality::from_trust_count(0).is_fully_verified());
    assert_eq!(ReconstructionQuality::from_trust_count(0).trust_count(), 0);

    let partial = ReconstructionQuality::from_trust_count(3);
    assert_eq!(
        partial,
        ReconstructionQuality::PartiallyTrusted { trust_count: 3 }
    );
    assert!(!partial.is_fully_verified());
    assert_eq!(partial.trust_count(), 3);
}

#[test]
fn test_residual_trust_summary_primary_prioritizes_local_gaps() {
    let mut summary = ResidualTrustSummary::from_source(ResidualTrustSource::TheoryLemmaGeneric);
    summary.merge(ResidualTrustSummary::from_source(
        ResidualTrustSource::ArithmeticBoundary,
    ));
    summary.merge(ResidualTrustSummary::from_source(
        ResidualTrustSource::LocalReconstructionGap,
    ));

    assert_eq!(
        summary.primary,
        Some(ResidualTrustSource::LocalReconstructionGap)
    );
    assert_eq!(summary.total_steps(), 3);
}

#[test]
fn test_accept_kernel_reconstruction_candidate_preserves_residual_summary() {
    let proof_term = mk_trusted_ay_single();
    let mut raw = mk_raw_result(Some(proof_term.clone()));
    raw.trust_subterm_count = count_embedded_trusted_ay_terms(&proof_term);
    raw.residual = ResidualTrustSummary::from_source(ResidualTrustSource::AletheTrustStep);

    let accepted = accept_kernel_reconstruction_candidate(raw, TrustBudget::Unlimited)
        .expect("trusted proof should still be accepted");

    assert_eq!(
        accepted.residual,
        ResidualTrustSummary::from_source(ResidualTrustSource::AletheTrustStep)
    );
}

#[test]
fn test_accept_kernel_reconstruction_candidate_zeroes_residual_for_fully_verified() {
    let mut raw = mk_raw_result(Some(Expr::const_(Name::from_string("clean_proof"), vec![])));
    raw.residual = ResidualTrustSummary::from_source(ResidualTrustSource::LocalReconstructionGap);

    let accepted = accept_kernel_reconstruction_candidate(raw, TrustBudget::Unlimited)
        .expect("fully verified proof should still be accepted");

    assert_eq!(accepted.residual, ResidualTrustSummary::empty());
}

#[test]
fn test_trust_budget_zero_trust_rejects_partially_trusted() {
    let proof_term = mk_trusted_ay_pair();
    let mut raw = mk_raw_result(Some(proof_term.clone()));
    raw.trust_subterm_count = count_embedded_trusted_ay_terms(&proof_term);

    assert!(
        accept_kernel_reconstruction_candidate(raw, TrustBudget::ZeroTrust).is_none(),
        "ZeroTrust budget should reject proofs with trustedAy sub-terms"
    );
}

#[test]
fn test_trust_budget_zero_trust_accepts_fully_verified() {
    let raw = mk_raw_result(Some(Expr::const_(Name::from_string("clean_proof"), vec![])));

    let accepted = accept_kernel_reconstruction_candidate(raw, TrustBudget::ZeroTrust)
        .expect("ZeroTrust budget should accept fully verified proofs");
    assert!(accepted.quality.is_fully_verified());
}

#[test]
fn test_derive_primary_full_priority_chain_without_local_gaps() {
    let mut summary = ResidualTrustSummary::from_source(ResidualTrustSource::TheoryLemmaGeneric);
    assert_eq!(
        summary.primary,
        Some(ResidualTrustSource::TheoryLemmaGeneric),
        "Generic alone should be primary"
    );

    summary.add_source(ResidualTrustSource::TheoryLemmaArrayAxiom);
    assert_eq!(
        summary.primary,
        Some(ResidualTrustSource::TheoryLemmaArrayAxiom),
        "ArrayAxiom should outprioritize Generic"
    );

    summary.add_source(ResidualTrustSource::TheoryLemmaBvBitBlast);
    assert_eq!(
        summary.primary,
        Some(ResidualTrustSource::TheoryLemmaBvBitBlast),
        "BvBitBlast should outprioritize ArrayAxiom"
    );

    summary.add_source(ResidualTrustSource::AletheTrustStep);
    assert_eq!(
        summary.primary,
        Some(ResidualTrustSource::AletheTrustStep),
        "AletheTrustStep should outprioritize BvBitBlast"
    );

    summary.add_source(ResidualTrustSource::ArithmeticBoundary);
    assert_eq!(
        summary.primary,
        Some(ResidualTrustSource::ArithmeticBoundary),
        "ArithmeticBoundary should outprioritize AletheTrustStep"
    );

    summary.add_source(ResidualTrustSource::LocalReconstructionGap);
    assert_eq!(
        summary.primary,
        Some(ResidualTrustSource::LocalReconstructionGap),
        "LocalReconstructionGap should outprioritize everything"
    );

    assert_eq!(summary.total_steps(), 6, "all 6 sources should be counted");
}

#[test]
fn test_accept_kernel_reconstruction_candidate_returns_none_for_missing_proof_term() {
    let raw = mk_raw_result(None);
    assert!(
        accept_kernel_reconstruction_candidate(raw, TrustBudget::Unlimited).is_none(),
        "None proof_term should be rejected regardless of budget"
    );
}

#[test]
fn test_accept_with_residual_count_disagreement_still_accepts() {
    let proof_term = mk_trusted_ay_single();
    let exact = count_embedded_trusted_ay_terms(&proof_term);
    assert_eq!(exact, 1, "fixture should have exactly 1 trustedAy");

    let mut raw = mk_raw_result(Some(proof_term));
    raw.trust_subterm_count = exact;
    raw.residual = ResidualTrustSummary::empty();
    raw.residual
        .add_source(ResidualTrustSource::AletheTrustStep);
    raw.residual
        .add_source(ResidualTrustSource::ArithmeticBoundary);
    assert_eq!(raw.residual.total_steps(), 2);

    let accepted = accept_kernel_reconstruction_candidate(raw, TrustBudget::Unlimited)
        .expect("disagreement should warn but still accept");
    assert_eq!(
        accepted.quality.trust_count(),
        1,
        "should use exact recount, not residual total"
    );
    assert_eq!(accepted.residual.total_steps(), 2);
}

#[test]
fn test_accept_prunes_unreached_trusted_ay_counts_from_raw_stats() {
    let proof_term = mk_trusted_ay_single();
    let exact = count_embedded_trusted_ay_terms(&proof_term);
    assert_eq!(exact, 1, "fixture should have exactly 1 trustedAy");

    let mut raw = mk_raw_result(Some(proof_term));
    raw.trust_subterm_count = exact + 2;
    raw.residual = ResidualTrustSummary::from_source(ResidualTrustSource::AletheTrustStep);

    let accepted = accept_kernel_reconstruction_candidate(raw, TrustBudget::Unlimited)
        .expect("overreported raw trust counts should be trimmed by exact recount");
    assert_eq!(
        accepted.quality,
        ReconstructionQuality::PartiallyTrusted { trust_count: exact },
        "accepted quality should use the exact embedded trustedAy recount"
    );
    assert_eq!(
        accepted.residual,
        ResidualTrustSummary::from_source(ResidualTrustSource::AletheTrustStep),
        "matching residual metadata should survive the raw-count trim"
    );
}

#[test]
fn test_accept_zeroes_stale_residual_after_exact_recount_drops_to_zero() {
    let mut raw = mk_raw_result(Some(Expr::const_(Name::from_string("clean_proof"), vec![])));
    raw.trust_subterm_count = 2;
    raw.residual = ResidualTrustSummary::from_source(ResidualTrustSource::AletheTrustStep);
    raw.residual
        .add_source(ResidualTrustSource::LocalReconstructionGap);

    let accepted = accept_kernel_reconstruction_candidate(raw, TrustBudget::Unlimited)
        .expect("fully verified proof should still be accepted after exact recount");
    assert!(
        accepted.quality.is_fully_verified(),
        "exact recount should downgrade stale trusted metadata to FullyVerified"
    );
    assert_eq!(
        accepted.residual,
        ResidualTrustSummary::empty(),
        "fully verified acceptance must drop stale residual trust metadata"
    );
}

#[test]
fn test_residual_trust_summary_primary_is_stable_when_lower_priority_sources_arrive_later() {
    let mut summary = ResidualTrustSummary::from_source(ResidualTrustSource::ArithmeticBoundary);
    summary.add_source(ResidualTrustSource::TheoryLemmaGeneric);
    summary.add_source(ResidualTrustSource::AletheTrustStep);

    assert_eq!(
        summary.primary,
        Some(ResidualTrustSource::ArithmeticBoundary),
        "lower-priority sources must not demote an existing higher-priority primary"
    );

    let mut merged = ResidualTrustSummary::from_source(ResidualTrustSource::TheoryLemmaGeneric);
    merged.merge(ResidualTrustSummary::from_source(
        ResidualTrustSource::ArithmeticBoundary,
    ));
    assert_eq!(
        merged.primary,
        Some(ResidualTrustSource::ArithmeticBoundary),
        "merge order must converge to the same precedence winner"
    );
}

#[test]
fn test_trust_budget_at_most_threshold() {
    let proof_term = mk_trusted_ay_pair();
    let trust_count = count_embedded_trusted_ay_terms(&proof_term);
    assert!(trust_count > 0, "test fixture must have trust sub-terms");

    let mut raw = mk_raw_result(Some(proof_term.clone()));
    raw.trust_subterm_count = trust_count;
    let accepted = accept_kernel_reconstruction_candidate(raw, TrustBudget::AtMost(trust_count))
        .expect("AtMost(exact_count) should accept");
    assert_eq!(accepted.quality.trust_count(), trust_count);

    let mut raw2 = mk_raw_result(Some(proof_term));
    raw2.trust_subterm_count = trust_count;
    assert!(
        accept_kernel_reconstruction_candidate(raw2, TrustBudget::AtMost(trust_count - 1))
            .is_none(),
        "AtMost(count-1) should reject proofs exceeding the threshold"
    );
}

// --- Isolated count_embedded_trusted_ay_terms tests ---

#[test]
fn test_count_embedded_trusted_ay_terms_zero_for_non_trusted_consts() {
    let expr = Expr::apps(
        Expr::const_(Name::from_string("f"), vec![]),
        [
            Expr::const_(Name::from_string("a"), vec![]),
            Expr::const_(Name::from_string("b"), vec![]),
            Expr::const_(Name::from_string("c"), vec![]),
        ],
    );
    assert_eq!(
        count_embedded_trusted_ay_terms(&expr),
        0,
        "expression with no trustedAy constants should count as 0"
    );
}

#[test]
fn test_count_embedded_trusted_ay_terms_under_lambda() {
    // λ x : Prop . trustedAy
    let body = Expr::const_(Name::from_string("trustedAy"), vec![]);
    let expr = Expr::lam(BinderInfo::Default, Expr::prop(), body);
    assert_eq!(
        count_embedded_trusted_ay_terms(&expr),
        1,
        "trustedAy nested under a lambda should be counted"
    );
}

#[test]
fn test_count_embedded_trusted_ay_terms_in_lambda_type() {
    // λ x : trustedAy . clean
    let expr = Expr::lam(
        BinderInfo::Default,
        Expr::const_(Name::from_string("trustedAy"), vec![]),
        Expr::const_(Name::from_string("clean"), vec![]),
    );
    assert_eq!(
        count_embedded_trusted_ay_terms(&expr),
        1,
        "trustedAy nested in a lambda binder type should be counted"
    );
}

#[test]
fn test_count_embedded_trusted_ay_terms_under_pi() {
    // Π x : trustedAy . trustedAy
    let trusted = || Expr::const_(Name::from_string("trustedAy"), vec![]);
    let expr = Expr::pi(BinderInfo::Default, trusted(), trusted());
    assert_eq!(
        count_embedded_trusted_ay_terms(&expr),
        2,
        "trustedAy in both domain and codomain of Pi should count both"
    );
}

#[test]
fn test_count_embedded_trusted_ay_terms_under_let() {
    // let x : Prop := trustedAy in (trustedAy trustedAy)
    let trusted = || Expr::const_(Name::from_string("trustedAy"), vec![]);
    let body = Expr::app(trusted(), trusted());
    let expr = Expr::let_named(Name::anon(), Expr::prop(), trusted(), body, false);
    assert_eq!(
        count_embedded_trusted_ay_terms(&expr),
        3,
        "trustedAy in let value and body should all be counted"
    );
}

#[test]
fn test_count_embedded_trusted_ay_terms_in_let_type() {
    // let x : trustedAy := clean in clean
    let clean = || Expr::const_(Name::from_string("clean"), vec![]);
    let expr = Expr::let_named(
        Name::anon(),
        Expr::const_(Name::from_string("trustedAy"), vec![]),
        clean(),
        clean(),
        false,
    );
    assert_eq!(
        count_embedded_trusted_ay_terms(&expr),
        1,
        "trustedAy nested in a let annotation type should be counted"
    );
}

#[test]
fn test_count_embedded_trusted_ay_terms_deeply_nested() {
    // λ _ : Prop . λ _ : Prop . App(App(trustedAy, clean), trustedAy)
    let trusted = || Expr::const_(Name::from_string("trustedAy"), vec![]);
    let clean = Expr::const_(Name::from_string("clean"), vec![]);
    let inner = Expr::app(Expr::app(trusted(), clean), trusted());
    let expr = Expr::lam(
        BinderInfo::Default,
        Expr::prop(),
        Expr::lam(BinderInfo::Default, Expr::prop(), inner),
    );
    assert_eq!(
        count_embedded_trusted_ay_terms(&expr),
        2,
        "deeply nested trustedAy under multiple lambdas should all be found"
    );
}

// --- Multi-source merge test ---

#[test]
fn test_residual_trust_summary_merge_two_multi_source_summaries() {
    let mut a = ResidualTrustSummary::empty();
    a.add_source(ResidualTrustSource::ArithmeticBoundary);
    a.add_source(ResidualTrustSource::ArithmeticBoundary);
    a.add_source(ResidualTrustSource::TheoryLemmaGeneric);
    assert_eq!(a.arithmetic_boundary_steps, 2);
    assert_eq!(a.theory_generic_steps, 1);
    assert_eq!(a.total_steps(), 3);

    let mut b = ResidualTrustSummary::empty();
    b.add_source(ResidualTrustSource::AletheTrustStep);
    b.add_source(ResidualTrustSource::ArithmeticBoundary);
    b.add_source(ResidualTrustSource::LocalReconstructionGap);
    assert_eq!(b.total_steps(), 3);

    a.merge(b);
    assert_eq!(
        a.arithmetic_boundary_steps, 3,
        "should sum arithmetic steps"
    );
    assert_eq!(a.alethe_trust_steps, 1, "should sum alethe steps");
    assert_eq!(a.theory_generic_steps, 1, "should preserve generic steps");
    assert_eq!(a.local_gap_steps, 1, "should sum local gap steps");
    assert_eq!(a.theory_bv_bitblast_steps, 0, "absent sources stay 0");
    assert_eq!(a.theory_array_axiom_steps, 0, "absent sources stay 0");
    assert_eq!(a.total_steps(), 6, "total should be sum of all steps");
    assert_eq!(
        a.primary,
        Some(ResidualTrustSource::LocalReconstructionGap),
        "merged summary should re-derive primary by priority"
    );
}

// --- LocalReconstructionGap preservation through acceptance (#2922) ---

#[test]
fn test_accept_kernel_reconstruction_candidate_preserves_local_gap_residual() {
    let proof_term = mk_trusted_ay_single();
    let mut raw = mk_raw_result(Some(proof_term.clone()));
    raw.trust_subterm_count = count_embedded_trusted_ay_terms(&proof_term);
    raw.residual = ResidualTrustSummary::from_source(ResidualTrustSource::LocalReconstructionGap);

    let accepted = accept_kernel_reconstruction_candidate(raw, TrustBudget::Unlimited)
        .expect("partially trusted proof with local gap should be accepted");
    assert_eq!(
        accepted.residual,
        ResidualTrustSummary::from_source(ResidualTrustSource::LocalReconstructionGap),
        "LocalReconstructionGap residual must survive acceptance for partially-trusted proofs \
         so the selection layer can distinguish gap-carrying direct proofs from clean ones"
    );
}

// --- derive_primary None case ---

#[test]
fn test_residual_trust_summary_default_has_no_primary() {
    let summary = ResidualTrustSummary::empty();
    assert_eq!(
        summary.primary, None,
        "default summary with all-zero counters should have no primary"
    );
    assert_eq!(summary.total_steps(), 0);
}
