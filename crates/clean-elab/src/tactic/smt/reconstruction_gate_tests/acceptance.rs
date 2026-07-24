// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Acceptance and trust-accounting ratchets for
//! `finalize_kernel_reconstruction_candidate(...)`.

#[cfg(feature = "ay-smt")]
use super::super::*;
#[cfg(feature = "ay-smt")]
use super::support::*;
#[cfg(feature = "ay-smt")]
use clean_auto::bridge::ay_contract::test_utils::{
    kernel_reconstruction_candidate, residual_trust_summary_from_source,
};
#[cfg(feature = "ay-smt")]
use clean_kernel::name::Name;
#[cfg(feature = "ay-smt")]
use clean_kernel::Expr;
#[cfg(feature = "ay-smt")]
use serial_test::serial;

#[cfg(feature = "ay-smt")]
#[test]
#[serial]
fn test_finalize_kernel_reconstruction_candidate_records_success_counter() {
    let (env, p) = mk_prop_hyp_env(false);
    let neg_p = mk_negated(&p);
    let neg_fvar = clean_kernel::FVarId::new(123);
    let refutation = mk_absurd_false(
        &p,
        &Expr::const_(Name::from_string("hp"), vec![]),
        &Expr::fvar(neg_fvar),
    );

    reset_ay_reconstruction_success_counter();
    let (proof, trust_count, _residual) =
        reconstruction_gate::finalize_kernel_reconstruction_candidate(
            &p,
            &neg_p,
            mk_candidate(refutation, Some(neg_fvar), 0),
            &[],
        );

    assert_eq!(
        trust_count, 0,
        "fully-verified proof should have zero trust sub-terms"
    );
    assert_eq!(
        ay_reconstruction_success_count(),
        1,
        "accepted direct ay candidates should increment the success counter"
    );

    assert_inferred_type(
        &env,
        &proof,
        &p,
        "finalized refutation should prove the original goal",
    );
}

#[cfg(feature = "ay-smt")]
#[test]
#[serial]
fn test_finalize_kernel_reconstruction_candidate_preserves_trust_subterms() {
    let (env, p) = mk_prop_hyp_env(true);
    let neg_p = mk_negated(&p);
    let neg_fvar = clean_kernel::FVarId::new(456);
    let trusted_p = mk_trusted_ay_proof(&env, &p);
    let refutation = mk_absurd_false(&p, &trusted_p, &Expr::fvar(neg_fvar));

    reset_ay_reconstruction_success_counter();
    let (proof, trust_count, _residual) =
        reconstruction_gate::finalize_kernel_reconstruction_candidate(
            &p,
            &neg_p,
            mk_candidate(refutation, Some(neg_fvar), 1),
            &[],
        );

    assert_eq!(
        trust_count, 1,
        "gate should return the exact embedded trustedAy count from the accepted proof term"
    );
    assert_eq!(
        trusted_subterms::count_embedded_trusted_ay_terms(&proof),
        trust_count,
        "wrapped goal proof should preserve the accepted proof term's exact trust debt"
    );
    assert_eq!(
        ay_reconstruction_success_count(),
        1,
        "partially-verified proofs should increment the success counter"
    );

    assert_inferred_type(
        &env,
        &proof,
        &p,
        "finalized proof should prove the original goal",
    );
}

#[cfg(feature = "ay-smt")]
#[test]
#[serial]
fn test_finalize_kernel_reconstruction_candidate_uses_exact_trust_count() {
    let (env, p) = mk_prop_env(true);
    let neg_p = mk_negated(&p);
    let neg_fvar = clean_kernel::FVarId::new(789);
    let trusted_p = mk_trusted_ay_proof(&env, &p);
    let refutation = mk_absurd_false(&p, &trusted_p, &Expr::fvar(neg_fvar));

    let (proof, trust_count, _residual) =
        reconstruction_gate::finalize_kernel_reconstruction_candidate(
            &p,
            &neg_p,
            mk_candidate(refutation, Some(neg_fvar), 1),
            &[],
        );

    assert_eq!(
        trust_count, 1,
        "accepted candidates should keep the exact trust debt computed in clean-auto"
    );
    assert_eq!(
        trusted_subterms::count_embedded_trusted_ay_terms(&proof),
        trust_count,
        "wrapped goal proof should carry only the accepted proof term's reachable trust debt"
    );
}

/// Regression: the typed `ResidualTrustSummary` survives the reconstruction
/// gate without being recomputed or defaulted. Part of #2618.
#[cfg(feature = "ay-smt")]
#[test]
#[serial]
fn test_finalize_kernel_reconstruction_candidate_preserves_residual_summary() {
    use clean_auto::bridge::ay_contract::ResidualTrustSource;

    let (env, p) = mk_prop_hyp_env(true);
    let neg_p = mk_negated(&p);
    let neg_fvar = clean_kernel::FVarId::new(999);
    let trusted_p = mk_trusted_ay_proof(&env, &p);
    let refutation = mk_absurd_false(&p, &trusted_p, &Expr::fvar(neg_fvar));

    let expected_residual =
        residual_trust_summary_from_source(ResidualTrustSource::AletheTrustStep);
    let candidate = kernel_reconstruction_candidate(
        refutation,
        Some(neg_fvar),
        clean_auto::bridge::ay_contract::ReconstructionQuality::from_trust_count(1),
        expected_residual,
    );

    let (_proof, trust_count, residual) =
        reconstruction_gate::finalize_kernel_reconstruction_candidate(&p, &neg_p, candidate, &[]);

    assert_eq!(trust_count, 1);
    assert_eq!(
        residual, expected_residual,
        "reconstruction gate must preserve the typed residual summary from the accepted candidate"
    );
    assert_eq!(
        residual.primary(),
        Some(ResidualTrustSource::AletheTrustStep),
        "primary residual source should survive the gate unchanged"
    );
    assert_eq!(residual.alethe_trust_steps(), 1);
}
