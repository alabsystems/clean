// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for trust enforcement gates: policy, visibility, transitivity,
//! contamination detection, and the full enforcement report.

use super::*;
use crate::trust::axiom_propagation::DependencyGraph;
use crate::types::{AxiomProfile, TrustLevel};

// -- TrustPolicy --

#[test]
fn test_strict_policy_blocks_all_gated() {
    let policy = TrustPolicy::strict();
    assert!(!policy.allow_axiomatized);
    assert!(!policy.allow_universe_inconsistent);
    assert!(!policy.allow_float_approx);
    assert!(!policy.allow_nn_abstraction);
    assert!(!policy.allow_trusted_oracle);
    assert!(!policy.allow_partially_axiomatized);
}

#[test]
fn test_permissive_policy_allows_all() {
    let policy = TrustPolicy::permissive();
    assert!(policy.allow_axiomatized);
    assert!(policy.allow_universe_inconsistent);
    assert!(policy.allow_float_approx);
    assert!(policy.allow_nn_abstraction);
    assert!(policy.allow_trusted_oracle);
    assert!(policy.allow_partially_axiomatized);
}

// -- Visibility checks --

#[test]
fn test_kernel_verified_pure_always_visible() {
    let enforcer = TrustEnforcer::strict();
    enforcer
        .check_visible(0, AxiomProfile::NONE, TrustLevel::KernelVerified)
        .expect("KernelVerified with no axioms should always be visible");
}

#[test]
fn test_certificate_replayed_visible() {
    let enforcer = TrustEnforcer::strict();
    enforcer
        .check_visible(0, AxiomProfile::NONE, TrustLevel::CertificateReplayed)
        .expect("CertificateReplayed should be visible under strict policy");
}

#[test]
fn test_axiom_dependent_visible() {
    let enforcer = TrustEnforcer::strict();
    enforcer
        .check_visible(0, AxiomProfile::CLASSICAL, TrustLevel::AxiomDependent)
        .expect("AxiomDependent with CLASSICAL should be visible (no gated bits)");
}

#[test]
fn test_partially_axiomatized_blocked_by_strict() {
    let enforcer = TrustEnforcer::strict();
    let err = enforcer
        .check_visible(0, AxiomProfile::NONE, TrustLevel::PartiallyAxiomatized)
        .unwrap_err();
    assert!(matches!(err, TrustEnforcementError::NotVisible { .. }));
}

#[test]
fn test_trusted_oracle_blocked_by_strict() {
    let enforcer = TrustEnforcer::strict();
    let err = enforcer
        .check_visible(0, AxiomProfile::SMT_ORACLE, TrustLevel::TrustedOracle)
        .unwrap_err();
    assert!(matches!(err, TrustEnforcementError::NotVisible { .. }));
}

#[test]
fn test_axiomatized_profile_blocked_by_strict() {
    let enforcer = TrustEnforcer::strict();
    let err = enforcer
        .check_visible(0, AxiomProfile::AXIOMATIZED, TrustLevel::AxiomDependent)
        .unwrap_err();
    assert!(matches!(err, TrustEnforcementError::NotVisible { .. }));
}

#[test]
fn test_universe_incon_blocked_by_strict() {
    let enforcer = TrustEnforcer::strict();
    let err = enforcer
        .check_visible(0, AxiomProfile::UNIVERSE_INCON, TrustLevel::AxiomDependent)
        .unwrap_err();
    assert!(matches!(err, TrustEnforcementError::NotVisible { .. }));
}

#[test]
fn test_float_approx_blocked_by_strict() {
    let enforcer = TrustEnforcer::strict();
    let err = enforcer
        .check_visible(0, AxiomProfile::FLOAT_APPROX, TrustLevel::AxiomDependent)
        .unwrap_err();
    assert!(matches!(err, TrustEnforcementError::NotVisible { .. }));
}

#[test]
fn test_nn_abstraction_blocked_by_strict() {
    let enforcer = TrustEnforcer::strict();
    let err = enforcer
        .check_visible(0, AxiomProfile::NN_ABSTRACTION, TrustLevel::AxiomDependent)
        .unwrap_err();
    assert!(matches!(err, TrustEnforcementError::NotVisible { .. }));
}

#[test]
fn test_permissive_allows_all_gated() {
    let enforcer = TrustEnforcer::permissive();
    enforcer
        .check_visible(0, AxiomProfile::AXIOMATIZED, TrustLevel::TrustedOracle)
        .expect("permissive should allow everything");
    enforcer
        .check_visible(
            1,
            AxiomProfile::UNIVERSE_INCON | AxiomProfile::FLOAT_APPROX,
            TrustLevel::PartiallyAxiomatized,
        )
        .expect("permissive should allow everything");
}

#[test]
fn test_custom_policy_allow_axiomatized_only() {
    let policy = TrustPolicy {
        allow_axiomatized: true,
        ..TrustPolicy::strict()
    };
    let enforcer = TrustEnforcer::new(policy);
    enforcer
        .check_visible(0, AxiomProfile::AXIOMATIZED, TrustLevel::AxiomDependent)
        .expect("axiomatized should be allowed");
    enforcer
        .check_visible(1, AxiomProfile::FLOAT_APPROX, TrustLevel::AxiomDependent)
        .unwrap_err();
}

// -- Visibility filtering --

#[test]
fn test_filter_visible_strict() {
    let enforcer = TrustEnforcer::strict();
    let constants = vec![
        (AxiomProfile::NONE, TrustLevel::KernelVerified), // 0: visible
        (AxiomProfile::CLASSICAL, TrustLevel::AxiomDependent), // 1: visible
        (AxiomProfile::AXIOMATIZED, TrustLevel::AxiomDependent), // 2: blocked
        (AxiomProfile::NONE, TrustLevel::CertificateReplayed), // 3: visible
        (AxiomProfile::SMT_ORACLE, TrustLevel::TrustedOracle), // 4: blocked
        (AxiomProfile::NONE, TrustLevel::PartiallyAxiomatized), // 5: blocked
    ];
    let visible = enforcer.filter_visible(&constants);
    assert_eq!(visible, vec![0, 1, 3]);
}

#[test]
fn test_filter_visible_permissive() {
    let enforcer = TrustEnforcer::permissive();
    let constants = vec![
        (AxiomProfile::NONE, TrustLevel::KernelVerified),
        (AxiomProfile::AXIOMATIZED, TrustLevel::TrustedOracle),
        (AxiomProfile::FLOAT_APPROX, TrustLevel::PartiallyAxiomatized),
    ];
    let visible = enforcer.filter_visible(&constants);
    assert_eq!(visible, vec![0, 1, 2]);
}

// -- Trust transitivity --

#[test]
fn test_effective_trust_level_no_deps() {
    let eff = TrustEnforcer::effective_trust_level(TrustLevel::KernelVerified, &[]);
    assert_eq!(eff, TrustLevel::KernelVerified);
}

#[test]
fn test_effective_trust_level_same_deps() {
    let eff = TrustEnforcer::effective_trust_level(
        TrustLevel::KernelVerified,
        &[TrustLevel::KernelVerified, TrustLevel::KernelVerified],
    );
    assert_eq!(eff, TrustLevel::KernelVerified);
}

#[test]
fn test_effective_trust_level_lowered_by_dep() {
    let eff = TrustEnforcer::effective_trust_level(
        TrustLevel::KernelVerified,
        &[TrustLevel::KernelVerified, TrustLevel::TrustedOracle],
    );
    assert_eq!(eff, TrustLevel::TrustedOracle);
}

#[test]
fn test_effective_trust_level_dep_higher_than_own() {
    let eff = TrustEnforcer::effective_trust_level(
        TrustLevel::TrustedOracle,
        &[TrustLevel::KernelVerified],
    );
    assert_eq!(eff, TrustLevel::TrustedOracle);
}

#[test]
fn test_enforce_transitivity_valid_graph() {
    let enforcer = TrustEnforcer::strict();
    let mut graph = DependencyGraph::new(3);
    graph.add_edge(1, 0).unwrap();
    graph.add_edge(2, 1).unwrap();
    let levels = vec![
        TrustLevel::KernelVerified,
        TrustLevel::AxiomDependent,
        TrustLevel::TrustedOracle,
    ];
    enforcer
        .enforce_transitivity(&graph, &levels)
        .expect("valid hierarchy should pass");
}

#[test]
fn test_enforce_transitivity_violation() {
    let enforcer = TrustEnforcer::strict();
    let mut graph = DependencyGraph::new(2);
    graph.add_edge(1, 0).unwrap();
    let levels = vec![TrustLevel::TrustedOracle, TrustLevel::KernelVerified];
    let err = enforcer.enforce_transitivity(&graph, &levels).unwrap_err();
    assert!(matches!(
        err,
        TrustEnforcementError::TransitivityViolation {
            idx: 1,
            dep_idx: 0,
            ..
        }
    ));
}

#[test]
fn test_enforce_transitivity_kernel_depends_on_axiom() {
    let enforcer = TrustEnforcer::strict();
    let mut graph = DependencyGraph::new(2);
    graph.add_edge(1, 0).unwrap();
    let levels = vec![TrustLevel::AxiomDependent, TrustLevel::KernelVerified];
    let err = enforcer.enforce_transitivity(&graph, &levels).unwrap_err();
    assert!(matches!(
        err,
        TrustEnforcementError::TransitivityViolation {
            claimed: TrustLevel::KernelVerified,
            dep_level: TrustLevel::AxiomDependent,
            ..
        }
    ));
}

// -- Contamination detection --

#[test]
fn test_detect_contamination_clean_graph() {
    let enforcer = TrustEnforcer::strict();
    let mut graph = DependencyGraph::new(2);
    graph.add_edge(1, 0).unwrap();
    let levels = vec![TrustLevel::KernelVerified, TrustLevel::KernelVerified];
    let profiles = vec![AxiomProfile::NONE, AxiomProfile::NONE];
    assert!(enforcer
        .detect_contamination(&graph, &levels, &profiles)
        .is_empty());
}

#[test]
fn test_detect_contamination_axiomatized_dep() {
    let enforcer = TrustEnforcer::strict();
    let mut graph = DependencyGraph::new(2);
    graph.add_edge(1, 0).unwrap();
    let levels = vec![TrustLevel::AxiomDependent, TrustLevel::KernelVerified];
    let profiles = vec![AxiomProfile::AXIOMATIZED, AxiomProfile::NONE];
    let v = enforcer.detect_contamination(&graph, &levels, &profiles);
    assert_eq!(v.len(), 1);
    assert!(matches!(
        &v[0],
        TrustEnforcementError::AxiomContamination {
            idx: 1,
            dep_idx: 0,
            ..
        }
    ));
}

#[test]
fn test_detect_contamination_transitive() {
    let enforcer = TrustEnforcer::strict();
    let mut graph = DependencyGraph::new(3);
    graph.add_edge(1, 0).unwrap();
    graph.add_edge(2, 1).unwrap();
    let levels = vec![
        TrustLevel::AxiomDependent,
        TrustLevel::AxiomDependent,
        TrustLevel::KernelVerified,
    ];
    let profiles = vec![
        AxiomProfile::AXIOMATIZED,
        AxiomProfile::NONE,
        AxiomProfile::NONE,
    ];
    let v = enforcer.detect_contamination(&graph, &levels, &profiles);
    assert!(!v.is_empty(), "should detect transitive contamination");
    assert!(v.iter().any(|e| matches!(
        e,
        TrustEnforcementError::AxiomContamination {
            idx: 2,
            dep_idx: 0,
            ..
        }
    )));
}

#[test]
fn test_detect_contamination_non_kernel_not_flagged() {
    let enforcer = TrustEnforcer::strict();
    let mut graph = DependencyGraph::new(2);
    graph.add_edge(1, 0).unwrap();
    let levels = vec![TrustLevel::AxiomDependent, TrustLevel::AxiomDependent];
    let profiles = vec![AxiomProfile::AXIOMATIZED, AxiomProfile::NONE];
    assert!(enforcer
        .detect_contamination(&graph, &levels, &profiles)
        .is_empty());
}

// -- Full enforcement report --

#[test]
fn test_enforce_all_clean() {
    let enforcer = TrustEnforcer::strict();
    let graph = DependencyGraph::new(2);
    let levels = vec![TrustLevel::KernelVerified, TrustLevel::KernelVerified];
    let profiles = vec![AxiomProfile::NONE, AxiomProfile::NONE];
    let report = enforcer.enforce_all(&graph, &levels, &profiles);
    assert!(report.is_clean);
    assert_eq!(report.total_constants, 2);
    assert_eq!(report.visible_count, 2);
}

#[test]
fn test_enforce_all_with_violations() {
    let enforcer = TrustEnforcer::strict();
    let mut graph = DependencyGraph::new(3);
    graph.add_edge(2, 0).unwrap();
    let levels = vec![
        TrustLevel::TrustedOracle,
        TrustLevel::KernelVerified,
        TrustLevel::KernelVerified,
    ];
    let profiles = vec![
        AxiomProfile::SMT_ORACLE,
        AxiomProfile::NONE,
        AxiomProfile::NONE,
    ];
    let report = enforcer.enforce_all(&graph, &levels, &profiles);
    assert!(!report.is_clean);
    assert!(!report.visibility_violations.is_empty());
    assert!(report.transitivity_violation.is_some());
}

// -- Bypass and transitivity property proofs --

#[test]
fn test_trust_gate_cannot_bypass_without_optin() {
    let enforcer = TrustEnforcer::strict();
    let gated = [
        AxiomProfile::AXIOMATIZED,
        AxiomProfile::UNIVERSE_INCON,
        AxiomProfile::FLOAT_APPROX,
        AxiomProfile::NN_ABSTRACTION,
    ];
    for (i, &p) in gated.iter().enumerate() {
        assert!(
            enforcer
                .check_visible(i as u32, p, TrustLevel::AxiomDependent)
                .is_err(),
            "{:?} should be blocked under strict",
            p
        );
    }
    for (i, &t) in [TrustLevel::PartiallyAxiomatized, TrustLevel::TrustedOracle]
        .iter()
        .enumerate()
    {
        assert!(
            enforcer
                .check_visible(i as u32, AxiomProfile::NONE, t)
                .is_err(),
            "{:?} should be blocked under strict",
            t
        );
    }
}

#[test]
fn test_trust_transitivity_property() {
    let all = [
        TrustLevel::KernelVerified,
        TrustLevel::AxiomDependent,
        TrustLevel::CertificateReplayed,
        TrustLevel::PartiallyAxiomatized,
        TrustLevel::TrustedOracle,
    ];
    for &own in &all {
        for &dep in &all {
            let eff = TrustEnforcer::effective_trust_level(own, &[dep]);
            let own_r = trust_level_rank(own);
            let dep_r = trust_level_rank(dep);
            let eff_r = trust_level_rank(eff);
            assert_eq!(
                eff_r,
                own_r.max(dep_r),
                "effective({:?}, [{:?}]) rank {} != max({}, {})",
                own,
                dep,
                eff_r,
                own_r,
                dep_r
            );
        }
    }
}
