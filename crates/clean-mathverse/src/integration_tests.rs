// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Cross-importer integration tests for the Mathverse Library.
//!
//! Tests that exercise multiple modules together: trust pipeline, axiom
//! propagation, audit reporting, verification suite, certificate replay,
//! bulk import, and statistics.

#[cfg(test)]
mod tests {
    use crate::bulk_import::{BulkImportConfig, BulkImporter, ImportedConstant};
    use crate::progverif::cert_replay::{
        CertReplayResult, CertReplayStrategy, Certificate, CertificateFormat, NullReplayStrategy,
    };
    use crate::stats::{ImportStats, MathverseSummary};
    use crate::trust::audit_report::{AuditFinding, AuditReportBuilder, AuditSeverity};
    use crate::trust::axiom_propagation::DependencyGraph;
    use crate::trust::graph_gate::{TrainingExportGate, TrustGate};
    use crate::trust::verification::VerificationSuite;
    use crate::types::{AxiomProfile, Provenance, SourceSystem, TrustLevel};

    // ── Convenience constants ──

    const HOL_BASE: AxiomProfile = AxiomProfile(
        AxiomProfile::CLASSICAL.0 | AxiomProfile::EXTENSIONALITY.0 | AxiomProfile::HOL_EMBEDDING.0,
    );

    const MIZAR_BASE: AxiomProfile =
        AxiomProfile(AxiomProfile::CLASSICAL.0 | AxiomProfile::MIZAR_SOFT_TYPE.0);

    // ── Helper ──

    fn make_constant(
        name: &str,
        source: SourceSystem,
        profile: AxiomProfile,
        trust: TrustLevel,
    ) -> ImportedConstant {
        ImportedConstant {
            name: name.to_owned(),
            source,
            axiom_profile: profile,
            trust_level: trust,
            provenance: Provenance {
                source,
                original_name: name.to_owned(),
                source_file: None,
                axiom_profile: profile,
            },
            dependencies: Vec::new(),
        }
    }

    // ========================================================================
    // 1. Trust pipeline integration
    // ========================================================================

    #[test]
    fn test_full_trust_pipeline() {
        // Build a mixed-source dependency graph:
        // 0: Lean4 kernel-verified (no axioms)
        // 1: HOL Light (classical + ext + HOL)
        // 2: Mizar (classical + mizar_soft_type), depends on 0
        // 3: Dafny (SMT oracle), depends on 1
        let mut graph = DependencyGraph::new(4);
        graph.set_initial_profile(0, AxiomProfile::NONE).unwrap();
        graph.set_initial_profile(1, HOL_BASE).unwrap();
        graph.set_initial_profile(2, MIZAR_BASE).unwrap();
        graph
            .set_initial_profile(3, AxiomProfile::SMT_ORACLE)
            .unwrap();
        graph.add_edge(2, 0).unwrap();
        graph.add_edge(3, 1).unwrap();

        graph.propagate().unwrap();
        assert!(graph.verify_invariant().is_ok());

        // Node 2 inherits nothing new from node 0 (NONE)
        assert!(graph.profile(2).contains(AxiomProfile::CLASSICAL));
        assert!(graph.profile(2).contains(AxiomProfile::MIZAR_SOFT_TYPE));

        // Node 3 inherits HOL_BASE from node 1
        assert!(graph.profile(3).contains(AxiomProfile::SMT_ORACLE));
        assert!(graph.profile(3).contains(AxiomProfile::CLASSICAL));
        assert!(graph.profile(3).contains(AxiomProfile::HOL_EMBEDDING));

        // Trust gate audit: trust levels descend along edges
        let trust_levels = [
            TrustLevel::KernelVerified,
            TrustLevel::CertificateReplayed,
            TrustLevel::PartiallyAxiomatized,
            TrustLevel::TrustedOracle,
        ];
        let gate = TrustGate::default_policy();
        let violations = gate.audit_graph(&graph, &trust_levels);
        assert!(violations.is_empty(), "violations: {:?}", violations);
    }

    #[test]
    fn test_trust_violation_detection() {
        // KernelVerified depending on TrustedOracle = violation
        let mut graph = DependencyGraph::new(2);
        graph
            .set_initial_profile(0, AxiomProfile::SMT_ORACLE)
            .unwrap();
        graph.set_initial_profile(1, AxiomProfile::NONE).unwrap();
        graph.add_edge(1, 0).unwrap();
        graph.propagate().unwrap();

        let trust_levels = [TrustLevel::TrustedOracle, TrustLevel::KernelVerified];
        let gate = TrustGate::default_policy();
        let violations = gate.audit_graph(&graph, &trust_levels);
        assert_eq!(violations.len(), 1);
        assert_eq!(violations[0].parent_trust, TrustLevel::KernelVerified);
        assert_eq!(violations[0].child_trust, TrustLevel::TrustedOracle);
    }

    #[test]
    fn test_trust_pipeline_with_audit_report() {
        let mut graph = DependencyGraph::new(3);
        graph.set_initial_profile(0, AxiomProfile::NONE).unwrap();
        graph.set_initial_profile(1, HOL_BASE).unwrap();
        graph
            .set_initial_profile(2, AxiomProfile::SMT_ORACLE)
            .unwrap();
        graph.add_edge(2, 1).unwrap();
        graph.propagate().unwrap();

        let trust_levels = [
            TrustLevel::KernelVerified,
            TrustLevel::CertificateReplayed,
            TrustLevel::TrustedOracle,
        ];
        let gate = TrustGate::default_policy();
        let violations = gate.audit_graph(&graph, &trust_levels);
        assert!(violations.is_empty());

        // Build audit report for same graph
        let mut builder = AuditReportBuilder::new();
        builder.add_constant(TrustLevel::KernelVerified, "Lean4", graph.profile(0));
        builder.add_constant(
            TrustLevel::CertificateReplayed,
            "HolLight",
            graph.profile(1),
        );
        builder.add_constant(TrustLevel::TrustedOracle, "Dafny", graph.profile(2));
        let report = builder.build();
        assert_eq!(report.total_constants, 3);
        assert!(report.is_clean());
        assert_eq!(report.exportable_for_training, 1);
        let summary = report.summary();
        assert!(summary.contains("CLEAN"));
    }

    // ========================================================================
    // 2. Axiom profile consistency
    // ========================================================================

    #[test]
    fn test_hol_base_profile() {
        assert!(HOL_BASE.contains(AxiomProfile::CLASSICAL));
        assert!(HOL_BASE.contains(AxiomProfile::EXTENSIONALITY));
        assert!(HOL_BASE.contains(AxiomProfile::HOL_EMBEDDING));
        assert!(!HOL_BASE.contains(AxiomProfile::MIZAR_SOFT_TYPE));
        assert_eq!(HOL_BASE.axiom_count(), 3);
    }

    #[test]
    fn test_mizar_base_profile() {
        assert!(MIZAR_BASE.contains(AxiomProfile::CLASSICAL));
        assert!(MIZAR_BASE.contains(AxiomProfile::MIZAR_SOFT_TYPE));
        assert!(!MIZAR_BASE.contains(AxiomProfile::HOL_EMBEDDING));
        assert_eq!(MIZAR_BASE.axiom_count(), 2);
    }

    #[test]
    fn test_smt_oracle_profile_for_unverified_progverif() {
        let profile = AxiomProfile::SMT_ORACLE;
        assert!(profile.contains(AxiomProfile::SMT_ORACLE));
        assert!(!profile.contains(AxiomProfile::CLASSICAL));
        assert!(!profile.is_kernel_verified());
        assert_eq!(profile.axiom_count(), 1);
    }

    #[test]
    fn test_cross_system_profile_union() {
        let hol = AxiomProfile::CLASSICAL | AxiomProfile::HOL_EMBEDDING;
        let mizar = AxiomProfile::CLASSICAL | AxiomProfile::MIZAR_SOFT_TYPE;
        let combined = hol | mizar;
        assert!(combined.contains(AxiomProfile::CLASSICAL));
        assert!(combined.contains(AxiomProfile::HOL_EMBEDDING));
        assert!(combined.contains(AxiomProfile::MIZAR_SOFT_TYPE));
        // CLASSICAL shared, so total unique bits = 3
        assert_eq!(combined.axiom_count(), 3);
    }

    #[test]
    fn test_propagation_preserves_profile_consistency() {
        // HOL node depending on Mizar node should accumulate both profiles
        let mut graph = DependencyGraph::new(2);
        graph.set_initial_profile(0, MIZAR_BASE).unwrap();
        graph.set_initial_profile(1, HOL_BASE).unwrap();
        graph.add_edge(1, 0).unwrap(); // HOL depends on Mizar
        graph.propagate().unwrap();

        let propagated = graph.profile(1);
        assert!(propagated.contains(AxiomProfile::CLASSICAL));
        assert!(propagated.contains(AxiomProfile::EXTENSIONALITY));
        assert!(propagated.contains(AxiomProfile::HOL_EMBEDDING));
        assert!(propagated.contains(AxiomProfile::MIZAR_SOFT_TYPE));
        assert_eq!(propagated.axiom_count(), 4);
    }

    // ========================================================================
    // 3. TrustLevel hierarchy (all 25 combinations)
    // ========================================================================

    #[test]
    fn test_trust_level_ordering() {
        assert!(TrustLevel::KernelVerified < TrustLevel::AxiomDependent);
        assert!(TrustLevel::AxiomDependent < TrustLevel::CertificateReplayed);
        assert!(TrustLevel::CertificateReplayed < TrustLevel::PartiallyAxiomatized);
        assert!(TrustLevel::PartiallyAxiomatized < TrustLevel::TrustedOracle);
    }

    #[test]
    fn test_trust_gate_all_25_combinations() {
        let gate = TrustGate::default_policy();
        let levels = [
            TrustLevel::KernelVerified,
            TrustLevel::AxiomDependent,
            TrustLevel::CertificateReplayed,
            TrustLevel::PartiallyAxiomatized,
            TrustLevel::TrustedOracle,
        ];

        // Default policy: parent can depend on child iff child <= parent
        for &parent in &levels {
            for &child in &levels {
                let result = gate.check_dependency(parent, child);
                let should_allow = child <= parent;
                assert_eq!(
                    result.is_ok(),
                    should_allow,
                    "parent={:?} child={:?}: expected {}, got {}",
                    parent,
                    child,
                    should_allow,
                    result.is_ok()
                );
            }
        }
    }

    #[test]
    fn test_training_gate_strict() {
        // Only KernelVerified + NONE profile should be exportable
        let cases = [
            (AxiomProfile::NONE, TrustLevel::KernelVerified, true),
            (AxiomProfile::CLASSICAL, TrustLevel::KernelVerified, false),
            (AxiomProfile::NONE, TrustLevel::AxiomDependent, false),
            (AxiomProfile::NONE, TrustLevel::CertificateReplayed, false),
            (AxiomProfile::NONE, TrustLevel::PartiallyAxiomatized, false),
            (AxiomProfile::NONE, TrustLevel::TrustedOracle, false),
            (AxiomProfile::SMT_ORACLE, TrustLevel::TrustedOracle, false),
            (HOL_BASE, TrustLevel::CertificateReplayed, false),
            (MIZAR_BASE, TrustLevel::PartiallyAxiomatized, false),
        ];
        for (profile, trust, expected) in cases {
            assert_eq!(
                TrainingExportGate::can_export_for_training(profile, trust),
                expected,
                "profile={:?} trust={:?}",
                profile,
                trust
            );
        }
    }

    #[test]
    fn test_training_export_gate_filter_and_count() {
        let pairs = [
            (AxiomProfile::NONE, TrustLevel::KernelVerified),
            (HOL_BASE, TrustLevel::CertificateReplayed),
            (AxiomProfile::NONE, TrustLevel::KernelVerified),
            (AxiomProfile::SMT_ORACLE, TrustLevel::TrustedOracle),
        ];
        let exportable = TrainingExportGate::filter_exportable(&pairs);
        assert_eq!(exportable, vec![0, 2]);
        assert_eq!(TrainingExportGate::count_exportable(&pairs), 2);
    }

    // ========================================================================
    // 4. CertReplayStrategy integration
    // ========================================================================

    #[test]
    fn test_null_replay_strategy_returns_trusted_oracle() {
        let strategy = NullReplayStrategy;
        let cert = Certificate::new(CertificateFormat::SmtLib2, b"(proof ...)".to_vec(), "z3");
        let result = strategy.replay(&cert).expect("null always succeeds");
        assert!(result.verified);
        assert_eq!(result.trust_level, TrustLevel::TrustedOracle);
        assert!(result.axiom_profile.contains(AxiomProfile::SMT_ORACLE));
    }

    #[test]
    fn test_cert_replay_verified_constructor() {
        let result =
            CertReplayResult::verified(AxiomProfile::SAT_CERT, TrustLevel::CertificateReplayed, 42);
        assert!(result.verified);
        assert!(result.axiom_profile.contains(AxiomProfile::SAT_CERT));
        assert_eq!(result.trust_level, TrustLevel::CertificateReplayed);
        assert_eq!(result.replay_time_us, 42);
        assert!(result.diagnostics.is_empty());
    }

    #[test]
    fn test_cert_replay_failed_constructor() {
        let result = CertReplayResult::failed("bad proof step at index 7", 100);
        assert!(!result.verified);
        assert_eq!(result.trust_level, TrustLevel::TrustedOracle);
        assert_eq!(result.axiom_profile, AxiomProfile::NONE);
        assert_eq!(result.diagnostics.len(), 1);
    }

    #[test]
    fn test_certificate_with_metadata() {
        let cert = Certificate::new(CertificateFormat::Drat, vec![0xDE, 0xAD], "cadical")
            .with_metadata("version", "1.9.5")
            .with_metadata("solver", "cadical");
        assert_eq!(cert.byte_len(), 2);
        assert!(!cert.is_empty());
        assert_eq!(
            cert.metadata.get("version").map(String::as_str),
            Some("1.9.5")
        );
    }

    #[test]
    fn test_null_replay_all_formats() {
        let strategy = NullReplayStrategy;
        let formats = [
            CertificateFormat::SmtLib2,
            CertificateFormat::Drat,
            CertificateFormat::Lrat,
            CertificateFormat::AletheLF,
            CertificateFormat::Lfsc,
            CertificateFormat::Custom("boogie".into()),
        ];
        for format in formats {
            let cert = Certificate::new(format.clone(), vec![1, 2, 3], "tool");
            let result = strategy.replay(&cert).unwrap();
            assert!(
                result.verified,
                "NullReplayStrategy should accept {:?}",
                format
            );
            assert_eq!(result.trust_level, TrustLevel::TrustedOracle);
        }
    }

    #[test]
    fn test_cert_replay_feeds_into_audit() {
        let strategy = NullReplayStrategy;
        let cert = Certificate::new(CertificateFormat::SmtLib2, b"(proof ...)".to_vec(), "z3");
        let replay_result = strategy.replay(&cert).unwrap();

        // Use replay result to build audit
        let mut builder = AuditReportBuilder::new();
        builder.add_constant(
            replay_result.trust_level,
            "Dafny",
            replay_result.axiom_profile,
        );
        let report = builder.build();
        assert_eq!(report.total_constants, 1);
        assert_eq!(report.by_trust_level[&TrustLevel::TrustedOracle], 1);
        assert_eq!(report.exportable_for_training, 0);
    }

    // ========================================================================
    // 5. Multi-source audit scenario (10 constants, 5 systems)
    // ========================================================================

    #[test]
    fn test_multi_source_10_constants_5_systems() {
        let config = BulkImportConfig::builder().enforce_trust_gate(true).build();
        let mut importer = BulkImporter::new(config);

        // Lean4: 3 kernel-verified
        importer
            .add_constant(make_constant(
                "Nat.zero",
                SourceSystem::Lean4,
                AxiomProfile::NONE,
                TrustLevel::KernelVerified,
            ))
            .unwrap();
        importer
            .add_constant(make_constant(
                "Nat.succ",
                SourceSystem::Lean4,
                AxiomProfile::NONE,
                TrustLevel::KernelVerified,
            ))
            .unwrap();
        importer
            .add_constant(make_constant(
                "Nat.add_comm",
                SourceSystem::Lean4,
                AxiomProfile::NONE,
                TrustLevel::KernelVerified,
            ))
            .unwrap();

        // HOL Light: 2 certificate-replayed
        importer
            .add_constant(make_constant(
                "HOL.TrueI",
                SourceSystem::HolLight,
                HOL_BASE,
                TrustLevel::CertificateReplayed,
            ))
            .unwrap();
        importer
            .add_constant(make_constant(
                "HOL.FalseE",
                SourceSystem::HolLight,
                HOL_BASE,
                TrustLevel::CertificateReplayed,
            ))
            .unwrap();

        // Mizar: 2 partially axiomatized
        importer
            .add_constant(make_constant(
                "HIDDEN_1",
                SourceSystem::Mizar,
                MIZAR_BASE,
                TrustLevel::PartiallyAxiomatized,
            ))
            .unwrap();
        importer
            .add_constant(make_constant(
                "HIDDEN_2",
                SourceSystem::Mizar,
                MIZAR_BASE,
                TrustLevel::PartiallyAxiomatized,
            ))
            .unwrap();

        // Dafny: 2 trusted oracle
        importer
            .add_constant(make_constant(
                "Dafny.vc_1",
                SourceSystem::Dafny,
                AxiomProfile::SMT_ORACLE,
                TrustLevel::TrustedOracle,
            ))
            .unwrap();
        importer
            .add_constant(make_constant(
                "Dafny.vc_2",
                SourceSystem::Dafny,
                AxiomProfile::SMT_ORACLE,
                TrustLevel::TrustedOracle,
            ))
            .unwrap();

        // Coq: 1 axiom-dependent
        importer
            .add_constant(make_constant(
                "Coq.em_axiom_user",
                SourceSystem::Coq,
                AxiomProfile::CLASSICAL,
                TrustLevel::AxiomDependent,
            ))
            .unwrap();

        let result = importer.finalize().unwrap();
        assert_eq!(result.total_constants, 10);
        assert!(result.propagation_ok);
        assert!(result.trust_violations.is_empty());
        assert_eq!(result.exportable_count, 3); // 3 Lean4 kernel-verified NONE
        assert_eq!(result.source_count(), 5);
        assert!(result.is_clean());

        // Verify audit report details
        let report = &result.audit_report;
        assert_eq!(report.total_constants, 10);
        assert_eq!(report.exportable_for_training, 3);
        assert!(report.kernel_verified_fraction > 0.29);
        assert!(report.kernel_verified_fraction < 0.31);
        let summary = report.summary();
        assert!(summary.contains("CLEAN"));
    }

    // ========================================================================
    // 6. VerificationSuite integration
    // ========================================================================

    #[test]
    fn test_verification_suite_run_all_valid() {
        let mut graph = DependencyGraph::new(4);
        graph.set_initial_profile(0, AxiomProfile::NONE).unwrap();
        graph.set_initial_profile(1, AxiomProfile::NONE).unwrap();
        graph
            .set_initial_profile(2, AxiomProfile::CLASSICAL)
            .unwrap();
        graph
            .set_initial_profile(3, AxiomProfile::SMT_ORACLE)
            .unwrap();
        graph.add_edge(1, 0).unwrap();
        graph.add_edge(2, 0).unwrap();
        graph.add_edge(3, 2).unwrap();
        graph.propagate().unwrap();

        let trust_levels = [
            TrustLevel::KernelVerified,
            TrustLevel::KernelVerified,
            TrustLevel::AxiomDependent,
            TrustLevel::TrustedOracle,
        ];
        let gate = TrustGate::default_policy();
        let suite = VerificationSuite::new();
        let results = suite.run_all(&graph, &trust_levels, &gate);

        assert_eq!(results.len(), 5);
        for result in &results {
            assert!(
                result.passed,
                "{:?} failed: {}",
                result.property, result.evidence
            );
        }
    }

    #[test]
    fn test_verification_suite_detects_idempotency_failure() {
        // Build graph but skip propagation -> idempotency check should fail
        let mut graph = DependencyGraph::new(2);
        graph
            .set_initial_profile(0, AxiomProfile::CLASSICAL)
            .unwrap();
        graph.add_edge(1, 0).unwrap();
        // Intentionally skip propagation

        let trust_levels = [TrustLevel::AxiomDependent, TrustLevel::AxiomDependent];
        let gate = TrustGate::default_policy();
        let suite = VerificationSuite::new();
        let results = suite.run_all(&graph, &trust_levels, &gate);

        let failed: Vec<_> = results.iter().filter(|r| !r.passed).collect();
        assert!(
            !failed.is_empty(),
            "unpropagated graph should fail at least one property"
        );
    }

    #[test]
    fn test_verification_suite_monotonicity_on_diamond() {
        // Diamond graph: 0 <- 1, 0 <- 2, 1 <- 3, 2 <- 3
        let mut graph = DependencyGraph::new(4);
        graph
            .set_initial_profile(0, AxiomProfile::CLASSICAL)
            .unwrap();
        graph
            .set_initial_profile(1, AxiomProfile::EXTENSIONALITY)
            .unwrap();
        graph
            .set_initial_profile(2, AxiomProfile::HOL_EMBEDDING)
            .unwrap();
        graph.set_initial_profile(3, AxiomProfile::NONE).unwrap();
        graph.add_edge(1, 0).unwrap();
        graph.add_edge(2, 0).unwrap();
        graph.add_edge(3, 1).unwrap();
        graph.add_edge(3, 2).unwrap();
        graph.propagate().unwrap();

        let suite = VerificationSuite::new();
        let mono = suite.verify_propagation_monotonicity(&graph);
        assert!(mono.passed, "monotonicity: {}", mono.evidence);
        assert!(mono.checked_count >= 4); // at least 4 edges

        // Node 3 should have union of all
        let p3 = graph.profile(3);
        assert!(p3.contains(AxiomProfile::CLASSICAL));
        assert!(p3.contains(AxiomProfile::EXTENSIONALITY));
        assert!(p3.contains(AxiomProfile::HOL_EMBEDDING));
    }

    // ========================================================================
    // 7. Propagation invariant deep tests
    // ========================================================================

    #[test]
    fn test_propagation_chain_5_nodes() {
        // Linear chain: 0 <- 1 <- 2 <- 3 <- 4
        // Each node has a unique axiom bit
        let mut graph = DependencyGraph::new(5);
        graph
            .set_initial_profile(0, AxiomProfile::CLASSICAL)
            .unwrap();
        graph
            .set_initial_profile(1, AxiomProfile::EXTENSIONALITY)
            .unwrap();
        graph
            .set_initial_profile(2, AxiomProfile::PROP_EXT)
            .unwrap();
        graph
            .set_initial_profile(3, AxiomProfile::HOL_EMBEDDING)
            .unwrap();
        graph
            .set_initial_profile(4, AxiomProfile::MIZAR_SOFT_TYPE)
            .unwrap();
        graph.add_edge(1, 0).unwrap();
        graph.add_edge(2, 1).unwrap();
        graph.add_edge(3, 2).unwrap();
        graph.add_edge(4, 3).unwrap();

        graph.propagate().unwrap();
        assert!(graph.verify_invariant().is_ok());

        // Node 4 should accumulate all bits (each node uses a distinct bit)
        let final_profile = graph.profile(4);
        assert!(final_profile.contains(AxiomProfile::CLASSICAL));
        assert!(final_profile.contains(AxiomProfile::EXTENSIONALITY));
        assert!(final_profile.contains(AxiomProfile::PROP_EXT));
        assert!(final_profile.contains(AxiomProfile::HOL_EMBEDDING));
        assert!(final_profile.contains(AxiomProfile::MIZAR_SOFT_TYPE));
        assert_eq!(final_profile.axiom_count(), 5);

        // Node 0 should have only its own bit
        assert_eq!(graph.profile(0).axiom_count(), 1);
    }

    #[test]
    fn test_propagation_cycle_detection() {
        let mut graph = DependencyGraph::new(3);
        // 0 -> 1 -> 2 -> 0 (cycle via non-topological edges)
        graph.add_edge(0, 2).unwrap();
        graph.add_edge(1, 0).unwrap();
        graph.add_edge(2, 1).unwrap();

        let result = graph.propagate();
        assert!(result.is_err(), "cycle should be detected");
    }

    #[test]
    fn test_propagation_empty_graph() {
        let graph = DependencyGraph::new(0);
        assert_eq!(graph.node_count(), 0);
    }

    // ========================================================================
    // 8. Source system coverage
    // ========================================================================

    #[test]
    fn test_all_source_systems_importable() {
        let sources = [
            (
                SourceSystem::Lean4,
                AxiomProfile::NONE,
                TrustLevel::KernelVerified,
            ),
            (
                SourceSystem::Coq,
                AxiomProfile::CLASSICAL,
                TrustLevel::AxiomDependent,
            ),
            (
                SourceSystem::HolLight,
                HOL_BASE,
                TrustLevel::CertificateReplayed,
            ),
            (
                SourceSystem::Hol4,
                HOL_BASE,
                TrustLevel::CertificateReplayed,
            ),
            (
                SourceSystem::Isabelle,
                AxiomProfile::CLASSICAL,
                TrustLevel::PartiallyAxiomatized,
            ),
            (
                SourceSystem::Mizar,
                MIZAR_BASE,
                TrustLevel::PartiallyAxiomatized,
            ),
            (
                SourceSystem::Metamath,
                AxiomProfile::CLASSICAL,
                TrustLevel::AxiomDependent,
            ),
            (
                SourceSystem::Agda,
                AxiomProfile::AGDA_CUBICAL,
                TrustLevel::AxiomDependent,
            ),
            (
                SourceSystem::Idris2,
                AxiomProfile::IDRIS_QTT,
                TrustLevel::AxiomDependent,
            ),
            (
                SourceSystem::FStar,
                AxiomProfile::SMT_ORACLE,
                TrustLevel::TrustedOracle,
            ),
            (
                SourceSystem::Dafny,
                AxiomProfile::SMT_ORACLE,
                TrustLevel::TrustedOracle,
            ),
            (
                SourceSystem::Why3,
                AxiomProfile::SMT_ORACLE,
                TrustLevel::TrustedOracle,
            ),
        ];

        let config = BulkImportConfig::builder()
            .enforce_trust_gate(false)
            .build();
        let mut importer = BulkImporter::new(config);

        for (i, (source, profile, trust)) in sources.iter().enumerate() {
            let name = format!("test_const_{}", i);
            importer
                .add_constant(make_constant(&name, *source, *profile, *trust))
                .unwrap();
        }

        let result = importer.finalize().unwrap();
        assert_eq!(result.total_constants, 12);
        assert!(result.propagation_ok);
        // Only the Lean4 constant (KernelVerified + NONE) is exportable
        assert_eq!(result.exportable_count, 1);
    }

    // ========================================================================
    // 9. Bulk import end-to-end with dependencies
    // ========================================================================

    #[test]
    fn test_bulk_import_with_dependencies() {
        let config = BulkImportConfig::builder().build();
        let mut importer = BulkImporter::new(config);
        let base = importer
            .add_constant(make_constant(
                "base",
                SourceSystem::Lean4,
                AxiomProfile::NONE,
                TrustLevel::KernelVerified,
            ))
            .unwrap();
        let derived = importer
            .add_constant(make_constant(
                "derived",
                SourceSystem::HolLight,
                AxiomProfile::CLASSICAL,
                TrustLevel::CertificateReplayed,
            ))
            .unwrap();
        importer.add_dependency(derived, base).unwrap();

        let result = importer.finalize().unwrap();
        assert!(result.propagation_ok);
        assert_eq!(result.exportable_count, 1); // only base
    }

    #[test]
    fn test_bulk_import_capacity_limit() {
        let config = BulkImportConfig::builder().max_constants(3).build();
        let mut importer = BulkImporter::new(config);
        for i in 0..3 {
            importer
                .add_constant(make_constant(
                    &format!("c{}", i),
                    SourceSystem::Lean4,
                    AxiomProfile::NONE,
                    TrustLevel::KernelVerified,
                ))
                .unwrap();
        }
        let err = importer
            .add_constant(make_constant(
                "overflow",
                SourceSystem::Lean4,
                AxiomProfile::NONE,
                TrustLevel::KernelVerified,
            ))
            .unwrap_err();
        assert!(format!("{}", err).contains("capacity"));
    }

    // ========================================================================
    // 10. Stats integration
    // ========================================================================

    #[test]
    fn test_stats_multi_source() {
        let mut stats = ImportStats::new();
        stats.record("Lean4", TrustLevel::KernelVerified, AxiomProfile::NONE);
        stats.record("Lean4", TrustLevel::KernelVerified, AxiomProfile::NONE);
        stats.record(
            "HolLight",
            TrustLevel::CertificateReplayed,
            AxiomProfile::CLASSICAL,
        );
        stats.record("Mizar", TrustLevel::PartiallyAxiomatized, MIZAR_BASE);
        stats.record("Dafny", TrustLevel::TrustedOracle, AxiomProfile::SMT_ORACLE);
        stats.record_theorem("HolLight");
        stats.record_theorem("Mizar");

        assert_eq!(stats.total_constants, 5);
        assert_eq!(stats.total_theorems, 2);
        assert_eq!(stats.kernel_verified_count, 2);
        assert!((stats.kernel_verified_fraction() - 0.4).abs() < 1e-10);

        let summary = MathverseSummary {
            version: "0.1.0-beta".to_owned(),
            import_stats: stats,
            trust_audit_clean: true,
            verification_properties_passed: 5,
            verification_properties_total: 5,
        };
        assert!(summary.is_healthy());
        let md = summary.to_markdown();
        assert!(md.contains("HEALTHY"));
        assert!(md.contains("5"));
    }

    #[test]
    fn test_stats_merge_from_parallel_workers() {
        let mut worker_a = ImportStats::new();
        worker_a.record("Lean4", TrustLevel::KernelVerified, AxiomProfile::NONE);

        let mut worker_b = ImportStats::new();
        worker_b.record(
            "HolLight",
            TrustLevel::CertificateReplayed,
            AxiomProfile::CLASSICAL,
        );

        worker_a.merge(&worker_b);
        assert_eq!(worker_a.total_constants, 2);
        assert_eq!(worker_a.by_source.len(), 2);
        assert_eq!(worker_a.kernel_verified_count, 1);
    }

    // ========================================================================
    // 11. Audit report with findings integration
    // ========================================================================

    #[test]
    fn test_audit_report_with_findings_and_violations() {
        let mut builder = AuditReportBuilder::new();
        builder.add_constant(TrustLevel::KernelVerified, "Lean4", AxiomProfile::NONE);
        builder.add_constant(TrustLevel::TrustedOracle, "Dafny", AxiomProfile::SMT_ORACLE);

        // Add a violation
        builder.add_violation(crate::trust::graph_gate::TrustViolation {
            parent_idx: 0,
            parent_trust: TrustLevel::KernelVerified,
            child_idx: 1,
            child_trust: TrustLevel::TrustedOracle,
            violation: "kernel depends on oracle".to_owned(),
        });

        // Add findings at different severities
        builder.add_finding(AuditFinding {
            severity: AuditSeverity::Warning,
            category: "axiom-gap".to_owned(),
            message: "potential axiom gap".to_owned(),
            node_indices: vec![1],
            recommendation: None,
        });
        builder.add_finding(AuditFinding {
            severity: AuditSeverity::Critical,
            category: "trust-leak".to_owned(),
            message: "trust boundary violated".to_owned(),
            node_indices: vec![0, 1],
            recommendation: Some("remove dependency".to_owned()),
        });

        let report = builder.build();
        assert!(!report.is_clean());
        assert_eq!(report.trust_violations.len(), 1);
        assert_eq!(report.findings.len(), 2);
        let summary = report.summary();
        assert!(summary.contains("ISSUES FOUND"));
        assert!(summary.contains("Critical: 1"));
    }

    // ========================================================================
    // 12. Full pipeline: import → propagate → audit → export
    // ========================================================================

    #[test]
    fn test_full_pipeline_import_to_export() {
        let config = BulkImportConfig::builder()
            .enforce_trust_gate(false)
            .build();
        let mut importer = BulkImporter::new(config);

        // Import a small dependency chain from Lean4.
        let a = make_constant(
            "Nat.zero",
            SourceSystem::Lean4,
            AxiomProfile::NONE,
            TrustLevel::KernelVerified,
        );
        let b = make_constant(
            "Nat.succ",
            SourceSystem::Lean4,
            AxiomProfile::NONE,
            TrustLevel::KernelVerified,
        );
        let mut c = make_constant(
            "Nat.add",
            SourceSystem::Lean4,
            AxiomProfile::NONE,
            TrustLevel::KernelVerified,
        );
        c.dependencies = vec![0, 1]; // add depends on zero and succ

        importer.add_constant(a).expect("add zero");
        importer.add_constant(b).expect("add succ");
        importer.add_constant(c).expect("add add");

        let result = importer.finalize().expect("finalize");

        // All three should be exportable (KernelVerified + NONE profile).
        assert_eq!(result.total_constants, 3);
        assert_eq!(result.exportable_count, 3);
        assert!(result.propagation_ok);
        assert!(result.is_clean());

        // Audit report should be consistent.
        assert_eq!(result.audit_report.total_constants, 3);
        assert_eq!(result.audit_report.exportable_for_training, 3);

        // Verification suite on the audit report.
        let suite = VerificationSuite::new();
        let training_result = suite.verify_training_gate_strictness();
        assert!(
            training_result.passed,
            "training gate: {}",
            training_result.evidence
        );
    }

    // ========================================================================
    // 13. Multi-source with conflicting axiom profiles
    // ========================================================================

    #[test]
    fn test_multi_source_conflicting_profiles() {
        let config = BulkImportConfig::builder()
            .enforce_trust_gate(false)
            .build();
        let mut importer = BulkImporter::new(config);

        // HOL constant with HOL_EMBEDDING profile.
        let hol = make_constant(
            "hol.bool_ext",
            SourceSystem::HolLight,
            HOL_BASE,
            TrustLevel::CertificateReplayed,
        );
        importer.add_constant(hol).expect("add hol");

        // Mizar constant with MIZAR_SOFT_TYPE profile.
        let mizar = make_constant(
            "mizar.sethood",
            SourceSystem::Mizar,
            MIZAR_BASE,
            TrustLevel::PartiallyAxiomatized,
        );
        importer.add_constant(mizar).expect("add mizar");

        // A Lean4 constant depending on both.
        let mut lean = make_constant(
            "lean.combined",
            SourceSystem::Lean4,
            AxiomProfile::NONE,
            TrustLevel::TrustedOracle,
        );
        lean.dependencies = vec![0, 1]; // depends on hol and mizar
        importer.add_constant(lean).expect("add lean");

        let result = importer.finalize().expect("finalize");

        // Combined constant should inherit both profiles.
        // Verify through audit report: none are exportable (none are KernelVerified+NONE).
        assert_eq!(result.exportable_count, 0);
        assert_eq!(result.total_constants, 3);

        // Cross-system consistency verification.
        let suite = VerificationSuite::new();
        let hol_profiles = vec![HOL_BASE];
        let mizar_profiles = vec![MIZAR_BASE];
        let cross = suite.verify_cross_system_consistency(&hol_profiles, &mizar_profiles);
        assert!(cross.passed, "cross-system: {}", cross.evidence);
    }

    // ========================================================================
    // 14. Self-verification on synthetic graph
    // ========================================================================

    #[test]
    fn test_self_verification_on_synthetic_graph() {
        use crate::trust::verification::SelfVerificationSuite;

        // Build a propagated graph with known properties.
        let mut graph = DependencyGraph::new(5);
        graph
            .set_initial_profile(0, AxiomProfile::CLASSICAL)
            .unwrap();
        graph
            .set_initial_profile(1, AxiomProfile::EXTENSIONALITY)
            .unwrap();
        graph.set_initial_profile(2, AxiomProfile::NONE).unwrap();
        graph.set_initial_profile(3, AxiomProfile::NONE).unwrap();
        graph.set_initial_profile(4, AxiomProfile::NONE).unwrap();

        graph.add_edge(2, 0).unwrap();
        graph.add_edge(3, 1).unwrap();
        graph.add_edge(4, 2).unwrap();
        graph.add_edge(4, 3).unwrap();
        graph.propagate().unwrap();

        // Node 4 should have CLASSICAL | EXTENSIONALITY (transitive from 0 and 1).
        assert!(graph.profile(4).contains(AxiomProfile::CLASSICAL));
        assert!(graph.profile(4).contains(AxiomProfile::EXTENSIONALITY));

        let trust_levels = vec![
            TrustLevel::AxiomDependent,
            TrustLevel::AxiomDependent,
            TrustLevel::AxiomDependent,
            TrustLevel::AxiomDependent,
            TrustLevel::TrustedOracle,
        ];
        let gate = TrustGate::default_policy();

        // Build complete audit report.
        let violations = gate.audit_graph(&graph, &trust_levels);
        let mut builder = AuditReportBuilder::new();
        for (i, &tl) in trust_levels.iter().enumerate() {
            builder.add_constant(tl, "test", graph.profile(i as u32));
        }
        for v in &violations {
            builder.add_violation(v.clone());
        }
        let report = builder.build();

        // Run self-verification.
        let self_suite = SelfVerificationSuite::new();
        let evidence = self_suite.verify_all_properties(&graph, &trust_levels, &gate, &report);
        assert!(
            evidence.all_passed,
            "self-verification failed:\n{}",
            evidence.summary()
        );
        assert_eq!(evidence.properties_checked, 4);
    }

    // ========================================================================
    // 15. Audit report comparison across imports
    // ========================================================================

    #[test]
    fn test_audit_report_comparison_across_imports() {
        use crate::trust::audit_report::compare_reports;

        // First import: 2 constants, 1 violation.
        let config = BulkImportConfig::builder()
            .enforce_trust_gate(false)
            .build();
        let mut importer1 = BulkImporter::new(config.clone());
        importer1
            .add_constant(make_constant(
                "A",
                SourceSystem::Lean4,
                AxiomProfile::NONE,
                TrustLevel::KernelVerified,
            ))
            .unwrap();
        let mut b = make_constant(
            "B",
            SourceSystem::SmtSolver,
            AxiomProfile::SMT_ORACLE,
            TrustLevel::TrustedOracle,
        );
        b.dependencies = vec![0]; // bad: oracle depends on kernel
        importer1.add_constant(b).unwrap();
        let result1 = importer1.finalize().unwrap();

        // Second import: same but without the bad dependency.
        let mut importer2 = BulkImporter::new(config);
        importer2
            .add_constant(make_constant(
                "A",
                SourceSystem::Lean4,
                AxiomProfile::NONE,
                TrustLevel::KernelVerified,
            ))
            .unwrap();
        importer2
            .add_constant(make_constant(
                "B",
                SourceSystem::SmtSolver,
                AxiomProfile::SMT_ORACLE,
                TrustLevel::TrustedOracle,
            ))
            .unwrap();
        importer2
            .add_constant(make_constant(
                "C",
                SourceSystem::Lean4,
                AxiomProfile::NONE,
                TrustLevel::KernelVerified,
            ))
            .unwrap();
        let result2 = importer2.finalize().unwrap();

        let comparison = compare_reports(&result1.audit_report, &result2.audit_report);
        assert_eq!(comparison.constants_delta, 1); // 3 - 2
        assert!(comparison.exportable_delta >= 0); // more or equal exports
        assert!(result2.is_clean()); // no violations
    }

    // ========================================================================
    // 16. Incremental vs full propagation
    // ========================================================================

    #[test]
    fn test_incremental_vs_full_propagation_integration() {
        // Build a graph, propagate fully, then compare with incremental.
        let mut full_graph = DependencyGraph::new(5);
        full_graph
            .set_initial_profile(0, AxiomProfile::CLASSICAL)
            .unwrap();
        full_graph
            .set_initial_profile(1, AxiomProfile::EXTENSIONALITY)
            .unwrap();
        full_graph
            .set_initial_profile(2, AxiomProfile::CHOICE)
            .unwrap();
        full_graph.add_edge(3, 0).unwrap();
        full_graph.add_edge(3, 1).unwrap();
        full_graph.add_edge(4, 2).unwrap();
        full_graph.add_edge(4, 3).unwrap();
        full_graph.propagate().unwrap();

        // Incremental: propagate without the edge 4->3, then add it.
        let mut inc_graph = DependencyGraph::new(5);
        inc_graph
            .set_initial_profile(0, AxiomProfile::CLASSICAL)
            .unwrap();
        inc_graph
            .set_initial_profile(1, AxiomProfile::EXTENSIONALITY)
            .unwrap();
        inc_graph
            .set_initial_profile(2, AxiomProfile::CHOICE)
            .unwrap();
        inc_graph.add_edge(3, 0).unwrap();
        inc_graph.add_edge(3, 1).unwrap();
        inc_graph.add_edge(4, 2).unwrap();
        inc_graph.propagate().unwrap();

        // Now add edge 4->3 incrementally.
        inc_graph.add_edge(4, 3).unwrap();
        inc_graph.propagate_incremental(&[(4, 3)]).unwrap();

        // Both should produce identical profiles.
        for i in 0..5 {
            assert_eq!(
                full_graph.profile(i as u32),
                inc_graph.profile(i as u32),
                "node {} differs",
                i,
            );
        }

        // Node 4 should have CHOICE | CLASSICAL | EXTENSIONALITY.
        let p4 = full_graph.profile(4);
        assert!(p4.contains(AxiomProfile::CHOICE));
        assert!(p4.contains(AxiomProfile::CLASSICAL));
        assert!(p4.contains(AxiomProfile::EXTENSIONALITY));
    }

    // ========================================================================
    // 17. BulkImportReport and BulkImportStats
    // ========================================================================

    #[test]
    fn test_bulk_import_report_and_stats() {
        use crate::bulk_import::{BulkImportReport, BulkImportStats};

        let config = BulkImportConfig::builder()
            .enforce_trust_gate(false)
            .build();
        let mut importer = BulkImporter::new(config);

        importer
            .add_constant(make_constant(
                "A",
                SourceSystem::Lean4,
                AxiomProfile::NONE,
                TrustLevel::KernelVerified,
            ))
            .unwrap();
        importer
            .add_constant(make_constant(
                "B",
                SourceSystem::Coq,
                AxiomProfile::CLASSICAL,
                TrustLevel::AxiomDependent,
            ))
            .unwrap();
        importer
            .add_constant(make_constant(
                "C",
                SourceSystem::HolLight,
                HOL_BASE,
                TrustLevel::CertificateReplayed,
            ))
            .unwrap();

        let result = importer.finalize().unwrap();

        let report = BulkImportReport::from_result(&result);
        assert_eq!(report.stats.total_constants, 3);
        assert_eq!(report.stats.source_count(), 3);
        assert_eq!(report.stats.trust_level_count(), 3);
        assert!(report.is_clean);
        assert_eq!(report.exportable_count, 1); // only KernelVerified+NONE

        let summary = report.summary();
        assert!(summary.contains("Total constants: 3"));
        assert!(summary.contains("Source systems: 3"));
        assert!(summary.contains("CLEAN"));

        // Stats from result.
        let stats = BulkImportStats::from_result(&result);
        assert_eq!(stats.total_constants, 3);
        assert_eq!(stats.source_count(), 3);
    }

    // ========================================================================
    // 18. validate_before_finalize
    // ========================================================================

    #[test]
    fn test_validate_before_finalize_success() {
        let config = BulkImportConfig::builder()
            .enforce_trust_gate(false)
            .build();
        let mut importer = BulkImporter::new(config);

        importer
            .add_constant(make_constant(
                "A",
                SourceSystem::Lean4,
                AxiomProfile::NONE,
                TrustLevel::KernelVerified,
            ))
            .unwrap();
        let mut b = make_constant(
            "B",
            SourceSystem::Lean4,
            AxiomProfile::NONE,
            TrustLevel::KernelVerified,
        );
        b.dependencies = vec![0];
        importer.add_constant(b).unwrap();

        assert!(importer.validate_before_finalize().is_ok());
    }

    #[test]
    fn test_validate_before_finalize_empty() {
        let config = BulkImportConfig::builder().build();
        let importer = BulkImporter::new(config);

        let err = importer.validate_before_finalize().unwrap_err();
        assert!(err.to_string().contains("empty batch"));
    }

    #[test]
    fn test_validate_before_finalize_self_dep() {
        let config = BulkImportConfig::builder()
            .enforce_trust_gate(false)
            .build();
        let mut importer = BulkImporter::new(config);

        let mut a = make_constant(
            "A",
            SourceSystem::Lean4,
            AxiomProfile::NONE,
            TrustLevel::KernelVerified,
        );
        a.dependencies = vec![0]; // self-referential
        importer.add_constant(a).unwrap();

        let err = importer.validate_before_finalize().unwrap_err();
        assert!(err.to_string().contains("self-referential"));
    }

    #[test]
    fn test_validate_before_finalize_out_of_bounds_dep() {
        let config = BulkImportConfig::builder()
            .enforce_trust_gate(false)
            .build();
        let mut importer = BulkImporter::new(config);

        let mut a = make_constant(
            "A",
            SourceSystem::Lean4,
            AxiomProfile::NONE,
            TrustLevel::KernelVerified,
        );
        a.dependencies = vec![99]; // out of bounds
        importer.add_constant(a).unwrap();

        let err = importer.validate_before_finalize().unwrap_err();
        assert!(err.to_string().contains("out of bounds"));
    }

    // ========================================================================
    // 19. import_from_source convenience method
    // ========================================================================

    #[test]
    fn test_import_from_source_basic() {
        let config = BulkImportConfig::builder()
            .enforce_trust_gate(false)
            .build();
        let mut importer = BulkImporter::new(config);

        let indices = importer
            .import_from_source(
                SourceSystem::Lean4,
                TrustLevel::KernelVerified,
                AxiomProfile::NONE,
                &["Nat.zero", "Nat.succ", "Nat.add"],
                &[("Nat.add", "Nat.zero"), ("Nat.add", "Nat.succ")],
            )
            .unwrap();

        assert_eq!(indices.len(), 3);
        assert_eq!(importer.constant_count(), 3);

        let result = importer.finalize().unwrap();
        assert_eq!(result.total_constants, 3);
        assert_eq!(result.exportable_count, 3);
        assert!(result.is_clean());
    }

    #[test]
    fn test_import_from_source_with_propagation() {
        let config = BulkImportConfig::builder()
            .enforce_trust_gate(false)
            .build();
        let mut importer = BulkImporter::new(config);

        // Import axiom-dependent constants with dependencies.
        importer
            .import_from_source(
                SourceSystem::Coq,
                TrustLevel::AxiomDependent,
                AxiomProfile::CLASSICAL,
                &["base_axiom", "derived_thm"],
                &[("derived_thm", "base_axiom")],
            )
            .unwrap();

        let result = importer.finalize().unwrap();
        assert_eq!(result.total_constants, 2);
        // Neither is exportable (not KernelVerified+NONE).
        assert_eq!(result.exportable_count, 0);
    }

    // ========================================================================
    // 20. compute_stats on BulkImporter
    // ========================================================================

    #[test]
    fn test_bulk_importer_compute_stats() {
        let config = BulkImportConfig::builder()
            .enforce_trust_gate(false)
            .build();
        let mut importer = BulkImporter::new(config);

        importer
            .add_constant(make_constant(
                "A",
                SourceSystem::Lean4,
                AxiomProfile::NONE,
                TrustLevel::KernelVerified,
            ))
            .unwrap();
        importer
            .add_constant(make_constant(
                "B",
                SourceSystem::Lean4,
                AxiomProfile::CLASSICAL,
                TrustLevel::AxiomDependent,
            ))
            .unwrap();
        importer
            .add_constant(make_constant(
                "C",
                SourceSystem::Coq,
                AxiomProfile::CLASSICAL,
                TrustLevel::AxiomDependent,
            ))
            .unwrap();

        let stats = importer.compute_stats();
        assert_eq!(stats.total_constants, 3);
        assert_eq!(stats.source_count(), 2); // Lean4, Coq
        assert_eq!(stats.trust_level_count(), 2); // KernelVerified, AxiomDependent
                                                  // by_axiom_profile: NONE and CLASSICAL
        assert_eq!(stats.by_axiom_profile.len(), 2);
        assert_eq!(stats.by_axiom_profile.get(&AxiomProfile::NONE.0), Some(&1));
        assert_eq!(
            stats.by_axiom_profile.get(&AxiomProfile::CLASSICAL.0),
            Some(&2)
        );
    }

    // ========================================================================
    // 21. VerificationEvidence integration
    // ========================================================================

    #[test]
    fn test_verification_evidence_integration() {
        use crate::trust::verification::VerificationEvidence;

        let mut graph = DependencyGraph::new(3);
        graph
            .set_initial_profile(0, AxiomProfile::CLASSICAL)
            .unwrap();
        graph.add_edge(1, 0).unwrap();
        graph.add_edge(2, 1).unwrap();
        graph.propagate().unwrap();

        let trust_levels = vec![
            TrustLevel::AxiomDependent,
            TrustLevel::AxiomDependent,
            TrustLevel::TrustedOracle,
        ];
        let gate = TrustGate::default_policy();

        let suite = VerificationSuite::new();
        let results = suite.run_all(&graph, &trust_levels, &gate);

        let evidence = VerificationEvidence::from_results(results);
        assert!(evidence.all_passed, "summary:\n{}", evidence.summary());
        assert!(evidence.properties_checked >= 5);
        assert_eq!(evidence.properties_failed, 0);
        assert!(evidence.total_checks > 0);

        // Summary should mention PASS.
        let summary = evidence.summary();
        assert!(summary.contains("PASS"));
    }

    // ========================================================================
    // 22. Topological order + reachable_from integration
    // ========================================================================

    #[test]
    fn test_topological_order_and_reachable_from_integration() {
        let mut graph = DependencyGraph::new(6);
        // DAG: 0, 1 are roots
        // 2 depends on 0
        // 3 depends on 0, 1
        // 4 depends on 2, 3
        // 5 depends on 4
        graph.add_edge(2, 0).unwrap();
        graph.add_edge(3, 0).unwrap();
        graph.add_edge(3, 1).unwrap();
        graph.add_edge(4, 2).unwrap();
        graph.add_edge(4, 3).unwrap();
        graph.add_edge(5, 4).unwrap();

        // Topological order should exist (no cycles).
        let order = graph.topological_order().expect("should have topo order");
        assert_eq!(order.len(), 6);

        // Verify ordering: for every edge (parent, child), child before parent.
        let mut position = [0usize; 6];
        for (pos, &node) in order.iter().enumerate() {
            position[node as usize] = pos;
        }
        // Edge 2->0: 0 before 2.
        assert!(position[0] < position[2]);
        // Edge 5->4: 4 before 5.
        assert!(position[4] < position[5]);
        // Edge 4->2 and 4->3: both before 4.
        assert!(position[2] < position[4]);
        assert!(position[3] < position[4]);

        // Reachable from 5: everything except 5 itself.
        let reachable = graph.reachable_from(5);
        assert!(reachable.contains(&4));
        assert!(reachable.contains(&3));
        assert!(reachable.contains(&2));
        assert!(reachable.contains(&1));
        assert!(reachable.contains(&0));
        assert!(!reachable.contains(&5));
        assert_eq!(reachable.len(), 5);

        // Reachable from 2: only 0.
        let reachable2 = graph.reachable_from(2);
        assert_eq!(reachable2.len(), 1);
        assert!(reachable2.contains(&0));

        // Reachable from a root: empty set.
        let reachable_root = graph.reachable_from(0);
        assert!(reachable_root.is_empty());
    }

    // ========================================================================
    // 23. JSON output field completeness
    // ========================================================================

    #[test]
    fn test_json_output_field_completeness() {
        use crate::trust::audit_report::AuditReportFormat;

        let mut builder = AuditReportBuilder::new();
        builder.add_constant(TrustLevel::KernelVerified, "Lean4", AxiomProfile::NONE);
        builder.add_constant(TrustLevel::TrustedOracle, "SMT", AxiomProfile::SMT_ORACLE);
        builder.add_finding(AuditFinding {
            severity: AuditSeverity::Warning,
            category: "test-category".to_owned(),
            message: "test message".to_owned(),
            node_indices: vec![0],
            recommendation: None,
        });
        let report = builder.build();

        let json = report.format(AuditReportFormat::Json);

        // Required fields.
        assert!(json.contains("\"total_constants\":"));
        assert!(json.contains("\"axiom_coverage\":"));
        assert!(json.contains("\"kernel_verified_fraction\":"));
        assert!(json.contains("\"exportable_for_training\":"));
        assert!(json.contains("\"trust_violations_count\":"));
        assert!(json.contains("\"findings_count\":"));
        assert!(json.contains("\"by_trust_level\":"));
        assert!(json.contains("\"by_source_system\":"));
        assert!(json.contains("\"findings_by_severity\":"));
        assert!(json.contains("\"status\":"));

        // Verify Markdown also produces expected sections.
        let md = report.format(AuditReportFormat::Markdown);
        assert!(md.contains("# Mathverse Trust Audit Report"));
        assert!(md.contains("## Summary"));
        assert!(md.contains("## Trust Level Breakdown"));
        assert!(md.contains("## Findings"));

        // Text format.
        let text = report.format(AuditReportFormat::Text);
        assert!(text.contains("Total constants: 2"));
    }

    // ========================================================================
    // 24. DependencyGraphStats integration
    // ========================================================================

    #[test]
    fn test_dependency_graph_stats_integration() {
        let mut graph = DependencyGraph::new(5);
        graph.add_edge(1, 0).unwrap();
        graph.add_edge(2, 0).unwrap();
        graph.add_edge(2, 1).unwrap();
        graph.add_edge(3, 2).unwrap();
        graph.add_edge(4, 2).unwrap();
        graph.add_edge(4, 3).unwrap();

        let stats = graph.compute_stats();
        assert_eq!(stats.nodes, 5);
        assert_eq!(stats.edges, 6);
        assert!(!stats.cycles_detected);
        assert!(stats.max_depth >= 3); // 0->1->2->3 or 0->2->3->4
        assert!((stats.avg_degree - 1.2).abs() < 0.01); // 6/5 = 1.2

        // Edge count matches.
        assert_eq!(graph.edge_count(), 6);
    }

    // ========================================================================
    // 25. Audit report comparison: regression detection
    // ========================================================================

    #[test]
    fn test_audit_comparison_regression_detection() {
        use crate::trust::audit_report::compare_reports;

        // Build a "before" report: clean.
        let mut before_builder = AuditReportBuilder::new();
        before_builder.add_constant(TrustLevel::KernelVerified, "Lean4", AxiomProfile::NONE);
        before_builder.add_constant(TrustLevel::KernelVerified, "Lean4", AxiomProfile::NONE);
        let before = before_builder.build();

        // Build an "after" report: has a new critical finding.
        let mut after_builder = AuditReportBuilder::new();
        after_builder.add_constant(TrustLevel::KernelVerified, "Lean4", AxiomProfile::NONE);
        after_builder.add_constant(TrustLevel::KernelVerified, "Lean4", AxiomProfile::NONE);
        after_builder.add_constant(TrustLevel::TrustedOracle, "SMT", AxiomProfile::SMT_ORACLE);
        after_builder.add_finding(AuditFinding {
            severity: AuditSeverity::Critical,
            category: "trust-contamination".to_owned(),
            message: "oracle constant added".to_owned(),
            node_indices: vec![2],
            recommendation: Some("review trust assignment".to_owned()),
        });
        let after = after_builder.build();

        let comparison = compare_reports(&before, &after);
        assert!(comparison.is_regression);
        assert_eq!(comparison.constants_delta, 1); // 3 - 2
        assert!(comparison.findings_delta > 0);
        assert!(comparison
            .new_finding_categories
            .contains(&"trust-contamination".to_owned()));
    }

    // ========================================================================
    // 26. End-to-end: import_from_source → stats → report → compare
    // ========================================================================

    #[test]
    fn test_end_to_end_import_stats_report_compare() {
        use crate::bulk_import::BulkImportReport;
        use crate::trust::audit_report::compare_reports;

        // Round 1: Lean4 only.
        let config = BulkImportConfig::builder()
            .enforce_trust_gate(false)
            .build();
        let mut importer1 = BulkImporter::new(config.clone());
        importer1
            .import_from_source(
                SourceSystem::Lean4,
                TrustLevel::KernelVerified,
                AxiomProfile::NONE,
                &["A", "B"],
                &[("B", "A")],
            )
            .unwrap();
        let result1 = importer1.finalize().unwrap();
        let report1 = BulkImportReport::from_result(&result1);
        assert!(report1.is_clean);
        assert_eq!(report1.exportable_count, 2);

        // Round 2: Lean4 + Coq.
        let mut importer2 = BulkImporter::new(config);
        importer2
            .import_from_source(
                SourceSystem::Lean4,
                TrustLevel::KernelVerified,
                AxiomProfile::NONE,
                &["A", "B"],
                &[("B", "A")],
            )
            .unwrap();
        importer2
            .import_from_source(
                SourceSystem::Coq,
                TrustLevel::AxiomDependent,
                AxiomProfile::CLASSICAL,
                &["C", "D"],
                &[("D", "C")],
            )
            .unwrap();
        let result2 = importer2.finalize().unwrap();
        let report2 = BulkImportReport::from_result(&result2);
        assert!(report2.is_clean);
        assert_eq!(report2.stats.total_constants, 4);
        assert_eq!(report2.stats.source_count(), 2);

        // Compare audit reports.
        let comparison = compare_reports(&result1.audit_report, &result2.audit_report);
        assert_eq!(comparison.constants_delta, 2); // 4 - 2
        assert!(!comparison.is_regression);
    }
}
