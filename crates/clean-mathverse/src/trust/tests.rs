// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the trust enforcement module.

use crate::trust::axiom_propagation::{
    propagate_single_pass, verify_topological_order, DependencyGraph, PropagationError,
};
use crate::trust::graph_gate::{TrainingExportGate, TrustGate};
use crate::types::{AxiomProfile, TrustLevel};

// ============================================================================
// DependencyGraph construction tests
// ============================================================================

#[test]
fn test_dependency_graph_new_empty() {
    let graph = DependencyGraph::new(0);
    assert_eq!(graph.node_count(), 0);
}

#[test]
fn test_dependency_graph_new_profiles_default_to_none() {
    let graph = DependencyGraph::new(5);
    assert_eq!(graph.node_count(), 5);
    for i in 0..5 {
        assert_eq!(graph.profile(i), AxiomProfile::NONE);
    }
}

#[test]
fn test_dependency_graph_add_edge_valid() {
    let mut graph = DependencyGraph::new(3);
    graph.add_edge(2, 0).expect("should add valid edge");
    graph.add_edge(2, 1).expect("should add valid edge");
    assert_eq!(graph.dependencies(2), &[0, 1]);
}

#[test]
fn test_dependency_graph_add_edge_out_of_bounds() {
    let mut graph = DependencyGraph::new(3);
    let err = graph.add_edge(5, 0).unwrap_err();
    assert!(matches!(
        err,
        PropagationError::NodeOutOfBounds {
            index: 5,
            node_count: 3
        }
    ));

    let err = graph.add_edge(0, 10).unwrap_err();
    assert!(matches!(
        err,
        PropagationError::NodeOutOfBounds {
            index: 10,
            node_count: 3
        }
    ));
}

#[test]
fn test_dependency_graph_set_initial_profile() {
    let mut graph = DependencyGraph::new(3);
    graph
        .set_initial_profile(1, AxiomProfile::CLASSICAL)
        .expect("should set valid profile");
    assert_eq!(graph.profile(1), AxiomProfile::CLASSICAL);
    assert_eq!(graph.profile(0), AxiomProfile::NONE);
}

#[test]
fn test_dependency_graph_set_profile_out_of_bounds() {
    let mut graph = DependencyGraph::new(2);
    let err = graph
        .set_initial_profile(5, AxiomProfile::CHOICE)
        .unwrap_err();
    assert!(matches!(
        err,
        PropagationError::NodeOutOfBounds {
            index: 5,
            node_count: 2
        }
    ));
}

#[test]
fn test_dependency_graph_profile_out_of_bounds_returns_none() {
    let graph = DependencyGraph::new(2);
    assert_eq!(graph.profile(99), AxiomProfile::NONE);
}

// ============================================================================
// Linear chain propagation: A(2) -> B(1) -> C(0)
// ============================================================================

#[test]
fn test_propagation_linear_chain() {
    // C(0) has CLASSICAL, B(1) depends on C, A(2) depends on B.
    // After propagation: A and B should both have CLASSICAL.
    let mut graph = DependencyGraph::new(3);
    graph
        .set_initial_profile(0, AxiomProfile::CLASSICAL)
        .expect("set C profile");
    graph.add_edge(1, 0).expect("B -> C");
    graph.add_edge(2, 1).expect("A -> B");

    graph.propagate().expect("propagation should succeed");

    assert_eq!(graph.profile(0), AxiomProfile::CLASSICAL);
    assert_eq!(graph.profile(1), AxiomProfile::CLASSICAL);
    assert_eq!(graph.profile(2), AxiomProfile::CLASSICAL);

    graph
        .verify_invariant()
        .expect("invariant should hold after propagation");
}

// ============================================================================
// Diamond propagation: A -> B, A -> C, B -> D, C -> D
// ============================================================================

#[test]
fn test_propagation_diamond() {
    // D(0): CLASSICAL + CHOICE
    // B(1) -> D(0)
    // C(2) -> D(0), C also has EXTENSIONALITY
    // A(3) -> B(1), A -> C(2)
    let mut graph = DependencyGraph::new(4);
    graph
        .set_initial_profile(0, AxiomProfile::CLASSICAL | AxiomProfile::CHOICE)
        .expect("set D profile");
    graph
        .set_initial_profile(2, AxiomProfile::EXTENSIONALITY)
        .expect("set C profile");

    graph.add_edge(1, 0).expect("B -> D");
    graph.add_edge(2, 0).expect("C -> D");
    graph.add_edge(3, 1).expect("A -> B");
    graph.add_edge(3, 2).expect("A -> C");

    graph.propagate().expect("propagation should succeed");

    // D is unchanged
    assert_eq!(
        graph.profile(0),
        AxiomProfile::CLASSICAL | AxiomProfile::CHOICE
    );
    // B gets D's profile
    assert_eq!(
        graph.profile(1),
        AxiomProfile::CLASSICAL | AxiomProfile::CHOICE
    );
    // C gets D's profile + its own EXTENSIONALITY
    assert_eq!(
        graph.profile(2),
        AxiomProfile::CLASSICAL | AxiomProfile::CHOICE | AxiomProfile::EXTENSIONALITY
    );
    // A gets everything from B and C
    assert_eq!(
        graph.profile(3),
        AxiomProfile::CLASSICAL | AxiomProfile::CHOICE | AxiomProfile::EXTENSIONALITY
    );

    graph
        .verify_invariant()
        .expect("invariant should hold after propagation");
}

// ============================================================================
// Multiple independent components
// ============================================================================

#[test]
fn test_propagation_independent_components() {
    // Two independent chains:
    // Component 1: node 1 -> node 0 (CLASSICAL)
    // Component 2: node 3 -> node 2 (HOL_EMBEDDING)
    let mut graph = DependencyGraph::new(4);
    graph
        .set_initial_profile(0, AxiomProfile::CLASSICAL)
        .expect("set profile");
    graph
        .set_initial_profile(2, AxiomProfile::HOL_EMBEDDING)
        .expect("set profile");

    graph.add_edge(1, 0).expect("edge");
    graph.add_edge(3, 2).expect("edge");

    graph.propagate().expect("propagation should succeed");

    assert_eq!(graph.profile(0), AxiomProfile::CLASSICAL);
    assert_eq!(graph.profile(1), AxiomProfile::CLASSICAL);
    assert_eq!(graph.profile(2), AxiomProfile::HOL_EMBEDDING);
    assert_eq!(graph.profile(3), AxiomProfile::HOL_EMBEDDING);

    // Cross-component: no contamination
    assert!(!graph.profile(1).contains(AxiomProfile::HOL_EMBEDDING));
    assert!(!graph.profile(3).contains(AxiomProfile::CLASSICAL));

    graph
        .verify_invariant()
        .expect("invariant should hold after propagation");
}

// ============================================================================
// No-op propagation (no edges)
// ============================================================================

#[test]
fn test_propagation_no_edges() {
    let mut graph = DependencyGraph::new(5);
    graph
        .set_initial_profile(2, AxiomProfile::CLASSICAL)
        .expect("set profile");

    graph.propagate().expect("propagation should succeed");

    assert_eq!(graph.profile(0), AxiomProfile::NONE);
    assert_eq!(graph.profile(2), AxiomProfile::CLASSICAL);
    assert_eq!(graph.profile(4), AxiomProfile::NONE);
}

// ============================================================================
// Empty graph propagation
// ============================================================================

#[test]
fn test_propagation_empty_graph() {
    let mut graph = DependencyGraph::new(0);
    graph
        .propagate()
        .expect("empty graph propagation should succeed");
}

// ============================================================================
// Large graph propagation correctness
// ============================================================================

#[test]
fn test_propagation_large_linear_chain() {
    // 1000 nodes in a linear chain: node[i] depends on node[i-1].
    // node[0] has CLASSICAL. After propagation, all nodes should have CLASSICAL.
    let n = 1000;
    let mut graph = DependencyGraph::new(n);
    graph
        .set_initial_profile(0, AxiomProfile::CLASSICAL)
        .expect("set profile");

    for i in 1..n {
        graph.add_edge(i as u32, (i - 1) as u32).expect("add edge");
    }

    graph.propagate().expect("propagation should succeed");

    for i in 0..n {
        assert_eq!(
            graph.profile(i as u32),
            AxiomProfile::CLASSICAL,
            "node {} should have CLASSICAL after propagation",
            i
        );
    }

    graph
        .verify_invariant()
        .expect("invariant should hold on large chain");
}

#[test]
fn test_propagation_large_fan_in() {
    // 1000 leaf nodes (0..999) with various profiles, all feeding into node 1000.
    let n = 1001;
    let mut graph = DependencyGraph::new(n);

    // Give first 3 leaves distinct axiom bits.
    graph
        .set_initial_profile(0, AxiomProfile::CLASSICAL)
        .expect("set profile");
    graph
        .set_initial_profile(1, AxiomProfile::EXTENSIONALITY)
        .expect("set profile");
    graph
        .set_initial_profile(2, AxiomProfile::CHOICE)
        .expect("set profile");

    // Node 1000 depends on all leaves.
    for i in 0..1000u32 {
        graph.add_edge(1000, i).expect("add edge");
    }

    graph.propagate().expect("propagation should succeed");

    let root_profile = graph.profile(1000);
    assert!(root_profile.contains(AxiomProfile::CLASSICAL));
    assert!(root_profile.contains(AxiomProfile::EXTENSIONALITY));
    assert!(root_profile.contains(AxiomProfile::CHOICE));

    graph
        .verify_invariant()
        .expect("invariant should hold on large fan-in");
}

// ============================================================================
// Verify invariant failure detection
// ============================================================================

#[test]
fn test_verify_invariant_detects_violation() {
    // Construct a graph where invariant is NOT satisfied (don't call propagate).
    let mut graph = DependencyGraph::new(2);
    graph
        .set_initial_profile(0, AxiomProfile::CLASSICAL)
        .expect("set profile");
    // Node 1 depends on node 0 (which has CLASSICAL), but node 1 has NONE.
    graph.add_edge(1, 0).expect("add edge");

    let err = graph.verify_invariant().unwrap_err();
    assert!(matches!(err, PropagationError::InvariantViolation { .. }));
}

// ============================================================================
// Topological order verification
// ============================================================================

#[test]
fn test_topological_order_valid() {
    let edges = vec![
        vec![],     // node 0: no deps
        vec![0],    // node 1 -> 0
        vec![0, 1], // node 2 -> 0, 1
    ];
    verify_topological_order(&edges).expect("valid topological order");
}

#[test]
fn test_topological_order_invalid_self_loop() {
    let edges = vec![
        vec![0], // node 0 -> 0 (self-loop)
    ];
    let err = verify_topological_order(&edges).unwrap_err();
    assert!(matches!(
        err,
        PropagationError::TopologicalOrderViolation { from: 0, to: 0 }
    ));
}

#[test]
fn test_topological_order_invalid_forward_edge() {
    let edges = vec![
        vec![1], // node 0 -> 1 (violates child < parent)
        vec![],
    ];
    let err = verify_topological_order(&edges).unwrap_err();
    assert!(matches!(
        err,
        PropagationError::TopologicalOrderViolation { from: 0, to: 1 }
    ));
}

#[test]
fn test_topological_order_empty() {
    let edges: Vec<Vec<u32>> = vec![];
    verify_topological_order(&edges).expect("empty graph has valid order");
}

// ============================================================================
// Propagate single pass
// ============================================================================

#[test]
fn test_propagate_single_pass_no_change() {
    let mut profiles = vec![AxiomProfile::CLASSICAL, AxiomProfile::CLASSICAL];
    let edges = vec![vec![], vec![0]];
    let changed = propagate_single_pass(&mut profiles, &edges);
    assert!(
        !changed,
        "no change when parent already contains child profile"
    );
}

#[test]
fn test_propagate_single_pass_with_change() {
    let mut profiles = vec![AxiomProfile::CLASSICAL, AxiomProfile::NONE];
    let edges = vec![vec![], vec![0]];
    let changed = propagate_single_pass(&mut profiles, &edges);
    assert!(changed, "should change when parent missing child profile");
    assert_eq!(profiles[1], AxiomProfile::CLASSICAL);
}

// ============================================================================
// Cycle detection via fallback propagation
// ============================================================================

#[test]
fn test_propagation_cycle_detection() {
    // Create a graph with a cycle that violates topological order.
    // node 0 -> node 1, node 1 -> node 0 (mutual dependency).
    // Both edges violate topological order, so we'll hit the fixpoint fallback.
    let mut graph = DependencyGraph::new(2);
    graph
        .set_initial_profile(0, AxiomProfile::CLASSICAL)
        .expect("set profile");

    // Manually add edges that violate topological order.
    // add_edge doesn't check topological order, just bounds.
    graph.add_edge(0, 1).expect("add edge 0->1");
    graph.add_edge(1, 0).expect("add edge 1->0");

    let err = graph.propagate().unwrap_err();
    assert!(
        matches!(err, PropagationError::CycleDetected { .. }),
        "expected CycleDetected, got: {:?}",
        err
    );
}

// ============================================================================
// TrustGate default policy tests
// ============================================================================

#[test]
fn test_trust_gate_kernel_to_kernel_allowed() {
    let gate = TrustGate::default_policy();
    gate.check_dependency(TrustLevel::KernelVerified, TrustLevel::KernelVerified)
        .expect("KernelVerified -> KernelVerified should be allowed");
}

#[test]
fn test_trust_gate_kernel_to_axiom_violation() {
    let gate = TrustGate::default_policy();
    let err = gate
        .check_dependency(TrustLevel::KernelVerified, TrustLevel::AxiomDependent)
        .unwrap_err();
    assert!(
        format!("{}", err).contains("trust violation"),
        "should be a trust violation"
    );
}

#[test]
fn test_trust_gate_kernel_to_certificate_violation() {
    let gate = TrustGate::default_policy();
    gate.check_dependency(TrustLevel::KernelVerified, TrustLevel::CertificateReplayed)
        .unwrap_err();
}

#[test]
fn test_trust_gate_kernel_to_partially_axiomatized_violation() {
    let gate = TrustGate::default_policy();
    gate.check_dependency(TrustLevel::KernelVerified, TrustLevel::PartiallyAxiomatized)
        .unwrap_err();
}

#[test]
fn test_trust_gate_kernel_to_oracle_violation() {
    let gate = TrustGate::default_policy();
    gate.check_dependency(TrustLevel::KernelVerified, TrustLevel::TrustedOracle)
        .unwrap_err();
}

#[test]
fn test_trust_gate_axiom_to_kernel_allowed() {
    let gate = TrustGate::default_policy();
    gate.check_dependency(TrustLevel::AxiomDependent, TrustLevel::KernelVerified)
        .expect("AxiomDependent -> KernelVerified should be allowed");
}

#[test]
fn test_trust_gate_axiom_to_axiom_allowed() {
    let gate = TrustGate::default_policy();
    gate.check_dependency(TrustLevel::AxiomDependent, TrustLevel::AxiomDependent)
        .expect("AxiomDependent -> AxiomDependent should be allowed");
}

#[test]
fn test_trust_gate_axiom_to_certificate_violation() {
    let gate = TrustGate::default_policy();
    gate.check_dependency(TrustLevel::AxiomDependent, TrustLevel::CertificateReplayed)
        .unwrap_err();
}

#[test]
fn test_trust_gate_certificate_to_kernel_allowed() {
    let gate = TrustGate::default_policy();
    gate.check_dependency(TrustLevel::CertificateReplayed, TrustLevel::KernelVerified)
        .expect("CertificateReplayed -> KernelVerified should be allowed");
}

#[test]
fn test_trust_gate_certificate_to_axiom_allowed() {
    let gate = TrustGate::default_policy();
    gate.check_dependency(TrustLevel::CertificateReplayed, TrustLevel::AxiomDependent)
        .expect("CertificateReplayed -> AxiomDependent should be allowed");
}

#[test]
fn test_trust_gate_certificate_to_certificate_allowed() {
    let gate = TrustGate::default_policy();
    gate.check_dependency(
        TrustLevel::CertificateReplayed,
        TrustLevel::CertificateReplayed,
    )
    .expect("CertificateReplayed -> CertificateReplayed should be allowed");
}

#[test]
fn test_trust_gate_certificate_to_partially_violation() {
    let gate = TrustGate::default_policy();
    gate.check_dependency(
        TrustLevel::CertificateReplayed,
        TrustLevel::PartiallyAxiomatized,
    )
    .unwrap_err();
}

#[test]
fn test_trust_gate_partially_to_all_lower_allowed() {
    let gate = TrustGate::default_policy();
    gate.check_dependency(TrustLevel::PartiallyAxiomatized, TrustLevel::KernelVerified)
        .expect("should be allowed");
    gate.check_dependency(TrustLevel::PartiallyAxiomatized, TrustLevel::AxiomDependent)
        .expect("should be allowed");
    gate.check_dependency(
        TrustLevel::PartiallyAxiomatized,
        TrustLevel::CertificateReplayed,
    )
    .expect("should be allowed");
    gate.check_dependency(
        TrustLevel::PartiallyAxiomatized,
        TrustLevel::PartiallyAxiomatized,
    )
    .expect("should be allowed");
}

#[test]
fn test_trust_gate_partially_to_oracle_violation() {
    let gate = TrustGate::default_policy();
    gate.check_dependency(TrustLevel::PartiallyAxiomatized, TrustLevel::TrustedOracle)
        .unwrap_err();
}

#[test]
fn test_trust_gate_oracle_allows_all() {
    let gate = TrustGate::default_policy();
    let all_levels = [
        TrustLevel::KernelVerified,
        TrustLevel::AxiomDependent,
        TrustLevel::CertificateReplayed,
        TrustLevel::PartiallyAxiomatized,
        TrustLevel::TrustedOracle,
    ];
    for &child in &all_levels {
        gate.check_dependency(TrustLevel::TrustedOracle, child)
            .unwrap_or_else(|_| {
                panic!("TrustedOracle -> {:?} should be allowed", child);
            });
    }
}

// ============================================================================
// TrustGate audit_graph tests
// ============================================================================

#[test]
fn test_trust_gate_audit_graph_no_violations() {
    let gate = TrustGate::default_policy();
    let mut graph = DependencyGraph::new(3);
    graph.add_edge(1, 0).expect("add edge");
    graph.add_edge(2, 1).expect("add edge");

    // All kernel-verified: should have no violations.
    let trust_levels = vec![
        TrustLevel::KernelVerified,
        TrustLevel::KernelVerified,
        TrustLevel::KernelVerified,
    ];

    let violations = gate.audit_graph(&graph, &trust_levels);
    assert!(
        violations.is_empty(),
        "expected no violations, got: {:?}",
        violations
    );
}

#[test]
fn test_trust_gate_audit_graph_single_violation() {
    let gate = TrustGate::default_policy();
    let mut graph = DependencyGraph::new(2);
    graph.add_edge(1, 0).expect("add edge");

    // Node 1 (KernelVerified) depends on node 0 (AxiomDependent) -> violation.
    let trust_levels = vec![TrustLevel::AxiomDependent, TrustLevel::KernelVerified];

    let violations = gate.audit_graph(&graph, &trust_levels);
    assert_eq!(violations.len(), 1);
    assert_eq!(violations[0].parent_idx, 1);
    assert_eq!(violations[0].parent_trust, TrustLevel::KernelVerified);
    assert_eq!(violations[0].child_idx, 0);
    assert_eq!(violations[0].child_trust, TrustLevel::AxiomDependent);
}

#[test]
fn test_trust_gate_audit_graph_multiple_violations() {
    let gate = TrustGate::default_policy();
    let mut graph = DependencyGraph::new(4);
    // Node 2 (Kernel) -> Node 0 (Axiom) and Node 1 (Oracle)
    graph.add_edge(2, 0).expect("add edge");
    graph.add_edge(2, 1).expect("add edge");
    // Node 3 (Kernel) -> Node 1 (Oracle)
    graph.add_edge(3, 1).expect("add edge");

    let trust_levels = vec![
        TrustLevel::AxiomDependent, // 0
        TrustLevel::TrustedOracle,  // 1
        TrustLevel::KernelVerified, // 2
        TrustLevel::KernelVerified, // 3
    ];

    let violations = gate.audit_graph(&graph, &trust_levels);
    assert_eq!(
        violations.len(),
        3,
        "expected 3 violations: {:?}",
        violations
    );
}

#[test]
fn test_trust_gate_audit_graph_valid_downward_deps() {
    let gate = TrustGate::default_policy();
    let mut graph = DependencyGraph::new(3);
    // Oracle -> PartiallyAxiomatized -> KernelVerified: all valid downward
    graph.add_edge(1, 0).expect("add edge");
    graph.add_edge(2, 1).expect("add edge");

    let trust_levels = vec![
        TrustLevel::KernelVerified,
        TrustLevel::PartiallyAxiomatized,
        TrustLevel::TrustedOracle,
    ];

    let violations = gate.audit_graph(&graph, &trust_levels);
    assert!(violations.is_empty());
}

// ============================================================================
// TrainingExportGate tests
// ============================================================================

#[test]
fn test_training_gate_kernel_none_exportable() {
    assert!(TrainingExportGate::can_export_for_training(
        AxiomProfile::NONE,
        TrustLevel::KernelVerified
    ));
}

#[test]
fn test_training_gate_kernel_classical_not_exportable() {
    assert!(!TrainingExportGate::can_export_for_training(
        AxiomProfile::CLASSICAL,
        TrustLevel::KernelVerified
    ));
}

#[test]
fn test_training_gate_axiom_none_not_exportable() {
    assert!(!TrainingExportGate::can_export_for_training(
        AxiomProfile::NONE,
        TrustLevel::AxiomDependent
    ));
}

#[test]
fn test_training_gate_oracle_none_not_exportable() {
    assert!(!TrainingExportGate::can_export_for_training(
        AxiomProfile::NONE,
        TrustLevel::TrustedOracle
    ));
}

#[test]
fn test_training_gate_certificate_none_not_exportable() {
    assert!(!TrainingExportGate::can_export_for_training(
        AxiomProfile::NONE,
        TrustLevel::CertificateReplayed
    ));
}

#[test]
fn test_training_gate_partially_axiomatized_not_exportable() {
    assert!(!TrainingExportGate::can_export_for_training(
        AxiomProfile::NONE,
        TrustLevel::PartiallyAxiomatized
    ));
}

#[test]
fn test_training_gate_filter_exportable() {
    let constants = vec![
        (AxiomProfile::NONE, TrustLevel::KernelVerified), // 0: exportable
        (AxiomProfile::CLASSICAL, TrustLevel::KernelVerified), // 1: not (axiom)
        (AxiomProfile::NONE, TrustLevel::AxiomDependent), // 2: not (trust)
        (AxiomProfile::NONE, TrustLevel::KernelVerified), // 3: exportable
        (AxiomProfile::HOL_EMBEDDING, TrustLevel::TrustedOracle), // 4: not (both)
    ];

    let exportable = TrainingExportGate::filter_exportable(&constants);
    assert_eq!(exportable, vec![0, 3]);
}

#[test]
fn test_training_gate_count_exportable() {
    let constants = vec![
        (AxiomProfile::NONE, TrustLevel::KernelVerified),
        (AxiomProfile::CLASSICAL, TrustLevel::AxiomDependent),
        (AxiomProfile::NONE, TrustLevel::KernelVerified),
        (AxiomProfile::NONE, TrustLevel::KernelVerified),
    ];
    assert_eq!(TrainingExportGate::count_exportable(&constants), 3);
}

#[test]
fn test_training_gate_filter_empty() {
    let constants: Vec<(AxiomProfile, TrustLevel)> = vec![];
    let exportable = TrainingExportGate::filter_exportable(&constants);
    assert!(exportable.is_empty());
}

#[test]
fn test_training_gate_filter_none_exportable() {
    let constants = vec![
        (AxiomProfile::CLASSICAL, TrustLevel::AxiomDependent),
        (AxiomProfile::HOL_EMBEDDING, TrustLevel::TrustedOracle),
    ];
    let exportable = TrainingExportGate::filter_exportable(&constants);
    assert!(exportable.is_empty());
}

// ============================================================================
// Combined: propagation + trust gate audit
// ============================================================================

#[test]
fn test_combined_propagation_then_audit() {
    // Build a graph where a kernel-verified node transitively depends on
    // an axiom-dependent node through an intermediate.
    let gate = TrustGate::default_policy();

    let mut graph = DependencyGraph::new(3);
    graph
        .set_initial_profile(0, AxiomProfile::CLASSICAL)
        .expect("set profile");
    graph.add_edge(1, 0).expect("add edge");
    graph.add_edge(2, 1).expect("add edge");

    graph.propagate().expect("propagation should succeed");

    // Even though node 2 is kernel-verified, its axiom profile now contains
    // CLASSICAL (propagated from node 0). The trust gate should detect that
    // node 2 (KernelVerified) depends on node 1 (AxiomDependent).
    let trust_levels = vec![
        TrustLevel::AxiomDependent, // 0: has CLASSICAL axiom
        TrustLevel::AxiomDependent, // 1: intermediate
        TrustLevel::KernelVerified, // 2: should not depend on axiom-dependent
    ];

    let violations = gate.audit_graph(&graph, &trust_levels);
    assert_eq!(violations.len(), 1);
    assert_eq!(violations[0].parent_idx, 2);
    assert_eq!(violations[0].child_idx, 1);
}

// ============================================================================
// Edge cases
// ============================================================================

#[test]
fn test_propagation_self_loop_detected_as_cycle() {
    let mut graph = DependencyGraph::new(1);
    graph.add_edge(0, 0).expect("add self-loop");

    let err = graph.propagate().unwrap_err();
    assert!(matches!(err, PropagationError::CycleDetected { .. }));
}

#[test]
fn test_propagation_preserves_existing_profile() {
    // Parent already has a profile; propagation should union, not replace.
    let mut graph = DependencyGraph::new(2);
    graph
        .set_initial_profile(0, AxiomProfile::CLASSICAL)
        .expect("set profile");
    graph
        .set_initial_profile(1, AxiomProfile::HOL_EMBEDDING)
        .expect("set profile");
    graph.add_edge(1, 0).expect("add edge");

    graph.propagate().expect("propagation should succeed");

    let profile = graph.profile(1);
    assert!(profile.contains(AxiomProfile::CLASSICAL));
    assert!(profile.contains(AxiomProfile::HOL_EMBEDDING));
}

#[test]
fn test_propagation_multiple_axioms_union() {
    // Two children with different axioms; parent should get union.
    let mut graph = DependencyGraph::new(3);
    graph
        .set_initial_profile(0, AxiomProfile::CLASSICAL)
        .expect("set profile");
    graph
        .set_initial_profile(1, AxiomProfile::CHOICE)
        .expect("set profile");
    graph.add_edge(2, 0).expect("add edge");
    graph.add_edge(2, 1).expect("add edge");

    graph.propagate().expect("propagation should succeed");

    let profile = graph.profile(2);
    assert!(profile.contains(AxiomProfile::CLASSICAL));
    assert!(profile.contains(AxiomProfile::CHOICE));
    assert!(!profile.contains(AxiomProfile::EXTENSIONALITY));
}

#[test]
fn test_trust_gate_has_policy_for() {
    let gate = TrustGate::default_policy();
    assert!(gate.has_policy_for(TrustLevel::KernelVerified));
    assert!(gate.has_policy_for(TrustLevel::AxiomDependent));
    assert!(gate.has_policy_for(TrustLevel::CertificateReplayed));
    assert!(gate.has_policy_for(TrustLevel::PartiallyAxiomatized));
    assert!(gate.has_policy_for(TrustLevel::TrustedOracle));
}

// ============================================================================
// Proptest: property-based tests
// ============================================================================

// ============================================================================
// DependencyGraphStats tests
// ============================================================================

#[test]
fn test_dependency_graph_stats_empty() {
    let graph = DependencyGraph::new(0);
    let stats = graph.compute_stats();
    assert_eq!(stats.nodes, 0);
    assert_eq!(stats.edges, 0);
    assert_eq!(stats.max_depth, 0);
    assert_eq!(stats.avg_degree, 0.0);
    assert!(!stats.cycles_detected);
}

#[test]
fn test_dependency_graph_stats_linear_chain() {
    let mut graph = DependencyGraph::new(5);
    graph.add_edge(1, 0).expect("edge");
    graph.add_edge(2, 1).expect("edge");
    graph.add_edge(3, 2).expect("edge");
    graph.add_edge(4, 3).expect("edge");

    let stats = graph.compute_stats();
    assert_eq!(stats.nodes, 5);
    assert_eq!(stats.edges, 4);
    assert_eq!(stats.max_depth, 4);
    assert!((stats.avg_degree - 0.8).abs() < 1e-10);
    assert!(!stats.cycles_detected);
}

#[test]
fn test_dependency_graph_stats_diamond() {
    let mut graph = DependencyGraph::new(4);
    graph.add_edge(1, 0).expect("edge");
    graph.add_edge(2, 0).expect("edge");
    graph.add_edge(3, 1).expect("edge");
    graph.add_edge(3, 2).expect("edge");

    let stats = graph.compute_stats();
    assert_eq!(stats.nodes, 4);
    assert_eq!(stats.edges, 4);
    assert_eq!(stats.max_depth, 2);
    assert!(!stats.cycles_detected);
}

#[test]
fn test_dependency_graph_stats_no_edges() {
    let graph = DependencyGraph::new(10);
    let stats = graph.compute_stats();
    assert_eq!(stats.nodes, 10);
    assert_eq!(stats.edges, 0);
    assert_eq!(stats.max_depth, 0);
    assert_eq!(stats.avg_degree, 0.0);
    assert!(!stats.cycles_detected);
}

#[test]
fn test_dependency_graph_stats_with_cycle() {
    let mut graph = DependencyGraph::new(2);
    graph.add_edge(0, 1).expect("edge");
    graph.add_edge(1, 0).expect("edge");

    let stats = graph.compute_stats();
    assert_eq!(stats.nodes, 2);
    assert_eq!(stats.edges, 2);
    assert!(stats.cycles_detected);
}

// ============================================================================
// Topological order tests
// ============================================================================

use crate::trust::axiom_propagation::CycleError;

#[test]
fn test_topological_order_empty_graph() {
    let graph = DependencyGraph::new(0);
    let order = graph.topological_order().expect("should succeed");
    assert!(order.is_empty());
}

#[test]
fn test_topological_order_single_node() {
    let graph = DependencyGraph::new(1);
    let order = graph.topological_order().expect("should succeed");
    assert_eq!(order, vec![0]);
}

#[test]
fn test_topological_order_linear_chain() {
    let mut graph = DependencyGraph::new(4);
    graph.add_edge(1, 0).expect("edge");
    graph.add_edge(2, 1).expect("edge");
    graph.add_edge(3, 2).expect("edge");

    let order = graph.topological_order().expect("should succeed");
    assert_eq!(order.len(), 4);

    // Node 0 should come before node 1, etc.
    let pos = |node: u32| order.iter().position(|&n| n == node).unwrap();
    assert!(pos(0) < pos(1));
    assert!(pos(1) < pos(2));
    assert!(pos(2) < pos(3));
}

#[test]
fn test_topological_order_diamond() {
    let mut graph = DependencyGraph::new(4);
    graph.add_edge(1, 0).expect("edge");
    graph.add_edge(2, 0).expect("edge");
    graph.add_edge(3, 1).expect("edge");
    graph.add_edge(3, 2).expect("edge");

    let order = graph.topological_order().expect("should succeed");
    assert_eq!(order.len(), 4);

    let pos = |node: u32| order.iter().position(|&n| n == node).unwrap();
    assert!(pos(0) < pos(1));
    assert!(pos(0) < pos(2));
    assert!(pos(1) < pos(3));
    assert!(pos(2) < pos(3));
}

#[test]
fn test_topological_order_cycle_detected() {
    let mut graph = DependencyGraph::new(3);
    graph.add_edge(0, 2).expect("edge");
    graph.add_edge(1, 0).expect("edge");
    graph.add_edge(2, 1).expect("edge");

    let err = graph.topological_order().unwrap_err();
    // CycleError should reference a node involved in the cycle.
    assert!(err.node < 3, "cycle node should be in range");
}

#[test]
fn test_topological_order_independent_components() {
    let mut graph = DependencyGraph::new(4);
    // Component 1: 1 -> 0
    graph.add_edge(1, 0).expect("edge");
    // Component 2: 3 -> 2
    graph.add_edge(3, 2).expect("edge");

    let order = graph.topological_order().expect("should succeed");
    assert_eq!(order.len(), 4);

    let pos = |node: u32| order.iter().position(|&n| n == node).unwrap();
    assert!(pos(0) < pos(1));
    assert!(pos(2) < pos(3));
}

// ============================================================================
// Reachable-from tests
// ============================================================================

#[test]
fn test_reachable_from_no_deps() {
    let graph = DependencyGraph::new(3);
    let reachable = graph.reachable_from(0);
    assert!(reachable.is_empty());
}

#[test]
fn test_reachable_from_linear_chain() {
    let mut graph = DependencyGraph::new(4);
    graph.add_edge(1, 0).expect("edge");
    graph.add_edge(2, 1).expect("edge");
    graph.add_edge(3, 2).expect("edge");

    let reachable = graph.reachable_from(3);
    assert_eq!(reachable.len(), 3);
    assert!(reachable.contains(&0));
    assert!(reachable.contains(&1));
    assert!(reachable.contains(&2));
    assert!(!reachable.contains(&3));
}

#[test]
fn test_reachable_from_diamond() {
    let mut graph = DependencyGraph::new(4);
    graph.add_edge(1, 0).expect("edge");
    graph.add_edge(2, 0).expect("edge");
    graph.add_edge(3, 1).expect("edge");
    graph.add_edge(3, 2).expect("edge");

    let reachable = graph.reachable_from(3);
    assert_eq!(reachable.len(), 3);
    assert!(reachable.contains(&0));
    assert!(reachable.contains(&1));
    assert!(reachable.contains(&2));
}

#[test]
fn test_reachable_from_leaf() {
    let mut graph = DependencyGraph::new(3);
    graph.add_edge(1, 0).expect("edge");
    graph.add_edge(2, 0).expect("edge");

    let reachable = graph.reachable_from(0);
    assert!(reachable.is_empty(), "leaf should have no reachable nodes");
}

#[test]
fn test_reachable_from_out_of_bounds() {
    let graph = DependencyGraph::new(2);
    let reachable = graph.reachable_from(99);
    assert!(reachable.is_empty());
}

// ============================================================================
// Incremental propagation tests
// ============================================================================

#[test]
fn test_incremental_propagation_new_edge() {
    let mut graph = DependencyGraph::new(3);
    graph
        .set_initial_profile(0, AxiomProfile::CLASSICAL)
        .expect("set profile");
    graph.add_edge(1, 0).expect("edge");
    graph.propagate().expect("initial propagation");
    assert_eq!(graph.profile(1), AxiomProfile::CLASSICAL);

    // Now add node 2 depending on node 1 and propagate incrementally.
    graph.add_edge(2, 1).expect("edge");
    graph
        .propagate_incremental(&[(2, 1)])
        .expect("incremental propagation");

    assert_eq!(graph.profile(2), AxiomProfile::CLASSICAL);
}

#[test]
fn test_incremental_propagation_matches_full() {
    // Build same graph twice: once full propagation, once incremental.
    let mut full_graph = DependencyGraph::new(4);
    full_graph
        .set_initial_profile(0, AxiomProfile::CLASSICAL)
        .expect("set");
    full_graph
        .set_initial_profile(1, AxiomProfile::EXTENSIONALITY)
        .expect("set");
    full_graph.add_edge(2, 0).expect("edge");
    full_graph.add_edge(2, 1).expect("edge");
    full_graph.add_edge(3, 2).expect("edge");
    full_graph.propagate().expect("full propagation");

    // Incremental: first propagate without the edge 3->2, then add it.
    let mut inc_graph = DependencyGraph::new(4);
    inc_graph
        .set_initial_profile(0, AxiomProfile::CLASSICAL)
        .expect("set");
    inc_graph
        .set_initial_profile(1, AxiomProfile::EXTENSIONALITY)
        .expect("set");
    inc_graph.add_edge(2, 0).expect("edge");
    inc_graph.add_edge(2, 1).expect("edge");
    inc_graph.propagate().expect("partial propagation");

    // Now add edge 3->2 and propagate incrementally.
    inc_graph.add_edge(3, 2).expect("edge");
    inc_graph
        .propagate_incremental(&[(3, 2)])
        .expect("incremental");

    // Both graphs should have identical profiles.
    for i in 0..4 {
        assert_eq!(
            full_graph.profile(i),
            inc_graph.profile(i),
            "node {} differs: full={:?} inc={:?}",
            i,
            full_graph.profile(i),
            inc_graph.profile(i)
        );
    }
}

#[test]
fn test_incremental_propagation_empty_edges() {
    let mut graph = DependencyGraph::new(2);
    graph
        .set_initial_profile(0, AxiomProfile::CLASSICAL)
        .expect("set");
    graph.propagate().expect("propagation");

    // Incremental with no new edges is a no-op.
    graph.propagate_incremental(&[]).expect("empty incremental");
    assert_eq!(graph.profile(0), AxiomProfile::CLASSICAL);
}

#[test]
fn test_incremental_propagation_out_of_bounds() {
    let mut graph = DependencyGraph::new(2);
    let err = graph.propagate_incremental(&[(0, 99)]).unwrap_err();
    assert!(matches!(
        err,
        PropagationError::NodeOutOfBounds { index: 99, .. }
    ));
}

// ============================================================================
// SelfVerificationSuite tests
// ============================================================================

use crate::trust::audit_report::{AuditFinding, AuditReportBuilder, AuditSeverity};
use crate::trust::verification::{SelfVerificationSuite, VerificationEvidence, VerificationSuite};

#[test]
fn test_self_verification_propagation_completeness_valid() {
    let mut graph = DependencyGraph::new(4);
    graph
        .set_initial_profile(0, AxiomProfile::CLASSICAL)
        .expect("set");
    graph
        .set_initial_profile(1, AxiomProfile::EXTENSIONALITY)
        .expect("set");
    graph.add_edge(2, 0).expect("edge");
    graph.add_edge(2, 1).expect("edge");
    graph.add_edge(3, 2).expect("edge");
    graph.propagate().expect("propagation");

    let suite = SelfVerificationSuite::new();
    let result = suite.verify_propagation_completeness(&graph);
    assert!(result.passed, "evidence: {}", result.evidence);
    assert!(result.checked_count > 0);
}

#[test]
fn test_self_verification_propagation_completeness_unpropagated() {
    let mut graph = DependencyGraph::new(3);
    graph
        .set_initial_profile(0, AxiomProfile::CLASSICAL)
        .expect("set");
    graph.add_edge(1, 0).expect("edge");
    graph.add_edge(2, 1).expect("edge");
    // Skip propagation.

    let suite = SelfVerificationSuite::new();
    let result = suite.verify_propagation_completeness(&graph);
    assert!(!result.passed, "should fail on unpropagated graph");
}

#[test]
fn test_self_verification_training_gate_soundness() {
    let suite = SelfVerificationSuite::new();
    let result = suite.verify_training_gate_soundness();
    assert!(result.passed, "evidence: {}", result.evidence);
    assert!(result.checked_count >= 17 * 5); // 17 profiles * 5 trust levels
}

#[test]
fn test_self_verification_trust_hierarchy_transitivity() {
    let gate = TrustGate::default_policy();
    let suite = SelfVerificationSuite::new();
    let result = suite.verify_trust_hierarchy_transitivity(&gate);
    assert!(result.passed, "evidence: {}", result.evidence);
    assert!(result.checked_count > 0);
}

#[test]
fn test_self_verification_audit_report_completeness_valid() {
    let mut graph = DependencyGraph::new(2);
    graph.add_edge(1, 0).expect("edge");

    let trust_levels = vec![TrustLevel::TrustedOracle, TrustLevel::KernelVerified];
    let gate = TrustGate::default_policy();

    // Build an audit report that includes the violations.
    let violations = gate.audit_graph(&graph, &trust_levels);
    let mut builder = AuditReportBuilder::new();
    builder.add_constant(TrustLevel::TrustedOracle, "SMT", AxiomProfile::SMT_ORACLE);
    builder.add_constant(TrustLevel::KernelVerified, "Lean4", AxiomProfile::NONE);
    for v in &violations {
        builder.add_violation(v.clone());
    }
    let report = builder.build();

    let suite = SelfVerificationSuite::new();
    let result = suite.verify_audit_report_completeness(&graph, &trust_levels, &gate, &report);
    assert!(result.passed, "evidence: {}", result.evidence);
}

#[test]
fn test_self_verification_audit_report_completeness_missing_violation() {
    let mut graph = DependencyGraph::new(2);
    graph.add_edge(1, 0).expect("edge");

    let trust_levels = vec![TrustLevel::TrustedOracle, TrustLevel::KernelVerified];
    let gate = TrustGate::default_policy();

    // Build an audit report that omits the violation.
    let builder = AuditReportBuilder::new();
    let report = builder.build();

    let suite = SelfVerificationSuite::new();
    let result = suite.verify_audit_report_completeness(&graph, &trust_levels, &gate, &report);
    assert!(
        !result.passed,
        "should fail when violations are missing from report"
    );
}

#[test]
fn test_self_verification_verify_all_properties() {
    let mut graph = DependencyGraph::new(3);
    graph
        .set_initial_profile(0, AxiomProfile::CLASSICAL)
        .expect("set");
    graph.add_edge(1, 0).expect("edge");
    graph.add_edge(2, 1).expect("edge");
    graph.propagate().expect("propagation");

    let trust_levels = vec![
        TrustLevel::AxiomDependent,
        TrustLevel::AxiomDependent,
        TrustLevel::TrustedOracle,
    ];
    let gate = TrustGate::default_policy();

    // Build complete audit report.
    let violations = gate.audit_graph(&graph, &trust_levels);
    let mut builder = AuditReportBuilder::new();
    for (i, tl) in trust_levels.iter().enumerate() {
        builder.add_constant(*tl, "test", graph.profile(i as u32));
    }
    for v in &violations {
        builder.add_violation(v.clone());
    }
    let report = builder.build();

    let suite = SelfVerificationSuite::new();
    let evidence = suite.verify_all_properties(&graph, &trust_levels, &gate, &report);
    assert!(evidence.all_passed, "summary: {}", evidence.summary());
    assert_eq!(evidence.properties_checked, 4);
    assert_eq!(evidence.properties_failed, 0);
}

// ============================================================================
// VerificationEvidence tests
// ============================================================================

use crate::trust::verification::{VerificationProperty, VerificationResult};

#[test]
fn test_verification_evidence_from_results_all_pass() {
    let results = vec![
        VerificationResult {
            property: VerificationProperty::PropagationMonotonicity,
            passed: true,
            evidence: "ok".to_owned(),
            checked_count: 10,
        },
        VerificationResult {
            property: VerificationProperty::PropagationIdempotency,
            passed: true,
            evidence: "ok".to_owned(),
            checked_count: 5,
        },
    ];
    let evidence = VerificationEvidence::from_results(results);
    assert!(evidence.all_passed);
    assert_eq!(evidence.properties_checked, 2);
    assert_eq!(evidence.properties_passed, 2);
    assert_eq!(evidence.properties_failed, 0);
    assert_eq!(evidence.total_checks, 15);
}

#[test]
fn test_verification_evidence_from_results_with_failure() {
    let results = vec![
        VerificationResult {
            property: VerificationProperty::PropagationMonotonicity,
            passed: true,
            evidence: "ok".to_owned(),
            checked_count: 10,
        },
        VerificationResult {
            property: VerificationProperty::NoTrustLeakage,
            passed: false,
            evidence: "violation found".to_owned(),
            checked_count: 3,
        },
    ];
    let evidence = VerificationEvidence::from_results(results);
    assert!(!evidence.all_passed);
    assert_eq!(evidence.properties_failed, 1);
    assert_eq!(evidence.properties_passed, 1);
}

#[test]
fn test_verification_evidence_summary_contains_status() {
    let results = vec![VerificationResult {
        property: VerificationProperty::TrustGateCompleteness,
        passed: true,
        evidence: "all good".to_owned(),
        checked_count: 5,
    }];
    let evidence = VerificationEvidence::from_results(results);
    let summary = evidence.summary();
    assert!(summary.contains("PASS"));
    assert!(summary.contains("1/1"));
}

// ============================================================================
// Audit report formatting tests
// ============================================================================

use crate::trust::audit_report::{
    compare_reports, AuditComparison, AuditReport, AuditReportFormat,
};

#[test]
fn test_audit_report_to_json_empty() {
    let report = AuditReportBuilder::new().build();
    let json = report.to_json();
    assert!(json.contains("\"total_constants\": 0"));
    assert!(json.contains("\"status\": \"CLEAN\""));
    assert!(json.contains("\"trust_violations_count\": 0"));
}

#[test]
fn test_audit_report_to_json_with_constants() {
    let mut builder = AuditReportBuilder::new();
    builder.add_constant(TrustLevel::KernelVerified, "Lean4", AxiomProfile::NONE);
    builder.add_constant(TrustLevel::TrustedOracle, "SMT", AxiomProfile::SMT_ORACLE);
    let report = builder.build();

    let json = report.to_json();
    assert!(json.contains("\"total_constants\": 2"));
    assert!(json.contains("\"exportable_for_training\": 1"));
    assert!(json.contains("\"KernelVerified\": 1"));
    assert!(json.contains("\"TrustedOracle\": 1"));
}

#[test]
fn test_audit_report_to_markdown_empty() {
    let report = AuditReportBuilder::new().build();
    let md = report.to_markdown();
    assert!(md.contains("# Mathverse Trust Audit Report"));
    assert!(md.contains("**Status:** CLEAN"));
    assert!(md.contains("| Total constants | 0 |"));
}

#[test]
fn test_audit_report_to_markdown_with_findings() {
    let mut builder = AuditReportBuilder::new();
    builder.add_constant(TrustLevel::KernelVerified, "Lean4", AxiomProfile::NONE);
    builder.add_finding(AuditFinding {
        severity: AuditSeverity::Warning,
        category: "axiom-gap".to_owned(),
        message: "potential gap".to_owned(),
        node_indices: vec![0],
        recommendation: Some("investigate".to_owned()),
    });
    let report = builder.build();

    let md = report.to_markdown();
    assert!(md.contains("## Findings"));
    assert!(md.contains("[Warning]"));
    assert!(md.contains("axiom-gap"));
    assert!(md.contains("*Recommendation:*"));
}

#[test]
fn test_audit_report_to_markdown_with_violations() {
    let mut builder = AuditReportBuilder::new();
    builder.add_violation(crate::trust::graph_gate::TrustViolation {
        parent_idx: 1,
        parent_trust: TrustLevel::KernelVerified,
        child_idx: 0,
        child_trust: TrustLevel::TrustedOracle,
        violation: "kernel depends on oracle".to_owned(),
    });
    let report = builder.build();

    let md = report.to_markdown();
    assert!(md.contains("## Trust Violations"));
    assert!(md.contains("ISSUES FOUND"));
}

#[test]
fn test_audit_report_format_text() {
    let report = AuditReportBuilder::new().build();
    let text = report.format(AuditReportFormat::Text);
    assert!(text.contains("=== Mathverse Trust Audit Report ==="));
}

#[test]
fn test_audit_report_format_json() {
    let report = AuditReportBuilder::new().build();
    let json = report.format(AuditReportFormat::Json);
    assert!(json.starts_with('{'));
    assert!(json.ends_with('}'));
}

#[test]
fn test_audit_report_format_markdown() {
    let report = AuditReportBuilder::new().build();
    let md = report.format(AuditReportFormat::Markdown);
    assert!(md.contains("# Mathverse Trust Audit Report"));
}

// ============================================================================
// AuditComparison regression detection tests
// ============================================================================

#[test]
fn test_compare_reports_identical() {
    let mut builder = AuditReportBuilder::new();
    builder.add_constant(TrustLevel::KernelVerified, "Lean4", AxiomProfile::NONE);
    let report = builder.build();

    let comparison = compare_reports(&report, &report);
    assert_eq!(comparison.constants_delta, 0);
    assert_eq!(comparison.violations_delta, 0);
    assert!(!comparison.is_regression);
    assert!(!comparison.is_improvement);
}

#[test]
fn test_compare_reports_improvement() {
    // Old report: 1 violation.
    let mut old_builder = AuditReportBuilder::new();
    old_builder.add_constant(TrustLevel::KernelVerified, "Lean4", AxiomProfile::NONE);
    old_builder.add_violation(crate::trust::graph_gate::TrustViolation {
        parent_idx: 0,
        parent_trust: TrustLevel::KernelVerified,
        child_idx: 1,
        child_trust: TrustLevel::TrustedOracle,
        violation: "test".to_owned(),
    });
    let old_report = old_builder.build();

    // New report: 0 violations.
    let mut new_builder = AuditReportBuilder::new();
    new_builder.add_constant(TrustLevel::KernelVerified, "Lean4", AxiomProfile::NONE);
    let new_report = new_builder.build();

    let comparison = compare_reports(&old_report, &new_report);
    assert_eq!(comparison.violations_delta, -1);
    assert!(comparison.is_improvement);
    assert!(!comparison.is_regression);
}

#[test]
fn test_compare_reports_regression() {
    // Old report: clean.
    let old_report = AuditReportBuilder::new().build();

    // New report: has a critical finding.
    let mut new_builder = AuditReportBuilder::new();
    new_builder.add_finding(AuditFinding {
        severity: AuditSeverity::Critical,
        category: "trust-leak".to_owned(),
        message: "new issue".to_owned(),
        node_indices: vec![],
        recommendation: None,
    });
    let new_report = new_builder.build();

    let comparison = compare_reports(&old_report, &new_report);
    assert!(comparison.is_regression);
    assert!(comparison
        .new_finding_categories
        .contains(&"trust-leak".to_owned()));
}

#[test]
fn test_compare_reports_resolved_categories() {
    // Old report: has a warning finding.
    let mut old_builder = AuditReportBuilder::new();
    old_builder.add_finding(AuditFinding {
        severity: AuditSeverity::Warning,
        category: "axiom-gap".to_owned(),
        message: "old issue".to_owned(),
        node_indices: vec![],
        recommendation: None,
    });
    let old_report = old_builder.build();

    // New report: no findings.
    let new_report = AuditReportBuilder::new().build();

    let comparison = compare_reports(&old_report, &new_report);
    assert!(comparison
        .resolved_finding_categories
        .contains(&"axiom-gap".to_owned()));
    assert!(comparison.is_improvement);
}

#[test]
fn test_compare_reports_more_constants() {
    let mut old_builder = AuditReportBuilder::new();
    old_builder.add_constant(TrustLevel::KernelVerified, "Lean4", AxiomProfile::NONE);
    let old_report = old_builder.build();

    let mut new_builder = AuditReportBuilder::new();
    new_builder.add_constant(TrustLevel::KernelVerified, "Lean4", AxiomProfile::NONE);
    new_builder.add_constant(TrustLevel::KernelVerified, "Lean4", AxiomProfile::NONE);
    let new_report = new_builder.build();

    let comparison = compare_reports(&old_report, &new_report);
    assert_eq!(comparison.constants_delta, 1);
    assert_eq!(comparison.exportable_delta, 1);
}

// ============================================================================
// Edge count test
// ============================================================================

#[test]
fn test_dependency_graph_edge_count() {
    let mut graph = DependencyGraph::new(4);
    assert_eq!(graph.edge_count(), 0);

    graph.add_edge(1, 0).expect("edge");
    graph.add_edge(2, 0).expect("edge");
    graph.add_edge(3, 1).expect("edge");
    graph.add_edge(3, 2).expect("edge");
    assert_eq!(graph.edge_count(), 4);
}

// ============================================================================
// Proptest: property-based tests
// ============================================================================

mod proptest_tests {
    use super::*;
    use proptest::prelude::*;

    /// Strategy to generate a random DAG with `n` nodes.
    /// For each pair (i, j) where j < i, include the edge with probability `p`.
    fn random_dag(n: usize, edge_probability: f64) -> impl Strategy<Value = Vec<Vec<u32>>> {
        let n_edges = n * (n.saturating_sub(1)) / 2;
        proptest::collection::vec(proptest::bool::weighted(edge_probability), n_edges).prop_map(
            move |bits| {
                let mut edges = vec![Vec::new(); n];
                let mut bit_idx = 0;
                for (i, edge_list) in edges.iter_mut().enumerate() {
                    for j in 0..i {
                        if bit_idx < bits.len() && bits[bit_idx] {
                            edge_list.push(j as u32);
                        }
                        bit_idx += 1;
                    }
                }
                edges
            },
        )
    }

    /// Strategy for random axiom profiles (u64 bitvectors).
    fn random_axiom_profile() -> impl Strategy<Value = AxiomProfile> {
        // Use only the defined axiom bits (bits 0-3, 8-18, 24-25).
        let valid_bits: u64 = AxiomProfile::CLASSICAL.0
            | AxiomProfile::EXTENSIONALITY.0
            | AxiomProfile::CHOICE.0
            | AxiomProfile::PROOF_IRRELEVANCE.0
            | AxiomProfile::HOL_EMBEDDING.0
            | AxiomProfile::MIZAR_SOFT_TYPE.0
            | AxiomProfile::COQ_SPROP.0
            | AxiomProfile::COQ_MODULE_FUNCTOR.0
            | AxiomProfile::COQ_COINDUCTIVE.0
            | AxiomProfile::ISABELLE_LCF_ERASED.0
            | AxiomProfile::AGDA_CUBICAL.0
            | AxiomProfile::IDRIS_QTT.0
            | AxiomProfile::SMT_ORACLE.0
            | AxiomProfile::SAT_CERT.0
            | AxiomProfile::ATP_CERT.0
            | AxiomProfile::FLOAT_APPROX.0
            | AxiomProfile::NN_ABSTRACTION.0;

        (0u64..=valid_bits).prop_map(move |v| AxiomProfile(v & valid_bits))
    }

    /// Strategy for random trust levels.
    fn random_trust_level() -> impl Strategy<Value = TrustLevel> {
        prop_oneof![
            Just(TrustLevel::KernelVerified),
            Just(TrustLevel::AxiomDependent),
            Just(TrustLevel::CertificateReplayed),
            Just(TrustLevel::PartiallyAxiomatized),
            Just(TrustLevel::TrustedOracle),
        ]
    }

    proptest! {
        /// For any random DAG: propagate -> verify_invariant always holds.
        #[test]
        fn prop_propagation_invariant_holds(
            edges in random_dag(20, 0.3),
            profiles in proptest::collection::vec(random_axiom_profile(), 20),
        ) {
            let n = edges.len();
            let mut graph = DependencyGraph::new(n);

            for (i, &profile) in profiles.iter().enumerate().take(n) {
                graph.set_initial_profile(i as u32, profile)
                    .expect("set profile");
            }

            // Set edges (they already satisfy topological order: j < i).
            for (i, deps) in edges.iter().enumerate() {
                for &dep in deps {
                    graph.add_edge(i as u32, dep)
                        .expect("add edge");
                }
            }

            graph.propagate().expect("DAG propagation should succeed");
            graph.verify_invariant().expect("invariant must hold after propagation");
        }

        /// Propagated profile is always a superset of the initial profile.
        #[test]
        fn prop_propagation_preserves_initial(
            edges in random_dag(15, 0.2),
            profiles in proptest::collection::vec(random_axiom_profile(), 15),
        ) {
            let n = edges.len();
            let mut graph = DependencyGraph::new(n);
            let initial_profiles: Vec<AxiomProfile> = profiles.iter().copied().take(n).collect();

            for (i, &profile) in initial_profiles.iter().enumerate() {
                graph.set_initial_profile(i as u32, profile)
                    .expect("set profile");
            }

            for (i, deps) in edges.iter().enumerate() {
                for &dep in deps {
                    graph.add_edge(i as u32, dep)
                        .expect("add edge");
                }
            }

            graph.propagate().expect("DAG propagation should succeed");

            for (i, &initial) in initial_profiles.iter().enumerate() {
                let propagated = graph.profile(i as u32);
                prop_assert!(
                    propagated.is_superset_of(initial),
                    "node {} propagated {:?} is not a superset of initial {:?}",
                    i, propagated, initial
                );
            }
        }

        /// audit_graph finds all violations for random trust level assignments.
        #[test]
        fn prop_audit_finds_all_violations(
            edges in random_dag(10, 0.3),
            trust_levels in proptest::collection::vec(random_trust_level(), 10),
        ) {
            let n = edges.len();
            let gate = TrustGate::default_policy();
            let mut graph = DependencyGraph::new(n);

            for (i, deps) in edges.iter().enumerate() {
                for &dep in deps {
                    graph.add_edge(i as u32, dep)
                        .expect("add edge");
                }
            }

            let violations = gate.audit_graph(&graph, &trust_levels);

            // Manually count expected violations.
            let mut expected_count = 0;
            for (parent_idx, deps) in edges.iter().enumerate() {
                if parent_idx >= trust_levels.len() {
                    continue;
                }
                let parent_trust = trust_levels[parent_idx];
                for &child_idx in deps {
                    if (child_idx as usize) >= trust_levels.len() {
                        continue;
                    }
                    let child_trust = trust_levels[child_idx as usize];
                    if gate.check_dependency(parent_trust, child_trust).is_err() {
                        expected_count += 1;
                    }
                }
            }

            prop_assert_eq!(
                violations.len(), expected_count,
                "audit_graph should find exactly the violations that check_dependency rejects"
            );
        }

        /// TrainingExportGate: only NONE profile + KernelVerified passes.
        #[test]
        fn prop_training_gate_strict(
            profile in random_axiom_profile(),
            trust in random_trust_level(),
        ) {
            let exportable = TrainingExportGate::can_export_for_training(profile, trust);
            let expected = profile.is_kernel_verified() && trust == TrustLevel::KernelVerified;
            prop_assert_eq!(
                exportable, expected,
                "profile={:?} trust={:?}: expected={} got={}",
                profile, trust, expected, exportable
            );
        }

        /// Propagation is idempotent: calling propagate twice gives the same result.
        #[test]
        fn prop_propagation_idempotent(
            edges in random_dag(12, 0.25),
            profiles in proptest::collection::vec(random_axiom_profile(), 12),
        ) {
            let n = edges.len();

            // First propagation
            let mut graph1 = DependencyGraph::new(n);
            for (i, &profile) in profiles.iter().enumerate().take(n) {
                graph1.set_initial_profile(i as u32, profile).expect("set");
            }
            for (i, deps) in edges.iter().enumerate() {
                for &dep in deps {
                    graph1.add_edge(i as u32, dep).expect("add");
                }
            }
            graph1.propagate().expect("propagation 1");

            // Collect profiles after first propagation
            let after_first: Vec<AxiomProfile> =
                (0..n).map(|i| graph1.profile(i as u32)).collect();

            // Second propagation (on already-propagated data)
            graph1.propagate().expect("propagation 2");

            // Profiles should not change
            for (i, &expected) in after_first.iter().enumerate() {
                prop_assert_eq!(
                    graph1.profile(i as u32), expected,
                    "propagation should be idempotent at node {}",
                    i
                );
            }
        }

        /// Random DAGs maintain propagation completeness: after propagation,
        /// every reachable node's profile is included in the ancestor's profile.
        #[test]
        fn prop_propagation_completeness(
            edges in random_dag(10, 0.25),
            profiles in proptest::collection::vec(random_axiom_profile(), 10),
        ) {
            let n = edges.len();
            let mut graph = DependencyGraph::new(n);

            for (i, &profile) in profiles.iter().enumerate().take(n) {
                graph.set_initial_profile(i as u32, profile).expect("set");
            }
            for (i, deps) in edges.iter().enumerate() {
                for &dep in deps {
                    graph.add_edge(i as u32, dep).expect("add");
                }
            }
            graph.propagate().expect("propagation");

            // For each node, check all reachable nodes.
            for i in 0..n {
                let node_profile = graph.profile(i as u32);
                let reachable = graph.reachable_from(i as u32);
                for &dep in &reachable {
                    let dep_profile = graph.profile(dep);
                    prop_assert!(
                        node_profile.is_superset_of(dep_profile),
                        "node {} ({:?}) does not contain reachable {} ({:?})",
                        i, node_profile, dep, dep_profile
                    );
                }
            }
        }

        /// Topological order is valid for random DAGs (no cycles by construction).
        #[test]
        fn prop_topological_order_valid_for_dags(
            edges in random_dag(15, 0.3),
        ) {
            let n = edges.len();
            let mut graph = DependencyGraph::new(n);
            for (i, deps) in edges.iter().enumerate() {
                for &dep in deps {
                    graph.add_edge(i as u32, dep).expect("add");
                }
            }

            let order = graph.topological_order()
                .expect("DAG should have a valid topological order");
            prop_assert_eq!(order.len(), n);

            // Verify: for each edge (parent, child), child appears before parent.
            let mut position = vec![0usize; n];
            for (pos, &node) in order.iter().enumerate() {
                position[node as usize] = pos;
            }
            for (parent, deps) in edges.iter().enumerate() {
                for &child in deps {
                    prop_assert!(
                        position[child as usize] < position[parent],
                        "child {} (pos {}) should appear before parent {} (pos {})",
                        child, position[child as usize], parent, position[parent]
                    );
                }
            }
        }

        /// DependencyGraphStats: node count and edge count match the graph.
        #[test]
        fn prop_graph_stats_consistent(
            edges in random_dag(10, 0.3),
        ) {
            let n = edges.len();
            let mut graph = DependencyGraph::new(n);
            let mut expected_edges = 0;
            for (i, deps) in edges.iter().enumerate() {
                for &dep in deps {
                    graph.add_edge(i as u32, dep).expect("add");
                    expected_edges += 1;
                }
            }

            let stats = graph.compute_stats();
            prop_assert_eq!(stats.nodes, n);
            prop_assert_eq!(stats.edges, expected_edges);
            prop_assert!(!stats.cycles_detected, "DAG should not have cycles");
        }

        /// Incremental propagation matches full propagation on random DAGs.
        #[test]
        fn prop_incremental_matches_full(
            edges in random_dag(8, 0.2),
            profiles in proptest::collection::vec(random_axiom_profile(), 8),
        ) {
            let n = edges.len();
            if n < 2 {
                return Ok(());
            }

            // Full propagation.
            let mut full_graph = DependencyGraph::new(n);
            for (i, &profile) in profiles.iter().enumerate().take(n) {
                full_graph.set_initial_profile(i as u32, profile).expect("set");
            }
            for (i, deps) in edges.iter().enumerate() {
                for &dep in deps {
                    full_graph.add_edge(i as u32, dep).expect("add");
                }
            }
            full_graph.propagate().expect("full propagation");

            // Incremental: first propagate without the last node's edges,
            // then add them incrementally.
            let last = n - 1;
            let mut inc_graph = DependencyGraph::new(n);
            for (i, &profile) in profiles.iter().enumerate().take(n) {
                inc_graph.set_initial_profile(i as u32, profile).expect("set");
            }
            // Add all edges except those from the last node.
            for (i, deps) in edges.iter().enumerate() {
                if i == last {
                    continue;
                }
                for &dep in deps {
                    inc_graph.add_edge(i as u32, dep).expect("add");
                }
            }
            inc_graph.propagate().expect("partial propagation");

            // Now add last node's edges and propagate incrementally.
            let new_edges: Vec<(u32, u32)> = edges[last]
                .iter()
                .map(|&dep| (last as u32, dep))
                .collect();
            for &(from, to) in &new_edges {
                inc_graph.add_edge(from, to).expect("add");
            }
            inc_graph.propagate_incremental(&new_edges).expect("incremental");

            // Compare profiles.
            for i in 0..n {
                prop_assert_eq!(
                    full_graph.profile(i as u32),
                    inc_graph.profile(i as u32),
                    "node {} differs: full={:?} inc={:?}",
                    i, full_graph.profile(i as u32), inc_graph.profile(i as u32)
                );
            }
        }
    }
}
