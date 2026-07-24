// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Self-verification proofs as Rust tests: codec round-trip, hash-consing
//! correctness, topological sort invariant, and axiom profile propagation.

use crate::shard::{ShardReader, ShardWriter};
use crate::types::{
    AxiomProfile, ContentDomain, ImportConfidence, MathverseConstantHeader, SourceSystem,
};
use clean_kernel::flat::{FlatExpr, FlatLevel};

// ======================================================================
// Helpers
// ======================================================================

/// Build a test shard with one constant referencing `type_idx` and `value_idx`.
fn build_test_shard(writer: &mut ShardWriter, type_idx: u32, value_idx: u32) {
    let s = writer.add_string("test");
    writer.add_constant(MathverseConstantHeader {
        name_idx: s,
        type_idx,
        value_idx,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::KernelVerified as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: 0,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    });
}

/// Write a shard to bytes and read it back.
fn round_trip(writer: &ShardWriter) -> ShardReader {
    let mut buf = Vec::new();
    writer.write(&mut buf).unwrap();
    ShardReader::from_bytes(&buf).unwrap()
}

/// Extract expression references from a FlatExpr (sub-expression indices).
fn extract_expr_refs(expr: &FlatExpr) -> Vec<u32> {
    let d = &expr.data;
    let r =
        |off: usize| -> u32 { u32::from_le_bytes([d[off], d[off + 1], d[off + 2], d[off + 3]]) };
    match expr.tag {
        0 | 1 | 2 | 7 | 8 | 10 => vec![],
        3 => vec![r(0), r(4)],
        4 | 5 => {
            let ty = u32::from_le_bytes([d[1], d[2], d[3], d[4]]);
            let body = u32::from_le_bytes([d[5], d[6], d[7], d[8]]);
            vec![ty, body]
        }
        6 => vec![r(0), r(4), r(8)],
        9 => vec![r(6)],
        _ => vec![],
    }
}

// ======================================================================
// FlatExpr codec round-trip
// ======================================================================

#[test]
fn test_self_verify_flatexpr_codec_round_trip_exprs() {
    let mut writer = ShardWriter::new();
    let l0 = writer.add_level(FlatLevel::zero());
    let e_sort = writer.add_expr(FlatExpr::sort(l0));
    let e_bvar = writer.add_expr(FlatExpr::bvar(42));
    let e_app = writer.add_expr(FlatExpr::app(e_sort, e_bvar));
    let s0 = writer.add_string("Nat.add");
    let e_const = writer.add_expr(FlatExpr::const_ref(s0, u32::MAX));
    let e_lam = writer.add_expr(FlatExpr::lam(0, e_sort, e_bvar));
    let e_pi = writer.add_expr(FlatExpr::pi(1, e_sort, e_sort));
    let e_let = writer.add_expr(FlatExpr::let_expr(e_sort, e_bvar, e_app));
    let e_nat = writer.add_expr(FlatExpr::lit_nat(12345));
    let s1 = writer.add_string("hello");
    let e_str = writer.add_expr(FlatExpr::lit_str(s1));
    let e_fvar = writer.add_expr(FlatExpr::fvar(99));

    let expected: Vec<(u32, FlatExpr)> = vec![
        (e_sort, FlatExpr::sort(l0)),
        (e_bvar, FlatExpr::bvar(42)),
        (e_app, FlatExpr::app(e_sort, e_bvar)),
        (e_const, FlatExpr::const_ref(s0, u32::MAX)),
        (e_lam, FlatExpr::lam(0, e_sort, e_bvar)),
        (e_pi, FlatExpr::pi(1, e_sort, e_sort)),
        (e_let, FlatExpr::let_expr(e_sort, e_bvar, e_app)),
        (e_nat, FlatExpr::lit_nat(12345)),
        (e_str, FlatExpr::lit_str(s1)),
        (e_fvar, FlatExpr::fvar(99)),
    ];

    build_test_shard(&mut writer, e_sort, e_app);
    let reader = round_trip(&writer);

    for (idx, orig) in &expected {
        let rest = &reader.exprs[*idx as usize];
        assert_eq!(orig.tag, rest.tag, "tag mismatch at expr {idx}");
        assert_eq!(orig.flags, rest.flags, "flags mismatch at expr {idx}");
        assert_eq!(orig.data, rest.data, "data mismatch at expr {idx}");
    }
}

#[test]
fn test_self_verify_flatexpr_codec_round_trip_levels() {
    let mut writer = ShardWriter::new();
    let l0 = writer.add_level(FlatLevel::zero());
    let l1 = writer.add_level(FlatLevel::succ(l0));
    let l2 = writer.add_level(FlatLevel::max(l0, l1));
    let e0 = writer.add_expr(FlatExpr::sort(l0));

    let expected: Vec<(u32, FlatLevel)> = vec![
        (l0, FlatLevel::zero()),
        (l1, FlatLevel::succ(l0)),
        (l2, FlatLevel::max(l0, l1)),
    ];

    build_test_shard(&mut writer, e0, e0);
    let reader = round_trip(&writer);

    for (idx, orig) in &expected {
        let rest = &reader.levels[*idx as usize];
        assert_eq!(orig.tag, rest.tag, "level tag mismatch at {idx}");
        assert_eq!(orig.data, rest.data, "level data mismatch at {idx}");
    }
}

// ======================================================================
// Hash-consing correctness
// ======================================================================

#[test]
fn test_self_verify_hash_consing_correctness() {
    let mut writer = ShardWriter::new();

    let e0 = writer.add_expr(FlatExpr::sort(0));
    let e1 = writer.add_expr(FlatExpr::sort(0));
    let e2 = writer.add_expr(FlatExpr::sort(0));
    assert_eq!(e0, e1, "identical exprs must get the same index");
    assert_eq!(e1, e2, "identical exprs must get the same index");

    let e3 = writer.add_expr(FlatExpr::sort(1));
    let e4 = writer.add_expr(FlatExpr::bvar(0));
    assert_ne!(e0, e3, "different exprs must get different indices");
    assert_ne!(e0, e4, "different exprs must get different indices");

    let l0 = writer.add_level(FlatLevel::zero());
    let l1 = writer.add_level(FlatLevel::zero());
    assert_eq!(l0, l1, "identical levels must get the same index");
    let l2 = writer.add_level(FlatLevel::succ(0));
    assert_ne!(l0, l2, "different levels must get different indices");

    let s0 = writer.add_string("Nat");
    let s1 = writer.add_string("Nat");
    assert_eq!(s0, s1, "identical strings must get the same index");
    let s2 = writer.add_string("Bool");
    assert_ne!(s0, s2, "different strings must get different indices");

    let stats = writer.dedup_stats();
    assert_eq!(stats.exprs_total, 5);
    assert_eq!(stats.exprs_deduped, 2);
    // FlatLevel::zero is pre-seeded with its dedup entry, so both
    // add_level(zero) calls are dedup hits. Only succ(0) is unique.
    assert_eq!(stats.levels_total, 3);
    assert_eq!(stats.levels_deduped, 2);
    assert_eq!(stats.strings_total, 3);
    assert_eq!(stats.strings_deduped, 1);
}

// ======================================================================
// Topological sort: child_idx < parent_idx
// ======================================================================

#[test]
fn test_self_verify_topological_sort_invariant() {
    let mut writer = ShardWriter::new();
    let l0 = writer.add_level(FlatLevel::zero());
    let e0 = writer.add_expr(FlatExpr::sort(l0));
    let e1 = writer.add_expr(FlatExpr::bvar(0));
    let e2 = writer.add_expr(FlatExpr::app(e0, e1));
    let e3 = writer.add_expr(FlatExpr::lam(0, e0, e2));
    let e4 = writer.add_expr(FlatExpr::pi(1, e0, e3));
    let e5 = writer.add_expr(FlatExpr::let_expr(e0, e1, e4));

    build_test_shard(&mut writer, e0, e5);
    let reader = round_trip(&writer);

    for (idx, expr) in reader.exprs.iter().enumerate() {
        for r in extract_expr_refs(expr) {
            assert!(
                (r as usize) < idx,
                "topo-sort violated: expr[{idx}] refs expr[{r}] but {r} >= {idx}"
            );
        }
    }
}

// ======================================================================
// Axiom profile propagation
// ======================================================================

#[test]
fn test_self_verify_axiom_profile_propagation() {
    use crate::trust::axiom_propagation::DependencyGraph;

    let mut graph = DependencyGraph::new(4);
    graph
        .set_initial_profile(0, AxiomProfile::CLASSICAL)
        .unwrap();
    graph.set_initial_profile(1, AxiomProfile::CHOICE).unwrap();
    graph
        .set_initial_profile(3, AxiomProfile::EXTENSIONALITY)
        .unwrap();
    graph.add_edge(2, 0).unwrap();
    graph.add_edge(2, 1).unwrap();
    graph.add_edge(3, 2).unwrap();
    graph.propagate().unwrap();

    assert_eq!(graph.profile(0), AxiomProfile::CLASSICAL);
    assert_eq!(graph.profile(1), AxiomProfile::CHOICE);
    assert_eq!(
        graph.profile(2),
        AxiomProfile::CLASSICAL | AxiomProfile::CHOICE
    );
    let expect_3 = AxiomProfile::EXTENSIONALITY | AxiomProfile::CLASSICAL | AxiomProfile::CHOICE;
    assert_eq!(graph.profile(3), expect_3);
    graph.verify_invariant().unwrap();
}

#[test]
fn test_self_verify_axiom_profile_completeness() {
    use crate::trust::axiom_propagation::DependencyGraph;

    let mut graph = DependencyGraph::new(4);
    graph
        .set_initial_profile(0, AxiomProfile::CLASSICAL)
        .unwrap();
    graph.set_initial_profile(1, AxiomProfile::CHOICE).unwrap();
    graph
        .set_initial_profile(3, AxiomProfile::EXTENSIONALITY)
        .unwrap();
    graph.add_edge(2, 0).unwrap();
    graph.add_edge(2, 1).unwrap();
    graph.add_edge(3, 2).unwrap();
    graph.propagate().unwrap();

    // For each node, every reachable dep's profile is a subset.
    for i in 0..4u32 {
        let node_profile = graph.profile(i);
        for dep in graph.reachable_from(i) {
            assert!(
                node_profile.is_superset_of(graph.profile(dep)),
                "node {} profile does not contain dep {} profile",
                i,
                dep
            );
        }
    }
}
