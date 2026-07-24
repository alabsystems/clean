// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the retrieval sub-modules: name_index, type_index, dependency_graph, MathverseSearch.

use super::*;
use crate::retrieval::dependency_graph::DependencyGraph;
use crate::retrieval::name_index::{NameEntry, NameIndex};
use crate::retrieval::type_index::{HeadSymbol, TypeIndex, TypeIndexEntry};
use crate::trust::trust_enforcement::TrustPolicy;
use crate::types::{AxiomProfile, SourceSystem, TrustLevel};

// ---------------------------------------------------------------------------
// Existing BloomFilter / DiscTree / RetrievalIndex tests (migrated from inline)
// ---------------------------------------------------------------------------

#[test]
fn test_bloom_filter_basic() {
    let mut bf = BloomFilter::new(100, 0.01);
    bf.insert(b"hello");
    assert!(bf.might_contain(b"hello"));
    assert!(!bf.might_contain(b"definitely_not_there_xyzzy_12345"));
}

#[test]
fn test_disc_tree_insert_lookup() {
    let mut tree = DiscTreeNode::new();
    tree.insert(&[DiscTreeKey::Const(0), DiscTreeKey::App], 42);
    tree.insert(&[DiscTreeKey::Const(0), DiscTreeKey::App], 43);
    tree.insert(&[DiscTreeKey::Const(1), DiscTreeKey::App], 99);

    let results = tree.lookup(&[DiscTreeKey::Const(0), DiscTreeKey::App]);
    assert_eq!(results.len(), 2);
    assert!(results.contains(&42));
    assert!(results.contains(&43));
}

#[test]
fn test_disc_tree_wildcard() {
    let mut tree = DiscTreeNode::new();
    tree.insert(&[DiscTreeKey::Const(0)], 1);
    tree.insert(&[DiscTreeKey::Const(1)], 2);

    let results = tree.lookup(&[DiscTreeKey::Star]);
    assert_eq!(results.len(), 2);
}

#[test]
fn test_retrieval_index_name_lookup() {
    let mut index = RetrievalIndex::new(10);
    index.add(IndexEntry {
        constant_idx: 0,
        name: "Nat.add_comm".to_owned(),
        source: SourceSystem::Lean4,
        trust_level: TrustLevel::KernelVerified,
        axiom_profile: AxiomProfile::NONE,
        fingerprint: Vec::new(),
    });

    let results = index.lookup_by_name("Nat.add_comm");
    assert_eq!(results.len(), 1);
    assert_eq!(results[0].name, "Nat.add_comm");

    let empty = index.lookup_by_name("nonexistent");
    assert!(empty.is_empty());
}

#[test]
fn test_retrieval_index_prefix_search() {
    let mut index = RetrievalIndex::new(10);
    index.add(IndexEntry {
        constant_idx: 0,
        name: "Nat.add_comm".to_owned(),
        source: SourceSystem::Lean4,
        trust_level: TrustLevel::KernelVerified,
        axiom_profile: AxiomProfile::NONE,
        fingerprint: Vec::new(),
    });
    index.add(IndexEntry {
        constant_idx: 1,
        name: "Nat.mul_comm".to_owned(),
        source: SourceSystem::Lean4,
        trust_level: TrustLevel::KernelVerified,
        axiom_profile: AxiomProfile::NONE,
        fingerprint: Vec::new(),
    });
    index.add(IndexEntry {
        constant_idx: 2,
        name: "Int.add_comm".to_owned(),
        source: SourceSystem::Coq,
        trust_level: TrustLevel::PartiallyAxiomatized,
        axiom_profile: AxiomProfile::NONE,
        fingerprint: Vec::new(),
    });

    let nat_results = index.search_by_prefix("Nat.");
    assert_eq!(nat_results.len(), 2);
}

fn trust_entry(
    constant_idx: u32,
    name: &str,
    trust_level: TrustLevel,
    axiom_profile: AxiomProfile,
) -> IndexEntry {
    IndexEntry {
        constant_idx,
        name: name.to_owned(),
        source: SourceSystem::Lean4,
        trust_level,
        axiom_profile,
        fingerprint: Vec::new(),
    }
}

fn trust_policy_fixture() -> RetrievalIndex {
    let mut index = RetrievalIndex::new(10);
    let name = "Nat.trust_candidate";

    index.add(trust_entry(
        0,
        name,
        TrustLevel::KernelVerified,
        AxiomProfile::NONE,
    ));
    index.add(trust_entry(
        1,
        name,
        TrustLevel::CertificateReplayed,
        AxiomProfile::SAT_CERT,
    ));
    index.add(trust_entry(
        2,
        name,
        TrustLevel::AxiomDependent,
        AxiomProfile::CHOICE,
    ));
    index.add(trust_entry(
        3,
        name,
        TrustLevel::KernelVerified,
        AxiomProfile::AXIOMATIZED,
    ));
    index.add(trust_entry(
        4,
        name,
        TrustLevel::TrustedOracle,
        AxiomProfile::SMT_ORACLE,
    ));
    index.add(trust_entry(
        5,
        name,
        TrustLevel::PartiallyAxiomatized,
        AxiomProfile::NONE,
    ));
    index.add(trust_entry(
        6,
        name,
        TrustLevel::AxiomDependent,
        AxiomProfile::UNIVERSE_INCON,
    ));
    index.add(trust_entry(
        7,
        name,
        TrustLevel::CertificateReplayed,
        AxiomProfile::FLOAT_APPROX,
    ));
    index.add(trust_entry(
        8,
        name,
        TrustLevel::AxiomDependent,
        AxiomProfile::NN_ABSTRACTION,
    ));

    index
}

fn sorted_constant_indices(entries: Vec<&IndexEntry>) -> Vec<u32> {
    let mut indices: Vec<u32> = entries.iter().map(|entry| entry.constant_idx).collect();
    indices.sort_unstable();
    indices
}

#[test]
fn test_retrieval_index_strict_policy_filters_trust_gated_entries() {
    let index = trust_policy_fixture();
    let strict = TrustPolicy::strict();

    let strict_results = index.lookup_by_name_with_policy("Nat.trust_candidate", &strict);

    assert_eq!(sorted_constant_indices(strict_results), vec![0, 1, 2]);
}

#[test]
fn test_retrieval_index_permissive_policy_returns_trust_gated_entries() {
    let index = trust_policy_fixture();
    let permissive = TrustPolicy::permissive();

    let permissive_results = index.lookup_by_name_with_policy("Nat.trust_candidate", &permissive);

    assert_eq!(
        sorted_constant_indices(permissive_results),
        vec![0, 1, 2, 3, 4, 5, 6, 7, 8]
    );
}

#[test]
fn test_retrieval_index_policy_applies_to_prefix_and_full_scan() {
    let mut index = trust_policy_fixture();
    index.add(trust_entry(
        9,
        "Nat.other",
        TrustLevel::TrustedOracle,
        AxiomProfile::NONE,
    ));
    index.add(trust_entry(
        10,
        "Int.visible",
        TrustLevel::KernelVerified,
        AxiomProfile::NONE,
    ));

    let strict = TrustPolicy::strict();

    assert_eq!(
        sorted_constant_indices(index.search_by_prefix_with_policy("Nat.", &strict)),
        vec![0, 1, 2]
    );
    assert_eq!(
        sorted_constant_indices(index.trusted_entries(&strict)),
        vec![0, 1, 2, 10]
    );
}

#[test]
fn test_retrieval_index_source_filter() {
    let mut index = RetrievalIndex::new(10);
    index.add(IndexEntry {
        constant_idx: 0,
        name: "a".to_owned(),
        source: SourceSystem::Lean4,
        trust_level: TrustLevel::KernelVerified,
        axiom_profile: AxiomProfile::NONE,
        fingerprint: Vec::new(),
    });
    index.add(IndexEntry {
        constant_idx: 1,
        name: "b".to_owned(),
        source: SourceSystem::Coq,
        trust_level: TrustLevel::PartiallyAxiomatized,
        axiom_profile: AxiomProfile::NONE,
        fingerprint: Vec::new(),
    });

    let lean4 = index.filter_by_source(&SourceSystem::Lean4);
    assert_eq!(lean4.len(), 1);
    assert_eq!(lean4[0].name, "a");
}

// ---------------------------------------------------------------------------
// NameIndex tests
// ---------------------------------------------------------------------------

#[test]
fn test_name_index_exact_lookup_found() {
    let entries = vec![
        NameEntry {
            name: "Nat.add".to_owned(),
            constant_idx: 0,
        },
        NameEntry {
            name: "Nat.mul".to_owned(),
            constant_idx: 1,
        },
        NameEntry {
            name: "Bool.true".to_owned(),
            constant_idx: 2,
        },
    ];
    let index = NameIndex::build(entries);
    let result = index.search_exact("Nat.mul");
    assert_eq!(result, vec![1]);
}

#[test]
fn test_name_index_exact_lookup_not_found() {
    let entries = vec![NameEntry {
        name: "Nat.add".to_owned(),
        constant_idx: 0,
    }];
    let index = NameIndex::build(entries);
    let result = index.search_exact("List.nil");
    assert!(result.is_empty());
}

#[test]
fn test_name_index_exact_lookup_duplicates() {
    let entries = vec![
        NameEntry {
            name: "Nat.add".to_owned(),
            constant_idx: 0,
        },
        NameEntry {
            name: "Nat.add".to_owned(),
            constant_idx: 5,
        },
        NameEntry {
            name: "Nat.mul".to_owned(),
            constant_idx: 1,
        },
    ];
    let index = NameIndex::build(entries);
    let result = index.search_exact("Nat.add");
    assert_eq!(result.len(), 2);
    assert!(result.contains(&0));
    assert!(result.contains(&5));
}

#[test]
fn test_name_index_prefix_search() {
    let entries = vec![
        NameEntry {
            name: "Nat.add".to_owned(),
            constant_idx: 0,
        },
        NameEntry {
            name: "Nat.add_comm".to_owned(),
            constant_idx: 1,
        },
        NameEntry {
            name: "Nat.mul".to_owned(),
            constant_idx: 2,
        },
        NameEntry {
            name: "Int.add".to_owned(),
            constant_idx: 3,
        },
    ];
    let index = NameIndex::build(entries);
    let result = index.search_prefix("Nat.add");
    assert_eq!(result.len(), 2);
    let names: Vec<&str> = result.iter().map(|e| e.name.as_str()).collect();
    assert!(names.contains(&"Nat.add"));
    assert!(names.contains(&"Nat.add_comm"));
}

#[test]
fn test_name_index_prefix_search_no_match() {
    let entries = vec![NameEntry {
        name: "Nat.add".to_owned(),
        constant_idx: 0,
    }];
    let index = NameIndex::build(entries);
    let result = index.search_prefix("List.");
    assert!(result.is_empty());
}

#[test]
fn test_name_index_empty() {
    let index = NameIndex::build(Vec::new());
    assert!(index.is_empty());
    assert_eq!(index.len(), 0);
    assert!(index.search_exact("anything").is_empty());
    assert!(index.search_prefix("any").is_empty());
}

// ---------------------------------------------------------------------------
// TypeIndex tests
// ---------------------------------------------------------------------------

#[test]
fn test_type_index_search_by_head() {
    let entries = vec![
        TypeIndexEntry {
            constant_idx: 0,
            head: HeadSymbol::Const("Nat".to_owned()),
        },
        TypeIndexEntry {
            constant_idx: 1,
            head: HeadSymbol::Const("Nat".to_owned()),
        },
        TypeIndexEntry {
            constant_idx: 2,
            head: HeadSymbol::Const("Bool".to_owned()),
        },
        TypeIndexEntry {
            constant_idx: 3,
            head: HeadSymbol::Sort,
        },
    ];
    let index = TypeIndex::build(entries);

    let nat_results = index.search_by_head(&HeadSymbol::Const("Nat".to_owned()));
    assert_eq!(nat_results.len(), 2);
    assert!(nat_results.contains(&0));
    assert!(nat_results.contains(&1));

    let sort_results = index.search_by_head(&HeadSymbol::Sort);
    assert_eq!(sort_results, vec![3]);
}

#[test]
fn test_type_index_search_no_match() {
    let entries = vec![TypeIndexEntry {
        constant_idx: 0,
        head: HeadSymbol::Const("Nat".to_owned()),
    }];
    let index = TypeIndex::build(entries);
    let result = index.search_by_head(&HeadSymbol::Const("List".to_owned()));
    assert!(result.is_empty());
}

#[test]
fn test_type_index_head_symbols() {
    let entries = vec![
        TypeIndexEntry {
            constant_idx: 0,
            head: HeadSymbol::Const("Nat".to_owned()),
        },
        TypeIndexEntry {
            constant_idx: 1,
            head: HeadSymbol::Sort,
        },
        TypeIndexEntry {
            constant_idx: 2,
            head: HeadSymbol::Pi,
        },
    ];
    let index = TypeIndex::build(entries);
    let heads = index.head_symbols();
    assert_eq!(heads.len(), 3);
}

#[test]
fn test_type_index_empty() {
    let index = TypeIndex::build(Vec::new());
    assert!(index.is_empty());
    assert_eq!(index.len(), 0);
}

// ---------------------------------------------------------------------------
// DependencyGraph tests
// ---------------------------------------------------------------------------

#[test]
fn test_dep_graph_direct_deps() {
    let mut g = DependencyGraph::new(5);
    g.add_dependency(0, 1);
    g.add_dependency(0, 2);
    g.add_dependency(1, 3);

    assert_eq!(g.direct_deps(0), &[1, 2]);
    assert_eq!(g.direct_deps(1), &[3]);
    assert!(g.direct_deps(2).is_empty());
}

#[test]
fn test_dep_graph_reverse_deps() {
    let mut g = DependencyGraph::new(5);
    g.add_dependency(0, 1);
    g.add_dependency(2, 1);

    assert_eq!(g.direct_rdeps(1), &[0, 2]);
    assert!(g.direct_rdeps(0).is_empty());
}

#[test]
fn test_dep_graph_transitive_deps() {
    // 0 -> 1 -> 2 -> 3
    let mut g = DependencyGraph::new(4);
    g.add_dependency(0, 1);
    g.add_dependency(1, 2);
    g.add_dependency(2, 3);

    let deps = g.transitive_deps(0);
    assert_eq!(deps.len(), 3);
    assert!(deps.contains(&1));
    assert!(deps.contains(&2));
    assert!(deps.contains(&3));
}

#[test]
fn test_dep_graph_transitive_deps_diamond() {
    //   0
    //  / \
    // 1   2
    //  \ /
    //   3
    let mut g = DependencyGraph::new(4);
    g.add_dependency(0, 1);
    g.add_dependency(0, 2);
    g.add_dependency(1, 3);
    g.add_dependency(2, 3);

    let deps = g.transitive_deps(0);
    assert_eq!(deps.len(), 3);
    assert!(deps.contains(&1));
    assert!(deps.contains(&2));
    assert!(deps.contains(&3));
}

#[test]
fn test_dep_graph_transitive_rdeps() {
    // 0 -> 2, 1 -> 2, 2 -> 3
    let mut g = DependencyGraph::new(4);
    g.add_dependency(0, 2);
    g.add_dependency(1, 2);
    g.add_dependency(2, 3);

    let rdeps = g.transitive_rdeps(3);
    assert_eq!(rdeps.len(), 3);
    assert!(rdeps.contains(&2));
    assert!(rdeps.contains(&0));
    assert!(rdeps.contains(&1));
}

#[test]
fn test_dep_graph_cycle_handling() {
    // 0 -> 1 -> 2 -> 0 (cycle)
    let mut g = DependencyGraph::new(3);
    g.add_dependency(0, 1);
    g.add_dependency(1, 2);
    g.add_dependency(2, 0);

    // Should terminate without infinite loop.
    let deps = g.transitive_deps(0);
    assert_eq!(deps.len(), 2);
    assert!(deps.contains(&1));
    assert!(deps.contains(&2));
}

#[test]
fn test_dep_graph_empty() {
    let g = DependencyGraph::new(0);
    assert_eq!(g.node_count(), 0);
    assert_eq!(g.edge_count(), 0);
}

#[test]
fn test_dep_graph_out_of_bounds_ignored() {
    let mut g = DependencyGraph::new(2);
    // Adding edge with out-of-bounds index should be silently ignored.
    g.add_dependency(0, 5);
    assert!(g.direct_deps(0).is_empty());
}

// ---------------------------------------------------------------------------
// MathverseSearch trait tests (via CompositeSearch)
// ---------------------------------------------------------------------------

#[test]
fn test_composite_search_by_name() {
    let mut builder = CompositeSearch::builder();
    builder.add_constant(0, "Nat.add", HeadSymbol::Const("Nat".to_owned()));
    builder.add_constant(1, "Nat.mul", HeadSymbol::Const("Nat".to_owned()));
    builder.add_constant(2, "Bool.and", HeadSymbol::Const("Bool".to_owned()));
    let search = builder.build();

    let results = search.search_by_name("Nat.add");
    assert_eq!(results, vec![0]);

    let prefix = search.search_by_name_prefix("Nat.");
    assert_eq!(prefix.len(), 2);
}

#[test]
fn test_composite_search_by_type() {
    let mut builder = CompositeSearch::builder();
    builder.add_constant(0, "Nat.add", HeadSymbol::Const("Nat".to_owned()));
    builder.add_constant(1, "Nat.succ", HeadSymbol::Const("Nat".to_owned()));
    builder.add_constant(2, "Bool.true", HeadSymbol::Const("Bool".to_owned()));
    let search = builder.build();

    let results = search.search_by_type(&HeadSymbol::Const("Nat".to_owned()));
    assert_eq!(results.len(), 2);
    assert!(results.contains(&0));
    assert!(results.contains(&1));
}

#[test]
fn test_composite_search_dependencies() {
    let mut builder = CompositeSearch::builder();
    builder.add_constant(0, "Nat.add_comm", HeadSymbol::Const("Eq".to_owned()));
    builder.add_constant(1, "Nat.add", HeadSymbol::Const("Nat".to_owned()));
    builder.add_constant(2, "Nat", HeadSymbol::Sort);
    builder.add_dependency(0, 1);
    builder.add_dependency(1, 2);
    let search = builder.build();

    let direct = search.search_dependencies(0);
    assert_eq!(direct, vec![1]);

    let transitive = search.search_transitive_dependencies(0);
    assert_eq!(transitive.len(), 2);
    assert!(transitive.contains(&1));
    assert!(transitive.contains(&2));
}

#[test]
fn test_composite_search_reverse_deps() {
    let mut builder = CompositeSearch::builder();
    builder.add_constant(0, "A", HeadSymbol::Sort);
    builder.add_constant(1, "B", HeadSymbol::Sort);
    builder.add_constant(2, "C", HeadSymbol::Sort);
    builder.add_dependency(1, 0);
    builder.add_dependency(2, 0);
    let search = builder.build();

    let rdeps = search.search_reverse_dependencies(0);
    assert_eq!(rdeps.len(), 2);
    assert!(rdeps.contains(&1));
    assert!(rdeps.contains(&2));
}

// ---------------------------------------------------------------------------
// ShardNameIndex tests
// ---------------------------------------------------------------------------

use crate::retrieval::name_index::{ConstantRef, ShardNameEntry, ShardNameIndex};

#[test]
fn test_shard_name_index_lookup_found() {
    let entries = vec![
        ShardNameEntry {
            name: "Nat.add".to_owned(),
            constant_ref: ConstantRef {
                shard_idx: 0,
                constant_idx: 10,
            },
        },
        ShardNameEntry {
            name: "Nat.mul".to_owned(),
            constant_ref: ConstantRef {
                shard_idx: 0,
                constant_idx: 11,
            },
        },
    ];
    let index = ShardNameIndex::build(entries);
    let result = index.lookup("Nat.add");
    assert_eq!(
        result,
        Some(ConstantRef {
            shard_idx: 0,
            constant_idx: 10
        })
    );
}

#[test]
fn test_shard_name_index_lookup_not_found() {
    let entries = vec![ShardNameEntry {
        name: "Nat.add".to_owned(),
        constant_ref: ConstantRef {
            shard_idx: 0,
            constant_idx: 10,
        },
    }];
    let index = ShardNameIndex::build(entries);
    assert!(index.lookup("List.nil").is_none());
}

#[test]
fn test_shard_name_index_lookup_all_multi_shard() {
    let entries = vec![
        ShardNameEntry {
            name: "add_comm".to_owned(),
            constant_ref: ConstantRef {
                shard_idx: 0,
                constant_idx: 5,
            },
        },
        ShardNameEntry {
            name: "add_comm".to_owned(),
            constant_ref: ConstantRef {
                shard_idx: 1,
                constant_idx: 12,
            },
        },
    ];
    let index = ShardNameIndex::build(entries);
    let all = index.lookup_all("add_comm");
    assert_eq!(all.len(), 2);
    assert!(all.contains(&ConstantRef {
        shard_idx: 0,
        constant_idx: 5
    }));
    assert!(all.contains(&ConstantRef {
        shard_idx: 1,
        constant_idx: 12
    }));
}

#[test]
fn test_shard_name_index_prefix_search() {
    let entries = vec![
        ShardNameEntry {
            name: "Nat.add".to_owned(),
            constant_ref: ConstantRef {
                shard_idx: 0,
                constant_idx: 0,
            },
        },
        ShardNameEntry {
            name: "Nat.add_comm".to_owned(),
            constant_ref: ConstantRef {
                shard_idx: 0,
                constant_idx: 1,
            },
        },
        ShardNameEntry {
            name: "Nat.mul".to_owned(),
            constant_ref: ConstantRef {
                shard_idx: 0,
                constant_idx: 2,
            },
        },
        ShardNameEntry {
            name: "Int.add".to_owned(),
            constant_ref: ConstantRef {
                shard_idx: 1,
                constant_idx: 0,
            },
        },
    ];
    let index = ShardNameIndex::build(entries);
    let results = index.prefix_search("Nat.add");
    assert_eq!(results.len(), 2);
}

#[test]
fn test_shard_name_index_empty() {
    let index = ShardNameIndex::build(Vec::new());
    assert!(index.is_empty());
    assert_eq!(index.len(), 0);
    assert_eq!(index.name_count(), 0);
    assert!(index.lookup("anything").is_none());
    assert!(index.prefix_search("any").is_empty());
}

// ---------------------------------------------------------------------------
// TypeFingerprint tests
// ---------------------------------------------------------------------------

use crate::retrieval::type_index::{FingerprintTypeIndex, TypeFingerprint};

#[test]
fn test_type_fingerprint_identical_similarity() {
    let fp = TypeFingerprint::new(
        2,
        1,
        HeadSymbol::Const("Nat".to_owned()),
        vec!["Nat".to_owned(), "Bool".to_owned()],
    );
    let score = fp.similarity(&fp);
    assert!(
        (score - 1.0).abs() < f64::EPSILON,
        "identical fingerprints should have score 1.0, got {score}"
    );
}

#[test]
fn test_type_fingerprint_different_head_low_score() {
    let fp1 = TypeFingerprint::new(
        1,
        0,
        HeadSymbol::Const("Nat".to_owned()),
        vec!["Nat".to_owned()],
    );
    let fp2 = TypeFingerprint::new(
        1,
        0,
        HeadSymbol::Const("Bool".to_owned()),
        vec!["Bool".to_owned()],
    );
    let score = fp1.similarity(&fp2);
    assert!(
        score < 0.5,
        "different heads should have low score, got {score}"
    );
}

#[test]
fn test_type_fingerprint_same_head_partial_overlap() {
    let fp1 = TypeFingerprint::new(
        2,
        1,
        HeadSymbol::Const("Eq".to_owned()),
        vec!["Nat".to_owned(), "Bool".to_owned()],
    );
    let fp2 = TypeFingerprint::new(
        3,
        2,
        HeadSymbol::Const("Eq".to_owned()),
        vec!["Nat".to_owned(), "Int".to_owned()],
    );
    let score = fp1.similarity(&fp2);
    assert!(
        score > 0.5,
        "same head with partial overlap should have moderate score, got {score}"
    );
    assert!(
        score < 1.0,
        "different details should not give perfect score, got {score}"
    );
}

#[test]
fn test_type_fingerprint_dedup_base_types() {
    let fp = TypeFingerprint::new(
        0,
        0,
        HeadSymbol::Sort,
        vec!["Nat".to_owned(), "Nat".to_owned(), "Bool".to_owned()],
    );
    assert_eq!(fp.base_types.len(), 2);
    assert_eq!(fp.base_types, vec!["Bool", "Nat"]); // sorted and deduped
}

// ---------------------------------------------------------------------------
// FingerprintTypeIndex tests
// ---------------------------------------------------------------------------

#[test]
fn test_fingerprint_type_index_insert_and_search() {
    let mut index = FingerprintTypeIndex::new();
    index.insert(
        "Nat.add",
        0,
        TypeFingerprint::new(
            2,
            0,
            HeadSymbol::Const("Nat".to_owned()),
            vec!["Nat".to_owned()],
        ),
    );
    index.insert(
        "Nat.mul",
        1,
        TypeFingerprint::new(
            2,
            0,
            HeadSymbol::Const("Nat".to_owned()),
            vec!["Nat".to_owned()],
        ),
    );
    index.insert(
        "Bool.and",
        2,
        TypeFingerprint::new(
            2,
            0,
            HeadSymbol::Const("Bool".to_owned()),
            vec!["Bool".to_owned()],
        ),
    );

    let query = TypeFingerprint::new(
        2,
        0,
        HeadSymbol::Const("Nat".to_owned()),
        vec!["Nat".to_owned()],
    );
    let results = index.search_by_type(&query, 0.5);
    assert_eq!(results.len(), 2);
    // Both Nat.add and Nat.mul should match with high relevance.
    assert!(results.iter().any(|(idx, _)| *idx == 0));
    assert!(results.iter().any(|(idx, _)| *idx == 1));
    // Scores should be 1.0 (identical fingerprints).
    for (_, score) in &results {
        assert!((*score - 1.0).abs() < f64::EPSILON);
    }
}

#[test]
fn test_fingerprint_type_index_min_relevance_filter() {
    let mut index = FingerprintTypeIndex::new();
    index.insert(
        "Nat.add",
        0,
        TypeFingerprint::new(
            2,
            0,
            HeadSymbol::Const("Nat".to_owned()),
            vec!["Nat".to_owned()],
        ),
    );
    index.insert(
        "weird",
        1,
        TypeFingerprint::new(
            10,
            5,
            HeadSymbol::Const("Nat".to_owned()),
            vec!["Complex".to_owned()],
        ),
    );

    let query = TypeFingerprint::new(
        2,
        0,
        HeadSymbol::Const("Nat".to_owned()),
        vec!["Nat".to_owned()],
    );

    // With high min_relevance, only exact match should survive.
    let results = index.search_by_type(&query, 0.9);
    assert_eq!(results.len(), 1);
    assert_eq!(results[0].0, 0);
}

#[test]
fn test_fingerprint_type_index_empty() {
    let index = FingerprintTypeIndex::new();
    assert!(index.is_empty());
    assert_eq!(index.len(), 0);
    let query = TypeFingerprint::new(0, 0, HeadSymbol::Sort, vec![]);
    assert!(index.search_by_type(&query, 0.0).is_empty());
}

#[test]
fn test_fingerprint_type_index_sorted_by_relevance() {
    let mut index = FingerprintTypeIndex::new();
    // Exact match.
    index.insert(
        "exact",
        0,
        TypeFingerprint::new(
            2,
            1,
            HeadSymbol::Const("Eq".to_owned()),
            vec!["Nat".to_owned()],
        ),
    );
    // Partial match (different arrow depth and base types).
    index.insert(
        "partial",
        1,
        TypeFingerprint::new(
            5,
            3,
            HeadSymbol::Const("Eq".to_owned()),
            vec!["Int".to_owned()],
        ),
    );

    let query = TypeFingerprint::new(
        2,
        1,
        HeadSymbol::Const("Eq".to_owned()),
        vec!["Nat".to_owned()],
    );
    let results = index.search_by_type(&query, 0.0);
    assert!(results.len() >= 2);
    // First result should have higher score.
    assert!(results[0].1 >= results[1].1);
}
