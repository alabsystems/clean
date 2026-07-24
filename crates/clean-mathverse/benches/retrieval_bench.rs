// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Criterion retrieval benchmarks for the Mathverse Library search modes.
//!
//! Benchmarks the five search modes documented on the `MathverseSearch` trait:
//!   1. Name lookup (<100ns target) — bloom filter + sorted name index
//!   2. Type-directed search (<10us target) — discrimination tree
//!   3. Semantic search (<1ms target) — BM25 keyword index
//!   4. Dependency walk (<1us/hop target) — graph BFS traversal
//!   5. Cross-system equivalence (<100us target) — name-based matching

use std::hint::black_box;

use clean_kernel::flat::FlatExpr;
use clean_mathverse::cross_system_index::CrossSystemIndex;
use clean_mathverse::discrim::{fingerprint_for_search, DiscrimKey, DiscrimTree};
use clean_mathverse::embedding::{BM25Index, MathEmbedding};
use clean_mathverse::equivalence::EquivalenceDetector;
use clean_mathverse::graph_alpha::{ConceptEdge, ConceptGraph, ConceptNode};
use clean_mathverse::search::{DomainQuery, EdgeFilter, SearchConfig};
use clean_mathverse::shard::{ShardReader, ShardWriter};
use clean_mathverse::types::{
    AxiomProfile, ContentDomain, ImportConfidence, MathverseConstantHeader, SourceSystem, NO_VALUE,
};
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Synthetic math constant names mimicking real Lean 4 / Coq / Isabelle naming.
const MATH_NAMES: &[&str] = &[
    "Nat.add_comm",
    "Nat.add_assoc",
    "Nat.mul_comm",
    "Nat.mul_assoc",
    "Nat.zero_add",
    "Nat.succ_pred",
    "Nat.add_zero",
    "Nat.mul_one",
    "Int.add_comm",
    "Int.neg_neg",
    "Int.add_left_neg",
    "Int.mul_comm",
    "List.map_comp",
    "List.filter_map",
    "List.append_nil",
    "List.reverse_reverse",
    "Bool.not_not",
    "Bool.and_comm",
    "Bool.or_comm",
    "Bool.xor_assoc",
    "Group.mul_assoc",
    "Group.one_mul",
    "Group.mul_one",
    "Group.inv_mul",
    "Ring.add_comm",
    "Ring.mul_assoc",
    "Ring.left_distrib",
    "Ring.right_distrib",
    "Finset.card_union",
    "Finset.sum_add",
    "Finset.prod_mul",
    "Finset.mem_filter",
    "Real.add_comm",
    "Real.mul_comm",
    "Real.abs_nonneg",
    "Real.sqrt_sq",
    "Complex.norm_mul",
    "Complex.conj_conj",
    "Complex.add_comm",
    "Complex.mul_comm",
    "Topology.continuous_id",
    "Topology.compact_closed",
    "Metric.dist_comm",
    "Order.le_antisymm",
    "Order.le_trans",
    "Lattice.sup_comm",
    "Lattice.inf_comm",
    "Category.comp_id",
    "Category.id_comp",
    "Category.assoc",
    "Set.mem_union",
    "Set.mem_inter",
    "Set.subset_refl",
    "Set.empty_subset",
];

/// Source systems to cycle through for cross-system benchmarks.
const SOURCES: &[SourceSystem] = &[
    SourceSystem::Lean4,
    SourceSystem::Coq,
    SourceSystem::Isabelle,
    SourceSystem::HolLight,
    SourceSystem::Metamath,
];

fn make_header(name_idx: u32, type_idx: u32) -> MathverseConstantHeader {
    MathverseConstantHeader {
        name_idx,
        type_idx,
        value_idx: NO_VALUE,
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
    }
}

/// Build a shard with `n` constants whose types are simple Pi chains.
/// Returns the serialized bytes and the list of name strings used.
fn build_shard(n: usize) -> (Vec<u8>, Vec<String>) {
    let mut writer = ShardWriter::new();

    // Build a shared string table from MATH_NAMES, recycling names.
    let name_indices: Vec<u32> = (0..n)
        .map(|i| {
            let name = MATH_NAMES[i % MATH_NAMES.len()];
            writer.add_string(name)
        })
        .collect();

    // Base type consts: indices 0=Nat, 1=Bool.
    let type_name_nat = writer.add_string("Nat");
    let type_name_bool = writer.add_string("Bool");
    let e_nat = writer.add_expr(FlatExpr::const_ref(type_name_nat, u32::MAX));
    let e_bool = writer.add_expr(FlatExpr::const_ref(type_name_bool, u32::MAX));

    // Build a few type expressions.
    let e_nat2 = writer.add_expr(FlatExpr::const_ref(type_name_nat, u32::MAX));
    let pi_nat_nat = writer.add_expr(FlatExpr::pi(0, e_nat, e_nat2));
    let e_bool2 = writer.add_expr(FlatExpr::const_ref(type_name_bool, u32::MAX));
    let pi_nat_bool = writer.add_expr(FlatExpr::pi(0, e_nat, e_bool2));
    let e_bool3 = writer.add_expr(FlatExpr::const_ref(type_name_bool, u32::MAX));
    let pi_bool_bool = writer.add_expr(FlatExpr::pi(0, e_bool, e_bool3));

    let type_exprs = [pi_nat_nat, pi_nat_bool, pi_bool_bool];
    let names_out: Vec<String> = (0..n)
        .map(|i| MATH_NAMES[i % MATH_NAMES.len()].to_owned())
        .collect();

    for i in 0..n {
        let hdr = make_header(name_indices[i], type_exprs[i % type_exprs.len()]);
        writer.add_constant(hdr);
    }

    let mut buf = Vec::new();
    writer.write(&mut buf).expect("shard write");
    (buf, names_out)
}

/// Build a ConceptGraph with `n` nodes and a linear DependsOn chain.
fn build_dependency_graph(n: usize) -> (ConceptGraph, Vec<String>) {
    let mut graph = ConceptGraph::new();
    let mut strings = Vec::with_capacity(n);
    for i in 0..n {
        let name = format!("const_{i}");
        graph.add_named_node(
            &name,
            ConceptNode::Theorem {
                constant_idx: i as u32,
            },
        );
        strings.push(name);
    }
    // Linear chain: 0 -> 1 -> 2 -> ... -> n-1
    for i in 0..n.saturating_sub(1) {
        graph.add_edge(i as u32, (i + 1) as u32, ConceptEdge::DependsOn);
    }
    // Add some cross-links for realistic graph density.
    for i in (0..n).step_by(5) {
        let target = (i + 3) % n;
        graph.add_edge(i as u32, target as u32, ConceptEdge::DependsOn);
    }
    (graph, strings)
}

/// Build a BM25 index with `n` documents drawn from MATH_NAMES.
fn build_bm25_index(n: usize) -> BM25Index {
    let mut index = BM25Index::new();
    for i in 0..n {
        let name = MATH_NAMES[i % MATH_NAMES.len()];
        index.index_constant(i as u32, name, &[]);
    }
    index.rebuild_stats();
    index
}

/// Build a CrossSystemIndex with `n` entries spread across multiple systems.
fn build_cross_system_index(n: usize) -> CrossSystemIndex {
    let mut index = CrossSystemIndex::new();
    for i in 0..n {
        let name = MATH_NAMES[i % MATH_NAMES.len()];
        let source = SOURCES[i % SOURCES.len()];
        index.index_constant(name, source, (i / SOURCES.len()) as u32, i as u32);
    }
    index
}

/// Build a DiscrimTree from a shard's expression arena.
fn build_discrim_tree(shard_bytes: &[u8]) -> DiscrimTree {
    let reader = ShardReader::from_bytes(shard_bytes).expect("shard read");
    DiscrimTree::build_from_shard(&reader)
}

// ---------------------------------------------------------------------------
// Benchmark groups
// ---------------------------------------------------------------------------

/// Benchmark 1: Name lookup via sorted name index in shard.
///
/// Target: <100ns per lookup.
fn bench_name_lookup(c: &mut Criterion) {
    let mut group = c.benchmark_group("name_lookup");

    for &n in &[100, 500, 1000] {
        let (shard_bytes, names) = build_shard(n);
        let reader = ShardReader::from_bytes(&shard_bytes).expect("shard read");

        group.bench_with_input(BenchmarkId::new("shard_sorted_index", n), &n, |b, _| {
            let query = &names[n / 2];
            b.iter(|| {
                black_box(reader.lookup_name(query));
            });
        });
    }

    group.finish();
}

/// Benchmark 2: Type-directed search via discrimination tree.
///
/// Target: <10us per search.
fn bench_type_search(c: &mut Criterion) {
    let mut group = c.benchmark_group("type_search");

    for &n in &[100, 500, 1000] {
        let (shard_bytes, _names) = build_shard(n);
        let tree = build_discrim_tree(&shard_bytes);

        // Query: "? -> Nat" using fingerprint_for_search.
        let query_path = fingerprint_for_search("? -> Nat");

        group.bench_with_input(BenchmarkId::new("discrim_search", n), &n, |b, _| {
            b.iter(|| {
                black_box(tree.search_generalized(black_box(&query_path), 10));
            });
        });

        // Also bench exact search with FlatExpr query.
        let reader = ShardReader::from_bytes(&shard_bytes).expect("shard read");
        // Build a query arena for Pi(Nat, Star).
        let query_exprs = vec![
            FlatExpr::const_ref(0, u32::MAX), // 0: Nat (name_idx=0)
            FlatExpr::lit_nat(0),             // 1: Star (wildcard)
            FlatExpr::pi(0, 0, 1),            // 2: Pi(Nat, Star)
        ];

        group.bench_with_input(BenchmarkId::new("discrim_flat_search", n), &n, |b, _| {
            b.iter(|| {
                black_box(tree.search(black_box(&query_exprs), 2, 10));
            });
        });
    }

    group.finish();
}

/// Benchmark 3: Semantic search via BM25 keyword index.
///
/// Target: <1ms per search.
fn bench_semantic_search(c: &mut Criterion) {
    let mut group = c.benchmark_group("semantic_search");

    for &n in &[100, 500, 1000] {
        let index = build_bm25_index(n);

        group.bench_with_input(BenchmarkId::new("bm25_search", n), &n, |b, _| {
            b.iter(|| {
                black_box(index.search(black_box("commutative addition"), 10));
            });
        });

        group.bench_with_input(BenchmarkId::new("bm25_exact_name", n), &n, |b, _| {
            b.iter(|| {
                black_box(index.search(black_box("Nat.add_comm"), 10));
            });
        });
    }

    // BM25 index_constant throughput.
    group.bench_function("bm25_index_100", |b| {
        b.iter(|| {
            let mut idx = BM25Index::new();
            for i in 0..100 {
                let name = MATH_NAMES[i % MATH_NAMES.len()];
                idx.index_constant(i as u32, name, &[]);
            }
            idx.rebuild_stats();
            black_box(&idx);
        });
    });

    group.finish();
}

/// Benchmark 4: Dependency walk via ConceptGraph BFS.
///
/// Target: <1us per hop.
fn bench_dependency_walk(c: &mut Criterion) {
    let mut group = c.benchmark_group("dependency_walk");

    for &n in &[100, 500, 1000] {
        let (graph, _strings) = build_dependency_graph(n);

        // BFS from node 0 with depth limit.
        group.bench_with_input(BenchmarkId::new("bfs_depth_5", n), &n, |b, _| {
            let filter = EdgeFilter {
                allowed_edges: None,
                max_depth: Some(5),
            };
            b.iter(|| {
                black_box(graph.bfs(black_box(0), &filter));
            });
        });

        group.bench_with_input(BenchmarkId::new("bfs_depth_10", n), &n, |b, _| {
            let filter = EdgeFilter {
                allowed_edges: None,
                max_depth: Some(10),
            };
            b.iter(|| {
                black_box(graph.bfs(black_box(0), &filter));
            });
        });

        // Transitive deps from node 0.
        group.bench_with_input(BenchmarkId::new("transitive_deps", n), &n, |b, _| {
            b.iter(|| {
                black_box(graph.transitive_deps(black_box(0)));
            });
        });

        // Shortest path between distant nodes.
        let target = (n - 1) as u32;
        group.bench_with_input(BenchmarkId::new("find_path", n), &n, |b, _| {
            b.iter(|| {
                black_box(graph.find_path(black_box(0), black_box(target)));
            });
        });
    }

    group.finish();
}

/// Benchmark 5: Cross-system equivalence matching.
///
/// Target: <100us per find_matches call.
fn bench_cross_system(c: &mut Criterion) {
    let mut group = c.benchmark_group("cross_system");

    for &n in &[50, 200, 500] {
        let index = build_cross_system_index(n);

        group.bench_with_input(BenchmarkId::new("find_matches_2sys", n), &n, |b, _| {
            b.iter(|| {
                black_box(index.find_matches(black_box(2)));
            });
        });

        group.bench_with_input(BenchmarkId::new("find_matches_3sys", n), &n, |b, _| {
            b.iter(|| {
                black_box(index.find_matches(black_box(3)));
            });
        });
    }

    // EquivalenceDetector batch detection.
    for &n in &[50, 200] {
        let mut detector = EquivalenceDetector::new();
        // Build a FlatExpr arena with simple types.
        let exprs = vec![
            FlatExpr::const_ref(0, u32::MAX),
            FlatExpr::const_ref(1, u32::MAX),
            FlatExpr::pi(0, 0, 1),
        ];
        for i in 0..n {
            let name = MATH_NAMES[i % MATH_NAMES.len()];
            let source = SOURCES[i % SOURCES.len()];
            detector.index_constant(i as u32, name, source, &exprs, 2);
        }

        group.bench_with_input(BenchmarkId::new("detect_all", n), &n, |b, _| {
            b.iter(|| {
                black_box(detector.detect_all(black_box(0.7)));
            });
        });
    }

    group.finish();
}

/// Benchmark: DiscrimTree construction from shard data.
fn bench_discrim_build(c: &mut Criterion) {
    let mut group = c.benchmark_group("discrim_build");

    for &n in &[100, 500, 1000] {
        let (shard_bytes, _) = build_shard(n);
        let reader = ShardReader::from_bytes(&shard_bytes).expect("shard read");

        group.bench_with_input(BenchmarkId::new("build_from_shard", n), &n, |b, _| {
            b.iter(|| {
                black_box(DiscrimTree::build_from_shard(&reader));
            });
        });
    }

    group.finish();
}

/// Benchmark: MathEmbedding vector computation.
fn bench_embedding(c: &mut Criterion) {
    let mut group = c.benchmark_group("embedding");
    let emb = MathEmbedding::new();

    group.bench_function("embed_constant", |b| {
        b.iter(|| {
            black_box(emb.embed_constant(
                black_box("Nat.add_comm"),
                black_box(&["arrow".into(), "nat".into(), "nat".into()]),
            ));
        });
    });

    group.bench_function("fingerprint_for_search", |b| {
        b.iter(|| {
            black_box(fingerprint_for_search(black_box("? -> ? -> Nat")));
        });
    });

    group.finish();
}

/// Benchmark: DomainSearchEngine over a small graph.
fn bench_domain_search(c: &mut Criterion) {
    use clean_mathverse::graph_alpha::{build_domain_index, DomainIndex};
    use clean_mathverse::search::{search_domain_query, DomainSearchEngine};

    let mut group = c.benchmark_group("domain_search");

    for &n in &[50, 200, 500] {
        let (graph, strings) = build_dependency_graph(n);
        let domain_idx = build_domain_index(&graph, &strings);
        let config = SearchConfig::default();

        group.bench_with_input(BenchmarkId::new("free_text", n), &n, |b, _| {
            let query = DomainQuery::FreeText("const_42".to_owned());
            b.iter(|| {
                black_box(search_domain_query(
                    black_box(&query),
                    &graph,
                    &domain_idx,
                    &strings,
                    &config,
                ));
            });
        });
    }

    group.finish();
}

// ---------------------------------------------------------------------------
// Criterion entry
// ---------------------------------------------------------------------------

criterion_group!(
    benches,
    bench_name_lookup,
    bench_type_search,
    bench_semantic_search,
    bench_dependency_walk,
    bench_cross_system,
    bench_discrim_build,
    bench_embedding,
    bench_domain_search,
);
criterion_main!(benches);
