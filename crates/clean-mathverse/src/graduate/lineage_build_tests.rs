// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the corpus lineage builder ([`build_corpus_lineage`]).

use std::path::Path;

use clean_kernel::{BinderInfo, Declaration, Expr, Name};

use super::build_corpus_lineage;
use crate::export::kernel_export::KernelShardBuilder;

fn bd() -> BinderInfo {
    BinderInfo::Default
}

fn theorem(name: &str, type_: Expr, value: Expr) -> Declaration {
    Declaration::Theorem {
        name: Name::from_string(name),
        level_params: vec![],
        type_,
        value,
    }
}

/// `And a b` (the kernel does not type-check shard declarations, so raw consts are fine).
fn and(a: Expr, b: Expr) -> Expr {
    Expr::app(Expr::app(Expr::const_str("And"), a), b)
}

/// Write a shard with three statements: `And P Q`, its commutative reorder `And Q P`
/// (same Tier-1.5 form, distinct statement-hash), and an unrelated `And X Y`.
fn write_lineage_fixture(dir: &Path) {
    let p = || Expr::const_str("P");
    let q = || Expr::const_str("Q");
    let mut b = KernelShardBuilder::new();
    b.add_declaration(&theorem("L.pq", and(p(), q()), Expr::const_str("h")), &[])
        .expect("pq");
    b.add_declaration(&theorem("L.qp", and(q(), p()), Expr::const_str("h")), &[])
        .expect("qp");
    b.add_declaration(
        &theorem(
            "L.xy",
            and(Expr::const_str("X"), Expr::const_str("Y")),
            Expr::const_str("h"),
        ),
        &[],
    )
    .expect("xy");
    b.write_to_file(dir.join("lineage.mathverse"))
        .expect("write");
}

#[test]
fn test_corpus_lineage_collapses_commutative_class() {
    let tmp = tempfile::tempdir().expect("tempdir");
    write_lineage_fixture(tmp.path());
    let (mut graph, stats) = build_corpus_lineage(tmp.path()).expect("build lineage");

    assert_eq!(stats.shards, 1);
    assert_eq!(stats.constants, 3);
    // Three distinct statements (P∧Q, Q∧P, X∧Y) …
    assert_eq!(stats.distinct_statements, 3);
    // … but P∧Q and Q∧P fold to ONE form, so only two distinct Tier-1.5 forms.
    assert_eq!(stats.distinct_forms, 2);
    // Exactly one statement merged by commutativity beyond exact-hash dedup.
    assert_eq!(stats.collapsed_by_commutativity, 1);
    // One RewriteCanonical edge (P∧Q — Q∧P); one 2-member class; X∧Y stays isolated.
    assert_eq!(stats.rewrite_edges, 1);
    assert_eq!(stats.lineage_nodes, 2);
    assert_eq!(stats.lineage_classes, 1);

    // The two reorder statements are in the same class but NOT soundly-equivalent
    // (RewriteCanonical is deterministic evidence, never a proof).
    let pq = crate::graduate::record::expr_canonical_digest(&and(
        Expr::const_str("P"),
        Expr::const_str("Q"),
    ))
    .expect("hash pq");
    let qp = crate::graduate::record::expr_canonical_digest(&and(
        Expr::const_str("Q"),
        Expr::const_str("P"),
    ))
    .expect("hash qp");
    assert!(graph.same_class(&pq, &qp), "reorders cluster for search");
    assert!(
        !graph.soundly_equivalent(&pq, &qp),
        "a rewrite-canonical edge is evidence, not a sound proof of sameness"
    );
    // The edge log is the serializable audit trail.
    assert_eq!(graph.edges().len(), 1);
    assert!(graph.edges()[0].evidence.starts_with("blake3:"));
}

#[test]
fn test_corpus_lineage_empty_dir() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let dir = tmp.path().join("empty");
    std::fs::create_dir_all(&dir).expect("mkdir");
    let (graph, stats) = build_corpus_lineage(&dir).expect("build empty");
    assert_eq!(stats.constants, 0);
    assert_eq!(stats.distinct_statements, 0);
    assert!(graph.is_empty());
}
