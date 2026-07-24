// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Build a Tier-2 lineage graph from a `.mathverse` corpus and report the
//! rewrite-canonical equivalence-class statistics ("same object, different form").
//!
//! Usage:
//!   mathverse_lineage <corpus-dir> [out-edges.json]
//!
//! Prints JSON stats. With `out-edges.json`, also persists the serializable edge log
//! (the audit trail of every RewriteCanonical identity hint). The edges are Tier-1.5
//! deterministic evidence, NOT proofs — `same_class` clusters them for search-space
//! collapse; confirming true sameness still needs `same_object` / a `proved-iff` cert.

use std::path::Path;
use std::time::Instant;

use clean_mathverse::graduate::build_corpus_lineage;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        eprintln!("Usage: mathverse_lineage <corpus-dir> [out-edges.json]");
        std::process::exit(1);
    }
    let corpus = Path::new(&args[1]);
    let out = args.get(2).map(Path::new);

    let started = Instant::now();
    let (graph, stats) = match build_corpus_lineage(corpus) {
        Ok(v) => v,
        Err(e) => {
            eprintln!("lineage build failed: {e}");
            std::process::exit(1);
        }
    };
    let build_seconds = started.elapsed().as_secs_f64();

    if let Some(out) = out {
        match serde_json::to_string(graph.edges()) {
            Ok(s) => {
                if let Err(e) = std::fs::write(out, s) {
                    eprintln!("write {} failed: {e}", out.display());
                    std::process::exit(1);
                }
            }
            Err(e) => {
                eprintln!("serialize edges failed: {e}");
                std::process::exit(1);
            }
        }
    }

    let payload = serde_json::json!({
        "schema": "mathverse-corpus-lineage-v1",
        "corpus": corpus.display().to_string(),
        "shards": stats.shards,
        "constants": stats.constants,
        "distinct_statements": stats.distinct_statements,
        "distinct_forms": stats.distinct_forms,
        "collapsed_by_commutativity": stats.collapsed_by_commutativity,
        "rewrite_edges": stats.rewrite_edges,
        "lineage_nodes": stats.lineage_nodes,
        "lineage_classes": stats.lineage_classes,
        "edges_out": out.map(|p| p.display().to_string()),
        "build_seconds": build_seconds,
    });
    println!(
        "{}",
        serde_json::to_string_pretty(&payload).unwrap_or_else(|_| "{}".to_string())
    );
}
