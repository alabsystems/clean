// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `mathverse graph` — cross-system knowledge graph commands.
//!
//! Subcommands:
//!   mathverse graph search <name>     Search for a theorem name across all systems
//!   mathverse graph overlap            Show the overlap matrix between systems
//!   mathverse graph stats              Show knowledge graph statistics

use crate::cross_system_index::{CrossSystemIndex, CrossSystemReport, EquivalenceMatch};
use crate::equiv_graph::{build_equiv_graph, find_equivalents_in_graph};
use crate::library::MathverseLibrary;
use crate::types::SourceSystem;

use crate::mathverse_bin_cmds::fmt::{emit_delimited_row, source_system_display, OutputFormat};
use crate::mathverse_bin_cmds::load_library;

use super::graph_delimited::{print_search_delimited, print_stats_delimited};
use super::parse_format_arg;

pub fn cmd_graph(args: &[String]) {
    if args.is_empty() {
        print_graph_usage();
        std::process::exit(1);
    }

    match args[0].as_str() {
        "search" => cmd_graph_search(&args[1..]),
        "overlap" => cmd_graph_overlap(&args[1..]),
        "stats" => cmd_graph_stats(&args[1..]),
        "help" | "--help" | "-h" => print_graph_usage(),
        other => {
            eprintln!("Unknown graph subcommand: {other}");
            print_graph_usage();
            std::process::exit(1);
        }
    }
}

fn print_graph_usage() {
    eprintln!("Usage: mathverse graph <subcommand> [options]");
    eprintln!();
    eprintln!("Subcommands:");
    eprintln!("  search <name>    Search for a theorem name across all systems");
    eprintln!("  overlap          Show the overlap matrix between systems");
    eprintln!("  stats            Show knowledge graph statistics");
    eprintln!();
    eprintln!("Search options:");
    eprintln!("  --limit <N>      Max results (default: 20)");
    eprintln!("  --format <fmt>   Output format: table (default), json");
    eprintln!();
    eprintln!("Overlap/stats options:");
    eprintln!("  --format <fmt>   Output format: table (default), json");
    eprintln!("  --min <N>        Minimum shared names to show (default: 1)");
}

// ---------------------------------------------------------------------------
// Build the cross-system index from a loaded library
// ---------------------------------------------------------------------------

fn build_index(lib: &MathverseLibrary) -> CrossSystemIndex {
    let mut index = CrossSystemIndex::new();
    let count = lib.constant_count();

    for idx in 0..count as u32 {
        let name = match lib.get_name(idx) {
            Some(n) => n,
            None => continue,
        };
        let header = match lib.get_constant(idx) {
            Some(h) => h,
            None => continue,
        };
        let source = match SourceSystem::try_from(header.source_system) {
            Ok(s) => s,
            Err(_) => continue,
        };
        index.index_constant(name, source, 0, idx);
    }
    index
}

// ---------------------------------------------------------------------------
// graph search
// ---------------------------------------------------------------------------

fn cmd_graph_search(args: &[String]) {
    if args.is_empty() {
        eprintln!("Usage: mathverse graph search <name> [--limit N] [--format table|json]");
        std::process::exit(1);
    }

    let query = &args[0];
    let limit = parse_limit(&args[1..], 20);
    let format = parse_format_arg(&args[1..]);

    let lib = load_library();
    let index = build_index(&lib);
    let all_matches = index.find_matches(2);

    // Filter by query substring (case-insensitive).
    let query_lower = query.to_lowercase();
    let filtered: Vec<_> = all_matches
        .iter()
        .filter(|m| m.canonical_name.to_lowercase().contains(&query_lower))
        .take(limit)
        .collect();

    // Build knowledge graph and find direct equivalents.
    let (graph, _) = build_equiv_graph(&all_matches);
    let equivalents = find_equivalents_in_graph(&graph, query);

    match format {
        OutputFormat::Table => print_search_table(query, &filtered, &equivalents),
        OutputFormat::Json => print_search_json(query, &filtered, &equivalents),
        fmt @ (OutputFormat::Csv | OutputFormat::Tsv) => {
            print_search_delimited(&filtered, &equivalents, fmt)
        }
    }
}

fn print_search_table(
    query: &str,
    filtered: &[&EquivalenceMatch],
    equivalents: &[(String, SourceSystem)],
) {
    if filtered.is_empty() && equivalents.is_empty() {
        println!("No cross-system matches found for '{query}'.");
        return;
    }

    if !equivalents.is_empty() {
        println!("Equivalents of '{query}':");
        println!("{:<50} {:<15}", "NAME", "SYSTEM");
        println!("{}", "-".repeat(65));
        for (name, source) in equivalents {
            println!(
                "{:<50} {:<15}",
                truncate_name(name, 50),
                source_system_display(*source as u8),
            );
        }
        println!();
    }

    if !filtered.is_empty() {
        println!("Cross-system matches containing '{query}' (canonical names):");
        println!(
            "{:<40} {:<10} {:<10} CONFIDENCE",
            "CANONICAL NAME", "SYSTEMS", "REFS"
        );
        println!("{}", "-".repeat(75));
        for m in filtered {
            println!(
                "{:<40} {:<10} {:<10} {:.2}",
                truncate_name(&m.canonical_name, 40),
                m.system_count,
                m.refs.len(),
                m.confidence,
            );
        }
        println!("\n{} match(es)", filtered.len());
    }
}

fn print_search_json(
    query: &str,
    filtered: &[&EquivalenceMatch],
    equivalents: &[(String, SourceSystem)],
) {
    let equiv_arr: Vec<serde_json::Value> = equivalents
        .iter()
        .map(|(name, source)| {
            serde_json::json!({
                "name": name,
                "system": source_system_display(*source as u8),
            })
        })
        .collect();

    let matches_arr: Vec<serde_json::Value> = filtered
        .iter()
        .map(|m| {
            let refs: Vec<serde_json::Value> = m
                .refs
                .iter()
                .map(|r| {
                    serde_json::json!({
                        "original_name": r.original_name,
                        "system": source_system_display(r.source as u8),
                        "constant_id": r.constant_id,
                    })
                })
                .collect();
            serde_json::json!({
                "canonical_name": m.canonical_name,
                "system_count": m.system_count,
                "confidence": m.confidence,
                "refs": refs,
            })
        })
        .collect();

    let obj = serde_json::json!({
        "query": query,
        "equivalents": equiv_arr,
        "matches": matches_arr,
    });
    println!(
        "{}",
        serde_json::to_string_pretty(&obj).expect("invariant: json serialization")
    );
}

// ---------------------------------------------------------------------------
// graph overlap
// ---------------------------------------------------------------------------

fn cmd_graph_overlap(args: &[String]) {
    let format = parse_format_arg(args);
    let min_shared = parse_min(args, 1);

    let lib = load_library();
    let index = build_index(&lib);
    let overlaps = index.overlap_matrix();

    let filtered: Vec<_> = overlaps
        .iter()
        .filter(|o| o.shared_names >= min_shared)
        .collect();

    match format {
        OutputFormat::Table => {
            if filtered.is_empty() {
                println!("No system pairs share names (min_shared={min_shared}).");
                return;
            }
            println!("{:<20} {:<20} {:<10}", "SYSTEM A", "SYSTEM B", "SHARED");
            println!("{}", "-".repeat(50));
            for o in &filtered {
                println!(
                    "{:<20} {:<20} {:<10}",
                    source_system_display(o.system_a as u8),
                    source_system_display(o.system_b as u8),
                    o.shared_names,
                );
            }
            println!(
                "\n{} pair(s) with >= {min_shared} shared names",
                filtered.len()
            );
        }
        OutputFormat::Json => {
            let arr: Vec<serde_json::Value> = filtered
                .iter()
                .map(|o| {
                    serde_json::json!({
                        "system_a": source_system_display(o.system_a as u8),
                        "system_b": source_system_display(o.system_b as u8),
                        "shared_names": o.shared_names,
                    })
                })
                .collect();
            println!(
                "{}",
                serde_json::to_string_pretty(&arr).expect("invariant: json serialization")
            );
        }
        fmt @ (OutputFormat::Csv | OutputFormat::Tsv) => {
            emit_delimited_row(&["system_a", "system_b", "shared_names"], fmt);
            for o in &filtered {
                let shared = o.shared_names.to_string();
                emit_delimited_row(
                    &[
                        source_system_display(o.system_a as u8),
                        source_system_display(o.system_b as u8),
                        &shared,
                    ],
                    fmt,
                );
            }
        }
    }
}

// ---------------------------------------------------------------------------
// graph stats
// ---------------------------------------------------------------------------

fn cmd_graph_stats(args: &[String]) {
    let format = parse_format_arg(args);

    let lib = load_library();
    let index = build_index(&lib);
    let report = index.generate_report(10);

    match format {
        OutputFormat::Table => print_stats_table(&report),
        OutputFormat::Json => print_stats_json(&report),
        fmt @ (OutputFormat::Csv | OutputFormat::Tsv) => print_stats_delimited(&report, fmt),
    }
}

fn print_stats_table(report: &CrossSystemReport) {
    println!("Knowledge Graph Statistics");
    println!("=========================");
    println!("Total constants indexed:   {}", report.total_constants);
    println!("Source systems:            {}", report.total_systems);
    println!(
        "Multi-system names:        {} (appear in 2+ systems)",
        report.multi_system_count
    );

    if !report.top_cross_referenced.is_empty() {
        println!("\nTop cross-referenced names:");
        println!(
            "  {:<40} {:<10} {:<10}",
            "CANONICAL NAME", "SYSTEMS", "REFS"
        );
        println!("  {}", "-".repeat(60));
        for m in &report.top_cross_referenced {
            println!(
                "  {:<40} {:<10} {:<10}",
                truncate_name(&m.canonical_name, 40),
                m.system_count,
                m.refs.len(),
            );
        }
    }

    let non_zero: Vec<_> = report
        .overlap_matrix
        .iter()
        .filter(|o| o.shared_names > 0)
        .collect();
    if !non_zero.is_empty() {
        println!("\nSystem overlap matrix (pairs with shared names):");
        println!("  {:<20} {:<20} {:<10}", "SYSTEM A", "SYSTEM B", "SHARED");
        println!("  {}", "-".repeat(50));
        for o in non_zero.iter().take(15) {
            println!(
                "  {:<20} {:<20} {:<10}",
                source_system_display(o.system_a as u8),
                source_system_display(o.system_b as u8),
                o.shared_names,
            );
        }
    }
}

fn print_stats_json(report: &CrossSystemReport) {
    let top_matches: Vec<serde_json::Value> = report
        .top_cross_referenced
        .iter()
        .map(|m| {
            serde_json::json!({
                "canonical_name": m.canonical_name,
                "system_count": m.system_count,
                "ref_count": m.refs.len(),
                "confidence": m.confidence,
            })
        })
        .collect();

    let overlap_arr: Vec<serde_json::Value> = report
        .overlap_matrix
        .iter()
        .filter(|o| o.shared_names > 0)
        .map(|o| {
            serde_json::json!({
                "system_a": source_system_display(o.system_a as u8),
                "system_b": source_system_display(o.system_b as u8),
                "shared_names": o.shared_names,
            })
        })
        .collect();

    let obj = serde_json::json!({
        "total_constants": report.total_constants,
        "total_systems": report.total_systems,
        "multi_system_count": report.multi_system_count,
        "top_cross_referenced": top_matches,
        "overlap_matrix": overlap_arr,
    });
    println!(
        "{}",
        serde_json::to_string_pretty(&obj).expect("invariant: json serialization")
    );
}

// ---------------------------------------------------------------------------
// Argument parsing helpers
// ---------------------------------------------------------------------------

fn parse_limit(args: &[String], default: usize) -> usize {
    let mut i = 0;
    while i < args.len() {
        if args[i] == "--limit" {
            if let Some(val) = args.get(i + 1) {
                return val.parse().unwrap_or(default);
            }
        }
        i += 1;
    }
    default
}

fn parse_min(args: &[String], default: usize) -> usize {
    let mut i = 0;
    while i < args.len() {
        if args[i] == "--min" {
            if let Some(val) = args.get(i + 1) {
                return val.parse().unwrap_or(default);
            }
        }
        i += 1;
    }
    default
}

fn truncate_name(s: &str, max_len: usize) -> &str {
    if s.len() <= max_len {
        s
    } else {
        &s[..max_len]
    }
}
