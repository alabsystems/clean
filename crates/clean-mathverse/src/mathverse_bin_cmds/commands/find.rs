// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `mathverse find` — unified search combining name, tags, similarity, domain, cross-system,
//! and BM25 semantic search.

use crate::library::MathverseLibrary;
use crate::search::MathverseSearch;
use crate::similar::{SimilarResult, SimilarityEngine, SimilarityReason};

use crate::mathverse_bin_cmds::fmt::{
    confidence_display, domain_display, emit_delimited_row, parse_source_system,
    source_system_display, OutputFormat,
};
use crate::mathverse_bin_cmds::load_library;

use super::truncate;

pub fn cmd_find(args: &[String]) {
    let opts = FindOpts::parse(args);

    if opts.list_tags {
        run_list_tags(opts.limit, opts.format);
        return;
    }

    if opts.query.is_none()
        && opts.tags.is_empty()
        && opts.similar.is_none()
        && opts.cross_system.is_none()
        && opts.domain.is_none()
        && opts.system.is_none()
    {
        print_find_usage();
        std::process::exit(1);
    }

    let lib = load_library();

    if let Some(ref similar_name) = opts.similar {
        run_similar(&lib, similar_name, &opts);
        return;
    }

    if let Some(ref cross_name) = opts.cross_system {
        run_cross_system(&lib, cross_name, &opts);
        return;
    }

    if !opts.tags.is_empty() {
        run_tag_search(&lib, &opts.tags, opts.limit, opts.format);
        return;
    }

    if opts.semantic {
        run_semantic(&lib, &opts);
        return;
    }

    // Default: full-text search across names (with optional domain/system filters).
    run_fulltext(&lib, &opts);
}

fn run_fulltext(lib: &MathverseLibrary, opts: &FindOpts) {
    let results = collect_fulltext_matches(lib, opts);
    match opts.format {
        OutputFormat::Table => print_fulltext_table(lib, &results),
        OutputFormat::Json => print_fulltext_json(lib, &results),
        fmt @ (OutputFormat::Csv | OutputFormat::Tsv) => {
            print_fulltext_delimited(lib, &results, fmt)
        }
    }
}

fn collect_fulltext_matches(lib: &MathverseLibrary, opts: &FindOpts) -> Vec<(u32, String)> {
    let query = opts.query.as_deref().unwrap_or("");
    let query_lower = query.to_lowercase();
    let count = lib.constant_count();
    let mut results: Vec<(u32, String)> = Vec::new();
    for idx in 0..count as u32 {
        let name = match lib.get_name(idx) {
            Some(n) => n,
            None => continue,
        };
        if !name.to_lowercase().contains(&query_lower) {
            continue;
        }
        if let Some(header) = lib.get_constant(idx) {
            if opts.system.is_some_and(|s| header.source_system != s) {
                continue;
            }
            if opts.domain.is_some_and(|d| header.content_domain != d) {
                continue;
            }
        }
        results.push((idx, name.to_owned()));
        if results.len() >= opts.limit {
            break;
        }
    }
    results
}

fn print_fulltext_table(lib: &MathverseLibrary, results: &[(u32, String)]) {
    if results.is_empty() {
        println!("No results found.");
        return;
    }
    println!(
        "{:<8} {:<50} {:<15} {:<12} {:<16}",
        "IDX", "NAME", "SYSTEM", "DOMAIN", "TRUST"
    );
    println!("{}", "-".repeat(103));
    for (idx, name) in results {
        if let Some(h) = lib.get_constant(*idx) {
            println!(
                "{:<8} {:<50} {:<15} {:<12} {:<16}",
                idx,
                truncate(name, 50),
                source_system_display(h.source_system),
                domain_display(h.content_domain),
                confidence_display(h.import_confidence),
            );
        }
    }
    println!("\n{} result(s)", results.len());
}

fn print_fulltext_json(lib: &MathverseLibrary, results: &[(u32, String)]) {
    let entries: Vec<serde_json::Value> = results
        .iter()
        .filter_map(|(idx, name)| {
            let h = lib.get_constant(*idx)?;
            Some(serde_json::json!({
                "idx": idx,
                "name": name,
                "source_system": source_system_display(h.source_system),
                "domain": domain_display(h.content_domain),
                "trust": confidence_display(h.import_confidence),
            }))
        })
        .collect();
    println!(
        "{}",
        serde_json::to_string_pretty(&entries).expect("invariant: json serialization")
    );
}

fn print_fulltext_delimited(lib: &MathverseLibrary, results: &[(u32, String)], fmt: OutputFormat) {
    emit_delimited_row(&["idx", "name", "source_system", "domain", "trust"], fmt);
    for (idx, name) in results {
        if let Some(h) = lib.get_constant(*idx) {
            let idx_s = idx.to_string();
            emit_delimited_row(
                &[
                    &idx_s,
                    name,
                    source_system_display(h.source_system),
                    domain_display(h.content_domain),
                    confidence_display(h.import_confidence),
                ],
                fmt,
            );
        }
    }
}

fn run_semantic(lib: &MathverseLibrary, opts: &FindOpts) {
    let query = opts.query.as_deref().unwrap_or("");
    let results = lib
        .search_semantic(query, opts.limit * 2)
        .unwrap_or_default();
    let filtered: Vec<_> = results
        .into_iter()
        .filter(|r| {
            opts.system.is_none_or(|s| r.header.source_system == s)
                && opts.domain.is_none_or(|d| r.header.content_domain == d)
        })
        .take(opts.limit)
        .collect();

    if filtered.is_empty() {
        println!("No results found.");
        return;
    }
    match opts.format {
        OutputFormat::Table => {
            println!(
                "{:<8} {:<50} {:<15} {:<12} {:<8}",
                "IDX", "NAME", "SYSTEM", "DOMAIN", "SCORE"
            );
            println!("{}", "-".repeat(95));
            for r in &filtered {
                let name = lib.get_name(r.constant_idx).unwrap_or("?");
                println!(
                    "{:<8} {:<50} {:<15} {:<12} {:<8.3}",
                    r.constant_idx,
                    truncate(name, 50),
                    source_system_display(r.header.source_system),
                    domain_display(r.header.content_domain),
                    r.score
                );
            }
            println!("\n{} result(s)", filtered.len());
        }
        OutputFormat::Json => {
            let entries: Vec<serde_json::Value> = filtered
                .iter()
                .map(|r| {
                    serde_json::json!({
                        "idx": r.constant_idx, "name": lib.get_name(r.constant_idx).unwrap_or("?"),
                        "source_system": source_system_display(r.header.source_system),
                        "domain": domain_display(r.header.content_domain), "score": r.score,
                    })
                })
                .collect();
            println!(
                "{}",
                serde_json::to_string_pretty(&entries).expect("invariant: json serialization")
            );
        }
        fmt @ (OutputFormat::Csv | OutputFormat::Tsv) => {
            emit_delimited_row(&["idx", "name", "source_system", "domain", "score"], fmt);
            for r in &filtered {
                let name = lib.get_name(r.constant_idx).unwrap_or("?");
                let idx = r.constant_idx.to_string();
                let score = format!("{:.3}", r.score);
                emit_delimited_row(
                    &[
                        &idx,
                        name,
                        source_system_display(r.header.source_system),
                        domain_display(r.header.content_domain),
                        &score,
                    ],
                    fmt,
                );
            }
        }
    }
}

fn run_similar(lib: &MathverseLibrary, name: &str, opts: &FindOpts) {
    let engine = SimilarityEngine::new(lib);
    let results = engine.similar_by_name(name, opts.limit);
    print_similar_results(lib, &results, opts);
}

fn run_cross_system(lib: &MathverseLibrary, name: &str, opts: &FindOpts) {
    let engine = SimilarityEngine::new(lib);
    let results = engine.cross_system_matches(name, opts.limit);
    print_similar_results(lib, &results, opts);
}

fn print_similar_results(lib: &MathverseLibrary, results: &[SimilarResult], opts: &FindOpts) {
    let reason_str = |r: &SimilarResult| match r.reason {
        SimilarityReason::NameSimilarity => "name",
        SimilarityReason::SameDomain => "domain",
        SimilarityReason::CrossSystem => "cross-system",
    };
    match opts.format {
        OutputFormat::Table => {
            if results.is_empty() {
                println!("No results found.");
                return;
            }
            println!(
                "{:<8} {:<50} {:<15} {:<8} {:<16}",
                "IDX", "NAME", "SYSTEM", "SCORE", "REASON"
            );
            println!("{}", "-".repeat(100));
            for r in results {
                let sys = lib
                    .get_constant(r.constant_idx)
                    .map(|h| source_system_display(h.source_system))
                    .unwrap_or("Unknown");
                println!(
                    "{:<8} {:<50} {:<15} {:<8.3} {:<16}",
                    r.constant_idx,
                    truncate(&r.name, 50),
                    sys,
                    r.score,
                    reason_str(r),
                );
            }
            println!("\n{} result(s)", results.len());
        }
        OutputFormat::Json => {
            let entries: Vec<serde_json::Value> = results
                .iter()
                .map(|r| {
                    let sys = lib
                        .get_constant(r.constant_idx)
                        .map(|h| source_system_display(h.source_system))
                        .unwrap_or("Unknown");
                    serde_json::json!({
                        "idx": r.constant_idx,
                        "name": r.name,
                        "source_system": sys,
                        "score": r.score,
                        "reason": format!("{:?}", r.reason),
                    })
                })
                .collect();
            println!(
                "{}",
                serde_json::to_string_pretty(&entries).expect("invariant: json serialization")
            );
        }
        fmt @ (OutputFormat::Csv | OutputFormat::Tsv) => {
            emit_delimited_row(&["idx", "name", "source_system", "score", "reason"], fmt);
            for r in results {
                let sys = lib
                    .get_constant(r.constant_idx)
                    .map(|h| source_system_display(h.source_system))
                    .unwrap_or("Unknown");
                let idx = r.constant_idx.to_string();
                let score = format!("{:.3}", r.score);
                emit_delimited_row(&[&idx, &r.name, sys, &score, reason_str(r)], fmt);
            }
        }
    }
}

// Tag search and list implementations are split out to `find_tag.rs` to keep
// this file under the per-file line budget.
use super::find_tag::{run_list_tags, run_tag_search};

fn print_find_usage() {
    eprintln!("Usage: mathverse find <query>                          Full-text name search");
    eprintln!("       mathverse find <query> --semantic               BM25 semantic search");
    eprintln!("       mathverse find --tag <t> [--tag <t2>]           Tag intersection search");
    eprintln!("       mathverse find --similar <name>                 Similar theorem discovery");
    eprintln!("       mathverse find --cross-system <name>            Cross-system equivalents");
    eprintln!("       mathverse find --domain <domain>                Domain filter");
    eprintln!("       mathverse find --system <system>                Source system filter");
    eprintln!("       mathverse find --tags                           List all known tags");
    eprintln!();
    eprintln!("Options:");
    eprintln!("  --semantic         Use BM25 engine with math abbreviation expansion");
    eprintln!("  --limit <N>        Max results (default: 20)");
    eprintln!("  --format <fmt>     Output format: table (default), json");
}

// -----------------------------------------------------------------------
// Options
// -----------------------------------------------------------------------

struct FindOpts {
    query: Option<String>,
    tags: Vec<String>,
    similar: Option<String>,
    cross_system: Option<String>,
    domain: Option<u8>,
    system: Option<u8>,
    semantic: bool,
    list_tags: bool,
    limit: usize,
    format: OutputFormat,
}

impl FindOpts {
    fn parse(args: &[String]) -> Self {
        let mut opts = Self {
            query: None,
            tags: Vec::new(),
            similar: None,
            cross_system: None,
            domain: None,
            system: None,
            semantic: false,
            list_tags: false,
            limit: 20,
            format: OutputFormat::Table,
        };
        let mut i = 0;
        while i < args.len() {
            match args[i].as_str() {
                "--tag" => {
                    i += 1;
                    if let Some(val) = args.get(i) {
                        opts.tags.push(val.clone());
                    }
                }
                "--similar" => {
                    i += 1;
                    if let Some(val) = args.get(i) {
                        opts.similar = Some(val.clone());
                    }
                }
                "--cross-system" => {
                    i += 1;
                    if let Some(val) = args.get(i) {
                        opts.cross_system = Some(val.clone());
                    }
                }
                "--domain" => {
                    i += 1;
                    if let Some(val) = args.get(i) {
                        opts.domain = parse_domain(val);
                    }
                }
                "--system" => {
                    i += 1;
                    if let Some(val) = args.get(i) {
                        opts.system = parse_source_system(val);
                    }
                }
                "--semantic" => {
                    opts.semantic = true;
                }
                "--tags" => {
                    opts.list_tags = true;
                }
                "--limit" => {
                    i += 1;
                    if let Some(val) = args.get(i) {
                        opts.limit = val.parse().unwrap_or(20);
                    }
                }
                "--format" => {
                    i += 1;
                    if let Some(val) = args.get(i) {
                        opts.format = OutputFormat::parse(val).unwrap_or_else(|| {
                            eprintln!("Unknown format: {val}");
                            std::process::exit(1);
                        });
                    }
                }
                arg if !arg.starts_with("--") && opts.query.is_none() => {
                    opts.query = Some(arg.to_string());
                }
                _ => {}
            }
            i += 1;
        }
        opts
    }
}

fn parse_domain(name: &str) -> Option<u8> {
    match name.to_lowercase().replace(['-', '_'], "").as_str() {
        "puremath" | "math" => Some(0),
        "software" => Some(1),
        "complexity" => Some(2),
        "nnverification" | "nn" => Some(3),
        "physics" => Some(4),
        "logic" => Some(5),
        "cryptography" | "crypto" => Some(6),
        _ => None,
    }
}
