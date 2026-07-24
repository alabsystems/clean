// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `mathverse search` — fuzzy or exact name search over the library.
//!
//! Supports `--semantic` mode for BM25 search with math abbreviation expansion,
//! and `--explain` mode to show token-level score breakdowns.

use crate::library::MathverseLibrary;
use crate::search::MathverseSearch;

use crate::mathverse_bin_cmds::fmt::{
    confidence_display, domain_display, emit_delimited_row, parse_source_system, parse_trust_level,
    source_system_display, OutputFormat,
};
use crate::mathverse_bin_cmds::load_library;

use super::truncate;

pub fn cmd_search(args: &[String]) {
    if args.is_empty() {
        eprintln!(
            "Usage: mathverse search <query> [--exact] [--semantic] [--explain] \
             [--system <name>] [--trust <level>] [--limit N] \
             [--format table|json|csv|tsv]"
        );
        std::process::exit(1);
    }
    let query = &args[0];
    let opts = SearchOpts::parse(&args[1..]);
    let lib = load_library();

    if opts.explain {
        run_explain(&lib, query, &opts);
    } else if opts.semantic {
        run_semantic(&lib, query, &opts);
    } else {
        let results = collect_matches(&lib, query, &opts);
        match opts.format {
            OutputFormat::Table => print_table(&lib, &results),
            OutputFormat::Json => print_json(&lib, &results),
            fmt @ (OutputFormat::Csv | OutputFormat::Tsv) => print_delimited(&lib, &results, fmt),
        }
    }
}

fn run_semantic(lib: &MathverseLibrary, query: &str, opts: &SearchOpts) {
    let results = lib
        .search_semantic(query, opts.limit * 2)
        .unwrap_or_default();
    let filtered: Vec<_> = results
        .into_iter()
        .filter(|r| {
            opts.system_filter
                .is_none_or(|s| r.header.source_system == s)
                && opts
                    .trust_filter
                    .is_none_or(|t| r.header.import_confidence == t)
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
                "{:<8} {:<50} {:<15} {:<16} {:<8}",
                "IDX", "NAME", "SYSTEM", "TRUST", "SCORE"
            );
            println!("{}", "-".repeat(99));
            for r in &filtered {
                let name = lib.get_name(r.constant_idx).unwrap_or("?");
                println!(
                    "{:<8} {:<50} {:<15} {:<16} {:<8.3}",
                    r.constant_idx,
                    truncate(name, 50),
                    source_system_display(r.header.source_system),
                    confidence_display(r.header.import_confidence),
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
                        "trust": confidence_display(r.header.import_confidence),
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
            emit_delimited_row(&["idx", "name", "source_system", "trust", "score"], fmt);
            for r in &filtered {
                let name = lib.get_name(r.constant_idx).unwrap_or("?");
                let idx = r.constant_idx.to_string();
                let score = format!("{:.3}", r.score);
                emit_delimited_row(
                    &[
                        &idx,
                        name,
                        source_system_display(r.header.source_system),
                        confidence_display(r.header.import_confidence),
                        &score,
                    ],
                    fmt,
                );
            }
        }
    }
}

fn run_explain(lib: &MathverseLibrary, query: &str, opts: &SearchOpts) {
    let expanded = crate::embedding::math_tokenize(query);
    let explanations = lib.search_explain(query, opts.limit);
    let is_delimited = opts.format.is_delimited();
    if !is_delimited {
        println!("Query: {query:?}");
        println!("Expanded tokens: {expanded:?}\n");
    }
    if explanations.is_empty() {
        if !is_delimited {
            println!("No results found.");
        }
        return;
    }
    match opts.format {
        OutputFormat::Table => {
            for (rank, expl) in explanations.iter().enumerate() {
                let name = lib.get_name(expl.constant_idx).unwrap_or("?");
                println!(
                    "#{:<3} {} (idx={}, score={:.3})",
                    rank + 1,
                    name,
                    expl.constant_idx,
                    expl.total_score
                );
                for ts in &expl.token_scores {
                    println!(
                        "      token={:<20} tf={:<4} df={:<6} score={:.3}",
                        ts.token, ts.tf, ts.df, ts.score
                    );
                }
                println!();
            }
            println!("{} result(s)", explanations.len());
        }
        OutputFormat::Json => {
            let entries: Vec<serde_json::Value> = explanations.iter().map(|expl| {
                let tokens: Vec<serde_json::Value> = expl.token_scores.iter()
                    .map(|ts| serde_json::json!({"token": ts.token, "tf": ts.tf, "df": ts.df, "score": ts.score}))
                    .collect();
                serde_json::json!({
                    "idx": expl.constant_idx, "name": lib.get_name(expl.constant_idx).unwrap_or("?"),
                    "total_score": expl.total_score, "query_tokens": expl.query_tokens, "token_scores": tokens,
                })
            }).collect();
            println!(
                "{}",
                serde_json::to_string_pretty(&entries).expect("invariant: json serialization")
            );
        }
        fmt @ (OutputFormat::Csv | OutputFormat::Tsv) => {
            // Flatten explain into one row per (result, token) pair so the data
            // fits a uniform tabular schema.
            emit_delimited_row(
                &[
                    "idx",
                    "name",
                    "total_score",
                    "token",
                    "tf",
                    "df",
                    "token_score",
                ],
                fmt,
            );
            for expl in &explanations {
                let name = lib.get_name(expl.constant_idx).unwrap_or("?");
                let idx = expl.constant_idx.to_string();
                let total = format!("{:.3}", expl.total_score);
                if expl.token_scores.is_empty() {
                    emit_delimited_row(&[&idx, name, &total, "", "", "", ""], fmt);
                } else {
                    for ts in &expl.token_scores {
                        let tf = ts.tf.to_string();
                        let df = ts.df.to_string();
                        let score = format!("{:.3}", ts.score);
                        emit_delimited_row(&[&idx, name, &total, &ts.token, &tf, &df, &score], fmt);
                    }
                }
            }
        }
    }
}

fn collect_matches<'a>(
    lib: &'a MathverseLibrary,
    query: &str,
    opts: &SearchOpts,
) -> Vec<(u32, &'a str)> {
    let count = lib.constant_count();
    let query_lower = query.to_lowercase();
    let mut results: Vec<(u32, &str)> = Vec::new();

    for idx in 0..count as u32 {
        let name = match lib.get_name(idx) {
            Some(n) => n,
            None => continue,
        };
        let matched = if opts.exact {
            name == query
        } else {
            name.to_lowercase().contains(&query_lower)
        };
        if !matched {
            continue;
        }
        if let Some(header) = lib.get_constant(idx) {
            if let Some(sys) = opts.system_filter {
                if header.source_system != sys {
                    continue;
                }
            }
            if let Some(trust) = opts.trust_filter {
                if header.import_confidence != trust {
                    continue;
                }
            }
        }
        results.push((idx, name));
        if results.len() >= opts.limit {
            break;
        }
    }
    results
}

fn print_table(lib: &MathverseLibrary, results: &[(u32, &str)]) {
    if results.is_empty() {
        println!("No results found.");
        return;
    }
    println!(
        "{:<8} {:<50} {:<15} {:<16}",
        "IDX", "NAME", "SYSTEM", "TRUST"
    );
    println!("{}", "-".repeat(93));
    for &(idx, name) in results {
        if let Some(h) = lib.get_constant(idx) {
            println!(
                "{:<8} {:<50} {:<15} {:<16}",
                idx,
                truncate(name, 50),
                source_system_display(h.source_system),
                confidence_display(h.import_confidence),
            );
        }
    }
    println!("\n{} result(s)", results.len());
}

fn print_json(lib: &MathverseLibrary, results: &[(u32, &str)]) {
    let entries: Vec<serde_json::Value> = results
        .iter()
        .filter_map(|&(idx, name)| {
            let h = lib.get_constant(idx)?;
            Some(serde_json::json!({
                "idx": idx,
                "name": name,
                "source_system": source_system_display(h.source_system),
                "trust": confidence_display(h.import_confidence),
                "domain": domain_display(h.content_domain),
                "has_value": h.has_value(),
                "axiom_count": h.axiom_profile.axiom_count(),
            }))
        })
        .collect();
    println!(
        "{}",
        serde_json::to_string_pretty(&entries).expect("invariant: json serialization")
    );
}

fn print_delimited(lib: &MathverseLibrary, results: &[(u32, &str)], fmt: OutputFormat) {
    emit_delimited_row(
        &[
            "idx",
            "name",
            "source_system",
            "trust",
            "domain",
            "has_value",
            "axiom_count",
        ],
        fmt,
    );
    for &(idx, name) in results {
        if let Some(h) = lib.get_constant(idx) {
            let idx_s = idx.to_string();
            let has_val = h.has_value().to_string();
            let axioms = h.axiom_profile.axiom_count().to_string();
            emit_delimited_row(
                &[
                    &idx_s,
                    name,
                    source_system_display(h.source_system),
                    confidence_display(h.import_confidence),
                    domain_display(h.content_domain),
                    &has_val,
                    &axioms,
                ],
                fmt,
            );
        }
    }
}

// -----------------------------------------------------------------------
// Options
// -----------------------------------------------------------------------

struct SearchOpts {
    exact: bool,
    semantic: bool,
    explain: bool,
    system_filter: Option<u8>,
    trust_filter: Option<u8>,
    limit: usize,
    format: OutputFormat,
}

impl SearchOpts {
    fn parse(args: &[String]) -> Self {
        let mut opts = Self {
            exact: false,
            semantic: false,
            explain: false,
            system_filter: None,
            trust_filter: None,
            limit: 20,
            format: OutputFormat::Table,
        };
        let mut i = 0;
        while i < args.len() {
            match args[i].as_str() {
                "--exact" => opts.exact = true,
                "--semantic" => opts.semantic = true,
                "--explain" => {
                    opts.explain = true;
                    opts.semantic = true; // explain implies semantic
                }
                "--system" => {
                    i += 1;
                    if let Some(val) = args.get(i) {
                        opts.system_filter = parse_source_system(val);
                        if opts.system_filter.is_none() {
                            eprintln!("Unknown system: {val}");
                            std::process::exit(1);
                        }
                    }
                }
                "--trust" => {
                    i += 1;
                    if let Some(val) = args.get(i) {
                        opts.trust_filter = parse_trust_level(val);
                        if opts.trust_filter.is_none() {
                            eprintln!("Unknown trust level: {val}");
                            std::process::exit(1);
                        }
                    }
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
                _ => {}
            }
            i += 1;
        }
        opts
    }
}
