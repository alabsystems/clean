// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `mathverse diff` — symmetric diff of two `.mathverse` shards by constant name.
//!
//! Useful for comparing library versions, auditing a new shard against
//! a prior release, or confirming that a rebuild is deterministic.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use crate::shard::ShardReader;

use crate::mathverse_bin_cmds::fmt::{emit_delimited_row, OutputFormat};

use super::parse_format_arg;

pub fn cmd_diff(args: &[String]) {
    if args.len() < 2 {
        eprintln!(
            "Usage: mathverse diff <shard-a.mathverse> <shard-b.mathverse> [--format table|json|csv|tsv]"
        );
        std::process::exit(1);
    }
    let a_path = PathBuf::from(&args[0]);
    let b_path = PathBuf::from(&args[1]);
    let format = parse_format_arg(&args[2..]);

    let a_names = read_names(&a_path).unwrap_or_else(|e| {
        eprintln!("Failed to read {}: {e}", a_path.display());
        std::process::exit(1);
    });
    let b_names = read_names(&b_path).unwrap_or_else(|e| {
        eprintln!("Failed to read {}: {e}", b_path.display());
        std::process::exit(1);
    });

    let only_a: Vec<&String> = a_names.difference(&b_names).collect();
    let only_b: Vec<&String> = b_names.difference(&a_names).collect();
    let shared = a_names.intersection(&b_names).count();

    match format {
        OutputFormat::Table => print_table(&a_path, &b_path, &only_a, &only_b, shared),
        OutputFormat::Json => print_json(&a_path, &b_path, &only_a, &only_b, shared),
        fmt @ (OutputFormat::Csv | OutputFormat::Tsv) => print_delimited(&only_a, &only_b, fmt),
    }
}

fn read_names(path: &Path) -> Result<BTreeSet<String>, String> {
    let reader = ShardReader::from_file(path).map_err(|e| e.to_string())?;
    let mut names = BTreeSet::new();
    for c in &reader.constants {
        if let Some(s) = reader.strings.get(c.name_idx as usize) {
            names.insert(s.clone());
        }
    }
    Ok(names)
}

fn print_table(a: &Path, b: &Path, only_a: &[&String], only_b: &[&String], shared: usize) {
    println!("Shard A: {}", a.display());
    println!("Shard B: {}", b.display());
    println!("Shared constants: {shared}");
    println!("Only in A: {}", only_a.len());
    println!("Only in B: {}", only_b.len());

    if !only_a.is_empty() {
        println!("\n--- Only in A ---");
        for name in only_a.iter().take(200) {
            println!("  - {name}");
        }
        if only_a.len() > 200 {
            println!("  ... and {} more", only_a.len() - 200);
        }
    }
    if !only_b.is_empty() {
        println!("\n--- Only in B ---");
        for name in only_b.iter().take(200) {
            println!("  + {name}");
        }
        if only_b.len() > 200 {
            println!("  ... and {} more", only_b.len() - 200);
        }
    }
}

fn print_json(a: &Path, b: &Path, only_a: &[&String], only_b: &[&String], shared: usize) {
    let obj = serde_json::json!({
        "shard_a": a.display().to_string(),
        "shard_b": b.display().to_string(),
        "shared_count": shared,
        "only_a_count": only_a.len(),
        "only_b_count": only_b.len(),
        "only_a": only_a,
        "only_b": only_b,
    });
    println!(
        "{}",
        serde_json::to_string_pretty(&obj).expect("invariant: json serialization")
    );
}

/// CSV/TSV diff output: one row per declaration present in only one shard,
/// with a `side` column ("a" or "b") to distinguish. Shared constants are
/// omitted by design — `--format json` still carries the shared count.
fn print_delimited(only_a: &[&String], only_b: &[&String], fmt: OutputFormat) {
    emit_delimited_row(&["side", "name"], fmt);
    for name in only_a {
        emit_delimited_row(&["a", name.as_str()], fmt);
    }
    for name in only_b {
        emit_delimited_row(&["b", name.as_str()], fmt);
    }
}
