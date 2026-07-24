// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `mathverse list` — enumerate declarations with filtering and pagination.

use crate::library::MathverseLibrary;

use crate::mathverse_bin_cmds::fmt::{
    confidence_display, emit_delimited_row, parse_source_system, source_system_display,
    OutputFormat,
};
use crate::mathverse_bin_cmds::load_library;

use super::truncate;

pub fn cmd_list(args: &[String]) {
    let opts = ListOpts::parse(args);
    let lib = load_library();
    let count = lib.constant_count();

    let mut entries: Vec<(u32, &str)> = Vec::new();
    let mut skipped = 0usize;
    for idx in 0..count as u32 {
        let name = match lib.get_name(idx) {
            Some(n) => n,
            None => continue,
        };
        if let Some(sys) = opts.system_filter {
            if let Some(h) = lib.get_constant(idx) {
                if h.source_system != sys {
                    continue;
                }
            }
        }
        if skipped < opts.offset {
            skipped += 1;
            continue;
        }
        entries.push((idx, name));
        if entries.len() >= opts.limit {
            break;
        }
    }

    match opts.format {
        OutputFormat::Table => print_table(&lib, &entries, count),
        OutputFormat::Json => print_json(&lib, &entries),
        fmt @ (OutputFormat::Csv | OutputFormat::Tsv) => print_delimited(&lib, &entries, fmt),
    }
}

fn print_table(lib: &MathverseLibrary, entries: &[(u32, &str)], total: usize) {
    if entries.is_empty() {
        println!("No entries.");
        return;
    }
    println!(
        "{:<8} {:<50} {:<15} {:<16}",
        "IDX", "NAME", "SYSTEM", "TRUST"
    );
    println!("{}", "-".repeat(93));
    for &(idx, name) in entries {
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
    println!("\nShowing {} of {} total", entries.len(), total);
}

fn print_json(lib: &MathverseLibrary, entries: &[(u32, &str)]) {
    let arr: Vec<serde_json::Value> = entries
        .iter()
        .filter_map(|&(idx, name)| {
            let h = lib.get_constant(idx)?;
            Some(serde_json::json!({
                "idx": idx,
                "name": name,
                "source_system": source_system_display(h.source_system),
                "trust": confidence_display(h.import_confidence),
            }))
        })
        .collect();
    println!(
        "{}",
        serde_json::to_string_pretty(&arr).expect("invariant: json serialization")
    );
}

fn print_delimited(lib: &MathverseLibrary, entries: &[(u32, &str)], fmt: OutputFormat) {
    emit_delimited_row(&["idx", "name", "source_system", "trust"], fmt);
    for &(idx, name) in entries {
        if let Some(h) = lib.get_constant(idx) {
            let idx_s = idx.to_string();
            emit_delimited_row(
                &[
                    &idx_s,
                    name,
                    source_system_display(h.source_system),
                    confidence_display(h.import_confidence),
                ],
                fmt,
            );
        }
    }
}

// -----------------------------------------------------------------------
// Options
// -----------------------------------------------------------------------

struct ListOpts {
    system_filter: Option<u8>,
    limit: usize,
    offset: usize,
    format: OutputFormat,
}

impl ListOpts {
    fn parse(args: &[String]) -> Self {
        let mut opts = Self {
            system_filter: None,
            limit: 20,
            offset: 0,
            format: OutputFormat::Table,
        };
        let mut i = 0;
        while i < args.len() {
            match args[i].as_str() {
                "list" => {} // skip the subcommand name
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
                "--limit" => {
                    i += 1;
                    if let Some(val) = args.get(i) {
                        opts.limit = val.parse().unwrap_or(20);
                    }
                }
                "--offset" => {
                    i += 1;
                    if let Some(val) = args.get(i) {
                        opts.offset = val.parse().unwrap_or(0);
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
