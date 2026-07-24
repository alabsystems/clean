// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `mathverse deps` — transitive dependency graph for a single declaration.
//!
//! Walks the dependency adjacency list built at library load time and emits
//! either a direct-dependency listing or a bounded transitive closure. With
//! `--reverse` it walks the *inverse* adjacency instead — the declarations that
//! USE the target (its users / blast radius), ranked by impact — answering the
//! premise-selection / "what breaks if I change X" question.

use std::collections::{HashSet, VecDeque};

use crate::library::MathverseLibrary;
use crate::types::ConstantIdx;

use crate::mathverse_bin_cmds::fmt::{emit_delimited_row, source_system_display, OutputFormat};
use crate::mathverse_bin_cmds::load_library;

use super::{parse_format_arg, truncate};

/// Shared entry for `deps` (forward) and `uses` (reverse). `force_reverse`
/// lets the `uses` alias guarantee reverse mode even without `--reverse`.
pub fn cmd_deps_dir(args: &[String], force_reverse: bool) {
    if args.is_empty() {
        eprintln!(
            "Usage: mathverse deps <name> [--reverse] [--transitive] [--depth N] \
             [--limit N] [--format table|json|csv|tsv]"
        );
        std::process::exit(1);
    }
    let target = &args[0];
    let mut opts = DepsOpts::parse(&args[1..]);
    opts.reverse = opts.reverse || force_reverse;
    let format = parse_format_arg(&args[1..]);
    let lib = load_library();

    // Tolerant resolution so a `search`/`find` hit pipes straight in; report any
    // non-exact resolution on stderr (never silently retarget).
    let Some(idx) = lib.resolve_name_loose(target) else {
        eprintln!("Declaration not found: {target}");
        std::process::exit(1);
    };
    let resolved = lib.get_name(idx).unwrap_or(target).to_string();
    if &resolved != target {
        eprintln!("note: '{target}' not found exactly; using '{resolved}'");
    }

    let dep_list = if opts.reverse {
        lib.reverse_deps_bounded(idx, opts.transitive, opts.depth, opts.limit)
    } else {
        collect_deps(&lib, idx, &opts)
    };
    match format {
        OutputFormat::Table => print_table(&lib, &resolved, &dep_list, opts.reverse),
        OutputFormat::Json => print_json(&lib, &resolved, &dep_list, opts.reverse),
        fmt @ (OutputFormat::Csv | OutputFormat::Tsv) => {
            print_delimited(&lib, &resolved, &dep_list, opts.reverse, fmt)
        }
    }
}

pub fn cmd_deps(args: &[String]) {
    cmd_deps_dir(args, false);
}

/// `mathverse uses <name>` — reverse-dependency alias for `deps --reverse`.
pub fn cmd_uses(args: &[String]) {
    cmd_deps_dir(args, true);
}

struct DepsOpts {
    reverse: bool,
    transitive: bool,
    depth: usize,
    limit: usize,
}

impl DepsOpts {
    fn parse(args: &[String]) -> Self {
        let mut opts = Self {
            reverse: false,
            transitive: false,
            depth: 1,
            limit: 200,
        };
        let mut i = 0;
        while i < args.len() {
            match args[i].as_str() {
                "--reverse" => opts.reverse = true,
                "--transitive" => {
                    opts.transitive = true;
                    if opts.depth == 1 {
                        opts.depth = usize::MAX;
                    }
                }
                "--depth" => {
                    i += 1;
                    if let Some(val) = args.get(i) {
                        opts.depth = val.parse().unwrap_or(1);
                        if opts.depth > 1 {
                            opts.transitive = true;
                        }
                    }
                }
                "--limit" => {
                    i += 1;
                    if let Some(val) = args.get(i) {
                        opts.limit = val.parse().unwrap_or(200);
                    }
                }
                _ => {}
            }
            i += 1;
        }
        opts
    }
}

/// BFS walk over the dependency adjacency list bounded by `depth` and `limit`.
/// The root itself is not included in results.
fn collect_deps(
    lib: &MathverseLibrary,
    root: ConstantIdx,
    opts: &DepsOpts,
) -> Vec<(ConstantIdx, u32)> {
    let adj = lib.deps();
    let mut visited: HashSet<ConstantIdx> = HashSet::new();
    let mut queue: VecDeque<(ConstantIdx, u32)> = VecDeque::new();
    let mut out: Vec<(ConstantIdx, u32)> = Vec::new();

    visited.insert(root);
    if let Some(direct) = adj.get(root as usize) {
        for &d in direct {
            queue.push_back((d, 1));
        }
    }

    while let Some((idx, depth)) = queue.pop_front() {
        if !visited.insert(idx) {
            continue;
        }
        out.push((idx, depth));
        if out.len() >= opts.limit {
            break;
        }
        if !opts.transitive {
            continue;
        }
        if depth as usize >= opts.depth {
            continue;
        }
        if let Some(next) = adj.get(idx as usize) {
            for &n in next {
                if !visited.contains(&n) {
                    queue.push_back((n, depth + 1));
                }
            }
        }
    }

    out
}

fn print_table(lib: &MathverseLibrary, root: &str, deps: &[(ConstantIdx, u32)], reverse: bool) {
    if deps.is_empty() {
        if reverse {
            println!("Nothing in the loaded corpus depends on {root}.");
        } else {
            println!("{root} has no recorded dependencies.");
        }
        return;
    }
    if reverse {
        println!("Reverse dependencies (users) of {root}:");
        println!(
            "{:<8} {:<6} {:<8} {:<50} {:<15}",
            "IDX", "DEPTH", "USED-BY", "NAME", "SYSTEM"
        );
        println!("{}", "-".repeat(92));
        for &(idx, depth) in deps {
            let name = lib.get_name(idx).unwrap_or("?");
            let sys = lib
                .get_constant(idx)
                .map(|h| source_system_display(h.source_system))
                .unwrap_or("?");
            println!(
                "{:<8} {:<6} {:<8} {:<50} {:<15}",
                idx,
                depth,
                lib.reverse_in_degree(idx),
                truncate(name, 50),
                sys
            );
        }
        println!("\n{} dependents (ranked by impact)", deps.len());
        return;
    }
    println!("Dependencies of {root}:");
    println!(
        "{:<8} {:<6} {:<50} {:<15}",
        "IDX", "DEPTH", "NAME", "SYSTEM"
    );
    println!("{}", "-".repeat(83));
    for &(idx, depth) in deps {
        let name = lib.get_name(idx).unwrap_or("?");
        let sys = lib
            .get_constant(idx)
            .map(|h| source_system_display(h.source_system))
            .unwrap_or("?");
        println!(
            "{:<8} {:<6} {:<50} {:<15}",
            idx,
            depth,
            truncate(name, 50),
            sys
        );
    }
    println!("\n{} dependencies", deps.len());
}

fn print_json(lib: &MathverseLibrary, root: &str, deps: &[(ConstantIdx, u32)], reverse: bool) {
    let entries: Vec<serde_json::Value> = deps
        .iter()
        .map(|&(idx, depth)| {
            let mut row = serde_json::json!({
                "idx": idx,
                "depth": depth,
                "name": lib.get_name(idx).unwrap_or("?"),
                "source_system": lib
                    .get_constant(idx)
                    .map(|h| source_system_display(h.source_system))
                    .unwrap_or("?"),
            });
            if reverse {
                row["used_by_count"] = serde_json::json!(lib.reverse_in_degree(idx));
            }
            row
        })
        .collect();
    let mut obj = serde_json::json!({
        "root": root,
        "direction": if reverse { "reverse" } else { "forward" },
        "count": deps.len(),
    });
    obj[if reverse {
        "dependents"
    } else {
        "dependencies"
    }] = serde_json::json!(entries);
    println!(
        "{}",
        serde_json::to_string_pretty(&obj).expect("invariant: json serialization")
    );
}

fn print_delimited(
    lib: &MathverseLibrary,
    root: &str,
    deps: &[(ConstantIdx, u32)],
    reverse: bool,
    fmt: OutputFormat,
) {
    if reverse {
        emit_delimited_row(
            &[
                "root",
                "idx",
                "depth",
                "used_by_count",
                "name",
                "source_system",
            ],
            fmt,
        );
        for &(idx, depth) in deps {
            let idx_s = idx.to_string();
            let depth_s = depth.to_string();
            let used_by = lib.reverse_in_degree(idx).to_string();
            let name = lib.get_name(idx).unwrap_or("?");
            let sys = lib
                .get_constant(idx)
                .map(|h| source_system_display(h.source_system))
                .unwrap_or("?");
            emit_delimited_row(&[root, &idx_s, &depth_s, &used_by, name, sys], fmt);
        }
        return;
    }
    emit_delimited_row(&["root", "idx", "depth", "name", "source_system"], fmt);
    for &(idx, depth) in deps {
        let idx_s = idx.to_string();
        let depth_s = depth.to_string();
        let name = lib.get_name(idx).unwrap_or("?");
        let sys = lib
            .get_constant(idx)
            .map(|h| source_system_display(h.source_system))
            .unwrap_or("?");
        emit_delimited_row(&[root, &idx_s, &depth_s, name, sys], fmt);
    }
}
