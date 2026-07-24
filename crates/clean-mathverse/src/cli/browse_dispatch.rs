// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Dispatch helpers for the `list`, `sample`, `deps`, and `version` verbs
//! under `clean mathverse <verb>`.
//!
//! These mirror the behaviour of the standalone `mathverse` binary
//! (`crates/clean-mathverse/src/bin/mathverse/commands/{list,sample,deps,version}.rs`)
//! 1:1 while routing through the `clean-cli` clap tree. Kept in a separate
//! module from [`super::dispatch`] so each file stays under the 500-line
//! cap (see Issue #3512 risk note).
//!
//! Design: `designs/2026-04-19-epic-3436-orphan-triage.md` §"Mathverse partial
//! coverage". Epic: #3436. Tracking: #3512.

use std::collections::{BTreeMap, HashSet, VecDeque};
use std::io::{self, Write};

use serde_json::json;

use crate::cli::browse_common::{
    load_library, load_library_opt, parse_source_system, parse_trust_level,
};
use crate::cli::format::{confidence_name, domain_name, source_system_name, truncate};
use crate::cli::{DepsArgs, ListArgs, MathverseCliError, SampleArgs, VersionArgs};
use crate::library::MathverseLibrary;
use crate::types::ConstantIdx;

// -- version ------------------------------------------------------------------

/// Release version string surfaced by `clean mathverse version`. Must match the
/// standalone `mathverse` binary (see `crates/clean-mathverse/src/bin/mathverse/commands/version.rs`).
const MATHVERSE_RELEASE_VERSION: &str = "1.1.0";

/// Number of source systems in the `SourceSystem` enum. Must match the
/// standalone binary.
const SOURCE_SYSTEM_COUNT: u32 = 68;

/// Static fallback for "library not loaded" table output.
const FALLBACK_DECLARATIONS: usize = 3_254_463;
const FALLBACK_SHARDS: usize = 107;

pub(crate) fn cmd_version(args: VersionArgs) -> Result<(), MathverseCliError> {
    let stdout = io::stdout();
    let mut out = stdout.lock();
    let lib = load_library_opt(&args.shard_dir)?;

    let (shards, decls, by_trust): (usize, usize, BTreeMap<u8, usize>) = if let Some(l) = &lib {
        let count = l.constant_count();
        let mut by_trust: BTreeMap<u8, usize> = BTreeMap::new();
        for idx in 0..count as u32 {
            if let Some(h) = l.get_constant(idx) {
                *by_trust.entry(h.import_confidence).or_default() += 1;
            }
        }
        // We do not have live shard count without reading the release manifest,
        // so fall back to the canonical mathverse-v0.9.0 shard count.
        (FALLBACK_SHARDS, count, by_trust)
    } else {
        (FALLBACK_SHARDS, FALLBACK_DECLARATIONS, BTreeMap::new())
    };

    if args.json {
        let trust_map: serde_json::Map<String, serde_json::Value> = by_trust
            .iter()
            .map(|(id, n)| (confidence_name(*id).to_string(), json!(n)))
            .collect();
        let value = json!({
            "version": MATHVERSE_RELEASE_VERSION,
            "shards": shards,
            "source_systems": SOURCE_SYSTEM_COUNT,
            "declarations": decls,
            "trust_levels": trust_map,
            "library_loaded": lib.is_some(),
        });
        writeln!(out, "{}", serde_json::to_string_pretty(&value)?)?;
    } else {
        writeln!(out, "Mathverse Library v{MATHVERSE_RELEASE_VERSION}")?;
        writeln!(
            out,
            "Shards: {shards}  Systems: {SOURCE_SYSTEM_COUNT}  Declarations: {decls}"
        )?;
        if !by_trust.is_empty() {
            let parts: Vec<String> = by_trust
                .iter()
                .map(|(id, n)| format!("{}={}", confidence_name(*id), n))
                .collect();
            writeln!(out, "Trust: {}", parts.join(", "))?;
        } else if lib.is_none() {
            writeln!(out)?;
            writeln!(
                out,
                "Library not loaded (shard directory `{}` missing).",
                args.shard_dir.display()
            )?;
        }
    }
    Ok(())
}

// -- list ---------------------------------------------------------------------

pub(crate) fn cmd_list(args: ListArgs) -> Result<(), MathverseCliError> {
    let lib = load_library(&args.shard_dir)?;
    let stdout = io::stdout();
    let mut out = stdout.lock();
    let system_filter = args.system.as_deref().and_then(parse_source_system);

    let total = lib.constant_count();
    let mut entries: Vec<(u32, String)> = Vec::new();
    let mut skipped = 0usize;
    for idx in 0..total as u32 {
        let Some(name) = lib.get_name(idx) else {
            continue;
        };
        if let Some(sys) = system_filter {
            if let Some(h) = lib.get_constant(idx) {
                if h.source_system != sys {
                    continue;
                }
            } else {
                continue;
            }
        }
        if skipped < args.offset {
            skipped += 1;
            continue;
        }
        entries.push((idx, name.to_string()));
        if entries.len() >= args.limit {
            break;
        }
    }

    if args.json {
        let rows: Vec<_> = entries
            .iter()
            .filter_map(|(idx, name)| {
                lib.get_constant(*idx).map(|h| {
                    json!({
                        "idx": idx,
                        "name": name,
                        "source_system": source_system_name(h.source_system),
                        "trust": confidence_name(h.import_confidence),
                    })
                })
            })
            .collect();
        writeln!(out, "{}", serde_json::to_string_pretty(&rows)?)?;
    } else if entries.is_empty() {
        writeln!(out, "No entries.")?;
    } else {
        writeln!(
            out,
            "{:<8} {:<50} {:<15} {:<16}",
            "IDX", "NAME", "SYSTEM", "TRUST"
        )?;
        writeln!(out, "{}", "-".repeat(93))?;
        for (idx, name) in &entries {
            if let Some(h) = lib.get_constant(*idx) {
                writeln!(
                    out,
                    "{:<8} {:<50} {:<15} {:<16}",
                    idx,
                    truncate(name, 50),
                    source_system_name(h.source_system),
                    confidence_name(h.import_confidence),
                )?;
            }
        }
        writeln!(out, "\nShowing {} of {} total", entries.len(), total)?;
    }
    Ok(())
}

// -- sample -------------------------------------------------------------------

pub(crate) fn cmd_sample(args: SampleArgs) -> Result<(), MathverseCliError> {
    let lib = load_library(&args.shard_dir)?;
    let stdout = io::stdout();
    let mut out = stdout.lock();
    let system_filter = args.system.as_deref().and_then(parse_source_system);
    let trust_filter = args.trust.as_deref().and_then(parse_trust_level);

    let sample = collect_sample(&lib, args.n, args.seed, system_filter, trust_filter);

    if args.json {
        let rows: Vec<_> = sample
            .iter()
            .filter_map(|&idx| {
                let h = lib.get_constant(idx)?;
                let name = lib.get_name(idx)?;
                Some(json!({
                    "idx": idx,
                    "name": name,
                    "source_system": source_system_name(h.source_system),
                    "trust": confidence_name(h.import_confidence),
                    "domain": domain_name(h.content_domain),
                }))
            })
            .collect();
        writeln!(out, "{}", serde_json::to_string_pretty(&rows)?)?;
    } else if sample.is_empty() {
        writeln!(out, "No declarations match the requested filters.")?;
    } else {
        writeln!(
            out,
            "{:<8} {:<50} {:<15} {:<16} {:<14}",
            "IDX", "NAME", "SYSTEM", "TRUST", "DOMAIN"
        )?;
        writeln!(out, "{}", "-".repeat(105))?;
        for &idx in &sample {
            let Some(name) = lib.get_name(idx) else {
                continue;
            };
            let Some(h) = lib.get_constant(idx) else {
                continue;
            };
            writeln!(
                out,
                "{:<8} {:<50} {:<15} {:<16} {:<14}",
                idx,
                truncate(name, 50),
                source_system_name(h.source_system),
                confidence_name(h.import_confidence),
                domain_name(h.content_domain),
            )?;
        }
        writeln!(out, "\n{} sampled declaration(s)", sample.len())?;
    }
    Ok(())
}

fn collect_sample(
    lib: &MathverseLibrary,
    n: usize,
    seed: u64,
    system_filter: Option<u8>,
    trust_filter: Option<u8>,
) -> Vec<ConstantIdx> {
    let total = lib.constant_count();
    if total == 0 || n == 0 {
        return Vec::new();
    }

    // First pass: enumerate matching indices.
    let mut matching: Vec<ConstantIdx> = Vec::new();
    for idx in 0..total as u32 {
        if matches_filters(lib, idx, system_filter, trust_filter) {
            matching.push(idx);
        }
    }
    if matching.is_empty() {
        return Vec::new();
    }

    // Deterministic LCG walk across matching indices.
    let mut seed = seed.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut out = Vec::with_capacity(n);
    let mut seen: HashSet<ConstantIdx> = HashSet::with_capacity(n);
    let mut attempts = 0usize;
    let max_attempts = n.saturating_mul(10).max(matching.len());
    while out.len() < n && attempts < max_attempts {
        attempts += 1;
        seed = seed
            .wrapping_mul(0x5851_F42D_4C95_7F2D)
            .wrapping_add(0x1405_7B7E_F767_814F);
        let pos = (seed % matching.len() as u64) as usize;
        let pick = matching[pos];
        if seen.insert(pick) {
            out.push(pick);
        }
    }
    out
}

fn matches_filters(
    lib: &MathverseLibrary,
    idx: ConstantIdx,
    system_filter: Option<u8>,
    trust_filter: Option<u8>,
) -> bool {
    let Some(h) = lib.get_constant(idx) else {
        return false;
    };
    if let Some(s) = system_filter {
        if h.source_system != s {
            return false;
        }
    }
    if let Some(t) = trust_filter {
        if h.import_confidence != t {
            return false;
        }
    }
    true
}

// -- deps ---------------------------------------------------------------------

pub(crate) fn cmd_deps(args: DepsArgs) -> Result<(), MathverseCliError> {
    let mut lib = load_library(&args.shard_dir)?;
    // `deps()` is empty until `build_deps()` runs; the standalone binary
    // calls it implicitly via `load_built_library`. Build here so the
    // dispatch path does not rely on caller ordering.
    lib.build_deps();

    let stdout = io::stdout();
    let mut out = stdout.lock();
    // Tolerant resolution: exact name, else case-insensitive / substring match,
    // so a `search`/`find` hit can be piped straight in. Report any non-exact
    // resolution on stderr so the chosen target is never silent.
    let root_idx = lib
        .resolve_name_loose(&args.name)
        .ok_or_else(|| MathverseCliError::DeclarationNotFound(args.name.clone()))?;
    let resolved_name = lib.get_name(root_idx).unwrap_or(&args.name).to_string();
    if resolved_name != args.name {
        eprintln!(
            "note: '{}' not found exactly; using '{resolved_name}'",
            args.name
        );
    }

    let depth = if args.transitive && args.depth <= 1 {
        usize::MAX
    } else {
        args.depth
    };
    let transitive = args.transitive || args.depth > 1;

    let dep_list = if args.reverse {
        lib.reverse_deps_bounded(root_idx, transitive, depth, args.limit)
    } else {
        collect_deps(&lib, root_idx, transitive, depth, args.limit)
    };

    if args.json {
        let rows: Vec<_> = dep_list
            .iter()
            .map(|&(idx, d)| {
                let mut row = json!({
                    "idx": idx,
                    "depth": d,
                    "name": lib.get_name(idx).unwrap_or("?"),
                    "source_system": lib
                        .get_constant(idx)
                        .map(|h| source_system_name(h.source_system))
                        .unwrap_or("?"),
                });
                if args.reverse {
                    // Impact metric: how many declarations use this dependent.
                    row["used_by_count"] = json!(lib.reverse_in_degree(idx));
                }
                row
            })
            .collect();
        let mut obj = json!({
            "root": resolved_name,
            "direction": if args.reverse { "reverse" } else { "forward" },
            "count": dep_list.len(),
        });
        let key = if args.reverse {
            "dependents"
        } else {
            "dependencies"
        };
        obj[key] = json!(rows);
        writeln!(out, "{}", serde_json::to_string_pretty(&obj)?)?;
    } else if dep_list.is_empty() {
        if args.reverse {
            writeln!(
                out,
                "Nothing in the loaded corpus depends on {resolved_name}."
            )?;
        } else {
            writeln!(out, "{resolved_name} has no recorded dependencies.")?;
        }
    } else if args.reverse {
        writeln!(out, "Reverse dependencies (users) of {resolved_name}:")?;
        writeln!(
            out,
            "{:<8} {:<6} {:<8} {:<50} {:<15}",
            "IDX", "DEPTH", "USED-BY", "NAME", "SYSTEM"
        )?;
        writeln!(out, "{}", "-".repeat(92))?;
        for &(idx, d) in &dep_list {
            let name = lib.get_name(idx).unwrap_or("?");
            let sys = lib
                .get_constant(idx)
                .map(|h| source_system_name(h.source_system))
                .unwrap_or("?");
            writeln!(
                out,
                "{:<8} {:<6} {:<8} {:<50} {:<15}",
                idx,
                d,
                lib.reverse_in_degree(idx),
                truncate(name, 50),
                sys
            )?;
        }
        writeln!(out, "\n{} dependents (ranked by impact)", dep_list.len())?;
    } else {
        writeln!(out, "Dependencies of {resolved_name}:")?;
        writeln!(
            out,
            "{:<8} {:<6} {:<50} {:<15}",
            "IDX", "DEPTH", "NAME", "SYSTEM"
        )?;
        writeln!(out, "{}", "-".repeat(83))?;
        for &(idx, d) in &dep_list {
            let name = lib.get_name(idx).unwrap_or("?");
            let sys = lib
                .get_constant(idx)
                .map(|h| source_system_name(h.source_system))
                .unwrap_or("?");
            writeln!(
                out,
                "{:<8} {:<6} {:<50} {:<15}",
                idx,
                d,
                truncate(name, 50),
                sys
            )?;
        }
        writeln!(out, "\n{} dependencies", dep_list.len())?;
    }
    Ok(())
}

fn collect_deps(
    lib: &MathverseLibrary,
    root: ConstantIdx,
    transitive: bool,
    depth: usize,
    limit: usize,
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

    while let Some((idx, cur_depth)) = queue.pop_front() {
        if !visited.insert(idx) {
            continue;
        }
        out.push((idx, cur_depth));
        if out.len() >= limit {
            break;
        }
        if !transitive {
            continue;
        }
        if cur_depth as usize >= depth {
            continue;
        }
        if let Some(next) = adj.get(idx as usize) {
            for &n in next {
                if !visited.contains(&n) {
                    queue.push_back((n, cur_depth + 1));
                }
            }
        }
    }

    out
}

// -- tests --------------------------------------------------------------------
//
// Test body lives in the sibling file so browse_dispatch.rs itself stays
// under the 500-line new-file cap. The `#[path]` attribute pulls the file
// in as an inline submodule, preserving access to this module's private
// helpers (`collect_sample`, `collect_deps`, etc.).
#[cfg(test)]
#[path = "browse_dispatch_tests.rs"]
mod tests;
