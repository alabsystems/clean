// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Command dispatch helpers for `clean mathverse <verb>`.
//!
//! Each `cmd_*` function takes its parsed args, loads the shard directory,
//! invokes the library layer (`MathverseLibrary`, `MathverseSearch`), and writes
//! either the human-readable table or the JSON representation expected by
//! downstream scripts. Behaviour intentionally mirrors the deprecated
//! `mathverse_search` binary 1:1 so the compat shim path stays indistinguishable.

use std::collections::BTreeMap;
use std::io::{self, Write};
use std::path::Path;
use std::time::Instant;

use serde_json::json;

use crate::cli::format::{
    confidence_name, decl_kind_name, domain_name, source_system_name, truncate,
};
use crate::cli::{InfoArgs, MathverseCliError, SearchArgs, SearchMode, StatsArgs, SystemsArgs};
use crate::library::MathverseLibrary;
use crate::shard::ShardReader;
use crate::trust::policy::TrustPolicy;
use crate::types::MathverseConstantHeader;

// -- shared: library loading --------------------------------------------------

/// Load every `*.mathverse` shard in `shard_dir` into a permissive
/// [`MathverseLibrary`].
///
/// Returns a descriptive [`MathverseCliError`] if the directory is missing so
/// callers can surface the canonical "download the library" hint. Shard
/// read/load failures are emitted as warnings to stderr (matching
/// `mathverse_search`'s behaviour) and skipped, so a single corrupt shard does
/// not sink the whole session.
fn load_library(shard_dir: &Path) -> Result<MathverseLibrary, MathverseCliError> {
    if !shard_dir.exists() {
        return Err(MathverseCliError::ShardDirMissing(shard_dir.to_path_buf()));
    }

    let t0 = Instant::now();
    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    let mut shard_count = 0u32;
    let mut load_errors = 0u32;

    let read_dir = std::fs::read_dir(shard_dir).map_err(|e| MathverseCliError::ShardDirIo {
        path: shard_dir.to_path_buf(),
        source: e,
    })?;

    let mut entries: Vec<_> = read_dir
        .filter_map(|e| e.ok())
        .filter(|e| e.path().extension().is_some_and(|ext| ext == "mathverse"))
        .collect();
    entries.sort_by_key(|e| e.file_name());

    for entry in &entries {
        let path = entry.path();
        match ShardReader::from_file(&path) {
            Ok(reader) => match lib.load_shard(&reader) {
                Ok(_) => shard_count += 1,
                Err(e) => {
                    eprintln!("Warning: failed to load shard {}: {e}", path.display());
                    load_errors += 1;
                }
            },
            Err(e) => {
                eprintln!("Warning: failed to read shard {}: {e}", path.display());
                load_errors += 1;
            }
        }
    }

    let elapsed = t0.elapsed();
    eprintln!(
        "Loaded {shard_count} shards ({} declarations) in {:.2}s{}",
        lib.constant_count(),
        elapsed.as_secs_f64(),
        if load_errors > 0 {
            format!(" ({load_errors} errors)")
        } else {
            String::new()
        }
    );

    Ok(lib)
}

// -- search -------------------------------------------------------------------

pub(crate) fn cmd_search(args: SearchArgs) -> Result<(), MathverseCliError> {
    let lib = load_library(&args.shard_dir)?;
    let stdout = io::stdout();
    let mut out = stdout.lock();

    // `--like` always means a type-directed (discrimination-tree) query: it
    // names a reference declaration whose type we match by, regardless of
    // `--mode`.
    if let Some(like) = args.like.as_deref() {
        return search_by_type(&lib, like, args.limit, args.json, &mut out);
    }

    match args.mode {
        SearchMode::Name => {
            let pattern = require_pattern(&args, "name")?;
            search_by_name(&lib, pattern, args.limit, args.json, &mut out)
        }
        SearchMode::Type => {
            // In type mode without `--like`, the positional pattern names the
            // reference declaration whose type we search by.
            let anchor = require_pattern(&args, "type")?;
            search_by_type(&lib, anchor, args.limit, args.json, &mut out)
        }
        SearchMode::Structural => {
            // The positional pattern names the reference declaration whose
            // statement we search for structural equivalents of.
            let anchor = require_pattern(&args, "structural")?;
            search_by_structural(
                &lib,
                anchor,
                args.index.as_deref(),
                args.limit,
                args.json,
                &mut out,
            )
        }
        SearchMode::Semantic => {
            let pattern = require_pattern(&args, "semantic")?;
            search_by_semantic(&lib, pattern, args.limit, args.json, &mut out)
        }
    }
}

/// Return the positional query pattern, or a typed "missing query" error naming
/// the mode that needs it.
fn require_pattern<'a>(
    args: &'a SearchArgs,
    mode: &'static str,
) -> Result<&'a str, MathverseCliError> {
    args.pattern
        .as_deref()
        .ok_or(MathverseCliError::SearchMissingQuery(mode))
}

fn search_by_name(
    lib: &MathverseLibrary,
    pattern: &str,
    limit: usize,
    json: bool,
    out: &mut impl Write,
) -> Result<(), MathverseCliError> {
    let t0 = Instant::now();
    let needle = pattern.to_lowercase();

    // Collect EVERY substring match over the whole name table, then rank, then
    // truncate. Ranking over all matches (rather than the first `limit*2` in
    // corpus-index order) guarantees an exact/canonical hit — e.g. the canonical
    // `add_comm` — is never dropped just because it sits past the window. This is
    // an O(N) scan of the name table, which is acceptable: a rare needle already
    // scanned the whole corpus before the old early-break ever fired.
    let mut results: Vec<(u32, String)> = Vec::new();
    for idx in 0..lib.constant_count() as u32 {
        if let Some(name) = lib.get_name(idx) {
            if name.to_lowercase().contains(&needle) {
                results.push((idx, name.to_string()));
            }
        }
    }
    rank_name_results(lib, &mut results, &needle);
    results.truncate(limit);

    let elapsed = t0.elapsed();
    if json {
        write_json_results(out, lib, &results, elapsed.as_secs_f64())
    } else {
        writeln!(
            out,
            "Name search for '{}' ({} results, {:.3}ms):\n",
            pattern,
            results.len(),
            elapsed.as_secs_f64() * 1000.0
        )?;
        write_table_results(out, lib, &results)
    }
}

/// Rank name-search hits so the most canonical match floats to the top:
/// exact (case-insensitive) > prefix > shorter name > higher import-confidence >
/// name ascending (final, stable tiebreak). `needle` is already lowercased.
fn rank_name_results(lib: &MathverseLibrary, results: &mut [(u32, String)], needle: &str) {
    results.sort_by(|a, b| {
        let a_l = a.1.to_lowercase();
        let b_l = b.1.to_lowercase();
        let a_exact = a_l == needle;
        let b_exact = b_l == needle;
        if a_exact != b_exact {
            return b_exact.cmp(&a_exact);
        }
        let a_prefix = a_l.starts_with(needle);
        let b_prefix = b_l.starts_with(needle);
        if a_prefix != b_prefix {
            return b_prefix.cmp(&a_prefix);
        }
        match a.1.len().cmp(&b.1.len()) {
            std::cmp::Ordering::Equal => {}
            ord => return ord,
        }
        // Higher import-confidence wins the tie, then name ascending so the order
        // is fully deterministic across runs.
        let conf = |idx: u32| lib.get_constant(idx).map_or(0, |h| h.import_confidence);
        conf(b.0).cmp(&conf(a.0)).then_with(|| a.1.cmp(&b.1))
    });
}

/// Type-directed search through the discrimination tree.
///
/// `like_name` names a reference declaration. We resolve it to its global
/// index, take that declaration's already-interned type `ExprIdx`, and query
/// the discrimination tree (`MathverseSearch::search_type`) for every loaded
/// declaration whose type structurally matches/unifies with it. This is the
/// real type-directed retrieval path — it surfaces same-*shaped* theorems even
/// when their names share nothing with the anchor, which neither the name
/// substring nor the BM25 lexical mode can do.
///
/// No parser/elaborator is involved: the query type is reused verbatim from the
/// interned arena, so the `Const` name indices in the query path are exactly
/// those the discrimination tree stored at load.
fn search_by_type(
    lib: &MathverseLibrary,
    like_name: &str,
    limit: usize,
    json: bool,
    out: &mut impl Write,
) -> Result<(), MathverseCliError> {
    use crate::search::MathverseSearch;

    let t0 = Instant::now();

    // Resolve the reference declaration (exact, then loose) to its index + type.
    let anchor_idx = lib
        .lookup_constant_idx(like_name)
        .or_else(|| lib.resolve_name_loose(like_name))
        .ok_or_else(|| MathverseCliError::DeclarationNotFound(like_name.to_string()))?;
    let type_idx = lib
        .get_constant(anchor_idx)
        .ok_or_else(|| MathverseCliError::DeclarationNotFound(like_name.to_string()))?
        .type_idx;
    let anchor_name = lib.get_name(anchor_idx).unwrap_or(like_name).to_string();

    // Query the discrimination tree over a generous candidate pool so the
    // ranking below has room to work, then drop the anchor itself.
    let pool = limit.saturating_mul(8).max(128);
    let mut hits = lib
        .search_type(type_idx, pool)
        .map_err(|e| MathverseCliError::SearchFailed(e.to_string()))?;

    // Rank deterministically: structural match score desc, then higher import
    // confidence, then name ascending (stable across runs).
    hits.sort_by(|a, b| {
        b.score
            .partial_cmp(&a.score)
            .unwrap_or(std::cmp::Ordering::Equal)
            .then(b.header.import_confidence.cmp(&a.header.import_confidence))
            .then_with(|| {
                lib.get_name(a.constant_idx)
                    .unwrap_or("")
                    .cmp(lib.get_name(b.constant_idx).unwrap_or(""))
            })
    });

    let results: Vec<(u32, String)> = hits
        .into_iter()
        .filter(|sr| sr.constant_idx != anchor_idx)
        .filter_map(|sr| {
            lib.get_name(sr.constant_idx)
                .map(|name| (sr.constant_idx, name.to_string()))
        })
        .take(limit)
        .collect();

    let elapsed = t0.elapsed();
    if json {
        write_json_results(out, lib, &results, elapsed.as_secs_f64())
    } else {
        writeln!(
            out,
            "Type-directed search (discrimination tree) for declarations \
             matching the type of `{}` ({} results, {:.3}ms):\n",
            anchor_name,
            results.len(),
            elapsed.as_secs_f64() * 1000.0
        )?;
        write_table_results(out, lib, &results)
    }
}

/// Structural-equivalence search (`--mode structural`).
///
/// `anchor_name` names a reference declaration. We reconstruct its type, compute
/// the environment-free Tier-1.5 *rewrite-canonical* digest
/// ([`MathverseLibrary::structural_rewrite_digest_of`]) — the corpus-scale "same
/// object, different form" key the graduation novelty gate stores in `.mvix` —
/// and answer the "is this theorem already proven, differently stated?" query:
///
/// * With `--index <baseline.mvix>`: the digest is looked up in the index's
///   semantic table for the corpus-wide canonical representative in microseconds,
///   without rescanning the corpus. This is the dedup / premise-selection probe.
/// * Without `--index`: the full structural-equivalence class *within the loaded
///   shards* is scanned ([`MathverseLibrary::structural_equivalents_of`]).
///
/// A hit is a candidate match (equal up to commutative-operand rewrite), never a
/// soundness claim — `same_object` remains the arbiter for a confirmed identity.
fn search_by_structural(
    lib: &MathverseLibrary,
    anchor_name: &str,
    index_path: Option<&Path>,
    limit: usize,
    json: bool,
    out: &mut impl Write,
) -> Result<(), MathverseCliError> {
    let t0 = Instant::now();

    let anchor_idx = lib
        .lookup_constant_idx(anchor_name)
        .or_else(|| lib.resolve_name_loose(anchor_name))
        .ok_or_else(|| MathverseCliError::DeclarationNotFound(anchor_name.to_string()))?;
    let anchor_display = lib.get_name(anchor_idx).unwrap_or(anchor_name).to_string();
    let digest = lib
        .structural_rewrite_digest_of(anchor_idx)
        .ok_or_else(|| {
            MathverseCliError::SearchFailed(format!(
                "could not reconstruct the type of `{anchor_display}` (name-only / \
             unsupported expr) — no structural digest to search by"
            ))
        })?;

    // With an index: microsecond corpus-wide representative lookup. Without:
    // exhaustive scan of the loaded shards for the full equivalence class.
    let (representative, results): (Option<String>, Vec<(u32, String)>) = match index_path {
        Some(path) => {
            let index = crate::graduate::BaselineIndex::load(path)?;
            let rep = index.lookup_semantic(&digest).map(str::to_string);
            (rep, Vec::new())
        }
        None => {
            let hits = lib.structural_equivalents_of(anchor_idx, limit);
            let rows = hits
                .into_iter()
                .filter_map(|idx| lib.get_name(idx).map(|name| (idx, name.to_string())))
                .collect();
            (None, rows)
        }
    };

    let elapsed = t0.elapsed();
    if json {
        let rows: Vec<_> = results
            .iter()
            .filter_map(|(idx, name)| {
                lib.get_constant(*idx).map(|header| {
                    json!({
                        "index": idx,
                        "name": name,
                        "source_system": source_system_name(header.source_system),
                        "confidence": confidence_name(header.import_confidence),
                        "domain": domain_name(header.content_domain),
                        "kind": decl_kind_name(header.decl_kind),
                    })
                })
            })
            .collect();
        let value = json!({
            "anchor": anchor_display,
            "rewrite_canonical_digest": digest,
            "baseline_representative": representative,
            "count": results.len(),
            "elapsed_ms": elapsed.as_secs_f64() * 1000.0,
            "results": rows,
            "note": "Structural equivalence is equality up to commutative-operand \
                     rewrite (a candidate match, not a kernel identity). \
                     `baseline_representative` is the corpus-wide canonical name \
                     from the .mvix semantic table; `results` is the full \
                     equivalence class within the loaded shards.",
        });
        writeln!(out, "{}", serde_json::to_string_pretty(&value)?)?;
        return Ok(());
    }

    writeln!(
        out,
        "Structural-equivalence search for declarations equal-up-to-rewrite to \
         `{}` ({:.3}ms):",
        anchor_display,
        elapsed.as_secs_f64() * 1000.0
    )?;
    writeln!(out, "  rewrite-canonical digest: {digest}\n")?;
    if let Some(path) = index_path {
        match &representative {
            Some(rep) => writeln!(
                out,
                "  Already present in the baseline corpus ({}) as: {rep}",
                path.display()
            )?,
            None => writeln!(
                out,
                "  No structural equivalent found in the baseline corpus ({}).",
                path.display()
            )?,
        }
    }
    if index_path.is_none() {
        writeln!(
            out,
            "  Equivalence class within the loaded shards ({} results):\n",
            results.len()
        )?;
        write_table_results(out, lib, &results)?;
    }
    Ok(())
}

/// BM25 lexical search over declaration names and types (`--mode semantic`).
///
/// This is the former `--mode type` behaviour, restored to its honest label:
/// it is a lexical, not structural, query.
fn search_by_semantic(
    lib: &MathverseLibrary,
    pattern: &str,
    limit: usize,
    json: bool,
    out: &mut impl Write,
) -> Result<(), MathverseCliError> {
    use crate::search::MathverseSearch;

    let t0 = Instant::now();
    let search_results = lib
        .search_semantic(pattern, limit)
        .map_err(|e| MathverseCliError::SearchFailed(e.to_string()))?;

    let results: Vec<(u32, String)> = search_results
        .iter()
        .filter_map(|sr| {
            lib.get_name(sr.constant_idx)
                .map(|name| (sr.constant_idx, name.to_string()))
        })
        .collect();

    let elapsed = t0.elapsed();
    if json {
        write_json_results(out, lib, &results, elapsed.as_secs_f64())
    } else {
        writeln!(
            out,
            "Semantic (BM25) search for '{}' ({} results, {:.3}ms):\n",
            pattern,
            results.len(),
            elapsed.as_secs_f64() * 1000.0
        )?;
        write_table_results(out, lib, &results)
    }
}

// -- info ---------------------------------------------------------------------

pub(crate) fn cmd_info(args: InfoArgs) -> Result<(), MathverseCliError> {
    use crate::search::MathverseSearch;

    let lib = load_library(&args.shard_dir)?;
    let stdout = io::stdout();
    let mut out = stdout.lock();
    let header = lib
        .lookup_name(&args.name)
        .ok_or_else(|| MathverseCliError::DeclarationNotFound(args.name.clone()))?;

    if args.json {
        write_json_info(&mut out, &args.name, &header)
    } else {
        write_table_info(&mut out, &args.name, &header)
    }
}

// -- stats --------------------------------------------------------------------

pub(crate) fn cmd_stats(args: StatsArgs) -> Result<(), MathverseCliError> {
    let lib = load_library(&args.shard_dir)?;
    let stdout = io::stdout();
    let mut out = stdout.lock();
    let snapshot = collect_stats(&lib);

    if args.json {
        let value = json!({
            "total_declarations": snapshot.total,
            "with_proof_terms": snapshot.has_value_count,
            "axiomatized": snapshot.total - snapshot.has_value_count,
            "pure": snapshot.pure_count,
            "trust_gated": snapshot.trust_gated,
            "by_source": label_map(&snapshot.by_source, source_system_name),
            "by_confidence": label_map(&snapshot.by_confidence, confidence_name),
            "by_domain": label_map(&snapshot.by_domain, domain_name),
            "by_kind": label_map(&snapshot.by_kind, decl_kind_name),
        });
        writeln!(out, "{}", serde_json::to_string_pretty(&value)?)?;
    } else {
        write_table_stats(&mut out, &snapshot)?;
    }
    Ok(())
}

struct StatsSnapshot {
    total: usize,
    by_source: BTreeMap<u8, usize>,
    by_confidence: BTreeMap<u8, usize>,
    by_domain: BTreeMap<u8, usize>,
    by_kind: BTreeMap<u8, usize>,
    trust_gated: usize,
    pure_count: usize,
    has_value_count: usize,
}

fn collect_stats(lib: &MathverseLibrary) -> StatsSnapshot {
    let mut snap = StatsSnapshot {
        total: lib.constant_count(),
        by_source: BTreeMap::new(),
        by_confidence: BTreeMap::new(),
        by_domain: BTreeMap::new(),
        by_kind: BTreeMap::new(),
        trust_gated: 0,
        pure_count: 0,
        has_value_count: 0,
    };
    for idx in 0..snap.total as u32 {
        if let Some(header) = lib.get_constant(idx) {
            *snap.by_source.entry(header.source_system).or_insert(0) += 1;
            *snap
                .by_confidence
                .entry(header.import_confidence)
                .or_insert(0) += 1;
            *snap.by_domain.entry(header.content_domain).or_insert(0) += 1;
            *snap.by_kind.entry(header.decl_kind).or_insert(0) += 1;
            if header.is_trust_gated() {
                snap.trust_gated += 1;
            }
            if header.axiom_profile.is_pure() {
                snap.pure_count += 1;
            }
            if header.has_value() {
                snap.has_value_count += 1;
            }
        }
    }
    snap
}

fn label_map(
    map: &BTreeMap<u8, usize>,
    label: fn(u8) -> &'static str,
) -> serde_json::Map<String, serde_json::Value> {
    let mut out = serde_json::Map::new();
    for (k, v) in map {
        out.insert(label(*k).to_string(), json!(v));
    }
    out
}

fn write_table_stats(out: &mut impl Write, snap: &StatsSnapshot) -> Result<(), MathverseCliError> {
    writeln!(out, "=== Mathverse Library Statistics ===\n")?;
    writeln!(out, "Total declarations: {}", snap.total)?;
    writeln!(out, "  With proof terms:  {}", snap.has_value_count)?;
    writeln!(
        out,
        "  Axiomatized:       {}",
        snap.total - snap.has_value_count
    )?;
    writeln!(out, "  Pure (no axioms):  {}", snap.pure_count)?;
    writeln!(out, "  Trust-gated:       {}", snap.trust_gated)?;
    writeln!(out)?;
    write_stats_section(
        out,
        "--- By Source System ---",
        &snap.by_source,
        source_system_name,
        true,
    )?;
    write_stats_section(
        out,
        "--- By Confidence ---",
        &snap.by_confidence,
        confidence_name,
        false,
    )?;
    write_stats_section(out, "--- By Domain ---", &snap.by_domain, domain_name, true)?;
    write_stats_section(
        out,
        "--- By Declaration Kind ---",
        &snap.by_kind,
        decl_kind_name,
        true,
    )?;
    Ok(())
}

fn write_stats_section(
    out: &mut impl Write,
    header: &str,
    data: &BTreeMap<u8, usize>,
    label: fn(u8) -> &'static str,
    by_count_desc: bool,
) -> Result<(), MathverseCliError> {
    writeln!(out, "{header}")?;
    let mut entries: Vec<_> = data.iter().collect();
    if by_count_desc {
        entries.sort_by(|a, b| b.1.cmp(a.1));
    } else {
        entries.sort_by(|a, b| a.0.cmp(b.0));
    }
    for (k, count) in &entries {
        writeln!(out, "  {:20} {:>10}", label(**k), count)?;
    }
    writeln!(out)?;
    Ok(())
}

// -- systems ------------------------------------------------------------------

pub(crate) fn cmd_systems(args: SystemsArgs) -> Result<(), MathverseCliError> {
    let lib = load_library(&args.shard_dir)?;
    let stdout = io::stdout();
    let mut out = stdout.lock();
    let total = lib.constant_count();
    let mut by_source: BTreeMap<u8, usize> = BTreeMap::new();
    for idx in 0..total as u32 {
        if let Some(header) = lib.get_constant(idx) {
            *by_source.entry(header.source_system).or_insert(0) += 1;
        }
    }
    let mut entries: Vec<_> = by_source.iter().collect();
    entries.sort_by(|a, b| b.1.cmp(a.1));

    if args.json {
        let systems: Vec<_> = entries
            .iter()
            .map(|(sys, count)| {
                json!({
                    "id": **sys,
                    "name": source_system_name(**sys),
                    "count": **count,
                })
            })
            .collect();
        let value = json!({
            "total_declarations": total,
            "source_system_count": entries.len(),
            "systems": systems,
        });
        writeln!(out, "{}", serde_json::to_string_pretty(&value)?)?;
    } else {
        writeln!(
            out,
            "=== Source Systems ({} systems, {} total declarations) ===\n",
            entries.len(),
            total
        )?;
        writeln!(
            out,
            "  {:4}  {:24} {:>10}  {:>6}",
            "ID", "System", "Count", "%"
        )?;
        writeln!(out, "  {}", "-".repeat(50))?;
        for (sys, count) in &entries {
            let pct = if total > 0 {
                (**count as f64 / total as f64) * 100.0
            } else {
                0.0
            };
            writeln!(
                out,
                "  {:4}  {:24} {:>10}  {:>5.1}%",
                sys,
                source_system_name(**sys),
                count,
                pct
            )?;
        }
    }
    Ok(())
}

// -- shared writers -----------------------------------------------------------

fn write_table_results(
    out: &mut impl Write,
    lib: &MathverseLibrary,
    results: &[(u32, String)],
) -> Result<(), MathverseCliError> {
    if results.is_empty() {
        writeln!(out, "  (no results)")?;
        return Ok(());
    }
    writeln!(
        out,
        "  {:50} {:16} {:16} {:12}",
        "Name", "Source", "Confidence", "Kind"
    )?;
    writeln!(out, "  {}", "-".repeat(96))?;
    for (idx, name) in results {
        if let Some(header) = lib.get_constant(*idx) {
            writeln!(
                out,
                "  {:50} {:16} {:16} {:12}",
                truncate(name, 50),
                source_system_name(header.source_system),
                confidence_name(header.import_confidence),
                decl_kind_name(header.decl_kind),
            )?;
        }
    }
    Ok(())
}

fn write_json_results(
    out: &mut impl Write,
    lib: &MathverseLibrary,
    results: &[(u32, String)],
    elapsed_secs: f64,
) -> Result<(), MathverseCliError> {
    let rows: Vec<_> = results
        .iter()
        .filter_map(|(idx, name)| {
            lib.get_constant(*idx).map(|header| {
                json!({
                    "index": idx,
                    "name": name,
                    "source_system": source_system_name(header.source_system),
                    "confidence": confidence_name(header.import_confidence),
                    "domain": domain_name(header.content_domain),
                    "kind": decl_kind_name(header.decl_kind),
                    "has_value": header.has_value(),
                    "trust_gated": header.is_trust_gated(),
                    "axiom_count": header.axiom_profile.axiom_count(),
                })
            })
        })
        .collect();
    let value = json!({
        "count": results.len(),
        "elapsed_ms": elapsed_secs * 1000.0,
        "results": rows,
    });
    writeln!(out, "{}", serde_json::to_string_pretty(&value)?)?;
    Ok(())
}

fn write_table_info(
    out: &mut impl Write,
    name: &str,
    header: &MathverseConstantHeader,
) -> Result<(), MathverseCliError> {
    writeln!(out, "=== Declaration: {name} ===\n")?;
    writeln!(
        out,
        "  Source system:   {}",
        source_system_name(header.source_system)
    )?;
    writeln!(
        out,
        "  Confidence:      {}",
        confidence_name(header.import_confidence)
    )?;
    writeln!(
        out,
        "  Domain:          {}",
        domain_name(header.content_domain)
    )?;
    writeln!(
        out,
        "  Kind:            {}",
        decl_kind_name(header.decl_kind)
    )?;
    writeln!(out, "  Has proof:       {}", header.has_value())?;
    writeln!(out, "  Trust-gated:     {}", header.is_trust_gated())?;
    writeln!(out, "  Axiom profile:   0x{:016x}", header.axiom_profile.0)?;
    writeln!(
        out,
        "  Axiom count:     {}",
        header.axiom_profile.axiom_count()
    )?;
    writeln!(out, "  Pure:            {}", header.axiom_profile.is_pure())?;
    writeln!(out, "  Type idx:        {}", header.type_idx)?;
    writeln!(
        out,
        "  Value idx:       {}",
        if header.has_value() {
            header.value_idx.to_string()
        } else {
            "none (axiomatized)".to_string()
        }
    )?;
    writeln!(out, "  Level params:    {}", header.level_params_count)?;
    Ok(())
}

fn write_json_info(
    out: &mut impl Write,
    name: &str,
    header: &MathverseConstantHeader,
) -> Result<(), MathverseCliError> {
    let value = json!({
        "name": name,
        "source_system": source_system_name(header.source_system),
        "confidence": confidence_name(header.import_confidence),
        "domain": domain_name(header.content_domain),
        "kind": decl_kind_name(header.decl_kind),
        "has_value": header.has_value(),
        "trust_gated": header.is_trust_gated(),
        "axiom_profile": format!("0x{:016x}", header.axiom_profile.0),
        "axiom_count": header.axiom_profile.axiom_count(),
        "pure": header.axiom_profile.is_pure(),
        "type_idx": header.type_idx,
        "value_idx": if header.has_value() {
            header.value_idx as i64
        } else {
            -1
        },
        "level_params_count": header.level_params_count,
    });
    writeln!(out, "{}", serde_json::to_string_pretty(&value)?)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::shard::ShardWriter;
    use crate::types::{
        AxiomProfile, ContentDomain, ImportConfidence, MathverseConstantHeader, SourceSystem,
    };
    use clean_kernel::flat::{FlatExpr, FlatLevel};
    use tempfile::tempdir;

    fn build_test_shard(
        names: &[(&str, SourceSystem, ImportConfidence, ContentDomain)],
    ) -> Vec<u8> {
        let mut writer = ShardWriter::new();
        let l0 = writer.add_level(FlatLevel::zero());
        let e0 = writer.add_expr(FlatExpr::sort(l0));
        for &(name, source, confidence, domain) in names {
            let ni = writer.add_string(name);
            writer.add_constant(MathverseConstantHeader {
                name_idx: ni,
                type_idx: e0,
                value_idx: e0,
                source_system: source as u8,
                import_confidence: confidence as u8,
                content_domain: domain as u8,
                decl_kind: 0,
                axiom_profile: AxiomProfile::NONE,
                sidecar_digest: 0,
                provenance_idx: 0,
                level_params_start: 0,
                level_params_count: 0,
                _pad2: [0u8; 26],
            });
        }
        let mut buf = Vec::new();
        writer.write(&mut buf).expect("shard write");
        buf
    }

    fn make_shard_dir_with_decls() -> tempfile::TempDir {
        let dir = tempdir().expect("tempdir");
        let shard_bytes = build_test_shard(&[
            (
                "Nat.add",
                SourceSystem::Lean4,
                ImportConfidence::KernelVerified,
                ContentDomain::PureMath,
            ),
            (
                "Nat.add_comm",
                SourceSystem::Lean4,
                ImportConfidence::KernelVerified,
                ContentDomain::PureMath,
            ),
            (
                "Bool.true",
                SourceSystem::Lean4,
                ImportConfidence::KernelVerified,
                ContentDomain::Logic,
            ),
        ]);
        std::fs::write(dir.path().join("test.mathverse"), &shard_bytes).expect("write");
        dir
    }

    #[test]
    fn test_load_library_missing_dir_is_typed_error() {
        match load_library(Path::new("/nonexistent/shard/path")) {
            Err(MathverseCliError::ShardDirMissing(_)) => {}
            Err(other) => panic!("expected ShardDirMissing, got {other:?}"),
            Ok(_) => panic!("expected failure on missing shard directory"),
        }
    }

    #[test]
    fn test_search_name_mode_runs_and_ranks() {
        let dir = make_shard_dir_with_decls();
        let args = SearchArgs {
            pattern: Some("nat.add".into()),
            mode: SearchMode::Name,
            like: None,
            index: None,
            shard_dir: dir.path().to_path_buf(),
            limit: 10,
            json: false,
        };
        cmd_search(args).expect("search");
    }

    #[test]
    fn test_search_by_name_exact_match_never_dropped_outside_window() {
        // Regression: the name search used to collect only the first `limit*2`
        // substring matches in corpus-INDEX order, then rank within that window —
        // so an exact/canonical match sitting past the window was silently
        // dropped. Here 40 `add_comm_group_*` decls precede the exact `add_comm`,
        // and with `limit = 5` the old window (10 matches) stopped long before
        // reaching it. Ranking over ALL matches must surface `add_comm` first.
        let mut names: Vec<String> = (0..40).map(|i| format!("add_comm_group_{i}")).collect();
        names.push("add_comm".to_string());
        names.push("padd_comm".to_string());

        let decls: Vec<_> = names
            .iter()
            .map(|n| {
                (
                    n.as_str(),
                    SourceSystem::Lean4,
                    ImportConfidence::KernelVerified,
                    ContentDomain::PureMath,
                )
            })
            .collect();

        let dir = tempdir().expect("tempdir");
        let bytes = build_test_shard(&decls);
        std::fs::write(dir.path().join("window.mathverse"), &bytes).expect("write");
        let lib = load_library(dir.path()).expect("load");

        let mut out: Vec<u8> = Vec::new();
        search_by_name(&lib, "add_comm", 5, true, &mut out).expect("search");

        let v: serde_json::Value = serde_json::from_slice(&out).expect("valid json output");
        let results = v["results"].as_array().expect("results array");
        assert!(!results.is_empty(), "expected at least one result");
        assert_eq!(
            results[0]["name"].as_str(),
            Some("add_comm"),
            "exact/canonical `add_comm` must rank first even though it sits past \
             the first limit*2 corpus-order matches; got {results:?}"
        );
    }

    /// Build a shard whose constants carry *distinct* types so the
    /// discrimination tree actually discriminates: `alpha` and `beta` share the
    /// type `Const("Nat")` (different names), while `gamma : Const("Bool")` has
    /// a different shape. A name search for "alpha" cannot reach `beta`, but a
    /// type-directed `--like alpha` must.
    fn build_typed_shard_dir() -> tempfile::TempDir {
        let dir = tempdir().expect("tempdir");
        let mut writer = ShardWriter::new();
        let nat_name = writer.add_string("Nat");
        let bool_name = writer.add_string("Bool");
        // `u32::MAX` levels-list slot == "no universe args" (handled by remap).
        let nat_ty = writer.add_expr(FlatExpr::const_ref(nat_name, u32::MAX));
        let bool_ty = writer.add_expr(FlatExpr::const_ref(bool_name, u32::MAX));

        let push = |writer: &mut ShardWriter, name: &str, ty: u32| {
            let ni = writer.add_string(name);
            writer.add_constant(MathverseConstantHeader {
                name_idx: ni,
                type_idx: ty,
                value_idx: u32::MAX,
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
            });
        };
        push(&mut writer, "alpha", nat_ty);
        push(&mut writer, "beta", nat_ty);
        push(&mut writer, "gamma", bool_ty);

        let mut buf = Vec::new();
        writer.write(&mut buf).expect("shard write");
        std::fs::write(dir.path().join("typed.mathverse"), &buf).expect("write");
        dir
    }

    #[test]
    fn test_type_mode_finds_same_shaped_decl_a_name_search_misses() {
        use crate::search::MathverseSearch;

        let dir = build_typed_shard_dir();
        let lib = load_library(dir.path()).expect("load");

        // The anchor and its type-peer share no name substring.
        let alpha = lib.lookup_constant_idx("alpha").expect("alpha present");
        let alpha_ty = lib.get_constant(alpha).expect("alpha header").type_idx;

        // Real discrimination-tree query by the anchor's interned type.
        let hits = lib.search_type(alpha_ty, 16).expect("type search");
        let names: Vec<&str> = hits
            .iter()
            .filter_map(|sr| lib.get_name(sr.constant_idx))
            .collect();

        // `beta` shares `alpha`'s type and MUST appear; `gamma` (different type)
        // MUST NOT. A name substring search for "alpha" could never surface
        // "beta", so this is genuinely structural.
        assert!(
            names.contains(&"beta"),
            "type search by alpha's type should find same-shaped `beta`, got {names:?}"
        );
        assert!(
            !names.contains(&"gamma"),
            "type search must NOT return the differently-typed `gamma`, got {names:?}"
        );
    }

    #[test]
    fn test_like_flag_forces_type_search_and_excludes_anchor() {
        let dir = build_typed_shard_dir();
        // `--like` forces type mode even with the default `--mode name`; the
        // command runs end-to-end (the anchor itself is filtered from output).
        let args = SearchArgs {
            pattern: None,
            mode: SearchMode::Name,
            like: Some("alpha".into()),
            index: None,
            shard_dir: dir.path().to_path_buf(),
            limit: 10,
            json: true,
        };
        cmd_search(args).expect("type search via --like");
    }

    #[test]
    fn test_search_missing_query_is_typed_error() {
        let dir = make_shard_dir_with_decls();
        let args = SearchArgs {
            pattern: None,
            mode: SearchMode::Name,
            like: None,
            index: None,
            shard_dir: dir.path().to_path_buf(),
            limit: 10,
            json: false,
        };
        let err = cmd_search(args).expect_err("missing query should fail");
        assert!(matches!(err, MathverseCliError::SearchMissingQuery("name")));
    }

    /// Build a shard whose first two decls have types `@Eq Nat A B` and
    /// `@Eq Nat B A` — equal ONLY after commutative-operand canonicalisation —
    /// plus a third decl `@Eq Nat A A` whose canonical form differs. The
    /// rewrite-canonical digest must collapse the first pair and exclude the
    /// third, which neither a name search nor a raw discrimination-tree match
    /// (distinct child order) can do.
    fn build_commutative_shard_dir() -> tempfile::TempDir {
        let dir = tempdir().expect("tempdir");
        let mut writer = ShardWriter::new();
        let eq = writer.add_string("Eq");
        let nat = writer.add_string("Nat");
        let a = writer.add_string("A");
        let b = writer.add_string("B");
        let eq_c = writer.add_expr(FlatExpr::const_ref(eq, u32::MAX));
        let nat_c = writer.add_expr(FlatExpr::const_ref(nat, u32::MAX));
        let a_c = writer.add_expr(FlatExpr::const_ref(a, u32::MAX));
        let b_c = writer.add_expr(FlatExpr::const_ref(b, u32::MAX));

        // `@Eq Nat x y` == App(App(App(Eq, Nat), x), y); spine arity 3 matches
        // the commutative-operand rule, so the last two operands are reordered.
        let eq_app = |x: u32, y: u32, w: &mut ShardWriter| {
            let f1 = w.add_expr(FlatExpr::app(eq_c, nat_c));
            let f2 = w.add_expr(FlatExpr::app(f1, x));
            w.add_expr(FlatExpr::app(f2, y))
        };
        let ty_ab = eq_app(a_c, b_c, &mut writer);
        let ty_ba = eq_app(b_c, a_c, &mut writer);
        let ty_aa = eq_app(a_c, a_c, &mut writer);

        let push = |name: &str, ty: u32, w: &mut ShardWriter| {
            let ni = w.add_string(name);
            w.add_constant(MathverseConstantHeader {
                name_idx: ni,
                type_idx: ty,
                value_idx: u32::MAX,
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
            });
        };
        push("eq_ab", ty_ab, &mut writer);
        push("eq_ba", ty_ba, &mut writer);
        push("eq_aa", ty_aa, &mut writer);

        let mut buf = Vec::new();
        writer.write(&mut buf).expect("shard write");
        std::fs::write(dir.path().join("comm.mathverse"), &buf).expect("write");
        dir
    }

    #[test]
    fn test_structural_mode_collapses_commutative_reorder() {
        let dir = build_commutative_shard_dir();
        let lib = load_library(dir.path()).expect("load");

        let eq_ab = lib.lookup_constant_idx("eq_ab").expect("eq_ab present");
        // The rewrite-canonical digests of `@Eq Nat A B` and `@Eq Nat B A` match;
        // `@Eq Nat A A` differs.
        let d_ab = lib.structural_rewrite_digest_of(eq_ab).expect("digest ab");
        let eq_ba = lib.lookup_constant_idx("eq_ba").expect("eq_ba present");
        let eq_aa = lib.lookup_constant_idx("eq_aa").expect("eq_aa present");
        assert_eq!(
            d_ab,
            lib.structural_rewrite_digest_of(eq_ba).expect("digest ba"),
            "A=B and B=A must share a rewrite-canonical digest"
        );
        assert_ne!(
            d_ab,
            lib.structural_rewrite_digest_of(eq_aa).expect("digest aa"),
            "A=B and A=A must NOT share a digest"
        );

        // The scan path (no index) returns the equivalence class, excluding the
        // anchor and the differently-shaped `eq_aa`.
        let class = lib.structural_equivalents_of(eq_ab, 16);
        let names: Vec<&str> = class.iter().filter_map(|&i| lib.get_name(i)).collect();
        assert_eq!(names, vec!["eq_ba"], "expected only eq_ba, got {names:?}");
    }

    #[test]
    fn test_structural_mode_cmd_runs_scan_path() {
        let dir = build_commutative_shard_dir();
        let args = SearchArgs {
            pattern: Some("eq_ab".into()),
            mode: SearchMode::Structural,
            like: None,
            index: None,
            shard_dir: dir.path().to_path_buf(),
            limit: 10,
            json: true,
        };
        cmd_search(args).expect("structural search (scan path)");
    }

    #[test]
    fn test_structural_missing_query_is_typed_error() {
        let dir = build_commutative_shard_dir();
        let args = SearchArgs {
            pattern: None,
            mode: SearchMode::Structural,
            like: None,
            index: None,
            shard_dir: dir.path().to_path_buf(),
            limit: 10,
            json: false,
        };
        let err = cmd_search(args).expect_err("missing query should fail");
        assert!(matches!(
            err,
            MathverseCliError::SearchMissingQuery("structural")
        ));
    }

    #[test]
    fn test_info_missing_is_typed_error() {
        let dir = make_shard_dir_with_decls();
        let args = InfoArgs {
            name: "Nonexistent.decl".into(),
            shard_dir: dir.path().to_path_buf(),
            json: false,
        };
        let err = cmd_info(args).expect_err("should fail");
        assert!(matches!(err, MathverseCliError::DeclarationNotFound(_)));
    }

    #[test]
    fn test_stats_runs_without_error() {
        let dir = make_shard_dir_with_decls();
        cmd_stats(StatsArgs {
            shard_dir: dir.path().to_path_buf(),
            json: true,
        })
        .expect("stats");
    }

    #[test]
    fn test_systems_runs_without_error() {
        let dir = make_shard_dir_with_decls();
        cmd_systems(SystemsArgs {
            shard_dir: dir.path().to_path_buf(),
            json: false,
        })
        .expect("systems");
    }

    #[test]
    fn test_collect_stats_counts_match() {
        let dir = make_shard_dir_with_decls();
        let lib = load_library(dir.path()).expect("load");
        let snap = collect_stats(&lib);
        assert_eq!(snap.total, 3);
        assert_eq!(snap.by_source.len(), 1);
        assert_eq!(
            *snap.by_source.get(&(SourceSystem::Lean4 as u8)).unwrap(),
            3
        );
    }
}
