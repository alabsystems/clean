// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Export an ALREADY-VERIFIED set of Metamath theorems to a Mathverse shard
//! WITHOUT re-verifying their proofs.
//!
//! Usage: `mm_export_verified [--type-only] <set.mm> <verified-labels-file> <out.mathverse>`
//!
//! The two-pass parallel verifier (`scripts/mm_two_pass.sh` + `mm_verify_range` +
//! `mm_gate`) produces a dependency-closure-GATED list of verified theorem LABELS:
//! their proofs WERE kernel-checked, just in a separate (parallel) process. This
//! tool turns that label set into a publishable `.mathverse` shard.
//!
//! It does NOT re-check any proof. For each label in the verified set V it obtains
//! the theorem's schematic TYPE expression — the only thing a shard entry needs —
//! by running the importer's PASS-1 mechanism
//! ([`clean_olean::metamath::kernel_verify_pass1_types`]): each `$p` theorem's
//! schematic type is registered as an axiom (the SAME construction the real
//! verifier uses, so byte-identical types) WITHOUT checking the proof, and the
//! kernel-registered type of every V label is read back from the `Environment`.
//! Pass-1 is RANGE-SCOPED to V ∪ its `$p`-dependency closure, so memory stays
//! bounded; `--chunk <N>` splits V into N-label batches (each its own pass-1) to
//! bound it further.
//!
//! Each V theorem is emitted as a `NativeTheoremEntry` (name = `mm.<label>` exactly
//! as the kernel registered it, the schematic type expr, `value_expr: None` for
//! `--type-only`, `AxiomProfile::AXIOMATIZED`, tags `["metamath","set.mm"]`) into a
//! `StreamingShardExporter::new().with_value_less_kernel_verified(true)`.
//!
//! SOUNDNESS. The `KernelVerified` trust label is justified ONLY because the input
//! labels are the two-pass-verified, dependency-closure-gated set. This tool
//! exports ONLY labels present in V; it never invents or includes a label outside
//! V. The exported type is the one the kernel registered (same schematic
//! construction as the verifier), read from `env.get_const(mm.<label>).type_`.

use std::path::Path;
use std::process::ExitCode;

use clean_mathverse::export::native_export::{NativeTheoremEntry, StreamingShardExporter};
use clean_mathverse::types::{AxiomProfile, ContentDomain};
use clean_olean::metamath::{kernel_verify_pass1_types, parse_database_file};

/// Parse a verified-labels file: one label per line, either bare (as `mm_gate`
/// emits) or in the `V <label>` form (as `mm_verify_range`/`mm_kverify` emit).
/// Mirrors `mm_gate`'s reader, plus a robustness filter so the WHOLE stdout of
/// `mm_kverify` (which interleaves a `=== … ===` summary with the `V` lines) can be
/// fed directly: a real Metamath label is a single whitespace-free token, so any
/// post-strip token that still contains whitespace (every summary line) is dropped,
/// as are blank lines and the `VERIFIED_COUNT <n>` header. A non-provable label
/// that slips through is harmless anyway — it matches no theorem, so it is never
/// registered or exported (it would only show as a coverage "gap" in the report).
fn parse_verified_labels(raw: &str) -> hashbrown::HashSet<String> {
    raw.lines()
        .map(str::trim)
        .filter(|l| !l.is_empty() && !l.starts_with("VERIFIED_COUNT"))
        .map(|l| l.strip_prefix("V ").unwrap_or(l).trim().to_string())
        // A Metamath label has no internal whitespace; this discards summary lines.
        .filter(|l| !l.is_empty() && !l.chars().any(char::is_whitespace))
        .collect()
}

fn run() -> Result<(), String> {
    let args: Vec<String> = std::env::args().collect();
    let type_only = args.iter().any(|a| a == "--type-only");
    // `--chunk <N>`: split V into N-label batches, one pass-1 each (memory bound).
    let chunk_size: Option<usize> = args
        .iter()
        .position(|a| a == "--chunk")
        .and_then(|i| args.get(i + 1))
        .and_then(|s| s.parse::<usize>().ok())
        .filter(|&n| n > 0);
    // Positional args (skip the program name, any `--flag`, and the `--chunk` value).
    let mut positional: Vec<&String> = Vec::new();
    let mut skip_next = false;
    for a in args.iter().skip(1) {
        if skip_next {
            skip_next = false;
            continue;
        }
        if a == "--chunk" {
            skip_next = true; // the next token is the chunk count, not positional
            continue;
        }
        if a.starts_with("--") {
            continue;
        }
        positional.push(a);
    }
    if positional.len() < 3 {
        return Err(
            "usage: mm_export_verified [--type-only] [--chunk N] <set.mm> \
                    <verified-labels-file> <out.mathverse>"
                .to_string(),
        );
    }
    let in_path = positional[0];
    let labels_path = positional[1];
    let out_path = positional[2];

    // Read the gated, ALREADY-VERIFIED label set V. These proofs were kernel-checked
    // by the two-pass verifier; we trust them and export only their types.
    let raw = std::fs::read_to_string(labels_path)
        .map_err(|e| format!("read labels {labels_path}: {e}"))?;
    let verified = parse_verified_labels(&raw);
    if verified.is_empty() {
        return Err(format!("no verified labels found in {labels_path}"));
    }
    eprintln!("read {} verified labels from {labels_path}", verified.len());

    let db = parse_database_file(Path::new(in_path)).map_err(|e| format!("parse error: {e}"))?;

    let mut exporter = StreamingShardExporter::new().with_value_less_kernel_verified(true);
    // First emitted kernel-name, for the round-trip KernelVerified spot-check.
    let mut first_name: Option<String> = None;
    // Labels we actually emitted (⊆ V): a V label not registered in pass-1 (e.g. a
    // skipped/compressed type-build) is reported as MISSING rather than silently
    // dropped, so the operator sees the gap.
    let mut emitted: hashbrown::HashSet<String> = hashbrown::HashSet::new();
    let mut add_err: Option<String> = None;

    // Run pass-1 type registration, batched by `--chunk` if requested. Each batch is
    // an independent pass-1 over the SAME database (range-scoped to that batch's
    // closure), so peak memory is bounded by the largest batch's reuse closure.
    let batches: Vec<hashbrown::HashSet<String>> = match chunk_size {
        None => vec![verified.clone()],
        Some(n) => {
            let mut sorted: Vec<&String> = verified.iter().collect();
            sorted.sort(); // deterministic batching
            sorted
                .chunks(n)
                .map(|c| c.iter().map(|s| (*s).clone()).collect())
                .collect()
        }
    };
    if let Some(n) = chunk_size {
        eprintln!(
            "exporting in {} chunk(s) of up to {n} labels each",
            batches.len()
        );
    }

    for (bi, batch) in batches.iter().enumerate() {
        if chunk_size.is_some() {
            eprintln!(
                "  chunk {}/{}: {} labels",
                bi + 1,
                batches.len(),
                batch.len()
            );
        }
        let mut sink = |label: &str, kernel_name: &str, ty: &clean_kernel::Expr| {
            if add_err.is_some() {
                return;
            }
            // Defensive: the sink only fires for labels in `wanted`, but never emit a
            // label outside the overall verified set V (the trust boundary).
            if !verified.contains(label) {
                return;
            }
            if first_name.is_none() {
                first_name = Some(kernel_name.to_string());
            }
            let entry = NativeTheoremEntry {
                name: kernel_name.to_string(),
                type_expr: ty.clone(),
                // `--type-only` is the publishable form (small artifact); the verified
                // labels carry no proof VALUE here — pass-1 registered types only.
                value_expr: None,
                content_domain: ContentDomain::Logic,
                // HONEST trust: KernelVerified (the proofs WERE kernel-checked by the
                // two-pass) but AXIOMATIZED (trust-gated) — they rest on the Metamath
                // `$a` axioms, so this must NOT imply a foundational-only proof.
                axiom_profile: AxiomProfile::AXIOMATIZED,
                tags: vec!["metamath".to_string(), "set.mm".to_string()],
                conjecture_id: None,
            };
            match exporter.add(&entry) {
                Ok(()) => {
                    emitted.insert(label.to_string());
                }
                Err(e) => add_err = Some(e.to_string()),
            }
        };
        // `max_provables = usize::MAX`: traverse the whole database so every V label
        // (wherever it sits in source order) is reached. Range-scoping inside pass-1
        // keeps only this batch's reuse closure resident.
        kernel_verify_pass1_types(&db, usize::MAX, batch, &mut sink)
            .map_err(|e| format!("pass-1 type registration: {e}"))?;
        if let Some(e) = add_err.take() {
            return Err(format!("export error: {e}"));
        }
    }

    // The `--type-only` flag is documented for symmetry with `mm_export_shard`, but
    // pass-1 produces no proof values, so this exporter is ALWAYS value-less. A
    // caller passing the flag (or not) gets the same value-less KernelVerified shard;
    // surface that explicitly so the contract is not surprising.
    if !type_only {
        eprintln!(
            "note: pass-1 registers TYPES only (no proof values); the shard is value-less \
             regardless of --type-only"
        );
    }

    // Report any V label we could not register a type for (a coverage gap, not a
    // soundness issue — we simply emit fewer entries than V).
    let missing: Vec<&String> = verified.iter().filter(|l| !emitted.contains(*l)).collect();
    eprintln!(
        "registered + exporting {} of {} verified labels ({} type-build gaps)",
        emitted.len(),
        verified.len(),
        missing.len()
    );
    if !missing.is_empty() {
        let show: Vec<&&String> = missing.iter().take(10).collect();
        eprintln!("  first missing (no schematic type built): {show:?}");
    }

    let exported = exporter.len();
    let stats = exporter
        .finish(Path::new(out_path))
        .map_err(|e| format!("export error: {e}"))?;

    // Round-trip self-check: re-parse the header, validate the footer checksum, and
    // confirm a sample decl reloads with KernelVerified confidence.
    let reader = clean_mathverse::shard::ShardReader::from_file(Path::new(out_path))
        .map_err(|e| format!("shard written but round-trip reload failed: {e}"))?;
    let kv = clean_mathverse::types::ImportConfidence::KernelVerified as u8;
    let sample_kv = first_name
        .as_deref()
        .and_then(|n| reader.lookup_name(n))
        .is_some_and(|(_, h)| h.import_confidence == kv);
    println!(
        "exported {} KernelVerified metamath theorems (trust-gated: rests on Metamath axioms) -> {}",
        stats.entries_written, out_path
    );
    println!(
        "round-trip OK: shard reloads + checksum valid; entries_written={} (==exported {}); \
         sample decl KernelVerified={sample_kv}",
        stats.entries_written, exported
    );
    if !sample_kv && stats.entries_written > 0 {
        return Err("round-trip sample decl is NOT KernelVerified".to_string());
    }
    Ok(())
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("error: {e}");
            ExitCode::FAILURE
        }
    }
}
