// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-verify Metamath theorems and export them to a Mathverse shard.
//!
//! Usage: `mm_export_shard [--type-only] <path.mm> <out.mathverse> [max_provables]`
//!
//! Each theorem the Clean kernel verifies (schematic reuse — see
//! `clean_kernel::metamath_reflect`) is written as a `KernelVerified` declaration
//! (the kernel genuinely re-checked the derivation via `add_decl`). The
//! `AxiomProfile` is flagged `AXIOMATIZED` (trust-gated) to record HONESTLY that
//! these derivations rest on the Metamath `$a` axioms — they are kernel-verified
//! *relative to* Metamath's postulates, NOT foundational-only proofs.
//!
//! The export STREAMS: each verified theorem is fed straight into the shard
//! builder and its proof VALUE is dropped immediately (`forget_value`), so the
//! ~25-30k post-Pattern-B corpus (proof terms ~3 MB each) exports with bounded
//! memory instead of holding ~90 GB of values at once. `--type-only` additionally
//! drops the proof value FROM the shard (stores name+type+KernelVerified label as
//! an axiom-shaped entry) for a much smaller artifact when proof terms aren't
//! needed downstream.

use std::path::Path;
use std::process::ExitCode;

use clean_mathverse::export::native_export::{NativeTheoremEntry, StreamingShardExporter};
use clean_mathverse::types::{AxiomProfile, ContentDomain};
use clean_olean::metamath::{kernel_verify_database_prefix_streaming, parse_database_file};

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    let type_only = args.iter().any(|a| a == "--type-only");
    // Positional args (skip the program name and any `--flags`).
    let positional: Vec<&String> = args
        .iter()
        .skip(1)
        .filter(|a| !a.starts_with("--"))
        .collect();
    if positional.len() < 2 {
        eprintln!("usage: mm_export_shard [--type-only] <path.mm> <out.mathverse> [max_provables]");
        return ExitCode::FAILURE;
    }
    let in_path = positional[0];
    let out_path = positional[1];
    let max = positional
        .get(2)
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or(usize::MAX);

    let db = match parse_database_file(Path::new(in_path)) {
        Ok(db) => db,
        Err(e) => {
            eprintln!("parse error: {e}");
            return ExitCode::FAILURE;
        }
    };

    // Stream each verified theorem straight into the shard; its value is dropped by
    // the verifier right after the sink runs, so peak memory holds only the
    // deduplicated shard arena, never all ~25-30k proof values.
    // `--type-only` drops proof values from the shard. Those entries were still
    // kernel-verified (we only export `report.verified` theorems), so trust them as
    // KernelVerified, not Axiomatized — the type-only shard makes the same trust
    // claim as the values-kept one, just without the (huge) proof terms.
    // Segmented output (set `CLEAN_MM_SEGMENT=<K>`): flush a finalized shard every
    // K verified theorems to `<out>.seg<NNNN>.mathverse`, then reset the builder.
    // This makes a long run toward the FULL corpus PRODUCTIVE (each segment is
    // releasable as soon as it lands; mathverse is natively multi-shard), CRASH-
    // RESILIENT (a kill loses only the in-flight segment), and bounds the shard
    // builder's arena (which type-forgetting does not — it lives in this process,
    // not the kernel env). Unset ⇒ single shard at `<out>` (original behaviour).
    let segment_size: Option<usize> = std::env::var("CLEAN_MM_SEGMENT")
        .ok()
        .and_then(|s| s.parse::<usize>().ok())
        .filter(|&k| k > 0);
    let mut segment: usize = 0;
    let mut exporter = StreamingShardExporter::new().with_value_less_kernel_verified(type_only);
    let mut add_err: Option<String> = None;
    let mut first_name: Option<String> = None;
    let report = match kernel_verify_database_prefix_streaming(&db, max, &mut |name, ty, val| {
        if add_err.is_some() {
            return;
        }
        if first_name.is_none() {
            first_name = Some(name.to_string());
        }
        let entry = NativeTheoremEntry {
            name: name.to_string(),
            type_expr: ty.clone(),
            value_expr: if type_only { None } else { Some(val.clone()) },
            content_domain: ContentDomain::Logic,
            // HONEST trust: KernelVerified (the kernel checked the derivation) but
            // AXIOMATIZED (trust-gated) — these rest on the Metamath `$a` axioms,
            // so the profile must NOT imply a foundational-only proof.
            axiom_profile: AxiomProfile::AXIOMATIZED,
            tags: vec!["metamath".to_string(), "set.mm".to_string()],
            conjecture_id: None,
        };
        match exporter.add(&entry) {
            Err(e) => add_err = Some(e.to_string()),
            Ok(()) => {
                if let Some(seg_sz) = segment_size {
                    if exporter.len() >= seg_sz {
                        let fresh = StreamingShardExporter::new()
                            .with_value_less_kernel_verified(type_only);
                        let done = std::mem::replace(&mut exporter, fresh);
                        let seg_path = format!("{out_path}.seg{segment:04}.mathverse");
                        match done.finish(Path::new(&seg_path)) {
                            Ok(_) => {
                                use std::io::Write;
                                let _ = writeln!(
                                    std::io::stderr(),
                                    "FLUSHED segment {segment} ({seg_sz} entries) -> {seg_path}"
                                );
                                let _ = std::io::stderr().flush();
                                segment += 1;
                            }
                            Err(e) => add_err = Some(e.to_string()),
                        }
                    }
                }
            }
        }
    }) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("verify error: {e}");
            return ExitCode::FAILURE;
        }
    };
    if let Some(e) = add_err {
        eprintln!("export error: {e}");
        return ExitCode::FAILURE;
    }
    eprintln!(
        "kernel-verified {} theorems ({}); exporting {} entries to {}",
        report.verified.len(),
        if type_only {
            "type-only"
        } else {
            "with proof values"
        },
        exporter.len(),
        out_path
    );

    let final_path = if segment_size.is_some() {
        format!("{out_path}.seg{segment:04}.mathverse")
    } else {
        out_path.to_string()
    };
    // If the last segment flush emptied the builder, every entry is already written.
    if exporter.is_empty() {
        println!(
            "=== export complete: {} entries across {segment} segment(s) ===",
            report.verified.len()
        );
        return ExitCode::SUCCESS;
    }
    let stats = match exporter.finish(Path::new(&final_path)) {
        Ok(stats) => stats,
        Err(e) => {
            eprintln!("export error: {e}");
            return ExitCode::FAILURE;
        }
    };

    // Round-trip self-check: `ShardReader::from_file` re-parses the header and
    // validates the footer checksum, so a clean reload confirms the artifact is
    // intact and loadable by the Mathverse CLI.
    match clean_mathverse::shard::ShardReader::from_file(Path::new(&final_path)) {
        Ok(reader) => {
            println!(
                "exported {} KernelVerified metamath theorems (trust-gated: rests on Metamath \
                 axioms) -> {}",
                stats.entries_written, out_path
            );
            // Confirm a decl reloads with KernelVerified confidence.
            let kv = clean_mathverse::types::ImportConfidence::KernelVerified as u8;
            let sample_ok = first_name
                .as_deref()
                .and_then(|n| reader.lookup_name(n))
                .is_some_and(|(_, h)| h.import_confidence == kv);
            println!(
                "round-trip OK: shard reloads + checksum valid; sample decl KernelVerified={sample_ok}"
            );
            ExitCode::SUCCESS
        }
        Err(e) => {
            eprintln!("ERROR: shard written but round-trip reload failed: {e}");
            ExitCode::FAILURE
        }
    }
}
