// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Dispatch for `mathverse isabelle-import` — the standing re-import pipeline
//! (P3 of `designs/2026-07-07-isabelle-100pct-industrial-import.md`):
//! raw per-theory exports → serial-sorted deduplicated corpus (bounded-memory
//! assembly + closure sanity stats) → kernel closure replay (parallel or
//! serial) with snapshot resume/save → honest verdict report.

use std::path::Path;

use super::{IsabelleImportArgs, MathverseCliError};
use crate::hol::isabelle_import::assemble_corpus;
use crate::hol::isabelle_pure_verify::{
    import_proven_theorems_parallel, import_proven_theorems_retry,
    import_proven_theorems_retry_with_diff, import_proven_theorems_streaming, PureVerifiedImport,
};
use crate::process_env::ScopedEnv;
use crate::provenance::{add_provenance, ProvenanceBuilder, ProvenanceSidecar};
use crate::shard::ShardWriter;

/// Bump when the Isabelle import pipeline's semantics change (recorded in
/// every provenance record this verb writes).
const ISABELLE_IMPORT_PIPELINE_VERSION: u32 = 1;

/// Kernel replay recursion is deep; run the whole replay on a dedicated
/// big-stack thread so the verb works regardless of the caller's
/// `RUST_MIN_STACK`.
const REPLAY_STACK: usize = 2560 * 1024 * 1024;

fn err(e: impl std::fmt::Display) -> MathverseCliError {
    MathverseCliError::IsabelleImport(e.to_string())
}

pub(super) fn cmd_isabelle_import(args: IsabelleImportArgs) -> Result<(), MathverseCliError> {
    // --- Stage A: assembly (optional) ---
    if let Some(raw_dir) = &args.raw_dir {
        let report = assemble_corpus(raw_dir, &args.corpus, args.mem_budget).map_err(err)?;
        println!(
            "ASSEMBLED: {} files -> {} lines ({} bytes) at {}",
            report.files,
            report.lines_out,
            report.bytes_out,
            args.corpus.display()
        );
        println!(
            "  duplicates dropped: {}  unparseable: {}  nop proof roots: {}  legacy :null holes: {}  missing refs: {}",
            report.duplicates_dropped,
            report.unparseable,
            report.nop_lines,
            report.null_holes,
            report.missing_refs
        );
        if report.null_holes > 0 {
            eprintln!(
                "WARNING: {} legacy `:null` holes — this does not look like a zproof (record_proofs>=4) export",
                report.null_holes
            );
        }
    }
    if args.assemble_only {
        return Ok(());
    }

    // --- Stage B: replay with snapshot resume/save ---
    // The drivers read the snapshot/budget configuration from the environment
    // (the established test-harness surface). Hold the process-wide environment
    // guard until every replay worker has joined, then restore the exact ambient
    // values on every return path.
    let mut replay_env = ScopedEnv::new();
    if let Some(p) = &args.snapshot_in {
        replay_env.set("ISA_SNAPSHOT_IN", p);
    } else {
        replay_env.remove("ISA_SNAPSHOT_IN");
    }
    if let Some(p) = &args.snapshot_out {
        replay_env.set("ISA_SNAPSHOT_OUT", p);
    } else {
        replay_env.remove("ISA_SNAPSHOT_OUT");
    }
    // Ledger burn-down retry: widen `--retry-from` to re-attempt the trusted
    // ledger axioms + tier-2 conditionals too (see `import_proven_theorems_retry`).
    // It implies the two-tier ledger lane, so turn that on as well — a still-failing
    // ledger line must re-register as a trusted-ledger axiom, not fall to a bare
    // reject.
    if args.retry_ledger {
        replay_env.set("ISA_RETRY_LEDGER", "1");
        replay_env.set("ISA_TRUSTED_LEDGER", "1");
    } else {
        replay_env.remove("ISA_RETRY_LEDGER");
    }
    // Targeted re-attempt seed: the retry driver reads `ISA_RETRY_SEED` and
    // intersects its re-attempt set with the seed serials (a PARTIAL burn-down of
    // just that family). Threaded through the scoped-env guard like the rest.
    if let Some(seed) = &args.retry_seed {
        replay_env.set("ISA_RETRY_SEED", seed);
    } else {
        replay_env.remove("ISA_RETRY_SEED");
    }
    replay_env.set(
        "ISA_TRANSLATE_NODE_BUDGET",
        args.translate_budget.to_string(),
    );
    replay_env.set("ISA_ELIDE_PROOFS", "1");
    if std::env::var("ISA_PROGRESS_EVERY").is_err() {
        replay_env.set("ISA_PROGRESS_EVERY", "10000");
    }

    // Every replay path through this verb is a verify GROUP and must hold the
    // machine-wide primary verify lock for its lifetime. The #106 diagnosis
    // found the SERIAL streaming path ran lock-free (only the shard-group
    // driver acquired) — a grand could silently coexist with another verify
    // run. Bypass/force env overrides still apply (shard children, tests).
    let _verify_lock = crate::hol::isabelle_pure_verify::VerifyLock::acquire_default()
        .map_err(|e| MathverseCliError::IsabelleImport(e.to_string()))?;

    let corpus = args.corpus.clone();
    let workers = args.workers;
    let retry_from = args.retry_from.clone();
    let corpus_diff = args.corpus_diff.clone();
    let (result, mut writer): (PureVerifiedImport, ShardWriter) = std::thread::Builder::new()
        .stack_size(REPLAY_STACK)
        .spawn(
            move || -> Result<(PureVerifiedImport, ShardWriter), String> {
                let mut writer = ShardWriter::new();
                let r = if let (Some(snap), Some(diff)) = (&retry_from, &corpus_diff) {
                    // INCREMENTAL grand: re-verify the OLD version's former rejects
                    // PLUS the corpus-diff's NEW + CHANGED lines against the OLD
                    // version's trusted snapshot prefix. Refused (loud) if the diff
                    // shows any change inside that trusted prefix.
                    import_proven_theorems_retry_with_diff(
                        Path::new(&corpus),
                        Path::new(snap),
                        Path::new(diff),
                        &mut writer,
                        workers,
                    )
                } else if let Some(snap) = retry_from {
                    // Verdict-cache retry: re-verify the snapshot's former rejects
                    // (and, under `--retry-ledger` / `ISA_RETRY_LEDGER`, the trusted
                    // ledger axioms + tier-2 conditionals) against the same corpus
                    // under the current translator.
                    import_proven_theorems_retry(
                        Path::new(&corpus),
                        Path::new(&snap),
                        &mut writer,
                        workers,
                    )
                } else if workers > 0 {
                    import_proven_theorems_parallel(Path::new(&corpus), &mut writer, workers)
                } else {
                    import_proven_theorems_streaming(Path::new(&corpus), &mut writer)
                };
                r.map(|out| (out, writer)).map_err(|e| e.to_string())
            },
        )
        .map_err(err)?
        .join()
        .map_err(|_| err("replay thread panicked"))?
        .map_err(err)?;

    // Three distinct tiers (the two-tier ledger tiers are 0 on a non-ledger
    // run, so this line degrades to the historical `KernelVerified / rejected`
    // summary when `ISA_TRUSTED_LEDGER` is unset):
    //   tier-1  KernelVerified            — foundational-only closure
    //   tier-2  KernelCheckedConditional  — kernel re-checked, closure ⊇ ledger
    //   ledger  trusted-ledger axioms     — statement-only restatements
    println!(
        "REPLAY: {} KernelVerified (tier-1), {} KernelCheckedConditional (tier-2, ledger-dependent), \
         {} trusted-ledger axioms, {} rejected",
        result.kernel_verified,
        result.kernel_checked_ledger,
        result.ledger_size,
        result.rejected
    );
    let mut reasons: Vec<(&String, &usize)> = result.rejection_reasons.iter().collect();
    reasons.sort_by(|a, b| b.1.cmp(a.1).then_with(|| a.0.cmp(b.0)));
    for (reason, count) in reasons {
        println!("  {reason}: {count}");
    }

    // Per-run trusted-ledger report (serial-sorted, deterministic). Written
    // whenever the ledger is non-empty — to `ISA_LEDGER_REPORT` if set, else a
    // sibling `<corpus>.ledger.tsv`. One TSV row per registered ledger axiom.
    if !result.ledger.is_empty() {
        let report_path = std::env::var_os("ISA_LEDGER_REPORT")
            .map(std::path::PathBuf::from)
            .unwrap_or_else(|| {
                let mut p = args.corpus.clone();
                let name = p
                    .file_name()
                    .map(|n| format!("{}.ledger.tsv", n.to_string_lossy()))
                    .unwrap_or_else(|| "corpus.ledger.tsv".to_string());
                p.set_file_name(name);
                p
            });
        match write_ledger_report(&report_path, &result.ledger) {
            Ok(()) => println!(
                "LEDGER: {} trusted-ledger axioms -> {}",
                result.ledger.len(),
                report_path.display()
            ),
            Err(e) => eprintln!("WARNING: could not write ledger report: {e}"),
        }
    }

    // --- Stage C: publishable shard with per-constant provenance ---
    // Retry mode is a re-MEASURE, not a shard build: its writer holds only the
    // newly-recovered constants (like a resume shard), so the whole-corpus
    // provenance stamp below (which requires one header per verified NAME) does
    // not apply. A publishable shard comes from a full replay.
    if args.retry_from.is_some() && args.shard_out.is_some() {
        eprintln!(
            "NOTE: --shard-out ignored in retry mode (re-measure only); run a full \
             replay to publish a shard"
        );
    }
    if let Some(shard_path) = args
        .shard_out
        .as_ref()
        .filter(|_| args.retry_from.is_none())
    {
        let n = writer.constants_len();
        let stamp = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap_or_default()
            .as_secs();
        let fingerprint = crate::hol::isabelle_pure_verify::snapshot::current_fingerprint();
        let corpus_str = args.corpus.display().to_string();
        let mut sidecar = ProvenanceSidecar::new();
        // On a **ledger run** the shard also carries tier-2 / ledger constants,
        // so `written_constants` (populated only under `ISA_TRUSTED_LEDGER`)
        // gives the FULL shard-write-order list with each constant's exact shard
        // index, confidence, and note. Off the ledger path it is empty and we
        // stamp the historical `names`-only loop (byte-identical), where KV
        // constant `i` is at shard index `i`.
        if result.written_constants.is_empty() {
            if n != result.names.len() {
                return Err(err(format!(
                    "shard/name count mismatch ({n} headers vs {} verified names) — refusing to stamp provenance",
                    result.names.len()
                )));
            }
            for (i, name) in result.names.iter().enumerate() {
                let rec = ProvenanceBuilder::new(name)
                    .module_path(&corpus_str)
                    .source_version("Isabelle2025-2 zproof (record_proofs>=4)")
                    .import_timestamp(stamp)
                    .pipeline_version(ISABELLE_IMPORT_PIPELINE_VERSION)
                    .note(&format!(
                        "KernelVerified closure replay; translator {fingerprint}"
                    ))
                    .build();
                let (prov_idx, digest) = add_provenance(&mut sidecar, rec);
                writer.set_constant_provenance(i as u32, prov_idx, digest);
            }
        } else {
            if n != result.written_constants.len() {
                return Err(err(format!(
                    "shard/written-constant count mismatch ({n} headers vs {} written constants) — refusing to stamp provenance",
                    result.written_constants.len()
                )));
            }
            for wc in &result.written_constants {
                let note = wc.ledger_note.clone().unwrap_or_else(|| {
                    format!("KernelVerified closure replay; translator {fingerprint}")
                });
                let rec = ProvenanceBuilder::new(&wc.name)
                    .module_path(&corpus_str)
                    .source_version("Isabelle2025-2 zproof (record_proofs>=4)")
                    .import_timestamp(stamp)
                    .pipeline_version(ISABELLE_IMPORT_PIPELINE_VERSION)
                    .note(&note)
                    .build();
                let (prov_idx, digest) = add_provenance(&mut sidecar, rec);
                writer.set_constant_provenance(wc.shard_idx, prov_idx, digest);
            }
        }
        writer.set_provenance(sidecar.to_bytes().map_err(err)?);
        writer.write_to_file(shard_path).map_err(err)?;
        println!(
            "SHARD: {} constants ({} KernelVerified, {} KernelCheckedConditional, {} trusted-ledger) + provenance -> {}",
            n,
            result.kernel_verified,
            result.kernel_checked_ledger,
            result.ledger_size,
            shard_path.display()
        );
    }
    Ok(())
}

/// Write the per-run trusted-ledger report as a deterministic, serial-sorted
/// TSV: one row per registered ledger axiom (`serial`, `axiom_name`, `theory`,
/// `reject_reason`, `isabelle_name`).
fn write_ledger_report(
    path: &Path,
    ledger: &[crate::hol::isabelle_pure_verify::LedgerEntry],
) -> std::io::Result<()> {
    use std::io::Write as _;
    let mut sorted: Vec<&crate::hol::isabelle_pure_verify::LedgerEntry> = ledger.iter().collect();
    sorted.sort_by(|a, b| {
        a.serial
            .cmp(&b.serial)
            .then_with(|| a.axiom_name.cmp(&b.axiom_name))
    });
    let mut f = std::io::BufWriter::new(std::fs::File::create(path)?);
    writeln!(
        f,
        "serial\taxiom_name\ttheory\treject_reason\tisabelle_name"
    )?;
    for e in sorted {
        writeln!(
            f,
            "{}\t{}\t{}\t{}\t{}",
            e.serial, e.axiom_name, e.theory, e.reject_reason, e.isabelle_name
        )?;
    }
    f.flush()
}

pub(super) fn cmd_isabelle_targets(
    args: super::IsabelleTargetsArgs,
) -> Result<(), MathverseCliError> {
    let report = crate::hol::isabelle_targets::compute_targets(
        &args.corpus,
        &args.snapshot,
        args.dump.as_deref(),
        args.top,
    )
    .map_err(err)?;
    println!(
        "TARGETS: corpus {} lines | accepted {} | rejected {} | primaries {} (cascade {}) | forward-edges {}",
        report.corpus_lines,
        report.accepted,
        report.rejected,
        report.primaries,
        report.cascade,
        report.forward_edges,
    );
    println!(
        "{:>4}  {:>8}  {:>7}  {:>7}  {:<16}  name / signature",
        "rank", "serial", "blocked", "exclsv", "reason"
    );
    for (rank, row) in report.rows.iter().enumerate() {
        let reason = if row.reason.is_empty() {
            "-"
        } else {
            row.reason.as_str()
        };
        let detail = if row.signature.is_empty() {
            row.name.clone()
        } else {
            format!("{}  |  {}", row.name, row.signature)
        };
        println!(
            "{:>4}  {:>8}  {:>7}  {:>7}  {:<16}  {}",
            rank + 1,
            row.serial,
            row.blocked,
            row.exclusive,
            reason,
            detail,
        );
    }
    Ok(())
}

pub(super) fn cmd_isabelle_index(args: super::IsabelleIndexArgs) -> Result<(), MathverseCliError> {
    let index = crate::hol::isabelle_index::build_index(&args.corpus)
        .map_err(|e| MathverseCliError::IsabelleIndex(e.to_string()))?;
    let out = args
        .out
        .unwrap_or_else(|| crate::hol::isabelle_index::index_path(&args.corpus));
    crate::hol::isabelle_index::save_index(&out, &index)
        .map_err(|e| MathverseCliError::IsabelleIndex(e.to_string()))?;
    let dep_edges: usize = index.entries.iter().map(|e| e.deps.len()).sum();
    let reg_lines = index.entries.iter().filter(|e| e.is_registration).count();
    println!(
        "INDEX: {} entries ({} registration lines, {} dep edges) over {} corpus bytes -> {}",
        index.entries.len(),
        reg_lines,
        dep_edges,
        index.corpus_len,
        out.display()
    );
    Ok(())
}

pub(super) fn cmd_isabelle_corpus_diff(
    args: super::IsabelleCorpusDiffArgs,
) -> Result<(), MathverseCliError> {
    let diff = crate::hol::isabelle_corpus_diff::diff_corpora(&args.old, &args.new)
        .map_err(|e| MathverseCliError::IsabelleCorpusDiff(e.to_string()))?;
    crate::hol::isabelle_corpus_diff::write_diff(&args.out, &diff)
        .map_err(|e| MathverseCliError::IsabelleCorpusDiff(e.to_string()))?;
    let s = &diff.summary;
    println!(
        "CORPUS-DIFF: old {} lines (idx v{}) -> new {} lines (idx v{}) | unchanged {} | new {} | \
         changed {} | removed {} | {} -> {}",
        s.old_total,
        diff.old_idx_version,
        s.new_total,
        diff.new_idx_version,
        s.unchanged,
        s.new,
        s.changed,
        s.removed,
        if s.append_only {
            "APPEND-ONLY (incremental fast path)"
        } else {
            "NOT append-only (changed/removed lines present)"
        },
        args.out.display(),
    );
    Ok(())
}

pub(super) fn cmd_isabelle_verify_one(
    args: super::IsabelleVerifyOneArgs,
) -> Result<(), MathverseCliError> {
    let report = crate::hol::isabelle_verify_one::verify_one_line(
        &args.corpus,
        args.serial,
        args.snapshot.as_deref(),
        args.modes,
        args.full,
    )
    .map_err(|e| MathverseCliError::IsabelleVerifyOne(e.to_string()))?;

    let display_name = if report.name.is_empty() {
        format!("<anon.s{}>", report.serial)
    } else {
        report.name.clone()
    };
    let verdict = if report.already_accepted {
        "KernelVerified (already in snapshot closure)"
    } else if report.verified {
        "KernelVerified"
    } else {
        "REJECTED"
    };
    println!(
        "VERIFY-ONE: serial {} ({}) -> {} in {} ms [{}{}]",
        report.serial,
        display_name,
        verdict,
        report.wall_ms,
        if report.used_index { "index" } else { "scan" },
        if report.used_snapshot {
            "+snapshot"
        } else {
            "+minimal-state"
        },
    );
    if !report.deps.is_empty() {
        println!(
            "  deps: {} proof-term references, {} MISSING from the accepted closure",
            report.deps.len(),
            report.missing_deps.len()
        );
        if !report.missing_deps.is_empty() {
            let shown: Vec<String> = report
                .missing_deps
                .iter()
                .take(32)
                .map(|s| format!("s{s}"))
                .collect();
            let more = report.missing_deps.len().saturating_sub(shown.len());
            println!(
                "  MISSING-DEP (verify blocked until these verify): {}{}",
                shown.join(" "),
                if more > 0 {
                    format!(" … (+{more} more)")
                } else {
                    String::new()
                }
            );
        }
    }
    if !report.verified {
        for (reason, count) in &report.reasons {
            println!("  reason: {reason} x{count}");
        }
        for (specific, count) in &report.specifics {
            println!("  specific: {specific} x{count}");
        }
    }
    Ok(())
}

/// Map a Path-B batch error into the CLI error.
fn lean_goal_err(e: crate::hol::isabelle_lean_goal::batch::BatchError) -> MathverseCliError {
    MathverseCliError::IsabelleLeanGoal(e.to_string())
}

pub(super) fn cmd_isabelle_lean_goal(
    args: super::IsabelleLeanGoalArgs,
) -> Result<(), MathverseCliError> {
    use crate::hol::isabelle_lean_goal::types::LeanGoal;
    use crate::hol::isabelle_lean_goal::{batch, lean_name_from_isabelle, translate_prop};

    let corpus = &args.corpus;

    // Batch-prep mode: candidates → per-theorem stubs + manifest.
    if let Some(cands) = &args.candidates {
        let out_dir = args.out_dir.as_ref().ok_or_else(|| {
            MathverseCliError::IsabelleLeanGoal("--candidates requires --out-dir".to_string())
        })?;
        let serials = batch::read_candidate_serials(cands).map_err(lean_goal_err)?;
        let mut goals = Vec::with_capacity(serials.len());
        for s in serials {
            let line = batch::fetch_line_by_serial(corpus, s).map_err(lean_goal_err)?;
            goals.push(
                batch::prepare_from_line(format!("s{s}"), Some(s), &line).map_err(lean_goal_err)?,
            );
        }
        let report = batch::write_batch(out_dir, &goals).map_err(lean_goal_err)?;
        println!(
            "LEAN-GOAL BATCH: {} candidates -> {} supported, {} unsupported ({:.1}% coverage) at {}",
            report.total,
            report.supported,
            report.unsupported,
            report.coverage_pct(),
            out_dir.display()
        );
        return Ok(());
    }

    // Single-goal mode: fetch by serial or by name.
    let line = match (args.serial, &args.name) {
        (Some(s), _) => batch::fetch_line_by_serial(corpus, s).map_err(lean_goal_err)?,
        (None, Some(n)) => batch::fetch_line_by_name(corpus, n).map_err(lean_goal_err)?,
        (None, None) => {
            return Err(MathverseCliError::IsabelleLeanGoal(
                "single mode requires --serial or --name (or --candidates for batch)".to_string(),
            ))
        }
    };
    let (isabelle, prop) = batch::parse_line_prop(&line).map_err(lean_goal_err)?;
    let lean_name = args
        .lean_name
        .clone()
        .unwrap_or_else(|| lean_name_from_isabelle(&isabelle));

    println!("-- Isabelle: {isabelle}");
    match translate_prop(&prop, &lean_name) {
        LeanGoal::Supported(sg) => print!("{}", sg.sorry_stub()),
        LeanGoal::Unsupported(u) => println!("UNSUPPORTED: {u}"),
    }
    Ok(())
}

pub(super) fn cmd_isabelle_slice(args: super::IsabelleSliceArgs) -> Result<(), MathverseCliError> {
    let select = crate::hol::isabelle_slice::SliceSelect {
        serials: args.serials.iter().copied().collect(),
        name_substrings: args.names.clone(),
        reject_dump: args.reject_dump.clone(),
        reject_reason: args.reason.clone(),
        include_registrations: !args.no_registrations,
    };
    let report =
        crate::hol::isabelle_slice::extract_slice(&args.corpus, &args.out, &select).map_err(err)?;
    println!(
        "SLICE: {} seeds -> {} lines ({} bytes, {} registration lines) at {} ({} refs missing from corpus)",
        report.seeds,
        report.lines_out,
        report.bytes_out,
        report.registration_lines,
        args.out.display(),
        report.missing_refs
    );
    Ok(())
}
