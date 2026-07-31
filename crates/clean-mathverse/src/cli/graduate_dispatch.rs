// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean mathverse graduate` — CLI wrapper around the graduation intake
//! gate ([`crate::graduate::intake::graduate`]).
//!
//! The verb is a thin transcription layer: it builds the source environment,
//! digests the project manifest, pins the novelty baseline, runs the gate,
//! and immediately re-verifies the produced shard through
//! [`crate::shard_verify::cake_gate::verify_cake_shard`] so a CLI run can
//! never leave an unverified Cake shard behind.

use std::io::Write;
use std::path::PathBuf;

use clap::{Args, ValueEnum};
use clean_kernel::{ConstantKind, Environment, Name};
use serde_json::json;

use super::MathverseCliError;
use crate::build_library_native::seed_native_environment;
use crate::env_fingerprint::EnvFingerprint;
use crate::graduate::baseline_index::{build_baseline_index, BaselineIndex};
use crate::graduate::compact_record::extract_compact_record;
use crate::graduate::intake::{
    graduate_with_base_keep_env, GraduationBaseline, GraduationRequest, RecheckBase,
};
use crate::graduate::record::{
    blake3_file_digest, EnvProvenance, EvidenceClass, OnDuplicate, GRADUATION_SCHEMA_VERSION,
};
use crate::graduate::tree_score::{tree_score_verified_corpus, TreeScoreOptions, TREE_SCORE_FUEL};
use crate::shard_verify::cake_gate::verify_cake_shard_fused;

/// CLI mirror of [`OnDuplicate`] (record types stay clap-free).
#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum)]
pub enum OnDuplicateArg {
    /// Reject duplicate candidates.
    Reject,
    /// Reserved; behaves as reject in graduation v1.
    AcceptIfSharper,
}

impl From<OnDuplicateArg> for OnDuplicate {
    fn from(value: OnDuplicateArg) -> Self {
        match value {
            OnDuplicateArg::Reject => Self::Reject,
            OnDuplicateArg::AcceptIfSharper => Self::AcceptIfSharper,
        }
    }
}

/// CLI mirror of [`EvidenceClass`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum)]
pub enum EvidenceClassArg {
    /// Deterministic harness transcript backs this run.
    HarnessTranscribed,
    /// Agent-attested run without a deterministic transcript (default —
    /// honest floor for interactive CLI invocations).
    AgentAttested,
}

impl From<EvidenceClassArg> for EvidenceClass {
    fn from(value: EvidenceClassArg) -> Self {
        match value {
            EvidenceClassArg::HarnessTranscribed => Self::HarnessTranscribed,
            EvidenceClassArg::AgentAttested => Self::AgentAttested,
        }
    }
}

/// Source environment to graduate from.
#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum)]
pub enum GraduateEnvKind {
    /// The canonical native-pipeline environment
    /// ([`crate::build_library_native::seed_native_environment`] over a
    /// prelude environment) — the same shape `build-native` exports.
    Native,
    /// An environment imported from compiled Lean `.olean` modules via
    /// `clean-olean` (`load_module_with_deps`) — e.g. a lake-built project
    /// closure over mathlib. Requires `--olean-module` and
    /// `--olean-search-path`. The import is a *source* environment only:
    /// every accepted candidate is still re-checked from scratch by the
    /// live kernel in the gate's fresh recheck environment.
    Olean,
}

/// Arguments for `clean mathverse graduate`.
#[derive(Debug, Args)]
pub struct GraduateArgs {
    /// Path to the project manifest (digested and recorded; the project name
    /// is read from its top-level `project` JSON field when present).
    #[arg(long)]
    pub project: PathBuf,
    /// Source environment to graduate from.
    #[arg(long, value_enum, default_value_t = GraduateEnvKind::Native)]
    pub env: GraduateEnvKind,
    /// Lean module names to import (transitive closure, dependency order)
    /// when `--env olean`, e.g. `Crownproof.Bridge`. Repeatable /
    /// comma-separated; modules share one environment (deduplicated).
    #[arg(long, value_delimiter = ',')]
    pub olean_module: Vec<String>,
    /// `.olean` search-path roots for `--env olean` (project build dir,
    /// package build dirs, toolchain `lib/lean`). Repeatable. Usually unnecessary —
    /// prefer `--lake-project`, which derives all of these automatically.
    #[arg(long)]
    pub olean_search_path: Vec<PathBuf>,
    /// Lake project root (e.g. `crown-proofs/lean`). Auto-derives the `--olean-search-path`s
    /// so you don't list them by hand: the project's own `.lake/build/lib/lean`, every
    /// `.lake/packages/*/.lake/build/lib/lean`, and the toolchain `lib/lean` resolved from the
    /// project's `lean-toolchain`. Merged with any explicit `--olean-search-path`. When given,
    /// it also defaults `--olean-source-root` to this root (enabling the freshness check).
    #[arg(long)]
    pub lake_project: Option<PathBuf>,
    /// Comma-separated candidate theorem names.
    #[arg(long, value_delimiter = ',', required_unless_present = "all")]
    pub candidates: Vec<String>,
    /// Graduate every theorem-kind constant in the environment (the gate
    /// records a rejection for everything that does not qualify).
    #[arg(long, conflicts_with = "candidates")]
    pub all: bool,
    /// Novelty baseline: a `.mathverse` shard file or a directory of shards.
    #[arg(long, default_value = "data/mathverse-shards")]
    pub baseline: PathBuf,
    /// Novelty baseline as a prebuilt `MVBIDX01` index file (see
    /// `clean mathverse index-build`). Loads in seconds where `--baseline`
    /// re-scans shards; takes precedence over `--baseline` when given.
    #[arg(long)]
    pub baseline_index: Option<PathBuf>,
    /// Label recorded as the pinned baseline release.
    #[arg(long, default_value = "local-shards")]
    pub baseline_release: String,
    /// Output directory for the graduated shard + record.
    #[arg(long)]
    pub out: PathBuf,
    /// Duplicate policy.
    #[arg(long, value_enum, default_value_t = OnDuplicateArg::Reject)]
    pub on_duplicate: OnDuplicateArg,
    /// Attempt-log id to record.
    #[arg(long)]
    pub attempt_id: Option<String>,
    /// Replay-archive manifest sha256 to record.
    #[arg(long)]
    pub replay_sha256: Option<String>,
    /// Proof-engine label to record.
    #[arg(long)]
    pub engine: Option<String>,
    /// Engine seed to record.
    #[arg(long)]
    pub seed: Option<String>,
    /// Evidence class (design §7 honesty label).
    #[arg(long, value_enum, default_value_t = EvidenceClassArg::AgentAttested)]
    pub evidence_class: EvidenceClassArg,
    /// Mandatory residual-risk honesty field (may be `none-known`).
    #[arg(long, default_value = "unreviewed")]
    pub residual_risk: String,
    /// Pin the graduation decision time (epoch seconds) instead of reading the
    /// wall clock. The decision timestamp is the only wall-clock value that
    /// reaches the shard bytes; pinning it makes the shard reproducible
    /// byte-for-byte for verify-by-digest and attestation replay. Omit for
    /// normal runs.
    #[arg(long)]
    pub decided_at: Option<u64>,
    /// Project source root holding the `.lean` files for the declared
    /// `--olean-module`s (e.g. `crown-proofs/lean`). When given, Cake checks that
    /// each declared module's `.olean` is content-fresh vs its source (the
    /// import-list signature) and records the build provenance in the graduation
    /// record. Without it, freshness is not checked (legacy behavior).
    #[arg(long)]
    pub olean_source_root: Option<PathBuf>,
    /// Fail closed if Cake reports any declared module stale (requires
    /// `--olean-source-root`). Default: warn + record the staleness, still graduate.
    #[arg(long)]
    pub require_fresh: bool,
    /// Compute + record each candidate's Cake semantic identity — the env-free Tier-1.5
    /// `structural_rewrite_digest` that catches "same object, different form". FAST (no kernel
    /// normalisation); the corpus + intra-run novelty probes use it. Off by default (records
    /// stay byte-identical).
    #[arg(long)]
    pub score: bool,
    /// ALSO compute the expensive defeq Tier-1 identity (kernel `whnf` normalisation, bounded).
    /// Implies `--score`. Can be slow on heavy mathlib-Real statements; off by default.
    #[arg(long)]
    pub score_defeq: bool,
    /// Emit JSON instead of the human-readable summary.
    #[arg(long)]
    pub json: bool,
}

/// Arguments for `clean mathverse index-build`.
#[derive(Debug, Args)]
pub struct IndexBuildArgs {
    /// Release directory (or single `.mathverse` shard file) to index.
    pub release_dir: PathBuf,
    /// Output path for the `MVBIDX01` index file.
    #[arg(short, long)]
    pub out: PathBuf,
    /// After building, re-derive N statement hashes per shard through the
    /// independent per-constant scan path (`GraduationBaseline::load`'s
    /// reconstruction) and fail if any index lookup disagrees.
    #[arg(long, default_value_t = 0)]
    pub check_sample: u32,
    /// Emit JSON instead of the human-readable summary.
    #[arg(long)]
    pub json: bool,
}

pub(crate) fn cmd_index_build(args: IndexBuildArgs) -> Result<(), MathverseCliError> {
    let started = std::time::Instant::now();
    let stats = build_baseline_index(&args.release_dir, &args.out)?;
    let build_secs = started.elapsed().as_secs_f64();

    let load_started = std::time::Instant::now();
    let index = BaselineIndex::load(&args.out)?;
    let load_secs = load_started.elapsed().as_secs_f64();
    let checked = check_sample_against_scan(&args.release_dir, &index, args.check_sample)?;

    let stdout = std::io::stdout();
    let mut out = stdout.lock();
    if args.json {
        let payload = json!({
            "schema": "mathverse-baseline-index-v2",
            "index": args.out,
            "shards": stats.shards,
            "constants": stats.constants,
            "names": stats.names,
            "statement_hashes": stats.hashes,
            "semantic_hashes": stats.semantic_hashes,
            "skipped_hashes": stats.skipped_hashes,
            "index_bytes": stats.index_bytes,
            "corpus_digest": stats.corpus_digest,
            "build_seconds": build_secs,
            "load_seconds": load_secs,
            "check_sample": { "requested_per_shard": args.check_sample, "verified": checked },
        });
        writeln!(out, "{}", serde_json::to_string_pretty(&payload)?)?;
    } else {
        writeln!(
            out,
            "indexed {} constants ({} names, {} statement hashes, {} semantic hashes, \
             {} hash-skipped) from {} shard(s) in {build_secs:.1}s — {} ({} bytes, \
             loads in {load_secs:.2}s)",
            stats.constants,
            stats.names,
            stats.hashes,
            stats.semantic_hashes,
            stats.skipped_hashes,
            stats.shards,
            args.out.display(),
            stats.index_bytes,
        )?;
        if args.check_sample > 0 {
            writeln!(
                out,
                "check-sample: {checked} lookups verified against the direct shard scan"
            )?;
        }
    }
    Ok(())
}

/// Arguments for `clean mathverse index-tree-score`.
#[derive(Debug, Args)]
pub struct IndexTreeScoreArgs {
    /// Directory of `stamp-verified` `.mathverse` shards (or a single shard) to
    /// score. Only constants stamped at the confidence floor participate.
    pub shard_dir: PathBuf,
    /// Optional path to write the JSON report (MVBIDX stats + kernel-confirmed
    /// uniqueness hits). When omitted, the report goes to stdout with `--json`.
    #[arg(short, long)]
    pub out: Option<PathBuf>,
    /// `whnf` fuel for the kernel-confirmed defeq tree-signature.
    #[arg(long, default_value_t = TREE_SCORE_FUEL)]
    pub fuel: u32,
    /// Cap on confirmed same-tree-signature hits surfaced in the report
    /// (`0` = unbounded).
    #[arg(long, default_value_t = 256)]
    pub max_hits: usize,
    /// Emit JSON instead of the human-readable summary.
    #[arg(long)]
    pub json: bool,
}

/// `clean mathverse index-tree-score` entry point.
///
/// Computes the kernel-confirmed tree-score over a directory of verified shards:
/// every `KernelVerified` constant's type is reduced to its defeq tree-signature,
/// distinct-form collisions are confirmed with the kernel `is_def_eq` arbiter,
/// and the MVBIDX stats + confirmed hits are reported. SOUNDNESS: a shared
/// tree-signature is only a *candidate*; every reported hit carries the kernel's
/// `is_def_eq` verdict. Shards and stamps are never modified.
pub(crate) fn cmd_index_tree_score(args: IndexTreeScoreArgs) -> Result<(), MathverseCliError> {
    let started = std::time::Instant::now();
    let opts = TreeScoreOptions {
        fuel: args.fuel,
        max_hits: args.max_hits,
        ..TreeScoreOptions::default()
    };
    let stats = tree_score_verified_corpus(&args.shard_dir, &opts)?;
    let elapsed = started.elapsed().as_secs_f64();

    // Also build the persistent MVBIDX over the same shard dir so the report
    // carries the index stats (name/hash/semantic counts, corpus_digest) the
    // verified corpus needs alongside the kernel-confirmed tree-score.
    let index_out =
        std::env::temp_dir().join(format!("mvbidx-tree-score-{}.mvix", std::process::id()));
    let index_stats = build_baseline_index(&args.shard_dir, &index_out)?;
    let _ = std::fs::remove_file(&index_out);

    let hits: Vec<_> = stats
        .hits
        .iter()
        .map(|h| {
            json!({
                "name_a": h.name_a,
                "name_b": h.name_b,
                "tree_signature": h.tree_signature,
                "form": h.form.label(),
                "complete": h.complete,
                "same_object": h.same_object,
            })
        })
        .collect();

    let payload = json!({
        "schema": "mathverse-tree-score-index-v1",
        "shard_dir": args.shard_dir,
        "mvbidx": {
            "shards": index_stats.shards,
            "constants": index_stats.constants,
            "names": index_stats.names,
            "statement_hashes": index_stats.hashes,
            "semantic_hashes": index_stats.semantic_hashes,
            "skipped_hashes": index_stats.skipped_hashes,
            "corpus_digest": index_stats.corpus_digest,
        },
        "kernel_confirmed_tree_score": {
            "min_confidence": "KernelVerified",
            "fuel": args.fuel,
            "shards": stats.shards,
            "constants": stats.constants,
            "scored": stats.scored,
            "complete": stats.complete,
            "distinct_tree_signatures": stats.distinct_tree_signatures,
            "different_form_pairs": stats.different_form_pairs,
            "literal_duplicate_pairs": stats.literal_duplicate_pairs,
            "confirmed_same_object": stats.confirmed_same_object,
            "confirmed_different_form": stats.confirmed_different_form,
            "corpus_digest": stats.corpus_digest,
            "hits": hits,
        },
        "elapsed_seconds": elapsed,
    });

    if let Some(out_path) = &args.out {
        if let Some(parent) = out_path.parent() {
            if !parent.as_os_str().is_empty() {
                std::fs::create_dir_all(parent)?;
            }
        }
        std::fs::write(out_path, serde_json::to_string_pretty(&payload)?)?;
    }

    let stdout = std::io::stdout();
    let mut out = stdout.lock();
    if args.json || args.out.is_none() {
        writeln!(out, "{}", serde_json::to_string_pretty(&payload)?)?;
    } else {
        writeln!(
            out,
            "tree-score: scored {} KernelVerified decl(s) of {} ({} complete) from {} shard(s); \
             {} distinct tree-signatures; candidates: {} different-form + {} literal-duplicate; \
             kernel-confirmed same-object: {} ({} different-form) in {elapsed:.1}s",
            stats.scored,
            stats.constants,
            stats.complete,
            stats.shards,
            stats.distinct_tree_signatures,
            stats.different_form_pairs,
            stats.literal_duplicate_pairs,
            stats.confirmed_same_object,
            stats.confirmed_different_form,
        )?;
        writeln!(
            out,
            "  MVBIDX: {} names, {} statement hashes, {} semantic hashes; corpus {}",
            index_stats.names,
            index_stats.hashes,
            index_stats.semantic_hashes,
            index_stats.corpus_digest,
        )?;
        if let Some(out_path) = &args.out {
            writeln!(out, "  report -> {}", out_path.display())?;
        }
    }
    Ok(())
}

/// Arguments for `clean mathverse graduation-record`.
#[derive(Debug, Args)]
pub struct GraduationRecordArgs {
    /// Path to the full `mathverse-graduation-v3.x` `.graduation.json` record.
    #[arg(long)]
    pub from: PathBuf,
    /// Path to the produced `.mathverse` shard (the heavy Layer-2 artifact this
    /// record pins by blake3).
    #[arg(long)]
    pub shard: PathBuf,
    /// Output path for the compact `mathverse-graduation-record-v1` JSON. When
    /// omitted, the record is written to stdout.
    #[arg(long)]
    pub out: Option<PathBuf>,
}

/// `clean mathverse graduation-record` — project a full graduation record + its
/// shard into the compact `mathverse-graduation-record-v1` git artifact.
///
/// SOUNDNESS: pure projection. The verb transcribes the gate's already-decided
/// verdict and recomputes only the shard's blake3 + byte length (a content
/// check). It never re-runs the kernel, the gate, or any proof.
pub(crate) fn cmd_graduation_record(args: GraduationRecordArgs) -> Result<(), MathverseCliError> {
    let record = extract_compact_record(&args.from, &args.shard)?;
    let json = record.to_pretty_json()?;

    if let Some(out_path) = &args.out {
        if let Some(parent) = out_path.parent() {
            if !parent.as_os_str().is_empty() {
                std::fs::create_dir_all(parent)?;
            }
        }
        std::fs::write(out_path, &json)?;
        let stdout = std::io::stdout();
        let mut out = stdout.lock();
        writeln!(
            out,
            "wrote compact record for `{}` ({} theorem(s), shard {}) -> {}",
            record.project,
            record.theorems.len(),
            record.shard.blake3,
            out_path.display()
        )?;
    } else {
        let stdout = std::io::stdout();
        let mut out = stdout.lock();
        writeln!(out, "{json}")?;
    }
    Ok(())
}

/// Independently re-derive `per_shard` (name, statement-hash) pairs per
/// shard via the per-constant reconstruction path and assert the index
/// agrees. Returns the number of verified lookups.
fn check_sample_against_scan(
    input: &std::path::Path,
    index: &BaselineIndex,
    per_shard: u32,
) -> Result<u64, MathverseCliError> {
    use crate::shard::ShardReader;
    use crate::shard_reconstruct::reconstruct_from_shard_with_level_lists;

    if per_shard == 0 {
        return Ok(0);
    }
    let mut verified = 0u64;
    for shard_path in crate::graduate::intake::collect_shard_paths(input)? {
        let bytes = std::fs::read(&shard_path)?;
        let reader = ShardReader::from_bytes(&bytes)?;
        if reader.constants.is_empty() {
            continue;
        }
        // Deterministic spread: evenly spaced constants, including the last.
        let n = reader.constants.len();
        for k in 0..per_shard as usize {
            let pick = if per_shard == 1 {
                n - 1
            } else {
                (k * (n - 1)) / (per_shard as usize - 1)
            };
            let header = &reader.constants[pick];
            let Some(name) = reader.strings.get(header.name_idx as usize) else {
                continue;
            };
            if !index.contains_name(name) {
                return Err(MathverseCliError::IndexCheck(format!(
                    "`{name}` ({}) missing from name table",
                    shard_path.display()
                )));
            }
            let Ok(type_) = reconstruct_from_shard_with_level_lists(
                &reader.exprs,
                &reader.levels,
                &reader.strings,
                &reader.level_lists,
                header.type_idx,
            ) else {
                continue; // name-only constant in both paths
            };
            let digest = crate::graduate::record::expr_canonical_digest(&type_)?;
            if index.lookup_statement_hash(&digest).is_none() {
                return Err(MathverseCliError::IndexCheck(format!(
                    "statement hash of `{name}` ({}) missing from hash table",
                    shard_path.display()
                )));
            }
            // v2 semantic-table round-trip: the same reconstructed type's env-free Tier-1.5
            // digest must be served by the semantic table (gated on expr_canonical_digest
            // success exactly as the builder is). v1 indexes have no table — skip then.
            if index.semantic_count() > 0 {
                let sem = clean_cake::identity::structural_rewrite_digest(&type_);
                if index.lookup_semantic(&sem).is_none() {
                    return Err(MathverseCliError::IndexCheck(format!(
                        "semantic digest of `{name}` ({}) missing from semantic table",
                        shard_path.display()
                    )));
                }
            }
            verified += 1;
        }
    }
    Ok(verified)
}

pub(crate) fn cmd_graduate(args: GraduateArgs) -> Result<(), MathverseCliError> {
    // Mathlib-scale `--env olean` source environments contain deep
    // expression trees; dependency resolution, canonical hashing, and the
    // kernel re-check all recurse over them. Run the whole gate on a
    // 1 GiB-stack worker thread (the same discipline as the ny_bridge
    // import harness) so legitimately deep proof terms cannot overflow the
    // default main-thread stack.
    const GATE_STACK_BYTES: usize = 1024 * 1024 * 1024;
    std::thread::Builder::new()
        .name("mathverse-graduate".to_string())
        .stack_size(GATE_STACK_BYTES)
        .spawn(move || cmd_graduate_on_thread(args))
        .map_err(MathverseCliError::Io)?
        .join()
        .map_err(|_| {
            MathverseCliError::GraduationGate("graduation worker thread panicked".to_string())
        })?
}

fn cmd_graduate_on_thread(args: GraduateArgs) -> Result<(), MathverseCliError> {
    let env = build_environment(&args)?;
    let candidates = candidate_names(&args, &env);
    let baseline = match &args.baseline_index {
        Some(index_path) => GraduationBaseline::from_index(index_path)?,
        // Best default: if the caller did not override `--baseline`, auto-select the newest
        // released corpus index (`_mathverse-artifacts/*.mvix`) — the real corpus, in seconds —
        // instead of re-scanning the (usually empty) default shard dir.
        None => {
            let baseline_overridden =
                args.baseline.as_path() != std::path::Path::new("data/mathverse-shards");
            match (baseline_overridden, auto_baseline_index()) {
                (false, Some(idx)) => {
                    eprintln!(
                        "[graduate] auto-selected baseline index {} (newest \
                         _mathverse-artifacts/*.mvix; pass --baseline-index/--baseline to override)",
                        idx.display()
                    );
                    GraduationBaseline::from_index(&idx)?
                }
                _ => GraduationBaseline::load(&args.baseline)?,
            }
        }
    };
    let mut req = build_request(&args)?;

    // Cake build-provenance + content-hash freshness gate. When the caller points us
    // at the project's `.lean` sources, Cake checks that each declared `--olean-module`
    // is content-fresh vs its source (the import-list signature that would have caught
    // the stale-root-olean incident), records the fingerprint in the graduation record,
    // and — under `--require-fresh` — refuses to grade a stale environment.
    // `--lake-project` doubles as the freshness source root when `--olean-source-root` is absent.
    let effective_source_root = args
        .olean_source_root
        .as_ref()
        .or(args.lake_project.as_ref());
    if let (GraduateEnvKind::Olean, Some(source_root)) = (args.env, effective_source_root) {
        let toolchain = std::fs::read_to_string(source_root.join("lean-toolchain"))
            .ok()
            .map(|s| s.trim().to_string());
        let sig = clean_cake::signature_from_search_paths(
            &args.olean_module,
            source_root,
            &resolve_olean_search_paths(&args),
            toolchain,
        );
        if !sig.fresh {
            let summary = sig
                .staleness_summary()
                .unwrap_or_else(|| "stale build environment".to_string());
            if args.require_fresh {
                return Err(MathverseCliError::GraduateOleanEnv(format!(
                    "--require-fresh: {summary}"
                )));
            }
            eprintln!("[graduate] WARNING (cake freshness): {summary}");
        } else {
            eprintln!(
                "[graduate] cake freshness: all {} declared module(s) fresh (env_digest {})",
                sig.modules.len(),
                sig.env_digest
            );
        }
        req.env_provenance = Some(EnvProvenance {
            schema: sig.schema,
            env_digest: sig.env_digest,
            toolchain: sig.toolchain,
            fresh: sig.fresh,
            stale_modules: sig.stale_modules,
        });
    }

    // v3.2: `.olean`-sourced runs are decided against the shadow-free
    // Lean-core recheck base (the imported toolchain is the source of truth;
    // Clean's prelude must never silently substitute for it). Native runs
    // keep the Clean prelude, which IS their source of truth.
    let base = match args.env {
        GraduateEnvKind::Native => RecheckBase::CleanPrelude,
        GraduateEnvKind::Olean => RecheckBase::LeanCore,
    };
    eprintln!(
        "[graduate] recheck base: {} (env {:?})",
        base.record_label(),
        args.env
    );
    let (record, mut recheck) =
        graduate_with_base_keep_env(&env, &candidates, &req, &baseline, &args.out, base)?;
    let shard_path = args.out.join(&record.result.shard_filename);

    // Self-check: the produced shard must pass the cake gate before the verb
    // reports success. Fail-closed on any violation. ENV-FUSION: discharge the
    // gate's per-constant kernel clause from the primary gate's just-completed
    // recheck env (round-trip oracle against the shard bytes) instead of a
    // second, identical, dominant-cost full kernel pass in the same process.
    let gate = verify_cake_shard_fused(&shard_path, &mut recheck)
        .map_err(|e| MathverseCliError::GraduationGate(e.to_string()))?;
    if !gate.is_clean() {
        let reasons: Vec<String> = gate
            .violations
            .iter()
            .map(|v| format!("{}: {}", v.name(), v.reason()))
            .collect();
        return Err(MathverseCliError::GraduationGate(reasons.join("; ")));
    }

    let stdout = std::io::stdout();
    let mut out = stdout.lock();
    if args.json {
        let carried: Vec<&str> = record
            .carried_definitions
            .iter()
            .map(|d| d.name.as_str())
            .collect();
        let carried_families: Vec<&str> = record
            .carried_inductives
            .iter()
            .map(|f| f.name.as_str())
            .collect();
        let carried_thms: Vec<&str> = record
            .carried_theorems
            .iter()
            .map(|t| t.name.as_str())
            .collect();
        let payload = json!({
            "schema": GRADUATION_SCHEMA_VERSION,
            "shard": shard_path,
            "record": crate::graduate::record::graduation_record_path(&shard_path),
            "accepted": record.result.accepted,
            "rejected": record.result.rejected,
            "carried_definitions": carried,
            "carried_inductives": carried_families,
            "carried_theorems": carried_thms,
            "shard_digest": record.result.shard_digest,
            "cake_gate": { "checked": gate.checked, "violations": 0 },
        });
        writeln!(out, "{}", serde_json::to_string_pretty(&payload)?)?;
    } else {
        writeln!(
            out,
            "graduated {} theorem(s), rejected {} — shard: {} (cake gate: clean)",
            record.result.accepted.len(),
            record.result.rejected.len(),
            shard_path.display()
        )?;
        for entry in &record.theorems {
            let status = if entry.accepted {
                "ACCEPT".to_string()
            } else {
                format!(
                    "REJECT ({})",
                    entry.reject_reason.as_deref().unwrap_or("unspecified")
                )
            };
            writeln!(out, "  {:<50} {}", entry.name, status)?;
        }
    }
    Ok(())
}

fn build_environment(args: &GraduateArgs) -> Result<Environment, MathverseCliError> {
    match args.env {
        GraduateEnvKind::Native => {
            let mut env = Environment::with_prelude();
            seed_native_environment(&mut env);
            Ok(env)
        }
        GraduateEnvKind::Olean => build_olean_environment(args),
    }
}

/// Import the requested `.olean` modules (one shared, deduplicated
/// environment — the ny_bridge loading path) and return it as the
/// graduation source environment. Per-module progress goes to stderr: a
/// mathlib-scale closure load is minutes long and must be observable.
/// Derive `.olean` search paths from a lake project root (the `.lake/build` layout):
/// the project's own `.lake/build/lib/lean`, every `.lake/packages/*/.lake/build/lib/lean`
/// (sorted, for determinism), and the toolchain `lib/lean` resolved from `<root>/lean-toolchain`
/// (e.g. `leanprover/lean4:v4.30.0` → `~/.elan/toolchains/leanprover--lean4---v4.30.0/lib/lean`).
fn lake_project_search_paths(root: &std::path::Path) -> Vec<PathBuf> {
    let mut paths = Vec::new();
    let build_lib = root.join(".lake/build/lib/lean");
    if build_lib.exists() {
        paths.push(build_lib);
    }
    if let Ok(rd) = std::fs::read_dir(root.join(".lake/packages")) {
        let mut pkgs: Vec<PathBuf> = rd
            .filter_map(|e| e.ok())
            .map(|e| e.path().join(".lake/build/lib/lean"))
            .filter(|p| p.exists())
            .collect();
        pkgs.sort();
        paths.extend(pkgs);
    }
    if let Ok(tc) = std::fs::read_to_string(root.join("lean-toolchain")) {
        let dir = tc.trim().replace('/', "--").replace(':', "---");
        if let (false, Some(home)) = (dir.is_empty(), std::env::var_os("HOME")) {
            let tcp = PathBuf::from(home)
                .join(".elan/toolchains")
                .join(&dir)
                .join("lib/lean");
            if tcp.exists() {
                paths.push(tcp);
            }
        }
    }
    paths
}

/// Effective olean search paths: `--lake-project`-derived (if any), then explicit
/// `--olean-search-path`s, de-duplicated and order-preserving.
fn resolve_olean_search_paths(args: &GraduateArgs) -> Vec<PathBuf> {
    let mut seen = std::collections::HashSet::new();
    let mut out = Vec::new();
    let mut add = |p: PathBuf, out: &mut Vec<PathBuf>| {
        if seen.insert(p.clone()) {
            out.push(p);
        }
    };
    if let Some(root) = &args.lake_project {
        for p in lake_project_search_paths(root) {
            add(p, &mut out);
        }
    }
    for p in &args.olean_search_path {
        add(p.clone(), &mut out);
    }
    out
}

/// The "best default" novelty baseline: the newest `_mathverse-artifacts/*.mvix` — the real
/// released corpus index (with the v2 semantic table), loading in seconds. `None` if absent.
fn auto_baseline_index() -> Option<PathBuf> {
    let rd = std::fs::read_dir("_mathverse-artifacts").ok()?;
    let mut mvix: Vec<PathBuf> = rd
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|x| x == "mvix"))
        .collect();
    // Newest by mtime — the most recently built index (the v2 corpus index).
    mvix.sort_by_key(|p| std::fs::metadata(p).and_then(|m| m.modified()).ok());
    mvix.pop()
}

fn build_olean_environment(args: &GraduateArgs) -> Result<Environment, MathverseCliError> {
    if args.olean_module.is_empty() {
        return Err(MathverseCliError::GraduateOleanEnv(
            "--env olean requires at least one --olean-module".to_string(),
        ));
    }
    let search_paths = resolve_olean_search_paths(args);
    if search_paths.is_empty() {
        return Err(MathverseCliError::GraduateOleanEnv(
            "--env olean requires olean search paths: pass --lake-project <root> (recommended, \
             auto-derives them) or one or more --olean-search-path"
                .to_string(),
        ));
    }
    let started = std::time::Instant::now();

    // CONTENT-ADDRESSED CLOSURE CACHE (opt-in via $CLEAN_CLOSURE_CACHE_DIR; bypassed
    // when unset — zero default behavior change). A warm HIT fast-loads the
    // digest-bound closure from cached shards (inductives eager-from-olean,
    // definitional from shards) instead of re-converting every proof term. A MISS
    // cold-loads exactly as below, then best-effort populates the cache. The cache
    // is a LOAD ACCELERATOR, never in the TCB: every candidate is re-checked
    // downstream, and a digest/coverage/binding mismatch fails closed to this same
    // eager reconstruction. See `graduate_closure_cache`.
    use crate::cli::graduate_closure_cache::{decide, populate, CacheDecision};
    let cache = decide(
        &args.olean_module,
        &search_paths,
        args.lake_project.as_deref(),
    );
    let cold_plan = match cache {
        CacheDecision::Hit(env) => {
            eprintln!(
                "[graduate --env olean] closure cache HIT: warm-loaded {} module(s) (env total {}) [{:.1}s]",
                args.olean_module.len(),
                env.constants().count(),
                started.elapsed().as_secs_f64()
            );
            return Ok(*env);
        }
        CacheDecision::Miss(plan) => Some(plan),
        CacheDecision::Disabled => None,
    };

    let mut env = Environment::default();
    eprintln!(
        "[graduate --env olean] loading {} module(s) in one shared pass: {} ...",
        args.olean_module.len(),
        args.olean_module.join(", ")
    );
    // Single shared-visited pass over the UNION of the modules' closures. The previous
    // per-module loop re-read the shared mathlib closure once per module (O(modules ×
    // closure) of redundant .olean reads — a second mathlib module took >70min on top of
    // the first's 13min). `load_modules_with_deps` shares `visited`, so later modules skip
    // every already-loaded dependency.
    let summaries =
        clean_olean::load_modules_with_deps(&mut env, &args.olean_module, &search_paths)
            .map_err(|e| MathverseCliError::GraduateOleanEnv(format!("loading modules: {e}")))?;
    let added: usize = summaries.iter().map(|s| s.added_constants).sum();
    let skipped: usize = summaries.iter().map(|s| s.skipped_constants.len()).sum();
    eprintln!(
        "[graduate --env olean] loaded: added={added} skipped={skipped} (env total {}) [{:.1}s]",
        env.constants().count(),
        started.elapsed().as_secs_f64()
    );
    // Best-effort cache populate (never fails the load).
    if let Some(plan) = cold_plan {
        populate(&plan);
    }
    Ok(env)
}

fn candidate_names(args: &GraduateArgs, env: &Environment) -> Vec<Name> {
    if args.all {
        let mut names: Vec<Name> = env
            .constants()
            .filter(|c| c.kind == ConstantKind::Theorem)
            .map(|c| c.name.clone())
            .collect();
        names.sort_by_key(Name::to_string);
        names
    } else {
        args.candidates
            .iter()
            .map(|n| Name::from_string(n))
            .collect()
    }
}

fn build_request(args: &GraduateArgs) -> Result<GraduationRequest, MathverseCliError> {
    let manifest_digest = blake3_file_digest(&args.project)?;
    let project_name = project_name_from_manifest(&args.project);
    let clean_commit = EnvFingerprint::capture(".").ok().map(|fp| fp.clean_commit);
    Ok(GraduationRequest {
        project_name,
        manifest_kind: "clean-math-project-v1".to_string(),
        manifest_digest,
        certificate_schema: None,
        certificate_cross_checks: Vec::new(),
        mathverse_release: args.baseline_release.clone(),
        on_duplicate: args.on_duplicate.into(),
        attempt_id: args.attempt_id.clone(),
        replay_archive_sha256: args.replay_sha256.clone(),
        engine: args.engine.clone(),
        seed: args.seed.clone(),
        evidence_class: args.evidence_class.into(),
        residual_risk: args.residual_risk.clone(),
        clean_commit,
        shard_filename: None,
        decided_at_epoch_s: args.decided_at,
        // Populated in `cmd_graduate_on_thread` once the environment + freshness
        // check have run (only when `--olean-source-root` is given).
        env_provenance: None,
        score_identity: args.score || args.score_defeq,
        score_defeq: args.score_defeq,
    })
}

/// Read the `project` field from the manifest JSON; fall back to file stem.
fn project_name_from_manifest(path: &std::path::Path) -> String {
    let fallback = || {
        path.file_stem()
            .map(|s| s.to_string_lossy().into_owned())
            .unwrap_or_else(|| "project".to_string())
    };
    let Ok(bytes) = std::fs::read(path) else {
        return fallback();
    };
    let Ok(value) = serde_json::from_slice::<serde_json::Value>(&bytes) else {
        return fallback();
    };
    value
        .get("project")
        .and_then(|v| v.as_str())
        .map(str::to_string)
        .unwrap_or_else(fallback)
}
