// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Streaming, bounded-memory closure-replay driver:
//! `import_proven_theorems_streaming` plus the per-registry pre-pass
//! `collect_*` line filters.

use std::collections::BTreeMap;
use std::io::BufRead as _;
use std::path::{Path, PathBuf};

use clean_kernel::{Declaration, Environment};

use super::super::isabelle_pure::{parse_proven_theorem, IsaProvenTheorem};
use super::super::isabelle_pure_translate::{
    bnf_combinator_definition_decls, bnf_opaque_combinator_definition_decls,
    class_def_superclasses, connective_definition_decls, extremum_definition_decls,
    fun_combinator_definition_decls, fun_comp_definition_decl, fun_id_definition_decl,
    hol_if_definition_decl, hol_the_definition_decl, pointfree_definition_decls,
    pure_meta_definition_decls, register_datatype_inductives, wo_the_definition_decls,
    ClassRegistry, Closure, InstanceOpRegistry, ListFnRegistry, MethodRegistry, PolyInstRegistry,
};
use super::batch::verify_one;
use super::register::{
    register_classes_superclass_first, register_instance_ops, register_list_fns, register_methods,
    register_poly_insts,
};
use super::{PureVerifiedImport, StreamError};
use crate::shard::ShardWriter;

/// Streaming, bounded-memory closure-replay driver — verifies a corpus far
/// larger than RAM by reading a **serial-ascending-sorted** `.jsonl` closure
/// file line-by-line, never holding the whole parsed corpus in memory.
///
/// # Why serial order is a valid topological order
///
/// Isabelle assigns proof-term serials in **creation order**, and a theorem's
/// `PThm` dependencies are always created before it — so every dependency has a
/// **strictly smaller serial**. Reading the corpus in serial-ascending order
/// therefore presents every theorem *after* all of its in-corpus dependencies,
/// which is exactly the deps-before-uses invariant the batch driver's
/// `topological_order` establishes — without the batch driver's O(n²) all-pairs
/// dependency-graph build or its requirement to hold the entire parsed corpus in
/// a `Vec`. The caller must pass a file already sorted by the numeric `serial`
/// field; the companion test (`tests/isabelle_scale_run.rs`, `ISA_CLOSURE_STREAM`)
/// shows the one-line stable external sort (`sort -n` on the serial key) that
/// produces it.
///
/// # Peak memory
///
/// Bounded by the **accumulating state** — the `Environment`, the `Closure`
/// (compact embedded *types* keyed by serial), the `ClassRegistry`, and the
/// `PureVerifiedImport` counters — **plus one parsed theorem at a time**. The raw
/// JSON line and the parsed `IsaProvenTheorem` are dropped immediately after each
/// theorem is processed, so the multi-GB corpus file is never materialised in
/// memory.
///
/// # Class definitions
///
/// The `…c_class_def` axioms are bare `PAxm` leaves with no `PThm` dependencies,
/// so they cannot be ordered by the closure graph; the batch driver registers
/// them up front in superclass-first order via
/// [`register_classes_superclass_first`]. The streaming driver reproduces that
/// **identical** registry with a cheap **pre-pass**: it streams the file once,
/// parses only the (few hundred) lines that are class-def axioms, and runs the
/// very same `register_classes_superclass_first` fixpoint over just that subset
/// (the function only ever acts on class-def lines, so the subset yields a
/// bit-identical registry). A single forward pass would already encounter each
/// superclass's def before its subclasses' (superclass theory loads first → its
/// `_class_def` has a smaller serial), but driving the shared fixpoint guarantees
/// exact parity with the batch driver regardless.
///
/// # Soundness
///
/// Identical to [`import_proven_theorems`]: each theorem is re-checked by the
/// kernel in the accumulating environment, and only theorems the kernel accepts
/// with a foundational-only axiom closure are stamped `KernelVerified`. Order
/// independence (given deps-before-uses) makes the result identical to the batch
/// driver's.
///
/// # Errors
///
/// Returns [`StreamError::Io`] if the serial-sorted file cannot be opened or a
/// read fails. Per-theorem rejections are tallied, not errored.
pub fn import_proven_theorems_streaming(
    serial_sorted_path: impl AsRef<Path>,
    writer: &mut ShardWriter,
) -> Result<PureVerifiedImport, StreamError> {
    stream_with_recorder(serial_sorted_path.as_ref(), writer, None, None)
}

/// Shared streaming-replay body. When `recorder` is present it additionally
/// captures the per-line verdict for the line indices in its shard range (see
/// [`super::shard_verify`]); the recorder is a pure observer and never influences
/// a verdict. `recorder == None` reproduces [`import_proven_theorems_streaming`]
/// byte-for-byte — the recorder hooks are the only added code and they are
/// inert (a single `is_some_and` per line) when it is absent.
///
/// `prepass == Some(path)` is the **shard pre-pass hand-off** (see
/// [`super::shard_verify::export_prepass_snapshot`]): instead of scanning the
/// corpus to rebuild the five PASS-1 registries + built-in def-consts, load that
/// shared state from a leader-exported snapshot and replay PASS-2 from line 0.
/// This skips the O(T) registry pre-pass (the dominant setup I/O) per child; the
/// PASS-2 closure-replay itself stays O(T) and is UNCHANGED (its trajectory is
/// byte-identical, because the loaded env+registries equal a fresh
/// [`build_verify_state`]). Mutually exclusive with snapshot resume/save
/// (`ISA_SNAPSHOT_IN`/`_OUT`): a pre-pass shard is a fresh full replay whose line
/// indices are absolute from 0, so both are skipped when `prepass` is set.
pub(super) fn stream_with_recorder(
    path: &Path,
    writer: &mut ShardWriter,
    mut recorder: Option<&mut super::shard_verify::ShardRecorder>,
    prepass: Option<&Path>,
) -> Result<PureVerifiedImport, StreamError> {
    // Install THIS run's verify config (parsed once from env) for the whole
    // driver body, so every translate/verify read resolves against an explicit
    // per-run value rather than a process-global first-wins `OnceLock`. The
    // streaming driver + shard recorder run inline on this thread, so a single
    // install covers the whole replay. See [`super::super::isabelle_verify_config`].
    let _cfg = crate::hol::isabelle_verify_config::VerifyConfig::from_env().install();

    // --- Snapshot resume (`ISA_SNAPSHOT_IN`) / save (`ISA_SNAPSHOT_OUT`) ---
    // The standing re-import substrate (see [`super::snapshot`]): a resumed run
    // loads the prefix's complete verify-time state, PROVES the corpus is an
    // append-only extension of the snapshotted prefix (BLAKE3 over the prefix
    // byte range), refreshes the PASS-1 registries additively over the full
    // file, seeks directly to the first new byte, and verifies only the new
    // lines. Counters continue from the snapshot, so the reported totals cover
    // the WHOLE corpus. Shard output on a resumed run covers only the new
    // segment (full shards come from full runs).
    let snapshot_in = std::env::var("ISA_SNAPSHOT_IN").ok();
    let snapshot_out = std::env::var("ISA_SNAPSHOT_OUT").ok();

    let (
        mut env,
        mut closure,
        class_registry,
        method_registry,
        instance_op_registry,
        list_fn_registry,
        poly_inst_registry,
        elide,
        mut out,
        start_line,
        start_offset,
        mut rejects,
    ) = if let Some(prepass_path) = prepass {
        // Shard pre-pass hand-off: load the leader-exported post-pre-pass state
        // (env + built-in def-consts + the five PASS-1 registries; the closure is
        // empty and the counters are zero by construction). We deliberately do
        // NOT `refresh_registries` — that is the O(T) scan this hand-off skips —
        // because a pre-pass snapshot already carries the WHOLE-corpus registries
        // (the leader scanned once for the group). Replay PASS-2 from line 0.
        let snap = super::snapshot::load_snapshot(prepass_path)?;
        let super::snapshot::ReplaySnapshot {
            env,
            closure,
            class_registry,
            method_registry,
            instance_op_registry,
            list_fn_registry,
            poly_inst_registry,
            ..
        } = snap;
        (
            env,
            closure,
            class_registry,
            method_registry,
            instance_op_registry,
            list_fn_registry,
            poly_inst_registry,
            super::elide_proofs_enabled(),
            PureVerifiedImport::default(),
            0usize,
            0u64,
            Vec::new(),
        )
    } else if let Some(snap_path) = snapshot_in {
        let snap = super::snapshot::load_snapshot(Path::new(&snap_path))?;
        super::snapshot::validate_prefix(path, &snap)?;
        let super::snapshot::ReplaySnapshot {
            out,
            env,
            closure,
            mut class_registry,
            mut method_registry,
            mut instance_op_registry,
            mut list_fn_registry,
            mut poly_inst_registry,
            prefix_lines,
            prefix_bytes,
            rejects,
            ..
        } = snap;
        let mut env = env;
        // Additive registry refresh over the FULL corpus: idempotent for the
        // prefix (duplicate `add_decl`s are non-fatal, registry re-inserts
        // overwrite equal values), additive for the appended segment.
        refresh_registries(
            path,
            &mut env,
            &mut class_registry,
            &mut method_registry,
            &mut instance_op_registry,
            &mut list_fn_registry,
            &mut poly_inst_registry,
        )?;
        eprintln!(
            "SNAPSHOT RESUME: {} lines / {} bytes verified prefix loaded (KV so far: {})",
            prefix_lines, prefix_bytes, out.kernel_verified
        );
        (
            env,
            closure,
            class_registry,
            method_registry,
            instance_op_registry,
            list_fn_registry,
            poly_inst_registry,
            super::elide_proofs_enabled(),
            out,
            prefix_lines,
            prefix_bytes,
            rejects,
        )
    } else {
        let VerifyState {
            env,
            closure,
            class_registry,
            method_registry,
            instance_op_registry,
            list_fn_registry,
            poly_inst_registry,
            elide,
        } = build_verify_state(path)?;
        (
            env,
            closure,
            class_registry,
            method_registry,
            instance_op_registry,
            list_fn_registry,
            poly_inst_registry,
            elide,
            PureVerifiedImport::default(),
            0usize,
            0u64,
            Vec::new(),
        )
    };

    // Optional periodic progress interval (`ISA_PROGRESS_EVERY`, lines): 0 = off
    // (default). Read once, not per line. See the checkpoint print in PASS 2.
    let progress_every: usize = std::env::var("ISA_PROGRESS_EVERY")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(0);

    // Optional periodic SNAPSHOT CHECKPOINT interval (`ISA_SNAPSHOT_EVERY`, lines):
    // 0 = off (default). Crash/stall insurance for the 30h+ grand runs, whose
    // only snapshot is otherwise written at run END — a kill (OOM, the premise
    // spin, an operator stop) loses the whole run. When set to a positive N AND a
    // snapshot output path is configured (`ISA_SNAPSHOT_OUT`), every N lines we
    // atomically overwrite a `<ISA_SNAPSHOT_OUT>.ckpt` snapshot of the complete
    // accumulated state — a NORMAL v6 snapshot at prefix = (lines processed so
    // far), resumable through the unchanged `ISA_SNAPSHOT_IN` / `--retry-from`
    // prefix-trust machinery. Only the latest checkpoint is kept (overwrite).
    // Skipped on a pre-pass shard run (its counters cover only the shard range, so
    // it must never mint a resumable prefix snapshot — same rule as the final
    // save). Read once here.
    let snapshot_every: usize = std::env::var("ISA_SNAPSHOT_EVERY")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(0);
    let checkpoint_path: Option<PathBuf> = if snapshot_every != 0 && prepass.is_none() {
        match &snapshot_out {
            Some(out) => Some(PathBuf::from(format!("{out}.ckpt"))),
            None => {
                eprintln!(
                    "WARNING: ISA_SNAPSHOT_EVERY={snapshot_every} set but ISA_SNAPSHOT_OUT is \
                     unset — periodic checkpoints disabled (no output path)."
                );
                None
            }
        }
    } else {
        None
    };

    // PASS 2 — stream the serial-sorted corpus and verify each theorem in serial
    // (= topological) order, tracking exact byte offsets (delimiters included)
    // so a completed run can be snapshotted and a resumed run can seek straight
    // to the first unverified byte. One parsed theorem is held at a time.
    let mut file = std::fs::File::open(path)?;
    if start_offset > 0 {
        use std::io::Seek as _;
        file.seek(std::io::SeekFrom::Start(start_offset))?;
    }
    let mut reader = std::io::BufReader::new(file);
    let mut index = start_line;
    let mut offset: u64 = start_offset;
    let mut buf: Vec<u8> = Vec::new();
    loop {
        buf.clear();
        let n = reader.read_until(b'\n', &mut buf)?;
        if n == 0 {
            break;
        }
        let line_start = offset;
        offset += n as u64;
        let line = String::from_utf8_lossy(&buf);
        let line = line.trim_end_matches(['\n', '\r']);
        let cur = index;
        index += 1;
        if line.trim().is_empty() {
            continue;
        }
        // Verdict-cache bookkeeping: any rejection inside this iteration bumps
        // `out.rejected` by exactly one, so a before/after delta is a precise
        // "this line was rejected" signal — recorded with its exact byte
        // address so a retry re-measure can seek straight back to it.
        let rejected_before = out.rejected;
        // Shard-recorder observation (inert when unsharded): snapshot the counters
        // and reason maps this line may mutate, but only for a line index this
        // shard actually emits — so the extra clones cost nothing off the shard's
        // own ~1/N of the corpus.
        let kv_before = out.kernel_verified;
        let tier2_before = out.kernel_checked_ledger;
        let ledger_before = out.ledger_size;
        // Writer constant count BEFORE this line's verify: `verify_one` appends
        // exactly the constants THIS line emits into the shard writer, so
        // `[writer_const_before, writer.constants_len())` names them precisely —
        // used by the shard recorder to carve a per-RANGE `.mathverse` subset.
        // O(1) and verdict-neutral (a pure observation of the output sink).
        let writer_const_before = writer.constants_len();
        let record_this = recorder.as_ref().is_some_and(|r| r.in_range(cur));
        let (reasons_before, specifics_before) = if record_this {
            (
                out.rejection_reasons.clone(),
                out.rejection_specifics.clone(),
            )
        } else {
            (BTreeMap::new(), BTreeMap::new())
        };
        let line_serial = if let Ok(thm) = parse_proven_theorem(line) {
            let serial = thm.serial;
            verify_one(
                &thm,
                cur,
                &mut env,
                &mut closure,
                &class_registry,
                &method_registry,
                &instance_op_registry,
                &list_fn_registry,
                &poly_inst_registry,
                writer,
                &mut out,
                elide,
            );
            Some(serial)
        } else {
            // A line that does not parse is an honest rejection (e.g. an export
            // artifact), counted but never verified. Keep the soundness invariant
            // `kernel_verified + rejected == #lines processed`.
            out.reject("parse-error");
            None
        };
        let reject_record = if out.rejected > rejected_before {
            let rec = super::snapshot::RejectRecord {
                line: cur as u64,
                offset: line_start,
                len: n as u64,
            };
            rejects.push(rec);
            Some(rec)
        } else {
            None
        };
        if record_this {
            if let Some(r) = recorder.as_mut() {
                r.record_line(&super::shard_verify::LineOutcome {
                    cur,
                    serial: line_serial,
                    kv_delta: out.kernel_verified - kv_before,
                    kv_name: out.names.last().map(String::as_str),
                    reject_record,
                    tier2_delta: out.kernel_checked_ledger - tier2_before,
                    ledger_delta: out.ledger_size - ledger_before,
                    reasons_before: &reasons_before,
                    reasons_after: &out.rejection_reasons,
                    specifics_before: &specifics_before,
                    specifics_after: &out.rejection_specifics,
                    writer_const_lo: writer_const_before,
                    writer_const_hi: writer.constants_len(),
                });
            }
        }
        // Periodic progress checkpoint (env-gated). A full-corpus replay runs for
        // hours and its `kernel_verified` total is otherwise printed only at the
        // very end — an external stop mid-run loses it entirely. When
        // `ISA_PROGRESS_EVERY` names a positive line interval, emit the running
        // `processed / KernelVerified / rejected` counts to stderr so a killed run
        // still leaves a readable last-checkpoint in its captured output. Pure
        // logging: it never touches a verdict. Unset (default) = silent, no cost
        // beyond one modulo per line.
        if progress_every != 0 && (cur + 1) % progress_every == 0 {
            eprintln!(
                "PROGRESS: processed={} KernelVerified={} rejected={}",
                cur + 1,
                out.kernel_verified,
                out.rejected
            );
        }
        // Periodic snapshot CHECKPOINT (env-gated by `ISA_SNAPSHOT_EVERY`): every
        // N lines, atomically overwrite `<ISA_SNAPSHOT_OUT>.ckpt` with the complete
        // accumulated state so a killed 30h+ run resumes from the last checkpoint
        // instead of from zero. `offset`/`index` at this point address the END of
        // the just-processed line `cur` (both advanced before verify), so the
        // checkpoint is a NORMAL v6 prefix snapshot of exactly the `cur + 1` lines
        // verified so far — loadable and resumable byte-for-byte like the final
        // save. Best-effort: a checkpoint write failure is warned, never fatal (the
        // run must not die because crash-insurance I/O hiccuped).
        if let Some(ckpt) = &checkpoint_path {
            if (cur + 1) % snapshot_every == 0 {
                if let Err(e) = write_checkpoint_snapshot(
                    ckpt,
                    path,
                    index,
                    offset,
                    &out,
                    &env,
                    &closure,
                    &class_registry,
                    &method_registry,
                    &instance_op_registry,
                    &list_fn_registry,
                    &poly_inst_registry,
                    &rejects,
                ) {
                    eprintln!(
                        "WARNING: periodic checkpoint at line {} not written to {}: {e}",
                        cur + 1,
                        ckpt.display()
                    );
                } else {
                    eprintln!(
                        "SNAPSHOT CHECKPOINT: {} ({} lines / {} bytes, KV {})",
                        ckpt.display(),
                        index,
                        offset,
                        out.kernel_verified
                    );
                }
            }
        }
    }

    // --- Snapshot save: the completed state becomes the next run's prefix. ---
    // Skipped entirely on a pre-pass shard run (`prepass.is_some()`): its counters
    // cover only this shard's range, not the whole corpus, so it must never mint a
    // resumable prefix snapshot.
    if let Some(out_path) = snapshot_out.filter(|_| prepass.is_none()) {
        let prefix_blake3 = super::snapshot::hash_corpus_prefix(path, offset)?;
        let snap = super::snapshot::ReplaySnapshot {
            fingerprint: super::snapshot::current_fingerprint(),
            prefix_lines: index,
            prefix_bytes: offset,
            prefix_blake3,
            rejection_reasons: out.rejection_reasons.clone().into_iter().collect(),
            out: out.clone(),
            env,
            closure,
            class_registry,
            method_registry,
            instance_op_registry,
            list_fn_registry,
            poly_inst_registry,
            rejects,
        };
        // `None` build identity: the env-driven library replay path carries no
        // compile-time git SHA (only `clean-cli` embeds one), so the sidecar
        // records `"unknown"` for the SHA and pairs via the durable
        // `current_exe` path instead.
        super::snapshot::save_snapshot(Path::new(&out_path), &snap, None)?;
        eprintln!(
            "SNAPSHOT SAVED: {} ({} lines / {} bytes, KV {})",
            out_path, snap.prefix_lines, snap.prefix_bytes, snap.out.kernel_verified
        );
    }

    report_mode_attempt_stats();
    Ok(out)
}

/// Write a periodic CHECKPOINT snapshot of the in-flight replay state (env-gated
/// `ISA_SNAPSHOT_EVERY`). Unlike the final save — which MOVES the accumulated
/// state because the run is over — the shared [`super::snapshot::write_checkpoint`]
/// helper borrows and CLONES it (the run continues), reusing
/// [`super::snapshot::save_snapshot`]'s atomic (`.tmp` + rename) write and
/// provenance sidecar. The streaming driver's prefix GROWS line by line, so the
/// whole-prefix BLAKE3 is recomputed here (a sequential prefix read, negligible
/// against the 30h+ runs this insures) and handed to the shared helper; the retry
/// driver instead passes its fixed loaded prefix hash. `build` is `None` for the
/// env-driven library path, matching the final save.
#[allow(clippy::too_many_arguments)]
fn write_checkpoint_snapshot(
    ckpt_path: &Path,
    corpus: &Path,
    prefix_lines: usize,
    prefix_bytes: u64,
    out: &PureVerifiedImport,
    env: &Environment,
    closure: &Closure,
    class_registry: &ClassRegistry,
    method_registry: &MethodRegistry,
    instance_op_registry: &InstanceOpRegistry,
    list_fn_registry: &ListFnRegistry,
    poly_inst_registry: &PolyInstRegistry,
    rejects: &[super::snapshot::RejectRecord],
) -> Result<(), StreamError> {
    let prefix_blake3 = super::snapshot::hash_corpus_prefix(corpus, prefix_bytes)?;
    super::snapshot::write_checkpoint(
        ckpt_path,
        prefix_lines,
        prefix_bytes,
        prefix_blake3,
        out,
        env,
        closure,
        class_registry,
        method_registry,
        instance_op_registry,
        list_fn_registry,
        poly_inst_registry,
        rejects,
    )?;
    Ok(())
}

/// Print the master mode-attempt telemetry (diagnostic; env-gated by
/// `ISA_MODE_ATTEMPT_STATS`) — total kernel `add_decl` attempts, lines that
/// reached the escalation loop, and the average per-line attempt count (the P2
/// step-2 lever's baseline). Verdict-neutral; silent unless the env var is set.
pub(super) fn report_mode_attempt_stats() {
    if std::env::var("ISA_MODE_ATTEMPT_STATS").is_err() {
        return;
    }
    let (attempts, lines) = super::batch::mode_attempt_stats();
    let avg = if lines > 0 {
        attempts as f64 / lines as f64
    } else {
        0.0
    };
    eprintln!(
        "MODE ATTEMPT STATS: add_decl_attempts={attempts} lines={lines} avg_per_line={avg:.2}"
    );
}

/// The accumulated verify-time state shared by the streaming and parallel
/// drivers: the prelude+def-const environment, the (initially empty) closure,
/// the five frozen registries built by the PASS-1 pre-passes, and the elision
/// flag. Extracting this guarantees the parallel driver's registries are
/// BIT-IDENTICAL to the serial driver's (same functions, same order).
pub(super) struct VerifyState {
    pub(super) env: Environment,
    pub(super) closure: Closure,
    pub(super) class_registry: ClassRegistry,
    pub(super) method_registry: MethodRegistry,
    pub(super) instance_op_registry: InstanceOpRegistry,
    pub(super) list_fn_registry: ListFnRegistry,
    pub(super) poly_inst_registry: PolyInstRegistry,
    pub(super) elide: bool,
}

/// Build the shared verify-time state: prelude env + registered def-consts +
/// the five PASS-1 registries (each a cheap byte-prefiltered stream over the
/// corpus). Verbatim extraction of the streaming driver's setup block.
pub(super) fn build_verify_state(path: &Path) -> Result<VerifyState, StreamError> {
    let mut env = Environment::with_prelude();
    register_builtin_def_consts(&mut env);
    let closure: Closure = BTreeMap::new();
    let mut class_registry: ClassRegistry = BTreeMap::new();
    let mut method_registry: MethodRegistry = BTreeMap::new();
    let mut instance_op_registry: InstanceOpRegistry = BTreeMap::new();
    let mut list_fn_registry: ListFnRegistry = BTreeMap::new();
    let mut poly_inst_registry: PolyInstRegistry = BTreeMap::new();
    refresh_registries(
        path,
        &mut env,
        &mut class_registry,
        &mut method_registry,
        &mut instance_op_registry,
        &mut list_fn_registry,
        &mut poly_inst_registry,
    )?;
    // Opaque proof-value elision (env-gated, default off): after each theorem is
    // KernelVerified, drop its resident proof VALUE so peak memory stays bounded
    // on the full multi-GB corpus. Read once here — not per theorem — so the hot
    // loop pays no repeated env lookup. See [`super::elide_proofs_enabled`].
    let elide = super::elide_proofs_enabled();

    Ok(VerifyState {
        env,
        closure,
        class_registry,
        method_registry,
        instance_op_registry,
        list_fn_registry,
        poly_inst_registry,
        elide,
    })
}

/// Register the built-in combinator / logical / marker def-consts (and the
/// prelude-absent datatypes) into `env`, in strict dependency order. Shared by
/// the fresh setup ([`build_verify_state`]) and the snapshot-resume registry
/// refresh ([`refresh_registries`]), so the resume path picks up def-consts a
/// PRIOR translator never registered (e.g. a newly-added bnf-opaque combinator).
/// Without this, a registration-altering translator change leaves the new
/// def-const's `is_bnf_def` `Eq.refl` referencing an unregistered const → a
/// spurious kernel-reject on resume. `add_decl` is fail-silent for
/// already-present decls, so calling this on an env that already carries some/all
/// of them is idempotent. See `docs/analysis/zproof-cardinal-wall.md`.
/// The kernel name a [`Declaration`] declares. Used by the
/// `ISA_WITHHOLD_DEF_CONSTS` seam to match built-in def-consts to skip. Only
/// reached during the (once-per-driver) def-const registration, so the
/// allocation is negligible.
fn decl_name(decl: &Declaration) -> String {
    let name = match decl {
        Declaration::Definition { name, .. }
        | Declaration::Axiom { name, .. }
        | Declaration::Theorem { name, .. }
        | Declaration::Opaque { name, .. } => name,
    };
    name.to_string()
}

/// Parse the `ISA_WITHHOLD_DEF_CONSTS` debug/test seam: a comma-separated list of
/// built-in def-const kernel names [`register_builtin_def_consts`] must NOT
/// register. Empty (the default) ⇒ register everything, the production behavior.
/// See [`register_builtin_def_consts`] for why this exists.
fn withheld_def_consts() -> Vec<String> {
    match std::env::var("ISA_WITHHOLD_DEF_CONSTS") {
        Ok(s) if !s.trim().is_empty() => s
            .split(',')
            .map(str::trim)
            .filter(|s| !s.is_empty())
            .map(str::to_string)
            .collect(),
        _ => Vec::new(),
    }
}

pub(super) fn register_builtin_def_consts(env: &mut Environment) {
    // **Debug/test seam** (`ISA_WITHHOLD_DEF_CONSTS`): a comma-separated list of
    // built-in def-const kernel names to SKIP registering. Unset (default) ⇒ no
    // effect. Its sole purpose is to reproduce a *registration-altering* round in
    // a single binary: a snapshot minted with a name withheld lacks that
    // def-const exactly as a PRE-registration translator build would, so a retry
    // WITHOUT the withhold exercises the new-registration resume path (see
    // `tests/isabelle_snapshot_resume.rs` and `docs/analysis/zproof-retry-parity.md`).
    // Reads the env once here (cheap; called once per driver setup / resume).
    let withheld = withheld_def_consts();
    let add = |env: &mut Environment, decl: Declaration| {
        if !withheld.is_empty() && withheld.iter().any(|w| *w == decl_name(&decl)) {
            return;
        }
        let _ = env.add_decl(decl);
    };
    for decl in connective_definition_decls() {
        add(env, decl);
    }
    // Register the point-free HOL logical constants (`HOL.Uniq`/`Ex1`/`Let`/
    // `induct_forall`/`induct_equal`/`NO_MATCH`) as faithful polymorphic
    // `Definition`s (bodies built from the `∀`/`→`/`@Eq`/`∃`/`∧`/`True` encodings —
    // pure λ, no axiom content). A single shared def-const head makes each
    // constant's point-free `…_def_raw` axiom verify reflexively and every
    // occurrence δ-consistent. Registered AFTER the connective def-consts (their
    // `True`/`conj` dependencies), so the δ-unfolding chain closes. Non-fatal.
    for decl in pointfree_definition_decls() {
        add(env, decl);
    }
    // Register HOL's if-then-else `HOL.If` as a faithful polymorphic `Definition`
    // (`ite` over a classical `Decidable` instance; foundational closure). Every
    // `HOL.If` occurrence then unfolds to this one head, so the `…_def` bodies of
    // the recursive list/option functions that branch with `if` close and verify
    // reflexively. Non-fatal: an `if`-using `_def` simply stays unmapped on failure.
    add(env, hol_if_definition_decl());
    // Register HOL's definite description `HOL.The` (`THE x. P x`) — clean's
    // classical epsilon threaded with an explicit `Nonempty α` (foundational
    // `Classical.choice` closure). Makes `the_eq_trivial` and the `The`-defined
    // characterisations provable. Non-fatal.
    add(env, hol_the_definition_decl());
    // Register HOL's `The`-defined order extrema (`Least`/`Greatest`) as faithful
    // polymorphic `Definition`s (δ-unfolding to `THE x. P x ∧ (∀y. P y → x ≼ y)`),
    // making their defining axioms reflexive against the epsilon `The`. Non-fatal.
    for decl in extremum_definition_decls() {
        add(env, decl);
    }
    // Register HOL's function composition `Fun.comp` (`λf g x. f (g x)`, three type
    // vars) and identity `Fun.id` (`λx. x`) as faithful polymorphic `Definition`s.
    // `comp`/`id` are PERVASIVE across HOL — `foldr_def` and countless list/function
    // lemmas mention `comp f g`/`id` on a RHS or as a dep. A single shared
    // defeq-unfolding head makes `comp_def`/`id_def` reflexive and every consumer
    // δ-consistent. Pure λ (no axiom content) → consumers stay foundational.
    // Non-fatal: a `comp`/`id`-using node simply stays unmapped on failure.
    add(env, fun_comp_definition_decl());
    add(env, fun_id_definition_decl());
    // Register the `Fun.*` combinators (`fcomp`/`inj_on`/`bij_betw`/`fun_upd`/
    // `monotone_on`) as faithful polymorphic `Definition`s — bodies built from the
    // shared `Ball`/`image`/`If`/`conj`/`@Eq` encodings, so each constant's
    // `…_def`/`…_def_raw` axiom verifies reflexively and every occurrence is
    // δ-consistent. Registered AFTER the connective + `HOL.If` def-consts (their
    // bodies' dependencies), in internal dependency order (`inj_on` before
    // `bij_betw`). Non-fatal.
    for decl in fun_combinator_definition_decls() {
        add(env, decl);
    }
    // Register the BNF (Bounded Natural Functor) datatype-package combinators
    // (`convol`/`rel_fun`/`rel_set`/`eq_onp`/`vimage2p`/`Grp`/`Gr`/`csquare`/
    // `id_bnf`) as faithful polymorphic `Definition`s — bodies built from the same
    // `∀`/`Ball`/`Bex`/`∃`/`∧`/`@Eq`/`Prod.mk` encodings, so each constant's
    // `…_def`/`…_def_raw` axiom verifies reflexively and every occurrence is
    // δ-consistent. Registered AFTER the connective def-consts (their `HOL.conj`/
    // impredicative-`∃`/`Ball`/`Bex` dependencies). Non-fatal.
    for decl in bnf_combinator_definition_decls() {
        add(env, decl);
    }
    // Register the BNF leaf combinators whose bodies reference OPAQUE HOL
    // constants (`cinfinite`/`cfinite`/`pick_middlep`/`fstOp`/`sndOp`) as faithful
    // polymorphic `Definition`s with the opaque constants abstracted as leading
    // value binders and supplied at each use-site by re-embedding the actual HOL
    // constant (`pick_middlep` precedes `fstOp`/`sndOp`, which reference its
    // def-const). The two-`Field` cardinal `+`/`*`/`^`/`Csum` family is deferred
    // (see `connectives/bnf_cardinal.rs`). Non-fatal.
    for decl in bnf_opaque_combinator_definition_decls() {
        add(env, decl);
    }
    // Register the `wo_rel` `The`-threaded constants (`minim`/`supr`/`suc`) as
    // faithful polymorphic `Definition`s: `minim r A = THE b. isMinim r A b`, and
    // `supr`/`suc` = `minim r (Above/AboveS r A)`. Registered AFTER `HOL.The`, the
    // `isMinim` BNF combinator and the `Above`/`AboveS` opaque combinators their
    // bodies depend on, in internal dependency order (`minim` before `supr`/`suc`).
    // Non-fatal on registration failure.
    for decl in wo_the_definition_decls() {
        add(env, decl);
    }
    // Register Pure's judgement marker `Pure.term` as a faithful polymorphic
    // `Definition` (`λ_. ∀A. A → A`, the meta-truth its `_def` body denotes; no
    // axiom content). A single shared defeq-unfolding head makes `Pure.term_def`
    // reflexive and every `Pure.term` use-site δ-consistent (`Pure.sort_constraint`
    // is an erased sort constraint proved by a dedicated `propext` bridge, so it
    // needs no def-const). Non-fatal: a marker-using node stays unmapped on failure.
    for decl in pure_meta_definition_decls() {
        add(env, decl);
    }
    // Register the HOL datatypes clean's prelude lacks (currently `Num.num`) as
    // faithful clean inductives, so their constructors/recursor map to real kernel
    // declarations (see `register_datatype_inductives`). `Nat` is already in the
    // prelude. Idempotent and non-fatal.
    register_datatype_inductives(env);
}

/// Re-run the five PASS-1 registry pre-passes over `path` against EXISTING
/// state — idempotent for already-registered entries (`add_decl` duplicates
/// are non-fatal, registry re-inserts overwrite equal values) and ADDITIVE for
/// entries introduced by an appended corpus segment. Called with fresh state
/// by [`build_verify_state`] and with snapshot state by the resume path.
pub(super) fn refresh_registries(
    path: &Path,
    env: &mut Environment,
    class_registry: &mut ClassRegistry,
    method_registry: &mut MethodRegistry,
    instance_op_registry: &mut InstanceOpRegistry,
    list_fn_registry: &mut ListFnRegistry,
    poly_inst_registry: &mut PolyInstRegistry,
) -> Result<(), StreamError> {
    // Shadow the &mut params so the extracted block below stays verbatim with
    // the historical `&mut x` call spellings.
    let env = &mut *env;

    // Register the built-in def-consts FIRST. On the fresh path this repeats
    // `build_verify_state`'s call (idempotent). On the snapshot-resume path it is
    // the ONLY registration of these def-consts, so a translator change that added
    // a def-const (e.g. a new bnf-opaque combinator) is picked up here — otherwise
    // the resume env would lack it and the new `_def`'s reflexivity would
    // kernel-reject against an unregistered const.
    register_builtin_def_consts(env);

    // PASS 1 (MERGED — P2.4 pre-pass merge) — the five per-registry pre-passes
    // historically ran FIVE independent full-corpus scans (class-def, method-dict,
    // instance-op, list-fn, poly-inst). Their prefilters are cheap, independent
    // substring checks, so a SINGLE streaming scan that evaluates all five per line
    // and routes each matching line into the applicable set(s) produces registries
    // BIT-IDENTICAL to the five separate scans — at 1/5 the corpus reads (the
    // dominant setup I/O on the 52 GB grand corpus). The instance-op (PASS 1c) and
    // poly-inst (PASS 1e) scans used the IDENTICAL `_def` prefilter, so they share
    // one parsed `def_lines` set here — peak memory holds one copy of the `_def`
    // theorems, never two. Equivalence asserted on the fixture (and, when
    // `ISA_MERGE_EQUIV_CORPUS` is set, a real corpus) by `merge_equiv_tests`.
    let RegistryLineSets {
        class_defs,
        method_dicts,
        def_lines,
        list_defs,
    } = collect_registry_line_sets(path)?;

    // PASS 1a — structured type-class definitions in superclass-first order,
    // exactly as the batch driver does, via the shared
    // `register_classes_superclass_first` fixpoint over the class-def subset.
    register_classes_superclass_first(&class_defs, env, class_registry);
    drop(class_defs);

    // PASS 1b — overloaded class methods from their `…_dict` dictionary axioms,
    // mirroring the batch driver's `register_methods`.
    register_methods(&method_dicts, env, method_registry);
    drop(method_dicts);

    // PASS 1c — monomorphic ground-type instance operations from their
    // recursive-arithmetic `…_nat_def`/`…_num_def` axioms, mirroring the batch
    // driver's `register_instance_ops`. `register_instance_op_def` confirms each
    // `_def` candidate is a ground-type instance-op definition; registration in
    // serial (= dependency) order is bit-identical to the batch driver.
    register_instance_ops(&def_lines, env, instance_op_registry);

    // PASS 1d — plain polymorphic list-datatype functions from their recursive
    // `List.*_def` axioms, mirroring the batch driver's `register_list_fns`.
    register_list_fns(
        &list_defs,
        env,
        list_fn_registry,
        instance_op_registry,
        method_registry,
    );
    drop(list_defs);

    // PASS 1e — polymorphic instance operations from their `_def` axioms
    // (`Int.power_int_def`, … — `'a`-generic constants whose body uses overloaded
    // class operations), mirroring the batch driver's `register_poly_insts`. Reuses
    // the SAME `def_lines` set PASS 1c registered from (identical `_def` prefilter).
    register_poly_insts(
        &def_lines,
        env,
        poly_inst_registry,
        method_registry,
        instance_op_registry,
        list_fn_registry,
    );
    drop(def_lines);
    Ok(())
}

/// The five registry line-sets collected in ONE streaming pass over the corpus
/// (P2.4 pre-pass merge). `def_lines` is the `_def`-prefiltered set SHARED by the
/// instance-op (PASS 1c) and poly-inst (PASS 1e) registrations — the historical
/// pre-passes ran two identical `_def` scans; merging keeps a single parsed copy.
struct RegistryLineSets {
    class_defs: Vec<IsaProvenTheorem>,
    method_dicts: Vec<IsaProvenTheorem>,
    def_lines: Vec<IsaProvenTheorem>,
    list_defs: Vec<IsaProvenTheorem>,
}

/// Single-pass replacement for the five per-registry `collect_*` scans: stream
/// `path` ONCE, evaluate all five cheap substring prefilters per line, and route
/// each matching (parse-ok) line into the applicable set(s). Each set is populated
/// in line order exactly as its dedicated scan would, so the returned sets are
/// BIT-IDENTICAL to the five separate collectors (asserted by `merge_equiv_tests`
/// via the retained `#[cfg(test)]` originals). Cuts the pre-pass from five
/// full-corpus reads to one — the dominant setup I/O on the multi-GB grand corpus.
fn collect_registry_line_sets(path: &Path) -> Result<RegistryLineSets, StreamError> {
    let file = std::fs::File::open(path)?;
    let reader = std::io::BufReader::new(file);
    let mut class_defs = Vec::new();
    let mut method_dicts = Vec::new();
    let mut def_lines = Vec::new();
    let mut list_defs = Vec::new();
    for line in reader.lines() {
        let line = line?;
        // The five independent prefilters — the exact substrings the dedicated
        // collectors used. Note `_class_def` CONTAINS `_def`, so a class-def line
        // legitimately also joins `def_lines` (as the historical instance-op /
        // poly-inst scans admitted it), and `list` implies `def`.
        let has_class = line.contains("_class_def");
        let has_dict = line.contains("_dict");
        let has_def = line.contains("_def");
        let has_list = has_def
            && (line.contains("List.list")
                || line.contains("Basic_BNF_LFPs.sum.size_sum")
                || line.contains("Basic_BNF_LFPs.prod.size_prod"));
        if !has_class && !has_dict && !has_def {
            continue;
        }
        let Ok(thm) = parse_proven_theorem(&line) else {
            continue;
        };
        // Route into every set whose prefilter matched, in the same line order as
        // the dedicated scans. `def_lines` takes the owned `thm` LAST so the common
        // `_def` case avoids a clone; the earlier sets clone only when they match.
        if has_class && class_def_superclasses(&thm).is_some() {
            class_defs.push(thm.clone());
        }
        if has_dict {
            method_dicts.push(thm.clone());
        }
        if has_list {
            list_defs.push(thm.clone());
        }
        if has_def {
            def_lines.push(thm);
        }
    }
    Ok(RegistryLineSets {
        class_defs,
        method_dicts,
        def_lines,
        list_defs,
    })
}

/// Pre-pass for the streaming driver: stream `path` and return only the parsed
/// theorems that are `…c_class_def` axioms (the subset
/// [`register_classes_superclass_first`] acts on). A cheap `_class_def`
/// substring pre-filter avoids parsing the (vast majority of) non-class lines;
/// each candidate is confirmed by [`class_def_superclasses`] returning `Some`.
///
/// Retained under `#[cfg(test)]` as the reference implementation the merged
/// single-pass [`collect_registry_line_sets`] is proven bit-identical to (see
/// `merge_equiv_tests`); production now uses the merged pass exclusively.
#[cfg(test)]
fn collect_class_def_theorems(path: &Path) -> Result<Vec<IsaProvenTheorem>, StreamError> {
    let file = std::fs::File::open(path)?;
    let reader = std::io::BufReader::new(file);
    let mut class_defs = Vec::new();
    for line in reader.lines() {
        let line = line?;
        // Cheap pre-filter: only `…c_class_def` axiom lines can register a class,
        // so skip the JSON parse for everything else.
        if !line.contains("_class_def") {
            continue;
        }
        if let Ok(thm) = parse_proven_theorem(&line) {
            if class_def_superclasses(&thm).is_some() {
                class_defs.push(thm);
            }
        }
    }
    Ok(class_defs)
}

/// Pre-pass for the streaming driver: stream `path` and return only the parsed
/// theorems whose proofs reference an overloaded-method `…_dict` dictionary axiom
/// (the subset [`register_methods`] acts on). A cheap `_dict` substring
/// pre-filter avoids parsing the (vast majority of) lines that mention no method
/// dictionary; [`register_method_defs`] confirms each candidate carries a real
/// `Pure.symmetric % LHS % RHS %% …_dict` spine.
#[cfg(test)]
fn collect_method_dict_theorems(path: &Path) -> Result<Vec<IsaProvenTheorem>, StreamError> {
    let file = std::fs::File::open(path)?;
    let reader = std::io::BufReader::new(file);
    let mut dicts = Vec::new();
    for line in reader.lines() {
        let line = line?;
        // Cheap pre-filter: only lines mentioning a `…_dict` axiom can register a
        // method, so skip the JSON parse for everything else.
        if !line.contains("_dict") {
            continue;
        }
        if let Ok(thm) = parse_proven_theorem(&line) {
            dicts.push(thm);
        }
    }
    Ok(dicts)
}

/// Pre-pass for the streaming driver: stream `path` and return only the parsed
/// theorems that are monomorphic ground-type instance-operation definitions (the
/// subset [`register_instance_ops`] acts on). A cheap `_def` substring pre-filter
/// avoids parsing the (vast majority of) lines that define no instance operation;
/// [`register_instance_op_def`] confirms each candidate is a `Pure.eq (c@ground)`
/// definitional axiom whose body closes. Sorted by serial inside
/// `register_instance_ops`, this yields a registry bit-identical to the batch
/// driver's.
#[cfg(test)]
fn collect_instance_op_def_theorems(path: &Path) -> Result<Vec<IsaProvenTheorem>, StreamError> {
    let file = std::fs::File::open(path)?;
    let reader = std::io::BufReader::new(file);
    let mut defs = Vec::new();
    for line in reader.lines() {
        let line = line?;
        // Cheap pre-filter: an instance-op definition's name ends with `…_def`, so
        // skip the JSON parse for everything that mentions no `_def` axiom.
        if !line.contains("_def") {
            continue;
        }
        if let Ok(thm) = parse_proven_theorem(&line) {
            defs.push(thm);
        }
    }
    Ok(defs)
}

/// Pre-pass for the streaming driver: stream `path` and return only the parsed
/// theorems that are plain polymorphic list-function definitions (the subset
/// [`register_list_fns`] acts on). A cheap `List.` substring pre-filter avoids
/// parsing the (vast majority of) lines that mention no list datatype;
/// [`register_list_fn_def`] confirms each candidate is a single-`'a` list
/// function definition whose body closes. Sorted by serial inside
/// `register_list_fns`, this yields a registry bit-identical to the batch
/// driver's.
#[cfg(test)]
fn collect_list_fn_def_theorems(path: &Path) -> Result<Vec<IsaProvenTheorem>, StreamError> {
    let file = std::fs::File::open(path)?;
    let reader = std::io::BufReader::new(file);
    let mut defs = Vec::new();
    for line in reader.lines() {
        let line = line?;
        // Cheap pre-filter: a list-function definition is a `…_def` axiom whose
        // body mentions the `List.list` datatype, so skip the JSON parse for
        // everything that mentions neither. The BNF LFP-package datatype `size`
        // structural recursions (`Basic_BNF_LFPs.{sum.size_sum,prod.size_prod}`)
        // are registered through the SAME [`register_list_fn_def`] path (their
        // bodies are closed `case_sum`/`case_prod` folds into `nat`) but name no
        // `List.list`, so they are admitted here by their own constant name; the
        // name-gate + close-or-skip guard inside [`register_list_fn_def`] keeps
        // non-matching size lines (the overloaded/instance variants) out.
        let list_or_size = line.contains("List.list")
            || line.contains("Basic_BNF_LFPs.sum.size_sum")
            || line.contains("Basic_BNF_LFPs.prod.size_prod");
        if !line.contains("_def") || !list_or_size {
            continue;
        }
        if let Ok(thm) = parse_proven_theorem(&line) {
            defs.push(thm);
        }
    }
    Ok(defs)
}

/// Pre-pass for the streaming driver: stream `path` and return only the parsed
/// theorems that are polymorphic instance-operation definitions (the subset
/// [`register_poly_insts`] acts on). A cheap `_def` substring pre-filter avoids
/// parsing the (vast majority of) non-definitional lines;
/// [`register_poly_inst_def`] confirms each candidate is a bare-constant
/// definitional axiom whose body closes. Sorted by serial inside
/// `register_poly_insts`, this yields a registry bit-identical to the batch
/// driver's.
#[cfg(test)]
fn collect_poly_inst_def_theorems(path: &Path) -> Result<Vec<IsaProvenTheorem>, StreamError> {
    let file = std::fs::File::open(path)?;
    let reader = std::io::BufReader::new(file);
    let mut defs = Vec::new();
    for line in reader.lines() {
        let line = line?;
        // Cheap pre-filter: a polymorphic instance-op definition is a `…_def` /
        // `…_def_raw` axiom, so skip the JSON parse for everything else. The
        // historical additional `_class.`/`.class.` requirement mirrored the
        // (G2, now lifted) overloaded-method-mention gate in
        // `poly_inst_def_axiom`; under the lift, plain-body definitional
        // constants and PLAIN locale predicates (`Orderings.ordering_def`,
        // `Finite_Set.folding_on_def` — no `.class.` anywhere on the line)
        // register too, so the pre-filter admits every `_def` line — the same
        // breadth (and cost) as the instance-op pre-pass above.
        if !line.contains("_def") {
            continue;
        }
        if let Ok(thm) = parse_proven_theorem(&line) {
            defs.push(thm);
        }
    }
    Ok(defs)
}

#[cfg(test)]
mod merge_equiv_tests {
    //! Proves the P2.4 merged single-pass [`collect_registry_line_sets`] returns
    //! registry line-sets BIT-IDENTICAL to the five historical per-registry scans
    //! it replaces — the equivalence gate for the pre-pass merge.
    use super::*;
    use std::path::PathBuf;

    fn assert_merge_equiv(path: &Path) {
        let merged = collect_registry_line_sets(path).expect("merged single-pass pre-pass");
        let class = collect_class_def_theorems(path).expect("class-def scan");
        let dicts = collect_method_dict_theorems(path).expect("method-dict scan");
        let inst = collect_instance_op_def_theorems(path).expect("instance-op scan");
        let list = collect_list_fn_def_theorems(path).expect("list-fn scan");
        let poly = collect_poly_inst_def_theorems(path).expect("poly-inst scan");

        assert_eq!(
            merged.class_defs, class,
            "merged class_defs must equal the dedicated class-def scan"
        );
        assert_eq!(
            merged.method_dicts, dicts,
            "merged method_dicts must equal the dedicated method-dict scan"
        );
        assert_eq!(
            merged.def_lines, inst,
            "merged def_lines must equal the dedicated instance-op scan"
        );
        assert_eq!(
            merged.def_lines, poly,
            "merged def_lines must equal the dedicated poly-inst scan (identical `_def` filter)"
        );
        assert_eq!(
            merged.list_defs, list,
            "merged list_defs must equal the dedicated list-fn scan"
        );
    }

    #[test]
    fn test_merged_prepass_bit_identical_on_fixture() {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/isabelle/hol_foundational_closure.jsonl");
        assert_merge_equiv(&path);
    }

    /// Opt-in equivalence check over a REAL corpus (e.g. the prefix6k pair), which
    /// — unlike the small committed fixture — exercises the `_class_def` and
    /// `_dict` routing too. Set `ISA_MERGE_EQUIV_CORPUS=<path>` to run it; skipped
    /// (with no failure) when the env var is unset or names a missing file, so the
    /// default `cargo test` never depends on an out-of-tree corpus.
    #[test]
    fn test_merged_prepass_bit_identical_on_corpus_env() {
        let Ok(p) = std::env::var("ISA_MERGE_EQUIV_CORPUS") else {
            return;
        };
        let path = PathBuf::from(p);
        if !path.exists() {
            return;
        }
        assert_merge_equiv(&path);
    }
}
