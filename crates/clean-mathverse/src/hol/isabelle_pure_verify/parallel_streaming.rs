// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Parallel** streaming closure-replay driver (P2.1 of the industrial-import
//! program, `designs/2026-07-07-isabelle-100pct-industrial-import.md`):
//! parse + translate on N worker threads, kernel verdicts on the master thread
//! in **strict serial order** — verdict-identical to
//! [`super::streaming::import_proven_theorems_streaming`] by construction.
//!
//! # Why this is sound and deterministic
//!
//! Translation is a **pure function** of (theorem, the closure entries of its
//! proof-referenced serials, the frozen PASS-1 registries) — it takes no
//! [`Environment`] (see `translate_theorem_with_meta`). The kernel `add_decl`
//! loop, the honest-reject bucketing, the foundational-axiom gate, the closure
//! insert, the shard write and elision all run on the MASTER, one line at a
//! time, in exactly the serial driver's order — so the kernel remains the sole
//! verdict mint and the environment passes through the identical sequence of
//! states.
//!
//! A worker translates a line only after **all its in-corpus dependencies have
//! final verdicts** (Kahn-style dependency counters over the serial-DAG; deps
//! always have smaller serials, hence smaller line indices). Its closure view —
//! a per-job snapshot of exactly its deps' entries — therefore equals what the
//! serial driver's closure would contain for those lookups at that line. Equal
//! inputs, pure function: equal translations, equal verdicts.
//!
//! The dependency edges used for scheduling come from a byte-level scan for
//! `"k":"thm","id":` — a textual **superset** of the parser's
//! [`IsaProof::thm_deps`] (the parser reads the same JSON text), so a node is
//! never dispatched before a translation-relevant dep is final; a spurious
//! textual match only delays dispatch (conservative), never changes a verdict.

use std::collections::{BTreeMap, VecDeque};
use std::io::BufRead as _;
use std::path::Path;
use std::sync::mpsc;
use std::sync::{Arc, Condvar, Mutex, RwLock};

use super::super::isabelle_pure::{parse_proven_theorem, IsaProvenTheorem};
use super::super::isabelle_pure_translate::Closure;
use super::batch::{translate_all_modes, verify_one_with_translations, ModeTranslations};
use super::streaming::{build_verify_state, VerifyState};
use super::{PureVerifiedImport, StreamError};
use crate::shard::ShardWriter;

/// Raw line bytes allowed in flight (stored-but-not-finalized). Bounds peak
/// memory on the multi-GB corpus; the producer may always read ahead a small
/// fixed window past the master frontier regardless, so the master's next
/// needed line is never starved (deadlock-freedom). Shared with the retry
/// re-measure driver ([`super::retry`]).
pub(super) const INFLIGHT_BYTE_CAP: usize = 1_500_000_000;

/// Unconditional read-ahead window (lines) past the master frontier — see
/// [`INFLIGHT_BYTE_CAP`].
pub(super) const MIN_READAHEAD: usize = 64;

/// Worker stack size: proof translation recurses deeply (the serial driver
/// runs under `RUST_MIN_STACK=2.5G`); same order here, lazily committed.
pub(super) const WORKER_STACK: usize = 2 * 1024 * 1024 * 1024;

/// What the index pass learned about one corpus line.
struct Node {
    /// Empty/whitespace line — the serial driver `continue`s without counting;
    /// the master does the same (no worker involved).
    skip: bool,
    /// Exact raw byte length including the trailing delimiter(s) (in-flight
    /// accounting + the verdict cache's reject records).
    bytes: usize,
    /// Exact byte offset of the line's first byte in the corpus file (verdict
    /// cache's reject records).
    offset: u64,
    /// Line indices of in-corpus dependencies (byte-scan superset of
    /// `thm_deps`), deduplicated.
    deps: Vec<u32>,
}

/// Worker → master result for one line.
enum WorkerMsg {
    Parsed {
        idx: usize,
        thm: Box<IsaProvenTheorem>,
        translations: ModeTranslations,
    },
    ParseError {
        idx: usize,
    },
}

/// Scheduler state shared by producer, workers and master.
struct Sched {
    /// Raw line text, stored by the producer, taken by the dispatched worker.
    lines: Vec<Option<String>>,
    /// Remaining unfinalized in-corpus deps per line (Kahn counter).
    indeg: Vec<u32>,
    /// Dispatched-to-worker flag (a node is dispatched exactly once).
    dispatched: Vec<bool>,
    /// Ready-to-translate queue (indeg 0, line stored, not yet dispatched).
    ready: VecDeque<usize>,
    /// Bytes of stored-but-unfinalized lines.
    inflight_bytes: usize,
    /// Master frontier: all lines `< master_pos` have final verdicts.
    master_pos: usize,
    /// Producer has stored every line.
    done_reading: bool,
}

/// Parallel replay: verdict-identical to the serial streaming driver, with
/// parse+translate fanned out over `workers` threads. See the module docs for
/// the soundness argument. `workers == 0` is rejected (callers should use the
/// serial driver instead).
///
/// # Errors
/// [`StreamError::Io`] on file errors, exactly like the serial driver.
pub fn import_proven_theorems_parallel(
    serial_sorted_path: impl AsRef<Path>,
    writer: &mut ShardWriter,
    workers: usize,
) -> Result<PureVerifiedImport, StreamError> {
    let path = serial_sorted_path.as_ref();
    assert!(
        workers > 0,
        "import_proven_theorems_parallel needs workers > 0"
    );

    // Parse THIS run's verify config once and install it on the master thread.
    // The worker threads (which run `translate_all_modes`, the only translate-
    // budget / Miller readers off the master) each install a COPY at their start
    // — so the whole group verifies under one explicit per-run config rather than
    // a process-global first-wins `OnceLock`. See [`super::super::isabelle_verify_config`].
    let cfg = crate::hol::isabelle_verify_config::VerifyConfig::from_env();
    let _cfg = cfg.install();

    // === Shared verify-time state: identical to the serial driver, with the
    // same snapshot resume/save surface (`ISA_SNAPSHOT_IN`/`_OUT`) — see
    // [`super::snapshot`] for the trust model. All scheduler structures below
    // are SEGMENT-RELATIVE (index 0 = first unverified line); only the kernel
    // anon-naming index and the progress print are globalized by
    // `start_line`. ===
    let snapshot_in = std::env::var("ISA_SNAPSHOT_IN").ok();
    let snapshot_out = std::env::var("ISA_SNAPSHOT_OUT").ok();
    let (
        mut env,
        closure,
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
    ) = if let Some(snap_path) = snapshot_in {
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
        super::streaming::refresh_registries(
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
    let closure = Arc::new(RwLock::new(closure));

    let progress_every: usize = std::env::var("ISA_PROGRESS_EVERY")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(0);

    // === Index pass: serials + dependency edges via a cheap byte scan. ===
    // Serial-ascending order ⇒ a dep's serial→index entry exists when its
    // consumer is scanned. Missing serials (not in the corpus) are dropped —
    // they can never finalize and translation yields the same UnresolvedThm
    // the serial driver produces.
    let mut nodes: Vec<Node> = Vec::new();
    let mut dependents: Vec<Vec<u32>> = Vec::new();
    {
        let mut serial_to_idx: std::collections::HashMap<i64, u32> =
            std::collections::HashMap::new();
        let mut file = std::fs::File::open(path)?;
        if start_offset > 0 {
            use std::io::Seek as _;
            file.seek(std::io::SeekFrom::Start(start_offset))?;
        }
        // `read_until` (not `.lines()`) so each node's byte offset + length are
        // EXACT — the verdict cache's reject records must be seekable.
        let mut reader = std::io::BufReader::new(file);
        let mut raw: Vec<u8> = Vec::new();
        let mut pos: u64 = start_offset;
        loop {
            use std::io::BufRead as _;
            raw.clear();
            let nread = reader.read_until(b'\n', &mut raw)?;
            if nread == 0 {
                break;
            }
            let line_offset = pos;
            pos += nread as u64;
            let idx = nodes.len();
            let lossy = String::from_utf8_lossy(&raw);
            let line = lossy.trim_end_matches(['\n', '\r']);
            if line.trim().is_empty() {
                nodes.push(Node {
                    skip: true,
                    bytes: nread,
                    offset: line_offset,
                    deps: Vec::new(),
                });
                dependents.push(Vec::new());
                continue;
            }
            // Leading serial: `{"serial":<digits>`.
            if let Some(rest) = line.strip_prefix("{\"serial\":") {
                let digits: String = rest.chars().take_while(char::is_ascii_digit).collect();
                if let Ok(serial) = digits.parse::<i64>() {
                    serial_to_idx.insert(serial, idx as u32);
                }
            }
            // Dep edges: every `"k":"thm","id":<digits>` occurrence.
            let mut deps: Vec<u32> = Vec::new();
            let needle = "\"k\":\"thm\",\"id\":";
            let mut start = 0usize;
            while let Some(pos) = line[start..].find(needle) {
                let at = start + pos + needle.len();
                let digits: String = line[at..]
                    .chars()
                    .take_while(|c| c.is_ascii_digit() || *c == '-')
                    .collect();
                if let Ok(dep_serial) = digits.parse::<i64>() {
                    if let Some(&dep_idx) = serial_to_idx.get(&dep_serial) {
                        deps.push(dep_idx);
                    }
                }
                start = at;
            }
            deps.sort_unstable();
            deps.dedup();
            nodes.push(Node {
                skip: false,
                bytes: nread,
                offset: line_offset,
                deps,
            });
            dependents.push(Vec::new());
        }
        // Reverse adjacency for finalize-time wakeups.
        for (idx, node) in nodes.iter().enumerate() {
            for &d in &node.deps {
                dependents[d as usize].push(idx as u32);
            }
        }
    }
    let n = nodes.len();

    let sched = Arc::new((
        Mutex::new(Sched {
            lines: vec![None; n],
            indeg: nodes.iter().map(|nd| nd.deps.len() as u32).collect(),
            dispatched: vec![false; n],
            ready: VecDeque::new(),
            inflight_bytes: 0,
            master_pos: 0,
            done_reading: false,
        }),
        Condvar::new(), // workers wait for ready work
        Condvar::new(), // producer waits for capacity
    ));

    let (tx, rx) = mpsc::sync_channel::<WorkerMsg>(workers * 4);

    std::thread::scope(|scope| -> Result<(), StreamError> {
        // === Producer: stream lines into the scheduler. ===
        {
            let sched = Arc::clone(&sched);
            let nodes_skip: Vec<bool> = nodes.iter().map(|nd| nd.skip).collect();
            let path = path.to_path_buf();
            scope.spawn(move || {
                let mut file = match std::fs::File::open(&path) {
                    Ok(f) => f,
                    Err(_) => return, // master's own reads already errored the run
                };
                if start_offset > 0 {
                    use std::io::Seek as _;
                    if file.seek(std::io::SeekFrom::Start(start_offset)).is_err() {
                        return;
                    }
                }
                let reader = std::io::BufReader::new(file);
                let (lock, cv_work, cv_cap) = &*sched;
                for (idx, line) in reader.lines().enumerate() {
                    let Ok(line) = line else { break };
                    if nodes_skip[idx] {
                        continue; // master handles skips; nothing to store
                    }
                    let mut s = lock.lock().expect("scheduler lock");
                    while s.inflight_bytes > INFLIGHT_BYTE_CAP && idx > s.master_pos + MIN_READAHEAD
                    {
                        s = cv_cap.wait(s).expect("capacity wait");
                    }
                    s.inflight_bytes += line.len() + 1;
                    s.lines[idx] = Some(line);
                    if s.indeg[idx] == 0 && !s.dispatched[idx] {
                        s.ready.push_back(idx);
                        cv_work.notify_one();
                    }
                }
                let mut s = lock.lock().expect("scheduler lock");
                s.done_reading = true;
                cv_work.notify_all();
            });
        }

        // === Workers: parse + translate-all-modes against a dep snapshot. ===
        for _ in 0..workers {
            let sched = Arc::clone(&sched);
            let closure = Arc::clone(&closure);
            let tx = tx.clone();
            let class_registry = &class_registry;
            let method_registry = &method_registry;
            let instance_op_registry = &instance_op_registry;
            let list_fn_registry = &list_fn_registry;
            let poly_inst_registry = &poly_inst_registry;
            std::thread::Builder::new()
                .stack_size(WORKER_STACK)
                .spawn_scoped(scope, move || {
                    // Install the master's verify config on this worker thread so
                    // its `translate_all_modes` budget/Miller reads match the run.
                    let _wg = cfg.install();
                    let (lock, cv_work, _cv_cap) = &*sched;
                    loop {
                        let (idx, line) = {
                            let mut s = lock.lock().expect("scheduler lock");
                            loop {
                                if let Some(idx) = s.ready.pop_front() {
                                    s.dispatched[idx] = true;
                                    let line =
                                        s.lines[idx].take().expect("ready line must be stored");
                                    break (idx, line);
                                }
                                if s.done_reading && s.master_pos >= s.lines.len() {
                                    return;
                                }
                                // Also exit when everything is dispatched and
                                // reading is done (master may still be behind).
                                if s.done_reading
                                    && s.ready.is_empty()
                                    && s.dispatched.iter().all(|d| *d)
                                {
                                    return;
                                }
                                s = cv_work.wait(s).expect("work wait");
                            }
                        };
                        let msg = match parse_proven_theorem(&line) {
                            Err(_) => WorkerMsg::ParseError { idx },
                            Ok(thm) => {
                                drop(line);
                                // Dep-snapshot closure: exactly the entries a
                                // serial run would find for this line's lookups
                                // (deps are final; entries never mutate).
                                let mut dep_serials: Vec<i64> = Vec::new();
                                thm.proof.thm_deps(&mut dep_serials);
                                dep_serials.sort_unstable();
                                dep_serials.dedup();
                                let mini: Closure = {
                                    let g = closure.read().expect("closure read");
                                    dep_serials
                                        .iter()
                                        .filter_map(|s| g.get(s).map(|e| (*s, e.clone())))
                                        .collect()
                                };
                                let translations = translate_all_modes(
                                    &thm,
                                    &mini,
                                    class_registry,
                                    method_registry,
                                    instance_op_registry,
                                    list_fn_registry,
                                    poly_inst_registry,
                                );
                                WorkerMsg::Parsed {
                                    idx,
                                    thm: Box::new(thm),
                                    translations,
                                }
                            }
                        };
                        if tx.send(msg).is_err() {
                            return; // master gone (error path)
                        }
                    }
                })
                .expect("spawn worker");
        }
        drop(tx); // master's rx ends when the last worker exits

        // === Master: strict serial-order kernel verdicts. ===
        let (lock, cv_work, cv_cap) = &*sched;
        let mut buffer: BTreeMap<usize, WorkerMsg> = BTreeMap::new();
        for idx in 0..n {
            if !nodes[idx].skip {
                // Pull worker results until this line's is available.
                while !buffer.contains_key(&idx) {
                    match rx.recv() {
                        Ok(msg) => {
                            let key = match &msg {
                                WorkerMsg::Parsed { idx, .. } | WorkerMsg::ParseError { idx } => {
                                    *idx
                                }
                            };
                            buffer.insert(key, msg);
                        }
                        Err(_) => {
                            // All workers exited without producing this line —
                            // impossible under the invariants; surface as an
                            // honest error rather than a silent undercount.
                            return Err(StreamError::Io(std::io::Error::other(
                                "parallel replay: worker pool ended early",
                            )));
                        }
                    }
                }
                // Verdict-cache bookkeeping: a before/after `out.rejected`
                // delta is a precise "this line was rejected" signal (every
                // reject path bumps it exactly once) — recorded with the
                // line's exact byte address for the retry re-measure.
                let rejected_before = out.rejected;
                match buffer.remove(&idx).expect("buffered") {
                    WorkerMsg::ParseError { .. } => out.reject("parse-error"),
                    WorkerMsg::Parsed {
                        thm, translations, ..
                    } => {
                        let mut cg = closure.write().expect("closure write");
                        verify_one_with_translations(
                            &thm,
                            start_line + idx,
                            Some(&translations),
                            &mut env,
                            &mut cg,
                            &class_registry,
                            &method_registry,
                            &instance_op_registry,
                            &list_fn_registry,
                            &poly_inst_registry,
                            writer,
                            &mut out,
                            elide,
                        );
                    }
                }
                if out.rejected > rejected_before {
                    rejects.push(super::snapshot::RejectRecord {
                        line: (start_line + idx) as u64,
                        offset: nodes[idx].offset,
                        len: nodes[idx].bytes as u64,
                    });
                }
            }
            // Finalize `idx`: advance the frontier, release capacity, wake deps.
            {
                let mut s = lock.lock().expect("scheduler lock");
                s.master_pos = idx + 1;
                if !nodes[idx].skip {
                    s.inflight_bytes = s.inflight_bytes.saturating_sub(nodes[idx].bytes);
                }
                for &d in &dependents[idx] {
                    let d = d as usize;
                    s.indeg[d] -= 1;
                    if s.indeg[d] == 0 && s.lines[d].is_some() && !s.dispatched[d] {
                        s.ready.push_back(d);
                        cv_work.notify_one();
                    }
                }
                cv_cap.notify_all();
            }
            if progress_every != 0 && (start_line + idx + 1) % progress_every == 0 {
                eprintln!(
                    "PROGRESS: processed={} KernelVerified={} rejected={}",
                    start_line + idx + 1,
                    out.kernel_verified,
                    out.rejected
                );
            }
        }
        // Wake any workers still parked so the scope can join.
        {
            let _s = lock.lock().expect("scheduler lock");
            cv_work.notify_all();
        }
        Ok(())
    })?;

    // --- Snapshot save: the completed state becomes the next run's prefix.
    // Byte-exact prefix length = the whole file (this driver always reads to
    // EOF), taken from metadata rather than line-length reconstruction (the
    // index pass's `.lines()` strips delimiters).
    if let Some(out_path) = snapshot_out {
        let total_bytes = std::fs::metadata(path)?.len();
        let closure_inner = match Arc::try_unwrap(closure) {
            Ok(l) => l
                .into_inner()
                .unwrap_or_else(std::sync::PoisonError::into_inner),
            Err(arc) => arc.read().expect("closure read").clone(),
        };
        let prefix_blake3 = super::snapshot::hash_corpus_prefix(path, total_bytes)?;
        let snap = super::snapshot::ReplaySnapshot {
            fingerprint: super::snapshot::current_fingerprint(),
            prefix_lines: start_line + n,
            prefix_bytes: total_bytes,
            prefix_blake3,
            rejection_reasons: out.rejection_reasons.clone().into_iter().collect(),
            out: out.clone(),
            env,
            closure: closure_inner,
            class_registry,
            method_registry,
            instance_op_registry,
            list_fn_registry,
            poly_inst_registry,
            rejects,
        };
        // `None`: env-driven library path has no threaded build identity (see the
        // serial streaming save site); the sidecar records `"unknown"` SHA and
        // pairs via `current_exe`.
        super::snapshot::save_snapshot(Path::new(&out_path), &snap, None)?;
        eprintln!(
            "SNAPSHOT SAVED: {} ({} lines / {} bytes, KV {})",
            out_path, snap.prefix_lines, snap.prefix_bytes, snap.out.kernel_verified
        );
    }

    // --- Stage-4 Miller pre-check instrumentation. Report the CHEAP PRE-CHECK
    // hit rate (how many candidates the bounded head/arity walk pruned before the
    // expensive kernel re-check) whenever the redex-lane Miller solve did any
    // work. Diagnostic only — never affects a verdict.
    let (considered, precheck_rejects, emitted) =
        super::super::isabelle_pure_translate::miller_stats();
    if considered > 0 {
        let rate = 100.0 * (precheck_rejects as f64) / (considered as f64);
        eprintln!(
            "MILLER STATS: candidates={considered} precheck_rejects={precheck_rejects} \
             ({rate:.1}%) emitted={emitted}"
        );
    }

    super::streaming::report_mode_attempt_stats();
    Ok(out)
}
