// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Shard-group orchestration** — run an `N`-way sharded verify end-to-end on
//! one machine with a single call, then merge the shards into the one verdict
//! stream a serial run would produce.
//!
//! The primitives (per-shard [`import_proven_theorems_streaming_shard`], the
//! [`export_prepass_snapshot`] hand-off, [`merge_shard_verdicts`], the
//! [`VerifyLock`]) already exist; this module is the thin driver that wires them
//! into "verify shard `1/N` … `N/N`, wait, merge, write" so an operator does not
//! have to script it in bash (design note §7 follow-up). Two runners:
//!
//! - [`run_shard_group_in_process`] fans the shards out over `N` big-stack
//!   threads in ONE process — convenient, low-friction, and the one the fixture
//!   determinism/E2E gate drives. Each thread installs its own
//!   [`VerifyConfig`](crate::hol::isabelle_verify_config::VerifyConfig) (via the
//!   shard entry) so co-hosted shards never contaminate each other.
//! - [`run_shard_group_subprocess`] spawns `N` **child processes** (the clean
//!   binary or the harness) with `ISA_SHARD=k/N` and the verify-lock inheritance
//!   (`ISA_VERIFY_LOCK=held`) the leader already holds — true process isolation,
//!   the production scaling path on a big machine.
//!
//! Both optionally use the pre-pass hand-off: the leader exports the shared
//! post-pre-pass state ONCE and every shard loads it, skipping the O(T) registry
//! scan (see [`export_prepass_snapshot`]). The merge is byte-identical to a
//! serial run regardless (the determinism invariant of the whole design).

use std::path::{Path, PathBuf};

use super::shard_mathverse::{import_proven_theorems_streaming_shard_emit, merge_shard_mathverse};
use super::shard_verify::{
    export_prepass_snapshot, merge_shard_verdicts, MergedVerdicts, ShardError, ShardSpec,
    ShardVerdicts,
};
use super::verify_lock::{VerifyLock, VerifyLockError};
use super::StreamError;
use crate::shard::ShardWriter;

/// The pre-pass file name the leader exports into the group's work directory.
const PREPASS_FILE: &str = "prepass.snap";

/// Errors from the shard-group driver.
#[derive(Debug, thiserror::Error)]
pub enum ShardGroupError {
    /// `n == 0`, or a per-shard [`ShardSpec`] / merge-cover rejection.
    #[error("shard spec/merge: {0}")]
    Shard(#[from] ShardError),
    /// A shard's verify (or the pre-pass export) hit an I/O or snapshot error.
    #[error("shard verify: {0}")]
    Stream(#[from] StreamError),
    /// The machine-wide verify lock could not be acquired (another group runs).
    #[error("verify lock: {0}")]
    Lock(#[from] VerifyLockError),
    /// A child process could not be spawned.
    #[error("spawning shard {k}/{n}: {source}")]
    Spawn {
        /// 1-based shard index.
        k: usize,
        /// Total shard count.
        n: usize,
        /// Underlying spawn error.
        source: std::io::Error,
    },
    /// A child process exited non-zero.
    #[error("shard {k}/{n} child process failed: {status}")]
    ChildFailed {
        /// 1-based shard index.
        k: usize,
        /// Total shard count.
        n: usize,
        /// The child's exit status, rendered.
        status: String,
    },
    /// An in-process shard thread panicked (should never happen; surfaced rather
    /// than swallowed).
    #[error("shard {k}/{n} worker thread panicked")]
    ShardPanicked {
        /// 1-based shard index.
        k: usize,
        /// Total shard count.
        n: usize,
    },
    /// Writing a merged / per-shard artifact failed.
    #[error("writing {path}: {source}")]
    Io {
        /// The path being written.
        path: PathBuf,
        /// Underlying I/O error.
        source: std::io::Error,
    },
}

/// Options for a shard-group run.
#[derive(Debug, Clone)]
pub struct ShardGroupOpts {
    /// Number of shards `N` (`>= 1`).
    pub n: usize,
    /// Directory the group writes into: per-shard `shard_k.json`
    /// ([`ShardVerdicts`]), the pre-pass snapshot, and (if set) the merged
    /// output. Created if absent.
    pub work_dir: PathBuf,
    /// Optional path to write the merged [`MergedVerdicts`] JSON.
    pub merged_out: Option<PathBuf>,
    /// Optional path to write the merged `.mathverse` provenance shard. When set,
    /// each shard emits its OWN range's constants to `shard_k.mathverse` under
    /// [`Self::work_dir`] and the group merges them into this one artifact,
    /// equivalent to the unsharded stream's `.mathverse` output.
    pub mathverse_out: Option<PathBuf>,
    /// Use the pre-pass hand-off: export the shared post-pre-pass state once and
    /// have every shard load it, skipping the O(T) registry scan per shard.
    pub prepass: bool,
    /// Acquire the machine-wide verify lock (leader). Set `false` when the caller
    /// (e.g. the harness) already holds it.
    pub acquire_lock: bool,
    /// Override the verify-lock path (default: `work_dir/.clean_verify.lock`).
    pub lock_path: Option<PathBuf>,
    /// Per-shard worker-thread stack size (in-process runner). Proof translation
    /// recurses deeply; defaults to [`super::parallel_streaming::WORKER_STACK`].
    pub stack_size: usize,
}

impl ShardGroupOpts {
    /// Options for an `n`-way group whose artifacts live under `work_dir`, with
    /// all the optional knobs at their defaults (no merged-out file, no pre-pass,
    /// acquire the lock, default lock path + stack size).
    #[must_use]
    pub fn new(n: usize, work_dir: impl Into<PathBuf>) -> Self {
        Self {
            n,
            work_dir: work_dir.into(),
            merged_out: None,
            mathverse_out: None,
            prepass: false,
            acquire_lock: true,
            lock_path: None,
            stack_size: super::parallel_streaming::WORKER_STACK,
        }
    }

    fn effective_lock_path(&self) -> PathBuf {
        self.lock_path
            .clone()
            .unwrap_or_else(|| self.work_dir.join(".clean_verify.lock"))
    }
}

/// The per-shard verdicts artifact path within a group's work dir.
fn shard_out_path(work_dir: &Path, k: usize) -> PathBuf {
    work_dir.join(format!("shard_{k}.json"))
}

/// The per-shard `.mathverse` provenance-shard path within a group's work dir
/// (written only when [`ShardGroupOpts::mathverse_out`] is set).
fn shard_mathverse_path(work_dir: &Path, k: usize) -> PathBuf {
    work_dir.join(format!("shard_{k}.mathverse"))
}

/// Prepare a group run: validate `n`, create the work dir, (optionally) acquire
/// the leader lock, and (optionally) export the pre-pass snapshot once. Returns
/// the held lock guard (kept alive for the run) and the pre-pass path.
fn prepare(
    serial_sorted_corpus: &Path,
    opts: &ShardGroupOpts,
) -> Result<(Option<VerifyLock>, Option<PathBuf>), ShardGroupError> {
    // Validate n up front (a 0/N or malformed group is a loud error).
    ShardSpec::new(1, opts.n)?;
    std::fs::create_dir_all(&opts.work_dir).map_err(|source| ShardGroupError::Io {
        path: opts.work_dir.clone(),
        source,
    })?;
    let lock = if opts.acquire_lock {
        Some(VerifyLock::acquire(opts.effective_lock_path())?)
    } else {
        None
    };
    let prepass = if opts.prepass {
        let pp = opts.work_dir.join(PREPASS_FILE);
        export_prepass_snapshot(serial_sorted_corpus, &pp)?;
        Some(pp)
    } else {
        None
    };
    Ok((lock, prepass))
}

/// Merge a group's per-shard verdicts, persist each shard's JSON + the merged
/// artifact, and return the merged stream. Shared tail of both runners.
fn finalize(
    parts: &[ShardVerdicts],
    opts: &ShardGroupOpts,
    already_on_disk: bool,
) -> Result<MergedVerdicts, ShardGroupError> {
    if !already_on_disk {
        for part in parts {
            part.save(shard_out_path(&opts.work_dir, part.k))?;
        }
    }
    let merged = merge_shard_verdicts(parts)?;
    if let Some(out) = &opts.merged_out {
        let bytes = serde_json::to_vec_pretty(&merged)
            .map_err(|e| StreamError::Io(std::io::Error::other(e)))?;
        std::fs::write(out, bytes).map_err(|source| ShardGroupError::Io {
            path: out.clone(),
            source,
        })?;
    }
    // Merge the per-range `.mathverse` shards (each shard wrote its own range's
    // constants to `shard_k.mathverse`) into one artifact equivalent to the
    // unsharded stream's output. The shards must be combined in serial/line order,
    // so order the shard indices by their `lo` (== `ShardSpec::range` order).
    if let Some(mv_out) = &opts.mathverse_out {
        let mut ordered: Vec<&ShardVerdicts> = parts.iter().collect();
        ordered.sort_by_key(|s| s.lo);
        let shard_mathverse: Vec<PathBuf> = ordered
            .iter()
            .map(|s| shard_mathverse_path(&opts.work_dir, s.k))
            .collect();
        merge_shard_mathverse(&shard_mathverse, mv_out)?;
    }
    Ok(merged)
}

/// Run an `N`-way shard group **in one process**, fanning the shards out over
/// `N` big-stack threads, and merge them into the single verdict stream a serial
/// run would produce (byte-identical). Each shard runs the full deterministic
/// replay recording only its range; every per-shard `shard_k.json` and the
/// optional merged output are written under [`ShardGroupOpts::work_dir`].
///
/// `serial_sorted_corpus` must be serial-ascending (deps-before-uses) — the same
/// precondition as [`import_proven_theorems_streaming_shard`]. The shards read it
/// concurrently read-only, which is safe.
///
/// # Errors
/// [`ShardGroupError`] on a bad `n`, a lock failure, a shard verify error, a
/// worker-thread panic, or an artifact write failure.
pub fn run_shard_group_in_process(
    serial_sorted_corpus: impl AsRef<Path>,
    opts: &ShardGroupOpts,
) -> Result<MergedVerdicts, ShardGroupError> {
    let corpus = serial_sorted_corpus.as_ref();
    let (_lock, prepass) = prepare(corpus, opts)?;

    // Spawn one big-stack thread per shard. Owned captures keep the closures
    // `'static`; each shard entry installs its own VerifyConfig on its thread.
    let mut handles = Vec::with_capacity(opts.n);
    for k in 1..=opts.n {
        let spec = ShardSpec::new(k, opts.n)?;
        let corpus = corpus.to_path_buf();
        let prepass = prepass.clone();
        // Emit this shard's per-range `.mathverse` only when the group is
        // producing a merged provenance shard.
        let emit_path = opts
            .mathverse_out
            .as_ref()
            .map(|_| shard_mathverse_path(&opts.work_dir, k));
        let n = opts.n;
        let handle = std::thread::Builder::new()
            .name(format!("isa-shard-{k}-of-{n}"))
            .stack_size(opts.stack_size)
            .spawn(move || -> Result<ShardVerdicts, StreamError> {
                let mut writer = ShardWriter::new();
                import_proven_theorems_streaming_shard_emit(
                    &corpus,
                    &mut writer,
                    spec,
                    prepass.as_deref(),
                    emit_path.as_deref(),
                )
            })
            .map_err(|source| ShardGroupError::Spawn { k, n, source })?;
        handles.push((k, handle));
    }

    let mut parts = Vec::with_capacity(opts.n);
    for (k, handle) in handles {
        let verds = handle
            .join()
            .map_err(|_| ShardGroupError::ShardPanicked { k, n: opts.n })??;
        parts.push(verds);
    }

    finalize(&parts, opts, false)
}

/// How to spawn one shard **child process** — the program, its base args, and
/// the base env applied to every child. The driver adds `ISA_SHARD=k/N`,
/// `ISA_SHARD_VERDICTS_OUT=<work_dir>/shard_k.json`, `ISA_VERIFY_LOCK=held`, and
/// (with pre-pass) `ISA_SHARD_PREPASS=<snapshot>` per child.
#[derive(Debug, Clone)]
pub struct ChildCommand {
    /// The program to run (e.g. `cargo`, or the `clean` binary).
    pub program: String,
    /// Its arguments (e.g. the harness test invocation).
    pub args: Vec<String>,
    /// Base environment applied to every child (e.g. `ISA_CLOSURE_STREAM`,
    /// `ISA_CLOSURE_STREAM_SORTED`, `ISA_CLOSURE_STREAM_PRESORTED=1`).
    pub envs: Vec<(String, String)>,
}

/// Run an `N`-way shard group by spawning `N` **child processes**, waiting for
/// all of them, then loading and merging the `shard_k.json` each wrote. The
/// leader holds ONE verify lock; every child inherits `ISA_VERIFY_LOCK=held` so
/// it bypasses the lock rather than failing `Held`. True process isolation — the
/// production scaling path.
///
/// Each child is expected to write its [`ShardVerdicts`] to the
/// `ISA_SHARD_VERDICTS_OUT` path the driver injects (the harness's `ISA_SHARD`
/// branch does exactly this).
///
/// # Errors
/// [`ShardGroupError`] on a bad `n`, a lock failure, a spawn failure, a non-zero
/// child exit, a missing/invalid per-shard artifact, or a merge/write failure.
pub fn run_shard_group_subprocess(
    serial_sorted_corpus: impl AsRef<Path>,
    opts: &ShardGroupOpts,
    child: &ChildCommand,
) -> Result<MergedVerdicts, ShardGroupError> {
    let corpus = serial_sorted_corpus.as_ref();
    let (_lock, prepass) = prepare(corpus, opts)?;

    // Spawn all children first (they run concurrently), recording each one's
    // expected verdicts path.
    let mut running = Vec::with_capacity(opts.n);
    let mut out_paths = Vec::with_capacity(opts.n);
    for k in 1..=opts.n {
        let out = shard_out_path(&opts.work_dir, k);
        let mut cmd = std::process::Command::new(&child.program);
        cmd.args(&child.args);
        for (key, val) in &child.envs {
            cmd.env(key, val);
        }
        cmd.env("ISA_SHARD", format!("{k}/{}", opts.n));
        cmd.env("ISA_SHARD_VERDICTS_OUT", &out);
        // The leader holds the lock; children bypass it (never a second acquire).
        cmd.env("ISA_VERIFY_LOCK", "held");
        if let Some(pp) = &prepass {
            cmd.env("ISA_SHARD_PREPASS", pp);
        }
        // When the group produces a merged provenance shard, each child emits its
        // OWN range's `.mathverse` to the path the leader will later merge.
        if opts.mathverse_out.is_some() {
            cmd.env(
                "ISA_SHARD_MATHVERSE_OUT",
                shard_mathverse_path(&opts.work_dir, k),
            );
        }
        let handle = cmd.spawn().map_err(|source| ShardGroupError::Spawn {
            k,
            n: opts.n,
            source,
        })?;
        running.push((k, handle));
        out_paths.push(out);
    }

    // Wait for all children; a non-zero exit is a loud group failure.
    for (k, mut handle) in running {
        let status = handle.wait().map_err(|source| ShardGroupError::Spawn {
            k,
            n: opts.n,
            source,
        })?;
        if !status.success() {
            return Err(ShardGroupError::ChildFailed {
                k,
                n: opts.n,
                status: status.to_string(),
            });
        }
    }

    // Load each child's artifact (children already wrote them) and merge.
    let mut parts = Vec::with_capacity(opts.n);
    for out in &out_paths {
        parts.push(ShardVerdicts::load(out)?);
    }
    finalize(&parts, opts, true)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_shard_out_path_names_per_shard_file() {
        let dir = Path::new("/tmp/grp");
        assert_eq!(
            shard_out_path(dir, 3),
            PathBuf::from("/tmp/grp/shard_3.json")
        );
    }

    #[test]
    fn test_shard_mathverse_path_names_per_shard_shard_file() {
        let dir = Path::new("/tmp/grp");
        assert_eq!(
            shard_mathverse_path(dir, 2),
            PathBuf::from("/tmp/grp/shard_2.mathverse")
        );
    }

    #[test]
    fn test_effective_lock_path_defaults_under_work_dir() {
        let opts = ShardGroupOpts::new(4, "/tmp/grp");
        assert_eq!(
            opts.effective_lock_path(),
            PathBuf::from("/tmp/grp/.clean_verify.lock")
        );
        let mut o2 = opts;
        o2.lock_path = Some(PathBuf::from("/tmp/custom.lock"));
        assert_eq!(o2.effective_lock_path(), PathBuf::from("/tmp/custom.lock"));
    }
}
