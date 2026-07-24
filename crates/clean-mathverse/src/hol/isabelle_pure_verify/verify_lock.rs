// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Machine-wide advisory verify lock** — one verify GROUP at a time.
//!
//! The Isabelle stream verify is deterministic *in isolation* (see the design
//! note `designs/2026-07-15-isabelle-shard-verify.md`): the verify logic carries
//! no wall-clock fuel, its budgets are deterministic node/step counters, and the
//! parallel driver is verdict-identical to the serial one by construction. The
//! observed collapse of a slice's `KernelVerified` yield when it ran *alongside*
//! a grand run was therefore never a property of the verify math under CPU load —
//! it was contamination from **shared mutable state** between two concurrently
//! running verify runs (a shared on-disk scratch path, or — when two runs share
//! one OS process — the process-global env + first-wins `OnceLock` config).
//!
//! Until the sharded driver + isolated scratch paths are proven to make
//! concurrent verifying safe, this lock is the loud backstop: a second verify
//! GROUP that starts while one is already running **fails immediately with a
//! diagnostic** instead of silently producing depressed, untrustworthy numbers.
//!
//! # Model
//!
//! A verify GROUP (a single serial run, or a set of shard processes that together
//! cover one corpus) holds exactly ONE lock. The group leader calls
//! [`VerifyLock::acquire`]; the returned guard removes the lockfile on `Drop`.
//! Shard children do NOT re-acquire — the leader exports [`LOCK_HELD_ENV`]=`held`
//! into their environment, keeps the guard returned by
//! [`VerifyLock::export_child_env`] until every child is spawned, and each child's
//! [`VerifyLock::acquire`] sees it and returns a no-op guard. The whole group
//! therefore shares the leader's lock without leaking the bypass into later work.
//!
//! # The side-verify lease
//!
//! A grand run holds the PRIMARY lock for many hours. Serializing every *bounded*
//! side job (an `isabelle-flip-gate --check`/`--add`, a `verify-one`, a small
//! fixture replay) behind it turned a 30-second gate into a ~30-hour queue. The
//! [`SideVerifyLease`] ends that serialization: while a primary is held, ONE
//! bounded side verify may run **alongside** it, guarded by a second sentinel file
//! (`.clean_verify.side.lock`) carrying the same `pid=… started=… label=…` record
//! and stale-holder auto-reclaim as the primary. At most one side lease exists at a
//! time — the `O_EXCL` sentinel guarantees it.
//!
//! ## Why this is verdict-SAFE (not the 4,111 → 1,310 collapse redux)
//!
//! The original concurrent-verify collapse
//! (`designs/2026-07-15-isabelle-shard-verify.md` §0) was **not** the verify math
//! bending under CPU load — it was contamination from shared MUTABLE state between
//! two concurrently running verify runs. Both leaks are now closed, so two verify
//! processes are independent by construction:
//!
//! 1. **Per-process scratch is pid-unique.** Every on-disk scratch/temp path the
//!    lane writes is namespaced by [`std::process::id`] (this lock's own tmp paths,
//!    the snapshot/probe scratch dirs, `isa_*_<pid>` throughout), so two verify
//!    PROCESSES never collide on a scratch file. A side lease is always a
//!    **separate OS process** from the primary grand (a distinct `clean`
//!    invocation), so there is no shared on-disk verify state between them.
//! 2. **Config is thread-installed, never a process-global `OnceLock`.** The
//!    cross-run leak where a first-wins `OnceLock` froze one run's budget/flags for
//!    another co-hosted run is gone: config is a `Copy`
//!    [`VerifyConfig`](crate::hol::isabelle_verify_config::VerifyConfig) built once
//!    per entry point and installed on the running thread
//!    ([`VerifyConfig::install`](crate::hol::isabelle_verify_config::VerifyConfig::install)).
//!    Two processes have wholly separate address spaces regardless.
//! 3. **No shared mutable on-disk state between the two verify processes.** Each
//!    replay resolves `PThm` references against its OWN in-memory accumulating
//!    closure; the shard-determinism gate (`tests/isabelle_shard_determinism.rs`)
//!    is the standing evidence that concurrent replays produce **byte-identical
//!    merged verdicts** — that A/B equality is exactly the property a side verify
//!    relies on.
//!
//! ## Why RAM is the only residual risk (hence the gate)
//!
//! With scratch and config isolated, the two processes cannot influence each
//! other's *verdicts*. What they DO share is one machine's physical RAM: a grand
//! holds a large resident kernel environment, and a second full-resident verify on
//! top of it can drive the box into swap or an OS OOM/jetsam kill. That is the sole
//! remaining hazard, and it is a *liveness/throughput* risk, not a *correctness*
//! one (an OOM-killed side job produces no verdicts, never wrong ones). So the side
//! lease is gated ONLY on RAM: it declares a budget ([`SIDE_RAM_BUDGET_ENV`],
//! default [`SIDE_RAM_BUDGET_DEFAULT_GB`] GiB) and refuses unless a conservative
//! free-RAM estimate ([`free_ram_estimate_gb`]) covers `budget + `
//! [`SIDE_RAM_FLOOR_GB`]` GiB`. A kill-switch ([`SIDE_DISABLE_ENV`]`=0`) disables
//! the whole mechanism, and a side lease refuses outright when NO primary is held
//! (the caller then just takes the primary — the simple path stays primary-only).
//!
//! # Bypass / override
//!
//! - `ISA_VERIFY_LOCK=held` (or `bypass`/`1`): skip acquisition entirely — set by
//!   the group leader for its children, and by in-process tests.
//! - `ISA_VERIFY_LOCK_FORCE=1`: reclaim a stale lockfile (a previous run crashed
//!   without `Drop` running) before acquiring.
//! - `ISA_VERIFY_LOCK_PATH=<path>`: override the default lockfile location.
//! - `ISA_VERIFY_LOCK_LABEL=<text>`: a human label for THIS group (e.g.
//!   `release grand`) recorded in the lockfile so `isabelle-doctor`'s verify-busy
//!   check can report *which* run holds the lock.
//!
//! # Lockfile record
//!
//! The holder writes one line — `pid=<pid> started=<unix-secs> label=<text>` —
//! at acquire. `label=` is written LAST so it may contain spaces; it is empty
//! when [`LOCK_LABEL_ENV`] is unset. A contender reads this back for its loud
//! error, and the doctor parses it to name the holder. Legacy/empty lockfiles
//! (from before this record existed) are read back verbatim and degrade to
//! "unknown".
//!
//! # Why an `O_EXCL` sentinel, not `flock(2)`
//!
//! `create_new` (`O_CREAT|O_EXCL`) is a portable, `unsafe`-free mutual-exclusion
//! primitive: exactly one creator wins the race. `flock`'s auto-release on process
//! death is operationally nicer, but it costs an `unsafe` FFI block the crate
//! otherwise avoids, and the loud-error-plus-`FORCE`-reclaim path handles a stale
//! lock cleanly enough for a coarse "one group at a time" guard.

use std::io::Write as _;
use std::path::{Path, PathBuf};

use crate::process_env::ScopedEnv;

/// Environment variable a group leader exports so its shard children bypass the
/// lock the leader already holds.
pub const LOCK_HELD_ENV: &str = "ISA_VERIFY_LOCK";

/// Reclaim a stale lockfile before acquiring (a previous run left one behind).
pub const LOCK_FORCE_ENV: &str = "ISA_VERIFY_LOCK_FORCE";

/// Override the default lockfile path.
pub const LOCK_PATH_ENV: &str = "ISA_VERIFY_LOCK_PATH";

/// A human label for this verify group, recorded in the lockfile so the doctor
/// can name the holder (e.g. `release grand`).
pub const LOCK_LABEL_ENV: &str = "ISA_VERIFY_LOCK_LABEL";

/// Kill-switch for the whole [`SideVerifyLease`] mechanism. Set to `0` (or `off`)
/// to disable side leases entirely — every bounded side job then falls back to
/// waiting on the primary lock exactly as before. Unset ⇒ side leases enabled.
pub const SIDE_DISABLE_ENV: &str = "ISA_SIDE_VERIFY";

/// The RAM budget (in **GiB**) a side verify declares for itself. Acquisition
/// refuses unless the conservative free-RAM estimate covers `budget +`
/// [`SIDE_RAM_FLOOR_GB`]. Defaults to [`SIDE_RAM_BUDGET_DEFAULT_GB`] when unset or
/// unparseable.
pub const SIDE_RAM_BUDGET_ENV: &str = "ISA_SIDE_VERIFY_RAM_GB";

/// Override the default side-lease sentinel path (mirrors [`LOCK_PATH_ENV`] for
/// the primary). Default: `.clean_verify.side.lock` beside the primary lockfile.
pub const SIDE_LOCK_PATH_ENV: &str = "ISA_SIDE_VERIFY_LOCK_PATH";

/// Default side-verify RAM budget in GiB when [`SIDE_RAM_BUDGET_ENV`] is unset.
pub const SIDE_RAM_BUDGET_DEFAULT_GB: u64 = 6;

/// Hard free-RAM floor (GiB) added ON TOP of the declared budget: a side lease is
/// refused unless the estimate covers `budget + SIDE_RAM_FLOOR_GB`. The floor is
/// the conservatism margin that absorbs free-RAM estimation error and leaves
/// working headroom for the OS + the primary grand.
pub const SIDE_RAM_FLOOR_GB: u64 = 4;

/// Scoped export of [`LOCK_HELD_ENV`] for child-process spawning.
///
/// Keep this value alive until every child has been spawned. Dropping it
/// restores the exact ambient value while still holding the crate-wide process
/// environment lock.
#[must_use = "keep this guard alive until every verify child has been spawned"]
pub struct ChildEnvGuard {
    _env: ScopedEnv,
}

/// The fixed sentinel filename for a side lease, placed beside the primary
/// lockfile so the doctor and the leaser agree on its location.
const SIDE_LOCK_FILENAME: &str = ".clean_verify.side.lock";

/// Failure modes of [`VerifyLock::acquire`].
#[derive(Debug, thiserror::Error)]
pub enum VerifyLockError {
    /// Another verify group already holds the lock. The message names the holder
    /// recorded in the lockfile so an operator can find the offending process.
    #[error(
        "another verify group already holds {path} — refusing to run concurrently \
         (holder: {holder}). Wait for it to finish, or set {force}=1 to reclaim a \
         stale lock, or {bypass}=held to bypass.",
        force = LOCK_FORCE_ENV,
        bypass = LOCK_HELD_ENV
    )]
    Held {
        /// The lockfile path.
        path: String,
        /// The `pid=… started=…` record read from the held lockfile.
        holder: String,
    },
    /// The lockfile could not be created/removed for a reason other than "already
    /// held" (e.g. the parent directory is missing or unwritable).
    #[error("verify lock I/O at {path}: {source}")]
    Io {
        /// The lockfile path.
        path: String,
        /// Underlying I/O error.
        source: std::io::Error,
    },
}

/// A held machine-wide verify lock. Dropping the guard releases the lock. A no-op
/// guard (`owned == None`) is returned when the lock was bypassed via
/// [`LOCK_HELD_ENV`]; dropping it does nothing.
#[derive(Debug)]
#[must_use = "the lock is released when the guard is dropped; bind it for the run's lifetime"]
pub struct VerifyLock {
    /// `Some(path)` when THIS guard created the lockfile and must remove it on
    /// drop; `None` when acquisition was bypassed (a shard child or a test).
    owned: Option<PathBuf>,
}

impl VerifyLock {
    /// Acquire the machine-wide verify lock at `lock_path`.
    ///
    /// Returns a bypass (no-op) guard when [`LOCK_HELD_ENV`] is `held`/`bypass`/`1`.
    /// Otherwise creates the lockfile atomically; if it already exists, returns
    /// [`VerifyLockError::Held`] (unless [`LOCK_FORCE_ENV`] is set, which reclaims
    /// it first).
    ///
    /// # Errors
    /// [`VerifyLockError::Held`] when another group holds the lock;
    /// [`VerifyLockError::Io`] on any other filesystem failure.
    pub fn acquire(lock_path: impl AsRef<Path>) -> Result<Self, VerifyLockError> {
        let lock_path = lock_path.as_ref();
        if bypass_requested() {
            return Ok(Self { owned: None });
        }
        if std::env::var_os(LOCK_FORCE_ENV).is_some() {
            // Best-effort reclaim; a genuine removal failure surfaces below when
            // `create_new` still cannot make the file.
            let _ = std::fs::remove_file(lock_path);
        }
        // At most one stale-holder reclaim per acquire: a crash that leaves the
        // lockfile behind (holder pid recorded but DEAD) must not stall polite
        // waiters for their whole timeout (measured: 4h of gate registrations
        // burned waiting on an orphaned holder).
        let mut reclaimed_stale = false;
        loop {
            match std::fs::OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(lock_path)
            {
                Ok(mut f) => {
                    // Record the holder for the loud error the next contender prints
                    // and for the doctor's verify-busy report. `label=` is last so it
                    // may contain spaces (e.g. `release grand`); empty when unset.
                    let _ = writeln!(
                        f,
                        "pid={} started={} label={}",
                        std::process::id(),
                        now_unix_secs(),
                        lock_label()
                    );
                    let _ = f.flush();
                    return Ok(Self {
                        owned: Some(lock_path.to_path_buf()),
                    });
                }
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => {
                    let holder = std::fs::read_to_string(lock_path)
                        .ok()
                        .map(|s| s.trim().to_string())
                        .filter(|s| !s.is_empty())
                        .unwrap_or_else(|| "unknown".to_string());
                    if !reclaimed_stale && holder_pid_dead(&holder) {
                        eprintln!(
                            "verify lock {}: recorded holder is DEAD ({holder}) — \
                             reclaiming the stale lock",
                            lock_path.display()
                        );
                        let _ = std::fs::remove_file(lock_path);
                        reclaimed_stale = true;
                        continue;
                    }
                    return Err(VerifyLockError::Held {
                        path: lock_path.display().to_string(),
                        holder,
                    });
                }
                Err(source) => {
                    return Err(VerifyLockError::Io {
                        path: lock_path.display().to_string(),
                        source,
                    });
                }
            }
        }
    }

    /// Acquire at the default lockfile path ([`default_lock_path`]).
    ///
    /// # Errors
    /// As [`VerifyLock::acquire`].
    pub fn acquire_default() -> Result<Self, VerifyLockError> {
        Self::acquire(default_lock_path())
    }

    /// Whether this guard actually owns (holds) the lock, as opposed to being a
    /// bypass no-op.
    #[must_use]
    pub fn is_owned(&self) -> bool {
        self.owned.is_some()
    }

    /// Export [`LOCK_HELD_ENV`]=`held` into the current process environment so
    /// child processes spawned for this shard group bypass the lock the leader
    /// already holds. The group leader keeps the returned guard until all
    /// children have been spawned.
    ///
    /// Call before spawning any threads that read the environment (the group
    /// leader does so at startup), matching the crate's existing single-threaded
    /// env-setup discipline.
    pub fn export_child_env() -> ChildEnvGuard {
        let mut env = ScopedEnv::new();
        env.set(LOCK_HELD_ENV, "held");
        ChildEnvGuard { _env: env }
    }
}

impl Drop for VerifyLock {
    fn drop(&mut self) {
        if let Some(path) = &self.owned {
            let _ = std::fs::remove_file(path);
        }
    }
}

/// The holder label from [`LOCK_LABEL_ENV`], trimmed; empty string when unset or
/// blank (so the lockfile always has a well-formed `label=` field).
fn lock_label() -> String {
    std::env::var(LOCK_LABEL_ENV)
        .ok()
        .map(|s| s.trim().to_string())
        .filter(|s| !s.is_empty())
        .unwrap_or_default()
}

/// Whether lock acquisition is bypassed via [`LOCK_HELD_ENV`].
fn bypass_requested() -> bool {
    matches!(
        std::env::var(LOCK_HELD_ENV).ok().as_deref(),
        Some("held") | Some("bypass") | Some("1")
    )
}

/// The default machine-wide lockfile path:
/// `$ISA_VERIFY_LOCK_PATH`, else `$HOME/isabelle-work/.clean_verify.lock`, else
/// (no `HOME`) a temp-dir fallback so acquisition never silently no-ops.
#[must_use]
pub fn default_lock_path() -> PathBuf {
    if let Some(p) = std::env::var_os(LOCK_PATH_ENV) {
        return PathBuf::from(p);
    }
    if let Some(home) = std::env::var_os("HOME") {
        return PathBuf::from(home)
            .join("isabelle-work")
            .join(".clean_verify.lock");
    }
    std::env::temp_dir().join(".clean_verify.lock")
}

/// The side-lease sentinel path that sits beside a given primary lockfile
/// (`.clean_verify.side.lock` in the same directory). Shared by the leaser and the
/// doctor so both agree on where a side lease is recorded.
#[must_use]
pub fn side_lock_path_for(primary: &Path) -> PathBuf {
    primary.with_file_name(SIDE_LOCK_FILENAME)
}

/// The default side-lease sentinel path: `$ISA_SIDE_VERIFY_LOCK_PATH` if set, else
/// [`side_lock_path_for`] applied to [`default_lock_path`].
#[must_use]
pub fn default_side_lock_path() -> PathBuf {
    if let Some(p) = std::env::var_os(SIDE_LOCK_PATH_ENV) {
        return PathBuf::from(p);
    }
    side_lock_path_for(&default_lock_path())
}

// ---------------------------------------------------------------------------
// Side-verify lease
// ---------------------------------------------------------------------------

/// Failure modes of [`SideVerifyLease::acquire`]. Only [`Self::NoPrimary`] asks
/// the caller to change course (take the primary instead); every other variant is
/// a loud "side lease unavailable" the caller absorbs by waiting on the primary.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum SideLeaseError {
    /// The kill-switch [`SIDE_DISABLE_ENV`]`=0` disabled the whole mechanism.
    #[error("side-verify lease disabled by {env}=0", env = SIDE_DISABLE_ENV)]
    Disabled,
    /// No primary verify is held, so a side lease makes no sense — the caller
    /// should take the primary lock directly (the simple path stays primary-only).
    #[error(
        "no primary verify is held — take the primary lock directly \
         (a side lease only runs ALONGSIDE a held primary)"
    )]
    NoPrimary,
    /// The conservative free-RAM estimate is below `budget + floor`: a second
    /// full-resident verify would risk driving the box into swap / an OOM kill.
    #[error(
        "side-verify lease refused: estimated free RAM {free_gb} GiB < required \
         {need_gb} GiB (budget {budget_gb} + {floor_gb} GiB floor) — a second verify \
         alongside the primary would risk OOM"
    )]
    Ram {
        /// The conservative free-RAM estimate (GiB).
        free_gb: u64,
        /// The required free RAM (`budget + floor`, GiB).
        need_gb: u64,
        /// The declared budget (GiB).
        budget_gb: u64,
        /// The hard floor added on top of the budget (GiB).
        floor_gb: u64,
    },
    /// Free RAM could not be estimated at all (probe failed / unparseable). We
    /// refuse rather than risk OOM on an unknown machine state.
    #[error(
        "side-verify lease refused: free RAM could not be estimated (need {need_gb} GiB) \
         — refusing rather than risk OOM"
    )]
    RamUnknown {
        /// The required free RAM that could not be confirmed (`budget + floor`, GiB).
        need_gb: u64,
    },
    /// A side lease is already held by a live process — at most ONE at a time.
    #[error(
        "a side-verify lease is already held at {path} (holder: {holder}) — only ONE \
         side lease at a time"
    )]
    Held {
        /// The side sentinel path.
        path: String,
        /// The `pid=… started=… label=…` record read from the held side sentinel.
        holder: String,
    },
    /// The side sentinel could not be created/removed for a reason other than
    /// "already held" (e.g. an unwritable directory).
    #[error("side-verify lease I/O at {path}: {source}")]
    Io {
        /// The side sentinel path.
        path: String,
        /// Underlying I/O error.
        source: std::io::Error,
    },
}

/// A held side-verify lease: a single BOUNDED verify running alongside a primary.
/// Dropping the guard removes the `.clean_verify.side.lock` sentinel. Acquired via
/// [`SideVerifyLease::acquire`] only when a primary is held, RAM is sufficient, and
/// the mechanism is enabled — see [`SideLeaseError`] for the refusal modes.
#[derive(Debug)]
#[must_use = "the side lease is released when the guard is dropped; bind it for the run's lifetime"]
pub struct SideVerifyLease {
    /// The side sentinel this guard created and must remove on drop.
    path: PathBuf,
    /// The conservative free-RAM estimate (GiB) at acquire time — for the loud
    /// "acquired a side lease" report the caller prints.
    free_ram_gb: u64,
    /// The declared RAM budget (GiB) this lease acquired under.
    budget_gb: u64,
}

impl SideVerifyLease {
    /// Acquire a side lease at the default paths ([`default_lock_path`] /
    /// [`default_side_lock_path`]).
    ///
    /// # Errors
    /// As [`SideVerifyLease::acquire`].
    pub fn acquire_default() -> Result<Self, SideLeaseError> {
        Self::acquire(default_lock_path(), default_side_lock_path())
    }

    /// Acquire a side lease guarded by (in order, all loud):
    /// 1. the kill-switch [`SIDE_DISABLE_ENV`] (→ [`SideLeaseError::Disabled`]);
    /// 2. a primary MUST be held at `primary_path` (→ [`SideLeaseError::NoPrimary`]);
    /// 3. the free-RAM gate `budget + floor` (→ [`SideLeaseError::Ram`] /
    ///    [`SideLeaseError::RamUnknown`]);
    /// 4. the one-at-a-time `O_EXCL` sentinel at `side_path`, with single
    ///    stale-holder auto-reclaim (→ [`SideLeaseError::Held`]).
    ///
    /// # Errors
    /// One of the [`SideLeaseError`] variants above, or [`SideLeaseError::Io`] on a
    /// filesystem failure creating the sentinel.
    pub fn acquire(
        primary_path: impl AsRef<Path>,
        side_path: impl AsRef<Path>,
    ) -> Result<Self, SideLeaseError> {
        let primary_path = primary_path.as_ref();
        let side_path = side_path.as_ref();

        if side_disabled() {
            return Err(SideLeaseError::Disabled);
        }
        if !primary_is_held(primary_path) {
            return Err(SideLeaseError::NoPrimary);
        }
        let budget_gb = side_ram_budget_gb();
        let free_ram_gb = side_ram_gate(budget_gb)?;

        // One side lease at a time: O_EXCL sentinel, with at most one stale-holder
        // reclaim (a crashed side job must not block the next polite waiter).
        let mut reclaimed_stale = false;
        loop {
            match std::fs::OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(side_path)
            {
                Ok(mut f) => {
                    let _ = writeln!(
                        f,
                        "pid={} started={} label={}",
                        std::process::id(),
                        now_unix_secs(),
                        lock_label()
                    );
                    let _ = f.flush();
                    return Ok(Self {
                        path: side_path.to_path_buf(),
                        free_ram_gb,
                        budget_gb,
                    });
                }
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => {
                    let holder = std::fs::read_to_string(side_path)
                        .ok()
                        .map(|s| s.trim().to_string())
                        .filter(|s| !s.is_empty())
                        .unwrap_or_else(|| "unknown".to_string());
                    if !reclaimed_stale && holder_pid_dead(&holder) {
                        eprintln!(
                            "side-verify lease {}: recorded holder is DEAD ({holder}) — \
                             reclaiming the stale side lease",
                            side_path.display()
                        );
                        let _ = std::fs::remove_file(side_path);
                        reclaimed_stale = true;
                        continue;
                    }
                    return Err(SideLeaseError::Held {
                        path: side_path.display().to_string(),
                        holder,
                    });
                }
                Err(source) => {
                    return Err(SideLeaseError::Io {
                        path: side_path.display().to_string(),
                        source,
                    });
                }
            }
        }
    }

    /// The conservative free-RAM estimate (GiB) at acquire time.
    #[must_use]
    pub fn free_ram_gb(&self) -> u64 {
        self.free_ram_gb
    }

    /// The RAM budget (GiB) this lease acquired under.
    #[must_use]
    pub fn budget_gb(&self) -> u64 {
        self.budget_gb
    }
}

impl Drop for SideVerifyLease {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.path);
    }
}

/// The acquired verify authority: either the exclusive PRIMARY lock or a bounded
/// SIDE lease running alongside a live primary. Both variants own their sentinel
/// and release it on `Drop`; bind one for the verify run's lifetime.
#[derive(Debug)]
#[must_use = "the lock/lease is released when the guard is dropped; bind it for the run's lifetime"]
pub enum VerifyLease {
    /// The exclusive machine-wide primary lock.
    Primary(VerifyLock),
    /// A bounded side lease running alongside a held primary.
    Side(SideVerifyLease),
}

impl VerifyLease {
    /// A short human tag for the acquired mode (`"primary"` / `"side"`) — for the
    /// caller's loud "which mode did I get" report.
    #[must_use]
    pub fn mode(&self) -> &'static str {
        match self {
            VerifyLease::Primary(_) => "primary",
            VerifyLease::Side(_) => "side",
        }
    }

    /// Whether this is a side lease (as opposed to the exclusive primary lock).
    #[must_use]
    pub fn is_side(&self) -> bool {
        matches!(self, VerifyLease::Side(_))
    }
}

/// Whether the side-lease mechanism is disabled via [`SIDE_DISABLE_ENV`] (`0`/`off`).
fn side_disabled() -> bool {
    matches!(
        std::env::var(SIDE_DISABLE_ENV).ok().as_deref(),
        Some("0") | Some("off")
    )
}

/// The declared side-verify RAM budget in GiB ([`SIDE_RAM_BUDGET_ENV`]), defaulting
/// to [`SIDE_RAM_BUDGET_DEFAULT_GB`] when unset or unparseable.
fn side_ram_budget_gb() -> u64 {
    std::env::var(SIDE_RAM_BUDGET_ENV)
        .ok()
        .and_then(|s| s.trim().parse::<u64>().ok())
        .unwrap_or(SIDE_RAM_BUDGET_DEFAULT_GB)
}

/// The free-RAM gate: `Ok(free_gb)` when the estimate covers `budget + floor`, else
/// a loud [`SideLeaseError::Ram`] / [`SideLeaseError::RamUnknown`].
fn side_ram_gate(budget_gb: u64) -> Result<u64, SideLeaseError> {
    let need_gb = budget_gb + SIDE_RAM_FLOOR_GB;
    match free_ram_estimate_gb() {
        Some(free_gb) if free_gb >= need_gb => Ok(free_gb),
        Some(free_gb) => Err(SideLeaseError::Ram {
            free_gb,
            need_gb,
            budget_gb,
            floor_gb: SIDE_RAM_FLOOR_GB,
        }),
        None => Err(SideLeaseError::RamUnknown { need_gb }),
    }
}

/// Whether a primary verify is held at `primary_path`. Held ⇔ the lockfile exists
/// and its recorded holder pid is NOT definitely dead. A missing file ⇒ not held
/// (→ the caller takes the primary itself); an empty/unparseable-but-present file
/// ⇒ held (conservative: a primary exists, we cannot prove its holder dead).
fn primary_is_held(primary_path: &Path) -> bool {
    match std::fs::read_to_string(primary_path) {
        Ok(content) => {
            let record = content.trim();
            // Empty/garbled but present: cannot prove dead ⇒ treat as held.
            record.is_empty() || !holder_pid_dead(record)
        }
        Err(_) => false,
    }
}

/// A conservative estimate of currently-FREE physical RAM in GiB, or `None` when it
/// cannot be determined (the gate then refuses the lease).
///
/// The formula is deliberately a LOWER bound on what a new process can allocate
/// before the OS must swap out an active working set: it counts only the pages the
/// kernel can hand out cheaply (free + inactive/reclaimable + speculative
/// read-ahead) and never the resident working set (active/wired/compressed). The
/// [`SIDE_RAM_FLOOR_GB`] margin added by the gate absorbs the estimation error.
///
/// - **macOS:** parse `vm_stat` — page size × (free + inactive + speculative).
/// - **Linux/other:** `/proc/meminfo` `MemAvailable` (the kernel's own estimate).
#[must_use]
pub fn free_ram_estimate_gb() -> Option<u64> {
    #[cfg(test)]
    {
        if let Some(gb) = test_free_ram_override() {
            return Some(gb);
        }
    }
    free_ram_bytes_estimate().map(|bytes| bytes / (1024 * 1024 * 1024))
}

/// Platform free-RAM probe in bytes. Split from [`free_ram_estimate_gb`] so the
/// pure parsers ([`parse_vm_stat_free_bytes`], [`parse_meminfo_available_bytes`])
/// stay unit-testable without a host probe.
fn free_ram_bytes_estimate() -> Option<u64> {
    #[cfg(target_os = "macos")]
    {
        let out = std::process::Command::new("vm_stat").output().ok()?;
        parse_vm_stat_free_bytes(&String::from_utf8_lossy(&out.stdout))
    }
    #[cfg(not(target_os = "macos"))]
    {
        let text = std::fs::read_to_string("/proc/meminfo").ok()?;
        parse_meminfo_available_bytes(&text)
    }
}

/// Parse `vm_stat` output into a conservative free-bytes estimate:
/// `page_size × (Pages free + Pages inactive + Pages speculative)`. Returns `None`
/// if the page size or the `Pages free:` line cannot be parsed.
fn parse_vm_stat_free_bytes(output: &str) -> Option<u64> {
    let page_size = output
        .lines()
        .next()
        .and_then(|l| l.split("page size of ").nth(1))
        .and_then(|rest| rest.split_whitespace().next())
        .and_then(|n| n.parse::<u64>().ok())?;
    let mut free: Option<u64> = None;
    let mut inactive = 0u64;
    let mut speculative = 0u64;
    for line in output.lines() {
        if let Some(v) = vm_stat_pages(line, "Pages free:") {
            free = Some(v);
        } else if let Some(v) = vm_stat_pages(line, "Pages inactive:") {
            inactive = v;
        } else if let Some(v) = vm_stat_pages(line, "Pages speculative:") {
            speculative = v;
        }
    }
    let free = free?;
    Some(
        free.saturating_add(inactive)
            .saturating_add(speculative)
            .saturating_mul(page_size),
    )
}

/// Parse one `Pages <kind>:                 <count>.` line into its page count.
fn vm_stat_pages(line: &str, key: &str) -> Option<u64> {
    line.trim()
        .strip_prefix(key)?
        .trim()
        .trim_end_matches('.')
        .trim()
        .parse::<u64>()
        .ok()
}

/// Parse `/proc/meminfo` for `MemAvailable:` (in kB) → bytes.
fn parse_meminfo_available_bytes(output: &str) -> Option<u64> {
    output
        .lines()
        .find_map(|l| l.strip_prefix("MemAvailable:"))
        .and_then(|rest| rest.split_whitespace().next())
        .and_then(|kb| kb.parse::<u64>().ok())
        .map(|kb| kb * 1024)
}

/// Test-only free-RAM override so the RAM gate is exercisable without a real host
/// probe. `u64::MAX` = unset (fall through to the platform probe).
#[cfg(test)]
static TEST_FREE_RAM_GB: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(u64::MAX);

/// Read the test-only free-RAM override (`None` when unset).
#[cfg(test)]
fn test_free_ram_override() -> Option<u64> {
    let v = TEST_FREE_RAM_GB.load(std::sync::atomic::Ordering::SeqCst);
    (v != u64::MAX).then_some(v)
}

/// Install (or clear, with `None`) the test-only free-RAM override.
#[cfg(test)]
fn set_test_free_ram_gb(gb: Option<u64>) {
    TEST_FREE_RAM_GB.store(gb.unwrap_or(u64::MAX), std::sync::atomic::Ordering::SeqCst);
}

/// Whether the lockfile's recorded `pid=` holder is definitely DEAD. Conservative:
/// an unparseable/missing pid, a non-unix platform, or any probe failure reads as
/// "alive" (never reclaim on uncertainty; pid recycling likewise reads as alive).
fn holder_pid_dead(holder: &str) -> bool {
    let Some(pid) = holder
        .split_whitespace()
        .find_map(|t| t.strip_prefix("pid="))
        .and_then(|p| p.parse::<u32>().ok())
    else {
        return false;
    };
    pid_is_dead(pid)
}

/// Whether process `pid` is definitely DEAD. Conservative: this process itself, a
/// non-unix platform, or any probe failure reads as "alive" (never reclaim on
/// uncertainty; pid recycling likewise reads as alive).
fn pid_is_dead(pid: u32) -> bool {
    if pid == std::process::id() {
        return false;
    }
    #[cfg(unix)]
    {
        // `kill -0` = existence probe, sends no signal. EPERM (exit != 0 on a
        // live root-owned pid) is indistinguishable from dead here, but a verify
        // lock holder runs as this user, so treat probe failure as dead only
        // when the command itself ran.
        std::process::Command::new("kill")
            .arg("-0")
            .arg(pid.to_string())
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null())
            .status()
            .map(|s| !s.success())
            .unwrap_or(false)
    }
    #[cfg(not(unix))]
    {
        false
    }
}

/// Whether process `pid` is (probably) ALIVE — the negation of [`pid_is_dead`],
/// exposed so the doctor can suppress a stale (dead-holder) side-lease sentinel
/// from its "a side lease is running" report.
#[must_use]
pub fn holder_pid_alive(pid: u32) -> bool {
    !pid_is_dead(pid)
}

/// Seconds since the Unix epoch (0 if the clock is before it — diagnostic only).
fn now_unix_secs() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Mutex;

    /// These tests mutate the process-global lock env vars; serialize them so the
    /// default parallel test runner cannot interleave two runs' variables.
    static ENV_LOCK: Mutex<()> = Mutex::new(());

    fn scratch(tag: &str) -> PathBuf {
        let dir =
            std::env::temp_dir().join(format!("isa_verify_lock_{}_{}", tag, std::process::id()));
        std::fs::create_dir_all(&dir).expect("mk lock tmpdir");
        dir.join(".clean_verify.lock")
    }

    #[test]
    fn test_second_acquire_fails_loudly_while_first_held() {
        let _g = ENV_LOCK
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        // Ensure a clean, non-bypassed environment for this test.
        crate::process_env::remove_persistent(LOCK_HELD_ENV);
        crate::process_env::remove_persistent(LOCK_FORCE_ENV);
        let path = scratch("held");
        let _ = std::fs::remove_file(&path);

        let first = VerifyLock::acquire(&path).expect("first acquire holds");
        assert!(first.is_owned(), "first guard must own the lock");

        let second = VerifyLock::acquire(&path);
        match second {
            Err(VerifyLockError::Held { holder, .. }) => {
                assert!(
                    holder.contains("pid="),
                    "held error should name the holder, got {holder:?}"
                );
            }
            other => panic!("second concurrent acquire must fail Held, got {other:?}"),
        }

        // Releasing the first guard frees the lock for the next group.
        drop(first);
        let third = VerifyLock::acquire(&path).expect("acquire after release");
        assert!(third.is_owned());
    }

    #[test]
    fn test_bypass_env_returns_noop_guard() {
        let _g = ENV_LOCK
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let path = scratch("bypass");
        let _ = std::fs::remove_file(&path);
        crate::process_env::set_persistent(LOCK_HELD_ENV, "held");
        let g = VerifyLock::acquire(&path).expect("bypass acquire never fails");
        assert!(!g.is_owned(), "bypassed guard owns nothing");
        assert!(
            !path.exists(),
            "bypass must not create a lockfile: {}",
            path.display()
        );
        crate::process_env::remove_persistent(LOCK_HELD_ENV);
    }

    #[test]
    fn test_child_env_export_restores_ambient_value() {
        let _g = ENV_LOCK
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let mut ambient = ScopedEnv::new();
        ambient.set(LOCK_HELD_ENV, "ambient");

        {
            let _child_env = VerifyLock::export_child_env();
            assert_eq!(
                std::env::var(LOCK_HELD_ENV).expect("child bypass value"),
                "held",
                "children see the inherited bypass only while the guard lives"
            );
        }

        assert_eq!(
            std::env::var(LOCK_HELD_ENV).expect("restored ambient value"),
            "ambient",
            "dropping the child guard restores the exact ambient value"
        );
    }

    #[test]
    fn test_stale_dead_holder_auto_reclaims_without_force() {
        let _g = ENV_LOCK
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        crate::process_env::remove_persistent(LOCK_HELD_ENV);
        crate::process_env::remove_persistent(LOCK_FORCE_ENV);
        let path = scratch("stale_dead");
        // Simulate a stale lockfile left by a crashed run: recorded pid is dead.
        // (A polite waiter once burned 4h of gate registrations on exactly this.)
        std::fs::write(&path, "pid=99999999 started=0 label=\n").expect("write stale lock");
        let g = VerifyLock::acquire(&path).expect("dead-holder lock auto-reclaims");
        assert!(g.is_owned(), "reclaimed guard must own the lock");
    }

    #[test]
    fn test_live_holder_still_fails_held_and_force_reclaims() {
        let _g = ENV_LOCK
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        crate::process_env::remove_persistent(LOCK_HELD_ENV);
        crate::process_env::remove_persistent(LOCK_FORCE_ENV);
        let path = scratch("live_holder");
        // A lockfile naming a LIVE pid (this test process) must NOT auto-reclaim…
        std::fs::write(
            &path,
            format!("pid={} started=0 label=\n", std::process::id()),
        )
        .expect("write live-holder lock");
        assert!(matches!(
            VerifyLock::acquire(&path),
            Err(VerifyLockError::Held { .. })
        ));
        // …but the explicit force override still reclaims it.
        crate::process_env::set_persistent(LOCK_FORCE_ENV, "1");
        let g = VerifyLock::acquire(&path).expect("force reclaims even a live-holder lock");
        assert!(g.is_owned());
        crate::process_env::remove_persistent(LOCK_FORCE_ENV);
    }

    #[test]
    fn test_unparseable_holder_never_auto_reclaims() {
        let _g = ENV_LOCK
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        crate::process_env::remove_persistent(LOCK_HELD_ENV);
        crate::process_env::remove_persistent(LOCK_FORCE_ENV);
        let path = scratch("unparseable");
        // No pid record (legacy/garbled lockfile): conservative — treated as live.
        std::fs::write(&path, "garbled\n").expect("write garbled lock");
        assert!(matches!(
            VerifyLock::acquire(&path),
            Err(VerifyLockError::Held { .. })
        ));
    }

    #[test]
    fn test_lockfile_records_pid_started_and_label() {
        let _g = ENV_LOCK
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        crate::process_env::remove_persistent(LOCK_HELD_ENV);
        crate::process_env::remove_persistent(LOCK_FORCE_ENV);
        crate::process_env::set_persistent(LOCK_LABEL_ENV, "  release grand  ");
        let path = scratch("label");
        let _ = std::fs::remove_file(&path);

        let guard = VerifyLock::acquire(&path).expect("acquire records the label");
        assert!(guard.is_owned());
        let recorded = std::fs::read_to_string(&path).expect("lockfile is readable");
        assert!(
            recorded.contains(&format!("pid={}", std::process::id())),
            "records this pid: {recorded:?}"
        );
        assert!(
            recorded.contains("started="),
            "records a start time: {recorded:?}"
        );
        // The env label is trimmed and may contain spaces.
        assert!(
            recorded.contains("label=release grand"),
            "records the trimmed label verbatim: {recorded:?}"
        );
        crate::process_env::remove_persistent(LOCK_LABEL_ENV);
    }

    #[test]
    fn test_lockfile_label_empty_when_env_unset() {
        let _g = ENV_LOCK
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        crate::process_env::remove_persistent(LOCK_HELD_ENV);
        crate::process_env::remove_persistent(LOCK_FORCE_ENV);
        crate::process_env::remove_persistent(LOCK_LABEL_ENV);
        let path = scratch("nolabel");
        let _ = std::fs::remove_file(&path);

        let _guard = VerifyLock::acquire(&path).expect("acquire without a label");
        let recorded = std::fs::read_to_string(&path).expect("lockfile is readable");
        // A well-formed but empty label field (nothing after `label=`).
        assert!(
            recorded.contains("label=\n") || recorded.trim_end().ends_with("label="),
            "empty label still writes the field: {recorded:?}"
        );
    }

    #[test]
    fn test_default_lock_path_honours_override() {
        let _g = ENV_LOCK
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        crate::process_env::set_persistent(LOCK_PATH_ENV, "/tmp/custom_verify.lock");
        assert_eq!(
            default_lock_path(),
            PathBuf::from("/tmp/custom_verify.lock")
        );
        crate::process_env::remove_persistent(LOCK_PATH_ENV);
    }

    // --- Side-verify lease ------------------------------------------------

    /// Reset every env var the side-lease path reads, so a leaked var from a prior
    /// test cannot skew this one.
    fn clean_side_env() {
        crate::process_env::remove_persistent(SIDE_DISABLE_ENV);
        crate::process_env::remove_persistent(SIDE_RAM_BUDGET_ENV);
        crate::process_env::remove_persistent(SIDE_LOCK_PATH_ENV);
        crate::process_env::remove_persistent(LOCK_LABEL_ENV);
    }

    /// A fresh (primary, side) sentinel pair under a pid-unique scratch dir, both
    /// pre-removed so each test starts from a clean slate.
    fn side_paths(tag: &str) -> (PathBuf, PathBuf) {
        let dir =
            std::env::temp_dir().join(format!("isa_side_lease_{}_{}", tag, std::process::id()));
        std::fs::create_dir_all(&dir).expect("mk side tmpdir");
        let primary = dir.join(".clean_verify.lock");
        let side = dir.join(SIDE_LOCK_FILENAME);
        let _ = std::fs::remove_file(&primary);
        let _ = std::fs::remove_file(&side);
        (primary, side)
    }

    /// Write a primary lockfile whose holder pid is THIS process (so it reads as a
    /// LIVE primary — `pid_is_dead` treats self as alive).
    fn write_live_primary(path: &Path) {
        std::fs::write(
            path,
            format!("pid={} started=0 label=grand\n", std::process::id()),
        )
        .expect("write live primary lockfile");
    }

    #[test]
    fn test_side_lease_acquires_while_primary_held() {
        let _g = ENV_LOCK
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        clean_side_env();
        crate::process_env::set_persistent(SIDE_RAM_BUDGET_ENV, "6");
        set_test_free_ram_gb(Some(100)); // plenty of headroom
        let (primary, side) = side_paths("acquire");
        write_live_primary(&primary);

        let lease = SideVerifyLease::acquire(&primary, &side)
            .expect("side lease acquires while a live primary is held with ample RAM");
        assert_eq!(lease.budget_gb(), 6);
        assert_eq!(lease.free_ram_gb(), 100);
        assert!(side.exists(), "side sentinel is created while held");
        let rec = std::fs::read_to_string(&side).expect("side sentinel readable");
        assert!(
            rec.contains(&format!("pid={}", std::process::id())),
            "side sentinel records this pid: {rec:?}"
        );

        drop(lease);
        assert!(
            !side.exists(),
            "dropping the lease removes the side sentinel"
        );

        set_test_free_ram_gb(None);
        clean_side_env();
    }

    #[test]
    fn test_second_side_lease_refused_one_at_a_time() {
        let _g = ENV_LOCK
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        clean_side_env();
        set_test_free_ram_gb(Some(100));
        let (primary, side) = side_paths("second");
        write_live_primary(&primary);

        let first = SideVerifyLease::acquire(&primary, &side).expect("first side lease acquires");
        match SideVerifyLease::acquire(&primary, &side) {
            Err(SideLeaseError::Held { holder, .. }) => assert!(
                holder.contains("pid="),
                "second side lease names the live holder: {holder:?}"
            ),
            other => panic!("second side lease must be refused Held, got {other:?}"),
        }
        drop(first);
        // Freed: the next side lease can acquire.
        let third =
            SideVerifyLease::acquire(&primary, &side).expect("side lease acquires after release");
        drop(third);

        set_test_free_ram_gb(None);
        clean_side_env();
    }

    #[test]
    fn test_side_lease_ram_below_budget_refused_loud() {
        let _g = ENV_LOCK
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        clean_side_env();
        crate::process_env::set_persistent(SIDE_RAM_BUDGET_ENV, "6");
        set_test_free_ram_gb(Some(5)); // 5 < budget 6 + floor 4 = 10
        let (primary, side) = side_paths("lowram");
        write_live_primary(&primary);

        match SideVerifyLease::acquire(&primary, &side) {
            Err(SideLeaseError::Ram {
                free_gb,
                need_gb,
                budget_gb,
                floor_gb,
            }) => {
                assert_eq!((free_gb, need_gb, budget_gb, floor_gb), (5, 10, 6, 4));
                let msg = SideLeaseError::Ram {
                    free_gb,
                    need_gb,
                    budget_gb,
                    floor_gb,
                }
                .to_string();
                assert!(msg.contains("OOM"), "RAM refusal is loud about OOM: {msg}");
            }
            other => panic!("low-RAM side lease must be refused Ram, got {other:?}"),
        }
        assert!(!side.exists(), "a refused side lease creates NO sentinel");

        set_test_free_ram_gb(None);
        clean_side_env();
    }

    #[test]
    fn test_stale_dead_side_lease_auto_reclaims() {
        let _g = ENV_LOCK
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        clean_side_env();
        set_test_free_ram_gb(Some(100));
        let (primary, side) = side_paths("stale");
        write_live_primary(&primary);
        // A crashed side job's leftover sentinel: recorded pid is dead.
        std::fs::write(&side, "pid=99999999 started=0 label=\n")
            .expect("write stale side sentinel");

        let lease = SideVerifyLease::acquire(&primary, &side)
            .expect("a dead-holder side sentinel auto-reclaims");
        assert!(side.exists());
        drop(lease);

        set_test_free_ram_gb(None);
        clean_side_env();
    }

    #[test]
    fn test_side_lease_kill_switch_disables() {
        let _g = ENV_LOCK
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        clean_side_env();
        set_test_free_ram_gb(Some(100)); // RAM is fine; the switch still wins
        crate::process_env::set_persistent(SIDE_DISABLE_ENV, "0");
        let (primary, side) = side_paths("killswitch");
        write_live_primary(&primary);

        assert!(
            matches!(
                SideVerifyLease::acquire(&primary, &side),
                Err(SideLeaseError::Disabled)
            ),
            "ISA_SIDE_VERIFY=0 disables the whole mechanism"
        );
        assert!(!side.exists(), "disabled ⇒ no sentinel");

        set_test_free_ram_gb(None);
        clean_side_env();
    }

    #[test]
    fn test_side_lease_refused_when_no_primary_held() {
        let _g = ENV_LOCK
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        clean_side_env();
        set_test_free_ram_gb(Some(100));
        let (primary, side) = side_paths("noprimary");
        // No primary lockfile written -> not held.
        assert!(
            matches!(
                SideVerifyLease::acquire(&primary, &side),
                Err(SideLeaseError::NoPrimary)
            ),
            "no primary held ⇒ refuse and let the caller take the primary"
        );
        // A primary with a DEAD holder is also "not held".
        std::fs::write(&primary, "pid=99999999 started=0 label=grand\n").expect("dead primary");
        assert!(matches!(
            SideVerifyLease::acquire(&primary, &side),
            Err(SideLeaseError::NoPrimary)
        ));

        set_test_free_ram_gb(None);
        clean_side_env();
    }

    #[test]
    fn test_free_ram_override_roundtrips_then_clears() {
        let _g = ENV_LOCK
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        set_test_free_ram_gb(Some(42));
        assert_eq!(free_ram_estimate_gb(), Some(42));
        set_test_free_ram_gb(None);
        // With the override cleared, the estimate falls back to the host probe
        // (which may be Some or None on this box — we only assert the override is
        // no longer forcing 42).
        assert_ne!(free_ram_estimate_gb(), Some(42));
    }

    #[test]
    fn test_side_lock_path_derivation_and_override() {
        let _g = ENV_LOCK
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        clean_side_env();
        assert_eq!(
            side_lock_path_for(Path::new("/work/.clean_verify.lock")),
            PathBuf::from("/work/.clean_verify.side.lock")
        );
        crate::process_env::set_persistent(SIDE_LOCK_PATH_ENV, "/tmp/custom.side.lock");
        assert_eq!(
            default_side_lock_path(),
            PathBuf::from("/tmp/custom.side.lock")
        );
        clean_side_env();
    }

    #[test]
    fn test_parse_vm_stat_free_bytes_sums_reclaimable_pages() {
        // page size 16384; free 100 + inactive 200 + speculative 50 = 350 pages.
        let out = "Mach Virtual Memory Statistics: (page size of 16384 bytes)\n\
                   Pages free:                              100.\n\
                   Pages active:                          9000.\n\
                   Pages inactive:                         200.\n\
                   Pages speculative:                       50.\n\
                   Pages wired down:                      5000.\n";
        assert_eq!(
            parse_vm_stat_free_bytes(out),
            Some(350 * 16384),
            "sums free+inactive+speculative × page size"
        );
        // Missing the header page size -> None.
        assert_eq!(parse_vm_stat_free_bytes("Pages free: 100.\n"), None);
    }

    #[test]
    fn test_parse_meminfo_available_bytes() {
        let out = "MemTotal:       65695484 kB\n\
                   MemFree:         1234567 kB\n\
                   MemAvailable:   40000000 kB\n";
        assert_eq!(
            parse_meminfo_available_bytes(out),
            Some(40_000_000u64 * 1024)
        );
        assert_eq!(parse_meminfo_available_bytes("MemTotal: 1 kB\n"), None);
    }
}
