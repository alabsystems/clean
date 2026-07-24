// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Flip-gate registry** — corpus-routing-verified proof of every claimed flip.
//!
//! # The gap this closes
//!
//! Fixture tests can prove a prover/discharge arm *works* on a hand-built input
//! and still be a lie at corpus scale: the round burned a 29-hour grand because
//! the escalation ladder never *routed* three target serials to the arm the
//! fixtures exercised. The claimed flips silently did not happen, and we only
//! learned after the grand.
//!
//! A **flip gate** removes that blind spot. It pins a durable, closure-complete
//! SLICE (the target serial plus its transitive proof-dependency closure — the
//! same minimal corpus [`super::isabelle_slice`] extracts) and asserts that
//! replaying it through the **real** library stream-verify entry
//! ([`super::isabelle_pure_verify::import_proven_theorems_streaming_shard`], the
//! same driver `isabelle-import` runs) lands the target serial
//! `KernelVerified`. Because the slice carries the real dependency closure and
//! the replay is the real driver, the gate exercises the real escalation
//! routing — so a claimed flip is verified BEFORE any grand (a bounded
//! per-serial replay, orders of magnitude cheaper than the whole-corpus grand),
//! not discovered missing after one.
//!
//! # Registry vs. slices
//!
//! The registry ([`data/isabelle_flip_gates.json`]) is committed and tiny; the
//! slices are 30–50 MB+ and live durably under
//! `~/isabelle-work/corpora/flip_gates/`, NOT in git. To detect a slice that
//! drifted (regenerated, truncated, corrupted) out from under a registered
//! expectation, each entry pins the slice's BLAKE3 digest and line count. A
//! `--check` recomputes both and fails loud on any mismatch — a drifted slice is
//! never silently replayed.

use std::collections::BTreeSet;
use std::io::Read as _;
use std::path::{Path, PathBuf};

use crate::hol::isabelle_pure_verify::{
    import_proven_theorems_streaming_shard, ShardSpec, ShardVerdicts,
};
use crate::hol::isabelle_slice::{extract_slice, SliceSelect};
use crate::shard::ShardWriter;

/// The committed registry path, relative to the repo root.
pub const REGISTRY_REL_PATH: &str = "data/isabelle_flip_gates.json";

/// The durable, portable (`~`-prefixed) home of the flip-gate slices. Slices are
/// too large to commit; they live here and are pinned by BLAKE3 + line count.
pub const GATES_DIR_PORTABLE: &str = "~/isabelle-work/corpora/flip_gates";

/// The only verdict a flip gate currently asserts. A gate fires iff the target
/// serial lands exactly this (tier-1, foundational-only) verdict — never tier-2,
/// ledger, or bridge, which the check keeps disabled by construction.
pub const EXPECTED_KERNEL_VERIFIED: &str = "KernelVerified";

/// Kernel replay recursion is deep; run every slice replay on a dedicated
/// big-stack thread so the gate works regardless of the caller's stack size
/// (matches the `isabelle-import` verb's `REPLAY_STACK`).
const REPLAY_STACK: usize = 2560 * 1024 * 1024;

/// Errors from the flip-gate registry and its check/add flows.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum FlipGateError {
    /// Reading or writing the registry / a slice file failed.
    #[error("flip-gate I/O on {path}: {source}")]
    Io {
        /// Path involved.
        path: PathBuf,
        /// Underlying error.
        source: std::io::Error,
    },
    /// The registry JSON could not be parsed or serialized.
    #[error("flip-gate registry JSON at {path}: {source}")]
    Json {
        /// Registry path.
        path: PathBuf,
        /// Underlying serde error.
        source: serde_json::Error,
    },
    /// `--add` was asked to register a serial that already has a gate.
    #[error("serial s{0} is already registered as a flip gate")]
    AlreadyRegistered(i64),
    /// Building the closure slice for `--add` failed.
    #[error("slice extraction: {0}")]
    Slice(#[from] crate::hol::isabelle_slice::IsabelleSliceError),
    /// The replay driver hit an I/O / snapshot error (not a per-line rejection —
    /// those are outcomes, never errors).
    #[error("slice replay: {0}")]
    Replay(String),
    /// Spawning the big-stack replay thread failed.
    #[error("spawning replay thread: {0}")]
    ReplayThread(std::io::Error),
    /// The big-stack replay thread panicked.
    #[error("replay thread panicked")]
    ReplayPanicked,
    /// `--add` built + replayed the slice but the target serial did NOT land
    /// `KernelVerified` under the current binary, so it is NOT a flip to
    /// register. The reject buckets seen across the slice are attached.
    #[error(
        "serial s{serial} did not KernelVerify under the current binary — not registering \
             a gate (reject buckets: {reasons})"
    )]
    NotAFlip {
        /// The serial that failed to flip.
        serial: i64,
        /// Human-rendered `reason x count` list over the whole slice.
        reasons: String,
    },
}

fn io_err(path: &Path) -> impl FnOnce(std::io::Error) -> FlipGateError + '_ {
    move |source| FlipGateError::Io {
        path: path.to_path_buf(),
        source,
    }
}

/// One registered flip gate: a pinned, closure-complete slice whose replay must
/// land `serial` at [`Self::expected`].
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct FlipGate {
    /// The target proof-term serial that must flip to `KernelVerified`.
    pub serial: i64,
    /// The theorem's shard-catalog name (as minted by the verify driver).
    pub name: String,
    /// Why this flip matters / how it was made to flip (free text).
    pub description: String,
    /// Durable, `~`-portable path to the closure slice (NOT committed).
    pub slice: String,
    /// The asserted verdict — currently always [`EXPECTED_KERNEL_VERIFIED`].
    pub expected: String,
    /// BLAKE3 hex digest of the slice bytes, pinned at registration (drift
    /// detection).
    pub blake3: String,
    /// Newline count of the slice, pinned at registration (drift detection).
    pub lines: u64,
    /// UTC date (`YYYY-MM-DD`) the gate was registered.
    pub added: String,
    /// The round / fix tag that made this serial flip.
    pub round: String,
}

/// The committed flip-gate registry: a versioned, serial-sorted list of gates.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct FlipGateRegistry {
    /// Registry schema version (bump on a breaking shape change).
    #[serde(default = "default_version")]
    pub version: u32,
    /// The registered gates, kept serial-ascending by [`Self::save`].
    #[serde(default)]
    pub gates: Vec<FlipGate>,
}

impl Default for FlipGateRegistry {
    /// The canonical empty registry carries the current schema version (not
    /// `u32::default()`), so a freshly bootstrapped registry writes `version: 1`.
    fn default() -> Self {
        Self {
            version: default_version(),
            gates: Vec::new(),
        }
    }
}

fn default_version() -> u32 {
    1
}

impl FlipGateRegistry {
    /// Load the registry from `path`. A **missing file** is not an error — it
    /// yields an empty registry (so a first `--add` bootstraps it and a
    /// `--check` on a fresh tree reports zero gates rather than crashing).
    ///
    /// # Errors
    /// [`FlipGateError::Io`] on a read failure other than "not found";
    /// [`FlipGateError::Json`] on malformed JSON.
    pub fn load(path: &Path) -> Result<Self, FlipGateError> {
        let bytes = match std::fs::read(path) {
            Ok(b) => b,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
                return Ok(Self::default());
            }
            Err(source) => {
                return Err(FlipGateError::Io {
                    path: path.to_path_buf(),
                    source,
                })
            }
        };
        serde_json::from_slice(&bytes).map_err(|source| FlipGateError::Json {
            path: path.to_path_buf(),
            source,
        })
    }

    /// Serialize the registry to `path` as pretty JSON with a trailing newline,
    /// gates sorted serial-ascending for a stable, review-friendly diff.
    ///
    /// # Errors
    /// [`FlipGateError::Json`] on a serialize failure; [`FlipGateError::Io`] on
    /// a write failure.
    pub fn save(&self, path: &Path) -> Result<(), FlipGateError> {
        let mut ordered = self.clone();
        ordered.gates.sort_by_key(|g| g.serial);
        let mut json =
            serde_json::to_string_pretty(&ordered).map_err(|source| FlipGateError::Json {
                path: path.to_path_buf(),
                source,
            })?;
        json.push('\n');
        if let Some(parent) = path.parent() {
            if !parent.as_os_str().is_empty() {
                std::fs::create_dir_all(parent).map_err(io_err(path))?;
            }
        }
        std::fs::write(path, json).map_err(io_err(path))
    }

    /// The registered gate for `serial`, if any.
    #[must_use]
    pub fn gate(&self, serial: i64) -> Option<&FlipGate> {
        self.gates.iter().find(|g| g.serial == serial)
    }
}

/// A slice's content fingerprint: BLAKE3 over the exact on-disk bytes plus the
/// newline count. Both are pinned in the registry so any regeneration,
/// truncation, or corruption of a slice is caught before it is replayed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SlicePin {
    /// BLAKE3 hex digest of the slice bytes.
    pub blake3: String,
    /// Number of `\n` bytes in the slice.
    pub lines: u64,
}

/// Compute the [`SlicePin`] of `slice` in one streaming pass (chunked read, so a
/// 50 MB slice never lands wholly in memory twice).
///
/// # Errors
/// [`FlipGateError::Io`] if the slice cannot be opened or read.
pub fn compute_pin(slice: &Path) -> Result<SlicePin, FlipGateError> {
    let mut file = std::fs::File::open(slice).map_err(io_err(slice))?;
    let mut hasher = blake3::Hasher::new();
    let mut lines: u64 = 0;
    let mut buf = vec![0u8; 1 << 20];
    loop {
        let n = file.read(&mut buf).map_err(io_err(slice))?;
        if n == 0 {
            break;
        }
        let chunk = &buf[..n];
        hasher.update(chunk);
        lines += chunk.iter().filter(|&&b| b == b'\n').count() as u64;
    }
    Ok(SlicePin {
        blake3: hasher.finalize().to_hex().to_string(),
        lines,
    })
}

/// The verdict of evaluating one registered gate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GateOutcome {
    /// The slice replayed and the target serial landed `KernelVerified`.
    Pass,
    /// The pinned slice file is absent on this machine (rebuild it before
    /// checking).
    MissingSlice(PathBuf),
    /// The slice on disk no longer matches the pinned fingerprint.
    Drift {
        /// The fingerprint recorded in the registry.
        expected: SlicePin,
        /// The fingerprint recomputed from the on-disk slice.
        actual: SlicePin,
    },
    /// The gate's `expected` field names a verdict this checker does not
    /// support (only [`EXPECTED_KERNEL_VERIFIED`] is understood today).
    UnsupportedExpected(String),
    /// The slice replayed cleanly but the target serial did NOT land
    /// `KernelVerified` — the flip regressed. Carries the whole-slice reject
    /// buckets for triage.
    Regressed {
        /// Human-rendered `reason x count` list over the whole slice.
        reasons: String,
    },
}

impl GateOutcome {
    /// Whether the gate passed.
    #[must_use]
    pub fn is_pass(&self) -> bool {
        matches!(self, GateOutcome::Pass)
    }

    /// A one-line, human-readable status for the PASS/FAIL report.
    #[must_use]
    pub fn describe(&self) -> String {
        match self {
            GateOutcome::Pass => "KernelVerified".to_string(),
            GateOutcome::MissingSlice(p) => {
                format!(
                    "MISSING SLICE {} — rebuild it (`--add` or `isabelle-slice`)",
                    p.display()
                )
            }
            GateOutcome::Drift { expected, actual } => format!(
                "SLICE DRIFT — pinned blake3 {}… / {} lines, on-disk {}… / {} lines",
                short_hash(&expected.blake3),
                expected.lines,
                short_hash(&actual.blake3),
                actual.lines,
            ),
            GateOutcome::UnsupportedExpected(v) => {
                format!("unsupported expected verdict `{v}` (only KernelVerified is supported)")
            }
            GateOutcome::Regressed { reasons } => {
                format!("REGRESSED — serial did NOT KernelVerify (reject buckets: {reasons})")
            }
        }
    }
}

fn short_hash(hex: &str) -> &str {
    &hex[..hex.len().min(12)]
}

/// Evaluate a single registered gate: existence → drift → replay → serial-in-KV.
///
/// A missing slice or a fingerprint drift is a **hard FAIL that never replays**
/// (the pin is the contract; a changed slice is not the registered artifact).
/// Only a slice that matches its pin is replayed.
///
/// # Errors
/// [`FlipGateError`] only for a genuine replay I/O / thread failure; a missing
/// slice, a drift, and a non-flip are returned as [`GateOutcome`]s, never errors.
pub fn evaluate_gate(gate: &FlipGate) -> Result<GateOutcome, FlipGateError> {
    if gate.expected != EXPECTED_KERNEL_VERIFIED {
        return Ok(GateOutcome::UnsupportedExpected(gate.expected.clone()));
    }
    let slice = crate::hol::isabelle_sessions::expand_tilde(Path::new(&gate.slice));
    if !slice.exists() {
        return Ok(GateOutcome::MissingSlice(slice));
    }
    let actual = compute_pin(&slice)?;
    let expected = SlicePin {
        blake3: gate.blake3.clone(),
        lines: gate.lines,
    };
    if actual != expected {
        return Ok(GateOutcome::Drift { expected, actual });
    }
    let verdicts = replay_slice(&slice)?;
    if kv_serials(&verdicts).contains(&gate.serial) {
        Ok(GateOutcome::Pass)
    } else {
        Ok(GateOutcome::Regressed {
            reasons: render_reasons(&verdicts),
        })
    }
}

/// Build a fresh closure slice for `serial`, replay it, and — only if the serial
/// lands `KernelVerified` — pin it and return the registry entry the caller
/// appends. The whole point is registering an EXPECTED flip: the serial must be
/// KernelVerified under the CURRENT binary before it is registered.
///
/// The built slice is written durably under `gates_dir`; on a non-flip it is
/// removed and [`FlipGateError::NotAFlip`] is returned (no gate is registered).
///
/// # Errors
/// [`FlipGateError::AlreadyRegistered`] if `serial` already has a gate;
/// [`FlipGateError::NotAFlip`] if the serial does not KernelVerify;
/// [`FlipGateError`] on slice-build / replay failure.
pub fn build_and_pin_gate(
    registry: &FlipGateRegistry,
    corpus: &Path,
    serial: i64,
    gates_dir: &Path,
    description: &str,
    round: &str,
) -> Result<FlipGate, FlipGateError> {
    if registry.gate(serial).is_some() {
        return Err(FlipGateError::AlreadyRegistered(serial));
    }
    std::fs::create_dir_all(gates_dir).map_err(io_err(gates_dir))?;

    // Build the closure-complete slice (registration lines included, so PASS-1
    // registries match the grand corpus — mode-seam fidelity).
    let build_path = gates_dir.join(format!("s{serial}.jsonl"));
    let select = SliceSelect {
        serials: [serial].into_iter().collect(),
        include_registrations: true,
        ..SliceSelect::default()
    };
    extract_slice(corpus, &build_path, &select)?;

    // Replay through the real driver and check the serial flipped.
    let verdicts = replay_slice(&build_path)?;
    let Some(name) = kv_name(&verdicts, serial) else {
        // Not a flip: clean up the slice and refuse to register.
        let _ = std::fs::remove_file(&build_path);
        return Err(FlipGateError::NotAFlip {
            serial,
            reasons: render_reasons(&verdicts),
        });
    };

    // Rename to a human-friendly, name-bearing durable path, then pin the final
    // bytes (a rename preserves bytes, so the pin covers exactly what is stored).
    // The RAW driver name drives the filename (empty ⇒ `sN.jsonl`).
    let final_path = gates_dir.join(slice_file_name(serial, &name));
    if final_path != build_path {
        std::fs::rename(&build_path, &final_path).map_err(io_err(&final_path))?;
    }
    let pin = compute_pin(&final_path)?;

    // A KernelVerified anonymous proof-term node mints no catalog name; store a
    // self-describing `<anon.sN>` in the registry so the report reads cleanly
    // (the check keys on the serial, so this display name is never load-bearing).
    let display_name = if name.trim().is_empty() {
        format!("<anon.s{serial}>")
    } else {
        name
    };

    Ok(FlipGate {
        serial,
        name: display_name,
        description: description.to_string(),
        slice: to_portable(&final_path),
        expected: EXPECTED_KERNEL_VERIFIED.to_string(),
        blake3: pin.blake3,
        lines: pin.lines,
        added: today_ymd(),
        round: round.to_string(),
    })
}

/// Replay a slice through the real stream-verify shard driver (`k=1/N=1`
/// records the whole run) on a big-stack thread, returning its per-line
/// verdicts. Verdict-neutral wrt. tier-2 / ledger / bridge: the caller keeps
/// those lanes disabled so `kv` is exactly the tier-1 `KernelVerified` set.
fn replay_slice(slice: &Path) -> Result<ShardVerdicts, FlipGateError> {
    let slice = slice.to_path_buf();
    let handle = std::thread::Builder::new()
        .stack_size(REPLAY_STACK)
        .spawn(move || -> Result<ShardVerdicts, String> {
            let mut writer = ShardWriter::new();
            let spec = ShardSpec::new(1, 1).map_err(|e| e.to_string())?;
            import_proven_theorems_streaming_shard(&slice, &mut writer, spec)
                .map_err(|e| e.to_string())
        })
        .map_err(FlipGateError::ReplayThread)?;
    handle
        .join()
        .map_err(|_| FlipGateError::ReplayPanicked)?
        .map_err(FlipGateError::Replay)
}

/// The set of serials the replay stamped `KernelVerified`.
fn kv_serials(verdicts: &ShardVerdicts) -> BTreeSet<i64> {
    verdicts.kv.iter().map(|kv| kv.serial).collect()
}

/// The shard-catalog name the replay stamped for `serial`, if it KernelVerified.
fn kv_name(verdicts: &ShardVerdicts, serial: i64) -> Option<String> {
    verdicts
        .kv
        .iter()
        .find(|kv| kv.serial == serial)
        .map(|kv| kv.name.clone())
}

/// Render a slice's coarse reject buckets as a stable `reason x count, …` list.
fn render_reasons(verdicts: &ShardVerdicts) -> String {
    if verdicts.rejection_reasons.is_empty() {
        return "none".to_string();
    }
    let mut pairs: Vec<(&String, &usize)> = verdicts.rejection_reasons.iter().collect();
    pairs.sort_by(|a, b| b.1.cmp(a.1).then_with(|| a.0.cmp(b.0)));
    pairs
        .iter()
        .map(|(r, c)| format!("{r} x{c}"))
        .collect::<Vec<_>>()
        .join(", ")
}

/// Deterministic durable slice file name: `s<serial>[_<sanitized-name>].jsonl`.
fn slice_file_name(serial: i64, name: &str) -> String {
    let san = sanitize_name(name);
    if san.is_empty() {
        format!("s{serial}.jsonl")
    } else {
        format!("s{serial}_{san}.jsonl")
    }
}

/// Sanitize a theorem name for use in a filename: keep `[A-Za-z0-9._-]`, map the
/// rest to `_`, and truncate to a bounded length.
fn sanitize_name(name: &str) -> String {
    name.chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || matches!(c, '.' | '_' | '-') {
                c
            } else {
                '_'
            }
        })
        .take(60)
        .collect()
}

/// Convert an absolute path under `$HOME` back to its `~`-portable form so the
/// committed registry is not machine-specific; other paths are returned verbatim.
fn to_portable(path: &Path) -> String {
    if let (Some(home), Some(s)) = (std::env::var_os("HOME"), path.to_str()) {
        let home = home.to_string_lossy();
        if let Some(rest) = s.strip_prefix(home.as_ref()) {
            let rest = rest.strip_prefix('/').unwrap_or(rest);
            return format!("~/{rest}");
        }
    }
    path.to_string_lossy().into_owned()
}

/// Today's UTC date as `YYYY-MM-DD`.
fn today_ymd() -> String {
    let secs = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0);
    ymd_from_epoch(secs)
}

/// Format Unix epoch seconds (UTC) as `YYYY-MM-DD` — dependency-free
/// civil-from-days (Hinnant's algorithm), so the registry writer pulls in no
/// date crate.
fn ymd_from_epoch(epoch_secs: u64) -> String {
    let days = (epoch_secs / 86_400) as i64;
    let z = days + 719_468;
    let era = if z >= 0 { z } else { z - 146_096 } / 146_097;
    let doe = z - era * 146_097;
    let yoe = (doe - doe / 1_460 + doe / 36_524 - doe / 146_096) / 365;
    let year = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let day = doy - (153 * mp + 2) / 5 + 1;
    let month = if mp < 10 { mp + 3 } else { mp - 9 };
    let year = if month <= 2 { year + 1 } else { year };
    format!("{year:04}-{month:02}-{day:02}")
}

#[cfg(test)]
mod tests;
