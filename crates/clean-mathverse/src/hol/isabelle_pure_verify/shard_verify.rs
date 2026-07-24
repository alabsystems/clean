// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Sharded stream verify** — split one corpus replay across `N` processes with
//! a deterministic merge that is byte-identical to a single serial run.
//!
//! # Why sharding filters *emission*, not *verification*
//!
//! The closure-replay verdict for a line is a pure function of (the theorem, the
//! closure entries of its dependency serials, the frozen PASS-1 registries) — and
//! the closure holds **only successfully-`KernelVerified` serials**
//! (`batch.rs`, the `closure.insert` after the foundational-axiom gate). A later
//! line that references a serial the kernel never accepted is rejected
//! (`UnresolvedThm`). So the closure state at line *i* encodes the accept/reject
//! decision of every prior line — it cannot be reconstructed by a cheap "register
//! statements only" pre-pass without re-deciding those verdicts, which is the
//! verification itself.
//!
//! Therefore a shard that *skipped* verifying prior lines would see a different
//! closure at its range boundary and could flip a verdict — breaking the
//! byte-identical invariant (and, worse, risking an unsound accept). Instead each
//! shard runs the **full deterministic replay** (identical closure/env/verdict
//! trajectory to a serial run — see [`super::parallel_streaming`] for the same
//! soundness argument) and merely **records the verdict only for the line indices
//! in its assigned contiguous range** ([`ShardSpec::range`]). The union of the
//! shards' ranges is exactly `[0, total_lines)`, so [`merge_shard_verdicts`]
//! concatenating them in shard order reproduces the serial run's verdict stream
//! exactly.
//!
//! The corpus is dependency-ordered (serial-ascending == topological), so line
//! index *is* the natural, stable partition key: shard `k` of `N` owns line
//! indices `[(k-1)·T/N, k·T/N)`, a contiguous, total, non-overlapping partition
//! that needs no cross-shard coordination.
//!
//! # Trade-off, honestly
//!
//! Each shard still pays the full replay's CPU (translation is re-done per shard).
//! The win is **safe wall-clock parallelism** — bounded per-shard output memory
//! and the freedom to fan the emission across machines — plus the P0 that matters:
//! concurrent verifying that is *trustworthy and deterministic* rather than
//! load-depressed. A future "cheap registration pre-pass + verify-only-range"
//! optimization would have to reconstruct the exact `KernelVerified` closure first
//! (a snapshot hand-off), which is left as a follow-up.

use std::collections::BTreeMap;
use std::path::Path;

use serde::{Deserialize, Serialize};

use super::snapshot::RejectRecord;
use super::{PureVerifiedImport, StreamError};
use crate::shard::ShardWriter;

/// Errors from shard-spec parsing and merge validation.
#[derive(Debug, thiserror::Error)]
pub enum ShardError {
    /// A `--shard k/N` spec that is malformed or out of range.
    #[error("invalid shard spec {spec:?}: {why}")]
    BadSpec {
        /// The offending spec string.
        spec: String,
        /// Why it was rejected.
        why: String,
    },
    /// The per-shard outputs handed to [`merge_shard_verdicts`] do not form a
    /// complete, non-overlapping cover of `[0, total_lines)`.
    #[error("cannot merge shard outputs: {0}")]
    BadCover(String),
}

/// A `k`-of-`N` shard assignment (`k` is **1-based**, `1 <= k <= n`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ShardSpec {
    /// 1-based shard index.
    pub k: usize,
    /// Total shard count.
    pub n: usize,
}

impl ShardSpec {
    /// Construct a validated `k`-of-`n` spec.
    ///
    /// # Errors
    /// [`ShardError::BadSpec`] unless `n >= 1` and `1 <= k <= n`.
    pub fn new(k: usize, n: usize) -> Result<Self, ShardError> {
        if n == 0 || k == 0 || k > n {
            return Err(ShardError::BadSpec {
                spec: format!("{k}/{n}"),
                why: "need n >= 1 and 1 <= k <= n".to_string(),
            });
        }
        Ok(Self { k, n })
    }

    /// Parse a `"k/N"` spec (the `--shard k/N` CLI form).
    ///
    /// # Errors
    /// [`ShardError::BadSpec`] on a non-`k/N` string or an out-of-range spec.
    pub fn parse(s: &str) -> Result<Self, ShardError> {
        let bad = |why: &str| ShardError::BadSpec {
            spec: s.to_string(),
            why: why.to_string(),
        };
        let (k, n) = s.split_once('/').ok_or_else(|| bad("expected form k/N"))?;
        let k: usize = k.trim().parse().map_err(|_| bad("k is not an integer"))?;
        let n: usize = n.trim().parse().map_err(|_| bad("N is not an integer"))?;
        Self::new(k, n)
    }

    /// This shard's half-open line-index range `[lo, hi)` over `total` lines.
    /// Balanced integer partition: `lo = (k-1)·total/n`, `hi = k·total/n`.
    #[must_use]
    pub fn range(&self, total: usize) -> (usize, usize) {
        // u128 math so `k * total` never overflows for any realistic corpus.
        let t = total as u128;
        let n = self.n as u128;
        let lo = ((self.k as u128 - 1) * t / n) as usize;
        let hi = (self.k as u128 * t / n) as usize;
        (lo, hi)
    }
}

/// One `KernelVerified` line captured by a shard: its raw line index, serial, and
/// stored name — enough to reproduce the serial run's `names` multiset in order.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct KvVerdict {
    /// Zero-based raw corpus line index (empty lines counted), == `RejectRecord::line`.
    pub line: u64,
    /// The theorem's Isabelle proof-term serial.
    pub serial: i64,
    /// The stored (shard-catalog) name — `PureVerifiedImport::names` entry.
    pub name: String,
}

/// The mergeable output of one shard: the verdicts for exactly the line indices
/// in `[lo, hi)`. Serde-serialized to a per-shard artifact that
/// [`merge_shard_verdicts`] recombines.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ShardVerdicts {
    /// 1-based shard index.
    pub k: usize,
    /// Total shard count.
    pub n: usize,
    /// Inclusive low line index of this shard's range.
    pub lo: usize,
    /// Exclusive high line index of this shard's range.
    pub hi: usize,
    /// Total raw line count of the corpus (identical across a group's shards).
    pub total_lines: usize,
    /// `KernelVerified` lines in this range (line-ascending).
    pub kv: Vec<KvVerdict>,
    /// Rejected lines in this range (line-ascending).
    pub reject_records: Vec<RejectRecord>,
    /// Tier-2 (`KernelCheckedConditional`) count in this range (ledger runs).
    pub kernel_checked_ledger: usize,
    /// Trusted-ledger axiom count in this range (ledger runs).
    pub ledger_size: usize,
    /// Coarse rejection-reason buckets summed over this range.
    pub rejection_reasons: BTreeMap<String, usize>,
    /// Fine rejection-specific buckets summed over this range.
    pub rejection_specifics: BTreeMap<String, usize>,
}

impl ShardVerdicts {
    /// `KernelVerified` count in this shard's range.
    #[must_use]
    pub fn kernel_verified(&self) -> usize {
        self.kv.len()
    }

    /// Rejected count in this shard's range.
    #[must_use]
    pub fn rejected(&self) -> usize {
        self.reject_records.len()
    }

    /// Serialize to a pretty JSON artifact (small; human-inspectable).
    ///
    /// # Errors
    /// [`StreamError::Io`] on write failure or a serde encode error.
    pub fn save(&self, path: impl AsRef<Path>) -> Result<(), StreamError> {
        let bytes = serde_json::to_vec_pretty(self)
            .map_err(|e| StreamError::Io(std::io::Error::other(e)))?;
        std::fs::write(path, bytes)?;
        Ok(())
    }

    /// Load a per-shard artifact written by [`ShardVerdicts::save`].
    ///
    /// # Errors
    /// [`StreamError::Io`] on read failure or a serde decode error.
    pub fn load(path: impl AsRef<Path>) -> Result<Self, StreamError> {
        let bytes = std::fs::read(path)?;
        serde_json::from_slice(&bytes).map_err(|e| StreamError::Io(std::io::Error::other(e)))
    }
}

/// The deterministic merge of a group's per-shard outputs — the fields of a
/// serial [`PureVerifiedImport`] that a sharded run must reproduce exactly, plus
/// the per-line lists (`kv_serials`, `reject_records`) the aggregate omits.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct MergedVerdicts {
    /// Total raw line count.
    pub total_lines: usize,
    /// `KernelVerified` count (`== names.len()`).
    pub kernel_verified: usize,
    /// Rejected count.
    pub rejected: usize,
    /// Tier-2 count (ledger runs).
    pub kernel_checked_ledger: usize,
    /// Trusted-ledger axiom count (ledger runs).
    pub ledger_size: usize,
    /// KV names in line order — the serial run's `PureVerifiedImport::names`.
    pub names: Vec<String>,
    /// KV serials in line order.
    pub kv_serials: Vec<i64>,
    /// Reject records in line order.
    pub reject_records: Vec<RejectRecord>,
    /// Coarse rejection-reason buckets — the serial run's `rejection_reasons`.
    pub rejection_reasons: BTreeMap<String, usize>,
    /// Fine rejection-specific buckets — the serial run's `rejection_specifics`.
    pub rejection_specifics: BTreeMap<String, usize>,
}

impl MergedVerdicts {
    /// Whether this merge agrees with a serial full-run [`PureVerifiedImport`] on
    /// every field the aggregate exposes (`kernel_verified`, `rejected`, tier
    /// counts, `names`, and both rejection maps). The per-line `kv_serials` /
    /// `reject_records` are validated shard-vs-shard by the determinism test — the
    /// aggregate does not carry them.
    #[must_use]
    pub fn agrees_with_full(&self, full: &PureVerifiedImport) -> bool {
        self.kernel_verified == full.kernel_verified
            && self.rejected == full.rejected
            && self.kernel_checked_ledger == full.kernel_checked_ledger
            && self.ledger_size == full.ledger_size
            && self.names == full.names
            && self.rejection_reasons == full.rejection_reasons
            && self.rejection_specifics == full.rejection_specifics
    }
}

/// Combine a group's per-shard outputs into a single [`MergedVerdicts`] that is
/// byte-identical to a serial run's verdict stream.
///
/// The shards must form a complete, non-overlapping cover of `[0, total_lines)`
/// (exactly the ranges [`ShardSpec::range`] produces for `k = 1..=n`), all sharing
/// one `total_lines`. Order among the input slice does not matter — the merge
/// sorts by `lo`.
///
/// # Errors
/// [`ShardError::BadCover`] if the shards are empty, disagree on `total_lines`, or
/// leave a gap / overlap in the cover.
pub fn merge_shard_verdicts(shards: &[ShardVerdicts]) -> Result<MergedVerdicts, ShardError> {
    if shards.is_empty() {
        return Err(ShardError::BadCover("no shard outputs given".to_string()));
    }
    let total_lines = shards[0].total_lines;
    let mut ordered: Vec<&ShardVerdicts> = shards.iter().collect();
    ordered.sort_by_key(|s| s.lo);

    // Validate a gapless, non-overlapping cover of [0, total_lines).
    let mut frontier = 0usize;
    for s in &ordered {
        if s.total_lines != total_lines {
            return Err(ShardError::BadCover(format!(
                "shard {}/{} has total_lines {} != {total_lines}",
                s.k, s.n, s.total_lines
            )));
        }
        if s.lo != frontier {
            return Err(ShardError::BadCover(format!(
                "gap/overlap before shard {}/{}: expected lo {frontier}, got {}",
                s.k, s.n, s.lo
            )));
        }
        if s.hi < s.lo || s.hi > total_lines {
            return Err(ShardError::BadCover(format!(
                "shard {}/{} range [{}, {}) out of bounds (total {total_lines})",
                s.k, s.n, s.lo, s.hi
            )));
        }
        frontier = s.hi;
    }
    if frontier != total_lines {
        return Err(ShardError::BadCover(format!(
            "cover ends at {frontier}, expected total_lines {total_lines}"
        )));
    }

    let mut merged = MergedVerdicts {
        total_lines,
        ..Default::default()
    };
    for s in ordered {
        for kv in &s.kv {
            merged.names.push(kv.name.clone());
            merged.kv_serials.push(kv.serial);
        }
        merged.reject_records.extend_from_slice(&s.reject_records);
        merged.kernel_verified += s.kernel_verified();
        merged.rejected += s.rejected();
        merged.kernel_checked_ledger += s.kernel_checked_ledger;
        merged.ledger_size += s.ledger_size;
        add_maps(&mut merged.rejection_reasons, &s.rejection_reasons);
        add_maps(&mut merged.rejection_specifics, &s.rejection_specifics);
    }
    Ok(merged)
}

/// Add every `src` count into `dst` (summing on shared keys).
fn add_maps(dst: &mut BTreeMap<String, usize>, src: &BTreeMap<String, usize>) {
    for (k, v) in src {
        *dst.entry(k.clone()).or_insert(0) += *v;
    }
}

/// Positive per-key increases from `before` to `after` (the buckets THIS line
/// added). Exactly one bucket grows per rejected line, but the diff is general.
fn map_delta(
    before: &BTreeMap<String, usize>,
    after: &BTreeMap<String, usize>,
) -> BTreeMap<String, usize> {
    let mut d = BTreeMap::new();
    for (k, av) in after {
        let bv = before.get(k).copied().unwrap_or(0);
        if *av > bv {
            d.insert(k.clone(), av - bv);
        }
    }
    d
}

/// What one processed corpus line did to the running counters/maps, handed to
/// [`ShardRecorder::record_line`] by the streaming driver.
pub(super) struct LineOutcome<'a> {
    /// Raw line index.
    pub cur: usize,
    /// Parsed serial (`None` for a line that failed to parse).
    pub serial: Option<i64>,
    /// `kernel_verified` delta for this line (0 or 1).
    pub kv_delta: usize,
    /// The KV name (`out.names.last()`) — meaningful only when `kv_delta == 1`.
    pub kv_name: Option<&'a str>,
    /// The reject record, present iff this line was rejected.
    pub reject_record: Option<RejectRecord>,
    /// `kernel_checked_ledger` delta (tier-2; ledger runs).
    pub tier2_delta: usize,
    /// `ledger_size` delta (trusted-ledger axiom; ledger runs).
    pub ledger_delta: usize,
    /// `rejection_reasons` snapshot BEFORE this line.
    pub reasons_before: &'a BTreeMap<String, usize>,
    /// `rejection_reasons` AFTER this line.
    pub reasons_after: &'a BTreeMap<String, usize>,
    /// `rejection_specifics` BEFORE this line.
    pub specifics_before: &'a BTreeMap<String, usize>,
    /// `rejection_specifics` AFTER this line.
    pub specifics_after: &'a BTreeMap<String, usize>,
    /// Shard-writer constant count BEFORE this line's verify (inclusive low bound
    /// of the constants this line emitted into the writer).
    pub writer_const_lo: usize,
    /// Shard-writer constant count AFTER this line's verify (exclusive high bound).
    pub writer_const_hi: usize,
}

/// Records the per-line verdicts for the line indices in one shard's range as the
/// streaming driver replays the whole corpus. Verdict-neutral: it only observes.
pub(super) struct ShardRecorder {
    lo: usize,
    hi: usize,
    verdicts: ShardVerdicts,
    /// The shard-writer constant indices emitted by this range's lines, in line
    /// order — the exact subset a per-range `.mathverse` artifact must carry.
    /// Not serialized into [`ShardVerdicts`] (a writer-internal index, not a
    /// verdict); consumed by [`super::shard_mathverse`] after the replay.
    emitted_const_indices: Vec<u32>,
}

impl ShardRecorder {
    /// A recorder for `spec` over a corpus of `total` raw lines.
    pub(super) fn new(spec: ShardSpec, total: usize) -> Self {
        let (lo, hi) = spec.range(total);
        Self {
            lo,
            hi,
            verdicts: ShardVerdicts {
                k: spec.k,
                n: spec.n,
                lo,
                hi,
                total_lines: total,
                ..Default::default()
            },
            emitted_const_indices: Vec::new(),
        }
    }

    /// The shard-writer constant indices this range's lines emitted (line order).
    pub(super) fn emitted_const_indices(&self) -> &[u32] {
        &self.emitted_const_indices
    }

    /// Whether raw line index `cur` falls in this shard's emission range.
    pub(super) fn in_range(&self, cur: usize) -> bool {
        self.lo <= cur && cur < self.hi
    }

    /// Record one in-range line's outcome. Caller guarantees `in_range(cur)`.
    pub(super) fn record_line(&mut self, o: &LineOutcome<'_>) {
        if o.kv_delta >= 1 {
            self.verdicts.kv.push(KvVerdict {
                line: o.cur as u64,
                serial: o.serial.unwrap_or_default(),
                name: o.kv_name.unwrap_or_default().to_string(),
            });
        }
        if let Some(rec) = o.reject_record {
            self.verdicts.reject_records.push(rec);
            add_maps(
                &mut self.verdicts.rejection_reasons,
                &map_delta(o.reasons_before, o.reasons_after),
            );
            add_maps(
                &mut self.verdicts.rejection_specifics,
                &map_delta(o.specifics_before, o.specifics_after),
            );
        }
        self.verdicts.kernel_checked_ledger += o.tier2_delta;
        self.verdicts.ledger_size += o.ledger_delta;
        // Record the writer constant slots this line emitted (0 for a reject, 1
        // for a plain KV, more under the ledger tier) so a per-range `.mathverse`
        // subset can be carved from the full-replay writer afterwards.
        self.emitted_const_indices
            .extend((o.writer_const_lo..o.writer_const_hi).map(|i| i as u32));
    }

    /// Finalize the accumulated shard output.
    pub(super) fn into_verdicts(self) -> ShardVerdicts {
        self.verdicts
    }
}

/// Count raw corpus lines exactly as the streaming driver's `read_until(b'\n')`
/// loop indexes them (empty lines counted; a trailing partial line counted).
fn count_raw_lines(path: &Path) -> Result<usize, StreamError> {
    use std::io::BufRead as _;
    let mut reader = std::io::BufReader::new(std::fs::File::open(path)?);
    let mut buf = Vec::new();
    let mut lines = 0usize;
    loop {
        buf.clear();
        let n = reader.read_until(b'\n', &mut buf)?;
        if n == 0 {
            break;
        }
        lines += 1;
    }
    Ok(lines)
}

/// Stream-verify a corpus but record verdicts for **only** this shard's line
/// range, returning its mergeable [`ShardVerdicts`]. Runs the full deterministic
/// replay (identical trajectory to a serial run); a shard `k` of `1` records the
/// whole run.
///
/// Not compatible with snapshot resume (`ISA_SNAPSHOT_IN`): sharding is a fresh
/// full replay so the line indices are absolute from 0.
///
/// # Errors
/// [`StreamError::Io`] on file errors, exactly like the serial driver.
pub fn import_proven_theorems_streaming_shard(
    serial_sorted_path: impl AsRef<Path>,
    writer: &mut ShardWriter,
    spec: ShardSpec,
) -> Result<ShardVerdicts, StreamError> {
    Ok(stream_shard_recorded(serial_sorted_path.as_ref(), writer, spec, None)?.into_verdicts())
}

/// Run one shard's full deterministic replay and return the populated
/// [`ShardRecorder`] — the shared body behind the shard entry points. The caller
/// gets both the mergeable [`ShardVerdicts`] (via [`ShardRecorder::into_verdicts`])
/// and, for a per-range `.mathverse` emission, the writer constant indices this
/// range emitted (via [`ShardRecorder::emitted_const_indices`]). `writer` holds
/// the WHOLE replay's constants on return (the recorder carves the range's subset).
///
/// # Errors
/// [`StreamError`] on file / snapshot errors, exactly like the serial driver.
pub(super) fn stream_shard_recorded(
    path: &Path,
    writer: &mut ShardWriter,
    spec: ShardSpec,
    prepass: Option<&Path>,
) -> Result<ShardRecorder, StreamError> {
    let total = count_raw_lines(path)?;
    let mut recorder = ShardRecorder::new(spec, total);
    // Full deterministic replay; the returned whole-corpus aggregate is discarded
    // in favour of the shard-scoped recorder output.
    let _full = super::streaming::stream_with_recorder(path, writer, Some(&mut recorder), prepass)?;
    Ok(recorder)
}

/// Export the **shard pre-pass hand-off** state: build the shared post-pre-pass
/// verify state ONCE (built-in def-consts + the five PASS-1 registries scanned
/// from `serial_sorted_corpus`) and save it as a prefix-0 replay snapshot the
/// group's shard children load to SKIP that O(T) registry scan.
///
/// # What this soundly saves — and what stays O(T)
///
/// The pre-pass (`build_verify_state`) is the ONE part of a shard's work that is
/// (a) identical across every shard and (b) independent of any verdict: it is a
/// pure function of the corpus text. So the leader can compute it once and hand
/// it to `N` children, saving `(N-1)×` the pre-pass scan (the dominant *setup*
/// I/O on the multi-GB grand corpus).
///
/// The **PASS-2 closure replay stays O(T) per shard and cannot be shortened**:
/// the closure at line *i* holds only successfully-`KernelVerified` serials, so
/// it encodes the accept/reject decision of every prior line — reconstructing it
/// at a shard's range boundary IS re-deciding those verdicts, i.e. the
/// verification itself (see the module docs and the design note §3.1). A cheap
/// "register-only pre-pass + verify-only-range" would therefore risk a different
/// closure at the boundary and an unsound accept, so each shard still replays the
/// full corpus and merely records its own range. This hand-off is the *sound
/// subset* of the O(T/N) follow-up: it removes the shared registry-scan prefix,
/// not the per-line replay.
///
/// # Determinism
///
/// The exported env + registries are exactly [`build_verify_state`]'s output,
/// round-tripped through the v6 snapshot (its ENV-LAYOUT fingerprint refuses a
/// cross-binary layout drift up front). A child loading them replays the
/// identical PASS-2 trajectory, so its [`ShardVerdicts`] are byte-identical to a
/// no-hand-off shard run — asserted by `tests/isabelle_shard_determinism.rs`.
///
/// # Errors
/// [`StreamError::Io`] on corpus read failure, [`StreamError::Snapshot`] on a
/// snapshot encode/write failure.
pub fn export_prepass_snapshot(
    serial_sorted_corpus: impl AsRef<Path>,
    out_path: impl AsRef<Path>,
) -> Result<(), StreamError> {
    let corpus = serial_sorted_corpus.as_ref();
    let super::streaming::VerifyState {
        env,
        closure,
        class_registry,
        method_registry,
        instance_op_registry,
        list_fn_registry,
        poly_inst_registry,
        elide: _,
    } = super::streaming::build_verify_state(corpus)?;
    let snap = super::snapshot::ReplaySnapshot {
        fingerprint: super::snapshot::current_fingerprint(),
        prefix_lines: 0,
        prefix_bytes: 0,
        prefix_blake3: super::snapshot::hash_corpus_prefix(corpus, 0)?,
        out: PureVerifiedImport::default(),
        env,
        // Empty by construction (no theorem verified yet); the replay fills it.
        closure,
        class_registry,
        method_registry,
        instance_op_registry,
        list_fn_registry,
        poly_inst_registry,
        rejection_reasons: BTreeMap::new(),
        rejects: Vec::new(),
    };
    // `None`: the pre-pass export runs in the env-driven library path with no
    // threaded build identity; the sidecar records `"unknown"` SHA and pairs via
    // the durable `current_exe` path.
    super::snapshot::save_snapshot(out_path.as_ref(), &snap, None)?;
    Ok(())
}

/// [`import_proven_theorems_streaming_shard`] with the **pre-pass hand-off**: load
/// the shared post-pre-pass state from `prepass_snapshot` (a leader-exported
/// [`export_prepass_snapshot`]) instead of rescanning the corpus for the five
/// PASS-1 registries, then run the same full deterministic PASS-2 replay
/// recording only this shard's range. Byte-identical output to
/// [`import_proven_theorems_streaming_shard`] (the loaded state equals a fresh
/// pre-pass); see that function and [`export_prepass_snapshot`] for the soundness
/// and O(T) discussion.
///
/// # Errors
/// [`StreamError::Io`] on file errors; [`StreamError::Snapshot`] if the pre-pass
/// snapshot cannot be loaded (e.g. an ENV-LAYOUT drift from a different binary).
pub fn import_proven_theorems_streaming_shard_prepass(
    serial_sorted_path: impl AsRef<Path>,
    writer: &mut ShardWriter,
    spec: ShardSpec,
    prepass_snapshot: impl AsRef<Path>,
) -> Result<ShardVerdicts, StreamError> {
    Ok(stream_shard_recorded(
        serial_sorted_path.as_ref(),
        writer,
        spec,
        Some(prepass_snapshot.as_ref()),
    )?
    .into_verdicts())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_shard_spec_parse_and_validate() {
        assert_eq!(ShardSpec::parse("1/4").unwrap(), ShardSpec { k: 1, n: 4 });
        assert_eq!(
            ShardSpec::parse(" 3 / 8 ").unwrap(),
            ShardSpec { k: 3, n: 8 }
        );
        assert!(ShardSpec::parse("0/4").is_err(), "k must be 1-based");
        assert!(ShardSpec::parse("5/4").is_err(), "k must be <= n");
        assert!(ShardSpec::parse("1/0").is_err(), "n must be >= 1");
        assert!(ShardSpec::parse("abc").is_err());
        assert!(ShardSpec::parse("1/x").is_err());
    }

    #[test]
    fn test_shard_ranges_tile_completely() {
        // For any total and N, the k=1..=N ranges must exactly tile [0, total).
        for total in [0usize, 1, 7, 137, 270_773] {
            for n in [1usize, 2, 3, 4, 8, 16] {
                let mut frontier = 0;
                let mut covered = 0;
                for k in 1..=n {
                    let (lo, hi) = ShardSpec::new(k, n).unwrap().range(total);
                    assert_eq!(lo, frontier, "gap/overlap at k={k} n={n} total={total}");
                    assert!(hi >= lo);
                    covered += hi - lo;
                    frontier = hi;
                }
                assert_eq!(frontier, total, "cover end n={n} total={total}");
                assert_eq!(covered, total, "cover size n={n} total={total}");
            }
        }
    }

    fn kv(line: u64, serial: i64, name: &str) -> KvVerdict {
        KvVerdict {
            line,
            serial,
            name: name.to_string(),
        }
    }

    #[test]
    fn test_merge_is_order_independent_and_gapless() {
        let total = 4;
        let s0 = ShardVerdicts {
            k: 1,
            n: 2,
            lo: 0,
            hi: 2,
            total_lines: total,
            kv: vec![kv(0, 10, "a")],
            reject_records: vec![RejectRecord {
                line: 1,
                offset: 5,
                len: 5,
            }],
            rejection_reasons: BTreeMap::from([("hole".to_string(), 1)]),
            ..Default::default()
        };
        let s1 = ShardVerdicts {
            k: 2,
            n: 2,
            lo: 2,
            hi: 4,
            total_lines: total,
            kv: vec![kv(3, 30, "c")],
            reject_records: vec![RejectRecord {
                line: 2,
                offset: 10,
                len: 5,
            }],
            rejection_reasons: BTreeMap::from([("hole".to_string(), 1)]),
            ..Default::default()
        };
        // Deliberately pass out of order — merge must sort by lo.
        let merged = merge_shard_verdicts(&[s1.clone(), s0.clone()]).expect("merge");
        assert_eq!(merged.kernel_verified, 2);
        assert_eq!(merged.rejected, 2);
        assert_eq!(merged.names, vec!["a".to_string(), "c".to_string()]);
        assert_eq!(merged.kv_serials, vec![10, 30]);
        assert_eq!(
            merged
                .reject_records
                .iter()
                .map(|r| r.line)
                .collect::<Vec<_>>(),
            vec![1, 2]
        );
        assert_eq!(merged.rejection_reasons.get("hole"), Some(&2));
    }

    #[test]
    fn test_merge_rejects_gap() {
        let total = 4;
        let s0 = ShardVerdicts {
            k: 1,
            n: 2,
            lo: 0,
            hi: 2,
            total_lines: total,
            ..Default::default()
        };
        // Missing [2,4): frontier ends at 2 != 4.
        assert!(matches!(
            merge_shard_verdicts(&[s0]),
            Err(ShardError::BadCover(_))
        ));
    }
}
