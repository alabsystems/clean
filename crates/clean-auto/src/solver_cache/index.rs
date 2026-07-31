// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `VCIDX01`: a fail-closed, content-addressed index over the solver cache +
//! telemetry (Phase 1).
//!
//! See `designs/2026-06-24-solver-results-cache-service.md` §7.1. This mirrors
//! `clean-mathverse`'s `MVBIDX01` baseline index (`graduate/baseline_index.rs`):
//! a binary file with a magic+version header, a `corpus_digest` pin over the
//! source bytes, a `self_digest` trailer, and a **fail-closed** loader that
//! validates section arithmetic + sortedness + the self-digest *before* serving
//! a single lookup. Lookups are µs binary searches over the in-memory table.
//!
//! Where `MVBIDX01` maps `statement-hash → first baseline name`, `VCIDX01` maps
//! `obligation_digest → summary` of what the solver corpus knows about that
//! obligation: whether a re-checkable proof term is cached, and the aggregate
//! solve outcome (attempts / solved / best wall-time).
//!
//! # Soundness
//!
//! The index is a **lookup accelerator**, never an arbiter. A `cached = true`
//! entry means a proof term is on disk under that key; the caller still
//! re-checks that term through the kernel exactly as for a freshly-found proof
//! (see [`super::store`] module docs). A tampered or stale index is rejected at
//! load (self-digest + structure checks); even were one served, a wrong
//! `cached` bit only costs a redundant lookup-then-miss, never a trusted
//! verdict.
//!
//! # `VCIDX01` format (all integers little-endian)
//!
//! ```text
//! [ 0.. 8)  magic            b"VCIDX01\0"
//! [ 8..12)  version          u32 = 1
//! [12..16)  reserved         u32 = 0
//! [16..24)  entry_count      u64 (sorted unique obligation digests)
//! [24..56)  corpus_digest    blake3 over the source inputs (sorted-path order)
//! [56..  )  entry_records    entry_count × ENTRY_LEN bytes, sorted by key:
//!             key            [u8;32]  full 256-bit obligation digest
//!             flags          u8       bit0 = cached (proof term on disk)
//!             _pad           [u8;3]   reserved, zero
//!             attempts       u32      total attempts seen for this obligation
//!             solved         u32      attempts with result == Proved
//!             best_wall_ms   u64      min wall_ms over Proved attempts (u64::MAX if none)
//! [len-32)  self_digest      blake3 over all preceding bytes
//! ```
//!
//! **Full 256-bit keys, not 128-bit prefixes.** Per design §2.5 the safe
//! truncation direction *inverts* for a result cache versus the novelty gate: a
//! prefix collision in `MVBIDX01` can only mark a new statement as duplicate
//! (conservative), but in a result cache a prefix collision could serve a
//! *wrong* cached verdict. So `VCIDX01` keys on the full 256-bit digest.

use std::collections::BTreeMap;
use std::io::Write;
use std::path::Path;

use thiserror::Error;

/// File magic for a `VCIDX01` index (8 bytes, NUL-padded).
pub(crate) const MAGIC: &[u8; 8] = b"VCIDX01\0";
/// Current (and only) format version.
pub(crate) const VERSION: u32 = 1;
/// Header length up to the start of the entry table.
pub(crate) const HEADER_LEN: usize = 56;
/// Trailing self-digest length.
pub(crate) const TRAILER_LEN: usize = 32;
/// One entry record: 32B key + 1B flags + 3B pad + 4B attempts + 4B solved + 8B best_wall.
pub(crate) const ENTRY_LEN: usize = 32 + 1 + 3 + 4 + 4 + 8;
/// `flags` bit set when a re-checkable proof term is cached for the obligation.
const FLAG_CACHED: u8 = 0b0000_0001;
/// Sentinel `best_wall_ms` meaning "no solved attempt" (no finite best time).
const NO_BEST_WALL: u64 = u64::MAX;

/// Errors building or loading a `VCIDX01` index. Every load-side variant is a
/// fail-closed rejection: a malformed/tampered index never serves a lookup.
#[derive(Debug, Error)]
pub enum IndexError {
    /// An I/O error reading or writing the index file.
    #[error("solver index I/O: {0}")]
    Io(String),
    /// The on-disk index is structurally invalid or its digest does not match.
    #[error("solver index corrupt ({path}): {reason}")]
    Corrupt {
        /// Path of the offending index file.
        path: String,
        /// Human-readable reason the load failed closed.
        reason: String,
    },
    /// The index exceeds a `u32`/`u64` capacity bound while building.
    #[error("solver index capacity: {0}")]
    Capacity(String),
}

fn corrupt(path: &Path, reason: impl Into<String>) -> IndexError {
    IndexError::Corrupt {
        path: path.display().to_string(),
        reason: reason.into(),
    }
}

/// Parse a `blake3:<64hex>` digest string into its raw 32-byte key.
///
/// Returns `None` for any string that is not a clean `blake3:`-tagged 64-hex
/// digest — a malformed key is excluded from the index rather than risking a
/// truncated/colliding entry.
pub(crate) fn digest_key(digest: &str) -> Option<[u8; 32]> {
    let hex = digest.strip_prefix("blake3:")?;
    if hex.len() != 64 {
        return None;
    }
    let mut out = [0u8; 32];
    for (i, byte) in out.iter_mut().enumerate() {
        *byte = u8::from_str_radix(hex.get(2 * i..2 * i + 2)?, 16).ok()?;
    }
    Some(out)
}

/// Render a 32-byte key back to its `blake3:<64hex>` string form.
pub(crate) fn key_digest(key: &[u8; 32]) -> String {
    let mut s = String::with_capacity(7 + 64);
    s.push_str("blake3:");
    for b in key {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

/// The per-obligation summary stored in one index entry.
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize)]
pub struct ObligationSummary {
    /// `true` iff a re-checkable proof term is cached for this obligation.
    pub cached: bool,
    /// Total solving attempts recorded for this obligation (across engines).
    pub attempts: u32,
    /// Attempts whose result was `Proved`.
    pub solved: u32,
    /// Minimum wall time (ms) over `Proved` attempts; `None` if never solved.
    pub best_wall_ms: Option<u64>,
}

/// Accumulator used while building the index: merges attempt rows + cache
/// membership into one summary per obligation digest.
#[derive(Clone, Copy, Debug)]
pub(crate) struct SummaryAccumulator {
    cached: bool,
    attempts: u32,
    solved: u32,
    best_wall_ms: u64,
}

impl Default for SummaryAccumulator {
    /// A fresh accumulator has `best_wall_ms = NO_BEST_WALL` (the "no solved
    /// attempt" sentinel) — NOT `0`, so the first solved attempt's wall time
    /// wins the `min`. A derived `Default` (which would zero `best_wall_ms`)
    /// would be a latent bug, so the impl is explicit.
    fn default() -> Self {
        Self {
            cached: false,
            attempts: 0,
            solved: 0,
            best_wall_ms: NO_BEST_WALL,
        }
    }
}

impl SummaryAccumulator {
    /// Fold in one attempt observation (saturating on the `u32` counters).
    pub(crate) fn add_attempt(&mut self, solved: bool, wall_ms: u64) {
        self.attempts = self.attempts.saturating_add(1);
        if solved {
            self.solved = self.solved.saturating_add(1);
            self.best_wall_ms = self.best_wall_ms.min(wall_ms);
        }
    }

    /// Mark that a proof term is cached on disk for this obligation.
    pub(crate) fn mark_cached(&mut self) {
        self.cached = true;
    }

    /// Project the accumulator into the public [`ObligationSummary`].
    ///
    /// Used by the Phase-2 service's `/lookup` live-aggregate path (when no
    /// pre-built `VCIDX01` is loaded) so a single digest can be summarised
    /// directly from the telemetry stream with the *same* shape the on-disk
    /// index serves.
    pub(crate) fn finish(self) -> ObligationSummary {
        ObligationSummary {
            cached: self.cached,
            attempts: self.attempts,
            solved: self.solved,
            best_wall_ms: (self.best_wall_ms != NO_BEST_WALL).then_some(self.best_wall_ms),
        }
    }
}

/// Build a `VCIDX01` index from a pre-aggregated map of obligation digests to
/// accumulators, pinned to `corpus_digest`, writing to `out`.
///
/// The map is the caller's responsibility (it folds telemetry rows + cache
/// membership); this function is the pure serializer + fail-closed-compatible
/// writer. Keys that do not parse as `blake3:<64hex>` are skipped.
///
/// # Errors
///
/// I/O failures writing `out`, or a corpus that exceeds the `u64` entry-count
/// bound.
pub(crate) fn build_index(
    accumulators: &BTreeMap<String, SummaryAccumulator>,
    corpus_digest: &[u8; 32],
    out: &Path,
) -> Result<u64, IndexError> {
    // Parse + sort keys; a BTreeMap over the raw 32-byte key guarantees the
    // strict sortedness the loader re-validates.
    let mut entries: BTreeMap<[u8; 32], SummaryAccumulator> = BTreeMap::new();
    for (digest, acc) in accumulators {
        if let Some(key) = digest_key(digest) {
            entries.insert(key, *acc);
        }
    }
    let entry_count = u64::try_from(entries.len())
        .map_err(|_| IndexError::Capacity("entry count exceeds u64".to_string()))?;

    let mut body: Vec<u8> = Vec::with_capacity(HEADER_LEN + ENTRY_LEN * entries.len());
    body.extend_from_slice(MAGIC);
    body.extend_from_slice(&VERSION.to_le_bytes());
    body.extend_from_slice(&0u32.to_le_bytes()); // reserved
    body.extend_from_slice(&entry_count.to_le_bytes());
    body.extend_from_slice(corpus_digest);
    debug_assert_eq!(body.len(), HEADER_LEN);

    for (key, acc) in &entries {
        body.extend_from_slice(key);
        let flags = if acc.cached { FLAG_CACHED } else { 0 };
        body.push(flags);
        body.extend_from_slice(&[0u8; 3]); // pad
        body.extend_from_slice(&acc.attempts.to_le_bytes());
        body.extend_from_slice(&acc.solved.to_le_bytes());
        body.extend_from_slice(&acc.best_wall_ms.to_le_bytes());
    }

    let self_digest = blake3::hash(&body);
    let mut file = std::io::BufWriter::new(
        std::fs::File::create(out).map_err(|e| IndexError::Io(e.to_string()))?,
    );
    file.write_all(&body)
        .map_err(|e| IndexError::Io(e.to_string()))?;
    file.write_all(self_digest.as_bytes())
        .map_err(|e| IndexError::Io(e.to_string()))?;
    file.flush().map_err(|e| IndexError::Io(e.to_string()))?;
    Ok(entry_count)
}

/// A loaded, fully-validated `VCIDX01` index. Lookups are µs binary searches
/// over the in-memory entry table; no per-lookup allocation.
#[derive(Debug)]
pub struct SolverIndex {
    data: Vec<u8>,
    entry_count: usize,
    entries_pos: usize,
    corpus_digest: [u8; 32],
}

impl SolverIndex {
    /// Load and validate a `VCIDX01` index. Fail-closed: bad magic, an
    /// unsupported version, a self-digest mismatch, section-arithmetic
    /// overflow, a length mismatch, or a non-strictly-sorted key table is an
    /// error — never a partially-trusted index.
    pub(crate) fn load(path: &Path) -> Result<Self, IndexError> {
        let data = std::fs::read(path).map_err(|e| IndexError::Io(e.to_string()))?;
        if data.len() < HEADER_LEN + TRAILER_LEN {
            return Err(corrupt(path, "file shorter than header + trailer"));
        }
        if &data[0..8] != MAGIC {
            return Err(corrupt(path, "bad magic (not a VCIDX01 index)"));
        }
        let version = u32::from_le_bytes([data[8], data[9], data[10], data[11]]);
        if version != VERSION {
            return Err(corrupt(
                path,
                format!("unsupported index version {version}"),
            ));
        }
        let body_len = data.len() - TRAILER_LEN;
        let actual = blake3::hash(&data[..body_len]);
        if actual.as_bytes() != &data[body_len..] {
            return Err(corrupt(path, "self-digest mismatch (corrupted index)"));
        }
        let entry_count = {
            let mut buf = [0u8; 8];
            buf.copy_from_slice(&data[16..24]);
            usize::try_from(u64::from_le_bytes(buf))
                .map_err(|_| corrupt(path, "entry_count overflows usize"))?
        };
        let mut corpus_digest = [0u8; 32];
        corpus_digest.copy_from_slice(&data[24..56]);

        // Section arithmetic over the header-supplied (attacker-controllable)
        // count must fail closed, never overflow-panic.
        let entries_bytes = ENTRY_LEN
            .checked_mul(entry_count)
            .ok_or_else(|| corrupt(path, "entry table size overflow"))?;
        let expected_len = HEADER_LEN
            .checked_add(entries_bytes)
            .ok_or_else(|| corrupt(path, "section arithmetic overflow"))?;
        if expected_len != body_len {
            return Err(corrupt(
                path,
                format!("section sizes claim {expected_len} bytes, body has {body_len}"),
            ));
        }

        let index = Self {
            data,
            entry_count,
            entries_pos: HEADER_LEN,
            corpus_digest,
        };
        index.validate_sorted(path)?;
        Ok(index)
    }

    /// Verify the entry-key table is strictly sorted (binary-search precondition)
    /// and that the reserved pad bytes are zero.
    fn validate_sorted(&self, path: &Path) -> Result<(), IndexError> {
        let mut prev: Option<&[u8]> = None;
        for i in 0..self.entry_count {
            let at = self.entries_pos + ENTRY_LEN * i;
            let key = &self.data[at..at + 32];
            if prev.is_some_and(|p| p >= key) {
                return Err(corrupt(path, format!("keys not strictly sorted at {i}")));
            }
            prev = Some(key);
        }
        Ok(())
    }

    /// Number of obligations indexed.
    pub fn entry_count(&self) -> usize {
        self.entry_count
    }

    /// The 32-byte corpus digest pin (blake3 over the source inputs).
    pub fn corpus_digest(&self) -> &[u8; 32] {
        &self.corpus_digest
    }

    /// The corpus digest pin as a `blake3:<64hex>` string.
    #[must_use]
    pub fn corpus_digest_str(&self) -> String {
        key_digest(&self.corpus_digest)
    }

    /// Decode the summary stored at entry slot `i`.
    fn summary_at(&self, i: usize) -> ObligationSummary {
        let at = self.entries_pos + ENTRY_LEN * i;
        let rec = &self.data[at..at + ENTRY_LEN];
        let flags = rec[32];
        let attempts = u32::from_le_bytes([rec[36], rec[37], rec[38], rec[39]]);
        let solved = u32::from_le_bytes([rec[40], rec[41], rec[42], rec[43]]);
        let mut wall = [0u8; 8];
        wall.copy_from_slice(&rec[44..52]);
        let best = u64::from_le_bytes(wall);
        ObligationSummary {
            cached: flags & FLAG_CACHED != 0,
            attempts,
            solved,
            best_wall_ms: (best != NO_BEST_WALL).then_some(best),
        }
    }

    /// Look up the obligation summary for `digest` (`blake3:<64hex>`).
    ///
    /// Binary search over the full 256-bit key, ~µs. Returns `None` for a digest
    /// not in the index or one that does not parse.
    pub fn lookup(&self, digest: &str) -> Option<ObligationSummary> {
        let key = digest_key(digest)?;
        let mut lo = 0usize;
        let mut hi = self.entry_count;
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            let at = self.entries_pos + ENTRY_LEN * mid;
            let rec_key = &self.data[at..at + 32];
            match rec_key.cmp(&key[..]) {
                std::cmp::Ordering::Equal => return Some(self.summary_at(mid)),
                std::cmp::Ordering::Less => lo = mid + 1,
                std::cmp::Ordering::Greater => hi = mid,
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn key_digest_str(seed: u8) -> String {
        format!("blake3:{}", format!("{seed:02x}").repeat(32))
    }

    fn build_sample(out: &Path) -> [u8; 32] {
        let mut accs: BTreeMap<String, SummaryAccumulator> = BTreeMap::new();
        let mut a = SummaryAccumulator::default();
        a.add_attempt(true, 42);
        a.add_attempt(false, 0);
        a.mark_cached();
        accs.insert(key_digest_str(0xab), a);

        let mut b = SummaryAccumulator::default();
        b.add_attempt(false, 0);
        accs.insert(key_digest_str(0x01), b);

        let corpus = *blake3::hash(b"corpus-bytes").as_bytes();
        build_index(&accs, &corpus, out).expect("build index");
        corpus
    }

    #[test]
    fn test_digest_key_roundtrips() {
        let d = key_digest_str(0x7f);
        let k = digest_key(&d).expect("parse");
        assert_eq!(key_digest(&k), d);
    }

    #[test]
    fn test_digest_key_rejects_malformed() {
        assert!(digest_key("not-a-digest").is_none());
        assert!(digest_key("blake3:short").is_none());
        assert!(digest_key("blake3:zz".repeat(32).as_str()).is_none());
    }

    #[test]
    fn test_build_then_load_and_lookup() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let path = tmp.path().join("solver.vcidx");
        let corpus = build_sample(&path);

        let index = SolverIndex::load(&path).expect("load fail-closed");
        assert_eq!(index.entry_count(), 2);
        assert_eq!(index.corpus_digest(), &corpus);

        let s = index.lookup(&key_digest_str(0xab)).expect("hit");
        assert!(s.cached, "ab entry has a cached proof term");
        assert_eq!(s.attempts, 2);
        assert_eq!(s.solved, 1);
        assert_eq!(s.best_wall_ms, Some(42));

        let s2 = index.lookup(&key_digest_str(0x01)).expect("hit");
        assert!(!s2.cached);
        assert_eq!(s2.attempts, 1);
        assert_eq!(s2.solved, 0);
        assert_eq!(s2.best_wall_ms, None);

        assert!(
            index.lookup(&key_digest_str(0xcc)).is_none(),
            "absent key is a clean miss"
        );
    }

    #[test]
    fn test_load_rejects_tampered_self_digest() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let path = tmp.path().join("solver.vcidx");
        build_sample(&path);

        // Flip one byte in the entry table; the self-digest must no longer match.
        let mut bytes = std::fs::read(&path).expect("read");
        let flip = HEADER_LEN + 5;
        bytes[flip] ^= 0xff;
        std::fs::write(&path, &bytes).expect("write tampered");

        let err = SolverIndex::load(&path).expect_err("tampered index must fail closed");
        assert!(
            matches!(err, IndexError::Corrupt { .. }),
            "expected Corrupt, got {err:?}"
        );
    }

    #[test]
    fn test_load_rejects_bad_magic() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let path = tmp.path().join("solver.vcidx");
        build_sample(&path);
        let mut bytes = std::fs::read(&path).expect("read");
        bytes[0] = b'X';
        // Recompute a valid self-digest so ONLY the magic is wrong.
        let body_len = bytes.len() - TRAILER_LEN;
        let d = blake3::hash(&bytes[..body_len]);
        bytes[body_len..].copy_from_slice(d.as_bytes());
        std::fs::write(&path, &bytes).expect("write");
        let err = SolverIndex::load(&path).expect_err("bad magic must fail closed");
        assert!(matches!(err, IndexError::Corrupt { .. }));
    }

    #[test]
    fn test_load_rejects_truncated_file() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let path = tmp.path().join("solver.vcidx");
        build_sample(&path);
        let bytes = std::fs::read(&path).expect("read");
        std::fs::write(&path, &bytes[..HEADER_LEN + 4]).expect("truncate");
        let err = SolverIndex::load(&path).expect_err("truncated index must fail closed");
        assert!(matches!(err, IndexError::Corrupt { .. }));
    }

    #[test]
    fn test_full_256bit_key_no_prefix_collision() {
        // Two digests sharing a 128-bit prefix but differing in the tail must be
        // distinct entries (the result-cache safe direction; design §2.5).
        let tmp = tempfile::tempdir().expect("tempdir");
        let path = tmp.path().join("solver.vcidx");
        let shared = "ab".repeat(16); // 32 hex chars = 128 bits
        let d1 = format!("blake3:{shared}{}", "00".repeat(16));
        let d2 = format!("blake3:{shared}{}", "ff".repeat(16));
        let mut accs: BTreeMap<String, SummaryAccumulator> = BTreeMap::new();
        let mut a = SummaryAccumulator::default();
        a.add_attempt(true, 5);
        accs.insert(d1.clone(), a);
        let mut b = SummaryAccumulator::default();
        b.add_attempt(false, 0);
        accs.insert(d2.clone(), b);
        let corpus = *blake3::hash(b"x").as_bytes();
        build_index(&accs, &corpus, &path).expect("build");
        let index = SolverIndex::load(&path).expect("load");
        assert_eq!(
            index.entry_count(),
            2,
            "prefix-colliding keys stay distinct"
        );
        assert_eq!(index.lookup(&d1).expect("d1").solved, 1);
        assert_eq!(index.lookup(&d2).expect("d2").solved, 0);
    }
}
