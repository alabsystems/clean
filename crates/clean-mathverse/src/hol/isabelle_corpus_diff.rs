// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Corpus-version diff** (`isabelle-corpus-diff`) — the substrate of the
//! *incremental grand* (`designs/2026-07-18-isabelle-incremental-grand.md`).
//!
//! A fresh grand re-verifies every one of a 50–60 GB corpus's ~10^5–10^6 lines
//! through the kernel (25–100 h at AFP scale). But version `N+1` of a corpus is
//! almost always version `N` **plus appended increments** (the AFP wave pattern:
//! `assemble` unions the new capture dirs in serial order, so new declarations
//! land as new high-serial lines after the byte-identical old prefix). Given
//! that, `N`'s completed grand snapshot is a valid, byte-invariant accepted
//! prefix for `N+1`, and only the *added* lines (plus the former non-KV lines the
//! retry driver already re-attempts) need kernel work.
//!
//! This module classifies two corpus versions **straight off their `.idx`
//! sidecars** ([`super::isabelle_index`]) — no full-corpus read. Each line falls
//! into exactly one [`LineClass`]:
//!
//! * **UNCHANGED** — same serial (or, for anonymous `serial == 0` lines, same
//!   byte offset) and byte-identical content. Detected by comparing the sidecars'
//!   per-line BLAKE3 [`content_hash`](super::isabelle_index::IndexEntry::content_hash):
//!   equal hashes ⇒ identical content (BLAKE3 collision resistance is the same
//!   trust the snapshot's whole-prefix `prefix_blake3` already rests on).
//! * **NEW** — serial present only in the new corpus.
//! * **CHANGED** — serial present in both, content differs. A hash mismatch is
//!   **confirmed by a seek-read byte-compare of the two lines** (the only corpus
//!   reads beyond the on-demand hash fallback), so a CHANGED verdict is never a
//!   hashing artefact.
//! * **REMOVED** — serial present only in the old corpus.
//!
//! The output [`CorpusDiff`] is a typed JSON report (summary counts + the NEW /
//! CHANGED / REMOVED line addresses in both old- and new-corpus coordinates). It
//! deliberately omits the UNCHANGED list — that is the whole ~50 GB base and is
//! implied — so the report is bounded by the *increment + anomalies*, not the
//! corpus. The retry driver consumes it (`--corpus-diff`) to seed its re-attempt
//! set and to enforce the trusted-prefix refusal (see [`super::isabelle_pure_verify::retry`]).
//!
//! # Bounded memory
//!
//! Peak RAM is O(index size), not O(corpus size): the two compact sidecars are
//! loaded (offsets/lens/hashes/names — orders of magnitude smaller than the
//! corpus), joined on serial, and the only corpus touches are per-line seek-reads
//! to confirm a CHANGED line or to recompute a hash absent from a legacy (v1)
//! sidecar. No corpus file is ever read whole.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use super::isabelle_index::{self, CorpusIndex, IndexEntry, IsabelleIndexError};

/// Errors from a corpus-version diff.
#[derive(Debug, thiserror::Error)]
pub enum DiffError {
    /// Filesystem failure reading a corpus, a sidecar, or the report.
    #[error("corpus-diff I/O on {path}: {source}")]
    Io {
        /// Path involved.
        path: PathBuf,
        /// Underlying error.
        source: std::io::Error,
    },
    /// A corpus has no `.idx` sidecar. The diff runs off the sidecars only, so it
    /// refuses to fall back to a full-corpus scan; build the index first.
    #[error(
        "corpus-diff requires the `.idx` sidecar for {corpus} (expected at {idx}); \
         build it with `clean mathverse isabelle-index --corpus {corpus}`"
    )]
    IndexMissing {
        /// The corpus whose sidecar is absent.
        corpus: PathBuf,
        /// The expected sidecar path.
        idx: PathBuf,
    },
    /// A sidecar's stored corpus length no longer matches the corpus on disk —
    /// its offsets/hashes would be wrong, so the diff refuses it (soundness: the
    /// trusted-prefix boundary depends on accurate offsets).
    #[error(
        "corpus-diff: the `.idx` for {corpus} is STALE (indexed {indexed} bytes, corpus is now \
         {actual} bytes) — rebuild it with `clean mathverse isabelle-index`"
    )]
    IndexStale {
        /// The corpus whose sidecar is stale.
        corpus: PathBuf,
        /// Byte length the sidecar was built against.
        indexed: u64,
        /// Actual byte length of the corpus on disk.
        actual: u64,
    },
    /// The sidecar failed to load (bad envelope, digest mismatch, decode error).
    #[error("corpus-diff: loading `.idx` failed: {0}")]
    Index(#[from] IsabelleIndexError),
    /// JSON encode/decode of the diff report failed.
    #[error("corpus-diff report codec: {0}")]
    Codec(String),
}

fn io_err(path: &Path) -> impl FnOnce(std::io::Error) -> DiffError + '_ {
    move |source| DiffError::Io {
        path: path.to_path_buf(),
        source,
    }
}

/// The classification of one corpus line across two versions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LineClass {
    /// Same identity, byte-identical content.
    Unchanged,
    /// Serial present only in the new corpus.
    New,
    /// Serial present in both, content differs.
    Changed,
    /// Serial present only in the old corpus.
    Removed,
}

/// A line's address within ONE corpus — the serial, its 0-based line number, and
/// its byte offset/len (delimiter included, exactly the bytes a `read_until`
/// consumes). Mirrors `snapshot::RejectRecord` plus the serial, so the retry
/// driver reconstructs a `RejectRecord` from it directly.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct LineAddr {
    /// The line's leading proof-term serial (`0` for an anonymous line).
    pub serial: i64,
    /// 0-based corpus line number (delimited-line index; [`u64::MAX`] if the
    /// sidecar predates the line field).
    pub line: u64,
    /// Byte offset of the line's first byte.
    pub offset: u64,
    /// Byte length including the trailing delimiter(s).
    pub len: u64,
}

/// A CHANGED line: its address in BOTH corpora. `old` locates it for the
/// trusted-prefix refusal boundary (`old.offset < snapshot.prefix_bytes` ⇒ the
/// change is inside a trusted region ⇒ refuse incremental); `new` is the
/// re-attempt seed the retry reads from the new corpus.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct ChangedLine {
    /// The shared serial.
    pub serial: i64,
    /// Address in the OLD corpus.
    pub old: LineAddr,
    /// Address in the NEW corpus.
    pub new: LineAddr,
}

/// Summary counts. Invariants:
/// `old_total == unchanged + changed + removed`,
/// `new_total == unchanged + changed + new`.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct DiffSummary {
    /// Lines byte-identical across the two versions.
    pub unchanged: u64,
    /// Lines added in the new version.
    pub new: u64,
    /// Lines whose content changed.
    pub changed: u64,
    /// Lines dropped from the old version.
    pub removed: u64,
    /// Distinct indexed lines in the old corpus.
    pub old_total: u64,
    /// Distinct indexed lines in the new corpus.
    pub new_total: u64,
    /// TRUE iff the growth is **append-only**: no CHANGED and no REMOVED lines
    /// (every old line survives byte-identical; the delta is purely NEW). This is
    /// the incremental-grand fast path — a *necessary* condition; the retry
    /// driver still checks the changes fall outside the snapshot's trusted prefix
    /// (a partial-prefix snapshot can tolerate changes in its un-snapshotted
    /// tail).
    pub append_only: bool,
}

/// The typed corpus-version diff report.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct CorpusDiff {
    /// The old corpus path (as given).
    pub old_corpus: String,
    /// The new corpus path (as given).
    pub new_corpus: String,
    /// On-disk `.idx` format version of the old sidecar (1 = pre-content-hash).
    pub old_idx_version: u32,
    /// On-disk `.idx` format version of the new sidecar.
    pub new_idx_version: u32,
    /// Summary counts.
    pub summary: DiffSummary,
    /// Serials present only in NEW — new-corpus addresses, offset-ascending. The
    /// retry driver's incremental re-attempt seed.
    pub new_lines: Vec<LineAddr>,
    /// Serials in both with differing content — old + new addresses,
    /// new-offset-ascending.
    pub changed_lines: Vec<ChangedLine>,
    /// Serials present only in OLD — old-corpus addresses, offset-ascending.
    pub removed_lines: Vec<LineAddr>,
}

/// Load a corpus's `.idx` sidecar, refusing a missing or stale one (a stale
/// sidecar's offsets/hashes are wrong, which would silently corrupt the diff).
fn load_side(corpus: &Path) -> Result<(CorpusIndex, u32), DiffError> {
    let idx = isabelle_index::index_path(corpus);
    if !idx.exists() {
        return Err(DiffError::IndexMissing {
            corpus: corpus.to_path_buf(),
            idx,
        });
    }
    let (index, version) = isabelle_index::load_index_versioned(&idx)?;
    let actual = std::fs::metadata(corpus).map_err(io_err(corpus))?.len();
    if index.corpus_len != actual {
        return Err(DiffError::IndexStale {
            corpus: corpus.to_path_buf(),
            indexed: index.corpus_len,
            actual,
        });
    }
    Ok((index, version))
}

/// The per-corpus join keys: named lines keyed by their (unique) serial, and
/// anonymous (`serial == 0`) lines keyed by byte offset (their only stable
/// identity). Duplicate non-zero serials — pathological; corpus serials are the
/// unique kernel identity — collapse to the first (lowest-offset) occurrence.
struct Keyed<'a> {
    by_serial: BTreeMap<i64, &'a IndexEntry>,
    anon_by_offset: BTreeMap<u64, &'a IndexEntry>,
}

impl<'a> Keyed<'a> {
    fn build(index: &'a CorpusIndex) -> Self {
        let mut by_serial: BTreeMap<i64, &IndexEntry> = BTreeMap::new();
        let mut anon_by_offset: BTreeMap<u64, &IndexEntry> = BTreeMap::new();
        // `entries` is (serial, offset)-sorted, so `or_insert` keeps the
        // lowest-offset occurrence of any duplicate serial.
        for e in &index.entries {
            if e.serial == 0 {
                anon_by_offset.entry(e.offset).or_insert(e);
            } else {
                by_serial.entry(e.serial).or_insert(e);
            }
        }
        Keyed {
            by_serial,
            anon_by_offset,
        }
    }

    fn distinct(&self) -> u64 {
        (self.by_serial.len() + self.anon_by_offset.len()) as u64
    }
}

fn addr(e: &IndexEntry) -> LineAddr {
    LineAddr {
        serial: e.serial,
        line: e.line,
        offset: e.offset,
        len: e.len,
    }
}

/// Whether two entries have byte-identical trimmed content. Fast path: compare
/// the sidecars' stored BLAKE3 hashes (no I/O). A hash mismatch is **confirmed**
/// by seek-reading and byte-comparing the two lines, so a spurious hash
/// difference (e.g. one side is a legacy sidecar) can never mint a false CHANGED,
/// and hash equality — BLAKE3 collision resistance — is trusted as identity.
fn content_eq(
    old_idx: &CorpusIndex,
    oe: &IndexEntry,
    old_corpus: &Path,
    new_idx: &CorpusIndex,
    ne: &IndexEntry,
    new_corpus: &Path,
) -> Result<bool, DiffError> {
    let oh = old_idx.content_hash(old_corpus, oe)?;
    let nh = new_idx.content_hash(new_corpus, ne)?;
    if oh == nh {
        return Ok(true);
    }
    let ol = old_idx.read_line(old_corpus, oe)?;
    let nl = new_idx.read_line(new_corpus, ne)?;
    Ok(ol == nl)
}

/// Classify every line of `old_corpus` vs `new_corpus` from their `.idx`
/// sidecars, producing a typed [`CorpusDiff`].
///
/// Both corpora MUST have an up-to-date sidecar (build with
/// `clean mathverse isabelle-index`); a missing or stale one is a hard error
/// rather than a silent full-corpus scan.
///
/// # Errors
/// [`DiffError`] on a missing/stale/corrupt sidecar or an I/O failure.
pub fn diff_corpora(old_corpus: &Path, new_corpus: &Path) -> Result<CorpusDiff, DiffError> {
    let (old_index, old_ver) = load_side(old_corpus)?;
    let (new_index, new_ver) = load_side(new_corpus)?;
    let old = Keyed::build(&old_index);
    let new = Keyed::build(&new_index);

    let mut summary = DiffSummary {
        old_total: old.distinct(),
        new_total: new.distinct(),
        ..DiffSummary::default()
    };
    let mut new_lines: Vec<LineAddr> = Vec::new();
    let mut changed_lines: Vec<ChangedLine> = Vec::new();
    let mut removed_lines: Vec<LineAddr> = Vec::new();

    // Named lines: join on serial.
    for (serial, oe) in &old.by_serial {
        match new.by_serial.get(serial) {
            None => {
                summary.removed += 1;
                removed_lines.push(addr(oe));
            }
            Some(ne) => {
                if content_eq(&old_index, oe, old_corpus, &new_index, ne, new_corpus)? {
                    summary.unchanged += 1;
                } else {
                    summary.changed += 1;
                    changed_lines.push(ChangedLine {
                        serial: *serial,
                        old: addr(oe),
                        new: addr(ne),
                    });
                }
            }
        }
    }
    for (serial, ne) in &new.by_serial {
        if !old.by_serial.contains_key(serial) {
            summary.new += 1;
            new_lines.push(addr(ne));
        }
    }

    // Anonymous (serial == 0) lines: join on byte offset (position identity).
    for (offset, oe) in &old.anon_by_offset {
        match new.anon_by_offset.get(offset) {
            None => {
                summary.removed += 1;
                removed_lines.push(addr(oe));
            }
            Some(ne) => {
                if content_eq(&old_index, oe, old_corpus, &new_index, ne, new_corpus)? {
                    summary.unchanged += 1;
                } else {
                    summary.changed += 1;
                    changed_lines.push(ChangedLine {
                        serial: 0,
                        old: addr(oe),
                        new: addr(ne),
                    });
                }
            }
        }
    }
    for (offset, ne) in &new.anon_by_offset {
        if !old.anon_by_offset.contains_key(offset) {
            summary.new += 1;
            new_lines.push(addr(ne));
        }
    }

    summary.append_only = summary.changed == 0 && summary.removed == 0;

    // Deterministic, file-order output (offset is unique within a corpus).
    new_lines.sort_by_key(|a| a.offset);
    removed_lines.sort_by_key(|a| a.offset);
    changed_lines.sort_by_key(|c| c.new.offset);

    debug_assert_eq!(
        summary.old_total,
        summary.unchanged + summary.changed + summary.removed,
        "every old line is unchanged, changed, or removed"
    );
    debug_assert_eq!(
        summary.new_total,
        summary.unchanged + summary.changed + summary.new,
        "every new line is unchanged, changed, or new"
    );

    Ok(CorpusDiff {
        old_corpus: old_corpus.display().to_string(),
        new_corpus: new_corpus.display().to_string(),
        old_idx_version: old_ver,
        new_idx_version: new_ver,
        summary,
        new_lines,
        changed_lines,
        removed_lines,
    })
}

/// Write `diff` to `path` as pretty JSON (atomic `.tmp` + rename).
///
/// # Errors
/// [`DiffError`] on encode or I/O failure.
pub fn write_diff(path: &Path, diff: &CorpusDiff) -> Result<(), DiffError> {
    let json = serde_json::to_vec_pretty(diff).map_err(|e| DiffError::Codec(e.to_string()))?;
    let tmp = path.with_extension("json.tmp");
    std::fs::write(&tmp, &json).map_err(io_err(&tmp))?;
    std::fs::rename(&tmp, path).map_err(io_err(path))?;
    Ok(())
}

/// Load a [`CorpusDiff`] report from `path`.
///
/// # Errors
/// [`DiffError`] on I/O or decode failure.
pub fn load_diff(path: &Path) -> Result<CorpusDiff, DiffError> {
    let bytes = std::fs::read(path).map_err(io_err(path))?;
    serde_json::from_slice(&bytes).map_err(|e| DiffError::Codec(e.to_string()))
}

/// A diff line that falls **inside** a snapshot's trusted accepted prefix and
/// therefore forbids incremental retry — trusting the snapshot's prefix state
/// would silently trust a now-stale region of the old corpus.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PrefixViolation {
    /// The offending line's serial (`0` for an anonymous line).
    pub serial: i64,
    /// Its OLD-corpus byte offset (CHANGED/REMOVED) or NEW-corpus byte offset
    /// (an INSERTED new line landing inside the prefix span) — whichever proves
    /// the prefix is no longer byte-identical.
    pub offset: u64,
    /// `"changed"`, `"removed"`, or `"inserted"`.
    pub kind: &'static str,
}

/// The lines of `diff` that violate a trusted-prefix of `prefix_bytes` bytes.
///
/// A snapshot's accepted prefix (`[0, prefix_bytes)` of the OLD corpus) is only a
/// sound basis for incremental retry if it is **byte-identical** in the new
/// corpus. That fails exactly when, inside that span, a line CHANGED, was REMOVED
/// (old offset `< prefix_bytes`), or a NEW line was INSERTED (its new offset
/// `< prefix_bytes` — a mid-prefix insertion shifts the tail). An empty result ⇒
/// every delta is outside the trusted prefix ⇒ append-only over the prefix ⇒
/// incremental retry is sound. Pure and offset-only, so it is exact even under
/// `ISA_SNAPSHOT_SKIP_PREFIX_HASH=1`, where the byte-hash backstop is off.
#[must_use]
pub fn incremental_prefix_violations(diff: &CorpusDiff, prefix_bytes: u64) -> Vec<PrefixViolation> {
    let mut v = Vec::new();
    for c in &diff.changed_lines {
        if c.old.offset < prefix_bytes {
            v.push(PrefixViolation {
                serial: c.serial,
                offset: c.old.offset,
                kind: "changed",
            });
        }
    }
    for r in &diff.removed_lines {
        if r.offset < prefix_bytes {
            v.push(PrefixViolation {
                serial: r.serial,
                offset: r.offset,
                kind: "removed",
            });
        }
    }
    for n in &diff.new_lines {
        if n.offset < prefix_bytes {
            v.push(PrefixViolation {
                serial: n.serial,
                offset: n.offset,
                kind: "inserted",
            });
        }
    }
    v.sort_by_key(|p| p.offset);
    v
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write as _;

    /// Build a corpus file from raw JSONL lines and its v2 sidecar.
    fn write_corpus(dir: &Path, name: &str, lines: &[&str]) -> PathBuf {
        let corpus = dir.join(name);
        let mut f = std::fs::File::create(&corpus).expect("create corpus");
        for l in lines {
            writeln!(f, "{l}").expect("write line");
        }
        f.flush().expect("flush");
        let index = isabelle_index::build_index(&corpus).expect("build index");
        isabelle_index::save_index(&isabelle_index::index_path(&corpus), &index).expect("save idx");
        corpus
    }

    /// A minimal serial-tagged corpus line (content-only; the diff never parses
    /// it, it only hashes/compares the bytes).
    fn line(serial: i64, body: &str) -> String {
        format!("{{\"serial\":{serial},\"name\":\"T.s{serial}\",\"body\":\"{body}\"}}")
    }

    #[test]
    fn test_diff_classifies_all_four_classes() {
        let dir = std::env::temp_dir().join(format!("isa_diff_4class_{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("mk dir");

        // old: serials 10, 20, 30. new: 10 (same), 20 (changed body), 40 (new);
        // 30 is removed.
        let l10 = line(10, "a");
        let l20 = line(20, "b");
        let l30 = line(30, "c");
        let l20b = line(20, "CHANGED");
        let l40 = line(40, "d");
        let old = write_corpus(&dir, "old.jsonl", &[&l10, &l20, &l30]);
        let new = write_corpus(&dir, "new.jsonl", &[&l10, &l20b, &l40]);

        let diff = diff_corpora(&old, &new).expect("diff");
        assert_eq!(diff.summary.unchanged, 1, "serial 10 unchanged");
        assert_eq!(diff.summary.changed, 1, "serial 20 changed");
        assert_eq!(diff.summary.new, 1, "serial 40 new");
        assert_eq!(diff.summary.removed, 1, "serial 30 removed");
        assert_eq!(diff.summary.old_total, 3);
        assert_eq!(diff.summary.new_total, 3);
        assert!(
            !diff.summary.append_only,
            "changed+removed ⇒ not append-only"
        );

        assert_eq!(diff.new_lines.len(), 1);
        assert_eq!(diff.new_lines[0].serial, 40);
        assert_eq!(diff.changed_lines.len(), 1);
        assert_eq!(diff.changed_lines[0].serial, 20);
        // The changed line's old + new offsets locate it in each corpus.
        assert_eq!(diff.changed_lines[0].old.offset, l10.len() as u64 + 1);
        assert_eq!(diff.removed_lines.len(), 1);
        assert_eq!(diff.removed_lines[0].serial, 30);

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_diff_append_only_growth() {
        let dir = std::env::temp_dir().join(format!("isa_diff_append_{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("mk dir");
        let l10 = line(10, "a");
        let l20 = line(20, "b");
        let l30 = line(30, "c");
        let l40 = line(40, "d");
        // new = old ++ [30, 40], byte-identical prefix.
        let old = write_corpus(&dir, "old.jsonl", &[&l10, &l20]);
        let new = write_corpus(&dir, "new.jsonl", &[&l10, &l20, &l30, &l40]);

        let diff = diff_corpora(&old, &new).expect("diff");
        assert!(diff.summary.append_only, "pure additions ⇒ append-only");
        assert_eq!(diff.summary.unchanged, 2);
        assert_eq!(diff.summary.new, 2);
        assert_eq!(diff.summary.changed, 0);
        assert_eq!(diff.summary.removed, 0);
        // New lines sit AFTER the byte-identical prefix, in serial order.
        let prefix_bytes = std::fs::metadata(&old).expect("meta").len();
        assert!(
            diff.new_lines.iter().all(|a| a.offset >= prefix_bytes),
            "append-only ⇒ every new line offset >= old corpus length"
        );
        assert_eq!(
            diff.new_lines.iter().map(|a| a.serial).collect::<Vec<_>>(),
            vec![30, 40]
        );

        // Round-trip the report through JSON.
        let out = dir.join("diff.json");
        write_diff(&out, &diff).expect("write");
        let back = load_diff(&out).expect("load");
        assert_eq!(back.summary, diff.summary);
        assert_eq!(back.new_lines, diff.new_lines);

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_diff_refuses_missing_and_stale_sidecar() {
        let dir = std::env::temp_dir().join(format!("isa_diff_stale_{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("mk dir");
        let l10 = line(10, "a");
        let old = write_corpus(&dir, "old.jsonl", &[&l10]);

        // No sidecar for `new` yet.
        let new = dir.join("new.jsonl");
        {
            let mut f = std::fs::File::create(&new).expect("create new");
            writeln!(f, "{l10}").expect("write");
        }
        match diff_corpora(&old, &new) {
            Err(DiffError::IndexMissing { .. }) => {}
            other => panic!("missing sidecar must be refused, got {other:?}"),
        }

        // Build then invalidate the sidecar (append to the corpus without
        // re-indexing) ⇒ stale ⇒ refused.
        let index = isabelle_index::build_index(&new).expect("build");
        isabelle_index::save_index(&isabelle_index::index_path(&new), &index).expect("save");
        {
            let mut f = std::fs::OpenOptions::new()
                .append(true)
                .open(&new)
                .expect("append open");
            writeln!(f, "{}", line(99, "z")).expect("append");
        }
        match diff_corpora(&old, &new) {
            Err(DiffError::IndexStale { .. }) => {}
            other => panic!("stale sidecar must be refused, got {other:?}"),
        }

        let _ = std::fs::remove_dir_all(&dir);
    }

    fn addr_at(serial: i64, offset: u64) -> LineAddr {
        LineAddr {
            serial,
            line: 0,
            offset,
            len: 10,
        }
    }

    #[test]
    fn test_incremental_prefix_violations_flags_only_in_prefix() {
        // prefix_bytes = 100. A CHANGED at old.offset 50 (in prefix), a REMOVED
        // at 30 (in prefix), a CHANGED at 150 (in the un-snapshotted tail — OK),
        // an INSERTED new line at new.offset 60 (in prefix), and a legit append
        // at 200 (OK) => exactly three violations.
        let diff = CorpusDiff {
            old_corpus: "old".into(),
            new_corpus: "new".into(),
            old_idx_version: 2,
            new_idx_version: 2,
            summary: DiffSummary::default(),
            new_lines: vec![addr_at(41, 60), addr_at(42, 200)],
            changed_lines: vec![
                ChangedLine {
                    serial: 20,
                    old: addr_at(20, 50),
                    new: addr_at(20, 50),
                },
                ChangedLine {
                    serial: 90,
                    old: addr_at(90, 150),
                    new: addr_at(90, 150),
                },
            ],
            removed_lines: vec![addr_at(15, 30)],
        };
        let v = incremental_prefix_violations(&diff, 100);
        assert_eq!(v.len(), 3, "three deltas fall inside the 100-byte prefix");
        // Offset-sorted: removed@30, changed@50, inserted@60.
        assert_eq!(v[0].kind, "removed");
        assert_eq!(v[0].offset, 30);
        assert_eq!(v[1].kind, "changed");
        assert_eq!(v[1].offset, 50);
        assert_eq!(v[2].kind, "inserted");
        assert_eq!(v[2].offset, 60);
    }

    #[test]
    fn test_incremental_prefix_violations_empty_for_append_only() {
        // Pure append beyond the prefix => no violations => incremental is sound.
        let diff = CorpusDiff {
            old_corpus: "old".into(),
            new_corpus: "new".into(),
            old_idx_version: 2,
            new_idx_version: 2,
            summary: DiffSummary::default(),
            new_lines: vec![addr_at(30, 100), addr_at(40, 120)],
            changed_lines: vec![],
            removed_lines: vec![],
        };
        assert!(incremental_prefix_violations(&diff, 100).is_empty());
    }
}
