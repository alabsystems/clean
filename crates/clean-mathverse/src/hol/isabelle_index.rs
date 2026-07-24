// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Corpus index sidecar** (`<corpus>.idx`) — the instant-slicing substrate of
//! the standing import pipeline.
//!
//! A single streaming byte-scan of a serial-sorted Isabelle corpus produces a
//! compact, serial-sorted `Vec<`[`IndexEntry`]`>`: per line its leading serial,
//! its exact byte offset + length (delimiter included, matching a
//! `read_until(b'\n')` view), its `"name"` field, its `_def`/`_dict`
//! **registration** flag, and its byte-scan `"k":"thm","id":` dependency edges
//! (the same conservative [`thm_refs_public`] superset the drivers schedule
//! with). With the index present, [`super::isabelle_slice`],
//! [`super::isabelle_targets`], and the `isabelle-verify-one` diagnostic seek
//! directly to the handful of lines they need instead of scanning the (52 GB)
//! corpus — minutes-to-milliseconds.
//!
//! # Staleness
//!
//! The header records the corpus byte length at build time. [`try_load`] rejects
//! (and re-scans, with a stderr hint) an index whose stored length no longer
//! matches the corpus on disk, so a regenerated corpus never serves a stale
//! index. The corpus is the authority; the index is a pure accelerator whose
//! only outputs are byte offsets and a dependency graph both re-derivable from
//! the corpus, so a wrong/absent index can never change a verdict — only cost.

use std::io::{BufRead as _, Read as _, Seek as _, Write as _};
use std::path::{Path, PathBuf};

use super::isabelle_import::{leading_serial, thm_refs_public};

/// Sidecar magic ("CLNISIDX").
const MAGIC: &[u8; 8] = b"CLNISIDX";
/// Bump on ANY incompatible change to [`CorpusIndex`]/[`IndexEntry`] or the
/// on-disk envelope.
///
/// * **v1** — `{serial, offset, len, is_registration, name, deps}`.
/// * **v2** — adds the 0-based `line` number and a BLAKE3 `content_hash` of the
///   trimmed line, so [`super::isabelle_corpus_diff`] can classify two corpus
///   versions line-by-line straight off the sidecars (no full-corpus read). A v1
///   sidecar still loads: [`load_index_versioned`] migrates it, leaving `line`
///   at [`LINE_UNKNOWN`] and `content_hash` at [`ABSENT_HASH`] so consumers
///   recompute on demand (`corpus-diff` seek-reads the exact line).
const FORMAT_VERSION: u32 = 2;
/// Decode budget: a sidecar beyond this is corrupt or hostile, not real.
const DECODE_BUDGET_BYTES: u64 = 16 * 1024 * 1024 * 1024;

/// Sentinel `content_hash` for an entry whose hash is not stored (a v1 sidecar
/// migrated forward). BLAKE3 never produces all-zero bytes for any input, so
/// this is an unambiguous "absent" marker; [`CorpusIndex::content_hash`]
/// seek-reads and recomputes when it sees it.
pub const ABSENT_HASH: [u8; 32] = [0u8; 32];
/// Sentinel `line` for a v1-migrated entry whose true line number is unknown.
pub const LINE_UNKNOWN: u64 = u64::MAX;

/// Errors from corpus-index build / load.
#[derive(Debug, thiserror::Error)]
pub enum IsabelleIndexError {
    /// Filesystem failure reading the corpus or the sidecar.
    #[error("isabelle-index I/O on {path}: {source}")]
    Io {
        /// Path involved.
        path: PathBuf,
        /// Underlying error.
        source: std::io::Error,
    },
    /// Not an index file (bad magic) or an incompatible/absurd envelope.
    #[error("unrecognized corpus-index format (magic/version/length mismatch)")]
    Format,
    /// bincode encode/decode failure (corrupt sidecar).
    #[error("corpus-index encode/decode: {0}")]
    Codec(String),
}

fn io_err(path: &Path) -> impl FnOnce(std::io::Error) -> IsabelleIndexError + '_ {
    move |source| IsabelleIndexError::Io {
        path: path.to_path_buf(),
        source,
    }
}

/// One corpus line's index record. `offset`/`len` address the raw bytes
/// (including the trailing `\n`/`\r`) exactly as a `read_until(b'\n')` consumes
/// them; `name`/`is_registration`/`deps` are computed on the trimmed line so
/// they match the drivers' `String::lines()` view byte-for-byte.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct IndexEntry {
    /// The line's leading proof-term serial (`{"serial":<n>`).
    pub serial: i64,
    /// The line's 0-based corpus line number, counting EVERY delimited line
    /// (empty / non-serial lines included) exactly as the replay drivers'
    /// running index does — so a driver can name an anonymous (`serial == 0`)
    /// line `isabelle.anon.{line}` straight off the sidecar. [`LINE_UNKNOWN`]
    /// on a v1-migrated sidecar.
    pub line: u64,
    /// Byte offset of the line's first byte in the corpus.
    pub offset: u64,
    /// Byte length including the trailing delimiter(s).
    pub len: u64,
    /// TRUE when the (trimmed) line contains `_def` or `_dict` — a PASS-1
    /// registration line the slice extractor includes by default.
    pub is_registration: bool,
    /// The line's `"name"` field (empty when absent / anonymous).
    pub name: String,
    /// BLAKE3 of the **trimmed** line bytes (the drivers' `String::lines()`
    /// view — the exact text that gets parsed and verified). Two entries with an
    /// equal `content_hash` have byte-identical declaration content, the
    /// identity oracle [`super::isabelle_corpus_diff`] classifies UNCHANGED vs
    /// CHANGED with. [`ABSENT_HASH`] on a v1-migrated sidecar (recomputed on
    /// demand from the corpus via [`CorpusIndex::content_hash`]).
    pub content_hash: [u8; 32],
    /// The byte-scan `"k":"thm","id":` dependency serials (conservative superset
    /// of `IsaProof::thm_deps`).
    pub deps: Vec<i64>,
}

/// The whole-corpus index: a serial-sorted entry table plus the corpus byte
/// length it was built against (the staleness guard).
#[derive(Debug, Clone, Default, serde::Serialize, serde::Deserialize)]
pub struct CorpusIndex {
    /// Corpus byte length at build time — [`try_load`]'s cheap staleness check.
    pub corpus_len: u64,
    /// Entries in serial-ascending order (ties broken by offset).
    pub entries: Vec<IndexEntry>,
}

/// The `"name":"..."` field of a corpus line (after the serial key). Mirrors the
/// slice/targets extractors so the index's names are byte-identical to theirs.
fn line_name(line: &str) -> Option<&str> {
    let at = line.find("\"name\":\"")? + "\"name\":\"".len();
    let rest = &line[at..];
    let end = rest.find('"')?;
    Some(&rest[..end])
}

/// The conventional sidecar path for a corpus: `<corpus>.idx`.
#[must_use]
pub fn index_path(corpus: &Path) -> PathBuf {
    let mut s = corpus.as_os_str().to_os_string();
    s.push(".idx");
    PathBuf::from(s)
}

/// Build the corpus index in one streaming pass. Only lines with a parseable
/// leading serial are indexed (exactly the lines the drivers ever key on).
///
/// # Errors
/// [`IsabelleIndexError::Io`] on read failure.
pub fn build_index(corpus: &Path) -> Result<CorpusIndex, IsabelleIndexError> {
    let file = std::fs::File::open(corpus).map_err(io_err(corpus))?;
    let corpus_len = file.metadata().map_err(io_err(corpus))?.len();
    let mut reader = std::io::BufReader::new(file);
    let mut entries: Vec<IndexEntry> = Vec::new();
    let mut offset: u64 = 0;
    // 0-based line index incremented once per delimited line — INCLUDING the
    // empty / non-serial lines the index itself skips — so `line` matches the
    // replay drivers' running index (cf. `retry::derive_rejects`) byte-for-byte.
    let mut line_no: u64 = 0;
    let mut buf: Vec<u8> = Vec::new();
    let mut ref_buf: Vec<i64> = Vec::new();
    loop {
        buf.clear();
        let n = reader.read_until(b'\n', &mut buf).map_err(io_err(corpus))?;
        if n == 0 {
            break;
        }
        let line_start = offset;
        offset += n as u64;
        let cur_line = line_no;
        line_no += 1;
        let raw = String::from_utf8_lossy(&buf);
        let line = raw.trim_end_matches(['\n', '\r']);
        let Some(serial) = leading_serial(line) else {
            continue;
        };
        ref_buf.clear();
        thm_refs_public(line, &mut ref_buf);
        entries.push(IndexEntry {
            serial,
            line: cur_line,
            offset: line_start,
            len: n as u64,
            is_registration: line.contains("_def") || line.contains("_dict"),
            name: line_name(line).unwrap_or("").to_string(),
            content_hash: *blake3::hash(line.as_bytes()).as_bytes(),
            deps: ref_buf.clone(),
        });
    }
    entries.sort_by(|a, b| {
        a.serial
            .cmp(&b.serial)
            .then_with(|| a.offset.cmp(&b.offset))
    });
    Ok(CorpusIndex {
        corpus_len,
        entries,
    })
}

/// Write `index` to `path` atomically (`.tmp` + rename). Envelope: magic + u32
/// version + u64 payload length + bincode payload + trailing BLAKE3 of payload.
///
/// # Errors
/// [`IsabelleIndexError`] on I/O or encode failure.
pub fn save_index(path: &Path, index: &CorpusIndex) -> Result<(), IsabelleIndexError> {
    let payload = bincode::serde::encode_to_vec(index, bincode::config::standard())
        .map_err(|e| IsabelleIndexError::Codec(e.to_string()))?;
    let digest = blake3::hash(&payload);
    let tmp = path.with_extension("idx.tmp");
    {
        let mut w = std::io::BufWriter::new(std::fs::File::create(&tmp).map_err(io_err(&tmp))?);
        w.write_all(MAGIC).map_err(io_err(&tmp))?;
        w.write_all(&FORMAT_VERSION.to_le_bytes())
            .map_err(io_err(&tmp))?;
        w.write_all(&(payload.len() as u64).to_le_bytes())
            .map_err(io_err(&tmp))?;
        w.write_all(&payload).map_err(io_err(&tmp))?;
        w.write_all(digest.as_bytes()).map_err(io_err(&tmp))?;
        w.flush().map_err(io_err(&tmp))?;
    }
    std::fs::rename(&tmp, path).map_err(io_err(path))?;
    Ok(())
}

/// The **v1** on-disk shape of [`IndexEntry`] (no `line`, no `content_hash`),
/// kept so pre-content-hash sidecars still load. Field order matters: bincode
/// encodes structs positionally, so a v1 payload MUST decode against this exact
/// layout, then migrate into the current [`IndexEntry`] with sentinels.
#[derive(serde::Deserialize)]
struct IndexEntryV1 {
    serial: i64,
    offset: u64,
    len: u64,
    is_registration: bool,
    name: String,
    deps: Vec<i64>,
}

/// The **v1** on-disk shape of [`CorpusIndex`].
#[derive(serde::Deserialize)]
struct CorpusIndexV1 {
    corpus_len: u64,
    entries: Vec<IndexEntryV1>,
}

impl From<CorpusIndexV1> for CorpusIndex {
    fn from(v1: CorpusIndexV1) -> Self {
        CorpusIndex {
            corpus_len: v1.corpus_len,
            entries: v1
                .entries
                .into_iter()
                .map(|e| IndexEntry {
                    serial: e.serial,
                    line: LINE_UNKNOWN,
                    offset: e.offset,
                    len: e.len,
                    is_registration: e.is_registration,
                    name: e.name,
                    content_hash: ABSENT_HASH,
                    deps: e.deps,
                })
                .collect(),
        }
    }
}

/// Decode + integrity-check a sidecar's bytes into a [`CorpusIndex`], returning
/// the on-disk [`FORMAT_VERSION`] it was written at. A **v1** sidecar migrates
/// forward (`line` → [`LINE_UNKNOWN`], `content_hash` → [`ABSENT_HASH`]); a
/// **v2** sidecar decodes directly.
///
/// # Errors
/// [`IsabelleIndexError::Format`] on a bad envelope, [`IsabelleIndexError::Codec`]
/// on a digest mismatch or a decode failure.
pub fn load_index_versioned(path: &Path) -> Result<(CorpusIndex, u32), IsabelleIndexError> {
    let mut f = std::fs::File::open(path).map_err(io_err(path))?;
    let mut header = [0u8; 8 + 4 + 8];
    f.read_exact(&mut header).map_err(io_err(path))?;
    if &header[..8] != MAGIC {
        return Err(IsabelleIndexError::Format);
    }
    let version = u32::from_le_bytes([header[8], header[9], header[10], header[11]]);
    if version == 0 || version > FORMAT_VERSION {
        return Err(IsabelleIndexError::Format);
    }
    let payload_len = u64::from_le_bytes([
        header[12], header[13], header[14], header[15], header[16], header[17], header[18],
        header[19],
    ]);
    if payload_len > DECODE_BUDGET_BYTES {
        return Err(IsabelleIndexError::Format);
    }
    let mut payload = vec![0u8; payload_len as usize];
    f.read_exact(&mut payload).map_err(io_err(path))?;
    let mut stored_digest = [0u8; 32];
    f.read_exact(&mut stored_digest).map_err(io_err(path))?;
    if blake3::hash(&payload) != stored_digest {
        return Err(IsabelleIndexError::Codec(
            "payload digest mismatch".to_string(),
        ));
    }
    let cfg = bincode::config::standard();
    let index = if version == 1 {
        let (v1, _): (CorpusIndexV1, usize) = bincode::serde::decode_from_slice(&payload, cfg)
            .map_err(|e| IsabelleIndexError::Codec(e.to_string()))?;
        CorpusIndex::from(v1)
    } else {
        let (index, _): (CorpusIndex, usize) = bincode::serde::decode_from_slice(&payload, cfg)
            .map_err(|e| IsabelleIndexError::Codec(e.to_string()))?;
        index
    };
    Ok((index, version))
}

/// Decode + integrity-check a sidecar's bytes into a [`CorpusIndex`] (any
/// supported [`FORMAT_VERSION`]). See [`load_index_versioned`] for the version.
///
/// # Errors
/// [`IsabelleIndexError::Format`] on a bad envelope, [`IsabelleIndexError::Codec`]
/// on a digest mismatch or a decode failure.
pub fn load_index(path: &Path) -> Result<CorpusIndex, IsabelleIndexError> {
    load_index_versioned(path).map(|(index, _)| index)
}

/// Best-effort load of the `<corpus>.idx` sidecar for a consumer that can fall
/// back to a full scan. Returns `Some(index)` only when the sidecar exists,
/// decodes cleanly, AND its stored corpus length still matches the corpus on
/// disk. Any other outcome returns `None` after printing ONE concise stderr hint
/// (missing / stale / corrupt), so callers degrade to a scan without a hard
/// error. Never returns `Err` — the index is a pure accelerator.
#[must_use]
pub fn try_load(corpus: &Path) -> Option<CorpusIndex> {
    let idx = index_path(corpus);
    if !idx.exists() {
        eprintln!(
            "HINT: no corpus index at {} — scanning the corpus; build one with \
             `clean mathverse isabelle-index --corpus {}` for instant slicing",
            idx.display(),
            corpus.display()
        );
        return None;
    }
    match load_index(&idx) {
        Ok(index) => {
            let actual = std::fs::metadata(corpus).map(|m| m.len()).unwrap_or(0);
            if index.corpus_len == actual {
                Some(index)
            } else {
                eprintln!(
                    "HINT: corpus index {} is STALE (indexed {} bytes, corpus is now {} bytes) — \
                     scanning the corpus; rebuild with `clean mathverse isabelle-index`",
                    idx.display(),
                    index.corpus_len,
                    actual
                );
                None
            }
        }
        Err(e) => {
            eprintln!(
                "HINT: corpus index {} failed to load ({e}) — scanning the corpus",
                idx.display()
            );
            None
        }
    }
}

impl CorpusIndex {
    /// The entry for serial `s` (binary search over the serial-sorted table).
    /// Returns the first entry on a duplicate serial (corpus serials are the
    /// kernel identity and unique in practice).
    #[must_use]
    pub fn get(&self, s: i64) -> Option<&IndexEntry> {
        match self.entries.binary_search_by(|e| e.serial.cmp(&s)) {
            Ok(mut i) => {
                while i > 0 && self.entries[i - 1].serial == s {
                    i -= 1;
                }
                self.entries.get(i)
            }
            Err(_) => None,
        }
    }

    /// Entries in **file (offset) order** — the order a sequential scan yields
    /// them, so an index-driven emit reproduces scan-order output byte-for-byte.
    #[must_use]
    pub fn entries_in_file_order(&self) -> Vec<&IndexEntry> {
        let mut v: Vec<&IndexEntry> = self.entries.iter().collect();
        v.sort_by_key(|e| e.offset);
        v
    }

    /// Seek-read the raw line bytes for `entry` from `corpus`, returning the
    /// trimmed line (trailing `\n`/`\r` removed) — the drivers' `String::lines()`
    /// view of that line.
    ///
    /// # Errors
    /// [`IsabelleIndexError::Io`] on seek/read failure.
    pub fn read_line(
        &self,
        corpus: &Path,
        entry: &IndexEntry,
    ) -> Result<String, IsabelleIndexError> {
        let mut f = std::fs::File::open(corpus).map_err(io_err(corpus))?;
        f.seek(std::io::SeekFrom::Start(entry.offset))
            .map_err(io_err(corpus))?;
        let mut buf = vec![0u8; entry.len as usize];
        f.read_exact(&mut buf).map_err(io_err(corpus))?;
        let s = String::from_utf8_lossy(&buf);
        Ok(s.trim_end_matches(['\n', '\r']).to_string())
    }

    /// The BLAKE3 content hash of `entry`'s trimmed line. Returns the stored
    /// [`IndexEntry::content_hash`] when present (a v2 sidecar — no I/O); on a
    /// v1-migrated entry ([`ABSENT_HASH`]) it seek-reads the single line from
    /// `corpus` and hashes it, matching [`build_index`] byte-for-byte. Never
    /// reads more than one line — a corpus-diff over two sidecars stays
    /// bounded-RAM even when one sidecar predates the content hash.
    ///
    /// # Errors
    /// [`IsabelleIndexError::Io`] on the fallback seek/read.
    pub fn content_hash(
        &self,
        corpus: &Path,
        entry: &IndexEntry,
    ) -> Result<[u8; 32], IsabelleIndexError> {
        if entry.content_hash != ABSENT_HASH {
            return Ok(entry.content_hash);
        }
        let line = self.read_line(corpus, entry)?;
        Ok(*blake3::hash(line.as_bytes()).as_bytes())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const FIXTURE: &str =
        include_str!("../../tests/fixtures/isabelle/hol_foundational_closure.jsonl");

    fn write_fixture(dir: &Path) -> PathBuf {
        let corpus = dir.join("corpus.jsonl");
        let mut lines: Vec<&str> = FIXTURE.lines().filter(|l| !l.trim().is_empty()).collect();
        lines.sort_by_key(|l| leading_serial(l).expect("serials"));
        std::fs::write(&corpus, lines.join("\n") + "\n").expect("write corpus");
        corpus
    }

    #[test]
    fn test_build_index_roundtrips_and_matches_scan() {
        let dir = std::env::temp_dir().join(format!("isa_idx_rt_{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("mk dir");
        let corpus = write_fixture(&dir);

        let index = build_index(&corpus).expect("build");
        // Every indexed serial matches a direct scan, and offset/len address the
        // real line bytes.
        let raw = std::fs::read_to_string(&corpus).expect("read corpus");
        let scan_serials: Vec<i64> = raw.lines().filter_map(leading_serial).collect();
        let mut idx_serials: Vec<i64> = index.entries.iter().map(|e| e.serial).collect();
        assert_eq!(idx_serials.len(), scan_serials.len(), "one entry per line");
        idx_serials.sort_unstable();
        let mut scan_sorted = scan_serials.clone();
        scan_sorted.sort_unstable();
        assert_eq!(
            idx_serials, scan_sorted,
            "index covers exactly the corpus serials"
        );

        // Save + load round-trips byte-for-byte.
        let idx_path = index_path(&corpus);
        save_index(&idx_path, &index).expect("save");
        let loaded = load_index(&idx_path).expect("load");
        assert_eq!(loaded.corpus_len, index.corpus_len);
        assert_eq!(loaded.entries.len(), index.entries.len());

        // Seek-read reproduces each line exactly (vs the sequential scan view).
        let by_offset: Vec<&str> = raw.lines().collect();
        for (line, entry) in by_offset.iter().zip(loaded.entries_in_file_order()) {
            let got = loaded.read_line(&corpus, entry).expect("read line");
            assert_eq!(&got, line, "seek-read must reproduce the scanned line");
        }

        // get() finds an accepted foundational serial (HOL.refl = 300).
        let e = loaded.get(300).expect("serial 300 present");
        assert_eq!(e.name, "HOL.refl");

        // v2: every entry carries a real (non-sentinel) content hash and line
        // number, and the stored hash equals a fresh hash of the seek-read line.
        for entry in &loaded.entries {
            assert_ne!(entry.content_hash, ABSENT_HASH, "v2 stores a real hash");
            assert_ne!(entry.line, LINE_UNKNOWN, "v2 stores a real line number");
            let got = loaded.content_hash(&corpus, entry).expect("hash");
            assert_eq!(got, entry.content_hash, "stored hash == recomputed hash");
        }
        // Line numbers are the dense 0-based file order of a no-empty-line corpus.
        let mut lines_seen: Vec<u64> = loaded.entries.iter().map(|e| e.line).collect();
        lines_seen.sort_unstable();
        assert_eq!(
            lines_seen,
            (0..loaded.entries.len() as u64).collect::<Vec<_>>(),
            "dense corpus: line numbers are 0..N"
        );

        let _ = std::fs::remove_dir_all(&dir);
    }

    /// A v1 sidecar (no `line` / `content_hash`) still loads: it migrates to the
    /// current [`IndexEntry`] with the [`LINE_UNKNOWN`] / [`ABSENT_HASH`]
    /// sentinels, and [`CorpusIndex::content_hash`] recomputes the missing hash
    /// from the corpus so a diff over a legacy sidecar still classifies exactly.
    #[test]
    fn test_v1_sidecar_migrates_and_recomputes_hash() {
        let dir = std::env::temp_dir().join(format!("isa_idx_v1_{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("mk dir");
        let corpus = write_fixture(&dir);
        // Build a v2 index to borrow the real offsets/lens, then hand-encode a v1
        // payload (the pre-content-hash positional layout: corpus_len + entries of
        // {serial, offset, len, is_registration, name, deps}).
        let v2 = build_index(&corpus).expect("build v2");
        let v1_entries: Vec<(i64, u64, u64, bool, String, Vec<i64>)> = v2
            .entries
            .iter()
            .map(|e| {
                (
                    e.serial,
                    e.offset,
                    e.len,
                    e.is_registration,
                    e.name.clone(),
                    e.deps.clone(),
                )
            })
            .collect();
        let payload = bincode::serde::encode_to_vec(
            (v2.corpus_len, &v1_entries),
            bincode::config::standard(),
        )
        .expect("encode v1 payload");
        let digest = blake3::hash(&payload);
        let idx_path = dir.join("corpus.v1.idx");
        {
            let mut w =
                std::io::BufWriter::new(std::fs::File::create(&idx_path).expect("create v1 idx"));
            w.write_all(MAGIC).expect("magic");
            w.write_all(&1u32.to_le_bytes()).expect("version 1");
            w.write_all(&(payload.len() as u64).to_le_bytes())
                .expect("len");
            w.write_all(&payload).expect("payload");
            w.write_all(digest.as_bytes()).expect("digest");
            w.flush().expect("flush");
        }

        let (migrated, version) = load_index_versioned(&idx_path).expect("load v1");
        assert_eq!(version, 1, "sidecar reports its v1 origin");
        assert_eq!(migrated.entries.len(), v2.entries.len(), "same entry count");
        for (m, v) in migrated
            .entries_in_file_order()
            .into_iter()
            .zip(v2.entries_in_file_order())
        {
            assert_eq!(m.serial, v.serial);
            assert_eq!(m.line, LINE_UNKNOWN, "v1 has no line number");
            assert_eq!(m.content_hash, ABSENT_HASH, "v1 has no stored hash");
            // Recompute-on-demand reproduces the v2 stored hash exactly.
            let recomputed = migrated.content_hash(&corpus, m).expect("recompute");
            assert_eq!(recomputed, v.content_hash, "seek-read hash == v2 hash");
        }
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_try_load_rejects_stale_index() {
        let dir = std::env::temp_dir().join(format!("isa_idx_stale_{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("mk dir");
        let corpus = write_fixture(&dir);
        let index = build_index(&corpus).expect("build");
        save_index(&index_path(&corpus), &index).expect("save");
        // Fresh index loads.
        assert!(try_load(&corpus).is_some(), "fresh index loads");
        // Appending to the corpus makes the stored length mismatch -> stale.
        {
            use std::io::Write as _;
            let mut f = std::fs::OpenOptions::new()
                .append(true)
                .open(&corpus)
                .expect("open append");
            writeln!(f, "{{\"serial\":999999,\"name\":\"Extra.x\"}}").expect("append");
        }
        assert!(try_load(&corpus).is_none(), "stale index is rejected");
        let _ = std::fs::remove_dir_all(&dir);
    }
}
