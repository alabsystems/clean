// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Persistent graduation novelty-baseline index (`.mvix`).
//!
//! [`GraduationBaseline::load`](super::intake::GraduationBaseline) scans
//! shards at ~10ms/constant (the per-constant reconstruction path rebuilds
//! the shard expression table from scratch for every constant) — ≥16h for
//! the full 5.77M-declaration `mathverse-v1.2.0` release, measured in
//! GRADUATION #1 (`reports/graduation-1-2026-06-10.md`). This module builds
//! the same `name + statement-hash` baseline **once** per release into a
//! flat, binary-searchable artifact that loads in seconds.
//!
//! Hash discipline: statement hashes are produced by
//! [`expr_canonical_digest`](super::record::expr_canonical_digest) over
//! expressions reconstructed by the **same** code path `load` uses
//! (`shard_reconstruct`), so an index lookup answers exactly the question
//! the graduation gate asks. The corpus digest in the header is blake3 over
//! every shard's bytes in sorted-path order — identical to `load`'s pin.
//!
//! Beyond `name + statement-hash`, the index also carries a **semantic** table
//! (format version 2): the Cake env-free Tier-1.5 *rewrite-canonical* digest
//! ([`clean_cake::identity::structural_rewrite_digest`]) of each constant's
//! type. This is the corpus-scale "same object, different form" key —
//! commutative-operand canonicalisation collapses `a + b` / `b + a`,
//! `P ∧ Q` / `Q ∧ P`, … that the structural statement hash counts as distinct.
//! It is computable with no environment, so it scales to the whole 5.77M
//! release; a hit is a *candidate* to confirm (never a soundness claim).
//!
//! # `MVBIDX01` format (all integers little-endian)
//!
//! ```text
//! [ 0.. 8)  magic            b"MVBIDX01"
//! [ 8..12)  version          u32 ∈ {1, 2}  (1 = no semantic table)
//! [12..16)  sem_count        u32 (semantic-digest prefixes; 0 in v1)
//! [16..24)  name_count       u64 (sorted unique declaration names)
//! [24..32)  hash_count       u64 (sorted unique statement-hash prefixes)
//! [32..40)  names_blob_len   u64
//! [40..72)  corpus_digest    blake3 of shard bytes, sorted-path order
//! [72..  )  name_offsets     (name_count + 1) × u32 prefix offsets
//!           names_blob       UTF-8 names, sorted, concatenated
//!           hash_records     hash_count × 20B: hash_prefix [u8;16]
//!                            ‖ name_idx u32 (FIRST baseline name carrying
//!                            that statement hash, sorted-names index space)
//!           sem_records      sem_count × 20B: sem_prefix [u8;16]
//!                            ‖ name_idx u32 (FIRST baseline name carrying
//!                            that semantic digest). Absent when sem_count = 0.
//! [len-32)  self_digest      blake3 over all preceding bytes
//! ```
//!
//! `hash_prefix` / `sem_prefix` are the first 16 bytes of the blake3 statement
//! / rewrite-canonical digest. Truncation is one-sided safe for novelty: a
//! statement present in the baseline always reproduces its own prefix (never a
//! false `New`); a 128-bit prefix collision could only mark a new statement as
//! `Duplicate` (conservative direction, probability < 2⁻⁸⁰ at corpus scale).
//!
//! **Version compatibility.** The `[12..16)` field was `reserved = 0` in v1,
//! so it reads as `sem_count = 0` — a v1 index simply has no semantic table and
//! every semantic lookup misses. The loader accepts both versions; the builder
//! always writes v2 (with a — possibly empty — semantic table).
//!
//! Fail-closed: the loader verifies magic, version, section arithmetic, the
//! full-file self-digest, name-offset monotonicity/UTF-8, and sortedness of
//! all three tables before serving a single lookup.

use std::collections::HashMap;
use std::io::Write;
use std::path::Path;

use super::intake::collect_shard_paths;
use super::record::expr_canonical_digest;
use crate::error::{MathverseError, MathverseResult};
use crate::shard::ShardReader;
use crate::shard_reconstruct::reconstruct_expr_table_prefix;

pub(crate) const MAGIC: &[u8; 8] = b"MVBIDX01";
/// Current format version the builder writes (semantic table present).
pub(crate) const VERSION: u32 = 2;
/// Earliest format version the loader still accepts (no semantic table).
pub(crate) const MIN_VERSION: u32 = 1;
pub(crate) const HEADER_LEN: usize = 72;
pub(crate) const TRAILER_LEN: usize = 32;
const HASH_RECORD_LEN: usize = 20;
const HASH_PREFIX_LEN: usize = 16;
// The semantic table reuses the hash-record layout (16-byte prefix ‖ u32 name idx).
const SEM_RECORD_LEN: usize = 20;

fn corrupt(path: &Path, reason: impl Into<String>) -> MathverseError {
    MathverseError::BaselineIndexCorrupt {
        path: path.display().to_string(),
        reason: reason.into(),
    }
}

/// Parse a `blake3:<64 hex>` digest string into its 16-byte index prefix.
pub(crate) fn digest_prefix(digest: &str) -> Option<[u8; 16]> {
    let hex = digest.strip_prefix("blake3:")?;
    if hex.len() != 64 {
        return None;
    }
    let mut out = [0u8; 16];
    for (i, byte) in out.iter_mut().enumerate() {
        *byte = u8::from_str_radix(hex.get(2 * i..2 * i + 2)?, 16).ok()?;
    }
    Some(out)
}

// ---------------------------------------------------------------------------
// Builder
// ---------------------------------------------------------------------------

/// Build-side summary returned by [`build_baseline_index`].
#[derive(Debug, Clone)]
pub struct BaselineIndexStats {
    /// Shards scanned (sorted-path order).
    pub shards: usize,
    /// Constant headers visited across all shards.
    pub constants: u64,
    /// Unique declaration names indexed.
    pub names: u64,
    /// Unique statement-hash prefixes indexed.
    pub hashes: u64,
    /// Unique semantic (Tier-1.5 rewrite-canonical) digest prefixes indexed.
    pub semantic_hashes: u64,
    /// Constants whose type could not be reconstructed/hashed (name-only,
    /// same best-effort skip as `GraduationBaseline::load`).
    pub skipped_hashes: u64,
    /// Bytes written to the index file.
    pub index_bytes: u64,
    /// `blake3:<hex>` corpus digest (identical to `GraduationBaseline::load`).
    pub corpus_digest: String,
}

/// Scan a `.mathverse` shard file or directory tree and write a `MVBIDX01`
/// baseline index to `out`.
///
/// Semantics are exactly [`GraduationBaseline::load`]'s: every constant
/// name is indexed; a constant whose type fails reconstruction still
/// participates in name dedup; the first name (corpus order) carrying a
/// statement hash wins.
///
/// # Errors
///
/// I/O failures, malformed shards, or index capacity overflow (name table
/// limited to `u32` offsets/indices).
pub fn build_baseline_index(input: &Path, out: &Path) -> MathverseResult<BaselineIndexStats> {
    let shard_paths = collect_shard_paths(input)?;
    let mut corpus_hasher = blake3::Hasher::new();
    let mut name_ids: HashMap<Box<str>, u32> = HashMap::new();
    let mut names: Vec<Box<str>> = Vec::new();
    let mut hash_first: HashMap<[u8; 16], u32> = HashMap::new();
    // Semantic (Tier-1.5 env-free rewrite-canonical) digest prefix -> first name.
    let mut sem_first: HashMap<[u8; 16], u32> = HashMap::new();
    let mut constants: u64 = 0;
    let mut skipped_hashes: u64 = 0;

    for shard_path in &shard_paths {
        let bytes = std::fs::read(shard_path).map_err(MathverseError::Io)?;
        corpus_hasher.update(&bytes);
        let reader = ShardReader::from_bytes(&bytes)?;
        let table = reconstruct_expr_table_prefix(
            &reader.exprs,
            &reader.levels,
            &reader.strings,
            &reader.level_lists,
        );
        for header in &reader.constants {
            constants += 1;
            let Some(name) = reader.strings.get(header.name_idx as usize) else {
                continue;
            };
            let next_id = u32::try_from(names.len())
                .map_err(|_| corrupt(out, "name table exceeds u32 capacity"))?;
            let id = *name_ids.entry(name.as_str().into()).or_insert_with(|| {
                names.push(name.as_str().into());
                next_id
            });
            let Some(type_) = table.get(header.type_idx as usize) else {
                skipped_hashes += 1;
                continue;
            };
            let Ok(digest) = expr_canonical_digest(type_) else {
                skipped_hashes += 1;
                continue;
            };
            let Some(prefix) = digest_prefix(&digest) else {
                skipped_hashes += 1;
                continue;
            };
            hash_first.entry(prefix).or_insert(id);
            // Semantic key: same reconstructed type, env-free Tier-1.5 digest. Best-effort
            // (a digest that fails to parse simply leaves this constant out of the sem table;
            // its statement-hash entry above still anchors it).
            if let Some(sem_prefix) =
                digest_prefix(&clean_cake::identity::structural_rewrite_digest(type_))
            {
                sem_first.entry(sem_prefix).or_insert(id);
            }
        }
    }
    let corpus_digest = format!("blake3:{}", corpus_hasher.finalize().to_hex());

    // Sort names; remap build-order ids to sorted index space.
    let mut order: Vec<u32> = (0..names.len() as u32).collect();
    order.sort_unstable_by(|&a, &b| names[a as usize].cmp(&names[b as usize]));
    let mut id_to_sorted: Vec<u32> = vec![0; names.len()];
    for (sorted_idx, &id) in order.iter().enumerate() {
        id_to_sorted[id as usize] = sorted_idx as u32;
    }
    let remap = |first: HashMap<[u8; 16], u32>| -> Vec<([u8; 16], u32)> {
        let mut recs: Vec<([u8; 16], u32)> = first
            .into_iter()
            .map(|(prefix, id)| (prefix, id_to_sorted[id as usize]))
            .collect();
        recs.sort_unstable_by_key(|&(prefix, _)| prefix);
        recs
    };
    let records = remap(hash_first);
    let sem_records = remap(sem_first);
    u32::try_from(sem_records.len())
        .map_err(|_| corrupt(out, "semantic table exceeds u32 capacity"))?;

    let blob_len: usize = order.iter().map(|&id| names[id as usize].len()).sum();
    u32::try_from(blob_len).map_err(|_| corrupt(out, "names blob exceeds u32 capacity"))?;

    // Serialize: header ‖ name_offsets ‖ names_blob ‖ hash_records ‖ sem_records ‖ trailer.
    let mut body: Vec<u8> = Vec::with_capacity(
        HEADER_LEN
            + 4 * (names.len() + 1)
            + blob_len
            + HASH_RECORD_LEN * records.len()
            + SEM_RECORD_LEN * sem_records.len(),
    );
    body.extend_from_slice(MAGIC);
    body.extend_from_slice(&VERSION.to_le_bytes());
    body.extend_from_slice(&(sem_records.len() as u32).to_le_bytes());
    body.extend_from_slice(&(names.len() as u64).to_le_bytes());
    body.extend_from_slice(&(records.len() as u64).to_le_bytes());
    body.extend_from_slice(&(blob_len as u64).to_le_bytes());
    let digest_hex = corpus_digest
        .strip_prefix("blake3:")
        .unwrap_or(&corpus_digest);
    let mut digest_raw = [0u8; 32];
    for (i, byte) in digest_raw.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&digest_hex[2 * i..2 * i + 2], 16)
            .map_err(|_| corrupt(out, "internal: corpus digest not hex"))?;
    }
    body.extend_from_slice(&digest_raw);
    debug_assert_eq!(body.len(), HEADER_LEN);

    let mut offset: u32 = 0;
    body.extend_from_slice(&offset.to_le_bytes());
    for &id in &order {
        offset += names[id as usize].len() as u32;
        body.extend_from_slice(&offset.to_le_bytes());
    }
    for &id in &order {
        body.extend_from_slice(names[id as usize].as_bytes());
    }
    for (prefix, name_idx) in &records {
        body.extend_from_slice(prefix);
        body.extend_from_slice(&name_idx.to_le_bytes());
    }
    for (prefix, name_idx) in &sem_records {
        body.extend_from_slice(prefix);
        body.extend_from_slice(&name_idx.to_le_bytes());
    }
    let self_digest = blake3::hash(&body);
    let mut file = std::io::BufWriter::new(std::fs::File::create(out).map_err(MathverseError::Io)?);
    file.write_all(&body).map_err(MathverseError::Io)?;
    file.write_all(self_digest.as_bytes())
        .map_err(MathverseError::Io)?;
    file.flush().map_err(MathverseError::Io)?;

    Ok(BaselineIndexStats {
        shards: shard_paths.len(),
        constants,
        names: names.len() as u64,
        hashes: records.len() as u64,
        semantic_hashes: sem_records.len() as u64,
        skipped_hashes,
        index_bytes: (body.len() + TRAILER_LEN) as u64,
        corpus_digest,
    })
}

// ---------------------------------------------------------------------------
// Loader
// ---------------------------------------------------------------------------

/// A loaded, fully-validated `MVBIDX01` baseline index.
///
/// Lookups are binary searches over the in-memory sections (~µs each); no
/// per-lookup allocation.
#[derive(Debug)]
pub struct BaselineIndex {
    data: Vec<u8>,
    name_count: usize,
    hash_count: usize,
    sem_count: usize,
    name_offsets_pos: usize,
    names_blob_pos: usize,
    hash_records_pos: usize,
    sem_records_pos: usize,
    corpus_digest: String,
}

impl BaselineIndex {
    /// Load and validate an index file. Fail-closed: any structural
    /// inconsistency or digest mismatch is an error.
    pub fn load(path: &Path) -> MathverseResult<Self> {
        let data = std::fs::read(path).map_err(MathverseError::Io)?;
        if data.len() < HEADER_LEN + TRAILER_LEN {
            return Err(corrupt(path, "file shorter than header + trailer"));
        }
        if &data[0..8] != MAGIC {
            return Err(corrupt(path, "bad magic (not an MVBIDX01 index)"));
        }
        let version = u32::from_le_bytes([data[8], data[9], data[10], data[11]]);
        if !(MIN_VERSION..=VERSION).contains(&version) {
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
        let read_u64 = |at: usize| {
            let mut buf = [0u8; 8];
            buf.copy_from_slice(&data[at..at + 8]);
            u64::from_le_bytes(buf)
        };
        // `[12..16)` was `reserved = 0` in v1, so it reads as `sem_count = 0`: a v1
        // index has no semantic table and every semantic lookup misses.
        let sem_count = u32::from_le_bytes([data[12], data[13], data[14], data[15]]) as usize;
        // Enforce the documented v1 contract as a fail-closed invariant: a v1-versioned
        // file MUST declare no semantic table (the field was `reserved = 0`). A v1 file
        // carrying a nonzero sem_count is malformed even if its self-digest checks out.
        if version == MIN_VERSION && sem_count != 0 {
            return Err(corrupt(
                path,
                "v1 index must have sem_count = 0 (no semantic table)",
            ));
        }
        let name_count = usize::try_from(read_u64(16))
            .map_err(|_| corrupt(path, "name_count overflows usize"))?;
        let hash_count = usize::try_from(read_u64(24))
            .map_err(|_| corrupt(path, "hash_count overflows usize"))?;
        let blob_len = usize::try_from(read_u64(32))
            .map_err(|_| corrupt(path, "names_blob_len overflows usize"))?;
        let corpus_digest = {
            let hex: String = data[40..72].iter().map(|b| format!("{b:02x}")).collect();
            format!("blake3:{hex}")
        };
        // All section sizes are computed with checked arithmetic over header-supplied
        // (attacker-controllable) counts: a crafted hash_count/sem_count must yield a
        // fail-closed `BaselineIndexCorrupt`, never an integer-overflow panic/abort.
        let overflow = || corrupt(path, "section arithmetic overflow");
        let name_offsets_len = name_count
            .checked_add(1)
            .and_then(|n| n.checked_mul(4))
            .ok_or_else(overflow)?;
        let name_offsets_pos = HEADER_LEN;
        let names_blob_pos = name_offsets_pos
            .checked_add(name_offsets_len)
            .ok_or_else(overflow)?;
        let hash_records_pos = names_blob_pos.checked_add(blob_len).ok_or_else(overflow)?;
        let hash_bytes = HASH_RECORD_LEN
            .checked_mul(hash_count)
            .ok_or_else(overflow)?;
        let sem_records_pos = hash_records_pos
            .checked_add(hash_bytes)
            .ok_or_else(overflow)?;
        let sem_bytes = SEM_RECORD_LEN.checked_mul(sem_count).ok_or_else(overflow)?;
        let expected_len = sem_records_pos
            .checked_add(sem_bytes)
            .ok_or_else(overflow)?;
        if expected_len != body_len {
            return Err(corrupt(
                path,
                format!("section sizes claim {expected_len} bytes, body has {body_len}"),
            ));
        }
        let index = Self {
            data,
            name_count,
            hash_count,
            sem_count,
            name_offsets_pos,
            names_blob_pos,
            hash_records_pos,
            sem_records_pos,
            corpus_digest,
        };
        index.validate_sorted(path)?;
        Ok(index)
    }

    /// Verify offset monotonicity, blob coverage, UTF-8, and strict
    /// sortedness of both tables (binary-search preconditions).
    fn validate_sorted(&self, path: &Path) -> MathverseResult<()> {
        let blob_len = self.hash_records_pos - self.names_blob_pos;
        let mut prev_end = 0usize;
        let mut prev_name: Option<&str> = None;
        for i in 0..self.name_count {
            let start = self.name_offset(i);
            let end = self.name_offset(i + 1);
            if start != prev_end || end < start || end > blob_len {
                return Err(corrupt(path, format!("name offset {i} out of order")));
            }
            prev_end = end;
            let bytes = &self.data[self.names_blob_pos + start..self.names_blob_pos + end];
            let name = std::str::from_utf8(bytes)
                .map_err(|_| corrupt(path, format!("name {i} is not UTF-8")))?;
            if prev_name.is_some_and(|p| p >= name) {
                return Err(corrupt(path, format!("names not strictly sorted at {i}")));
            }
            prev_name = Some(name);
        }
        if self.name_count > 0 && prev_end != blob_len {
            return Err(corrupt(path, "names blob has trailing bytes"));
        }
        self.validate_record_table(path, self.hash_records_pos, self.hash_count, "hash")?;
        self.validate_record_table(path, self.sem_records_pos, self.sem_count, "sem")?;
        Ok(())
    }

    /// Validate a 20-byte record table (strict prefix sortedness + name-idx
    /// range). Both the statement-hash and semantic tables share the layout.
    fn validate_record_table(
        &self,
        path: &Path,
        pos: usize,
        count: usize,
        label: &str,
    ) -> MathverseResult<()> {
        let mut prev: Option<&[u8]> = None;
        for i in 0..count {
            let rec = &self.data[pos + HASH_RECORD_LEN * i..pos + HASH_RECORD_LEN * (i + 1)];
            let prefix = &rec[..HASH_PREFIX_LEN];
            if prev.is_some_and(|p| p >= prefix) {
                return Err(corrupt(
                    path,
                    format!("{label} table not strictly sorted at {i}"),
                ));
            }
            prev = Some(prefix);
            let name_idx = u32::from_le_bytes([rec[16], rec[17], rec[18], rec[19]]) as usize;
            if name_idx >= self.name_count {
                return Err(corrupt(
                    path,
                    format!("{label} record {i} name_idx out of range"),
                ));
            }
        }
        Ok(())
    }

    fn name_offset(&self, i: usize) -> usize {
        let at = self.name_offsets_pos + 4 * i;
        u32::from_le_bytes([
            self.data[at],
            self.data[at + 1],
            self.data[at + 2],
            self.data[at + 3],
        ]) as usize
    }

    fn name_at(&self, i: usize) -> &str {
        let start = self.names_blob_pos + self.name_offset(i);
        let end = self.names_blob_pos + self.name_offset(i + 1);
        // Validated UTF-8 at load time; recover gracefully regardless.
        std::str::from_utf8(&self.data[start..end]).unwrap_or("")
    }

    /// Number of unique declaration names indexed.
    #[must_use]
    pub fn name_count(&self) -> usize {
        self.name_count
    }

    /// Number of unique statement-hash prefixes indexed.
    #[must_use]
    pub fn hash_count(&self) -> usize {
        self.hash_count
    }

    /// Number of unique semantic (Tier-1.5 rewrite-canonical) prefixes indexed
    /// (0 for a v1 index — no semantic table).
    #[must_use]
    pub fn semantic_count(&self) -> usize {
        self.sem_count
    }

    /// `blake3:<hex>` digest over the baseline shard bytes (sorted-path
    /// order) — identical to `GraduationBaseline::load`'s pin digest.
    #[must_use]
    pub fn corpus_digest(&self) -> &str {
        &self.corpus_digest
    }

    /// Exact-name membership (binary search, ~µs).
    #[must_use]
    pub fn contains_name(&self, name: &str) -> bool {
        let mut lo = 0usize;
        let mut hi = self.name_count;
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            match self.name_at(mid).cmp(name) {
                std::cmp::Ordering::Equal => return true,
                std::cmp::Ordering::Less => lo = mid + 1,
                std::cmp::Ordering::Greater => hi = mid,
            }
        }
        false
    }

    /// Statement-hash lookup (`blake3:<hex>` digest string → first baseline
    /// name carrying it). Binary search, ~µs. Returns `None` for digests
    /// that do not parse — fail toward `New` is impossible for baseline
    /// statements (they always reproduce their own digest), and the gate
    /// hashes candidates with the same primitive before calling this.
    #[must_use]
    pub fn lookup_statement_hash(&self, digest: &str) -> Option<&str> {
        self.lookup_in_table(self.hash_records_pos, self.hash_count, digest)
    }

    /// Semantic lookup (`blake3:<hex>` Tier-1.5 env-free rewrite-canonical
    /// digest → first baseline name carrying it). The "same object, different
    /// form" corpus probe. Always `None` for a v1 index (empty semantic
    /// table). A hit is a *candidate* match, not a soundness claim.
    #[must_use]
    pub fn lookup_semantic(&self, digest: &str) -> Option<&str> {
        self.lookup_in_table(self.sem_records_pos, self.sem_count, digest)
    }

    /// Binary search over a 20-byte record table (16-byte prefix ‖ u32 name
    /// idx). Shared by the statement-hash and semantic tables.
    fn lookup_in_table(&self, pos: usize, count: usize, digest: &str) -> Option<&str> {
        let prefix = digest_prefix(digest)?;
        let mut lo = 0usize;
        let mut hi = count;
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            let at = pos + HASH_RECORD_LEN * mid;
            let rec = &self.data[at..at + HASH_RECORD_LEN];
            match rec[..HASH_PREFIX_LEN].cmp(&prefix) {
                std::cmp::Ordering::Equal => {
                    let name_idx =
                        u32::from_le_bytes([rec[16], rec[17], rec[18], rec[19]]) as usize;
                    return Some(self.name_at(name_idx));
                }
                std::cmp::Ordering::Less => lo = mid + 1,
                std::cmp::Ordering::Greater => hi = mid,
            }
        }
        None
    }
}

#[cfg(test)]
#[path = "baseline_index_tests.rs"]
mod tests;
