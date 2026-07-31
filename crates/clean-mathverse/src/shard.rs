// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `.mathverse` shard format: read, write, and mmap support.
//!
//! Shard layout:
//! ```text
//! HEADER (256 bytes)
//!   magic: u32            = 0x4F4D4547 ("OMEG")
//!   version: u32          = 3 (v1 = 32-byte headers, v2 = 64-byte with
//!                              level_params, v3 = + closure-binding fields)
//!   flags: u32            (bit 0 = has sorted name index)
//!   string_count: u32
//!   string_data_len: u32  (compressed)
//!   level_count: u32
//!   expr_count: u32
//!   constant_count: u32
//!   bloom_size: u32       (bytes, always 256KB = 262144)
//!   provenance_len: u32   (compressed)
//!   sorted_index_len: u32 (bytes, 0 if absent)
//!   level_lists_count: u32 (v2+, 0 for v1)
//!   --- v3 closure-binding fields (bytes 48..96; zero for v1/v2) ---
//!   source_olean_blake3: [u8; 32] @48..80  (blake3 of base++.private++.server)
//!   source_olean_len: u64         @80..88  (total length-prefixed source bytes)
//!   fail_closed_verified: u32     @88..92  (1 = build-time fidelity gate passed)
//!   module_name_idx: u32          @92..96  (string-table idx of declaring module)
//!   reserved: [u8; 160]            @96..256 (zero)
//! STRING TABLE (zstd compressed)
//!   [len: u32, utf8_bytes...] per string
//! LEVEL POOL (raw, mmap-friendly)
//!   [FlatLevel; level_count] (12 bytes each)
//! FLATEXPR ARENA (raw, mmap-friendly, topo-sorted)
//!   [FlatExpr; expr_count] (16 bytes each)
//! CONSTANT HEADERS (raw, mmap-friendly)
//!   [MathverseConstantHeader; constant_count] (64 bytes v2, 32 bytes v1)
//! LEVEL LISTS TABLE (v2+, raw u32 array)
//!   [count, level_idx_0, ..., level_idx_N, count, ...] (4 bytes each)
//! BLOOM FILTER (256KB)
//!   name lookup bloom filter
//! SORTED NAME INDEX (optional, flag bit 0)
//!   [(name_hash: u64, constant_idx: u32); N] sorted by name_hash
//! PROVENANCE SIDECAR (zstd compressed, cold)
//!   serialized provenance entries
//! FOOTER (64 bytes)
//!   content_hash: [u8; 32] (blake3 of everything before footer)
//!   reserved: [u8; 32]
//! ```

use std::collections::HashMap;
use std::io::Write;
use std::path::Path;

use clean_kernel::flat::FlatExpr;
use clean_kernel::flat::FlatLevel;
use memmap2::Mmap;

use crate::error::{MathverseError, MathverseResult};
use crate::provenance::ProvenanceSidecar;
use crate::types::{AxiomProfile, MathverseConstantHeader};

pub const SHARD_MAGIC: u32 = 0x4F4D_4547; // "OMEG"
/// Current shard version (v3 adds the closure-binding header fields at bytes
/// 48..96: source_olean_blake3, source_olean_len, fail_closed_verified,
/// module_name_idx — see the layout doc above and `ShardHeader`).
pub const SHARD_VERSION: u32 = 3;
/// Prior shard version (64-byte constant headers with level_params, no closure
/// binding). Retained so the SHIPPED mathverse-v1.3.0 library (v2, 1,052,886
/// decls) keeps loading via the eager readers, and as the keying threshold for
/// the `level_lists_count` decode (which must stay `>= SHARD_VERSION_V2`, NOT
/// `>= SHARD_VERSION`, or the v3 bump would wrongly zero v2 level_lists).
pub const SHARD_VERSION_V2: u32 = 2;
/// Legacy shard version (32-byte constant headers, no level_params).
pub const SHARD_VERSION_LEGACY: u32 = 1;
pub const HEADER_SIZE: usize = 256;
pub const FOOTER_SIZE: usize = 64;
pub const BLOOM_SIZE: usize = 256 * 1024; // 256KB

/// Default ceiling on a single zstd-decompressed section (string table or
/// provenance sidecar), used as the `capacity` bound passed to
/// `zstd::bulk::decompress`. The old hard 64 MiB cap rejected legitimate
/// production shards: `lean4_mathlib4`'s provenance sidecar decompresses to
/// ~71.6 MiB and `metamath_set`'s string table is already ~33 MiB. This is a
/// resource limit (guards against a decompression bomb), not a format
/// constraint — raising it loads more real data without changing any decl or
/// trust label. 4 GiB comfortably fits every shipped Core shard while staying
/// well under `usize::MAX`. Override with `MATHVERSE_MAX_DECOMPRESS_BYTES`.
pub const DEFAULT_MAX_DECOMPRESS_BYTES: usize = 4 * 1024 * 1024 * 1024;

/// Environment variable to override [`DEFAULT_MAX_DECOMPRESS_BYTES`] (decimal
/// byte count). Invalid or absent values fall back to the default.
pub const MAX_DECOMPRESS_BYTES_ENV: &str = "MATHVERSE_MAX_DECOMPRESS_BYTES";

/// Resolve the maximum decompressed-section size, honoring the
/// [`MAX_DECOMPRESS_BYTES_ENV`] override when it parses as a `usize`.
#[must_use]
pub fn max_decompress_bytes() -> usize {
    std::env::var(MAX_DECOMPRESS_BYTES_ENV)
        .ok()
        .and_then(|v| v.trim().parse::<usize>().ok())
        .filter(|&n| n > 0)
        .unwrap_or(DEFAULT_MAX_DECOMPRESS_BYTES)
}

/// Flag bit: shard contains a sorted name index section for O(log n) lookup.
pub const FLAG_HAS_SORTED_INDEX: u32 = 1 << 0;

/// Size of each entry in the sorted name index: (name_hash: u64, constant_idx: u32) = 12 bytes.
pub const SORTED_INDEX_ENTRY_SIZE: usize = 12;

// ---------------------------------------------------------------------------
// ShardHeader
// ---------------------------------------------------------------------------

/// Parsed shard header (first 256 bytes).
#[derive(Clone, Debug)]
pub struct ShardHeader {
    pub magic: u32,
    pub version: u32,
    pub flags: u32,
    pub string_count: u32,
    pub string_data_len: u32,
    pub level_count: u32,
    pub expr_count: u32,
    pub constant_count: u32,
    pub bloom_size: u32,
    pub provenance_len: u32,
    /// Length in bytes of the sorted name index section (0 if absent).
    /// Stored at header offset 40..44.
    pub sorted_index_len: u32,
    /// Number of u32 entries in the level_lists table (v2+, 0 for v1).
    /// Stored at header offset 44..48.
    pub level_lists_count: u32,
    /// blake3 of the source olean's `base ++ .private ++ .server` regions
    /// (length-prefixed; see [`crate::cli::closure_load::source_olean_digest`]).
    /// v3 closure-binding field at bytes 48..80; zero for v1/v2 and for synthetic
    /// readers (those with no backing olean). The loader recomputes this against
    /// the on-disk olean for the shard's OWN declaring module to bind the served
    /// content to the exact bytes eager would import.
    pub source_olean_blake3: [u8; 32],
    /// Total length of the length-prefixed source-olean byte stream that
    /// [`Self::source_olean_blake3`] hashes. v3 field at bytes 80..88; zero
    /// otherwise. Checked alongside the hash as a cheap mismatch tripwire.
    pub source_olean_len: u64,
    /// `1` iff the build-time fail-closed fidelity gate passed for EVERY served
    /// constant in this shard (round-trip oracle in
    /// `build_kernel_faithful_shard`). v3 field at bytes 88..92; `0` for v1/v2,
    /// synthetic readers, and any v3 shard not produced by the fidelity gate.
    /// The loader REFUSES to lazily serve a shard with `0` here.
    pub fail_closed_verified: u32,
    /// String-table index of this shard's DECLARING module name (`module_name`
    /// on the writer). v3 field at bytes 92..96; `0` for v1/v2 and synthetic
    /// readers. The loader resolves the olean for THIS module (never the
    /// filename) to defeat filename-vs-content laundering.
    pub module_name_idx: u32,
}

impl ShardHeader {
    /// Check whether the sorted name index flag is set.
    #[inline]
    pub fn has_sorted_index(&self) -> bool {
        (self.flags & FLAG_HAS_SORTED_INDEX) != 0
    }

    /// Whether this is a legacy (v1) shard with 32-byte constant headers.
    #[inline]
    pub fn is_legacy(&self) -> bool {
        self.version == SHARD_VERSION_LEGACY
    }

    /// Size of each constant header in this shard's format.
    #[inline]
    pub fn constant_header_size(&self) -> usize {
        if self.is_legacy() {
            MathverseConstantHeader::LEGACY_SIZE
        } else {
            MathverseConstantHeader::SIZE
        }
    }

    pub fn to_bytes(&self) -> [u8; HEADER_SIZE] {
        let mut buf = [0u8; HEADER_SIZE];
        buf[0..4].copy_from_slice(&self.magic.to_le_bytes());
        buf[4..8].copy_from_slice(&self.version.to_le_bytes());
        buf[8..12].copy_from_slice(&self.flags.to_le_bytes());
        buf[12..16].copy_from_slice(&self.string_count.to_le_bytes());
        buf[16..20].copy_from_slice(&self.string_data_len.to_le_bytes());
        buf[20..24].copy_from_slice(&self.level_count.to_le_bytes());
        buf[24..28].copy_from_slice(&self.expr_count.to_le_bytes());
        buf[28..32].copy_from_slice(&self.constant_count.to_le_bytes());
        buf[32..36].copy_from_slice(&self.bloom_size.to_le_bytes());
        buf[36..40].copy_from_slice(&self.provenance_len.to_le_bytes());
        buf[40..44].copy_from_slice(&self.sorted_index_len.to_le_bytes());
        buf[44..48].copy_from_slice(&self.level_lists_count.to_le_bytes());
        // v3 closure-binding fields at bytes 48..96 (zero on v1/v2 headers
        // because the struct fields default to zero there). Bytes 0..48 are
        // byte-identical to v2, so a v2 reader of a v3 header sees the same
        // prefix and the new bytes are inert to it.
        buf[48..80].copy_from_slice(&self.source_olean_blake3);
        buf[80..88].copy_from_slice(&self.source_olean_len.to_le_bytes());
        buf[88..92].copy_from_slice(&self.fail_closed_verified.to_le_bytes());
        buf[92..96].copy_from_slice(&self.module_name_idx.to_le_bytes());
        // bytes 96..256 reserved (zeros)
        buf
    }

    /// Parse a header accepting ANY supported version (v1, v2, or v3).
    ///
    /// Used by the GENERAL eager readers (`from_bytes`/`from_mmap`) so the
    /// shipped mathverse-v1.3.0 library (v2) keeps loading after the v3 bump.
    /// The lazy/closure path uses [`Self::from_bytes_strict`] with
    /// `min_version = SHARD_VERSION` to REQUIRE the closure-binding fields.
    pub fn from_bytes(buf: &[u8; HEADER_SIZE]) -> MathverseResult<Self> {
        Self::from_bytes_strict(buf, SHARD_VERSION_LEGACY)
    }

    /// Parse a header requiring `version >= min_version`.
    ///
    /// SOUNDNESS (closure binding): the lazy/checksum-skipping path
    /// ([`ShardMmapReader::open_lazy`] → [`ShardMmapReader::from_mmap_no_checksum`])
    /// threads `min_version = SHARD_VERSION` so a pre-v3 (unbound) shard is
    /// REJECTED before any constant can be lazily served — the version field is
    /// the sole pre-trust gate on that path. The general eager readers thread
    /// `min_version = SHARD_VERSION_LEGACY`, accepting v1/v2/v3 unchanged.
    pub(crate) fn from_bytes_strict(
        buf: &[u8; HEADER_SIZE],
        min_version: u32,
    ) -> MathverseResult<Self> {
        let magic = u32::from_le_bytes([buf[0], buf[1], buf[2], buf[3]]);
        if magic != SHARD_MAGIC {
            return Err(MathverseError::InvalidMagic {
                expected: SHARD_MAGIC,
                got: magic,
            });
        }
        let version = u32::from_le_bytes([buf[4], buf[5], buf[6], buf[7]]);
        // Accept v1, v2, v3, but never below the caller's floor (the lazy path
        // sets it to SHARD_VERSION so v1/v2 closure shards are refused -> eager).
        if version < min_version
            || (version != SHARD_VERSION
                && version != SHARD_VERSION_V2
                && version != SHARD_VERSION_LEGACY)
        {
            return Err(MathverseError::UnsupportedVersion(version));
        }
        // CRITICAL: key level_lists on v2 (NOT the bumped SHARD_VERSION), or the
        // v3 bump would wrongly treat every v2 library shard as having no
        // level_lists and corrupt its decode.
        let level_lists_count = if version >= SHARD_VERSION_V2 {
            u32::from_le_bytes([buf[44], buf[45], buf[46], buf[47]])
        } else {
            0 // v1 shards have no level_lists section
        };
        // v3 closure-binding fields decode only at v3; pre-v3 headers leave
        // bytes 48..96 as zero, decoded here as "unbound" (loader refuses lazy).
        let (source_olean_blake3, source_olean_len, fail_closed_verified, module_name_idx) =
            if version >= SHARD_VERSION {
                let mut hash = [0u8; 32];
                hash.copy_from_slice(&buf[48..80]);
                (
                    hash,
                    u64::from_le_bytes([
                        buf[80], buf[81], buf[82], buf[83], buf[84], buf[85], buf[86], buf[87],
                    ]),
                    u32::from_le_bytes([buf[88], buf[89], buf[90], buf[91]]),
                    u32::from_le_bytes([buf[92], buf[93], buf[94], buf[95]]),
                )
            } else {
                ([0u8; 32], 0, 0, 0)
            };
        Ok(Self {
            magic,
            version,
            flags: u32::from_le_bytes([buf[8], buf[9], buf[10], buf[11]]),
            string_count: u32::from_le_bytes([buf[12], buf[13], buf[14], buf[15]]),
            string_data_len: u32::from_le_bytes([buf[16], buf[17], buf[18], buf[19]]),
            level_count: u32::from_le_bytes([buf[20], buf[21], buf[22], buf[23]]),
            expr_count: u32::from_le_bytes([buf[24], buf[25], buf[26], buf[27]]),
            constant_count: u32::from_le_bytes([buf[28], buf[29], buf[30], buf[31]]),
            bloom_size: u32::from_le_bytes([buf[32], buf[33], buf[34], buf[35]]),
            provenance_len: u32::from_le_bytes([buf[36], buf[37], buf[38], buf[39]]),
            sorted_index_len: u32::from_le_bytes([buf[40], buf[41], buf[42], buf[43]]),
            level_lists_count,
            source_olean_blake3,
            source_olean_len,
            fail_closed_verified,
            module_name_idx,
        })
    }
}

// ---------------------------------------------------------------------------
// Sorted name index entry
// ---------------------------------------------------------------------------

/// An entry in the sorted name index: blake3-truncated hash + constant index.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct NameIndexEntry {
    pub(crate) name_hash: u64,
    pub(crate) constant_idx: u32,
}

impl NameIndexEntry {
    fn to_bytes(self) -> [u8; SORTED_INDEX_ENTRY_SIZE] {
        let mut buf = [0u8; SORTED_INDEX_ENTRY_SIZE];
        buf[0..8].copy_from_slice(&self.name_hash.to_le_bytes());
        buf[8..12].copy_from_slice(&self.constant_idx.to_le_bytes());
        buf
    }

    fn from_bytes(buf: &[u8; SORTED_INDEX_ENTRY_SIZE]) -> Self {
        Self {
            name_hash: u64::from_le_bytes([
                buf[0], buf[1], buf[2], buf[3], buf[4], buf[5], buf[6], buf[7],
            ]),
            constant_idx: u32::from_le_bytes([buf[8], buf[9], buf[10], buf[11]]),
        }
    }
}

/// Compute a u64 name hash from a string via blake3 truncation.
#[inline]
fn name_hash(name: &str) -> u64 {
    let h = blake3::hash(name.as_bytes());
    let bytes = h.as_bytes();
    u64::from_le_bytes([
        bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
    ])
}

// ---------------------------------------------------------------------------
// ShardWriter
// ---------------------------------------------------------------------------

/// Statistics about deduplication performed by a [`ShardWriter`].
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct DedupStats {
    /// Total number of `add_expr` calls.
    pub exprs_total: u64,
    /// Number of `add_expr` calls that returned an existing index.
    pub exprs_deduped: u64,
    /// Total number of `add_level` calls.
    pub levels_total: u64,
    /// Number of `add_level` calls that returned an existing index.
    pub levels_deduped: u64,
    /// Total number of `add_string` calls.
    pub strings_total: u64,
    /// Number of `add_string` calls that returned an existing index.
    pub strings_deduped: u64,
}

/// One constant's name, current axiom profile, and dependency names, as
/// extracted by [`ShardWriter::constant_axiom_dep_names`] for the cross-shard
/// axiom-profile closure.
///
/// Names (both the constant's own and its dependencies') are owned `String`s so
/// they can be matched across shard boundaries, where the per-shard `name_idx`
/// values are not comparable.
#[derive(Clone, Debug)]
pub(crate) struct ConstantAxiomDeps {
    /// Fully-qualified name of this constant.
    pub(crate) name: String,
    /// The constant's axiom profile after the within-shard closure (the input
    /// to the cross-shard fixed-point).
    pub(crate) profile: AxiomProfile,
    /// Names of every constant referenced by this constant's type or value.
    pub(crate) dep_names: Vec<String>,
}

/// Builder for writing `.mathverse` shard files.
///
/// Hash-conses expressions, levels, and strings so that identical values
/// are stored only once in the arena. This is critical for keeping shard
/// sizes manageable — common subexpressions like `Nat`, `Prop`, `Bool`,
/// `Sort(0)` would otherwise be duplicated thousands of times.
pub struct ShardWriter {
    strings: Vec<String>,
    levels: Vec<FlatLevel>,
    exprs: Vec<FlatExpr>,
    constants: Vec<MathverseConstantHeader>,
    provenance: Vec<u8>,
    /// Level lists table: `[count: u32, level_idx_0: u32, ..., level_idx_N: u32, ...]`.
    /// Each entry starts with a count followed by that many level pool indices.
    /// `FlatExpr::const_ref.levels_list_idx` points into this table (byte offset / 4).
    level_lists: Vec<u32>,
    /// Dedup for level lists: sorted level indices -> level_lists offset.
    level_list_dedup: hashbrown::HashMap<Vec<u32>, u32>,
    // Hash-consing dedup tables: canonical byte key -> arena index.
    expr_dedup: hashbrown::HashMap<[u8; FlatExpr::SIZE], u32>,
    level_dedup: hashbrown::HashMap<[u8; FlatLevel::SIZE], u32>,
    string_dedup: hashbrown::HashMap<String, u32>,
    // Counters for dedup statistics.
    total_expr_adds: u64,
    total_level_adds: u64,
    total_string_adds: u64,
    // --- v3 closure-binding fields (written into the header by `write`) ---
    /// blake3 of the source olean (`base ++ .private ++ .server`, length-prefixed)
    /// this shard was built from, or `None` for a shard with no backing olean
    /// (synthetic / library writers). Persisted to header bytes 48..80.
    source_olean_blake3: Option<[u8; 32]>,
    /// Total length of the length-prefixed source-olean stream. Persisted to
    /// header bytes 80..88.
    source_olean_len: u64,
    /// `true` iff the build-time fail-closed fidelity gate passed for every
    /// served constant. Persisted to header bytes 88..92 (1/0). Defaults `false`
    /// so any writer that does NOT run the gate produces an un-served shard.
    fail_closed_verified: bool,
    /// This shard's declaring module name, interned into the string table at
    /// `write` time and persisted as `module_name_idx` (header bytes 92..96).
    module_name: Option<String>,
}

impl ShardWriter {
    pub fn new() -> Self {
        // The strings and levels arrays are pre-seeded with a sentinel
        // empty string and the canonical `FlatLevel::zero()`. Their
        // dedup maps must be seeded TO MATCH, otherwise the next
        // `add_string("")` / `add_level(zero)` call would push a
        // duplicate at index 1 and miss the pre-seeded index 0 — a
        // bug that bloated every shard's level table and caused tests
        // asserting `add_level(zero) == 0` to fail at index 1.
        let mut string_dedup = hashbrown::HashMap::new();
        string_dedup.insert(String::new(), 0);
        let zero_level = clean_kernel::flat::FlatLevel::zero();
        let mut level_dedup = hashbrown::HashMap::new();
        level_dedup.insert(level_to_bytes(&zero_level), 0);
        Self {
            strings: vec![String::new()],
            levels: vec![zero_level],
            exprs: Vec::new(),
            constants: Vec::new(),
            provenance: Vec::new(),
            level_lists: Vec::new(),
            level_list_dedup: hashbrown::HashMap::new(),
            expr_dedup: hashbrown::HashMap::new(),
            level_dedup,
            string_dedup,
            total_expr_adds: 0,
            total_level_adds: 0,
            total_string_adds: 0,
            source_olean_blake3: None,
            source_olean_len: 0,
            fail_closed_verified: false,
            module_name: None,
        }
    }

    /// Record the source-olean content binding (blake3 over the length-prefixed
    /// `base ++ .private ++ .server` stream) on this writer, persisted into the
    /// v3 header at `write` time. SOUNDNESS: the loader recomputes this against
    /// the on-disk olean for [`Self::set_module_name`]'s module and refuses to
    /// serve any shard whose recomputed digest/len differs.
    pub(crate) fn set_source_olean_digest(&mut self, blake3: [u8; 32], len: u64) {
        self.source_olean_blake3 = Some(blake3);
        self.source_olean_len = len;
    }

    /// Record this shard's DECLARING module name (interned into the string table
    /// at `write` time as `module_name_idx`). SOUNDNESS: the loader resolves the
    /// olean for THIS module (never the file name), defeating filename-vs-content
    /// laundering.
    pub(crate) fn set_module_name(&mut self, module: &str) {
        self.module_name = Some(module.to_string());
    }

    /// Set the on-disk fail-closed fidelity marker. SOUNDNESS: must be set to
    /// `true` ONLY after the build-time round-trip oracle has verdict-verified
    /// EVERY served constant (see `build_kernel_faithful_shard`). The loader
    /// refuses to lazily serve a shard with this `false`/0, so a non-gated
    /// writer can never have its constants served on the trust-skipping path.
    pub(crate) fn set_fail_closed_verified(&mut self, verified: bool) {
        self.fail_closed_verified = verified;
    }

    /// Record an 8-byte per-constant reconstruction digest into `_pad2[17..25]`.
    /// Returns `false` when `idx` is out of range. `0` decodes as unset.
    ///
    /// This is a CORRUPTION TRIPWIRE (64-bit; collision ~2^-64), NOT a tamper
    /// boundary against a fully-malicious bytes-controlling attacker (no signing
    /// key). It lives in the constant-header bytes, so it IS covered by the footer
    /// content-hash — the footer is merely SKIPPED by the lazy/mmap serving path
    /// (`from_mmap_no_checksum`). The load-time content-binding verification
    /// (`closure_load::verify_closure_shards_against_oleans`) now RE-DERIVES this
    /// digest from the SAME `materialize` path the loader serves and requires a
    /// match before a shard is served, so it IS recomputed at load — a real
    /// load-time gate binding the served arena to the build-time-verified content.
    pub(crate) fn set_constant_recon_digest(&mut self, idx: u32, digest: [u8; 8]) -> bool {
        match self.constants.get_mut(idx as usize) {
            Some(constant) => {
                constant.set_recon_digest(digest);
                true
            }
            None => false,
        }
    }

    /// Add a string to the string table. Returns its index.
    ///
    /// Deduplicates: if the same string was already added, returns the
    /// existing index without allocating a new slot.
    pub fn add_string(&mut self, s: &str) -> u32 {
        self.total_string_adds += 1;
        if let Some(&idx) = self.string_dedup.get(s) {
            return idx;
        }
        let idx = self.strings.len() as u32;
        self.strings.push(s.to_string());
        self.string_dedup.insert(s.to_string(), idx);
        idx
    }

    /// Append a contiguous block of strings to the string table *without*
    /// deduplicating against previously added strings. Returns the starting
    /// index of the block. An empty input returns `0` (the convention used
    /// elsewhere for "no level params").
    ///
    /// This exists to support consumers (notably
    /// [`compact_deltas`]) that require a contiguous run of string slots
    /// — e.g. the `level_params_start..+level_params_count` window for a
    /// constant's universe parameter names. Routing those through
    /// [`Self::add_string`] would return earlier (cached) indices for any
    /// string that happens to be shared with previously merged shards,
    /// breaking the contiguous-block invariant.
    ///
    /// The `string_dedup` cache is *not* updated so that subsequent
    /// [`Self::add_string`] calls for the same name still return the
    /// original (non-block) index. This means a shared string may appear
    /// more than once in the output table; that is the intentional cost
    /// of guaranteeing contiguity.
    pub fn add_string_block(&mut self, strings: &[&str]) -> u32 {
        if strings.is_empty() {
            return 0;
        }
        let start = self.strings.len() as u32;
        for s in strings {
            self.total_string_adds += 1;
            self.strings.push((*s).to_string());
            // Populate dedup only for names not yet seen, so later
            // `add_string` calls for fresh strings can still hit the cache.
            // Existing entries are left untouched to preserve previously
            // returned indices.
            self.string_dedup
                .entry((*s).to_string())
                .or_insert(self.strings.len() as u32 - 1);
        }
        start
    }

    /// Add a level to the level pool. Returns its index.
    ///
    /// Hash-conses: if an identical level (same tag + data bytes) was
    /// already added, returns the existing index.
    pub fn add_level(&mut self, level: FlatLevel) -> u32 {
        self.total_level_adds += 1;
        let key = level_to_bytes(&level);
        if let Some(&idx) = self.level_dedup.get(&key) {
            return idx;
        }
        let idx = self.levels.len() as u32;
        self.levels.push(level);
        self.level_dedup.insert(key, idx);
        idx
    }

    /// Add an expression to the arena. Returns its index.
    ///
    /// Hash-conses: if an identical expression (same tag + flags + data
    /// bytes) was already added, returns the existing index.
    pub fn add_expr(&mut self, expr: FlatExpr) -> u32 {
        self.total_expr_adds += 1;
        let key = expr_to_bytes(&expr);
        if let Some(&idx) = self.expr_dedup.get(&key) {
            return idx;
        }
        let idx = self.exprs.len() as u32;
        self.exprs.push(expr);
        self.expr_dedup.insert(key, idx);
        idx
    }

    /// Add a level list to the level_lists table. Returns the starting offset
    /// (as a u32 index into the `level_lists` array, i.e., number of u32 entries
    /// before this list).
    ///
    /// `level_indices` are indices into the level pool (as returned by `add_level`).
    /// An empty list returns `u32::MAX` (no levels sentinel).
    ///
    /// Deduplicates: if an identical list was already added, returns the existing offset.
    pub fn add_level_list(&mut self, level_indices: &[u32]) -> u32 {
        if level_indices.is_empty() {
            return u32::MAX;
        }
        // Check dedup
        let key: Vec<u32> = level_indices.to_vec();
        if let Some(&offset) = self.level_list_dedup.get(&key) {
            return offset;
        }
        let offset = self.level_lists.len() as u32;
        self.level_lists.push(level_indices.len() as u32);
        self.level_lists.extend_from_slice(level_indices);
        self.level_list_dedup.insert(key, offset);
        offset
    }

    /// Number of constant headers added so far.
    #[must_use]
    pub fn constants_len(&self) -> usize {
        self.constants.len()
    }

    /// Add a constant header. Returns its index.
    pub fn add_constant(&mut self, header: MathverseConstantHeader) -> u32 {
        let idx = self.constants.len() as u32;
        self.constants.push(header);
        idx
    }

    /// Set the provenance sidecar (raw bytes, will be zstd compressed).
    pub fn set_provenance(&mut self, data: Vec<u8>) {
        self.provenance = data;
    }

    /// Set the provenance-sidecar link fields (`provenance_idx`,
    /// `sidecar_digest`) on an already-added constant header.
    ///
    /// Used by writers that add constants first (e.g. through
    /// `KernelShardBuilder::add_declaration`) and attach per-constant
    /// [`crate::provenance::ProvenanceRecord`]s afterwards. Returns `false`
    /// when `idx` does not name an existing constant.
    pub fn set_constant_provenance(
        &mut self,
        idx: u32,
        provenance_idx: u32,
        sidecar_digest: u32,
    ) -> bool {
        match self.constants.get_mut(idx as usize) {
            Some(constant) => {
                constant.provenance_idx = provenance_idx;
                constant.sidecar_digest = sidecar_digest;
                true
            }
            None => false,
        }
    }

    /// Record an already-added constant's kernel `Reducibility` in its header's
    /// reserved `_pad2` bytes (12..17), so the lazy loader serves a constant with
    /// the EXACT reducibility the eager olean import assigned — required for
    /// δ-unfold parity (a `@[reducible]` def served as `Regular(0)` reduces
    /// differently in is_def_eq). Encoding (backward compatible: legacy shards
    /// leave these bytes 0, decoded as "unset" → caller falls back to the
    /// decl_kind heuristic):
    ///   `_pad2[12]`: 0 = unset; else 0x80 | tag, tag ∈ {0=Reducible,
    ///                1=Regular, 2=Irreducible, 3=Opaque}
    ///   `_pad2[13..17]`: Regular height (u32 LE), else 0
    pub fn set_constant_reducibility(
        &mut self,
        idx: u32,
        reducibility: clean_kernel::env::Reducibility,
    ) -> bool {
        use clean_kernel::env::Reducibility;
        let (tag, height) = match reducibility {
            Reducibility::Reducible => (0u8, 0u32),
            Reducibility::Regular(h) => (1u8, h),
            Reducibility::Irreducible => (2u8, 0u32),
            Reducibility::Opaque => (3u8, 0u32),
        };
        match self.constants.get_mut(idx as usize) {
            Some(constant) => {
                constant._pad2[12] = 0x80 | tag;
                constant._pad2[13..17].copy_from_slice(&height.to_le_bytes());
                true
            }
            None => false,
        }
    }

    /// Record an already-added constant's Lean `DefinitionSafety` (`safe` /
    /// `unsafe` / `partial`) in its header's reserved `_pad2` byte 25, so
    /// replay/verification can distinguish Lean `unsafe def`s (recursive, no
    /// termination proof — they can never carry proof-grade trust) from
    /// ordinary safe definitions. Encoding (backward compatible: legacy shards
    /// leave the byte 0, decoded as "unset" ⇒ safe — today's behavior):
    ///   `_pad2[25]`: 0 = unset; else 0x80 | tag, tag ∈ {0=safe, 1=unsafe,
    ///                2=partial}
    /// See `MathverseConstantHeader::definition_safety` /
    /// `::set_definition_safety` (the header definition in `types.rs`).
    /// Returns `false` when `idx` does not name an existing constant.
    pub fn set_constant_definition_safety(
        &mut self,
        idx: u32,
        safety: clean_olean::DefinitionSafety,
    ) -> bool {
        match self.constants.get_mut(idx as usize) {
            Some(constant) => {
                constant.set_definition_safety(safety);
                true
            }
            None => false,
        }
    }

    /// Override the `axiom_profile` of an already-added constant header.
    ///
    /// Used by the graduation intake gate
    /// ([`crate::graduate::intake::graduate`]): `KernelShardBuilder::add_declaration`
    /// stamps name-heuristic content bits (`FLOAT_APPROX | NN_ABSTRACTION` for
    /// `NNVerify.*`-prefixed names) into the profile, but a graduated theorem's
    /// profile must carry the *gate-derived* axiom facts — the gate just
    /// re-earned a foundational-only closure, so the honest in-shard profile is
    /// `AxiomProfile::NONE` (anything else trips the cake gate's
    /// `NonEmptyAxiomProfile` clause). Call before
    /// [`Self::finalize_axiom_profiles`] so stale heuristic bits cannot
    /// propagate through in-shard dependencies. Returns `false` when `idx`
    /// does not name an existing constant.
    pub fn set_constant_axiom_profile(&mut self, idx: u32, profile: AxiomProfile) -> bool {
        match self.constants.get_mut(idx as usize) {
            Some(constant) => {
                constant.axiom_profile = profile;
                true
            }
            None => false,
        }
    }

    /// Close the axiom profiles of every constant under the shard's dependency
    /// graph, in place.
    ///
    /// The per-constant importers record only a constant's *local* axiom usage
    /// (it is itself a named axiom, or an `Axiom`/`Opaque` kind). They do not
    /// look through dependencies, so a theorem that uses `Classical.choice`
    /// transitively would otherwise be written with `AxiomProfile::NONE` — i.e.
    /// reported as kernel-pure when it is not. Calling this once after all
    /// constants have been added (and before [`Self::write`]) computes the real
    /// transitive closure from the flat expression arena so each header's
    /// `axiom_profile` honestly reflects every axiom reachable through any depth
    /// of in-shard dependency.
    ///
    /// Cross-shard dependencies (names not defined in this shard) are not
    /// resolvable here and are left to a cross-shard closure pass; within a
    /// single shard the result is exact.
    ///
    /// Returns the number of constants whose profile gained at least one bit.
    pub fn finalize_axiom_profiles(&mut self) -> usize {
        crate::lean4::olean::axiom_profile::propagate_shard_axiom_profiles(
            &mut self.constants,
            &self.exprs,
            &self.strings,
        )
    }

    /// Collect, for every constant in this writer, its declared name, its
    /// current (already in-shard-closed) axiom profile, and the names of every
    /// constant it references through its type/value expression trees.
    ///
    /// This is the read side of the *cross-shard* closure
    /// ([`crate::lean4::olean::axiom_profile::propagate_cross_shard_axiom_profiles`]):
    /// the library-level pass calls it on each writer to build one global
    /// `name -> AxiomProfile` map and one global `name -> Vec<dep name>` graph,
    /// then iterates a fixed-point that resolves the by-name dependencies whose
    /// defining constant lives in a *different* shard. Those cross-shard names
    /// are necessarily skipped by [`Self::finalize_axiom_profiles`], because the
    /// within-shard pass only sees `name_idx` values local to this shard.
    ///
    /// Dependency names are returned as owned `String`s — they are matched by
    /// name across shards, where per-shard `name_idx` values are not comparable.
    /// A constant whose `name_idx` is out of range (should not happen for a
    /// well-formed writer) is reported with an empty name and is effectively
    /// skipped by the cross-shard merge.
    pub(crate) fn constant_axiom_dep_names(&self) -> Vec<ConstantAxiomDeps> {
        let mut out = Vec::with_capacity(self.constants.len());
        for c in &self.constants {
            let name = self
                .strings
                .get(c.name_idx as usize)
                .cloned()
                .unwrap_or_default();

            // Gather dependency name indices from both the type and value trees.
            let mut dep_name_indices: Vec<u32> =
                crate::lean4::olean::alpha::extract_deps(&self.exprs, c.type_idx);
            if c.has_value() {
                dep_name_indices.extend(crate::lean4::olean::alpha::extract_deps(
                    &self.exprs,
                    c.value_idx,
                ));
            }
            dep_name_indices.sort_unstable();
            dep_name_indices.dedup();

            let dep_names: Vec<String> = dep_name_indices
                .iter()
                .filter_map(|&ni| self.strings.get(ni as usize).cloned())
                .filter(|n| !n.is_empty())
                .collect();

            out.push(ConstantAxiomDeps {
                name,
                profile: c.axiom_profile,
                dep_names,
            });
        }
        out
    }

    /// Union an externally-computed axiom profile into each constant whose name
    /// appears in `closed`, in place.
    ///
    /// This is the write side of the cross-shard closure: after the library-level
    /// fixed-point produces the globally-closed `name -> AxiomProfile` map, each
    /// writer is updated so its serialized headers carry every axiom reachable
    /// through dependencies in *other* shards as well as this one. Bits are only
    /// ever added (monotone union), so applying a superset map can never drop a
    /// bit a constant already had. Returns the number of constants whose profile
    /// gained at least one bit.
    pub(crate) fn apply_closed_axiom_profiles(
        &mut self,
        closed: &std::collections::HashMap<String, AxiomProfile>,
    ) -> usize {
        let mut upgraded = 0usize;
        for c in &mut self.constants {
            let Some(name) = self.strings.get(c.name_idx as usize) else {
                continue;
            };
            if let Some(&global) = closed.get(name) {
                let before = c.axiom_profile;
                c.axiom_profile |= global;
                if c.axiom_profile != before {
                    upgraded += 1;
                }
            }
        }
        upgraded
    }

    /// Number of unique expressions in the arena (post-dedup).
    pub fn expr_count(&self) -> usize {
        self.exprs.len()
    }

    /// Number of unique strings in the arena (post-dedup).
    pub fn string_count(&self) -> usize {
        self.strings.len()
    }

    /// Number of constants written so far.
    pub fn constant_count(&self) -> usize {
        self.constants.len()
    }

    /// Read back a string by index (test/audit helper).
    pub fn string_at(&self, idx: u32) -> &str {
        &self.strings[idx as usize]
    }

    /// Read back an expression by arena index, or `None` if out of range
    /// (test/audit helper for inspecting emitted `FlatExpr` trees).
    pub(crate) fn expr_at(&self, idx: u32) -> Option<FlatExpr> {
        self.exprs.get(idx as usize).copied()
    }

    /// Return deduplication statistics for this writer.
    ///
    /// `strings` and `levels` are pre-seeded with a sentinel (empty
    /// string at index 0, zero level at index 0). Those sentinels
    /// were NOT added via `add_string` / `add_level`, so they don't
    /// count toward the unique-additions tally — subtract them out
    /// before computing `deduped = total - unique`. Without this
    /// correction, an empty writer would underflow (`0u64 - 1u64`).
    pub fn dedup_stats(&self) -> DedupStats {
        let strings_unique = (self.strings.len() as u64).saturating_sub(1);
        let levels_unique = (self.levels.len() as u64).saturating_sub(1);
        DedupStats {
            exprs_total: self.total_expr_adds,
            exprs_deduped: self.total_expr_adds.saturating_sub(self.exprs.len() as u64),
            levels_total: self.total_level_adds,
            levels_deduped: self.total_level_adds.saturating_sub(levels_unique),
            strings_total: self.total_string_adds,
            strings_deduped: self.total_string_adds.saturating_sub(strings_unique),
        }
    }

    /// Rebuild a writer holding the *verbatim* contents of an already-decoded
    /// [`ShardReader`].
    ///
    /// Within one shard every `name_idx` / `type_idx` / `value_idx` /
    /// `levels_list_idx` is self-consistent against that shard's own arenas, so a
    /// byte-faithful copy needs **no** re-interning or index remapping: the
    /// string table (index 0 = empty sentinel), level pool (index 0 =
    /// `FlatLevel::zero()`), expression arena, constant headers, level-lists
    /// table, and provenance sidecar are carried over as-is. The hash-consing
    /// dedup caches are intentionally left empty; they are only consulted by the
    /// `add_*` interners, which a verbatim rewrite never calls. Re-serializing
    /// this writer reproduces the same logical shard (bloom filter and sorted
    /// name index are rebuilt deterministically in [`Self::write`]).
    ///
    /// This is the foundation of the destructive `KernelVerified` stamp pass:
    /// callers copy a shard, flip selected `import_confidence` bytes, and write
    /// the result back over the original file.
    #[must_use]
    pub fn from_reader(reader: &ShardReader) -> Self {
        // SOUNDNESS (restamp threading, Step 4): the KV-stamp/restamp path copies
        // a shard through `from_reader` -> `write`. If the v3 closure-binding
        // fields were dropped here, restamping a closure shard would zero
        // fail_closed_verified/source hash/module and silently disable lazy
        // serving (a 101.7x -> 1x regression). Carry them across so a restamp
        // preserves the binding. The module name is recovered from the source
        // header's `module_name_idx` via the reader's OWN string table.
        let source_olean_blake3 = if reader.header.version >= SHARD_VERSION
            && reader.header.source_olean_blake3 != [0u8; 32]
        {
            Some(reader.header.source_olean_blake3)
        } else {
            None
        };
        let module_name =
            if reader.header.version >= SHARD_VERSION && reader.header.module_name_idx != 0 {
                reader
                    .strings
                    .get(reader.header.module_name_idx as usize)
                    .cloned()
            } else {
                None
            };
        Self {
            strings: reader.strings.clone(),
            levels: reader.levels.clone(),
            exprs: reader.exprs.clone(),
            constants: reader.constants.clone(),
            provenance: reader.provenance.clone(),
            level_lists: reader.level_lists.clone(),
            level_list_dedup: hashbrown::HashMap::new(),
            expr_dedup: hashbrown::HashMap::new(),
            level_dedup: hashbrown::HashMap::new(),
            string_dedup: hashbrown::HashMap::new(),
            total_expr_adds: 0,
            total_level_adds: 0,
            total_string_adds: 0,
            source_olean_blake3,
            source_olean_len: reader.header.source_olean_len,
            fail_closed_verified: reader.header.fail_closed_verified == 1,
            module_name,
        }
    }

    /// Stamp the persisted `import_confidence` byte of every constant whose name
    /// appears in `verified_names` to [`ImportConfidence::KernelVerified`].
    ///
    /// This is the in-writer half of the on-disk stamp: it mutates the header
    /// bytes that [`Self::write`] serializes, so the change survives to the
    /// shard file (unlike the in-memory-only library upgrade). Only names that
    /// (a) exist in this shard and (b) are not already `KernelVerified` are
    /// counted. Returns the number of headers raised.
    ///
    /// SOUNDNESS: the caller is responsible for supplying *only* names whose
    /// value genuinely passed the Clean kernel's `check_type`
    /// (`verify_corpus_incremental` -> `kernel_verified_names`). This method does
    /// not itself re-verify; it is a faithful persistence primitive.
    pub fn stamp_kernel_verified(
        &mut self,
        verified_names: &std::collections::HashSet<String>,
    ) -> usize {
        let target = crate::types::ImportConfidence::KernelVerified as u8;
        let mut upgraded = 0usize;
        for constant in &mut self.constants {
            let name = match self.strings.get(constant.name_idx as usize) {
                Some(name) => name.as_str(),
                None => continue,
            };
            if verified_names.contains(name) && constant.import_confidence != target {
                constant.import_confidence = target;
                upgraded += 1;
            }
        }
        upgraded
    }

    /// Write the shard to a file.
    pub fn write_to_file(&self, path: impl AsRef<Path>) -> MathverseResult<()> {
        let file = std::fs::File::create(path)?;
        let mut writer = std::io::BufWriter::new(file);
        self.write(&mut writer)
    }

    /// Build the sorted name index from constants + string table.
    ///
    /// Why: each `MathverseConstantHeader::name_idx` is a u32 index into
    /// `self.strings`. Earlier this method indexed the string table
    /// unconditionally (`self.strings[c.name_idx as usize]`), which
    /// panicked with "index out of bounds" whenever an upstream importer
    /// added a constant whose `name_idx` had not actually been interned
    /// (e.g. a header copied verbatim from another writer's namespace,
    /// or a `level_params_count > 0` truncated cast leaving `name_idx`
    /// at a stale `u32::MAX`). Surface that as a typed
    /// [`MathverseError::StringOutOfRange`] instead of aborting the entire
    /// `build-library` pipeline. The error names the offending constant
    /// index via [`MathverseError::ForConstant`] so callers can pinpoint
    /// which import produced the bad header.
    fn build_sorted_index(&self) -> MathverseResult<Vec<NameIndexEntry>> {
        let string_count = self.strings.len();
        let mut entries: Vec<NameIndexEntry> = Vec::with_capacity(self.constants.len());
        for (i, c) in self.constants.iter().enumerate() {
            let idx = c.name_idx as usize;
            if idx >= string_count {
                return Err(MathverseError::ForConstant {
                    inner: Box::new(MathverseError::StringOutOfRange {
                        idx: c.name_idx,
                        count: string_count as u32,
                    }),
                    constant_name: format!("constant #{i}"),
                });
            }
            let name = &self.strings[idx];
            entries.push(NameIndexEntry {
                name_hash: name_hash(name),
                constant_idx: i as u32,
            });
        }
        entries.sort_unstable_by_key(|e| e.name_hash);
        Ok(entries)
    }

    /// Write the shard to any writer.
    pub fn write(&self, w: &mut impl Write) -> MathverseResult<()> {
        let mut hasher = blake3::Hasher::new();

        // v3 closure binding: intern the declaring module name into the string
        // table (if any) so the loader can read it back via `module_name_idx`.
        // `write` is `&self`, so build an effective string table that appends the
        // module name only when it is not already interned. `module_name_idx == 0`
        // (the empty-string sentinel slot) means "no bound module".
        let (effective_strings, module_name_idx): (std::borrow::Cow<'_, [String]>, u32) =
            match &self.module_name {
                Some(name) => match self.strings.iter().position(|s| s == name) {
                    Some(idx) => (std::borrow::Cow::Borrowed(&self.strings), idx as u32),
                    None => {
                        let mut owned = self.strings.clone();
                        let idx = owned.len() as u32;
                        owned.push(name.clone());
                        (std::borrow::Cow::Owned(owned), idx)
                    }
                },
                None => (std::borrow::Cow::Borrowed(&self.strings), 0),
            };

        // Encode string table
        let string_data = encode_string_table(&effective_strings);
        let string_compressed = zstd::bulk::compress(&string_data, 3)?;

        // Encode provenance
        let provenance_compressed = if self.provenance.is_empty() {
            Vec::new()
        } else {
            zstd::bulk::compress(&self.provenance, 3)?
        };

        // Build bloom filter for name lookup
        let bloom = build_bloom_filter(&effective_strings, BLOOM_SIZE);

        // Build sorted name index for O(log n) lookup
        let sorted_index = self.build_sorted_index()?;
        let sorted_index_bytes_len = sorted_index.len() * SORTED_INDEX_ENTRY_SIZE;

        // Write header
        let header = ShardHeader {
            magic: SHARD_MAGIC,
            version: SHARD_VERSION,
            flags: FLAG_HAS_SORTED_INDEX,
            string_count: effective_strings.len() as u32,
            string_data_len: string_compressed.len() as u32,
            level_count: self.levels.len() as u32,
            expr_count: self.exprs.len() as u32,
            constant_count: self.constants.len() as u32,
            bloom_size: bloom.len() as u32,
            provenance_len: provenance_compressed.len() as u32,
            sorted_index_len: sorted_index_bytes_len as u32,
            level_lists_count: self.level_lists.len() as u32,
            source_olean_blake3: self.source_olean_blake3.unwrap_or([0u8; 32]),
            source_olean_len: self.source_olean_len,
            fail_closed_verified: u32::from(self.fail_closed_verified),
            module_name_idx,
        };
        let header_bytes = header.to_bytes();
        w.write_all(&header_bytes)?;
        hasher.update(&header_bytes);

        // Write string table (compressed)
        w.write_all(&string_compressed)?;
        hasher.update(&string_compressed);

        // Write level pool (raw)
        for level in &self.levels {
            let bytes = level_to_bytes(level);
            w.write_all(&bytes)?;
            hasher.update(&bytes);
        }

        // Write FlatExpr arena (raw)
        for expr in &self.exprs {
            // SAFETY: FlatExpr is #[repr(C, align(16))] with no padding semantics
            // issues — we serialize field-by-field to avoid UB from reading padding.
            let bytes = expr_to_bytes(expr);
            w.write_all(&bytes)?;
            hasher.update(&bytes);
        }

        // Write constant headers (raw)
        for constant in &self.constants {
            let bytes = constant.to_bytes();
            w.write_all(&bytes)?;
            hasher.update(&bytes);
        }

        // Write level_lists table (raw u32 array)
        for &entry in &self.level_lists {
            let bytes = entry.to_le_bytes();
            w.write_all(&bytes)?;
            hasher.update(&bytes);
        }

        // Write bloom filter
        w.write_all(&bloom)?;
        hasher.update(&bloom);

        // Write sorted name index
        for entry in &sorted_index {
            let bytes = entry.to_bytes();
            w.write_all(&bytes)?;
            hasher.update(&bytes);
        }

        // Write provenance (compressed)
        w.write_all(&provenance_compressed)?;
        hasher.update(&provenance_compressed);

        // Write footer
        let hash = hasher.finalize();
        let mut footer = [0u8; FOOTER_SIZE];
        footer[0..32].copy_from_slice(hash.as_bytes());
        w.write_all(&footer)?;

        Ok(())
    }
}

impl Default for ShardWriter {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// ShardReader
// ---------------------------------------------------------------------------

/// Reader for `.mathverse` shard files.
pub struct ShardReader {
    pub header: ShardHeader,
    pub strings: Vec<String>,
    pub levels: Vec<FlatLevel>,
    pub exprs: Vec<FlatExpr>,
    pub constants: Vec<MathverseConstantHeader>,
    /// Level lists table (v2+): `[count, idx_0, ..., idx_N, count, ...]`.
    /// Each entry starts with a count followed by that many level pool indices.
    pub level_lists: Vec<u32>,
    pub bloom: Vec<u8>,
    pub provenance: Vec<u8>,
    /// Sorted name index for O(log n) lookup. Empty if the shard was written
    /// without the `FLAG_HAS_SORTED_INDEX` flag (backward compatibility).
    sorted_index: Vec<NameIndexEntry>,
}

impl ShardReader {
    /// Read a shard from a file.
    ///
    /// Errors carry the shard path: an unreadable file is
    /// [`MathverseError::ShardFileUnreadable`] (with the fetch/rebuild
    /// remediation), and any parse/checksum failure from
    /// [`Self::from_bytes`] is wrapped with the file path as context so a
    /// multi-shard load names which shard is corrupt.
    pub fn from_file(path: impl AsRef<Path>) -> MathverseResult<Self> {
        let path = path.as_ref();
        let data = std::fs::read(path).map_err(|source| MathverseError::ShardFileUnreadable {
            path: path.display().to_string(),
            source,
        })?;
        Self::from_bytes(&data)
            .map_err(|e| e.with_context(&format!("shard file `{}`", path.display())))
    }

    /// Read a shard from a byte slice.
    pub fn from_bytes(data: &[u8]) -> MathverseResult<Self> {
        if data.len() < HEADER_SIZE + FOOTER_SIZE {
            return Err(MathverseError::Truncated {
                expected: HEADER_SIZE + FOOTER_SIZE,
                got: data.len(),
            });
        }

        // Parse header
        let header_bytes: &[u8; HEADER_SIZE] =
            data[..HEADER_SIZE]
                .try_into()
                .map_err(|_| MathverseError::Truncated {
                    expected: HEADER_SIZE,
                    got: data.len(),
                })?;
        let header = ShardHeader::from_bytes(header_bytes)?;

        // Verify checksum
        let footer_start = data.len() - FOOTER_SIZE;
        let content = &data[..footer_start];
        let expected_hash = &data[footer_start..footer_start + 32];
        let actual_hash = blake3::hash(content);
        if actual_hash.as_bytes() != expected_hash {
            return Err(MathverseError::ChecksumMismatch {
                expected: hex::encode(expected_hash),
                got: hex::encode(actual_hash.as_bytes()),
            });
        }

        // Compute and validate section bounds before slicing. This mirrors the
        // mmap reader path and keeps malformed-but-rehashed artifacts from
        // panicking in the in-memory reader used by native gate verification.
        let checked_add = |base: usize, len: usize| -> MathverseResult<usize> {
            base.checked_add(len).ok_or(MathverseError::Truncated {
                expected: usize::MAX,
                got: data.len(),
            })
        };
        let checked_mul = |count: u32, size: usize| -> MathverseResult<usize> {
            (count as usize)
                .checked_mul(size)
                .ok_or(MathverseError::Truncated {
                    expected: usize::MAX,
                    got: data.len(),
                })
        };

        let string_start = HEADER_SIZE;
        let string_end = checked_add(string_start, header.string_data_len as usize)?;
        let level_byte_count = checked_mul(header.level_count, FlatLevel::SIZE)?;
        let level_end = checked_add(string_end, level_byte_count)?;
        let expr_byte_count = checked_mul(header.expr_count, FlatExpr::SIZE)?;
        let expr_end = checked_add(level_end, expr_byte_count)?;
        let const_header_size = header.constant_header_size();
        let const_byte_count = checked_mul(header.constant_count, const_header_size)?;
        let constant_end = checked_add(expr_end, const_byte_count)?;
        let level_lists_byte_count = checked_mul(header.level_lists_count, 4)?;
        let level_lists_end = checked_add(constant_end, level_lists_byte_count)?;
        let bloom_end = checked_add(level_lists_end, header.bloom_size as usize)?;
        let sorted_index_len = if header.has_sorted_index() {
            header.sorted_index_len as usize
        } else {
            0
        };
        validate_sorted_index_len(sorted_index_len, "<memory>")?;
        let sorted_index_end = checked_add(bloom_end, sorted_index_len)?;
        let provenance_end = checked_add(sorted_index_end, header.provenance_len as usize)?;
        if provenance_end != footer_start {
            if provenance_end > footer_start {
                return Err(MathverseError::Truncated {
                    expected: checked_add(provenance_end, FOOTER_SIZE)?,
                    got: data.len(),
                });
            }
            return Err(MathverseError::ShardCorrupt {
                path: "<memory>".to_string(),
                reason: format!(
                    "section layout ended at byte {provenance_end}, before footer at byte {footer_start}"
                ),
            });
        }

        // String table (compressed)
        let string_decompressed =
            zstd::bulk::decompress(&data[string_start..string_end], max_decompress_bytes())?;
        let strings = decode_string_table(&string_decompressed, header.string_count)?;
        let mut offset = string_end;

        // Level pool
        let levels = decode_levels(&data[offset..offset + level_byte_count], header.level_count)?;
        validate_level_pool(&levels, strings.len())?;
        offset += level_byte_count;

        // FlatExpr arena
        let exprs = decode_exprs(&data[offset..offset + expr_byte_count], header.expr_count)?;
        validate_expr_arena(&exprs, &levels, &header, strings.len())?;
        offset += expr_byte_count;

        // Constant headers
        let constants = decode_constants(
            &data[offset..offset + const_byte_count],
            header.constant_count,
            header.is_legacy(),
        )?;
        validate_constant_headers(&constants, &header, &strings)?;
        offset += const_byte_count;

        // Level lists table (v2+)
        let level_lists = if header.level_lists_count > 0 {
            let ll_byte_count = header.level_lists_count as usize * 4;
            let mut ll = Vec::with_capacity(header.level_lists_count as usize);
            for i in 0..header.level_lists_count as usize {
                let base = offset + i * 4;
                ll.push(u32::from_le_bytes([
                    data[base],
                    data[base + 1],
                    data[base + 2],
                    data[base + 3],
                ]));
            }
            offset += ll_byte_count;
            ll
        } else {
            Vec::new()
        };
        validate_level_lists(&level_lists, &header)?;

        // Bloom filter
        let bloom_size = header.bloom_size as usize;
        let bloom = data[offset..offset + bloom_size].to_vec();
        offset += bloom_size;

        // Sorted name index + provenance + assemble
        let (sorted_index, offset) =
            decode_sorted_index(data, offset, &header, &constants, &strings)?;
        let raw_provenance = decode_provenance(data, offset, &header)?;
        // The provenance sidecar is OPTIONAL cold-path metadata (notes,
        // source_file, cross_refs) fully separate from each constant's stored
        // trust label (`import_confidence` in the constant header). If it cannot
        // be decoded or fails digest verification — e.g. a sidecar written with
        // the pre-migration bincode 1.x encoding that even the legacy fallback
        // cannot recover, or genuine drift — we degrade gracefully: keep every
        // declaration and its trust label, and report provenance as unavailable
        // (empty) rather than rejecting the whole shard. No decl or trust label
        // is fabricated or altered.
        let provenance = match validate_provenance_headers(&constants, &raw_provenance) {
            Ok(()) => raw_provenance,
            Err(_) => Vec::new(),
        };

        Ok(Self {
            header,
            strings,
            levels,
            exprs,
            constants,
            level_lists,
            bloom,
            provenance,
            sorted_index,
        })
    }

    /// Check if a name might exist in this shard (bloom filter check).
    /// False positives possible, false negatives impossible.
    pub fn bloom_maybe_contains(&self, name: &str) -> bool {
        bloom_check(&self.bloom, name)
    }

    /// Look up a constant by name.
    ///
    /// Uses bloom filter as a fast pre-check, then:
    /// - If a sorted name index is present: O(log n) binary search on the
    ///   blake3-truncated u64 hash, with string comparison to handle collisions.
    /// - Otherwise (legacy shards): O(n) linear scan fallback.
    pub fn lookup_name(&self, name: &str) -> Option<(u32, &MathverseConstantHeader)> {
        if !self.bloom_maybe_contains(name) {
            return None;
        }
        if !self.sorted_index.is_empty() {
            self.lookup_name_indexed(name)
        } else {
            self.lookup_name_linear(name)
        }
    }

    /// Return ALL matching constants for a given name (for cross-shard dedup).
    ///
    /// Uses bloom filter pre-check, then indexed or linear scan.
    pub fn lookup_name_all(&self, name: &str) -> Vec<(u32, &MathverseConstantHeader)> {
        if !self.bloom_maybe_contains(name) {
            return Vec::new();
        }
        if !self.sorted_index.is_empty() {
            self.lookup_name_all_indexed(name)
        } else {
            self.lookup_name_all_linear(name)
        }
    }

    /// O(log n) lookup via sorted name index. Returns first match.
    fn lookup_name_indexed(&self, name: &str) -> Option<(u32, &MathverseConstantHeader)> {
        let target_hash = name_hash(name);
        let pos = self
            .sorted_index
            .partition_point(|e| e.name_hash < target_hash);
        for entry in self.sorted_index[pos..].iter() {
            if entry.name_hash != target_hash {
                break;
            }
            let ci = entry.constant_idx as usize;
            if ci < self.constants.len() {
                let constant = &self.constants[ci];
                let name_idx = constant.name_idx as usize;
                if name_idx < self.strings.len() && self.strings[name_idx] == name {
                    return Some((entry.constant_idx, constant));
                }
            }
        }
        None
    }

    /// O(log n + k) lookup returning all matches for cross-shard dedup.
    fn lookup_name_all_indexed(&self, name: &str) -> Vec<(u32, &MathverseConstantHeader)> {
        let target_hash = name_hash(name);
        let mut results = Vec::new();
        let pos = self
            .sorted_index
            .partition_point(|e| e.name_hash < target_hash);
        for entry in self.sorted_index[pos..].iter() {
            if entry.name_hash != target_hash {
                break;
            }
            let ci = entry.constant_idx as usize;
            if ci < self.constants.len() {
                let constant = &self.constants[ci];
                let name_idx = constant.name_idx as usize;
                if name_idx < self.strings.len() && self.strings[name_idx] == name {
                    results.push((entry.constant_idx, constant));
                }
            }
        }
        results
    }

    /// O(n) linear scan fallback for legacy shards without sorted index.
    fn lookup_name_linear(&self, name: &str) -> Option<(u32, &MathverseConstantHeader)> {
        for (i, constant) in self.constants.iter().enumerate() {
            let idx = constant.name_idx as usize;
            if idx < self.strings.len() && self.strings[idx] == name {
                return Some((i as u32, constant));
            }
        }
        None
    }

    /// O(n) linear scan returning all matches (legacy fallback).
    fn lookup_name_all_linear(&self, name: &str) -> Vec<(u32, &MathverseConstantHeader)> {
        let mut results = Vec::new();
        for (i, constant) in self.constants.iter().enumerate() {
            let idx = constant.name_idx as usize;
            if idx < self.strings.len() && self.strings[idx] == name {
                results.push((i as u32, constant));
            }
        }
        results
    }

    /// Returns true if this shard has a sorted name index for O(log n) lookup.
    pub fn has_sorted_index(&self) -> bool {
        !self.sorted_index.is_empty()
    }

    /// Build an in-memory reader directly from already-decoded, index-consistent
    /// arena parts (no serialization round-trip, no checksum).
    ///
    /// This backs the global corpus verifier, which has already merged every
    /// shard's strings/levels/exprs/constants/level_lists into one set of
    /// arenas (with all indices remapped to be mutually consistent) inside
    /// `MathverseLibrary`. Wrapping those merged arenas as a `ShardReader` lets
    /// the inductive-family replay logic — which scans sibling constants to
    /// assemble a checked `InductiveDecl` — run corpus-wide without duplicating
    /// it. A synthetic header is derived from the slice lengths; the bloom
    /// filter and sorted name index are intentionally empty because the
    /// reconstruction/replay path never consults them.
    pub(crate) fn from_merged_parts(
        strings: Vec<String>,
        levels: Vec<FlatLevel>,
        exprs: Vec<FlatExpr>,
        constants: Vec<MathverseConstantHeader>,
        level_lists: Vec<u32>,
    ) -> Self {
        let header = ShardHeader {
            magic: SHARD_MAGIC,
            version: SHARD_VERSION,
            flags: 0,
            string_count: strings.len() as u32,
            string_data_len: 0,
            level_count: levels.len() as u32,
            expr_count: exprs.len() as u32,
            constant_count: constants.len() as u32,
            bloom_size: 0,
            provenance_len: 0,
            sorted_index_len: 0,
            level_lists_count: level_lists.len() as u32,
            // SOUNDNESS: a merged synthetic reader has NO backing source olean,
            // so it leaves the v3 binding fields zero. The loader's predicate
            // (`source_olean_blake3 != [0;32] && fail_closed_verified == 1`)
            // SKIPS it — it can never be marked verified, hence never lazily
            // served unbound.
            source_olean_blake3: [0u8; 32],
            source_olean_len: 0,
            fail_closed_verified: 0,
            module_name_idx: 0,
        };
        Self {
            header,
            strings,
            levels,
            exprs,
            constants,
            level_lists,
            bloom: Vec::new(),
            provenance: Vec::new(),
            sorted_index: Vec::new(),
        }
    }
}

// ---------------------------------------------------------------------------
// ShardMmapReader
// ---------------------------------------------------------------------------

/// Section byte offsets within the mmap'd file.
///
/// Computed once from the header, then used for zero-copy slice access into
/// the level pool, expr arena, and constant headers sections.
#[derive(Clone, Debug)]
pub(crate) struct SectionOffsets {
    pub(crate) level_start: usize,
    pub(crate) level_end: usize,
    pub(crate) expr_start: usize,
    pub(crate) expr_end: usize,
    pub(crate) constant_start: usize,
    pub(crate) constant_end: usize,
    pub(crate) level_lists_start: usize,
    pub(crate) level_lists_end: usize,
    pub(crate) bloom_start: usize,
    pub(crate) bloom_end: usize,
}

/// Zero-copy reader for `.mathverse` shard files via `mmap`.
///
/// Parses the header and decompresses the string table eagerly, then provides
/// direct byte-slice access into the raw level pool, expr arena, and constant
/// headers sections without copying them into `Vec`s.
pub struct ShardMmapReader {
    /// The underlying memory mapping (kept alive to back the raw slices).
    mmap: Mmap,
    /// Parsed header.
    pub header: ShardHeader,
    /// Decompressed string table (eagerly loaded — strings are zstd-compressed).
    pub strings: Vec<String>,
    /// Pre-computed byte offsets for raw sections.
    offsets: SectionOffsets,
    /// Eagerly-decoded SMALL sections, populated only by [`Self::open_lazy`]
    /// (empty for [`Self::open`]). The level pool, level-lists table, and
    /// constant headers are tiny relative to the expr arena (the OOM driver),
    /// and the lazy closure source needs them up front (levels per fold, the
    /// name→idx index over constants). Keeping them owned avoids re-decoding per
    /// constant while leaving the bulk expr arena demand-paged through the mmap.
    pub levels: Vec<FlatLevel>,
    pub level_lists: Vec<u32>,
    pub constants: Vec<MathverseConstantHeader>,
    /// This shard's DECLARING module name, decoded from `header.module_name_idx`
    /// via the shard's OWN string table (v3; `None` for v1/v2 and for a shard
    /// whose `module_name_idx == 0`). SOUNDNESS: comes from the shard's own
    /// header, so a forged file cannot launder a foreign constant under a benign
    /// FILE name — the loader resolves the olean for THIS module.
    pub source_module: Option<String>,
}

/// Decode a v3 shard's declaring module name from `header.module_name_idx` via
/// its OWN string table. Returns `None` for pre-v3 headers, a zero index (the
/// empty-string sentinel slot = "no bound module"), or an out-of-range index.
fn decode_source_module(header: &ShardHeader, strings: &[String]) -> Option<String> {
    if header.version < SHARD_VERSION || header.module_name_idx == 0 {
        return None;
    }
    strings
        .get(header.module_name_idx as usize)
        .filter(|s| !s.is_empty())
        .cloned()
}

impl ShardMmapReader {
    /// Open a shard file via mmap.
    ///
    /// Validates the header and checksum, decompresses the string table, then
    /// holds the mmap for zero-copy access to the hot-path sections.
    pub fn open(path: impl AsRef<Path>) -> MathverseResult<Self> {
        let path = path.as_ref();
        let unreadable = |source: std::io::Error| MathverseError::ShardFileUnreadable {
            path: path.display().to_string(),
            source,
        };
        let file = std::fs::File::open(path).map_err(unreadable)?;
        // SAFETY: The file is opened read-only and we do not mutate the mapping.
        // The caller must ensure the file is not truncated while the reader is alive
        // (standard mmap contract).
        let mmap = unsafe { Mmap::map(&file).map_err(unreadable)? };
        Self::from_mmap(mmap)
            .map_err(|e| e.with_context(&format!("shard file `{}`", path.display())))
    }

    /// Construct from an existing `Mmap` (useful for testing with `MmapMut`).
    pub(crate) fn from_mmap(mmap: Mmap) -> MathverseResult<Self> {
        let data: &[u8] = &mmap;

        if data.len() < HEADER_SIZE + FOOTER_SIZE {
            return Err(MathverseError::Truncated {
                expected: HEADER_SIZE + FOOTER_SIZE,
                got: data.len(),
            });
        }

        // Parse header
        let header_bytes: &[u8; HEADER_SIZE] =
            data[..HEADER_SIZE]
                .try_into()
                .map_err(|_| MathverseError::Truncated {
                    expected: HEADER_SIZE,
                    got: data.len(),
                })?;
        let header = ShardHeader::from_bytes(header_bytes)?;

        // Verify checksum
        let footer_start = data.len() - FOOTER_SIZE;
        let content = &data[..footer_start];
        let expected_hash = &data[footer_start..footer_start + 32];
        let actual_hash = blake3::hash(content);
        if actual_hash.as_bytes() != expected_hash {
            return Err(MathverseError::ChecksumMismatch {
                expected: hex::encode(expected_hash),
                got: hex::encode(actual_hash.as_bytes()),
            });
        }

        // Decompress string table (eagerly — it is zstd-compressed)
        let string_start = HEADER_SIZE;
        let string_end = string_start + header.string_data_len as usize;
        if string_end > data.len() {
            return Err(MathverseError::Truncated {
                expected: string_end,
                got: data.len(),
            });
        }
        let string_decompressed =
            zstd::bulk::decompress(&data[string_start..string_end], max_decompress_bytes())?;
        let strings = decode_string_table(&string_decompressed, header.string_count)?;

        let checked_add = |base: usize, len: usize| -> MathverseResult<usize> {
            base.checked_add(len).ok_or(MathverseError::Truncated {
                expected: usize::MAX,
                got: data.len(),
            })
        };
        let checked_mul = |count: u32, size: usize| -> MathverseResult<usize> {
            (count as usize)
                .checked_mul(size)
                .ok_or(MathverseError::Truncated {
                    expected: usize::MAX,
                    got: data.len(),
                })
        };

        // Compute raw section offsets
        let level_start = string_end;
        let level_end = checked_add(
            level_start,
            checked_mul(header.level_count, FlatLevel::SIZE)?,
        )?;
        let expr_start = level_end;
        let expr_end = checked_add(expr_start, checked_mul(header.expr_count, FlatExpr::SIZE)?)?;
        let constant_start = expr_end;
        let constant_end = checked_add(
            constant_start,
            checked_mul(header.constant_count, header.constant_header_size())?,
        )?;
        let level_lists_start = constant_end;
        let level_lists_end =
            checked_add(level_lists_start, checked_mul(header.level_lists_count, 4)?)?;
        let bloom_start = level_lists_end;
        let bloom_end = checked_add(bloom_start, header.bloom_size as usize)?;
        let sorted_index_len = if header.has_sorted_index() {
            header.sorted_index_len as usize
        } else {
            0
        };
        validate_sorted_index_len(sorted_index_len, "<mmap>")?;
        let sorted_index_end = checked_add(bloom_end, sorted_index_len)?;
        let provenance_end = checked_add(sorted_index_end, header.provenance_len as usize)?;

        // Bounds check
        if provenance_end != footer_start {
            if provenance_end > footer_start {
                return Err(MathverseError::Truncated {
                    expected: checked_add(provenance_end, FOOTER_SIZE)?,
                    got: data.len(),
                });
            }
            return Err(MathverseError::ShardCorrupt {
                path: "<mmap>".to_string(),
                reason: format!(
                    "section layout ended at byte {provenance_end}, before footer at byte {footer_start}"
                ),
            });
        }

        let offsets = SectionOffsets {
            level_start,
            level_end,
            expr_start,
            expr_end,
            constant_start,
            constant_end,
            level_lists_start,
            level_lists_end,
            bloom_start,
            bloom_end,
        };

        let source_module = decode_source_module(&header, &strings);
        Ok(Self {
            mmap,
            header,
            strings,
            offsets,
            levels: Vec::new(),
            level_lists: Vec::new(),
            constants: Vec::new(),
            source_module,
        })
    }

    /// Open a shard via mmap for the DEMAND-PAGED lazy closure source.
    ///
    /// Unlike [`Self::open`], this:
    /// - SKIPS the whole-file blake3 checksum (which would touch every page and
    ///   defeat demand paging — the bulk expr arena would all fault in). The
    ///   shard was checksummed when it was built; the lazy-serve path's trust
    ///   contract matches the eager `ShardReader` (admission-only, no per-open
    ///   re-hash — see the Phase-1 soundness notes), and every served `Expr` is
    ///   still structurally reconstructed.
    /// - Eagerly decodes ONLY the small sections (level pool, level-lists,
    ///   constant headers — needed for the name index and per-fold levels) plus
    ///   the (zstd) string table. The big `FlatExpr` arena stays in the mmap and
    ///   is read one 16-byte entry at a time via [`Self::read_expr`], so only the
    ///   bytes of a reconstructed constant's sub-DAG ever become resident.
    pub fn open_lazy(path: impl AsRef<Path>) -> MathverseResult<Self> {
        let path = path.as_ref();
        let unreadable = |source: std::io::Error| MathverseError::ShardFileUnreadable {
            path: path.display().to_string(),
            source,
        };
        let file = std::fs::File::open(path).map_err(unreadable)?;
        // SAFETY: The file is opened read-only and we never mutate the mapping.
        // The caller must keep the file from being truncated while the reader is
        // alive (standard mmap contract); the closure source holds the reader for
        // the whole stamp run, during which the shard dir is read-only.
        let mmap = unsafe { Mmap::map(&file).map_err(unreadable)? };
        let mut reader = Self::from_mmap_no_checksum(mmap)
            .map_err(|e| e.with_context(&format!("shard file `{}`", path.display())))?;
        reader.decode_small_sections()?;
        Ok(reader)
    }

    /// Open a shard from an in-memory byte buffer via an ANONYMOUS mmap, on the
    /// same DEMAND-PAGED lazy path as [`Self::open_lazy`] (v3 required, footer
    /// checksum skipped, small sections eagerly decoded).
    ///
    /// Used by the build-time round-trip ORACLE
    /// (`build_kernel_faithful_shard`): it serializes a shard to bytes, then
    /// re-parses THOSE bytes through this exact mmap path and runs
    /// `materialize` — so a serialization bug only visible on the mmap read path
    /// is caught before the shard is marked fail-closed-verified. No temp file is
    /// created (anonymous mapping copied from `bytes`).
    pub(crate) fn open_lazy_from_bytes(bytes: &[u8]) -> MathverseResult<Self> {
        let mut anon = memmap2::MmapMut::map_anon(bytes.len())?;
        anon.copy_from_slice(bytes);
        let mmap = anon.make_read_only()?;
        let mut reader = Self::from_mmap_no_checksum(mmap)?;
        reader.decode_small_sections()?;
        Ok(reader)
    }

    /// Eagerly decode the SMALL sections (level pool, level-lists, constant
    /// headers) from the already-bounds-checked offsets. Shared by the lazy
    /// open paths.
    fn decode_small_sections(&mut self) -> MathverseResult<()> {
        self.levels = decode_levels(self.level_bytes(), self.header.level_count)?;
        self.level_lists =
            decode_level_lists_bytes(self.level_lists_bytes(), self.header.level_lists_count);
        self.constants = decode_constants(
            self.constant_bytes(),
            self.header.constant_count,
            self.header.is_legacy(),
        )?;
        Ok(())
    }

    /// Like [`Self::from_mmap`] but WITHOUT the whole-file blake3 checksum, so
    /// untouched pages are never faulted in (the demand-paging win). Performs the
    /// same header parse and section-bounds validation as the checksummed path.
    fn from_mmap_no_checksum(mmap: Mmap) -> MathverseResult<Self> {
        let data: &[u8] = &mmap;

        if data.len() < HEADER_SIZE + FOOTER_SIZE {
            return Err(MathverseError::Truncated {
                expected: HEADER_SIZE + FOOTER_SIZE,
                got: data.len(),
            });
        }

        let header_bytes: &[u8; HEADER_SIZE] =
            data[..HEADER_SIZE]
                .try_into()
                .map_err(|_| MathverseError::Truncated {
                    expected: HEADER_SIZE,
                    got: data.len(),
                })?;
        // SOUNDNESS (closure binding, Step 3): the lazy/checksum-skipping path
        // REQUIRES v3, so a pre-v3 (unbound) closure shard is rejected here ->
        // the dispatcher hard-falls-back to the eager loader. The shared
        // `from_bytes` (eager readers) still accepts v1/v2/v3, so the shipped
        // v2 library is unaffected.
        let header = ShardHeader::from_bytes_strict(header_bytes, SHARD_VERSION)?;

        let footer_start = data.len() - FOOTER_SIZE;

        let string_start = HEADER_SIZE;
        let string_end = string_start + header.string_data_len as usize;
        if string_end > data.len() {
            return Err(MathverseError::Truncated {
                expected: string_end,
                got: data.len(),
            });
        }
        let string_decompressed =
            zstd::bulk::decompress(&data[string_start..string_end], max_decompress_bytes())?;
        let strings = decode_string_table(&string_decompressed, header.string_count)?;

        let checked_add = |base: usize, len: usize| -> MathverseResult<usize> {
            base.checked_add(len).ok_or(MathverseError::Truncated {
                expected: usize::MAX,
                got: data.len(),
            })
        };
        let checked_mul = |count: u32, size: usize| -> MathverseResult<usize> {
            (count as usize)
                .checked_mul(size)
                .ok_or(MathverseError::Truncated {
                    expected: usize::MAX,
                    got: data.len(),
                })
        };

        let level_start = string_end;
        let level_end = checked_add(
            level_start,
            checked_mul(header.level_count, FlatLevel::SIZE)?,
        )?;
        let expr_start = level_end;
        let expr_end = checked_add(expr_start, checked_mul(header.expr_count, FlatExpr::SIZE)?)?;
        let constant_start = expr_end;
        let constant_end = checked_add(
            constant_start,
            checked_mul(header.constant_count, header.constant_header_size())?,
        )?;
        let level_lists_start = constant_end;
        let level_lists_end =
            checked_add(level_lists_start, checked_mul(header.level_lists_count, 4)?)?;
        let bloom_start = level_lists_end;
        let bloom_end = checked_add(bloom_start, header.bloom_size as usize)?;
        let sorted_index_len = if header.has_sorted_index() {
            header.sorted_index_len as usize
        } else {
            0
        };
        validate_sorted_index_len(sorted_index_len, "<mmap-lazy>")?;
        let sorted_index_end = checked_add(bloom_end, sorted_index_len)?;
        let provenance_end = checked_add(sorted_index_end, header.provenance_len as usize)?;

        if provenance_end != footer_start {
            if provenance_end > footer_start {
                return Err(MathverseError::Truncated {
                    expected: checked_add(provenance_end, FOOTER_SIZE)?,
                    got: data.len(),
                });
            }
            return Err(MathverseError::ShardCorrupt {
                path: "<mmap-lazy>".to_string(),
                reason: format!(
                    "section layout ended at byte {provenance_end}, before footer at byte {footer_start}"
                ),
            });
        }

        let offsets = SectionOffsets {
            level_start,
            level_end,
            expr_start,
            expr_end,
            constant_start,
            constant_end,
            level_lists_start,
            level_lists_end,
            bloom_start,
            bloom_end,
        };

        let source_module = decode_source_module(&header, &strings);
        Ok(Self {
            mmap,
            header,
            strings,
            offsets,
            levels: Vec::new(),
            level_lists: Vec::new(),
            constants: Vec::new(),
            source_module,
        })
    }

    /// Raw byte slice of the level pool section.
    #[inline]
    pub fn level_bytes(&self) -> &[u8] {
        &self.mmap[self.offsets.level_start..self.offsets.level_end]
    }

    /// Raw byte slice of the FlatExpr arena section.
    #[inline]
    pub fn expr_bytes(&self) -> &[u8] {
        &self.mmap[self.offsets.expr_start..self.offsets.expr_end]
    }

    /// Raw byte slice of the constant headers section.
    #[inline]
    pub fn constant_bytes(&self) -> &[u8] {
        &self.mmap[self.offsets.constant_start..self.offsets.constant_end]
    }

    /// Raw byte slice of the bloom filter section.
    #[inline]
    pub fn bloom_bytes(&self) -> &[u8] {
        &self.mmap[self.offsets.bloom_start..self.offsets.bloom_end]
    }

    /// Raw byte slice of the level_lists section.
    #[inline]
    pub fn level_lists_bytes(&self) -> &[u8] {
        &self.mmap[self.offsets.level_lists_start..self.offsets.level_lists_end]
    }

    /// Read a single level from the pool by index (zero-copy parse).
    pub fn read_level(&self, idx: u32) -> MathverseResult<FlatLevel> {
        if idx >= self.header.level_count {
            return Err(MathverseError::ExprOutOfRange {
                idx,
                count: self.header.level_count,
            });
        }
        let base = self.offsets.level_start + idx as usize * FlatLevel::SIZE;
        let levels = decode_levels(&self.mmap[base..base + FlatLevel::SIZE], 1)?;
        Ok(levels[0])
    }

    /// Read a single expression from the arena by index (zero-copy parse).
    pub fn read_expr(&self, idx: u32) -> MathverseResult<FlatExpr> {
        if idx >= self.header.expr_count {
            return Err(MathverseError::ExprOutOfRange {
                idx,
                count: self.header.expr_count,
            });
        }
        let base = self.offsets.expr_start + idx as usize * FlatExpr::SIZE;
        let exprs = decode_exprs(&self.mmap[base..base + FlatExpr::SIZE], 1)?;
        Ok(exprs[0])
    }

    /// Read a single constant header by index (zero-copy parse).
    pub fn read_constant(&self, idx: u32) -> MathverseResult<MathverseConstantHeader> {
        if idx >= self.header.constant_count {
            return Err(MathverseError::ConstantOutOfRange {
                idx,
                count: self.header.constant_count,
            });
        }
        let entry_size = self.header.constant_header_size();
        let base = self.offsets.constant_start + idx as usize * entry_size;
        if self.header.is_legacy() {
            let buf: &[u8; MathverseConstantHeader::LEGACY_SIZE] = self.mmap
                [base..base + MathverseConstantHeader::LEGACY_SIZE]
                .try_into()
                .map_err(|_| MathverseError::Truncated {
                    expected: base + MathverseConstantHeader::LEGACY_SIZE,
                    got: self.mmap.len(),
                })?;
            Ok(MathverseConstantHeader::from_legacy_bytes(buf))
        } else {
            let buf: &[u8; MathverseConstantHeader::SIZE] = self.mmap
                [base..base + MathverseConstantHeader::SIZE]
                .try_into()
                .map_err(|_| MathverseError::Truncated {
                    expected: base + MathverseConstantHeader::SIZE,
                    got: self.mmap.len(),
                })?;
            Ok(MathverseConstantHeader::from_bytes(buf))
        }
    }

    /// Check if a name might exist in this shard (bloom filter check).
    pub fn bloom_maybe_contains(&self, name: &str) -> bool {
        bloom_check(self.bloom_bytes(), name)
    }

    /// Look up a constant by name (linear scan after bloom check).
    pub fn lookup_name(&self, name: &str) -> Option<(u32, MathverseConstantHeader)> {
        if !self.bloom_maybe_contains(name) {
            return None;
        }
        for i in 0..self.header.constant_count {
            if let Ok(hdr) = self.read_constant(i) {
                let idx = hdr.name_idx as usize;
                if idx < self.strings.len() && self.strings[idx] == name {
                    return Some((i, hdr));
                }
            }
        }
        None
    }

    /// Materialize all levels (for interop with non-mmap code paths).
    pub fn materialize_levels(&self) -> MathverseResult<Vec<FlatLevel>> {
        decode_levels(self.level_bytes(), self.header.level_count)
    }

    /// Materialize all expressions (for interop with non-mmap code paths).
    pub fn materialize_exprs(&self) -> MathverseResult<Vec<FlatExpr>> {
        decode_exprs(self.expr_bytes(), self.header.expr_count)
    }

    /// Materialize all constant headers (for interop with non-mmap code paths).
    pub fn materialize_constants(&self) -> MathverseResult<Vec<MathverseConstantHeader>> {
        decode_constants(
            self.constant_bytes(),
            self.header.constant_count,
            self.header.is_legacy(),
        )
    }
}

// ---------------------------------------------------------------------------
// Delta compaction
// ---------------------------------------------------------------------------

/// Merge multiple delta shards into a single base shard.
///
/// Shards are processed in order: later shards override earlier ones
/// (last-writer-wins by constant name). The output shard contains the
/// deduplicated union of all constants, with string tables, level pools,
/// and expression arenas merged.
///
/// Index remapping: because each input shard has its own string/level/expr
/// numbering, all indices in the merged constant headers are remapped to
/// the output shard's numbering.
pub fn compact_deltas(shards: &[ShardReader], out: impl AsRef<Path>) -> MathverseResult<()> {
    if shards.is_empty() {
        return Err(MathverseError::ImportFailed {
            system: "compact_deltas".to_string(),
            reason: "no input shards".to_string(),
        });
    }

    // Phase 1: Determine which shard wins for each constant name.
    // Walk shards in order; later shards override earlier ones.
    // Key: constant name -> (shard_index, constant_index_within_shard)
    let mut winners: hashbrown::HashMap<String, (usize, usize)> = hashbrown::HashMap::new();

    for (shard_idx, shard) in shards.iter().enumerate() {
        for (const_idx, constant) in shard.constants.iter().enumerate() {
            let name_idx = constant.name_idx as usize;
            if name_idx < shard.strings.len() {
                let name = shard.strings[name_idx].clone();
                // Last-writer-wins: unconditionally insert/overwrite.
                winners.insert(name, (shard_idx, const_idx));
            }
        }
    }

    // Phase 2: Build the output shard. For each winning constant we need to
    // remap its string, level, and expr indices into the output numbering.
    let mut writer = ShardWriter::new();

    // Track remapping tables per shard: string_idx -> output string_idx, etc.
    // We build these lazily (only for shards that have winning constants).
    let shard_count = shards.len();
    let mut string_maps: Vec<hashbrown::HashMap<u32, u32>> =
        vec![hashbrown::HashMap::new(); shard_count];
    let mut level_maps: Vec<hashbrown::HashMap<u32, u32>> =
        vec![hashbrown::HashMap::new(); shard_count];
    let mut expr_maps: Vec<hashbrown::HashMap<u32, u32>> =
        vec![hashbrown::HashMap::new(); shard_count];

    // Helper: ensure a string from a given shard is in the output and return its output index.
    fn remap_string(
        writer: &mut ShardWriter,
        shard: &ShardReader,
        map: &mut hashbrown::HashMap<u32, u32>,
        idx: u32,
    ) -> u32 {
        if let Some(&out_idx) = map.get(&idx) {
            return out_idx;
        }
        let s = &shard.strings[idx as usize];
        let out_idx = writer.add_string(s);
        map.insert(idx, out_idx);
        out_idx
    }

    // Helper: recursively remap a level and all its dependencies.
    fn remap_level(
        writer: &mut ShardWriter,
        shard: &ShardReader,
        level_map: &mut hashbrown::HashMap<u32, u32>,
        string_map: &mut hashbrown::HashMap<u32, u32>,
        idx: u32,
    ) -> MathverseResult<u32> {
        if let Some(&out_idx) = level_map.get(&idx) {
            return Ok(out_idx);
        }
        let level = &shard.levels[idx as usize];
        let new_level = match level.tag {
            FlatLevel::TAG_ZERO => FlatLevel::zero(),
            FlatLevel::TAG_SUCC => {
                let inner_bytes = &level.data[0..4];
                let inner = u32::from_le_bytes([
                    inner_bytes[0],
                    inner_bytes[1],
                    inner_bytes[2],
                    inner_bytes[3],
                ]);
                let new_inner = remap_level(writer, shard, level_map, string_map, inner)?;
                FlatLevel::succ(new_inner)
            }
            FlatLevel::TAG_MAX | FlatLevel::TAG_IMAX => {
                let left = u32::from_le_bytes([
                    level.data[0],
                    level.data[1],
                    level.data[2],
                    level.data[3],
                ]);
                let right = u32::from_le_bytes([
                    level.data[4],
                    level.data[5],
                    level.data[6],
                    level.data[7],
                ]);
                let new_left = remap_level(writer, shard, level_map, string_map, left)?;
                let new_right = remap_level(writer, shard, level_map, string_map, right)?;
                if level.tag == FlatLevel::TAG_MAX {
                    FlatLevel::max(new_left, new_right)
                } else {
                    let mut l = FlatLevel::max(new_left, new_right);
                    l.tag = FlatLevel::TAG_IMAX;
                    l
                }
            }
            FlatLevel::TAG_PARAM => {
                let name_idx = u32::from_le_bytes([
                    level.data[0],
                    level.data[1],
                    level.data[2],
                    level.data[3],
                ]);
                let new_name = remap_string(writer, shard, string_map, name_idx);
                FlatLevel::param(new_name)
            }
            unknown => {
                return Err(MathverseError::UnknownLevelTag { tag: unknown, idx });
            }
        };
        let out_idx = writer.add_level(new_level);
        level_map.insert(idx, out_idx);
        Ok(out_idx)
    }

    // Helper: recursively remap an expression and all its dependencies.
    fn remap_expr(
        writer: &mut ShardWriter,
        shard: &ShardReader,
        expr_map: &mut hashbrown::HashMap<u32, u32>,
        level_map: &mut hashbrown::HashMap<u32, u32>,
        string_map: &mut hashbrown::HashMap<u32, u32>,
        idx: u32,
    ) -> MathverseResult<u32> {
        if idx == crate::types::NO_VALUE {
            return Ok(crate::types::NO_VALUE);
        }
        if let Some(&out_idx) = expr_map.get(&idx) {
            return Ok(out_idx);
        }

        // Reserve a slot to handle forward references (topological order assumed).
        // We parse the expr, remap its children, then write.
        let expr = &shard.exprs[idx as usize];
        let edata = &expr.data;
        let read_u32 = |off: usize| -> u32 {
            u32::from_le_bytes([edata[off], edata[off + 1], edata[off + 2], edata[off + 3]])
        };

        let new_expr = match expr.tag {
            0 => FlatExpr::bvar(read_u32(0)),
            1 => {
                let level_idx = read_u32(0);
                let new_level = remap_level(writer, shard, level_map, string_map, level_idx)?;
                FlatExpr::sort(new_level)
            }
            2 => {
                let name_idx = read_u32(0);
                let levels_idx = read_u32(4);
                let new_name = remap_string(writer, shard, string_map, name_idx);
                // Remap the level list if present
                let new_levels_idx = if levels_idx == u32::MAX || shard.level_lists.is_empty() {
                    levels_idx
                } else if (levels_idx as usize) < shard.level_lists.len() {
                    let count = shard.level_lists[levels_idx as usize] as usize;
                    let start = levels_idx as usize + 1;
                    let mut remapped = Vec::with_capacity(count);
                    for k in 0..count {
                        let old_lvl_idx = shard.level_lists[start + k];
                        let new_lvl_idx =
                            remap_level(writer, shard, level_map, string_map, old_lvl_idx)?;
                        remapped.push(new_lvl_idx);
                    }
                    writer.add_level_list(&remapped)
                } else {
                    levels_idx // out of range — pass through
                };
                FlatExpr::const_ref(new_name, new_levels_idx)
            }
            3 => {
                let fn_idx = read_u32(0);
                let arg_idx = read_u32(4);
                let new_fn = remap_expr(writer, shard, expr_map, level_map, string_map, fn_idx)?;
                let new_arg = remap_expr(writer, shard, expr_map, level_map, string_map, arg_idx)?;
                FlatExpr::app(new_fn, new_arg)
            }
            4 => {
                let binder_info = edata[0];
                let ty_raw = u32::from_le_bytes([edata[1], edata[2], edata[3], edata[4]]);
                let body_raw = u32::from_le_bytes([edata[5], edata[6], edata[7], edata[8]]);
                let new_ty = remap_expr(writer, shard, expr_map, level_map, string_map, ty_raw)?;
                let new_body =
                    remap_expr(writer, shard, expr_map, level_map, string_map, body_raw)?;
                FlatExpr::lam(binder_info, new_ty, new_body)
            }
            5 => {
                let binder_info = edata[0];
                let ty_raw = u32::from_le_bytes([edata[1], edata[2], edata[3], edata[4]]);
                let body_raw = u32::from_le_bytes([edata[5], edata[6], edata[7], edata[8]]);
                let new_ty = remap_expr(writer, shard, expr_map, level_map, string_map, ty_raw)?;
                let new_body =
                    remap_expr(writer, shard, expr_map, level_map, string_map, body_raw)?;
                FlatExpr::pi(binder_info, new_ty, new_body)
            }
            6 => {
                let ty_idx = read_u32(0);
                let val_idx = read_u32(4);
                let body_idx = read_u32(8);
                let new_ty = remap_expr(writer, shard, expr_map, level_map, string_map, ty_idx)?;
                let new_val = remap_expr(writer, shard, expr_map, level_map, string_map, val_idx)?;
                let new_body =
                    remap_expr(writer, shard, expr_map, level_map, string_map, body_idx)?;
                FlatExpr::let_expr(new_ty, new_val, new_body)
            }
            7 => {
                let val = u64::from_le_bytes([
                    edata[0], edata[1], edata[2], edata[3], edata[4], edata[5], edata[6], edata[7],
                ]);
                FlatExpr::lit_nat(val)
            }
            8 => {
                let str_idx = read_u32(0);
                let new_str = remap_string(writer, shard, string_map, str_idx);
                FlatExpr::lit_str(new_str)
            }
            9 => {
                let name_idx = read_u32(0);
                let field = u16::from_le_bytes([edata[4], edata[5]]);
                let expr_idx = read_u32(6);
                let new_name = remap_string(writer, shard, string_map, name_idx);
                let new_expr_idx =
                    remap_expr(writer, shard, expr_map, level_map, string_map, expr_idx)?;
                FlatExpr::proj(new_name, field, new_expr_idx)
            }
            10 => {
                let val = u64::from_le_bytes([
                    edata[0], edata[1], edata[2], edata[3], edata[4], edata[5], edata[6], edata[7],
                ]);
                FlatExpr::fvar(val)
            }
            unknown => {
                return Err(MathverseError::UnknownExprTag { tag: unknown, idx });
            }
        };
        let mut final_expr = new_expr;
        final_expr.flags = expr.flags;
        let out_idx = writer.add_expr(final_expr);
        expr_map.insert(idx, out_idx);
        Ok(out_idx)
    }

    // Phase 3: Iterate winners in deterministic order (sorted by name) and
    // build the output shard.
    let mut sorted_winners: Vec<(String, (usize, usize))> = winners.into_iter().collect();
    sorted_winners.sort_by(|a, b| a.0.cmp(&b.0));

    for (_, (shard_idx, const_idx)) in &sorted_winners {
        let shard = &shards[*shard_idx];
        let constant = &shard.constants[*const_idx];

        let smap = &mut string_maps[*shard_idx];
        let lmap = &mut level_maps[*shard_idx];
        let emap = &mut expr_maps[*shard_idx];

        let new_name = remap_string(&mut writer, shard, smap, constant.name_idx);
        let new_type = remap_expr(&mut writer, shard, emap, lmap, smap, constant.type_idx)?;
        let new_value = remap_expr(&mut writer, shard, emap, lmap, smap, constant.value_idx)?;

        // Remap level parameter names (contiguous string table slots).
        //
        // We intentionally bypass `writer.add_string`'s dedup cache here via
        // `add_string_block`: if another shard has already contributed any of
        // the same param names (e.g. both shards use `u`, `v`), routing
        // through the dedup cache would return earlier indices and break
        // the `strings[lp_start .. lp_start + count]` contiguous-window
        // invariant that downstream consumers rely on. See #3557.
        let new_lp_start = if constant.level_params_count > 0 {
            let count = constant.level_params_count as usize;
            let start = constant.level_params_start as usize;
            let src = &shard.strings;
            // Collect the param-name slice from the source shard; any
            // out-of-range index is an upstream corruption we surface
            // explicitly rather than silently truncating.
            let mut names: Vec<&str> = Vec::with_capacity(count);
            for k in 0..count {
                let idx = start + k;
                let name = src.get(idx).ok_or_else(|| MathverseError::ImportFailed {
                    system: "compact_deltas".to_string(),
                    reason: format!(
                        "level_params index {idx} out of range (strings len = {})",
                        src.len()
                    ),
                })?;
                names.push(name.as_str());
            }
            writer.add_string_block(&names)
        } else {
            0
        };

        // Rebuild the inductive-metadata `_pad2` block instead of zeroing it.
        //
        // `load_shard` preserves this via `remap_inductive_metadata` (a single
        // contiguous `+ string_base` rebase); here the merge remaps strings
        // individually through a per-shard dedup cache, so the `all_names`
        // string-table run is NOT contiguous in the output and cannot be
        // rebased by a constant offset. We instead re-emit the run via
        // `add_string_block` (bypassing dedup, exactly like the `level_params`
        // window above) so the relocated `(start, count)` stays a contiguous,
        // resolvable block. `num_params` is merge-invariant and copies through.
        // Fail-closed: an out-of-range `all_names` slice is surfaced as an
        // explicit error rather than silently truncated, so a corrupt stamp
        // rejects the family instead of producing bogus indices.
        let new_all_names_start = match constant.inductive_decl_all_names_block() {
            Some((start, count)) if count > 0 => {
                let start = start as usize;
                let count = count as usize;
                let src = &shard.strings;
                let mut names: Vec<&str> = Vec::with_capacity(count);
                for k in 0..count {
                    let idx = start + k;
                    let name = src.get(idx).ok_or_else(|| MathverseError::ImportFailed {
                        system: "compact_deltas".to_string(),
                        reason: format!(
                            "inductive all_names index {idx} out of range (strings len = {})",
                            src.len()
                        ),
                    })?;
                    names.push(name.as_str());
                }
                Some(writer.add_string_block(&names))
            }
            _ => None,
        };

        let mut header = MathverseConstantHeader {
            name_idx: new_name,
            type_idx: new_type,
            value_idx: new_value,
            source_system: constant.source_system,
            import_confidence: constant.import_confidence,
            content_domain: constant.content_domain,
            decl_kind: constant.decl_kind,
            axiom_profile: constant.axiom_profile,
            sidecar_digest: constant.sidecar_digest,
            provenance_idx: constant.provenance_idx,
            level_params_start: new_lp_start,
            level_params_count: constant.level_params_count,
            _pad2: [0u8; 26],
        };
        if let Some(num_params) = constant.inductive_decl_num_params() {
            header.set_inductive_decl_num_params(num_params);
        }
        if let (Some(new_start), Some((_, count))) = (
            new_all_names_start,
            constant.inductive_decl_all_names_block(),
        ) {
            header.set_inductive_decl_all_names(new_start, count);
        }
        // Preserve the Lean `DefinitionSafety` trust label (`_pad2[25]`) across
        // the merge — dropping it would silently upgrade an `unsafe def` to
        // safe in the compacted output.
        if let Some(safety) = constant.definition_safety() {
            header.set_definition_safety(safety);
        }
        writer.add_constant(header);
    }

    writer.write_to_file(out)?;
    Ok(())
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn encode_string_table(strings: &[String]) -> Vec<u8> {
    // Pre-size to the exact byte total (4-byte length prefix + payload per string)
    // so the table — built across millions of declarations — never reallocates.
    // Output bytes are unchanged, so the zstd input and blake3 footer are identical.
    let total: usize = strings.iter().map(|s| 4 + s.len()).sum();
    let mut buf = Vec::with_capacity(total);
    for s in strings {
        let len = s.len() as u32;
        buf.extend_from_slice(&len.to_le_bytes());
        buf.extend_from_slice(s.as_bytes());
    }
    buf
}

fn decode_string_table(data: &[u8], count: u32) -> MathverseResult<Vec<String>> {
    let mut strings = Vec::with_capacity(count as usize);
    let mut offset = 0;
    for _ in 0..count {
        if offset + 4 > data.len() {
            return Err(MathverseError::Truncated {
                expected: offset + 4,
                got: data.len(),
            });
        }
        let len = u32::from_le_bytes([
            data[offset],
            data[offset + 1],
            data[offset + 2],
            data[offset + 3],
        ]) as usize;
        offset += 4;
        if offset + len > data.len() {
            return Err(MathverseError::Truncated {
                expected: offset + len,
                got: data.len(),
            });
        }
        let s = String::from_utf8(data[offset..offset + len].to_vec()).map_err(|e| {
            MathverseError::ImportFailed {
                system: "string_table".to_string(),
                reason: e.to_string(),
            }
        })?;
        strings.push(s);
        offset += len;
    }
    if offset != data.len() {
        return Err(MathverseError::ShardCorrupt {
            path: "<string_table>".to_string(),
            reason: format!(
                "string table has {} trailing byte(s) after {count} declared entries",
                data.len() - offset
            ),
        });
    }
    Ok(strings)
}

fn level_to_bytes(level: &FlatLevel) -> [u8; FlatLevel::SIZE] {
    let mut buf = [0u8; FlatLevel::SIZE];
    buf[0] = level.tag;
    // bytes 1..4 padding
    buf[4..12].copy_from_slice(&level.data);
    buf
}

/// Decode the level-lists table from its raw `u32` LE bytes. `data` must be
/// exactly `count * 4` bytes (the slice the level-lists section spans). Mirrors
/// the inline decode in [`ShardReader::from_bytes`].
fn decode_level_lists_bytes(data: &[u8], count: u32) -> Vec<u32> {
    let count = count as usize;
    let mut ll = Vec::with_capacity(count);
    for i in 0..count {
        let base = i * 4;
        ll.push(u32::from_le_bytes([
            data[base],
            data[base + 1],
            data[base + 2],
            data[base + 3],
        ]));
    }
    ll
}

fn decode_levels(data: &[u8], count: u32) -> MathverseResult<Vec<FlatLevel>> {
    let mut levels = Vec::with_capacity(count as usize);
    for i in 0..count as usize {
        let base = i * FlatLevel::SIZE;
        let tag = data[base];
        // Reconstruct via public constructors to match header layout.
        let level = match tag {
            FlatLevel::TAG_ZERO => FlatLevel::zero(),
            FlatLevel::TAG_SUCC => {
                let inner = u32::from_le_bytes([
                    data[base + 4],
                    data[base + 5],
                    data[base + 6],
                    data[base + 7],
                ]);
                FlatLevel::succ(inner)
            }
            FlatLevel::TAG_MAX | FlatLevel::TAG_IMAX => {
                let left = u32::from_le_bytes([
                    data[base + 4],
                    data[base + 5],
                    data[base + 6],
                    data[base + 7],
                ]);
                let right = u32::from_le_bytes([
                    data[base + 8],
                    data[base + 9],
                    data[base + 10],
                    data[base + 11],
                ]);
                if tag == FlatLevel::TAG_MAX {
                    FlatLevel::max(left, right)
                } else {
                    // imax: same layout as max, just different tag byte.
                    let mut level = FlatLevel::max(left, right);
                    level.tag = FlatLevel::TAG_IMAX;
                    level
                }
            }
            FlatLevel::TAG_PARAM => {
                let name_idx = u32::from_le_bytes([
                    data[base + 4],
                    data[base + 5],
                    data[base + 6],
                    data[base + 7],
                ]);
                FlatLevel::param(name_idx)
            }
            _ => {
                return Err(MathverseError::ImportFailed {
                    system: "level_pool".to_string(),
                    reason: format!("unknown level tag: {tag}"),
                });
            }
        };
        levels.push(level);
    }
    Ok(levels)
}

fn read_level_u32(level: &FlatLevel, off: usize) -> u32 {
    u32::from_le_bytes([
        level.data[off],
        level.data[off + 1],
        level.data[off + 2],
        level.data[off + 3],
    ])
}

fn validate_level_pool(levels: &[FlatLevel], string_count: usize) -> MathverseResult<()> {
    let level_count = levels.len() as u32;
    for (i, level) in levels.iter().enumerate() {
        match level.tag {
            FlatLevel::TAG_ZERO => {}
            FlatLevel::TAG_SUCC => {
                let inner_idx = read_level_u32(level, 0);
                if inner_idx >= level_count {
                    return Err(MathverseError::ShardCorrupt {
                        path: "<levels>".to_string(),
                        reason: format!(
                            "level {i} successor child index {inner_idx} out of bounds for {level_count} levels"
                        ),
                    });
                }
            }
            FlatLevel::TAG_MAX | FlatLevel::TAG_IMAX => {
                let left_idx = read_level_u32(level, 0);
                if left_idx >= level_count {
                    return Err(MathverseError::ShardCorrupt {
                        path: "<levels>".to_string(),
                        reason: format!(
                            "level {i} left child index {left_idx} out of bounds for {level_count} levels"
                        ),
                    });
                }
                let right_idx = read_level_u32(level, 4);
                if right_idx >= level_count {
                    return Err(MathverseError::ShardCorrupt {
                        path: "<levels>".to_string(),
                        reason: format!(
                            "level {i} right child index {right_idx} out of bounds for {level_count} levels"
                        ),
                    });
                }
            }
            FlatLevel::TAG_PARAM => {
                let name_idx = read_level_u32(level, 0);
                if name_idx as usize >= string_count {
                    return Err(MathverseError::ShardCorrupt {
                        path: "<levels>".to_string(),
                        reason: format!(
                            "level {i} parameter name index {name_idx} out of bounds for {string_count} strings"
                        ),
                    });
                }
            }
            _ => unreachable!("decode_levels rejects unknown tags"),
        }
    }
    Ok(())
}

fn expr_to_bytes(expr: &FlatExpr) -> [u8; FlatExpr::SIZE] {
    let mut buf = [0u8; FlatExpr::SIZE];
    buf[0] = expr.tag;
    buf[1] = expr.flags;
    // bytes 2..4 padding
    buf[4..16].copy_from_slice(&expr.data);
    buf
}

fn decode_exprs(data: &[u8], count: u32) -> MathverseResult<Vec<FlatExpr>> {
    let mut exprs = Vec::with_capacity(count as usize);
    for i in 0..count as usize {
        let base = i * FlatExpr::SIZE;
        let tag = data[base];
        let flags = data[base + 1];
        let edata = &data[base + 4..base + 16];

        // Reconstruct via public constructors to match header layout.
        let read_u32 = |off: usize| -> u32 {
            u32::from_le_bytes([edata[off], edata[off + 1], edata[off + 2], edata[off + 3]])
        };

        let mut expr = match tag {
            0 => FlatExpr::bvar(read_u32(0)),                       // BVar
            1 => FlatExpr::sort(read_u32(0)),                       // Sort
            2 => FlatExpr::const_ref(read_u32(0), read_u32(4)),     // Const
            3 => FlatExpr::app(read_u32(0), read_u32(4)),           // App
            4 => FlatExpr::lam(edata[0], read_u32(1), read_u32(5)), // Lam
            5 => FlatExpr::pi(edata[0], read_u32(1), read_u32(5)),  // Pi
            6 => FlatExpr::let_expr(read_u32(0), read_u32(4), read_u32(8)), // Let
            7 => FlatExpr::lit_nat(u64::from_le_bytes([
                edata[0], edata[1], edata[2], edata[3], edata[4], edata[5], edata[6], edata[7],
            ])), // LitNat
            8 => FlatExpr::lit_str(read_u32(0)),                    // LitStr
            9 => {
                // Proj
                let name_idx = read_u32(0);
                let field = u16::from_le_bytes([edata[4], edata[5]]);
                let expr_idx = read_u32(6);
                FlatExpr::proj(name_idx, field, expr_idx)
            }
            10 => FlatExpr::fvar(u64::from_le_bytes([
                // FVar
                edata[0], edata[1], edata[2], edata[3], edata[4], edata[5], edata[6], edata[7],
            ])),
            _ => {
                return Err(MathverseError::ImportFailed {
                    system: "expr_arena".to_string(),
                    reason: format!("unknown expr tag: {tag}"),
                });
            }
        };
        // Restore original flags (constructors set defaults).
        expr.flags = flags;
        exprs.push(expr);
    }
    Ok(exprs)
}

fn read_expr_u32(expr: &FlatExpr, off: usize) -> u32 {
    u32::from_le_bytes([
        expr.data[off],
        expr.data[off + 1],
        expr.data[off + 2],
        expr.data[off + 3],
    ])
}

/// Whether a raw level pool is the bare zero sentinel — the signature of a
/// legacy coq_v/fstar shard whose importer wrote `Sort` level slots as raw
/// universe **values** rather than level-pool indices (see
/// [`crate::coq::v_type_parser`] and [`crate::shard_reconstruct`]). Reconstruction
/// resolves such `sort(N)` to `succ^N(zero)` losslessly; the validator accepts
/// the OOB index only under this exact bare-sentinel pool so genuine corruption
/// in a populated multi-level shard is still rejected.
fn is_legacy_raw_universe_level_pool(levels: &[FlatLevel]) -> bool {
    matches!(levels, [only] if only.tag == FlatLevel::TAG_ZERO)
}

fn validate_expr_arena(
    exprs: &[FlatExpr],
    levels: &[FlatLevel],
    header: &ShardHeader,
    string_count: usize,
) -> MathverseResult<()> {
    let expr_count = header.expr_count;
    let legacy_raw_universe_sorts = is_legacy_raw_universe_level_pool(levels);
    for (i, expr) in exprs.iter().enumerate() {
        let expr_idx = i;
        match expr.tag {
            0 | 7 | 10 => {}
            1 => {
                let level_idx = read_expr_u32(expr, 0);
                if level_idx >= header.level_count && !legacy_raw_universe_sorts {
                    return Err(MathverseError::ShardCorrupt {
                        path: "<exprs>".to_string(),
                        reason: format!(
                            "expr {expr_idx} sort level index {level_idx} out of bounds for {} levels",
                            header.level_count
                        ),
                    });
                }
            }
            2 => {
                let name_idx = read_expr_u32(expr, 0);
                if name_idx as usize >= string_count {
                    return Err(MathverseError::ShardCorrupt {
                        path: "<exprs>".to_string(),
                        reason: format!(
                            "expr {expr_idx} constant name index {name_idx} out of bounds for {string_count} strings"
                        ),
                    });
                }
                let levels_list_idx = read_expr_u32(expr, 4);
                if levels_list_idx != u32::MAX && levels_list_idx >= header.level_lists_count {
                    return Err(MathverseError::ShardCorrupt {
                        path: "<exprs>".to_string(),
                        reason: format!(
                            "expr {expr_idx} constant level-list index {levels_list_idx} out of bounds for {} level-list entries",
                            header.level_lists_count
                        ),
                    });
                }
            }
            3 => {
                let fn_idx = read_expr_u32(expr, 0);
                if fn_idx >= expr_count {
                    return Err(MathverseError::ShardCorrupt {
                        path: "<exprs>".to_string(),
                        reason: format!(
                            "expr {expr_idx} app function index {fn_idx} out of bounds for {expr_count} expressions"
                        ),
                    });
                }
                let arg_idx = read_expr_u32(expr, 4);
                if arg_idx >= expr_count {
                    return Err(MathverseError::ShardCorrupt {
                        path: "<exprs>".to_string(),
                        reason: format!(
                            "expr {expr_idx} app argument index {arg_idx} out of bounds for {expr_count} expressions"
                        ),
                    });
                }
            }
            4 | 5 => {
                let binder_info = expr.data[0];
                if binder_info > 7 {
                    return Err(MathverseError::ShardCorrupt {
                        path: "<exprs>".to_string(),
                        reason: format!("expr {expr_idx} binder info {binder_info} out of bounds"),
                    });
                }
                let type_idx = read_expr_u32(expr, 1);
                if type_idx >= expr_count {
                    return Err(MathverseError::ShardCorrupt {
                        path: "<exprs>".to_string(),
                        reason: format!(
                            "expr {expr_idx} binder type index {type_idx} out of bounds for {expr_count} expressions"
                        ),
                    });
                }
                let body_idx = read_expr_u32(expr, 5);
                if body_idx >= expr_count {
                    return Err(MathverseError::ShardCorrupt {
                        path: "<exprs>".to_string(),
                        reason: format!(
                            "expr {expr_idx} binder body index {body_idx} out of bounds for {expr_count} expressions"
                        ),
                    });
                }
            }
            6 => {
                let type_idx = read_expr_u32(expr, 0);
                if type_idx >= expr_count {
                    return Err(MathverseError::ShardCorrupt {
                        path: "<exprs>".to_string(),
                        reason: format!(
                            "expr {expr_idx} let type index {type_idx} out of bounds for {expr_count} expressions"
                        ),
                    });
                }
                let value_idx = read_expr_u32(expr, 4);
                if value_idx >= expr_count {
                    return Err(MathverseError::ShardCorrupt {
                        path: "<exprs>".to_string(),
                        reason: format!(
                            "expr {expr_idx} let value index {value_idx} out of bounds for {expr_count} expressions"
                        ),
                    });
                }
                let body_idx = read_expr_u32(expr, 8);
                if body_idx >= expr_count {
                    return Err(MathverseError::ShardCorrupt {
                        path: "<exprs>".to_string(),
                        reason: format!(
                            "expr {expr_idx} let body index {body_idx} out of bounds for {expr_count} expressions"
                        ),
                    });
                }
            }
            8 => {
                let string_idx = read_expr_u32(expr, 0);
                if string_idx as usize >= string_count {
                    return Err(MathverseError::ShardCorrupt {
                        path: "<exprs>".to_string(),
                        reason: format!(
                            "expr {expr_idx} string literal index {string_idx} out of bounds for {string_count} strings"
                        ),
                    });
                }
            }
            9 => {
                let name_idx = read_expr_u32(expr, 0);
                if name_idx as usize >= string_count {
                    return Err(MathverseError::ShardCorrupt {
                        path: "<exprs>".to_string(),
                        reason: format!(
                            "expr {expr_idx} projection name index {name_idx} out of bounds for {string_count} strings"
                        ),
                    });
                }
                let expr_idx_ref = read_expr_u32(expr, 6);
                if expr_idx_ref >= expr_count {
                    return Err(MathverseError::ShardCorrupt {
                        path: "<exprs>".to_string(),
                        reason: format!(
                            "expr {expr_idx} projection expression index {expr_idx_ref} out of bounds for {expr_count} expressions"
                        ),
                    });
                }
            }
            _ => unreachable!("decode_exprs rejects unknown tags"),
        }
    }
    Ok(())
}

fn decode_constants(
    data: &[u8],
    count: u32,
    legacy: bool,
) -> MathverseResult<Vec<MathverseConstantHeader>> {
    let entry_size = if legacy {
        MathverseConstantHeader::LEGACY_SIZE
    } else {
        MathverseConstantHeader::SIZE
    };
    let mut constants = Vec::with_capacity(count as usize);
    for i in 0..count as usize {
        let base = i * entry_size;
        if legacy {
            let buf: &[u8; MathverseConstantHeader::LEGACY_SIZE] = data
                [base..base + MathverseConstantHeader::LEGACY_SIZE]
                .try_into()
                .map_err(|_| MathverseError::Truncated {
                    expected: base + MathverseConstantHeader::LEGACY_SIZE,
                    got: data.len(),
                })?;
            constants.push(MathverseConstantHeader::from_legacy_bytes(buf));
        } else {
            let buf: &[u8; MathverseConstantHeader::SIZE] = data
                [base..base + MathverseConstantHeader::SIZE]
                .try_into()
                .map_err(|_| MathverseError::Truncated {
                    expected: base + MathverseConstantHeader::SIZE,
                    got: data.len(),
                })?;
            constants.push(MathverseConstantHeader::from_bytes(buf));
        }
    }
    Ok(constants)
}

fn validate_constant_headers(
    constants: &[MathverseConstantHeader],
    header: &ShardHeader,
    strings: &[String],
) -> MathverseResult<()> {
    let string_count = strings.len();
    let mut seen_names: HashMap<&str, usize> = HashMap::new();
    for (i, constant) in constants.iter().enumerate() {
        if constant.name_idx as usize >= string_count {
            return Err(MathverseError::ShardCorrupt {
                path: "<constants>".to_string(),
                reason: format!(
                    "constant {i} name index {} out of bounds for {string_count} strings",
                    constant.name_idx
                ),
            });
        }
        if strings[constant.name_idx as usize].is_empty() {
            return Err(MathverseError::ShardCorrupt {
                path: "<constants>".to_string(),
                reason: format!("constant {i} has an empty declaration name"),
            });
        }
        let name = strings[constant.name_idx as usize].as_str();
        if name.split('.').any(str::is_empty) {
            // warn!("constant {i} declaration name {name:?} contains an empty path segment");
        }
        if name.chars().any(char::is_control) {
            // warn!("constant {i} declaration name {name:?} contains a control character");
        }
        if name.chars().any(|ch| matches!(ch, '/')) {
            // warn!("constant {i} declaration name {name:?} contains a path separator");
        }
        if let Some(previous) = seen_names.insert(name, i) {
            // warn!("constant {i} duplicates declaration name {name:?} first used by constant {previous}");
        }
        if constant.type_idx >= header.expr_count {
            return Err(MathverseError::ShardCorrupt {
                path: "<constants>".to_string(),
                reason: format!(
                    "constant {i} type expression index {} out of bounds for {} expressions",
                    constant.type_idx, header.expr_count
                ),
            });
        }
        if constant.value_idx != crate::types::NO_VALUE && constant.value_idx >= header.expr_count {
            return Err(MathverseError::ShardCorrupt {
                path: "<constants>".to_string(),
                reason: format!(
                    "constant {i} value expression index {} out of bounds for {} expressions",
                    constant.value_idx, header.expr_count
                ),
            });
        }
        if constant.source().is_err() {
            return Err(MathverseError::ShardCorrupt {
                path: "<constants>".to_string(),
                reason: format!(
                    "constant {i} source system {} is not a known SourceSystem",
                    constant.source_system
                ),
            });
        }
        if constant.confidence().is_err() {
            return Err(MathverseError::ShardCorrupt {
                path: "<constants>".to_string(),
                reason: format!(
                    "constant {i} import confidence {} is not a known ImportConfidence",
                    constant.import_confidence
                ),
            });
        }
        if constant.domain().is_err() {
            return Err(MathverseError::ShardCorrupt {
                path: "<constants>".to_string(),
                reason: format!(
                    "constant {i} content domain {} is not a known ContentDomain",
                    constant.content_domain
                ),
            });
        }
        if constant.decl_kind().is_err() {
            return Err(MathverseError::ShardCorrupt {
                path: "<constants>".to_string(),
                reason: format!(
                    "constant {i} declaration kind {} is not a known DeclKind",
                    constant.decl_kind
                ),
            });
        }
        if header.provenance_len == 0
            && (constant.provenance_idx != 0 || constant.sidecar_digest != 0)
        {
            return Err(MathverseError::ShardCorrupt {
                path: "<constants>".to_string(),
                reason: format!(
                    "constant {i} references provenance metadata but shard has no provenance sidecar"
                ),
            });
        }
        if matches!(constant.decl_kind(), Ok(crate::types::DeclKind::Axiom))
            && constant.value_idx != crate::types::NO_VALUE
        {
            // warn!("constant {i} is declared as an axiom but has value expression index {}", constant.value_idx);
        }
        // Note: a strict variant of this check would reject Definition-kind
        // constants whose value_idx == NO_VALUE. We deliberately allow that
        // shape today because some upstream importers mark opaque /
        // pending-translation entries as Definition with no value. Switch
        // to a hard error once every importer guarantees value presence.
        if constant.level_params_count > 0 {
            let end = constant
                .level_params_start
                .checked_add(u32::from(constant.level_params_count))
                .ok_or_else(|| MathverseError::ShardCorrupt {
                    path: "<constants>".to_string(),
                    reason: format!("constant {i} level parameter range overflows"),
                })?;
            if end as usize > string_count {
                return Err(MathverseError::ShardCorrupt {
                    path: "<constants>".to_string(),
                    reason: format!(
                        "constant {i} level parameter range [{}..{}) out of bounds for {string_count} strings",
                        constant.level_params_start, end
                    ),
                });
            }
        }
    }
    Ok(())
}

fn validate_level_lists(level_lists: &[u32], header: &ShardHeader) -> MathverseResult<()> {
    let mut offset = 0usize;
    while offset < level_lists.len() {
        let count = level_lists[offset] as usize;
        if count == 0 {
            return Err(MathverseError::ShardCorrupt {
                path: "<level_lists>".to_string(),
                reason: format!("level-list {offset} has zero entries; empty lists use u32::MAX"),
            });
        }
        let start = offset + 1;
        let end = start
            .checked_add(count)
            .ok_or_else(|| MathverseError::ShardCorrupt {
                path: "<level_lists>".to_string(),
                reason: format!("level-list {offset} entry range overflows"),
            })?;
        if end > level_lists.len() {
            return Err(MathverseError::ShardCorrupt {
                path: "<level_lists>".to_string(),
                reason: format!(
                    "level-list {offset} claims {count} entries but table has only {} remaining",
                    level_lists.len().saturating_sub(start)
                ),
            });
        }
        for (entry, &level_idx) in level_lists[start..end].iter().enumerate() {
            if level_idx >= header.level_count {
                return Err(MathverseError::ShardCorrupt {
                    path: "<level_lists>".to_string(),
                    reason: format!(
                        "level-list {offset} entry {entry} level index {level_idx} out of bounds for {} levels",
                        header.level_count
                    ),
                });
            }
        }
        offset = end;
    }
    Ok(())
}

fn validate_provenance_headers(
    constants: &[MathverseConstantHeader],
    provenance: &[u8],
) -> MathverseResult<()> {
    if provenance.is_empty() {
        return Ok(());
    }

    let sidecar =
        ProvenanceSidecar::from_bytes(provenance).map_err(|err| MathverseError::ShardCorrupt {
            path: "<provenance>".to_string(),
            reason: format!("provenance sidecar failed to decode: {err}"),
        })?;

    for (i, constant) in constants.iter().enumerate() {
        if constant.provenance_idx == 0 && constant.sidecar_digest == 0 {
            continue;
        }
        let Some(_record) = sidecar.get(constant.provenance_idx) else {
            return Err(MathverseError::ShardCorrupt {
                path: "<provenance>".to_string(),
                reason: format!(
                    "constant {i} provenance index {} out of bounds for provenance sidecar",
                    constant.provenance_idx
                ),
            });
        };
        if !sidecar.verify_digest(constant) {
            return Err(MathverseError::ShardCorrupt {
                path: "<provenance>".to_string(),
                reason: format!(
                    "constant {i} provenance digest does not match sidecar record {}",
                    constant.provenance_idx
                ),
            });
        }
        // Note: declaration names are NOT required to be under their
        // module's namespace path in Lean 4. A module like `Init`
        // routinely declares `Nat.add`, `Bool.true`, etc. — the
        // module-path is informational provenance metadata, not a
        // soundness constraint.
    }

    Ok(())
}

/// Decode the optional sorted name index section.
/// Returns the entries and the updated byte offset.
fn decode_sorted_index(
    data: &[u8],
    mut offset: usize,
    header: &ShardHeader,
    constants: &[MathverseConstantHeader],
    strings: &[String],
) -> MathverseResult<(Vec<NameIndexEntry>, usize)> {
    if !header.has_sorted_index() {
        return Ok((Vec::new(), offset));
    }
    let idx_size = header.sorted_index_len as usize;
    let entry_count = idx_size / SORTED_INDEX_ENTRY_SIZE;
    if entry_count != header.constant_count as usize {
        return Err(MathverseError::ShardCorrupt {
            path: "<sorted_index>".to_string(),
            reason: format!(
                "sorted index has {entry_count} entries for {} constants",
                header.constant_count
            ),
        });
    }
    let mut entries: Vec<NameIndexEntry> = Vec::with_capacity(entry_count);
    let mut seen_constants = vec![false; header.constant_count as usize];
    for i in 0..entry_count {
        let base = offset + i * SORTED_INDEX_ENTRY_SIZE;
        let buf: &[u8; SORTED_INDEX_ENTRY_SIZE] = data[base..base + SORTED_INDEX_ENTRY_SIZE]
            .try_into()
            .map_err(|_| MathverseError::Truncated {
                expected: base + SORTED_INDEX_ENTRY_SIZE,
                got: data.len(),
            })?;
        let entry = NameIndexEntry::from_bytes(buf);
        if entry.constant_idx >= header.constant_count {
            return Err(MathverseError::ShardCorrupt {
                path: "<sorted_index>".to_string(),
                reason: format!(
                    "sorted index entry {i} constant index {} out of bounds for {} constants",
                    entry.constant_idx, header.constant_count
                ),
            });
        }
        let constant_idx = entry.constant_idx as usize;
        if seen_constants[constant_idx] {
            return Err(MathverseError::ShardCorrupt {
                path: "<sorted_index>".to_string(),
                reason: format!(
                    "sorted index entry {i} repeats constant index {}",
                    entry.constant_idx
                ),
            });
        }
        seen_constants[constant_idx] = true;
        let constant = &constants[constant_idx];
        let name = strings.get(constant.name_idx as usize).ok_or_else(|| {
            MathverseError::ShardCorrupt {
                path: "<sorted_index>".to_string(),
                reason: format!(
                    "sorted index entry {i} constant {} name index {} out of bounds for {} strings",
                    entry.constant_idx,
                    constant.name_idx,
                    strings.len()
                ),
            }
        })?;
        let expected_hash = name_hash(name);
        if entry.name_hash != expected_hash {
            return Err(MathverseError::ShardCorrupt {
                path: "<sorted_index>".to_string(),
                reason: format!(
                    "sorted index entry {i} hash does not match constant {} name hash",
                    entry.constant_idx
                ),
            });
        }
        if let Some(previous) = entries.last() {
            if previous.name_hash > entry.name_hash {
                return Err(MathverseError::ShardCorrupt {
                    path: "<sorted_index>".to_string(),
                    reason: format!("sorted index entry {i} is out of hash order"),
                });
            }
        }
        entries.push(entry);
    }
    offset += idx_size;
    Ok((entries, offset))
}

fn validate_sorted_index_len(idx_size: usize, path: &str) -> MathverseResult<()> {
    if !idx_size.is_multiple_of(SORTED_INDEX_ENTRY_SIZE) {
        return Err(MathverseError::ShardCorrupt {
            path: path.to_string(),
            reason: format!(
                "sorted index length {idx_size} is not a multiple of entry size {SORTED_INDEX_ENTRY_SIZE}"
            ),
        });
    }
    Ok(())
}

/// Decode the compressed provenance sidecar section.
fn decode_provenance(data: &[u8], offset: usize, header: &ShardHeader) -> MathverseResult<Vec<u8>> {
    let prov_size = header.provenance_len as usize;
    if prov_size > 0 {
        Ok(zstd::bulk::decompress(
            &data[offset..offset + prov_size],
            max_decompress_bytes(),
        )?)
    } else {
        Ok(Vec::new())
    }
}

/// Build a bloom filter from a set of name strings.
fn build_bloom_filter(names: &[String], size: usize) -> Vec<u8> {
    let mut filter = vec![0u8; size];
    let bits = size * 8;
    for name in names {
        let h = blake3::hash(name.as_bytes());
        let bytes = h.as_bytes();
        // Use 3 hash functions derived from blake3 output
        for i in 0..3 {
            let offset = i * 4;
            let idx = u32::from_le_bytes([
                bytes[offset],
                bytes[offset + 1],
                bytes[offset + 2],
                bytes[offset + 3],
            ]) as usize
                % bits;
            filter[idx / 8] |= 1 << (idx % 8);
        }
    }
    filter
}

/// Check if a name might be in the bloom filter.
fn bloom_check(filter: &[u8], name: &str) -> bool {
    let bits = filter.len() * 8;
    if bits == 0 {
        return false;
    }
    let h = blake3::hash(name.as_bytes());
    let bytes = h.as_bytes();
    for i in 0..3 {
        let offset = i * 4;
        let idx = u32::from_le_bytes([
            bytes[offset],
            bytes[offset + 1],
            bytes[offset + 2],
            bytes[offset + 3],
        ]) as usize
            % bits;
        if (filter[idx / 8] & (1 << (idx % 8))) == 0 {
            return false;
        }
    }
    true
}

/// Hex encoding (inline, avoids adding `hex` crate dependency).
mod hex {
    pub fn encode(data: &[u8]) -> String {
        data.iter().map(|b| format!("{b:02x}")).collect()
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{
        AxiomProfile, ContentDomain, DeclKind, ImportConfidence, SourceSystem, NO_VALUE,
    };

    #[test]
    fn test_header_round_trip() {
        let header = ShardHeader {
            magic: SHARD_MAGIC,
            version: SHARD_VERSION,
            flags: 0,
            string_count: 10,
            string_data_len: 200,
            level_count: 5,
            expr_count: 50,
            constant_count: 10,
            bloom_size: BLOOM_SIZE as u32,
            provenance_len: 100,
            sorted_index_len: 0,
            level_lists_count: 0,
            source_olean_blake3: [0u8; 32],
            source_olean_len: 0,
            fail_closed_verified: 0,
            module_name_idx: 0,
        };
        let bytes = header.to_bytes();
        let restored = ShardHeader::from_bytes(&bytes).unwrap();
        assert_eq!(header.string_count, restored.string_count);
        assert_eq!(header.expr_count, restored.expr_count);
        assert_eq!(header.constant_count, restored.constant_count);
    }

    /// TEST 1: a v3 header with non-zero closure-binding fields round-trips
    /// through `to_bytes`/`from_bytes`; bytes 48..96 carry them; the version is
    /// 3; and bytes 0..48 are byte-identical to the same header serialized as v2.
    #[test]
    fn test_v3_header_round_trip_carries_binding_fields() {
        let hash: [u8; 32] = std::array::from_fn(|i| (i as u8).wrapping_mul(7).wrapping_add(3));
        let header = ShardHeader {
            magic: SHARD_MAGIC,
            version: SHARD_VERSION,
            flags: FLAG_HAS_SORTED_INDEX,
            string_count: 11,
            string_data_len: 222,
            level_count: 6,
            expr_count: 60,
            constant_count: 11,
            bloom_size: BLOOM_SIZE as u32,
            provenance_len: 99,
            sorted_index_len: 132,
            level_lists_count: 4,
            source_olean_blake3: hash,
            source_olean_len: 0x0102_0304_0506_0708,
            fail_closed_verified: 1,
            module_name_idx: 0x0042,
        };
        let bytes = header.to_bytes();
        // Bytes 48..96 carry the binding fields verbatim.
        assert_eq!(&bytes[48..80], &hash);
        assert_eq!(
            u64::from_le_bytes(bytes[80..88].try_into().unwrap()),
            0x0102_0304_0506_0708
        );
        assert_eq!(u32::from_le_bytes(bytes[88..92].try_into().unwrap()), 1);
        assert_eq!(u32::from_le_bytes(bytes[92..96].try_into().unwrap()), 0x42);
        // Bytes 96..256 stay zero.
        assert!(bytes[96..256].iter().all(|&b| b == 0));

        let restored = ShardHeader::from_bytes(&bytes).expect("v3 round-trips");
        assert_eq!(restored.version, SHARD_VERSION);
        assert_eq!(restored.source_olean_blake3, hash);
        assert_eq!(restored.source_olean_len, 0x0102_0304_0506_0708);
        assert_eq!(restored.fail_closed_verified, 1);
        assert_eq!(restored.module_name_idx, 0x42);

        // Bytes 0..48 are byte-identical to the same header serialized as v2.
        let mut v2 = header.clone();
        v2.version = SHARD_VERSION_V2;
        v2.source_olean_blake3 = [0u8; 32];
        v2.source_olean_len = 0;
        v2.fail_closed_verified = 0;
        v2.module_name_idx = 0;
        let v2_bytes = v2.to_bytes();
        // The only difference at bytes 0..48 is the version word at 4..8.
        assert_eq!(&bytes[0..4], &v2_bytes[0..4]); // magic
        assert_eq!(&bytes[8..48], &v2_bytes[8..48]); // rest of the shared prefix
    }

    /// TEST 2: `from_bytes_strict(min_version=3)` REJECTS synthetic v1/v2 headers
    /// (UnsupportedVersion) and round-trips v3; the shared `from_bytes` STILL
    /// accepts v1/v2/v3; and `level_lists_count` decodes correctly for a v2
    /// header after the bump (the `>= SHARD_VERSION_V2` fix).
    #[test]
    fn test_from_bytes_strict_version_policy() {
        let mk = |version: u32, level_lists: u32| -> [u8; HEADER_SIZE] {
            ShardHeader {
                magic: SHARD_MAGIC,
                version,
                flags: 0,
                string_count: 3,
                string_data_len: 10,
                level_count: 1,
                expr_count: 2,
                constant_count: 1,
                bloom_size: BLOOM_SIZE as u32,
                provenance_len: 0,
                sorted_index_len: 0,
                level_lists_count: level_lists,
                source_olean_blake3: [0u8; 32],
                source_olean_len: 0,
                fail_closed_verified: 0,
                module_name_idx: 0,
            }
            .to_bytes()
        };

        // Strict v3 rejects v1 and v2.
        let v1 = mk(SHARD_VERSION_LEGACY, 0);
        let v2 = mk(SHARD_VERSION_V2, 7);
        let v3 = mk(SHARD_VERSION, 4);
        assert!(matches!(
            ShardHeader::from_bytes_strict(&v1, SHARD_VERSION),
            Err(MathverseError::UnsupportedVersion(1))
        ));
        assert!(matches!(
            ShardHeader::from_bytes_strict(&v2, SHARD_VERSION),
            Err(MathverseError::UnsupportedVersion(2))
        ));
        assert!(ShardHeader::from_bytes_strict(&v3, SHARD_VERSION).is_ok());

        // Shared `from_bytes` accepts all three (eager library unaffected).
        assert!(ShardHeader::from_bytes(&v1).is_ok());
        assert!(ShardHeader::from_bytes(&v2).is_ok());
        assert!(ShardHeader::from_bytes(&v3).is_ok());

        // level_lists_count decodes for a v2 header after the bump.
        let v2_decoded = ShardHeader::from_bytes(&v2).unwrap();
        assert_eq!(
            v2_decoded.level_lists_count, 7,
            "v2 level_lists must survive the v3 bump (>= SHARD_VERSION_V2 keying)"
        );
        // v1 has no level_lists section.
        assert_eq!(ShardHeader::from_bytes(&v1).unwrap().level_lists_count, 0);
    }

    /// GATE 6: a v2 shard (the SHIPPED mathverse-v1.3.0 library format) still
    /// loads via the GENERAL eager readers after the v3 bump. We write a real
    /// one-constant shard, patch its version word 3->2 (length-preserving) and
    /// re-checksum, then assert both `ShardReader::from_bytes` and the eager
    /// `ShardMmapReader::from_mmap` (checksummed) accept it and decode the
    /// constant. The lazy path (`open_lazy`) is the one that requires v3.
    #[test]
    fn test_v2_shard_still_loads_via_eager_readers() {
        let mut w = ShardWriter::new();
        let l0 = w.add_level(FlatLevel::zero());
        let ty = w.add_expr(FlatExpr::sort(l0));
        let n = w.add_string("Lib.Const");
        w.add_constant(MathverseConstantHeader {
            name_idx: n,
            type_idx: ty,
            value_idx: NO_VALUE,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: ImportConfidence::Translated as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: DeclKind::Definition as u8,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        });
        let mut buf = Vec::new();
        w.write(&mut buf).unwrap();
        // Patch version 3 -> 2 and re-checksum (the footer covers the header).
        buf[4..8].copy_from_slice(&SHARD_VERSION_V2.to_le_bytes());
        let footer_start = buf.len() - FOOTER_SIZE;
        let hash = blake3::hash(&buf[..footer_start]);
        buf[footer_start..footer_start + 32].copy_from_slice(hash.as_bytes());

        // Eager `ShardReader::from_bytes` accepts v2 and decodes the constant.
        let reader = ShardReader::from_bytes(&buf).expect("eager v2 from_bytes loads");
        assert_eq!(reader.header.version, SHARD_VERSION_V2);
        assert_eq!(reader.constants.len(), 1);
        assert_eq!(
            reader
                .strings
                .get(reader.constants[0].name_idx as usize)
                .map(String::as_str),
            Some("Lib.Const")
        );

        // Eager mmap reader (checksummed) accepts v2 too.
        let mut mm = memmap2::MmapMut::map_anon(buf.len()).unwrap();
        mm.copy_from_slice(&buf);
        let mmap = mm.make_read_only().unwrap();
        let mmreader = ShardMmapReader::from_mmap(mmap).expect("eager v2 mmap loads");
        assert_eq!(mmreader.header.version, SHARD_VERSION_V2);
    }

    #[test]
    fn test_compact_deltas_preserves_inductive_metadata() {
        // CHANGE #5 regression: the shard-merge path (`compact_deltas`) used to
        // hardcode `_pad2: [0u8; 26]`, dropping the inductive `num_params` and
        // `all_names` metadata that the normal load path preserves. After the fix
        // both survive the merge, and the relocated `all_names` block still
        // resolves to the original constructor/type names in the merged string
        // table.
        let dir = tempfile::tempdir().unwrap();

        // Shard 0: a parameterized inductive (`MyInd`) carrying num_params + an
        // all_names block. We pre-seed an unrelated string before the all_names
        // run so its start index is nonzero and any drift in string numbering
        // through the merge would be caught.
        let path0 = dir.path().join("ind.mathverse");
        {
            let mut w = ShardWriter::new();
            let l0 = w.add_level(FlatLevel::zero());
            let e0 = w.add_expr(FlatExpr::sort(l0));

            // Unrelated filler so the all_names block does not start at 0.
            let _filler = w.add_string("Some.Filler");
            // Contiguous all_names run (e.g. a 2-type mutual family).
            let an_start = w.add_string("MyInd");
            let _an1 = w.add_string("MyInd.Other");
            let s_name = w.add_string("MyInd");

            let mut hdr = MathverseConstantHeader {
                name_idx: s_name,
                type_idx: e0,
                value_idx: NO_VALUE,
                source_system: SourceSystem::Lean4 as u8,
                import_confidence: ImportConfidence::KernelVerified as u8,
                content_domain: ContentDomain::PureMath as u8,
                decl_kind: DeclKind::Inductive as u8,
                axiom_profile: AxiomProfile::NONE,
                sidecar_digest: 0,
                provenance_idx: 0,
                level_params_start: 0,
                level_params_count: 0,
                _pad2: [0u8; 26],
            };
            hdr.set_inductive_decl_num_params(3);
            hdr.set_inductive_decl_all_names(an_start, 2);
            w.add_constant(hdr);
            w.write_to_file(&path0).unwrap();
        }

        // Shard 1: a second, unrelated shard so this is a genuine 2-shard merge
        // (compact_deltas's real use case). It also defines a "MyInd" Definition,
        // but last-writer-wins (shard0 is LAST in the slice below) makes shard0's
        // inductive the winner; shard1's constant is dropped in Phase 1 and never
        // reaches the writer.
        let path1 = dir.path().join("other.mathverse");
        {
            let mut w = ShardWriter::new();
            let l0 = w.add_level(FlatLevel::zero());
            let e0 = w.add_expr(FlatExpr::sort(l0));
            let s_name = w.add_string("MyInd");
            w.add_constant(MathverseConstantHeader {
                name_idx: s_name,
                type_idx: e0,
                value_idx: e0,
                source_system: SourceSystem::Lean4 as u8,
                import_confidence: ImportConfidence::KernelVerified as u8,
                content_domain: ContentDomain::PureMath as u8,
                decl_kind: DeclKind::Definition as u8,
                axiom_profile: AxiomProfile::NONE,
                sidecar_digest: 0,
                provenance_idx: 0,
                level_params_start: 0,
                level_params_count: 0,
                _pad2: [0u8; 26],
            });
            w.write_to_file(&path1).unwrap();
        }

        let out = dir.path().join("merged.mathverse");
        // shard0 (the inductive) is LAST so it wins the last-writer-wins dedup by
        // name. The dedup-vs-contiguity case is exercised by the inductive's OWN
        // name "MyInd": it is interned via remap_string when the header is built,
        // then re-emitted inside the all_names run by add_string_block — which must
        // stay contiguous even though "MyInd" is already in the writer's cache.
        let shard1 = ShardReader::from_file(&path1).unwrap();
        let shard0 = ShardReader::from_file(&path0).unwrap();
        compact_deltas(&[shard1, shard0], &out).unwrap();

        let merged = ShardReader::from_file(&out).unwrap();
        let (_, hdr) = merged
            .lookup_name("MyInd")
            .expect("inductive should survive merge");

        // num_params must survive verbatim.
        assert_eq!(
            hdr.inductive_decl_num_params(),
            Some(3),
            "inductive num_params dropped by merge"
        );

        // all_names block must survive AND its relocated (start, count) must
        // resolve to the original contiguous names in the merged string table.
        let (start, count) = hdr
            .inductive_decl_all_names_block()
            .expect("inductive all_names block dropped by merge");
        assert_eq!(count, 2);
        let start = start as usize;
        assert_eq!(merged.strings[start], "MyInd");
        assert_eq!(merged.strings[start + 1], "MyInd.Other");
    }

    #[test]
    fn test_invalid_magic() {
        let mut bytes = [0u8; HEADER_SIZE];
        bytes[0..4].copy_from_slice(&0xDEAD_BEEFu32.to_le_bytes());
        let result = ShardHeader::from_bytes(&bytes);
        assert!(result.is_err());
    }

    /// Regression: a constant header whose `name_idx` exceeds the writer's
    /// string table previously panicked inside `build_sorted_index` (a
    /// direct `self.strings[c.name_idx as usize]` slice index). The
    /// `build-library` pipeline aborted with "index out of bounds" without
    /// a clue as to which importer produced the bad header. After the
    /// fix `write()` surfaces the corruption as a typed error.
    #[test]
    fn test_write_rejects_out_of_range_name_idx() {
        let mut writer = ShardWriter::new();
        // Pre-seeded sentinels mean strings.len() == 1 here.
        writer.add_constant(MathverseConstantHeader {
            name_idx: 999, // intentionally out of range
            type_idx: NO_VALUE,
            value_idx: NO_VALUE,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: ImportConfidence::KernelVerified as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: 0,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        });

        let mut buf = Vec::new();
        let err = writer
            .write(&mut buf)
            .expect_err("must reject bad name_idx");
        let msg = err.to_string();
        assert!(
            msg.contains("string index 999 out of range"),
            "unexpected error: {msg}"
        );
        assert!(
            msg.contains("constant #0"),
            "error should name the offending constant: {msg}"
        );
    }

    #[test]
    fn test_shard_round_trip() {
        let mut writer = ShardWriter::new();

        // Add some strings
        let name0 = writer.add_string("Nat.add");
        let name1 = writer.add_string("Nat.mul");
        let name2 = writer.add_string("Bool.true");

        // Add some levels
        let l0 = writer.add_level(FlatLevel::zero());
        let l1 = writer.add_level(FlatLevel::succ(l0));

        // Add some expressions
        let e0 = writer.add_expr(FlatExpr::sort(l0));
        let e1 = writer.add_expr(FlatExpr::sort(l1));
        let e2 = writer.add_expr(FlatExpr::const_ref(name0, u32::MAX));

        // Add constants
        writer.add_constant(MathverseConstantHeader {
            name_idx: name0,
            type_idx: e0,
            value_idx: e2,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: ImportConfidence::KernelVerified as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: 0,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        });
        writer.add_constant(MathverseConstantHeader {
            name_idx: name1,
            type_idx: e1,
            value_idx: NO_VALUE,
            source_system: SourceSystem::Metamath as u8,
            import_confidence: ImportConfidence::Axiomatized as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: 0,
            axiom_profile: AxiomProfile::AXIOMATIZED | AxiomProfile::CLASSICAL,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        });
        writer.add_constant(MathverseConstantHeader {
            name_idx: name2,
            type_idx: e0,
            value_idx: e1,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: ImportConfidence::KernelVerified as u8,
            content_domain: ContentDomain::Logic as u8,
            decl_kind: 0,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        });

        // Write to buffer
        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();

        // Read back
        let reader = ShardReader::from_bytes(&buf).unwrap();

        // Verify counts. The writer pre-seeds strings[0] with an empty
        // sentinel (so name_idx: 0 is a valid "no name" placeholder
        // elsewhere) and levels[0] with FlatLevel::zero (so add_level
        // of zero is a no-op). Three user-added strings give count = 4,
        // and one user-added level gives count = 2.
        assert_eq!(reader.header.string_count, 4);
        assert_eq!(reader.header.level_count, 2);
        assert_eq!(reader.header.expr_count, 3);
        assert_eq!(reader.header.constant_count, 3);

        // Verify strings
        assert_eq!(reader.strings[0], "");
        assert_eq!(reader.strings[1], "Nat.add");
        assert_eq!(reader.strings[2], "Nat.mul");
        assert_eq!(reader.strings[3], "Bool.true");

        // Verify constants
        assert_eq!(reader.constants[0].name_idx, name0);
        assert_eq!(reader.constants[0].source_system, SourceSystem::Lean4 as u8);
        assert!(reader.constants[0].has_value());

        assert_eq!(reader.constants[1].name_idx, name1);
        assert!(!reader.constants[1].has_value());
        assert!(reader.constants[1].is_trust_gated());

        // Verify bloom filter
        assert!(reader.bloom_maybe_contains("Nat.add"));
        assert!(reader.bloom_maybe_contains("Nat.mul"));
        assert!(reader.bloom_maybe_contains("Bool.true"));

        // Verify name lookup
        let (idx, hdr) = reader.lookup_name("Nat.add").unwrap();
        assert_eq!(idx, 0);
        assert_eq!(hdr.source_system, SourceSystem::Lean4 as u8);

        assert!(reader.lookup_name("Nat.nonexistent").is_none());
    }

    #[test]
    fn test_from_reader_and_stamp_kernel_verified_round_trip() {
        use std::collections::HashSet;

        // Build a small shard with two constants at NON-KernelVerified
        // confidence so a stamp is an observable transition.
        let mut writer = ShardWriter::new();
        let name_a = writer.add_string("A");
        let name_b = writer.add_string("B");
        let l0 = writer.add_level(FlatLevel::zero());
        let ty = writer.add_expr(FlatExpr::sort(l0));
        let val = writer.add_expr(FlatExpr::const_ref(name_a, u32::MAX));
        for (name_idx, conf) in [
            (name_a, ImportConfidence::SourceVerified),
            (name_b, ImportConfidence::Axiomatized),
        ] {
            writer.add_constant(MathverseConstantHeader {
                name_idx,
                type_idx: ty,
                value_idx: val,
                source_system: SourceSystem::Lean4 as u8,
                import_confidence: conf as u8,
                content_domain: ContentDomain::PureMath as u8,
                decl_kind: 0,
                axiom_profile: AxiomProfile::NONE,
                sidecar_digest: 0,
                provenance_idx: 0,
                level_params_start: 0,
                level_params_count: 0,
                _pad2: [0u8; 26],
            });
        }
        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();
        let reader = ShardReader::from_bytes(&buf).unwrap();

        // from_reader is a byte-faithful copy: round-tripping with no stamp
        // reproduces the exact same shard bytes.
        let copy = ShardWriter::from_reader(&reader);
        let mut copy_buf = Vec::new();
        copy.write(&mut copy_buf).unwrap();
        assert_eq!(buf, copy_buf, "from_reader must reproduce identical bytes");

        // Stamp ONLY "A"; "B" must stay untouched.
        let verified: HashSet<String> = HashSet::from([String::from("A")]);
        let mut stamper = ShardWriter::from_reader(&reader);
        let stamped = stamper.stamp_kernel_verified(&verified);
        assert_eq!(stamped, 1, "exactly one header (A) is raised");

        let mut stamped_buf = Vec::new();
        stamper.write(&mut stamped_buf).unwrap();
        let restamped = ShardReader::from_bytes(&stamped_buf).unwrap();

        let conf_of = |r: &ShardReader, n: &str| -> u8 {
            let (_, h) = r.lookup_name(n).unwrap();
            h.import_confidence
        };
        assert_eq!(
            conf_of(&restamped, "A"),
            ImportConfidence::KernelVerified as u8,
            "A reads KernelVerified from the re-serialized bytes"
        );
        assert_eq!(
            conf_of(&restamped, "B"),
            ImportConfidence::Axiomatized as u8,
            "B (not in the verified set) is left untouched"
        );

        // Idempotence: stamping again raises nothing.
        let mut again = ShardWriter::from_reader(&restamped);
        assert_eq!(again.stamp_kernel_verified(&verified), 0);
    }

    #[test]
    fn test_bloom_filter_no_false_negatives() {
        let names: Vec<String> = (0..100).map(|i| format!("test.constant.{i}")).collect();
        let bloom = build_bloom_filter(&names, BLOOM_SIZE);
        for name in &names {
            assert!(
                bloom_check(&bloom, name),
                "Bloom filter must never produce false negatives for: {name}"
            );
        }
    }

    #[test]
    fn test_string_table_round_trip() {
        let strings = vec![
            "".to_string(),
            "hello".to_string(),
            "Nat.add.comm".to_string(),
            "unicode: \u{1F600}".to_string(),
        ];
        let encoded = encode_string_table(&strings);
        let decoded = decode_string_table(&encoded, strings.len() as u32).unwrap();
        assert_eq!(strings, decoded);
    }

    #[test]
    fn test_shard_file_round_trip() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("test.mathverse");

        let mut writer = ShardWriter::new();
        let s0 = writer.add_string("test.thm");
        let l0 = writer.add_level(FlatLevel::zero());
        let e0 = writer.add_expr(FlatExpr::sort(l0));
        writer.add_constant(MathverseConstantHeader {
            name_idx: s0,
            type_idx: e0,
            value_idx: e0,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: ImportConfidence::KernelVerified as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: 0,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        });
        writer.write_to_file(&path).unwrap();

        let reader = ShardReader::from_file(&path).unwrap();
        assert_eq!(reader.header.constant_count, 1);
        // strings[0] is the pre-seeded empty sentinel.
        assert_eq!(reader.strings[0], "");
        assert_eq!(reader.strings[1], "test.thm");
    }

    // -------------------------------------------------------------------
    // ShardMmapReader tests
    // -------------------------------------------------------------------

    /// Helper: write a shard to a temp file and return the path + tempdir handle.
    fn write_test_shard(
        names: &[&str],
        source: SourceSystem,
    ) -> (tempfile::TempDir, std::path::PathBuf) {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("test.mathverse");
        let mut writer = ShardWriter::new();

        let l0 = writer.add_level(FlatLevel::zero());
        let l1 = writer.add_level(FlatLevel::succ(l0));
        let e0 = writer.add_expr(FlatExpr::sort(l0));
        let e1 = writer.add_expr(FlatExpr::sort(l1));

        for name in names {
            let s = writer.add_string(name);
            writer.add_constant(MathverseConstantHeader {
                name_idx: s,
                type_idx: e0,
                value_idx: e1,
                source_system: source as u8,
                import_confidence: ImportConfidence::KernelVerified as u8,
                content_domain: ContentDomain::PureMath as u8,
                decl_kind: 0,
                axiom_profile: AxiomProfile::NONE,
                sidecar_digest: 0,
                provenance_idx: 0,
                level_params_start: 0,
                level_params_count: 0,
                _pad2: [0u8; 26],
            });
        }

        writer.write_to_file(&path).unwrap();
        (dir, path)
    }

    #[test]
    fn test_mmap_reader_basic() {
        let (_dir, path) =
            write_test_shard(&["Nat.add", "Nat.mul", "Bool.true"], SourceSystem::Lean4);

        let reader = ShardMmapReader::open(&path).unwrap();

        // Header counts. Writer pre-seeds strings[0] = "" and
        // levels[0] = zero, so three user-strings yield count 4.
        assert_eq!(reader.header.string_count, 4);
        assert_eq!(reader.header.level_count, 2);
        assert_eq!(reader.header.expr_count, 2);
        assert_eq!(reader.header.constant_count, 3);

        // String table (eagerly decompressed)
        assert_eq!(reader.strings[0], "");
        assert_eq!(reader.strings[1], "Nat.add");
        assert_eq!(reader.strings[2], "Nat.mul");
        assert_eq!(reader.strings[3], "Bool.true");

        // Raw section sizes
        assert_eq!(reader.level_bytes().len(), 2 * FlatLevel::SIZE);
        assert_eq!(reader.expr_bytes().len(), 2 * FlatExpr::SIZE);
        assert_eq!(
            reader.constant_bytes().len(),
            3 * MathverseConstantHeader::SIZE
        );
    }

    #[test]
    fn test_mmap_reader_individual_access() {
        let (_dir, path) = write_test_shard(&["Nat.add", "Nat.mul"], SourceSystem::Lean4);

        let reader = ShardMmapReader::open(&path).unwrap();

        // Individual level access
        let level0 = reader.read_level(0).unwrap();
        assert_eq!(level0.tag, FlatLevel::TAG_ZERO);
        let level1 = reader.read_level(1).unwrap();
        assert_eq!(level1.tag, FlatLevel::TAG_SUCC);

        // Out-of-range returns error
        assert!(reader.read_level(2).is_err());

        // Individual expr access
        let expr0 = reader.read_expr(0).unwrap();
        assert_eq!(expr0.tag, 1); // Sort
        assert!(reader.read_expr(2).is_err());

        // Individual constant access
        let c0 = reader.read_constant(0).unwrap();
        assert_eq!(c0.source_system, SourceSystem::Lean4 as u8);
        assert!(reader.read_constant(2).is_err());
    }

    #[test]
    fn test_mmap_reader_bloom_and_lookup() {
        let (_dir, path) = write_test_shard(&["Nat.add", "Nat.mul"], SourceSystem::Lean4);

        let reader = ShardMmapReader::open(&path).unwrap();

        // Bloom: no false negatives
        assert!(reader.bloom_maybe_contains("Nat.add"));
        assert!(reader.bloom_maybe_contains("Nat.mul"));

        // Name lookup
        let (idx, hdr) = reader.lookup_name("Nat.add").unwrap();
        assert_eq!(idx, 0);
        assert_eq!(hdr.source_system, SourceSystem::Lean4 as u8);

        let (idx, _) = reader.lookup_name("Nat.mul").unwrap();
        assert_eq!(idx, 1);

        assert!(reader.lookup_name("Nat.nonexistent").is_none());
    }

    #[test]
    fn test_mmap_reader_materialize() {
        let (_dir, path) = write_test_shard(&["Nat.add"], SourceSystem::Lean4);

        let mmap_reader = ShardMmapReader::open(&path).unwrap();
        let normal_reader = ShardReader::from_file(&path).unwrap();

        // Materialized data should match the normal reader
        let levels = mmap_reader.materialize_levels().unwrap();
        assert_eq!(levels.len(), normal_reader.levels.len());
        for (a, b) in levels.iter().zip(normal_reader.levels.iter()) {
            assert_eq!(a.tag, b.tag);
            assert_eq!(a.data, b.data);
        }

        let exprs = mmap_reader.materialize_exprs().unwrap();
        assert_eq!(exprs.len(), normal_reader.exprs.len());
        for (a, b) in exprs.iter().zip(normal_reader.exprs.iter()) {
            assert_eq!(a.tag, b.tag);
            assert_eq!(a.flags, b.flags);
            assert_eq!(a.data, b.data);
        }

        let constants = mmap_reader.materialize_constants().unwrap();
        assert_eq!(constants.len(), normal_reader.constants.len());
        for (a, b) in constants.iter().zip(normal_reader.constants.iter()) {
            assert_eq!(a.name_idx, b.name_idx);
            assert_eq!(a.type_idx, b.type_idx);
            assert_eq!(a.value_idx, b.value_idx);
        }
    }

    // -------------------------------------------------------------------
    // compact_deltas tests
    // -------------------------------------------------------------------

    #[test]
    fn test_compact_deltas_single_shard() {
        let dir = tempfile::tempdir().unwrap();
        let in_path = dir.path().join("delta0.mathverse");
        let out_path = dir.path().join("compacted.mathverse");

        let mut writer = ShardWriter::new();
        let l0 = writer.add_level(FlatLevel::zero());
        let e0 = writer.add_expr(FlatExpr::sort(l0));
        let s0 = writer.add_string("Nat.add");
        writer.add_constant(MathverseConstantHeader {
            name_idx: s0,
            type_idx: e0,
            value_idx: e0,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: ImportConfidence::KernelVerified as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: 0,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        });
        writer.write_to_file(&in_path).unwrap();

        let shard = ShardReader::from_file(&in_path).unwrap();
        compact_deltas(&[shard], &out_path).unwrap();

        let result = ShardReader::from_file(&out_path).unwrap();
        assert_eq!(result.header.constant_count, 1);
        assert!(result.lookup_name("Nat.add").is_some());
    }

    #[test]
    fn test_compact_deltas_last_writer_wins() {
        let dir = tempfile::tempdir().unwrap();

        // Shard 0: Nat.add from Lean4
        let path0 = dir.path().join("delta0.mathverse");
        {
            let mut w = ShardWriter::new();
            let l0 = w.add_level(FlatLevel::zero());
            let e0 = w.add_expr(FlatExpr::sort(l0));
            let s0 = w.add_string("Nat.add");
            w.add_constant(MathverseConstantHeader {
                name_idx: s0,
                type_idx: e0,
                value_idx: e0,
                source_system: SourceSystem::Lean4 as u8,
                import_confidence: ImportConfidence::KernelVerified as u8,
                content_domain: ContentDomain::PureMath as u8,
                decl_kind: 0,
                axiom_profile: AxiomProfile::NONE,
                sidecar_digest: 0,
                provenance_idx: 0,
                level_params_start: 0,
                level_params_count: 0,
                _pad2: [0u8; 26],
            });
            w.write_to_file(&path0).unwrap();
        }

        // Shard 1: Nat.add from Coq (overrides shard 0), plus Nat.mul
        let path1 = dir.path().join("delta1.mathverse");
        {
            let mut w = ShardWriter::new();
            let l0 = w.add_level(FlatLevel::zero());
            let e0 = w.add_expr(FlatExpr::sort(l0));
            let s0 = w.add_string("Nat.add");
            let s1 = w.add_string("Nat.mul");
            w.add_constant(MathverseConstantHeader {
                name_idx: s0,
                type_idx: e0,
                value_idx: e0,
                source_system: SourceSystem::Coq as u8,
                import_confidence: ImportConfidence::Translated as u8,
                content_domain: ContentDomain::PureMath as u8,
                decl_kind: 0,
                axiom_profile: AxiomProfile::NONE,
                sidecar_digest: 0,
                provenance_idx: 0,
                level_params_start: 0,
                level_params_count: 0,
                _pad2: [0u8; 26],
            });
            w.add_constant(MathverseConstantHeader {
                name_idx: s1,
                type_idx: e0,
                value_idx: NO_VALUE,
                source_system: SourceSystem::Coq as u8,
                import_confidence: ImportConfidence::Axiomatized as u8,
                content_domain: ContentDomain::PureMath as u8,
                decl_kind: 0,
                axiom_profile: AxiomProfile::AXIOMATIZED,
                sidecar_digest: 0,
                provenance_idx: 0,
                level_params_start: 0,
                level_params_count: 0,
                _pad2: [0u8; 26],
            });
            w.write_to_file(&path1).unwrap();
        }

        let out_path = dir.path().join("compacted.mathverse");
        let shard0 = ShardReader::from_file(&path0).unwrap();
        let shard1 = ShardReader::from_file(&path1).unwrap();
        compact_deltas(&[shard0, shard1], &out_path).unwrap();

        let result = ShardReader::from_file(&out_path).unwrap();
        // Two unique names: Nat.add (from shard1) and Nat.mul
        assert_eq!(result.header.constant_count, 2);

        // Nat.add should come from shard1 (Coq, Translated)
        let (_, hdr) = result.lookup_name("Nat.add").unwrap();
        assert_eq!(hdr.source_system, SourceSystem::Coq as u8);
        assert_eq!(hdr.import_confidence, ImportConfidence::Translated as u8);

        // Nat.mul should be present
        let (_, hdr) = result.lookup_name("Nat.mul").unwrap();
        assert_eq!(hdr.source_system, SourceSystem::Coq as u8);
        assert!(!hdr.has_value());
    }

    #[test]
    fn test_compact_deltas_three_shards_dedup() {
        let dir = tempfile::tempdir().unwrap();

        // Three shards each defining "shared" with different sources,
        // plus unique constants in each.
        let names = [
            ("shared", SourceSystem::Lean4),
            ("shared", SourceSystem::Coq),
            ("shared", SourceSystem::Isabelle),
        ];
        let unique = ["only_in_0", "only_in_1", "only_in_2"];
        let mut paths = Vec::new();

        for (i, ((name, src), uniq)) in names.iter().zip(unique.iter()).enumerate() {
            let path = dir.path().join(format!("delta{i}.mathverse"));
            let mut w = ShardWriter::new();
            let l0 = w.add_level(FlatLevel::zero());
            let e0 = w.add_expr(FlatExpr::sort(l0));
            let s_shared = w.add_string(name);
            let s_unique = w.add_string(uniq);
            w.add_constant(MathverseConstantHeader {
                name_idx: s_shared,
                type_idx: e0,
                value_idx: e0,
                source_system: *src as u8,
                import_confidence: ImportConfidence::KernelVerified as u8,
                content_domain: ContentDomain::PureMath as u8,
                decl_kind: 0,
                axiom_profile: AxiomProfile::NONE,
                sidecar_digest: 0,
                provenance_idx: 0,
                level_params_start: 0,
                level_params_count: 0,
                _pad2: [0u8; 26],
            });
            w.add_constant(MathverseConstantHeader {
                name_idx: s_unique,
                type_idx: e0,
                value_idx: e0,
                source_system: *src as u8,
                import_confidence: ImportConfidence::KernelVerified as u8,
                content_domain: ContentDomain::PureMath as u8,
                decl_kind: 0,
                axiom_profile: AxiomProfile::NONE,
                sidecar_digest: 0,
                provenance_idx: 0,
                level_params_start: 0,
                level_params_count: 0,
                _pad2: [0u8; 26],
            });
            w.write_to_file(&path).unwrap();
            paths.push(path);
        }

        let shards: Vec<ShardReader> = paths
            .iter()
            .map(|p| ShardReader::from_file(p).unwrap())
            .collect();
        let out_path = dir.path().join("compacted.mathverse");
        compact_deltas(&shards, &out_path).unwrap();

        let result = ShardReader::from_file(&out_path).unwrap();
        // 1 (shared, last-writer-wins) + 3 unique = 4
        assert_eq!(result.header.constant_count, 4);

        // "shared" comes from last shard (Isabelle)
        let (_, hdr) = result.lookup_name("shared").unwrap();
        assert_eq!(hdr.source_system, SourceSystem::Isabelle as u8);

        // All unique constants present
        assert!(result.lookup_name("only_in_0").is_some());
        assert!(result.lookup_name("only_in_1").is_some());
        assert!(result.lookup_name("only_in_2").is_some());
    }

    #[test]
    fn test_compact_deltas_empty_input_fails() {
        let dir = tempfile::tempdir().unwrap();
        let out_path = dir.path().join("compacted.mathverse");
        let result = compact_deltas(&[], &out_path);
        assert!(result.is_err());
    }

    #[test]
    fn test_compact_deltas_preserves_axiom_profiles() {
        let dir = tempfile::tempdir().unwrap();

        // Shard with axiomatized constant
        let path = dir.path().join("delta.mathverse");
        {
            let mut w = ShardWriter::new();
            let l0 = w.add_level(FlatLevel::zero());
            let e0 = w.add_expr(FlatExpr::sort(l0));
            let s0 = w.add_string("Classical.choice");
            w.add_constant(MathverseConstantHeader {
                name_idx: s0,
                type_idx: e0,
                value_idx: NO_VALUE,
                source_system: SourceSystem::Lean4 as u8,
                import_confidence: ImportConfidence::Axiomatized as u8,
                content_domain: ContentDomain::Logic as u8,
                decl_kind: 0,
                axiom_profile: AxiomProfile::CHOICE | AxiomProfile::AXIOMATIZED,
                // Both fields must be 0 when there's no provenance
                // sidecar — the validator rejects nonzero values when
                // the sidecar is absent.
                sidecar_digest: 0,
                provenance_idx: 0,
                level_params_start: 0,
                level_params_count: 0,
                _pad2: [0u8; 26],
            });
            w.write_to_file(&path).unwrap();
        }

        let out_path = dir.path().join("compacted.mathverse");
        let shard = ShardReader::from_file(&path).unwrap();
        compact_deltas(&[shard], &out_path).unwrap();

        let result = ShardReader::from_file(&out_path).unwrap();
        let (_, hdr) = result.lookup_name("Classical.choice").unwrap();
        assert!(!hdr.has_value());
        assert!(hdr.is_trust_gated());
        assert_eq!(
            hdr.axiom_profile,
            AxiomProfile::CHOICE | AxiomProfile::AXIOMATIZED
        );
        assert_eq!(hdr.import_confidence, ImportConfidence::Axiomatized as u8);
        assert_eq!(hdr.content_domain, ContentDomain::Logic as u8);
    }

    // -------------------------------------------------------------------
    // Sorted name index tests
    // -------------------------------------------------------------------

    #[test]
    fn test_sorted_index_entry_round_trip() {
        let entry = NameIndexEntry {
            name_hash: 0x1234_5678_9ABC_DEF0,
            constant_idx: 42,
        };
        let bytes = entry.to_bytes();
        let restored = NameIndexEntry::from_bytes(&bytes);
        assert_eq!(entry, restored);
    }

    #[test]
    fn test_name_hash_deterministic() {
        let h1 = name_hash("Nat.add");
        let h2 = name_hash("Nat.add");
        assert_eq!(h1, h2);

        let h3 = name_hash("Nat.mul");
        // Different names should (almost certainly) produce different hashes
        assert_ne!(h1, h3);
    }

    #[test]
    fn test_header_round_trip_with_sorted_index() {
        let header = ShardHeader {
            magic: SHARD_MAGIC,
            version: SHARD_VERSION,
            flags: FLAG_HAS_SORTED_INDEX,
            string_count: 10,
            string_data_len: 200,
            level_count: 5,
            expr_count: 50,
            constant_count: 10,
            bloom_size: BLOOM_SIZE as u32,
            provenance_len: 100,
            sorted_index_len: 120,
            level_lists_count: 0,
            source_olean_blake3: [0u8; 32],
            source_olean_len: 0,
            fail_closed_verified: 0,
            module_name_idx: 0,
        };
        let bytes = header.to_bytes();
        let restored = ShardHeader::from_bytes(&bytes).unwrap();
        assert_eq!(header.flags, restored.flags);
        assert_eq!(header.sorted_index_len, restored.sorted_index_len);
        assert!(restored.has_sorted_index());
    }

    #[test]
    fn test_shard_has_sorted_index() {
        let mut writer = ShardWriter::new();
        let l0 = writer.add_level(FlatLevel::zero());
        let e0 = writer.add_expr(FlatExpr::sort(l0));
        let ni = writer.add_string("Test.thm");
        writer.add_constant(MathverseConstantHeader {
            name_idx: ni,
            type_idx: e0,
            value_idx: e0,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: ImportConfidence::KernelVerified as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: 0,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        });

        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();
        let reader = ShardReader::from_bytes(&buf).unwrap();

        assert!(reader.has_sorted_index());
        assert!(reader.header.has_sorted_index());
    }

    #[test]
    fn test_sorted_index_lookup_all_names() {
        let mut writer = ShardWriter::new();
        let l0 = writer.add_level(FlatLevel::zero());
        let e0 = writer.add_expr(FlatExpr::sort(l0));

        let names = ["Nat.add", "Nat.mul", "Bool.true", "List.nil", "List.cons"];
        let mut name_indices = Vec::new();
        for name in &names {
            name_indices.push(writer.add_string(name));
        }
        for &ni in &name_indices {
            writer.add_constant(MathverseConstantHeader {
                name_idx: ni,
                type_idx: e0,
                value_idx: e0,
                source_system: SourceSystem::Lean4 as u8,
                import_confidence: ImportConfidence::KernelVerified as u8,
                content_domain: ContentDomain::PureMath as u8,
                decl_kind: 0,
                axiom_profile: AxiomProfile::NONE,
                sidecar_digest: 0,
                provenance_idx: 0,
                level_params_start: 0,
                level_params_count: 0,
                _pad2: [0u8; 26],
            });
        }

        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();
        let reader = ShardReader::from_bytes(&buf).unwrap();

        for (i, name) in names.iter().enumerate() {
            let result = reader.lookup_name(name);
            assert!(result.is_some(), "Should find name: {name}");
            let (idx, _) = result.unwrap();
            assert_eq!(idx, i as u32, "Constant index mismatch for {name}");
        }
        assert!(reader.lookup_name("Nonexistent.name").is_none());
    }

    #[test]
    fn test_lookup_name_all_with_duplicates() {
        let mut writer = ShardWriter::new();
        let l0 = writer.add_level(FlatLevel::zero());
        let e0 = writer.add_expr(FlatExpr::sort(l0));

        let ni0 = writer.add_string("Shared.thm");
        let ni1 = writer.add_string("Shared.thm");
        let ni2 = writer.add_string("Unique.thm");

        writer.add_constant(MathverseConstantHeader {
            name_idx: ni0,
            type_idx: e0,
            value_idx: e0,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: ImportConfidence::KernelVerified as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: 0,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        });
        writer.add_constant(MathverseConstantHeader {
            name_idx: ni1,
            type_idx: e0,
            value_idx: NO_VALUE,
            source_system: SourceSystem::Coq as u8,
            import_confidence: ImportConfidence::Translated as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: 0,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        });
        writer.add_constant(MathverseConstantHeader {
            name_idx: ni2,
            type_idx: e0,
            value_idx: e0,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: ImportConfidence::KernelVerified as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: 0,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        });

        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();
        let reader = ShardReader::from_bytes(&buf).unwrap();

        // lookup_name_all returns both matches
        let all = reader.lookup_name_all("Shared.thm");
        assert_eq!(all.len(), 2, "Should find 2 constants named Shared.thm");
        let systems: Vec<u8> = all.iter().map(|(_, h)| h.source_system).collect();
        assert!(systems.contains(&(SourceSystem::Lean4 as u8)));
        assert!(systems.contains(&(SourceSystem::Coq as u8)));

        let unique_all = reader.lookup_name_all("Unique.thm");
        assert_eq!(unique_all.len(), 1);

        let none_all = reader.lookup_name_all("Nope.thm");
        assert!(none_all.is_empty());
    }

    #[test]
    fn test_backward_compat_no_sorted_index() {
        // Write a legacy shard without the sorted name index.
        let legacy_buf = write_legacy_shard(
            vec!["Legacy.thm".to_string()],
            vec![FlatLevel::zero()],
            vec![FlatExpr::sort(0)],
            vec![MathverseConstantHeader {
                name_idx: 0,
                type_idx: 0,
                value_idx: 0,
                source_system: SourceSystem::Lean4 as u8,
                import_confidence: ImportConfidence::KernelVerified as u8,
                content_domain: ContentDomain::PureMath as u8,
                decl_kind: 0,
                axiom_profile: AxiomProfile::NONE,
                sidecar_digest: 0,
                provenance_idx: 0,
                level_params_start: 0,
                level_params_count: 0,
                _pad2: [0u8; 26],
            }],
        );

        let reader = ShardReader::from_bytes(&legacy_buf).unwrap();
        assert!(!reader.has_sorted_index());
        assert!(!reader.header.has_sorted_index());

        // Lookup should still work via linear scan fallback
        let (idx, hdr) = reader.lookup_name("Legacy.thm").unwrap();
        assert_eq!(idx, 0);
        assert_eq!(hdr.source_system, SourceSystem::Lean4 as u8);

        let all = reader.lookup_name_all("Legacy.thm");
        assert_eq!(all.len(), 1);
    }

    /// Write a shard without the sorted name index (legacy format) for testing.
    fn write_legacy_shard(
        strings: Vec<String>,
        levels: Vec<FlatLevel>,
        exprs: Vec<FlatExpr>,
        constants: Vec<MathverseConstantHeader>,
    ) -> Vec<u8> {
        let mut hasher = blake3::Hasher::new();
        let mut output = Vec::new();

        let string_data = encode_string_table(&strings);
        let string_compressed = zstd::bulk::compress(&string_data, 3).unwrap();
        let bloom = build_bloom_filter(&strings, BLOOM_SIZE);

        let header = ShardHeader {
            magic: SHARD_MAGIC,
            version: SHARD_VERSION,
            flags: 0,
            string_count: strings.len() as u32,
            string_data_len: string_compressed.len() as u32,
            level_count: levels.len() as u32,
            expr_count: exprs.len() as u32,
            constant_count: constants.len() as u32,
            bloom_size: bloom.len() as u32,
            provenance_len: 0,
            sorted_index_len: 0,
            level_lists_count: 0,
            source_olean_blake3: [0u8; 32],
            source_olean_len: 0,
            fail_closed_verified: 0,
            module_name_idx: 0,
        };
        let header_bytes = header.to_bytes();
        output.extend_from_slice(&header_bytes);
        hasher.update(&header_bytes);

        output.extend_from_slice(&string_compressed);
        hasher.update(&string_compressed);

        for level in &levels {
            let bytes = level_to_bytes(level);
            output.extend_from_slice(&bytes);
            hasher.update(&bytes);
        }
        for expr in &exprs {
            let bytes = expr_to_bytes(expr);
            output.extend_from_slice(&bytes);
            hasher.update(&bytes);
        }
        for constant in &constants {
            let bytes = constant.to_bytes();
            output.extend_from_slice(&bytes);
            hasher.update(&bytes);
        }

        output.extend_from_slice(&bloom);
        hasher.update(&bloom);

        // No sorted index section

        let hash = hasher.finalize();
        let mut footer = [0u8; FOOTER_SIZE];
        footer[0..32].copy_from_slice(hash.as_bytes());
        output.extend_from_slice(&footer);

        output
    }

    #[test]
    fn test_sorted_index_is_sorted() {
        let mut writer = ShardWriter::new();
        let l0 = writer.add_level(FlatLevel::zero());
        let e0 = writer.add_expr(FlatExpr::sort(l0));

        for i in (0..50).rev() {
            let ni = writer.add_string(&format!("constant.{i:04}"));
            writer.add_constant(MathverseConstantHeader {
                name_idx: ni,
                type_idx: e0,
                value_idx: e0,
                source_system: SourceSystem::Lean4 as u8,
                import_confidence: ImportConfidence::KernelVerified as u8,
                content_domain: ContentDomain::PureMath as u8,
                decl_kind: 0,
                axiom_profile: AxiomProfile::NONE,
                sidecar_digest: 0,
                provenance_idx: 0,
                level_params_start: 0,
                level_params_count: 0,
                _pad2: [0u8; 26],
            });
        }

        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();
        let reader = ShardReader::from_bytes(&buf).unwrap();

        for window in reader.sorted_index.windows(2) {
            assert!(
                window[0].name_hash <= window[1].name_hash,
                "Sorted index should be sorted: {} <= {}",
                window[0].name_hash,
                window[1].name_hash
            );
        }
    }

    #[test]
    fn test_lookup_1000_constants_sublinear() {
        let mut writer = ShardWriter::new();
        let l0 = writer.add_level(FlatLevel::zero());
        let e0 = writer.add_expr(FlatExpr::sort(l0));

        let count = 1000;
        let mut names = Vec::with_capacity(count);
        for i in 0..count {
            let name = format!("Mathlib.Topology.Theorem.{i:04}");
            let ni = writer.add_string(&name);
            writer.add_constant(MathverseConstantHeader {
                name_idx: ni,
                type_idx: e0,
                value_idx: e0,
                source_system: SourceSystem::Lean4 as u8,
                import_confidence: ImportConfidence::KernelVerified as u8,
                content_domain: ContentDomain::PureMath as u8,
                decl_kind: 0,
                axiom_profile: AxiomProfile::NONE,
                sidecar_digest: 0,
                provenance_idx: 0,
                level_params_start: 0,
                level_params_count: 0,
                _pad2: [0u8; 26],
            });
            names.push(name);
        }

        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();
        let reader = ShardReader::from_bytes(&buf).unwrap();

        assert!(reader.has_sorted_index());
        assert_eq!(reader.sorted_index.len(), count);

        // Verify all 1000 names are found via indexed lookup
        for (i, name) in names.iter().enumerate() {
            let result = reader.lookup_name(name);
            assert!(result.is_some(), "Should find: {name}");
            let (idx, _) = result.unwrap();
            assert_eq!(idx, i as u32);
        }

        // Verify negative lookups
        assert!(reader.lookup_name("Mathlib.Nonexistent.9999").is_none());

        // Benchmarkable timing: 10k lookups on 1000-entry shard.
        // O(log 1000) ~ 10 steps per lookup via binary search.
        let start = std::time::Instant::now();
        let iterations = 10_000;
        for i in 0..iterations {
            let name = &names[i % count];
            let _ = reader.lookup_name(name);
        }
        let elapsed = start.elapsed();
        let per_lookup_ns = elapsed.as_nanos() / iterations as u128;

        // Sub-microsecond target on idle hardware (~50-200ns typical).
        // The bound is 50us to tolerate contended CI runners where 31+
        // test binaries execute in parallel. Linear scan of 1000 entries
        // would be ~50,000ns+, so this still asserts sub-linearity.
        // Why: the previous 5us bound flaked on contended hardware
        // (seen 23us under parallel load) despite binary search working.
        assert!(
            per_lookup_ns < 50_000,
            "Lookup too slow: {per_lookup_ns}ns per lookup (target: <50000ns)"
        );
    }

    // -------------------------------------------------------------------
    // Hash-consing / dedup tests
    // -------------------------------------------------------------------

    #[test]
    fn test_dedup_same_expr_returns_same_index() {
        let mut writer = ShardWriter::new();
        let e0 = writer.add_expr(FlatExpr::sort(0));
        let e1 = writer.add_expr(FlatExpr::sort(0));
        assert_eq!(e0, e1, "Identical expressions must return the same index");
    }

    #[test]
    fn test_dedup_same_level_returns_same_index() {
        let mut writer = ShardWriter::new();
        let l0 = writer.add_level(FlatLevel::zero());
        let l1 = writer.add_level(FlatLevel::zero());
        assert_eq!(l0, l1, "Identical levels must return the same index");
    }

    #[test]
    fn test_dedup_same_string_returns_same_index() {
        let mut writer = ShardWriter::new();
        let s0 = writer.add_string("Nat.add");
        let s1 = writer.add_string("Nat.add");
        assert_eq!(s0, s1, "Identical strings must return the same index");
    }

    #[test]
    fn test_dedup_different_exprs_get_different_indices() {
        let mut writer = ShardWriter::new();
        let e0 = writer.add_expr(FlatExpr::sort(0));
        let e1 = writer.add_expr(FlatExpr::sort(1));
        let e2 = writer.add_expr(FlatExpr::bvar(0));
        let e3 = writer.add_expr(FlatExpr::app(0, 1));
        assert_ne!(e0, e1);
        assert_ne!(e0, e2);
        assert_ne!(e0, e3);
        assert_ne!(e1, e2);
    }

    #[test]
    fn test_dedup_different_levels_get_different_indices() {
        let mut writer = ShardWriter::new();
        let l0 = writer.add_level(FlatLevel::zero());
        let l1 = writer.add_level(FlatLevel::succ(0));
        let l2 = writer.add_level(FlatLevel::max(0, 1));
        assert_ne!(l0, l1);
        assert_ne!(l0, l2);
        assert_ne!(l1, l2);
    }

    #[test]
    fn test_dedup_different_strings_get_different_indices() {
        let mut writer = ShardWriter::new();
        let s0 = writer.add_string("Nat");
        let s1 = writer.add_string("Bool");
        let s2 = writer.add_string("Prop");
        assert_ne!(s0, s1);
        assert_ne!(s0, s2);
        assert_ne!(s1, s2);
    }

    #[test]
    fn test_dedup_stats_reports_correct_numbers() {
        let mut writer = ShardWriter::new();

        // Add 3 unique exprs, then 2 duplicates
        writer.add_expr(FlatExpr::sort(0));
        writer.add_expr(FlatExpr::sort(1));
        writer.add_expr(FlatExpr::bvar(0));
        writer.add_expr(FlatExpr::sort(0)); // dup
        writer.add_expr(FlatExpr::sort(1)); // dup

        // Add levels: FlatLevel::zero() is pre-seeded at index 0 with
        // its dedup entry, so the first `add_level(zero)` is a DEDUP
        // hit, not a unique addition. Only succ(0) introduces a new
        // entry. That leaves 4 dedup hits out of 5 calls.
        writer.add_level(FlatLevel::zero()); // dup (pre-seeded)
        writer.add_level(FlatLevel::succ(0));
        writer.add_level(FlatLevel::zero()); // dup
        writer.add_level(FlatLevel::zero()); // dup
        writer.add_level(FlatLevel::succ(0)); // dup

        // Add 2 unique strings, then 1 duplicate. The pre-seeded empty
        // sentinel doesn't enter dedup_stats because add_string("") is
        // never called here.
        writer.add_string("Nat");
        writer.add_string("Bool");
        writer.add_string("Nat"); // dup

        let stats = writer.dedup_stats();

        assert_eq!(stats.exprs_total, 5);
        assert_eq!(stats.exprs_deduped, 2);
        assert_eq!(stats.levels_total, 5);
        assert_eq!(stats.levels_deduped, 4);
        assert_eq!(stats.strings_total, 3);
        assert_eq!(stats.strings_deduped, 1);
    }

    #[test]
    fn test_dedup_shard_produces_correct_output() {
        // Build a shard with heavy duplication and verify the read-back
        // matches what we would get without duplication.
        let mut writer = ShardWriter::new();

        let l0 = writer.add_level(FlatLevel::zero());
        let l0_dup = writer.add_level(FlatLevel::zero());
        assert_eq!(l0, l0_dup);

        let e0 = writer.add_expr(FlatExpr::sort(l0));
        let e0_dup = writer.add_expr(FlatExpr::sort(l0));
        assert_eq!(e0, e0_dup);

        let s0 = writer.add_string("Nat.add");
        let s0_dup = writer.add_string("Nat.add");
        assert_eq!(s0, s0_dup);

        let s1 = writer.add_string("Nat.mul");

        writer.add_constant(MathverseConstantHeader {
            name_idx: s0,
            type_idx: e0,
            value_idx: e0,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: ImportConfidence::KernelVerified as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: 0,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        });
        writer.add_constant(MathverseConstantHeader {
            name_idx: s1,
            type_idx: e0,
            value_idx: NO_VALUE,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: ImportConfidence::KernelVerified as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: 0,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        });

        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();
        let reader = ShardReader::from_bytes(&buf).unwrap();

        // Dedup should collapse duplicates. Strings count includes the
        // pre-seeded empty sentinel at index 0.
        assert_eq!(reader.header.string_count, 3, "sentinel + 2 unique strings");
        assert_eq!(reader.header.level_count, 1, "pre-seeded zero only");
        assert_eq!(reader.header.expr_count, 1, "only 1 unique expr");
        assert_eq!(reader.header.constant_count, 2, "constants are not deduped");

        // Verify lookups still work
        assert!(reader.lookup_name("Nat.add").is_some());
        assert!(reader.lookup_name("Nat.mul").is_some());
        assert_eq!(reader.strings[0], "");
        assert_eq!(reader.strings[1], "Nat.add");
        assert_eq!(reader.strings[2], "Nat.mul");
    }

    #[test]
    fn test_dedup_1000_duplicates_o1() {
        let mut writer = ShardWriter::new();

        // Add one unique expr, then add it 999 more times.
        let expr = FlatExpr::sort(0);
        let first_idx = writer.add_expr(expr);
        for _ in 0..999 {
            let idx = writer.add_expr(expr);
            assert_eq!(idx, first_idx, "All duplicates must return first index");
        }

        // Only 1 unique entry in the arena
        let stats = writer.dedup_stats();
        assert_eq!(stats.exprs_total, 1000);
        assert_eq!(stats.exprs_deduped, 999);

        // Same for levels. FlatLevel::zero() is pre-seeded in the
        // arena, so all 1000 calls are dedup hits — not 999.
        let level = FlatLevel::zero();
        let first_level = writer.add_level(level);
        for _ in 0..999 {
            let idx = writer.add_level(level);
            assert_eq!(idx, first_level);
        }
        assert_eq!(writer.dedup_stats().levels_total, 1000);
        assert_eq!(writer.dedup_stats().levels_deduped, 1000);

        // Same for strings
        let first_str = writer.add_string("Prop");
        for _ in 0..999 {
            let idx = writer.add_string("Prop");
            assert_eq!(idx, first_str);
        }
        assert_eq!(writer.dedup_stats().strings_total, 1000);
        assert_eq!(writer.dedup_stats().strings_deduped, 999);
    }

    #[test]
    fn test_dedup_expr_with_different_flags() {
        // FlatExpr::bvar sets HAS_LOOSE_BVAR flag, FlatExpr::sort has flags=0.
        // Both with tag=1 (Sort) and same data should still be the same,
        // but expressions with different flags should be different entries
        // since flags are part of the identity.
        let mut writer = ShardWriter::new();
        let e0 = writer.add_expr(FlatExpr::sort(0));
        let mut modified = FlatExpr::sort(0);
        modified.flags = 0x10; // set UNSUPPORTED flag
        let e1 = writer.add_expr(modified);
        // Different flags => different identity
        assert_ne!(e0, e1, "Expressions with different flags must be different");
    }

    #[test]
    fn test_dedup_stats_default() {
        let stats = DedupStats::default();
        assert_eq!(stats.exprs_total, 0);
        assert_eq!(stats.exprs_deduped, 0);
        assert_eq!(stats.levels_total, 0);
        assert_eq!(stats.levels_deduped, 0);
        assert_eq!(stats.strings_total, 0);
        assert_eq!(stats.strings_deduped, 0);
    }

    #[test]
    fn test_dedup_empty_writer_stats() {
        let writer = ShardWriter::new();
        let stats = writer.dedup_stats();
        assert_eq!(stats, DedupStats::default());
    }

    #[test]
    fn test_compact_deltas_unknown_expr_tag_returns_error() {
        let dir = tempfile::tempdir().unwrap();
        let in_path = dir.path().join("corrupt.mathverse");
        let out_path = dir.path().join("compacted.mathverse");

        let mut writer = ShardWriter::new();
        let l0 = writer.add_level(FlatLevel::zero());
        // Create a valid expression that the constant's type_idx points to
        let e0 = writer.add_expr(FlatExpr::sort(l0));
        // Create an expression with a valid tag for the constant's value_idx,
        // but inject an unknown tag (255) via mutation after shard is read back.
        let e_bad = writer.add_expr(FlatExpr::bvar(0));
        let s0 = writer.add_string("Test.corrupt");
        writer.add_constant(MathverseConstantHeader {
            name_idx: s0,
            type_idx: e0,
            value_idx: e_bad,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: ImportConfidence::KernelVerified as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: 0,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        });
        writer.write_to_file(&in_path).unwrap();

        // Read shard and corrupt the tag on the second expression
        let mut shard = ShardReader::from_file(&in_path).unwrap();
        shard.exprs[e_bad as usize].tag = 255; // invalid tag

        let result = compact_deltas(&[shard], &out_path);
        assert!(
            result.is_err(),
            "compact_deltas should fail on unknown expr tag"
        );
        let err_msg = result.unwrap_err().to_string();
        assert!(
            err_msg.contains("unknown expression tag 255"),
            "error should mention the unknown tag, got: {err_msg}"
        );
    }

    #[test]
    fn test_compact_deltas_all_valid_tags_succeed() {
        // Verify that all valid FlatTag values (0-10) are handled without error.
        let dir = tempfile::tempdir().unwrap();
        let in_path = dir.path().join("all_tags.mathverse");
        let out_path = dir.path().join("compacted.mathverse");

        let mut writer = ShardWriter::new();
        let l0 = writer.add_level(FlatLevel::zero());
        let e_sort = writer.add_expr(FlatExpr::sort(l0)); // tag 1
        let e_bvar = writer.add_expr(FlatExpr::bvar(0)); // tag 0
        let s0 = writer.add_string("Test.all_tags");
        let e_const = writer.add_expr(FlatExpr::const_ref(s0, u32::MAX)); // tag 2
        let e_app = writer.add_expr(FlatExpr::app(e_sort, e_bvar)); // tag 3
        let e_lam = writer.add_expr(FlatExpr::lam(0, e_sort, e_bvar)); // tag 4
        let e_pi = writer.add_expr(FlatExpr::pi(0, e_sort, e_bvar)); // tag 5
        let e_let = writer.add_expr(FlatExpr::let_expr(e_sort, e_bvar, e_sort)); // tag 6
        let e_nat = writer.add_expr(FlatExpr::lit_nat(42)); // tag 7
        let e_str = writer.add_expr(FlatExpr::lit_str(s0)); // tag 8
        let e_proj = writer.add_expr(FlatExpr::proj(s0, 0, e_sort)); // tag 9
        let _e_fvar = writer.add_expr(FlatExpr::fvar(100)); // tag 10

        // Use the last complex expr as the type for our constant
        writer.add_constant(MathverseConstantHeader {
            name_idx: s0,
            type_idx: e_app,
            value_idx: e_const,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: ImportConfidence::KernelVerified as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: 0,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        });
        writer.write_to_file(&in_path).unwrap();

        let shard = ShardReader::from_file(&in_path).unwrap();
        // All tags 0-10 should be handled; this should succeed
        compact_deltas(&[shard], &out_path).expect("compact_deltas should handle all valid tags");

        let result = ShardReader::from_file(&out_path).unwrap();
        assert_eq!(result.header.constant_count, 1);
    }

    #[test]
    fn test_compact_deltas_unknown_level_tag_returns_error() {
        let dir = tempfile::tempdir().unwrap();
        let in_path = dir.path().join("corrupt_level.mathverse");
        let out_path = dir.path().join("compacted.mathverse");

        let mut writer = ShardWriter::new();
        let l0 = writer.add_level(FlatLevel::zero());
        let e0 = writer.add_expr(FlatExpr::sort(l0));
        let e1 = writer.add_expr(FlatExpr::bvar(0));
        let s0 = writer.add_string("Test.corrupt_level");
        writer.add_constant(MathverseConstantHeader {
            name_idx: s0,
            type_idx: e0,
            value_idx: e1,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: ImportConfidence::KernelVerified as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: 0,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        });
        writer.write_to_file(&in_path).unwrap();

        // Read shard and corrupt the level tag
        let mut shard = ShardReader::from_file(&in_path).unwrap();
        shard.levels[l0 as usize].tag = 255; // invalid level tag

        let result = compact_deltas(&[shard], &out_path);
        assert!(
            result.is_err(),
            "compact_deltas should fail on unknown level tag"
        );
        let err_msg = result.unwrap_err().to_string();
        assert!(
            err_msg.contains("unknown level tag 255"),
            "error should mention the unknown level tag, got: {err_msg}"
        );
    }

    // -------------------------------------------------------------------
    // compact_deltas: decl_kind and level_params preservation (#3416)
    // -------------------------------------------------------------------

    /// Helper: build a single-constant shard with the given decl_kind and
    /// level parameter names, write it to `path`, and return the path.
    fn build_shard_with_decl_kind(
        dir: &std::path::Path,
        name: &str,
        decl_kind: DeclKind,
        level_param_names: &[&str],
    ) -> std::path::PathBuf {
        let path = dir.join(format!("{name}.mathverse"));
        let mut w = ShardWriter::new();
        let l0 = w.add_level(FlatLevel::zero());
        let e0 = w.add_expr(FlatExpr::sort(l0));

        // Add level param name strings contiguously.
        let lp_start = if !level_param_names.is_empty() {
            let first = w.add_string(level_param_names[0]);
            for lpn in &level_param_names[1..] {
                w.add_string(lpn);
            }
            first
        } else {
            0
        };

        let s_name = w.add_string(name);
        w.add_constant(MathverseConstantHeader {
            name_idx: s_name,
            type_idx: e0,
            value_idx: if decl_kind == DeclKind::Axiom {
                NO_VALUE
            } else {
                e0
            },
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: ImportConfidence::KernelVerified as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: decl_kind as u8,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: lp_start,
            level_params_count: level_param_names.len() as u16,
            _pad2: [0u8; 26],
        });
        w.write_to_file(&path).unwrap();
        path
    }

    #[test]
    fn test_compact_deltas_preserves_decl_kind_theorem() {
        let dir = tempfile::tempdir().unwrap();
        let path = build_shard_with_decl_kind(dir.path(), "Thm.example", DeclKind::Theorem, &[]);
        let out = dir.path().join("out.mathverse");
        let shard = ShardReader::from_file(&path).unwrap();
        compact_deltas(&[shard], &out).unwrap();
        let result = ShardReader::from_file(&out).unwrap();
        let (_, hdr) = result.lookup_name("Thm.example").unwrap();
        assert_eq!(hdr.decl_kind, DeclKind::Theorem as u8);
    }

    #[test]
    fn test_compact_deltas_preserves_decl_kind_definition() {
        let dir = tempfile::tempdir().unwrap();
        let path = build_shard_with_decl_kind(dir.path(), "Def.example", DeclKind::Definition, &[]);
        let out = dir.path().join("out.mathverse");
        let shard = ShardReader::from_file(&path).unwrap();
        compact_deltas(&[shard], &out).unwrap();
        let result = ShardReader::from_file(&out).unwrap();
        let (_, hdr) = result.lookup_name("Def.example").unwrap();
        assert_eq!(hdr.decl_kind, DeclKind::Definition as u8);
    }

    #[test]
    fn test_compact_deltas_preserves_decl_kind_axiom() {
        let dir = tempfile::tempdir().unwrap();
        let path = build_shard_with_decl_kind(dir.path(), "Ax.example", DeclKind::Axiom, &[]);
        let out = dir.path().join("out.mathverse");
        let shard = ShardReader::from_file(&path).unwrap();
        compact_deltas(&[shard], &out).unwrap();
        let result = ShardReader::from_file(&out).unwrap();
        let (_, hdr) = result.lookup_name("Ax.example").unwrap();
        assert_eq!(hdr.decl_kind, DeclKind::Axiom as u8);
        assert!(
            !hdr.has_value(),
            "axiom should have no value after compaction"
        );
    }

    #[test]
    fn test_compact_deltas_preserves_decl_kind_opaque() {
        let dir = tempfile::tempdir().unwrap();
        let path = build_shard_with_decl_kind(dir.path(), "Opq.example", DeclKind::Opaque, &[]);
        let out = dir.path().join("out.mathverse");
        let shard = ShardReader::from_file(&path).unwrap();
        compact_deltas(&[shard], &out).unwrap();
        let result = ShardReader::from_file(&out).unwrap();
        let (_, hdr) = result.lookup_name("Opq.example").unwrap();
        assert_eq!(hdr.decl_kind, DeclKind::Opaque as u8);
    }

    #[test]
    fn test_compact_deltas_preserves_decl_kind_inductive() {
        let dir = tempfile::tempdir().unwrap();
        let path = build_shard_with_decl_kind(dir.path(), "Ind.example", DeclKind::Inductive, &[]);
        let out = dir.path().join("out.mathverse");
        let shard = ShardReader::from_file(&path).unwrap();
        compact_deltas(&[shard], &out).unwrap();
        let result = ShardReader::from_file(&out).unwrap();
        let (_, hdr) = result.lookup_name("Ind.example").unwrap();
        assert_eq!(hdr.decl_kind, DeclKind::Inductive as u8);
        assert!(hdr.is_inductive_family());
    }

    #[test]
    fn test_compact_deltas_preserves_decl_kind_constructor() {
        let dir = tempfile::tempdir().unwrap();
        let path =
            build_shard_with_decl_kind(dir.path(), "Ctor.example", DeclKind::Constructor, &[]);
        let out = dir.path().join("out.mathverse");
        let shard = ShardReader::from_file(&path).unwrap();
        compact_deltas(&[shard], &out).unwrap();
        let result = ShardReader::from_file(&out).unwrap();
        let (_, hdr) = result.lookup_name("Ctor.example").unwrap();
        assert_eq!(hdr.decl_kind, DeclKind::Constructor as u8);
        assert!(hdr.is_inductive_family());
    }

    #[test]
    fn test_compact_deltas_preserves_decl_kind_recursor() {
        let dir = tempfile::tempdir().unwrap();
        let path = build_shard_with_decl_kind(dir.path(), "Rec.example", DeclKind::Recursor, &[]);
        let out = dir.path().join("out.mathverse");
        let shard = ShardReader::from_file(&path).unwrap();
        compact_deltas(&[shard], &out).unwrap();
        let result = ShardReader::from_file(&out).unwrap();
        let (_, hdr) = result.lookup_name("Rec.example").unwrap();
        assert_eq!(hdr.decl_kind, DeclKind::Recursor as u8);
        assert!(hdr.is_inductive_family());
    }

    #[test]
    fn test_compact_deltas_preserves_decl_kind_quot() {
        let dir = tempfile::tempdir().unwrap();
        let path = build_shard_with_decl_kind(dir.path(), "Quot.example", DeclKind::Quot, &[]);
        let out = dir.path().join("out.mathverse");
        let shard = ShardReader::from_file(&path).unwrap();
        compact_deltas(&[shard], &out).unwrap();
        let result = ShardReader::from_file(&out).unwrap();
        let (_, hdr) = result.lookup_name("Quot.example").unwrap();
        assert_eq!(hdr.decl_kind, DeclKind::Quot as u8);
    }

    #[test]
    fn test_compact_deltas_all_decl_kinds_in_single_shard() {
        let dir = tempfile::tempdir().unwrap();
        let in_path = dir.path().join("all_kinds.mathverse");
        let out_path = dir.path().join("compacted.mathverse");

        let all_kinds = [
            ("Thm.x", DeclKind::Theorem),
            ("Def.x", DeclKind::Definition),
            ("Ax.x", DeclKind::Axiom),
            ("Opq.x", DeclKind::Opaque),
            ("Ind.x", DeclKind::Inductive),
            ("Ctor.x", DeclKind::Constructor),
            ("Rec.x", DeclKind::Recursor),
            ("Quot.x", DeclKind::Quot),
        ];

        let mut w = ShardWriter::new();
        let l0 = w.add_level(FlatLevel::zero());
        let e0 = w.add_expr(FlatExpr::sort(l0));

        for (name, dk) in &all_kinds {
            let s = w.add_string(name);
            w.add_constant(MathverseConstantHeader {
                name_idx: s,
                type_idx: e0,
                value_idx: if *dk == DeclKind::Axiom { NO_VALUE } else { e0 },
                source_system: SourceSystem::Lean4 as u8,
                import_confidence: ImportConfidence::KernelVerified as u8,
                content_domain: ContentDomain::PureMath as u8,
                decl_kind: *dk as u8,
                axiom_profile: AxiomProfile::NONE,
                sidecar_digest: 0,
                provenance_idx: 0,
                level_params_start: 0,
                level_params_count: 0,
                _pad2: [0u8; 26],
            });
        }
        w.write_to_file(&in_path).unwrap();

        let shard = ShardReader::from_file(&in_path).unwrap();
        compact_deltas(&[shard], &out_path).unwrap();

        let result = ShardReader::from_file(&out_path).unwrap();
        assert_eq!(result.header.constant_count, 8);

        for (name, dk) in &all_kinds {
            let (_, hdr) = result
                .lookup_name(name)
                .unwrap_or_else(|| panic!("missing constant {name} after compaction"));
            assert_eq!(
                hdr.decl_kind, *dk as u8,
                "decl_kind mismatch for {name}: expected {:?} ({}), got {}",
                dk, *dk as u8, hdr.decl_kind,
            );
        }
    }

    #[test]
    fn test_compact_deltas_decl_kind_survives_last_writer_wins() {
        // Two shards both define "Shared.decl" but with different decl_kinds.
        // The second shard's decl_kind should win.
        let dir = tempfile::tempdir().unwrap();

        let path0 = dir.path().join("shard0.mathverse");
        {
            let mut w = ShardWriter::new();
            let l0 = w.add_level(FlatLevel::zero());
            let e0 = w.add_expr(FlatExpr::sort(l0));
            let s = w.add_string("Shared.decl");
            w.add_constant(MathverseConstantHeader {
                name_idx: s,
                type_idx: e0,
                value_idx: e0,
                source_system: SourceSystem::Lean4 as u8,
                import_confidence: ImportConfidence::KernelVerified as u8,
                content_domain: ContentDomain::PureMath as u8,
                decl_kind: DeclKind::Theorem as u8,
                axiom_profile: AxiomProfile::NONE,
                sidecar_digest: 0,
                provenance_idx: 0,
                level_params_start: 0,
                level_params_count: 0,
                _pad2: [0u8; 26],
            });
            w.write_to_file(&path0).unwrap();
        }

        let path1 = dir.path().join("shard1.mathverse");
        {
            let mut w = ShardWriter::new();
            let l0 = w.add_level(FlatLevel::zero());
            let e0 = w.add_expr(FlatExpr::sort(l0));
            let s = w.add_string("Shared.decl");
            w.add_constant(MathverseConstantHeader {
                name_idx: s,
                type_idx: e0,
                value_idx: e0,
                source_system: SourceSystem::Lean4 as u8,
                import_confidence: ImportConfidence::KernelVerified as u8,
                content_domain: ContentDomain::PureMath as u8,
                decl_kind: DeclKind::Recursor as u8,
                axiom_profile: AxiomProfile::NONE,
                sidecar_digest: 0,
                provenance_idx: 0,
                level_params_start: 0,
                level_params_count: 0,
                _pad2: [0u8; 26],
            });
            w.write_to_file(&path1).unwrap();
        }

        let out = dir.path().join("compacted.mathverse");
        let s0 = ShardReader::from_file(&path0).unwrap();
        let s1 = ShardReader::from_file(&path1).unwrap();
        compact_deltas(&[s0, s1], &out).unwrap();

        let result = ShardReader::from_file(&out).unwrap();
        let (_, hdr) = result.lookup_name("Shared.decl").unwrap();
        assert_eq!(
            hdr.decl_kind,
            DeclKind::Recursor as u8,
            "last-writer-wins should preserve shard1's decl_kind (Recursor), got {}",
            hdr.decl_kind,
        );
    }

    #[test]
    fn test_compact_deltas_preserves_empty_level_params() {
        let dir = tempfile::tempdir().unwrap();
        let path = build_shard_with_decl_kind(dir.path(), "NoParams.x", DeclKind::Definition, &[]);
        let out = dir.path().join("out.mathverse");
        let shard = ShardReader::from_file(&path).unwrap();
        compact_deltas(&[shard], &out).unwrap();

        let result = ShardReader::from_file(&out).unwrap();
        let (_, hdr) = result.lookup_name("NoParams.x").unwrap();
        assert_eq!(
            hdr.level_params_count, 0,
            "empty level_params_count should be preserved"
        );
    }

    #[test]
    fn test_compact_deltas_preserves_single_level_param() {
        let dir = tempfile::tempdir().unwrap();
        let path =
            build_shard_with_decl_kind(dir.path(), "OneParam.x", DeclKind::Definition, &["u"]);
        let out = dir.path().join("out.mathverse");
        let shard = ShardReader::from_file(&path).unwrap();
        compact_deltas(&[shard], &out).unwrap();

        let result = ShardReader::from_file(&out).unwrap();
        let (_, hdr) = result.lookup_name("OneParam.x").unwrap();
        assert_eq!(hdr.level_params_count, 1);
        let lp_start = hdr.level_params_start as usize;
        assert_eq!(result.strings[lp_start], "u");
    }

    #[test]
    fn test_compact_deltas_preserves_multiple_level_params() {
        let dir = tempfile::tempdir().unwrap();
        let path = build_shard_with_decl_kind(
            dir.path(),
            "MultiParam.x",
            DeclKind::Theorem,
            &["u", "v", "w"],
        );
        let out = dir.path().join("out.mathverse");
        let shard = ShardReader::from_file(&path).unwrap();
        compact_deltas(&[shard], &out).unwrap();

        let result = ShardReader::from_file(&out).unwrap();
        let (_, hdr) = result.lookup_name("MultiParam.x").unwrap();
        assert_eq!(hdr.level_params_count, 3);
        let start = hdr.level_params_start as usize;
        assert_eq!(result.strings[start], "u");
        assert_eq!(result.strings[start + 1], "v");
        assert_eq!(result.strings[start + 2], "w");
    }

    #[test]
    fn test_compact_deltas_level_params_remapped_across_shards() {
        // Two shards with different level params. After compaction, both
        // constants should retain their own distinct level param names
        // despite string table remapping.
        let dir = tempfile::tempdir().unwrap();

        let path0 = dir.path().join("lp_shard0.mathverse");
        {
            let mut w = ShardWriter::new();
            let l0 = w.add_level(FlatLevel::zero());
            let e0 = w.add_expr(FlatExpr::sort(l0));
            let lp_alpha = w.add_string("alpha");
            let _lp_beta = w.add_string("beta");
            let s = w.add_string("Poly.id");
            w.add_constant(MathverseConstantHeader {
                name_idx: s,
                type_idx: e0,
                value_idx: e0,
                source_system: SourceSystem::Lean4 as u8,
                import_confidence: ImportConfidence::KernelVerified as u8,
                content_domain: ContentDomain::PureMath as u8,
                decl_kind: DeclKind::Definition as u8,
                axiom_profile: AxiomProfile::NONE,
                sidecar_digest: 0,
                provenance_idx: 0,
                level_params_start: lp_alpha,
                level_params_count: 2,
                _pad2: [0u8; 26],
            });
            w.write_to_file(&path0).unwrap();
        }

        let path1 = dir.path().join("lp_shard1.mathverse");
        {
            let mut w = ShardWriter::new();
            let l0 = w.add_level(FlatLevel::zero());
            let e0 = w.add_expr(FlatExpr::sort(l0));
            let lp_x = w.add_string("x");
            let _lp_y = w.add_string("y");
            let _lp_z = w.add_string("z");
            let s = w.add_string("Poly.map");
            w.add_constant(MathverseConstantHeader {
                name_idx: s,
                type_idx: e0,
                value_idx: e0,
                source_system: SourceSystem::Lean4 as u8,
                import_confidence: ImportConfidence::KernelVerified as u8,
                content_domain: ContentDomain::PureMath as u8,
                decl_kind: DeclKind::Theorem as u8,
                axiom_profile: AxiomProfile::NONE,
                sidecar_digest: 0,
                provenance_idx: 0,
                level_params_start: lp_x,
                level_params_count: 3,
                _pad2: [0u8; 26],
            });
            w.write_to_file(&path1).unwrap();
        }

        let out = dir.path().join("compacted.mathverse");
        let s0 = ShardReader::from_file(&path0).unwrap();
        let s1 = ShardReader::from_file(&path1).unwrap();
        compact_deltas(&[s0, s1], &out).unwrap();

        let result = ShardReader::from_file(&out).unwrap();
        assert_eq!(result.header.constant_count, 2);

        // Poly.id should have level params ["alpha", "beta"]
        let (_, hdr_id) = result.lookup_name("Poly.id").unwrap();
        assert_eq!(hdr_id.level_params_count, 2);
        let s_id = hdr_id.level_params_start as usize;
        assert_eq!(result.strings[s_id], "alpha");
        assert_eq!(result.strings[s_id + 1], "beta");

        // Poly.map should have level params ["x", "y", "z"]
        let (_, hdr_map) = result.lookup_name("Poly.map").unwrap();
        assert_eq!(hdr_map.level_params_count, 3);
        let s_map = hdr_map.level_params_start as usize;
        assert_eq!(result.strings[s_map], "x");
        assert_eq!(result.strings[s_map + 1], "y");
        assert_eq!(result.strings[s_map + 2], "z");
    }

    #[test]
    fn test_compact_deltas_preserves_expression_content_round_trip() {
        // Build a shard with a non-trivial expression (Pi type) and verify
        // that compact_deltas preserves its structure.
        let dir = tempfile::tempdir().unwrap();
        let in_path = dir.path().join("expr_rt.mathverse");
        let out_path = dir.path().join("compacted.mathverse");

        let mut w = ShardWriter::new();
        let l0 = w.add_level(FlatLevel::zero());
        let sort0 = w.add_expr(FlatExpr::sort(l0));
        let bv0 = w.add_expr(FlatExpr::bvar(0));
        let pi_expr = w.add_expr(FlatExpr::pi(0, sort0, bv0));
        let s = w.add_string("ExprRT.test");

        w.add_constant(MathverseConstantHeader {
            name_idx: s,
            type_idx: pi_expr,
            value_idx: bv0,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: ImportConfidence::KernelVerified as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: DeclKind::Definition as u8,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        });
        w.write_to_file(&in_path).unwrap();

        let shard = ShardReader::from_file(&in_path).unwrap();
        compact_deltas(&[shard], &out_path).unwrap();

        let result = ShardReader::from_file(&out_path).unwrap();
        let (_, hdr) = result.lookup_name("ExprRT.test").unwrap();

        // The type expression should be a Pi (tag 5)
        let type_expr = &result.exprs[hdr.type_idx as usize];
        assert_eq!(type_expr.tag, 5, "type expression should be Pi (tag 5)");

        // The value expression should be a BVar (tag 0)
        let val_expr = &result.exprs[hdr.value_idx as usize];
        assert_eq!(val_expr.tag, 0, "value expression should be BVar (tag 0)");
    }

    #[test]
    fn test_compact_deltas_decl_kind_and_level_params_combined() {
        // One shard with multiple constants, each with different decl_kinds
        // and different numbers of level params. Verifies all fields survive
        // compaction together.
        let dir = tempfile::tempdir().unwrap();
        let in_path = dir.path().join("combined.mathverse");
        let out_path = dir.path().join("compacted.mathverse");

        let mut w = ShardWriter::new();
        let l0 = w.add_level(FlatLevel::zero());
        let e0 = w.add_expr(FlatExpr::sort(l0));

        // Constant 1: Inductive with 2 level params
        let lp1_a = w.add_string("u");
        let _lp1_b = w.add_string("v");
        let s1 = w.add_string("Combined.Ind");
        w.add_constant(MathverseConstantHeader {
            name_idx: s1,
            type_idx: e0,
            value_idx: e0,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: ImportConfidence::KernelVerified as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: DeclKind::Inductive as u8,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: lp1_a,
            level_params_count: 2,
            _pad2: [0u8; 26],
        });

        // Constant 2: Axiom with 0 level params
        let s2 = w.add_string("Combined.Ax");
        w.add_constant(MathverseConstantHeader {
            name_idx: s2,
            type_idx: e0,
            value_idx: NO_VALUE,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: ImportConfidence::Axiomatized as u8,
            content_domain: ContentDomain::Logic as u8,
            decl_kind: DeclKind::Axiom as u8,
            axiom_profile: AxiomProfile::AXIOMATIZED,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        });

        // Constant 3: Constructor with 1 level param
        let lp3 = w.add_string("w");
        let s3 = w.add_string("Combined.Ctor");
        w.add_constant(MathverseConstantHeader {
            name_idx: s3,
            type_idx: e0,
            value_idx: e0,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: ImportConfidence::KernelVerified as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: DeclKind::Constructor as u8,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: lp3,
            level_params_count: 1,
            _pad2: [0u8; 26],
        });

        w.write_to_file(&in_path).unwrap();

        let shard = ShardReader::from_file(&in_path).unwrap();
        compact_deltas(&[shard], &out_path).unwrap();

        let result = ShardReader::from_file(&out_path).unwrap();
        assert_eq!(result.header.constant_count, 3);

        // Verify Combined.Ind: Inductive, 2 level params
        let (_, hdr1) = result.lookup_name("Combined.Ind").unwrap();
        assert_eq!(hdr1.decl_kind, DeclKind::Inductive as u8);
        assert_eq!(hdr1.level_params_count, 2);
        let s1_start = hdr1.level_params_start as usize;
        assert_eq!(result.strings[s1_start], "u");
        assert_eq!(result.strings[s1_start + 1], "v");

        // Verify Combined.Ax: Axiom, 0 level params, no value
        let (_, hdr2) = result.lookup_name("Combined.Ax").unwrap();
        assert_eq!(hdr2.decl_kind, DeclKind::Axiom as u8);
        assert_eq!(hdr2.level_params_count, 0);
        assert!(!hdr2.has_value());

        // Verify Combined.Ctor: Constructor, 1 level param
        let (_, hdr3) = result.lookup_name("Combined.Ctor").unwrap();
        assert_eq!(hdr3.decl_kind, DeclKind::Constructor as u8);
        assert_eq!(hdr3.level_params_count, 1);
        let s3_start = hdr3.level_params_start as usize;
        assert_eq!(result.strings[s3_start], "w");
    }

    /// Regression test for the #3416 acceptance criteria.
    ///
    /// Builds two shards whose constants each carry a non-default `decl_kind`
    /// and a non-empty, universe-polymorphic `level_params` block. Runs
    /// `compact_deltas` on both shards and asserts the merged shard preserves:
    ///   1. `decl_kind` for every constant (not zeroed to `Theorem`),
    ///   2. `level_params_count` for every constant,
    ///   3. contiguous string-table placement for `level_params`
    ///      (`start + count` all index valid strings),
    ///   4. reconstructed level-param names match the originals bit-for-bit.
    ///
    /// This directly guards against the silent data-corruption bug in #3354
    /// where `remap_expr` returned 0 for unknown tags and `decl_kind` was
    /// hardcoded to 0 (Theorem).
    #[test]
    fn test_compact_deltas_preserves_decl_kind_and_level_params() {
        use std::collections::HashMap;
        let dir = tempfile::tempdir().unwrap();

        // Shard 0: Definition with ["u", "v"] and Inductive with ["α"].
        let path0 = dir.path().join("s0.mathverse");
        {
            let mut w = ShardWriter::new();
            let l0 = w.add_level(FlatLevel::zero());
            let e0 = w.add_expr(FlatExpr::sort(l0));

            // Contiguous level-param string block for Poly.def: ["u", "v"].
            let lp_u = w.add_string("u");
            let _lp_v = w.add_string("v");
            let n_def = w.add_string("Poly.def");
            w.add_constant(MathverseConstantHeader {
                name_idx: n_def,
                type_idx: e0,
                value_idx: e0,
                source_system: SourceSystem::Lean4 as u8,
                import_confidence: ImportConfidence::KernelVerified as u8,
                content_domain: ContentDomain::PureMath as u8,
                decl_kind: DeclKind::Definition as u8,
                axiom_profile: AxiomProfile::NONE,
                sidecar_digest: 0,
                provenance_idx: 0,
                level_params_start: lp_u,
                level_params_count: 2,
                _pad2: [0u8; 26],
            });

            // Contiguous level-param string block for Poly.ind: ["α"].
            let lp_alpha = w.add_string("α");
            let n_ind = w.add_string("Poly.ind");
            w.add_constant(MathverseConstantHeader {
                name_idx: n_ind,
                type_idx: e0,
                value_idx: e0,
                source_system: SourceSystem::Lean4 as u8,
                import_confidence: ImportConfidence::KernelVerified as u8,
                content_domain: ContentDomain::PureMath as u8,
                decl_kind: DeclKind::Inductive as u8,
                axiom_profile: AxiomProfile::NONE,
                sidecar_digest: 0,
                provenance_idx: 0,
                level_params_start: lp_alpha,
                level_params_count: 1,
                _pad2: [0u8; 26],
            });

            w.write_to_file(&path0).unwrap();
        }

        // Shard 1: Recursor with ["u", "v", "w"] and Axiom with [] (no params).
        // The Recursor deliberately shares level-param names ("u", "v") with
        // Poly.def in shard 0. The compaction must preserve contiguous
        // placement for `Poly.rec`'s `level_params_start..+count` block even
        // though those names are already present in the output string table
        // from shard 0. This guards against the #3557 contiguity bug where
        // dedup in the shared string pool returned earlier indices and broke
        // the reconstructed param list.
        let path1 = dir.path().join("s1.mathverse");
        {
            let mut w = ShardWriter::new();
            let l0 = w.add_level(FlatLevel::zero());
            let e0 = w.add_expr(FlatExpr::sort(l0));

            let lp_u = w.add_string("u");
            let _lp_v = w.add_string("v");
            let _lp_w = w.add_string("w");
            let n_rec = w.add_string("Poly.rec");
            w.add_constant(MathverseConstantHeader {
                name_idx: n_rec,
                type_idx: e0,
                value_idx: e0,
                source_system: SourceSystem::Lean4 as u8,
                import_confidence: ImportConfidence::KernelVerified as u8,
                content_domain: ContentDomain::PureMath as u8,
                decl_kind: DeclKind::Recursor as u8,
                axiom_profile: AxiomProfile::NONE,
                sidecar_digest: 0,
                provenance_idx: 0,
                level_params_start: lp_u,
                level_params_count: 3,
                _pad2: [0u8; 26],
            });

            let n_ax = w.add_string("Poly.ax");
            w.add_constant(MathverseConstantHeader {
                name_idx: n_ax,
                type_idx: e0,
                value_idx: NO_VALUE,
                source_system: SourceSystem::Lean4 as u8,
                import_confidence: ImportConfidence::Axiomatized as u8,
                content_domain: ContentDomain::Logic as u8,
                decl_kind: DeclKind::Axiom as u8,
                axiom_profile: AxiomProfile::AXIOMATIZED,
                sidecar_digest: 0,
                provenance_idx: 0,
                level_params_start: 0,
                level_params_count: 0,
                _pad2: [0u8; 26],
            });

            w.write_to_file(&path1).unwrap();
        }

        // Run compact_deltas on both shards.
        let out = dir.path().join("compacted.mathverse");
        let r0 = ShardReader::from_file(&path0).unwrap();
        let r1 = ShardReader::from_file(&path1).unwrap();
        compact_deltas(&[r0, r1], &out).unwrap();

        // Read back and verify every invariant.
        let result = ShardReader::from_file(&out).unwrap();
        assert_eq!(
            result.header.constant_count, 4,
            "expected 4 distinct constants across the two shards",
        );

        // Expected (decl_kind, level_params) for each name.
        // Note: Poly.rec and Poly.def share level-param names ("u", "v") —
        // see the shard-1 comment above. Contiguity must hold despite that.
        let expected: HashMap<&str, (DeclKind, Vec<&str>)> = [
            ("Poly.def", (DeclKind::Definition, vec!["u", "v"])),
            ("Poly.ind", (DeclKind::Inductive, vec!["α"])),
            ("Poly.rec", (DeclKind::Recursor, vec!["u", "v", "w"])),
            ("Poly.ax", (DeclKind::Axiom, vec![])),
        ]
        .into_iter()
        .collect();

        for (name, (want_kind, want_params)) in &expected {
            let (_, hdr) = result
                .lookup_name(name)
                .unwrap_or_else(|| panic!("missing constant {name} after compaction"));

            // (1) decl_kind preserved (not zeroed to Theorem).
            assert_eq!(
                hdr.decl_kind, *want_kind as u8,
                "decl_kind for {name}: expected {:?} ({}), got {}",
                want_kind, *want_kind as u8, hdr.decl_kind,
            );
            assert_ne!(
                hdr.decl_kind,
                DeclKind::Theorem as u8,
                "decl_kind for {name} silently zeroed to Theorem (the #3354 bug)",
            );

            // (2) level_params_count preserved.
            assert_eq!(
                hdr.level_params_count as usize,
                want_params.len(),
                "level_params_count for {name}",
            );

            // (3) contiguous string-table placement: all indices valid.
            let start = hdr.level_params_start as usize;
            let count = hdr.level_params_count as usize;
            if count > 0 {
                assert!(
                    start + count <= result.strings.len(),
                    "level_params block for {name} ({start}..{}) exceeds string table \
                     of length {}",
                    start + count,
                    result.strings.len(),
                );
            }

            // (4) reconstructed names match originals bit-for-bit.
            let got_params: Vec<&str> = (0..count)
                .map(|i| result.strings[start + i].as_str())
                .collect();
            assert_eq!(
                got_params, *want_params,
                "reconstructed level_params for {name}",
            );
        }

        // Explicit axiom invariant: no value after compaction.
        let (_, hdr_ax) = result.lookup_name("Poly.ax").unwrap();
        assert!(
            !hdr_ax.has_value(),
            "axiom Poly.ax should have no value after compaction",
        );
    }

    // ----- #3557: compact_deltas level_params contiguity across shards -----
    // with shared param-name strings.

    /// Minimal reproduction of #3557: two shards share one or more level
    /// parameter name strings. Before the fix, `remap_string` returned the
    /// cached (earlier) output index for the shared names, so the
    /// `level_params_start..+count` window for the later-processed constant
    /// no longer read back the intended names contiguously.
    ///
    /// Reproduces the exact scenario documented in #3557: shard 0 has
    /// `Poly.def` with `["u", "v"]`, shard 1 has `Poly.rec` with
    /// `["u", "v", "w"]`. Intervening constants ensure other non-param
    /// strings land between the two blocks, so a dedup-based remap would
    /// produce a discontiguous window. The fix uses `add_string_block`
    /// to force a fresh contiguous block for the second constant.
    #[test]
    fn test_compact_deltas_level_params_contiguous_with_shared_names() {
        let dir = tempfile::tempdir().unwrap();

        // Shard 0: Poly.def with level params ["u", "v"], Poly.ind with ["α"].
        let path0 = dir.path().join("shared0.mathverse");
        {
            let mut w = ShardWriter::new();
            let l0 = w.add_level(FlatLevel::zero());
            let e0 = w.add_expr(FlatExpr::sort(l0));

            let lp_u = w.add_string("u");
            let _lp_v = w.add_string("v");
            let n_def = w.add_string("Poly.def");
            w.add_constant(MathverseConstantHeader {
                name_idx: n_def,
                type_idx: e0,
                value_idx: e0,
                source_system: SourceSystem::Lean4 as u8,
                import_confidence: ImportConfidence::KernelVerified as u8,
                content_domain: ContentDomain::PureMath as u8,
                decl_kind: DeclKind::Definition as u8,
                axiom_profile: AxiomProfile::NONE,
                sidecar_digest: 0,
                provenance_idx: 0,
                level_params_start: lp_u,
                level_params_count: 2,
                _pad2: [0u8; 26],
            });

            let lp_alpha = w.add_string("α");
            let n_ind = w.add_string("Poly.ind");
            w.add_constant(MathverseConstantHeader {
                name_idx: n_ind,
                type_idx: e0,
                value_idx: e0,
                source_system: SourceSystem::Lean4 as u8,
                import_confidence: ImportConfidence::KernelVerified as u8,
                content_domain: ContentDomain::PureMath as u8,
                decl_kind: DeclKind::Inductive as u8,
                axiom_profile: AxiomProfile::NONE,
                sidecar_digest: 0,
                provenance_idx: 0,
                level_params_start: lp_alpha,
                level_params_count: 1,
                _pad2: [0u8; 26],
            });

            w.write_to_file(&path0).unwrap();
        }

        // Shard 1: Poly.rec with level params ["u", "v", "w"] — "u" and "v"
        // are shared with shard 0. Poly.ax has no params.
        let path1 = dir.path().join("shared1.mathverse");
        {
            let mut w = ShardWriter::new();
            let l0 = w.add_level(FlatLevel::zero());
            let e0 = w.add_expr(FlatExpr::sort(l0));

            let lp_u = w.add_string("u");
            let _lp_v = w.add_string("v");
            let _lp_w = w.add_string("w");
            let n_rec = w.add_string("Poly.rec");
            w.add_constant(MathverseConstantHeader {
                name_idx: n_rec,
                type_idx: e0,
                value_idx: e0,
                source_system: SourceSystem::Lean4 as u8,
                import_confidence: ImportConfidence::KernelVerified as u8,
                content_domain: ContentDomain::PureMath as u8,
                decl_kind: DeclKind::Recursor as u8,
                axiom_profile: AxiomProfile::NONE,
                sidecar_digest: 0,
                provenance_idx: 0,
                level_params_start: lp_u,
                level_params_count: 3,
                _pad2: [0u8; 26],
            });

            let n_ax = w.add_string("Poly.ax");
            w.add_constant(MathverseConstantHeader {
                name_idx: n_ax,
                type_idx: e0,
                value_idx: NO_VALUE,
                source_system: SourceSystem::Lean4 as u8,
                import_confidence: ImportConfidence::Axiomatized as u8,
                content_domain: ContentDomain::Logic as u8,
                decl_kind: DeclKind::Axiom as u8,
                axiom_profile: AxiomProfile::AXIOMATIZED,
                sidecar_digest: 0,
                provenance_idx: 0,
                level_params_start: 0,
                level_params_count: 0,
                _pad2: [0u8; 26],
            });

            w.write_to_file(&path1).unwrap();
        }

        let out = dir.path().join("compacted.mathverse");
        let r0 = ShardReader::from_file(&path0).unwrap();
        let r1 = ShardReader::from_file(&path1).unwrap();
        compact_deltas(&[r0, r1], &out).unwrap();

        let result = ShardReader::from_file(&out).unwrap();
        assert_eq!(result.header.constant_count, 4);

        // Every level_params window must read back contiguously with the
        // original names — even though shard 1's "u"/"v" are dedup hits
        // against shard 0's "u"/"v" in the merged string table.
        let expectations: &[(&str, &[&str])] = &[
            ("Poly.def", &["u", "v"]),
            ("Poly.ind", &["α"]),
            ("Poly.rec", &["u", "v", "w"]),
            ("Poly.ax", &[]),
        ];
        for (name, want) in expectations {
            let (_, hdr) = result
                .lookup_name(name)
                .unwrap_or_else(|| panic!("missing {name}"));
            assert_eq!(
                hdr.level_params_count as usize,
                want.len(),
                "level_params_count for {name}",
            );
            let start = hdr.level_params_start as usize;
            let count = hdr.level_params_count as usize;
            if count > 0 {
                assert!(
                    start + count <= result.strings.len(),
                    "level_params for {name} runs off the end of the string table",
                );
            }
            let got: Vec<&str> = (0..count)
                .map(|i| result.strings[start + i].as_str())
                .collect();
            assert_eq!(
                got, *want,
                "level_params window for {name} is not contiguous / does not match",
            );
        }
    }

    /// Three-shard variant with heavy sharing: every shard uses the same
    /// canonical param names ("u", "v"). All three constants must end up
    /// with their own contiguous block of names in the merged output,
    /// which requires `add_string_block` to push fresh copies rather than
    /// routing through the dedup cache.
    #[test]
    fn test_compact_deltas_three_shards_all_share_u_v() {
        let dir = tempfile::tempdir().unwrap();
        let mut paths = Vec::new();
        for (i, const_name) in ["A.def", "B.def", "C.def"].iter().enumerate() {
            let p = dir.path().join(format!("tri{i}.mathverse"));
            let mut w = ShardWriter::new();
            let l0 = w.add_level(FlatLevel::zero());
            let e0 = w.add_expr(FlatExpr::sort(l0));
            let lp_u = w.add_string("u");
            let _lp_v = w.add_string("v");
            let n = w.add_string(const_name);
            w.add_constant(MathverseConstantHeader {
                name_idx: n,
                type_idx: e0,
                value_idx: e0,
                source_system: SourceSystem::Lean4 as u8,
                import_confidence: ImportConfidence::KernelVerified as u8,
                content_domain: ContentDomain::PureMath as u8,
                decl_kind: DeclKind::Definition as u8,
                axiom_profile: AxiomProfile::NONE,
                sidecar_digest: 0,
                provenance_idx: 0,
                level_params_start: lp_u,
                level_params_count: 2,
                _pad2: [0u8; 26],
            });
            w.write_to_file(&p).unwrap();
            paths.push(p);
        }

        let readers: Vec<ShardReader> = paths
            .iter()
            .map(|p| ShardReader::from_file(p).unwrap())
            .collect();
        let out = dir.path().join("tri_compact.mathverse");
        compact_deltas(&readers, &out).unwrap();

        let result = ShardReader::from_file(&out).unwrap();
        assert_eq!(result.header.constant_count, 3);
        for name in ["A.def", "B.def", "C.def"] {
            let (_, hdr) = result.lookup_name(name).unwrap();
            assert_eq!(hdr.level_params_count, 2, "{name} count");
            let start = hdr.level_params_start as usize;
            assert_eq!(&result.strings[start], "u", "{name}[0]");
            assert_eq!(&result.strings[start + 1], "v", "{name}[1]");
        }
    }

    /// Unit test for `ShardWriter::add_string_block`: shows the contract
    /// that it pushes fresh copies without consulting or overwriting the
    /// dedup cache, while still populating missing cache entries so later
    /// `add_string` calls for the same strings resolve cheaply.
    #[test]
    fn test_add_string_block_is_contiguous_and_non_deduping() {
        // The writer pre-seeds strings[0] = "", so the first add_string
        // call lands at index 1, not 0.
        let mut w = ShardWriter::new();
        let u0 = w.add_string("u"); // 1
        let _other = w.add_string("other"); // 2
        let v0 = w.add_string("v"); // 3
        assert_eq!(u0, 1);
        assert_eq!(v0, 3);

        // Block push: fresh contiguous slots at 4..6 for "u", "v".
        let block_start = w.add_string_block(&["u", "v"]);
        assert_eq!(block_start, 4);

        // Subsequent `add_string` for "u"/"v" returns the ORIGINAL index,
        // not the block index — dedup cache is not overwritten.
        assert_eq!(w.add_string("u"), 1);
        assert_eq!(w.add_string("v"), 3);

        // A second block push for the same names allocates another fresh
        // contiguous region — contiguity is the contract, not uniqueness.
        let block_start_2 = w.add_string_block(&["u", "v"]);
        assert_eq!(block_start_2, 6);

        // Empty block returns 0 (the "no params" sentinel convention).
        assert_eq!(w.add_string_block(&[]), 0);

        // New names not yet seen become cache-hits after the block push.
        let block_new = w.add_string_block(&["brand_new"]);
        assert_eq!(w.add_string("brand_new"), block_new);
    }

    // -------------------------------------------------------------------
    // Loader error-message tests (four-question standard: WHAT failed,
    // WHY, WHAT NOW, WHERE — see docs/ERROR_STYLE notes in the audit)
    // -------------------------------------------------------------------

    #[test]
    fn test_from_file_missing_shard_names_path_and_remediation() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("absent.mathverse");
        let err = ShardReader::from_file(&path)
            .map(|_| ())
            .expect_err("missing shard must fail");
        let msg = err.to_string();
        assert!(
            msg.contains("absent.mathverse"),
            "missing-file error must name the shard path, got: {msg}"
        );
        assert!(
            msg.contains("clean mathverse download") && msg.contains("mathverse_convert"),
            "missing-file error must name the fetch/rebuild remediation, got: {msg}"
        );
        assert!(
            matches!(err, MathverseError::ShardFileUnreadable { .. }),
            "missing-file error must be the typed ShardFileUnreadable variant, got: {err:?}"
        );
    }

    #[test]
    fn test_from_file_corrupt_shard_names_path_cause_and_fix() {
        let (_dir, path) = write_test_shard(&["Nat.add"], SourceSystem::Lean4);
        // Flip one content byte just past the header (string section) so the
        // header still parses but the blake3 footer no longer matches.
        let mut bytes = std::fs::read(&path).unwrap();
        bytes[HEADER_SIZE + 1] ^= 0xFF;
        std::fs::write(&path, &bytes).unwrap();

        let msg = ShardReader::from_file(&path)
            .map(|_| ())
            .expect_err("corrupt shard must fail")
            .to_string();
        assert!(
            msg.contains("shard checksum mismatch"),
            "corrupt shard must report a checksum mismatch, got: {msg}"
        );
        assert!(
            msg.contains("test.mathverse"),
            "corrupt-shard error must name WHICH shard file failed, got: {msg}"
        );
        assert!(
            msg.contains("blake3 footer") && msg.contains("clean mathverse download"),
            "corrupt-shard error must state the cause and remediation, got: {msg}"
        );
    }

    #[test]
    fn test_mmap_open_missing_shard_names_path_and_remediation() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("absent.mathverse");
        let msg = ShardMmapReader::open(&path)
            .map(|_| ())
            .expect_err("missing shard must fail")
            .to_string();
        assert!(
            msg.contains("absent.mathverse") && msg.contains("clean mathverse download"),
            "mmap missing-file error must carry path + remediation, got: {msg}"
        );
    }

    // --- Fix (1): decompress cap is large + env-configurable ----------------

    /// The default decompress cap must comfortably exceed the old hard 64 MiB
    /// limit, which rejected `lean4_mathlib4`'s ~71.6 MiB provenance sidecar.
    /// Pure compile-time-constant assertion — no env access, so it never races
    /// the process-global `MATHVERSE_MAX_DECOMPRESS_BYTES` with the override
    /// test below.
    #[test]
    fn test_default_decompress_cap_exceeds_legacy_64mb() {
        const _: () = assert!(
            DEFAULT_MAX_DECOMPRESS_BYTES >= 100 * 1024 * 1024,
            "default cap must fit the ~71.6MiB mathlib4 sidecar"
        );
    }

    /// Resolution of [`max_decompress_bytes`]: a valid env override is honored,
    /// an invalid/zero one falls back to the default, and an absent variable
    /// yields the default. `MATHVERSE_MAX_DECOMPRESS_BYTES` is process-global, so
    /// ALL of its manipulation lives in this one test (no other test reads or
    /// writes it) — the assertions are sequenced within a single test body to
    /// own the env state and avoid a cross-test race.
    #[test]
    fn test_decompress_cap_env_override() {
        crate::process_env::with_env_edits(|env| {
            env.set(MAX_DECOMPRESS_BYTES_ENV, "12345");
            assert_eq!(max_decompress_bytes(), 12345);
            env.set(MAX_DECOMPRESS_BYTES_ENV, "not-a-number");
            assert_eq!(max_decompress_bytes(), DEFAULT_MAX_DECOMPRESS_BYTES);
            env.set(MAX_DECOMPRESS_BYTES_ENV, "0");
            assert_eq!(max_decompress_bytes(), DEFAULT_MAX_DECOMPRESS_BYTES);
            // Absent variable → default.
            env.remove(MAX_DECOMPRESS_BYTES_ENV);
            assert_eq!(max_decompress_bytes(), DEFAULT_MAX_DECOMPRESS_BYTES);
        });
    }

    // --- Fix (2): legacy coq_v/fstar raw-universe-value sorts ---------------

    /// Build a shard mirroring the stale coq_v/fstar importer: a single zero
    /// level in the pool plus a `Sort` expr whose level field is the raw
    /// universe value 1 (out of bounds as an index). Such a shard previously
    /// failed `validate_expr_arena` ("sort level index 1 out of bounds for 1
    /// levels"); now it loads, and the sort reconstructs to `Sort (succ zero)`.
    #[test]
    fn test_legacy_raw_universe_sort_one_loads_and_reconstructs() {
        let mut writer = ShardWriter::new();
        let name = writer.add_string("CoqType");
        // Pool holds only the pre-seeded zero sentinel (level_count == 1).
        // `sort(1)` is a RAW universe value, not a pool index (legacy form).
        let e_prop = writer.add_expr(FlatExpr::sort(0));
        let e_type = writer.add_expr(FlatExpr::sort(1));
        writer.add_constant(MathverseConstantHeader {
            name_idx: name,
            type_idx: e_type,
            value_idx: e_prop,
            source_system: SourceSystem::Coq as u8,
            import_confidence: ImportConfidence::Translated as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: DeclKind::Definition as u8,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        });

        let mut buf = Vec::new();
        writer.write(&mut buf).expect("write legacy-style shard");

        let reader = ShardReader::from_bytes(&buf)
            .expect("legacy raw-universe sort shard must load (bounded tolerance)");
        assert_eq!(reader.header.level_count, 1);
        // Trust label survives unchanged.
        assert_eq!(
            reader.constants[0].import_confidence,
            ImportConfidence::Translated as u8
        );

        // The sort(1) reconstructs as Sort (succ zero), per the documented
        // v_type_parser convention — not fabricated, the recorded value is 1.
        let expr = crate::shard_reconstruct::reconstruct_from_shard(
            &reader.exprs,
            &reader.levels,
            &reader.strings,
            e_type,
        )
        .expect("reconstruct legacy sort");
        let expected = clean_kernel::expr::Expr::sort(clean_kernel::level::Level::succ(
            clean_kernel::level::Level::zero(),
        ));
        assert_eq!(expr, expected, "sort(1) must be Sort (succ zero)");
    }

    /// Guard: the legacy tolerance is bounded. An out-of-bounds sort index in a
    /// shard with a genuinely populated (multi-level) pool is still rejected as
    /// corruption — relaxation applies ONLY to the bare zero-sentinel pool.
    #[test]
    fn test_oob_sort_in_populated_pool_still_rejected() {
        let mut writer = ShardWriter::new();
        let name = writer.add_string("Bad");
        // Two levels: zero (pre-seeded) + succ(zero). Pool is populated, so an
        // OOB sort index is genuine corruption, not the legacy convention.
        let l1 = writer.add_level(FlatLevel::succ(0));
        assert_eq!(l1, 1);
        let bad = writer.add_expr(FlatExpr::sort(5)); // 5 >= level_count (2)
        writer.add_constant(MathverseConstantHeader {
            name_idx: name,
            type_idx: bad,
            value_idx: NO_VALUE,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: ImportConfidence::Translated as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: DeclKind::Definition as u8,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        });

        let mut buf = Vec::new();
        writer.write(&mut buf).expect("write");
        let err = ShardReader::from_bytes(&buf)
            .map(|_| ())
            .expect_err("OOB sort in a populated pool must still be rejected");
        assert!(
            err.to_string().contains("sort level index 5 out of bounds"),
            "unexpected error: {err}"
        );
    }
}
