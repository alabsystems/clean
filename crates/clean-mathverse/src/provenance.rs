// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Provenance sidecar — detailed import metadata for Mathverse Library constants.
//!
//! Stores cold-path information that is too large for the 32-byte
//! [`MathverseConstantHeader`] hot path. Each constant links to its provenance
//! record via `provenance_idx` and validates integrity via `sidecar_digest`
//! (blake3 truncated to 4 bytes).

use serde::{Deserialize, Serialize};

use crate::error::{MathverseError, MathverseResult};
use crate::types::{MathverseConstantHeader, SourceSystem};

/// Byte budget for decoding a provenance sidecar. Bounds bincode's allocation so
/// a corrupt length prefix cannot trigger a giant pre-allocation / abort; turns
/// it into a recoverable decode error. 4 GiB comfortably exceeds the largest
/// shipped sidecar (`lean4_mathlib4` ~71.6 MiB decompressed).
const DECODE_BUDGET_BYTES: usize = 4 * 1024 * 1024 * 1024;

/// Detailed provenance record for an imported constant.
/// Stored in the provenance sidecar (cold path), linked from
/// [`MathverseConstantHeader`] via `provenance_idx` and validated via `sidecar_digest`.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
pub struct ProvenanceRecord {
    /// Original name in the source system.
    pub original_name: String,
    /// Source file path (if known).
    pub source_file: Option<String>,
    /// Source line number (if known).
    pub source_line: Option<u32>,
    /// Source system version (e.g., "Coq 8.18", "Lean 4.3.0").
    pub source_version: Option<String>,
    /// Module/namespace path in the source system.
    pub module_path: Option<String>,
    /// Import timestamp (Unix epoch seconds).
    pub import_timestamp: u64,
    /// Import pipeline version.
    pub pipeline_version: u32,
    /// Translation notes (e.g., "Axiomatized: coinductive encoding").
    pub notes: Vec<String>,
    /// Dependencies in the source system (original names).
    pub source_deps: Vec<String>,
    /// Cross-references to equivalent constants in other systems.
    pub cross_refs: Vec<CrossReference>,
}

/// Cross-reference to an equivalent constant in another proof system.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
pub struct CrossReference {
    pub system: SourceSystem,
    pub name: String,
    /// Confidence that this is a true equivalence (0.0..=1.0).
    pub confidence: f32,
}

/// Which bincode encoding the records were (de)serialized with.
///
/// `Standard` is bincode 2.0 `config::standard()` (varint) — the current writer
/// format. `Legacy` is bincode 1.x / bincode 2.0 `config::legacy()` (fixed-int,
/// little-endian) — the format shards built before the bincode 1→2 migration
/// (commit 886baf53) carry. The sidecar remembers which encoding decoded it so
/// [`ProvenanceSidecar::verify_digest`] re-encodes records under the *same*
/// config; the stored `sidecar_digest` was computed under that config at build
/// time, so mixing configs would spuriously fail every legacy shard.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProvenanceEncoding {
    /// bincode 2.0 `config::standard()` (varint) — current writer format.
    Standard,
    /// bincode 1.x / `config::legacy()` (fixed-int LE) — pre-migration shards.
    Legacy,
}

/// Provenance sidecar — stores detailed metadata alongside the shard.
/// Records are indexed by position; [`MathverseConstantHeader::provenance_idx`]
/// holds the index into this container.
pub struct ProvenanceSidecar {
    records: Vec<ProvenanceRecord>,
    /// The encoding the records were decoded from (drives digest verification).
    /// `Standard` for freshly-built or in-memory sidecars.
    encoding: ProvenanceEncoding,
}

impl ProvenanceSidecar {
    /// Create an empty sidecar.
    pub fn new() -> Self {
        Self {
            records: Vec::new(),
            encoding: ProvenanceEncoding::Standard,
        }
    }

    /// The bincode encoding this sidecar's records were decoded from.
    #[must_use]
    pub fn encoding(&self) -> ProvenanceEncoding {
        self.encoding
    }

    /// Add a provenance record, returning its index.
    pub fn add(&mut self, record: ProvenanceRecord) -> u32 {
        let idx = self.records.len() as u32;
        self.records.push(record);
        idx
    }

    /// Get a record by index.
    pub fn get(&self, idx: u32) -> Option<&ProvenanceRecord> {
        self.records.get(idx as usize)
    }

    /// Number of records.
    #[must_use]
    pub fn len(&self) -> usize {
        self.records.len()
    }

    /// Whether the sidecar contains no records.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.records.is_empty()
    }

    /// Serialize to bytes (for embedding in shard via zstd compression).
    pub fn to_bytes(&self) -> MathverseResult<Vec<u8>> {
        bincode::serde::encode_to_vec(&self.records, bincode::config::standard()).map_err(|e| {
            MathverseError::ImportFailed {
                system: "provenance".to_string(),
                reason: format!("serialization failed: {e}"),
            }
        })
    }

    /// Deserialize from bytes, tolerating the legacy bincode encoding.
    ///
    /// Tries the current `config::standard()` (varint) first, then falls back to
    /// `config::legacy()` (fixed-int LE) for sidecars written before the
    /// bincode 1→2 migration. The recovered records are byte-for-byte the data
    /// the importer stored — this reads the legacy encoding correctly, it does
    /// not synthesize provenance. The chosen encoding is remembered so
    /// [`verify_digest`](Self::verify_digest) re-encodes under the same config.
    ///
    /// Both decodes are byte-budget-limited ([`DECODE_BUDGET_BYTES`]): the
    /// `legacy()` fixed-int config is `NoLimit` by default, so a corrupt sidecar
    /// with a bogus length prefix would otherwise try to pre-allocate a giant
    /// `Vec` and abort the process. The limit turns that into a recoverable
    /// decode error (the caller degrades to "provenance unavailable").
    pub fn from_bytes(data: &[u8]) -> MathverseResult<Self> {
        match bincode::serde::decode_from_slice::<Vec<ProvenanceRecord>, _>(
            data,
            bincode::config::standard().with_limit::<DECODE_BUDGET_BYTES>(),
        ) {
            Ok((records, _)) => Ok(Self {
                records,
                encoding: ProvenanceEncoding::Standard,
            }),
            Err(standard_err) => {
                match bincode::serde::decode_from_slice::<Vec<ProvenanceRecord>, _>(
                    data,
                    bincode::config::legacy().with_limit::<DECODE_BUDGET_BYTES>(),
                ) {
                    Ok((records, _)) => Ok(Self {
                        records,
                        encoding: ProvenanceEncoding::Legacy,
                    }),
                    // Report the standard-config error: it is the current format,
                    // and a sidecar that decodes under neither config is genuinely
                    // corrupt.
                    Err(_) => Err(MathverseError::ImportFailed {
                        system: "provenance".to_string(),
                        reason: format!("deserialization failed: {standard_err}"),
                    }),
                }
            }
        }
    }

    /// Compute the blake3 digest for a record under the current
    /// `config::standard()` encoding, truncated to 4 bytes. Matches
    /// `sidecar_digest` in [`MathverseConstantHeader`] for drift detection on
    /// freshly-written shards. For legacy-encoded sidecars use
    /// [`record_digest_with`](Self::record_digest_with).
    pub fn record_digest(record: &ProvenanceRecord) -> u32 {
        Self::record_digest_with(record, ProvenanceEncoding::Standard)
    }

    /// Compute a record's truncated blake3 digest under a specific bincode
    /// encoding. The stored `sidecar_digest` was computed under whichever
    /// encoding wrote the shard, so verification must re-encode with the same
    /// config.
    pub fn record_digest_with(record: &ProvenanceRecord, encoding: ProvenanceEncoding) -> u32 {
        let bytes = match encoding {
            ProvenanceEncoding::Standard => {
                bincode::serde::encode_to_vec(record, bincode::config::standard())
            }
            ProvenanceEncoding::Legacy => {
                bincode::serde::encode_to_vec(record, bincode::config::legacy())
            }
        }
        .unwrap_or_default();
        let hash = blake3::hash(&bytes);
        let h = hash.as_bytes();
        u32::from_le_bytes([h[0], h[1], h[2], h[3]])
    }

    /// Verify that a header's `sidecar_digest` matches its provenance record,
    /// re-encoding under the same bincode config the records were decoded from.
    pub fn verify_digest(&self, header: &MathverseConstantHeader) -> bool {
        match self.get(header.provenance_idx) {
            Some(record) => {
                Self::record_digest_with(record, self.encoding) == header.sidecar_digest
            }
            None => false,
        }
    }
}

impl Default for ProvenanceSidecar {
    fn default() -> Self {
        Self::new()
    }
}

/// Add provenance for a constant during shard writing.
/// Returns `(provenance_idx, sidecar_digest)` to set in [`MathverseConstantHeader`].
pub fn add_provenance(sidecar: &mut ProvenanceSidecar, record: ProvenanceRecord) -> (u32, u32) {
    let digest = ProvenanceSidecar::record_digest(&record);
    let idx = sidecar.add(record);
    (idx, digest)
}

/// Builder for creating provenance records during import with a fluent API.
pub struct ProvenanceBuilder {
    record: ProvenanceRecord,
}

impl ProvenanceBuilder {
    /// Start building a provenance record for the given original name.
    pub fn new(original_name: &str) -> Self {
        Self {
            record: ProvenanceRecord {
                original_name: original_name.to_string(),
                source_file: None,
                source_line: None,
                source_version: None,
                module_path: None,
                import_timestamp: 0,
                pipeline_version: 1,
                notes: Vec::new(),
                source_deps: Vec::new(),
                cross_refs: Vec::new(),
            },
        }
    }

    /// Set the source file path.
    pub fn source_file(mut self, path: &str) -> Self {
        self.record.source_file = Some(path.to_string());
        self
    }

    /// Set the source line number.
    pub fn source_line(mut self, line: u32) -> Self {
        self.record.source_line = Some(line);
        self
    }

    /// Set the source system version string.
    pub fn source_version(mut self, version: &str) -> Self {
        self.record.source_version = Some(version.to_string());
        self
    }

    /// Set the module/namespace path.
    pub fn module_path(mut self, path: &str) -> Self {
        self.record.module_path = Some(path.to_string());
        self
    }

    /// Set the import timestamp (Unix epoch seconds).
    pub fn import_timestamp(mut self, ts: u64) -> Self {
        self.record.import_timestamp = ts;
        self
    }

    /// Set the pipeline version.
    pub fn pipeline_version(mut self, version: u32) -> Self {
        self.record.pipeline_version = version;
        self
    }

    /// Add a translation note.
    pub fn note(mut self, note: &str) -> Self {
        self.record.notes.push(note.to_string());
        self
    }

    /// Add a source dependency.
    pub fn source_dep(mut self, dep: &str) -> Self {
        self.record.source_deps.push(dep.to_string());
        self
    }

    /// Add a cross-reference to an equivalent constant in another system.
    pub fn cross_ref(mut self, system: SourceSystem, name: &str, confidence: f32) -> Self {
        self.record.cross_refs.push(CrossReference {
            system,
            name: name.to_string(),
            confidence,
        });
        self
    }

    /// Consume the builder and return the completed record.
    pub fn build(self) -> ProvenanceRecord {
        self.record
    }
}

// ---------------------------------------------------------------------------
// ProvenanceQuery
// ---------------------------------------------------------------------------

/// Filtered provenance lookup with composable query predicates.
///
/// Build a query by chaining `by_source_system`, `by_module`, and `by_version`,
/// then call `execute` to find matching record indices.
pub struct ProvenanceQuery {
    source_system: Option<SourceSystem>,
    module_prefix: Option<String>,
    version_match: Option<String>,
}

impl ProvenanceQuery {
    /// Create a new empty query (matches everything).
    pub fn new() -> Self {
        Self {
            source_system: None,
            module_prefix: None,
            version_match: None,
        }
    }

    /// Filter by source system (from `ProvenanceRecord::cross_refs` or header context).
    /// Since `ProvenanceRecord` does not carry a `SourceSystem` directly, this
    /// matches records whose `source_version` string starts with the system name.
    #[must_use]
    pub fn by_source_system(mut self, system: SourceSystem) -> Self {
        self.source_system = Some(system);
        self
    }

    /// Filter by module path prefix.
    #[must_use]
    pub fn by_module(mut self, prefix: &str) -> Self {
        self.module_prefix = Some(prefix.to_string());
        self
    }

    /// Filter by source version (exact match).
    #[must_use]
    pub fn by_version(mut self, ver: &str) -> Self {
        self.version_match = Some(ver.to_string());
        self
    }

    /// Execute the query against a slice of provenance records.
    /// Returns indices of matching records.
    #[must_use]
    pub fn execute(&self, records: &[ProvenanceRecord]) -> Vec<usize> {
        records
            .iter()
            .enumerate()
            .filter(|(_, rec)| self.matches(rec))
            .map(|(i, _)| i)
            .collect()
    }

    fn matches(&self, record: &ProvenanceRecord) -> bool {
        if let Some(system) = self.source_system {
            let system_prefix = source_system_version_prefix(system);
            match &record.source_version {
                Some(ver) if ver.starts_with(system_prefix) => {}
                _ => return false,
            }
        }
        if let Some(prefix) = &self.module_prefix {
            match &record.module_path {
                Some(path) if path.starts_with(prefix.as_str()) => {}
                _ => return false,
            }
        }
        if let Some(ver) = &self.version_match {
            match &record.source_version {
                Some(sv) if sv == ver => {}
                _ => return false,
            }
        }
        true
    }
}

impl Default for ProvenanceQuery {
    fn default() -> Self {
        Self::new()
    }
}

/// Map a `SourceSystem` to the version string prefix used in `source_version`.
fn source_system_version_prefix(system: SourceSystem) -> &'static str {
    match system {
        SourceSystem::Lean4 => "Lean",
        SourceSystem::Coq => "Coq",
        SourceSystem::Agda => "Agda",
        SourceSystem::Idris2 => "Idris",
        SourceSystem::FStar => "FStar",
        SourceSystem::Cedille => "Cedille",
        SourceSystem::Isabelle => "Isabelle",
        SourceSystem::HolLight => "HOL Light",
        SourceSystem::Hol4 => "HOL4",
        SourceSystem::Metamath => "Metamath",
        SourceSystem::Mizar => "Mizar",
        SourceSystem::Dafny => "Dafny",
        SourceSystem::Why3 => "Why3",
        SourceSystem::Nuprl => "Nuprl",
        SourceSystem::Pvs => "PVS",
        SourceSystem::Acl2 => "ACL2",
        SourceSystem::LiquidHaskell => "LiquidHaskell",
        SourceSystem::Key => "KeY",
        SourceSystem::FramaC => "Frama-C",
        SourceSystem::Spark => "SPARK",
        SourceSystem::GammaCrown => "gamma-crown",
        SourceSystem::AlphaBetaCrown => "alpha-beta-crown",
        SourceSystem::Z3 => "Z3",
        SourceSystem::Cvc5 => "cvc5",
        SourceSystem::Vampire => "Vampire",
        SourceSystem::CaDiCaL => "CaDiCaL",
        SourceSystem::Tlc => "TLC",
        SourceSystem::CleanNative => "clean",
        SourceSystem::KeyFramacSpark => "KeY/Frama-C/SPARK",
        SourceSystem::SmtSolver => "SMT",
        SourceSystem::SatSolver => "SAT",
        SourceSystem::Atp => "ATP",
        SourceSystem::Arxiv => "arXiv",
        SourceSystem::Dedukti => "Dedukti",
        SourceSystem::Lambdapi => "Lambdapi",
        SourceSystem::Abella => "Abella",
        SourceSystem::Beluga => "Beluga",
        SourceSystem::Twelf => "Twelf",
        SourceSystem::Naproche => "Naproche",
        SourceSystem::Minlog => "Minlog",
        SourceSystem::Arend => "Arend",
        SourceSystem::Mm0 => "MM0",
        SourceSystem::Kind2 => "Kind2",
        SourceSystem::Rzk => "Rzk",
        SourceSystem::Ats2 => "ATS2",
        SourceSystem::Latte => "LaTTe",
        SourceSystem::CubicalTT => "CubicalTT",
        SourceSystem::Cooltt => "cooltt",
        SourceSystem::Redtt => "redtt",
        SourceSystem::Verus => "Verus",
        SourceSystem::Creusot => "Creusot",
        SourceSystem::Kani => "Kani",
        SourceSystem::Prusti => "Prusti",
        SourceSystem::Aeneas => "Aeneas",
        SourceSystem::Hax => "Hax",
        SourceSystem::CreuSat => "CreuSAT",
        SourceSystem::Stainless => "Stainless",
        SourceSystem::Lisa => "LISA",
        SourceSystem::MoveProver => "MoveProver",
        SourceSystem::Boogie => "Boogie",
        SourceSystem::Viper => "Viper",
        SourceSystem::VeriFast => "VeriFast",
        SourceSystem::Sail => "Sail",
        SourceSystem::KFramework => "K",
        SourceSystem::Alloy => "Alloy",
        SourceSystem::PLang => "P",
        SourceSystem::EthAct => "Act",
        SourceSystem::SvBenchmarks => "SV-COMP",
        SourceSystem::Matita => "Matita",
        SourceSystem::Cake => "Cake",
    }
}

// ---------------------------------------------------------------------------
// ProvenanceDiff
// ---------------------------------------------------------------------------

/// Describes a modification between two provenance records with the same name.
#[derive(Clone, Debug, PartialEq)]
pub struct ProvenanceModification {
    /// Original name shared by both records.
    pub name: String,
    /// Index in the old record list.
    pub old_idx: usize,
    /// Index in the new record list.
    pub new_idx: usize,
    /// Whether the version changed.
    pub version_changed: bool,
    /// Whether the module path changed.
    pub module_changed: bool,
}

/// Difference between two sets of provenance records.
#[derive(Clone, Debug, Default)]
pub struct ProvenanceDiff {
    /// Records present in `new` but not in `old` (by original_name).
    pub added: Vec<usize>,
    /// Records present in `old` but not in `new` (by original_name).
    pub removed: Vec<usize>,
    /// Records present in both but with differences.
    pub modified: Vec<ProvenanceModification>,
}

impl ProvenanceDiff {
    /// Compute the diff between two provenance record lists.
    ///
    /// Matching is done by `original_name`. Records with the same name are
    /// compared for version and module path changes.
    #[must_use]
    pub fn diff(old: &[ProvenanceRecord], new: &[ProvenanceRecord]) -> Self {
        use std::collections::HashMap;

        // Build index: name -> (idx, record) for old records.
        let old_map: HashMap<&str, (usize, &ProvenanceRecord)> = old
            .iter()
            .enumerate()
            .map(|(i, r)| (r.original_name.as_str(), (i, r)))
            .collect();
        let new_map: HashMap<&str, (usize, &ProvenanceRecord)> = new
            .iter()
            .enumerate()
            .map(|(i, r)| (r.original_name.as_str(), (i, r)))
            .collect();

        let mut result = ProvenanceDiff::default();

        // Find added and modified.
        for (name, &(new_idx, new_rec)) in &new_map {
            match old_map.get(name) {
                None => result.added.push(new_idx),
                Some(&(old_idx, old_rec)) => {
                    let version_changed = old_rec.source_version != new_rec.source_version;
                    let module_changed = old_rec.module_path != new_rec.module_path;
                    if version_changed || module_changed {
                        result.modified.push(ProvenanceModification {
                            name: name.to_string(),
                            old_idx,
                            new_idx,
                            version_changed,
                            module_changed,
                        });
                    }
                }
            }
        }

        // Find removed.
        for (name, &(old_idx, _)) in &old_map {
            if !new_map.contains_key(name) {
                result.removed.push(old_idx);
            }
        }

        // Sort for deterministic output.
        result.added.sort_unstable();
        result.removed.sort_unstable();
        result.modified.sort_by(|a, b| a.name.cmp(&b.name));

        result
    }

    /// Whether the diff is empty (no changes).
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.added.is_empty() && self.removed.is_empty() && self.modified.is_empty()
    }
}

// ---------------------------------------------------------------------------
// merge_provenance
// ---------------------------------------------------------------------------

/// Merge provenance records from multiple shards, deduplicating by `original_name`.
///
/// When duplicates exist, the record with the latest `import_timestamp` wins.
/// This is used when combining provenance sidecars from multiple shard files.
#[must_use]
pub fn merge_provenance(record_lists: &[Vec<ProvenanceRecord>]) -> Vec<ProvenanceRecord> {
    use std::collections::HashMap;

    let mut best: HashMap<String, ProvenanceRecord> = HashMap::new();

    for records in record_lists {
        for record in records {
            let entry = best.entry(record.original_name.clone());
            entry
                .and_modify(|existing| {
                    if record.import_timestamp > existing.import_timestamp {
                        *existing = record.clone();
                    }
                })
                .or_insert_with(|| record.clone());
        }
    }

    let mut result: Vec<ProvenanceRecord> = best.into_values().collect();
    result.sort_by(|a, b| a.original_name.cmp(&b.original_name));
    result
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{AxiomProfile, ImportConfidence, SourceSystem, NO_VALUE};

    fn sample_record() -> ProvenanceRecord {
        ProvenanceRecord {
            original_name: "Nat.add_comm".to_string(),
            source_file: Some("Mathlib/Data/Nat/Basic.lean".to_string()),
            source_line: Some(42),
            source_version: Some("Lean 4.3.0".to_string()),
            module_path: Some("Mathlib.Data.Nat.Basic".to_string()),
            import_timestamp: 1_711_700_000,
            pipeline_version: 1,
            notes: vec!["Translated via olean bridge".to_string()],
            source_deps: vec!["Nat".to_string(), "Nat.add".to_string()],
            cross_refs: vec![CrossReference {
                system: SourceSystem::Coq,
                name: "Nat.add_comm".to_string(),
                confidence: 0.95,
            }],
        }
    }

    fn sample_header(provenance_idx: u32, sidecar_digest: u32) -> MathverseConstantHeader {
        MathverseConstantHeader {
            name_idx: 0,
            type_idx: 1,
            value_idx: 2,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: ImportConfidence::Translated as u8,
            content_domain: 0,
            decl_kind: 0,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest,
            provenance_idx,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        }
    }

    #[test]
    fn test_record_serialization_round_trip() {
        let record = sample_record();
        let bytes =
            bincode::serde::encode_to_vec(&record, bincode::config::standard()).expect("serialize");
        let restored: ProvenanceRecord =
            bincode::serde::decode_from_slice(&bytes, bincode::config::standard())
                .map(|(__v, _)| __v)
                .expect("deserialize");
        assert_eq!(record, restored);
    }

    #[test]
    fn test_sidecar_add_get() {
        let mut sidecar = ProvenanceSidecar::new();
        assert!(sidecar.is_empty());
        assert_eq!(sidecar.len(), 0);

        let r0 = sample_record();
        let idx0 = sidecar.add(r0.clone());
        assert_eq!(idx0, 0);
        assert_eq!(sidecar.len(), 1);
        assert!(!sidecar.is_empty());

        let r1 = ProvenanceBuilder::new("Bool.not_not").build();
        let idx1 = sidecar.add(r1.clone());
        assert_eq!(idx1, 1);
        assert_eq!(sidecar.len(), 2);

        assert_eq!(sidecar.get(0), Some(&r0));
        assert_eq!(sidecar.get(1), Some(&r1));
        assert_eq!(sidecar.get(2), None);
    }

    #[test]
    fn test_sidecar_to_from_bytes_round_trip() {
        let mut sidecar = ProvenanceSidecar::new();
        sidecar.add(sample_record());
        sidecar.add(
            ProvenanceBuilder::new("List.map")
                .source_version("Lean 4.3.0")
                .note("Identity preservation verified")
                .build(),
        );

        let bytes = sidecar.to_bytes().expect("to_bytes");
        let restored = ProvenanceSidecar::from_bytes(&bytes).expect("from_bytes");

        assert_eq!(restored.len(), 2);
        assert_eq!(restored.get(0), sidecar.get(0));
        assert_eq!(restored.get(1), sidecar.get(1));
    }

    #[test]
    fn test_record_digest_deterministic() {
        let record = sample_record();
        let d1 = ProvenanceSidecar::record_digest(&record);
        let d2 = ProvenanceSidecar::record_digest(&record);
        assert_eq!(d1, d2);

        // Different record yields different digest (with overwhelming probability).
        let other = ProvenanceBuilder::new("different").build();
        let d3 = ProvenanceSidecar::record_digest(&other);
        assert_ne!(d1, d3);
    }

    #[test]
    fn test_verify_digest_matching() {
        let mut sidecar = ProvenanceSidecar::new();
        let record = sample_record();
        let (idx, digest) = add_provenance(&mut sidecar, record);

        let header = sample_header(idx, digest);
        assert!(sidecar.verify_digest(&header));
    }

    #[test]
    fn test_verify_digest_mismatch() {
        let mut sidecar = ProvenanceSidecar::new();
        let record = sample_record();
        let (idx, _digest) = add_provenance(&mut sidecar, record);

        // Wrong digest.
        let header = sample_header(idx, 0xBAD_CAFE);
        assert!(!sidecar.verify_digest(&header));
    }

    #[test]
    fn test_verify_digest_out_of_range() {
        let sidecar = ProvenanceSidecar::new();
        let header = sample_header(999, 0);
        assert!(!sidecar.verify_digest(&header));
    }

    #[test]
    fn test_builder_fluent_api() {
        let record = ProvenanceBuilder::new("Nat.add_comm")
            .source_file("Basic.lean")
            .source_line(42)
            .source_version("Lean 4.3.0")
            .module_path("Mathlib.Data.Nat.Basic")
            .import_timestamp(1_700_000_000)
            .pipeline_version(2)
            .note("Note 1")
            .note("Note 2")
            .source_dep("Nat")
            .source_dep("Nat.add")
            .cross_ref(SourceSystem::Coq, "Nat.add_comm", 0.95)
            .build();

        assert_eq!(record.original_name, "Nat.add_comm");
        assert_eq!(record.source_file.as_deref(), Some("Basic.lean"));
        assert_eq!(record.source_line, Some(42));
        assert_eq!(record.source_version.as_deref(), Some("Lean 4.3.0"));
        assert_eq!(
            record.module_path.as_deref(),
            Some("Mathlib.Data.Nat.Basic")
        );
        assert_eq!(record.import_timestamp, 1_700_000_000);
        assert_eq!(record.pipeline_version, 2);
        assert_eq!(record.notes, vec!["Note 1", "Note 2"]);
        assert_eq!(record.source_deps, vec!["Nat", "Nat.add"]);
        assert_eq!(record.cross_refs.len(), 1);
        assert_eq!(record.cross_refs[0].system, SourceSystem::Coq);
        assert_eq!(record.cross_refs[0].name, "Nat.add_comm");
        assert!((record.cross_refs[0].confidence - 0.95).abs() < f32::EPSILON);
    }

    #[test]
    fn test_empty_sidecar_round_trip() {
        let sidecar = ProvenanceSidecar::new();
        assert!(sidecar.is_empty());

        let bytes = sidecar.to_bytes().expect("to_bytes");
        let restored = ProvenanceSidecar::from_bytes(&bytes).expect("from_bytes");
        assert!(restored.is_empty());
        assert_eq!(restored.len(), 0);
    }

    #[test]
    fn test_sidecar_with_cross_references() {
        let record = ProvenanceBuilder::new("ring_theory.ideal.prime")
            .source_version("Coq 8.18")
            .cross_ref(SourceSystem::Lean4, "Ideal.IsPrime", 0.9)
            .cross_ref(SourceSystem::Isabelle, "prime_ideal", 0.75)
            .cross_ref(SourceSystem::Mizar, "IDEAL_1:def 6", 0.6)
            .build();

        assert_eq!(record.cross_refs.len(), 3);

        let mut sidecar = ProvenanceSidecar::new();
        sidecar.add(record);

        let bytes = sidecar.to_bytes().expect("to_bytes");
        let restored = ProvenanceSidecar::from_bytes(&bytes).expect("from_bytes");
        let r = restored.get(0).expect("record 0");
        assert_eq!(r.cross_refs.len(), 3);
        assert_eq!(r.cross_refs[0].system, SourceSystem::Lean4);
        assert_eq!(r.cross_refs[1].system, SourceSystem::Isabelle);
        assert_eq!(r.cross_refs[2].system, SourceSystem::Mizar);
    }

    #[test]
    fn test_digest_truncation_to_4_bytes() {
        // Verify the digest fits in u32 and is derived from blake3.
        let record = sample_record();
        let digest = ProvenanceSidecar::record_digest(&record);

        // Recompute manually.
        let bytes =
            bincode::serde::encode_to_vec(&record, bincode::config::standard()).expect("serialize");
        let hash = blake3::hash(&bytes);
        let expected = u32::from_le_bytes([
            hash.as_bytes()[0],
            hash.as_bytes()[1],
            hash.as_bytes()[2],
            hash.as_bytes()[3],
        ]);
        assert_eq!(digest, expected);
    }

    #[test]
    fn test_add_provenance_helper() {
        let mut sidecar = ProvenanceSidecar::new();
        let record = sample_record();
        let expected_digest = ProvenanceSidecar::record_digest(&record);

        let (idx, digest) = add_provenance(&mut sidecar, record.clone());
        assert_eq!(idx, 0);
        assert_eq!(digest, expected_digest);
        assert_eq!(sidecar.get(0), Some(&record));

        let r2 = ProvenanceBuilder::new("other").build();
        let (idx2, _) = add_provenance(&mut sidecar, r2);
        assert_eq!(idx2, 1);
        assert_eq!(sidecar.len(), 2);
    }

    #[test]
    fn test_axiomatized_constant_provenance() {
        let record = ProvenanceBuilder::new("Classical.choice")
            .source_version("Lean 4.3.0")
            .note("Axiomatized: no proof term")
            .build();

        let mut sidecar = ProvenanceSidecar::new();
        let (idx, digest) = add_provenance(&mut sidecar, record);

        let header = MathverseConstantHeader {
            name_idx: 0,
            type_idx: 1,
            value_idx: NO_VALUE,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: ImportConfidence::Axiomatized as u8,
            content_domain: 0,
            decl_kind: 0,
            axiom_profile: AxiomProfile::CHOICE | AxiomProfile::AXIOMATIZED,
            sidecar_digest: digest,
            provenance_idx: idx,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        };

        assert!(!header.has_value());
        assert!(header.is_trust_gated());
        assert!(sidecar.verify_digest(&header));
    }

    #[test]
    fn test_default_sidecar() {
        let sidecar = ProvenanceSidecar::default();
        assert!(sidecar.is_empty());
    }

    // -- ProvenanceQuery --

    fn make_records() -> Vec<ProvenanceRecord> {
        vec![
            ProvenanceBuilder::new("Nat.add_comm")
                .source_version("Lean 4.3.0")
                .module_path("Mathlib.Data.Nat.Basic")
                .import_timestamp(1000)
                .build(),
            ProvenanceBuilder::new("Bool.not_not")
                .source_version("Lean 4.3.0")
                .module_path("Mathlib.Data.Bool")
                .import_timestamp(1001)
                .build(),
            ProvenanceBuilder::new("ring_comm")
                .source_version("Coq 8.18")
                .module_path("Coq.Init.Ring")
                .import_timestamp(1002)
                .build(),
            ProvenanceBuilder::new("prime_ideal")
                .source_version("Isabelle/HOL 2023")
                .module_path("HOL.Algebra.Ring_Theory")
                .import_timestamp(1003)
                .build(),
        ]
    }

    #[test]
    fn test_query_empty_matches_all() {
        let records = make_records();
        let indices = ProvenanceQuery::new().execute(&records);
        assert_eq!(indices, vec![0, 1, 2, 3]);
    }

    #[test]
    fn test_query_by_module_prefix() {
        let records = make_records();
        let indices = ProvenanceQuery::new()
            .by_module("Mathlib.Data")
            .execute(&records);
        assert_eq!(indices, vec![0, 1]);
    }

    #[test]
    fn test_query_by_version_exact() {
        let records = make_records();
        let indices = ProvenanceQuery::new()
            .by_version("Coq 8.18")
            .execute(&records);
        assert_eq!(indices, vec![2]);
    }

    #[test]
    fn test_query_by_source_system() {
        let records = make_records();
        let indices = ProvenanceQuery::new()
            .by_source_system(SourceSystem::Lean4)
            .execute(&records);
        assert_eq!(indices, vec![0, 1]);
    }

    #[test]
    fn test_query_combined_filters() {
        let records = make_records();
        let indices = ProvenanceQuery::new()
            .by_source_system(SourceSystem::Lean4)
            .by_module("Mathlib.Data.Nat")
            .execute(&records);
        assert_eq!(indices, vec![0]);
    }

    #[test]
    fn test_query_no_matches() {
        let records = make_records();
        let indices = ProvenanceQuery::new()
            .by_version("Agda 2.7.0")
            .execute(&records);
        assert!(indices.is_empty());
    }

    // -- ProvenanceDiff --

    #[test]
    fn test_diff_identical() {
        let records = make_records();
        let diff = ProvenanceDiff::diff(&records, &records);
        assert!(diff.is_empty());
    }

    #[test]
    fn test_diff_added_removed() {
        let old = vec![
            ProvenanceBuilder::new("A").build(),
            ProvenanceBuilder::new("B").build(),
        ];
        let new = vec![
            ProvenanceBuilder::new("B").build(),
            ProvenanceBuilder::new("C").build(),
        ];
        let diff = ProvenanceDiff::diff(&old, &new);
        assert_eq!(diff.removed, vec![0]); // A removed (old idx 0)
        assert_eq!(diff.added, vec![1]); // C added (new idx 1)
        assert!(diff.modified.is_empty());
    }

    #[test]
    fn test_diff_modified_version() {
        let old = vec![ProvenanceBuilder::new("X")
            .source_version("Lean 4.2.0")
            .build()];
        let new = vec![ProvenanceBuilder::new("X")
            .source_version("Lean 4.3.0")
            .build()];
        let diff = ProvenanceDiff::diff(&old, &new);
        assert!(diff.added.is_empty());
        assert!(diff.removed.is_empty());
        assert_eq!(diff.modified.len(), 1);
        assert!(diff.modified[0].version_changed);
        assert!(!diff.modified[0].module_changed);
    }

    #[test]
    fn test_diff_empty_both() {
        let diff = ProvenanceDiff::diff(&[], &[]);
        assert!(diff.is_empty());
    }

    // -- merge_provenance --

    #[test]
    fn test_merge_deduplicates_by_name() {
        let shard_a = vec![
            ProvenanceBuilder::new("Nat.add")
                .import_timestamp(100)
                .build(),
            ProvenanceBuilder::new("Nat.mul")
                .import_timestamp(200)
                .build(),
        ];
        let shard_b = vec![
            ProvenanceBuilder::new("Nat.add")
                .import_timestamp(300)
                .source_version("Lean 4.4.0")
                .build(),
            ProvenanceBuilder::new("Bool.and")
                .import_timestamp(400)
                .build(),
        ];

        let merged = merge_provenance(&[shard_a, shard_b]);
        assert_eq!(merged.len(), 3); // Nat.add, Nat.mul, Bool.and

        // Nat.add should use the shard_b version (timestamp 300 > 100).
        let nat_add = merged
            .iter()
            .find(|r| r.original_name == "Nat.add")
            .unwrap();
        assert_eq!(nat_add.import_timestamp, 300);
        assert_eq!(nat_add.source_version.as_deref(), Some("Lean 4.4.0"));
    }

    #[test]
    fn test_merge_empty_shards() {
        let merged = merge_provenance(&[]);
        assert!(merged.is_empty());

        let merged = merge_provenance(&[vec![], vec![]]);
        assert!(merged.is_empty());
    }

    #[test]
    fn test_merge_single_shard() {
        let records = vec![
            ProvenanceBuilder::new("A").import_timestamp(1).build(),
            ProvenanceBuilder::new("B").import_timestamp(2).build(),
        ];
        let merged = merge_provenance(&[records]);
        assert_eq!(merged.len(), 2);
    }

    #[test]
    fn test_merge_sorted_by_name() {
        let shard = vec![
            ProvenanceBuilder::new("Z").build(),
            ProvenanceBuilder::new("A").build(),
            ProvenanceBuilder::new("M").build(),
        ];
        let merged = merge_provenance(&[shard]);
        let names: Vec<&str> = merged.iter().map(|r| r.original_name.as_str()).collect();
        assert_eq!(names, vec!["A", "M", "Z"]);
    }

    // --- Fix (3): legacy bincode-encoded provenance sidecar -----------------

    /// A sidecar serialized with the pre-migration bincode 1.x encoding
    /// (`config::legacy()`, fixed-int LE) must still decode — and report its
    /// encoding as `Legacy` — via `from_bytes`'s fallback. The shipped v1.3.0
    /// `lean4_stdlib` / `lean4_mathlib4` sidecars are in exactly this form.
    #[test]
    fn test_from_bytes_decodes_legacy_bincode() {
        let records = vec![sample_record(), ProvenanceBuilder::new("Bool.not").build()];
        // Write with the LEGACY (fixed-int) config, like a pre-migration shard.
        let legacy_bytes =
            bincode::serde::encode_to_vec(&records, bincode::config::legacy()).expect("encode");

        // The current standard() decode would fail on these bytes; from_bytes
        // must fall back to legacy() and recover them losslessly.
        let sidecar = ProvenanceSidecar::from_bytes(&legacy_bytes)
            .expect("legacy-encoded sidecar must decode via fallback");
        assert_eq!(sidecar.encoding(), ProvenanceEncoding::Legacy);
        assert_eq!(sidecar.len(), 2);
        assert_eq!(sidecar.get(0), Some(&records[0]));
        assert_eq!(sidecar.get(1), Some(&records[1]));
    }

    /// `verify_digest` re-encodes under the sidecar's own decoded config, so a
    /// digest computed at build time under legacy encoding matches after a
    /// legacy-fallback decode (and would NOT match under standard). This is the
    /// exact path the shipped `lean4_stdlib` / `lean4_mathlib4` sidecars take.
    #[test]
    fn test_verify_digest_matches_under_legacy_encoding() {
        let record = sample_record();
        // Build-time digest computed under the legacy encoding.
        let legacy_digest =
            ProvenanceSidecar::record_digest_with(&record, ProvenanceEncoding::Legacy);
        let standard_digest =
            ProvenanceSidecar::record_digest_with(&record, ProvenanceEncoding::Standard);
        // The two encodings differ for this record (varint vs fixed-int), so
        // using the wrong config would spuriously fail.
        assert_ne!(legacy_digest, standard_digest);

        // Two records so the legacy byte stream is unambiguously legacy (a
        // single short record can coincidentally parse under standard()); the
        // first record carries the digest we verify.
        let records = vec![record.clone(), ProvenanceBuilder::new("Bool.not").build()];
        let legacy_bytes =
            bincode::serde::encode_to_vec(&records, bincode::config::legacy()).expect("encode");
        let sidecar = ProvenanceSidecar::from_bytes(&legacy_bytes).expect("decode legacy");
        assert_eq!(
            sidecar.encoding(),
            ProvenanceEncoding::Legacy,
            "this payload must decode via the legacy fallback"
        );
        let header = sample_header(0, legacy_digest);
        assert!(
            sidecar.verify_digest(&header),
            "verify_digest must re-encode under the decoded (legacy) config"
        );
    }

    /// Standard-encoded sidecars still decode (and report `Standard`), so the
    /// fallback is purely additive — the current writer path is unaffected.
    #[test]
    fn test_from_bytes_still_decodes_standard_bincode() {
        let mut sidecar = ProvenanceSidecar::new();
        sidecar.add(sample_record());
        let bytes = sidecar.to_bytes().expect("to_bytes uses standard()");
        let restored = ProvenanceSidecar::from_bytes(&bytes).expect("decode standard");
        assert_eq!(restored.encoding(), ProvenanceEncoding::Standard);
        assert_eq!(restored.len(), 1);
        assert_eq!(restored.get(0), Some(&sample_record()));
    }

    /// Bytes that decode under neither config are reported as a genuine
    /// (decode) failure — the loader degrades on this, but the sidecar API
    /// itself still surfaces the error.
    #[test]
    fn test_from_bytes_rejects_undecodable_bytes() {
        // 0xFF-filled bytes: not a valid bincode Vec<ProvenanceRecord> under
        // standard or legacy (the leading length would be absurd).
        let garbage = vec![0xFFu8; 64];
        assert!(ProvenanceSidecar::from_bytes(&garbage).is_err());
    }
}
