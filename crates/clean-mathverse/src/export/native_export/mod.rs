// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Native theorem export pipeline: kernel `Expr` to `.mathverse` shard with metadata.
//!
//! Provides a higher-level API on top of [`crate::export::kernel_export::KernelShardBuilder`]
//! that adds:
//! - Tag-based search metadata (research-area keywords)
//! - Conjecture cross-references (gamma-crown C001-C012, C028-C030)
//! - `.mathverse.json` metadata sidecar with tags and conjecture IDs
//! - A hardcoded manifest of known nn_verify theorems

use std::collections::HashMap;
use std::path::Path;

use clean_kernel::expr::Expr;
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::Declaration;

use crate::error::{MathverseError, MathverseResult};
use crate::export::kernel_export::KernelShardBuilder;
use crate::shard_metadata::{DeclKind, MetadataEntry, ShardMetadata};
use crate::types::{AxiomProfile, ContentDomain};

#[cfg(test)]
mod tests;

// ---------------------------------------------------------------------------
// NativeTheoremEntry
// ---------------------------------------------------------------------------

/// A theorem entry to be exported to an mathverse shard.
///
/// Wraps a kernel `Expr` pair (type + optional value) with export metadata:
/// tags for search indexing and an optional conjecture cross-reference.
#[derive(Clone, Debug)]
pub struct NativeTheoremEntry {
    /// Fully qualified name (dot-separated, e.g. `nn_verify.compress_soundness`).
    pub name: String,
    /// The type expression of the theorem.
    pub type_expr: Expr,
    /// The proof term (value), if the theorem is proved. `None` for axioms.
    pub value_expr: Option<Expr>,
    /// Content domain classification.
    pub content_domain: ContentDomain,
    /// Axiom profile bits for this entry.
    pub axiom_profile: AxiomProfile,
    /// Research-area keyword tags (e.g. `["zonotope", "CROWN", "IBP"]`).
    pub tags: Vec<String>,
    /// Cross-reference to a gamma-crown conjecture (e.g. `"C001"`).
    pub conjecture_id: Option<String>,
}

// ---------------------------------------------------------------------------
// ExportStats
// ---------------------------------------------------------------------------

/// Statistics returned after exporting native theorems to a shard.
#[derive(Clone, Debug, Default)]
pub struct ExportStats {
    /// Total entries written to the shard.
    pub entries_written: usize,
    /// Count of entries by content domain.
    pub by_domain: HashMap<u8, usize>,
}

// ---------------------------------------------------------------------------
// NativeShardMetadata (JSON sidecar extension)
// ---------------------------------------------------------------------------

/// Extended metadata sidecar with tags and conjecture cross-references.
///
/// Written alongside the `.mathverse` shard as `.mathverse.json`.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub(crate) struct NativeShardMetadata {
    /// Base shard metadata (declarations, system name, etc.).
    #[serde(flatten)]
    pub(crate) base: ShardMetadata,
    /// Per-declaration tags (name -> tags list).
    pub(crate) tags: HashMap<String, Vec<String>>,
    /// Per-declaration conjecture cross-references (name -> conjecture_id).
    pub(crate) conjecture_refs: HashMap<String, String>,
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Export native theorems to an mathverse shard file with metadata sidecar.
///
/// Creates both `output_path` (the `.mathverse` binary shard) and
/// `output_path.json` (the metadata sidecar with tags and conjecture refs).
///
/// Each `NativeTheoremEntry` is converted to a kernel `Declaration::Theorem`
/// (or `Declaration::Axiom` if `value_expr` is `None`) and fed through
/// `KernelShardBuilder` for Expr->FlatExpr->shard conversion.
///
/// # Errors
///
/// Returns an error if expression flattening fails or the shard cannot be written.
pub fn export_native_theorems(
    entries: &[NativeTheoremEntry],
    output_path: &Path,
) -> MathverseResult<ExportStats> {
    let mut exporter = StreamingShardExporter::new();
    for entry in entries {
        exporter.add(entry)?;
    }
    exporter.finish(output_path)
}

/// Incremental shard exporter: feed verified theorems one at a time via [`add`],
/// then [`finish`]. Peak memory holds only the (deduplicated) shard arena, never a
/// `Vec` of all entries — this is what lets the full Metamath corpus (~25-30k
/// theorems whose proof values are ~3 MB each) export without OOM. The pipeline of
/// operations is identical to the old batch path, so the resulting shard is
/// byte-for-byte the same for the same entry sequence.
///
/// [`add`]: StreamingShardExporter::add
/// [`finish`]: StreamingShardExporter::finish
#[must_use = "call `finish` to write the shard"]
pub struct StreamingShardExporter {
    builder: KernelShardBuilder,
    base_metadata: ShardMetadata,
    tags_map: HashMap<String, Vec<String>>,
    conj_map: HashMap<String, String>,
    stats: ExportStats,
}

impl Default for StreamingShardExporter {
    fn default() -> Self {
        Self::new()
    }
}

impl StreamingShardExporter {
    pub fn new() -> Self {
        Self {
            builder: KernelShardBuilder::new(),
            base_metadata: ShardMetadata::new("CleanNative"),
            tags_map: HashMap::new(),
            conj_map: HashMap::new(),
            stats: ExportStats::default(),
        }
    }

    /// Trust value-LESS entries (those added with `value_expr: None`) as
    /// [`crate::types::ImportConfidence::KernelVerified`] rather than
    /// `Axiomatized`. See [`KernelShardBuilder::with_value_less_kernel_verified`]
    /// — OPT-IN, only sound when every value-less entry was already kernel-
    /// verified (e.g. a `--type-only` Metamath export).
    pub fn with_value_less_kernel_verified(mut self, yes: bool) -> Self {
        self.builder = self.builder.with_value_less_kernel_verified(yes);
        self
    }

    /// Add one verified theorem to the shard. Streaming-safe: retains only this
    /// entry's metadata plus the shared, deduplicated expression arena.
    ///
    /// # Errors
    /// Returns an error if the entry's expressions cannot be flattened into the
    /// shard arena.
    pub fn add(&mut self, entry: &NativeTheoremEntry) -> MathverseResult<()> {
        let tag_refs: Vec<&str> = entry.tags.iter().map(|s| s.as_str()).collect();
        let decl = entry_to_declaration(entry);
        // Add to the shard builder, preserving the entry's explicit axiom
        // profile. This is load-bearing for HONESTY: kernel-verified imports
        // that remain axiom-relative (e.g. Metamath theorems resting on the
        // `$a` postulates, tagged `AxiomProfile::AXIOMATIZED`) must carry that
        // bit through to the shard header so they are trust-gated rather than
        // mislabeled as foundational-only proofs. The `has_value`-only
        // heuristic inside the builder would otherwise drop it.
        self.builder
            .add_declaration_with_extra_profile(&decl, &tag_refs, entry.axiom_profile)
            .map_err(|e| MathverseError::Kernel(format!("failed to export {}: {e}", entry.name)))?;

        let kind = if entry.value_expr.is_some() {
            DeclKind::Theorem
        } else {
            DeclKind::Axiom
        };
        self.base_metadata.push(MetadataEntry {
            name: entry.name.clone(),
            kind: Some(kind),
            type_signature: None,
            source_file: None,
            line_number: None,
        });

        if !entry.tags.is_empty() {
            self.tags_map.insert(entry.name.clone(), entry.tags.clone());
        }
        if let Some(ref conj_id) = entry.conjecture_id {
            self.conj_map.insert(entry.name.clone(), conj_id.clone());
        }

        self.stats.entries_written += 1;
        *self
            .stats
            .by_domain
            .entry(entry.content_domain as u8)
            .or_insert(0) += 1;
        Ok(())
    }

    /// Number of entries added so far.
    #[must_use]
    pub fn len(&self) -> usize {
        self.stats.entries_written
    }

    /// Whether no entries have been added yet.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.stats.entries_written == 0
    }

    /// Write the binary shard and the JSON metadata sidecar; return the stats.
    ///
    /// # Errors
    /// Returns an error if the shard or sidecar cannot be written.
    pub fn finish(self, output_path: &Path) -> MathverseResult<ExportStats> {
        self.builder.write_to_file(output_path)?;
        let native_meta = NativeShardMetadata {
            base: self.base_metadata,
            tags: self.tags_map,
            conjecture_refs: self.conj_map,
        };
        let sidecar_path = crate::shard_metadata::sidecar_path_for(output_path);
        let json = serde_json::to_string_pretty(&native_meta).map_err(MathverseError::from)?;
        std::fs::write(&sidecar_path, json)?;
        Ok(self.stats)
    }
}

/// Collect the hardcoded manifest of known nn_verify theorems.
///
/// Returns `NativeTheoremEntry` stubs for 16 theorem entries spanning all 15
/// gamma-crown conjectures (C001-C012, C028-C030). C001 has two entries
/// (soundness + tightness). Each entry uses `Prop` as its type and value
/// (placeholders), with the correct `ContentDomain`, `AxiomProfile`, tags,
/// and conjecture IDs.
///
/// In production use, callers would replace `type_expr`/`value_expr` with the
/// actual kernel-verified expressions from the theorem registry.
#[must_use]
pub fn collect_nn_verify_theorems() -> Vec<NativeTheoremEntry> {
    let prop = Expr::sort(Level::zero());

    let manifest: [(&str, &str, &[&str]); 16] = [
        (
            "nn_verify.compress_soundness",
            "C001",
            &["zonotope", "CROWN", "compression"][..],
        ),
        (
            "nn_verify.compress_tightness",
            "C001",
            &["zonotope", "CROWN", "compression"],
        ),
        (
            "nn_verify.correlation_firewall",
            "C002",
            &["correlation", "independence", "LayerNorm"],
        ),
        (
            "nn_verify.eclipse_convergence",
            "C003",
            &["eclipse", "convergence", "Banach", "contraction"],
        ),
        (
            "nn_verify.crown_equals_ibp",
            "C004",
            &["CROWN", "IBP", "LayerNorm", "equivalence"],
        ),
        (
            "nn_verify.mccormick_attention_tight",
            "C005",
            &["McCormick", "attention", "tightness"],
        ),
        (
            "nn_verify.blockwise_equals_monolithic",
            "C006",
            &["blockwise", "monolithic", "CROWN", "equivalence"],
        ),
        (
            "nn_verify.streaming_cert_soundness",
            "C007",
            &["streaming", "certificates", "BnB", "incremental"],
        ),
        (
            "nn_verify.ibp_tightness_bound",
            "C008",
            &["IBP", "tightness", "bound", "depth"],
        ),
        (
            "nn_verify.crown_exponential_gap",
            "C009",
            &["CROWN", "IBP", "exponential", "depth"],
        ),
        (
            "nn_verify.zonotope_crown_equivalence",
            "C010",
            &["zonotope", "CROWN", "equivalence", "linear"],
        ),
        (
            "nn_verify.softmax_width_monotone",
            "C011",
            &["softmax", "monotonicity", "IBP", "width"],
        ),
        (
            "nn_verify.relu_stability",
            "C012",
            &["ReLU", "stability", "activation", "exact"],
        ),
        (
            "nn_verify.nullstellensatz_sos",
            "C028",
            &["nullstellensatz", "SoS", "polynomial", "certificate"],
        ),
        (
            "nn_verify.pac_to_proof",
            "C029",
            &["PAC", "PGD", "adversarial", "certificate"],
        ),
        (
            "nn_verify.orbit_crown_speedup",
            "C030",
            &["orbit", "symmetry", "quotient", "CROWN"],
        ),
    ];

    manifest
        .iter()
        .map(|(name, conj_id, tags)| NativeTheoremEntry {
            name: name.to_string(),
            type_expr: prop.clone(),
            value_expr: Some(prop.clone()),
            content_domain: ContentDomain::NnVerification,
            axiom_profile: AxiomProfile::FLOAT_APPROX | AxiomProfile::NN_ABSTRACTION,
            tags: tags.iter().map(|s| s.to_string()).collect(),
            conjecture_id: Some(conj_id.to_string()),
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

/// Convert a `NativeTheoremEntry` to a kernel `Declaration`.
fn entry_to_declaration(entry: &NativeTheoremEntry) -> Declaration {
    let name = Name::from_string(&entry.name);
    if let Some(ref value) = entry.value_expr {
        Declaration::Theorem {
            name,
            level_params: vec![],
            type_: entry.type_expr.clone(),
            value: value.clone(),
        }
    } else {
        Declaration::Axiom {
            name,
            level_params: vec![],
            type_: entry.type_expr.clone(),
        }
    }
}
