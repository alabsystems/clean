// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Mathverse shard builder for gamma-crown proved theorems.
//!
//! Two public entry points:
//!
//! 1. [`build_gamma_crown_shard_library`] — thin wrapper over
//!    [`crate::build_library_native::build_native_shard_with_config`] that
//!    emits a kernel-flattened `.mathverse` shard tagged with
//!    `SourceSystem::GammaCrown` + `ContentDomain::NnVerification`. This is
//!    the Tier-1 constructive export path and shares all kernel-flattening
//!    logic with the clean-Native pipeline (#3473).
//!
//! 2. [`GammaCrownShardBuilder`] — namespace-prefix-filtered trust-report
//!    builder that walks the kernel `Environment` via
//!    [`classify_declaration`] and emits a trust-classified header per
//!    declaration (including `Trusted`, `Pending`, and `Axiom` tiers that
//!    the purity-gated native path rejects). The trust report is the source
//!    of truth for conjecture-level certification metrics.
//!
//! The two entry points are complementary: the native wrapper exports only
//! constructive theorems with full type/value expressions, while the trust
//! report classifies every declaration under a namespace (constructive,
//! trusted, pending, axiom) for human-readable audit output. A future
//! consolidation (see trust-report merge discussion in #3473) can fold the
//! report into `CleanNativeBuildResult.decisions`.
//!
//! Each [`GammaCrownShardBuilder`] header carries:
//! - `SourceSystem::GammaCrown` (20)
//! - `ContentDomain::NnVerification` (3)
//! - `ImportConfidence` derived from [`TrustClassification`]
//! - `AxiomProfile` computed by [`classify_declaration`]

use std::collections::HashMap;
use std::path::Path;

use crate::build_library_native::{
    build_native_shard_with_config, CleanNativeBuildResult, NativeBuildConfig,
};
use crate::error::{MathverseError, MathverseResult};
use crate::shard::ShardWriter;
use crate::trust::gamma_crown::{
    build_trust_report, classify_declaration, format_trust_report, DeclarationTrustSummary,
    GammaCrownTrustReport, ProofQuality, TrustClassification,
};
use crate::types::{
    ContentDomain, ImportConfidence, MathverseConstantHeader, SourceSystem, NO_VALUE,
};

// ---------------------------------------------------------------------------
// build_gamma_crown_shard_library — thin wrapper over the native pipeline
// ---------------------------------------------------------------------------

/// Default namespace prefixes that identify a constant as belonging to the
/// gamma-crown corpus. Constants that do not match any of these prefixes are
/// skipped by [`build_gamma_crown_shard_library`].
pub const GAMMA_CROWN_NAMESPACE_PREFIXES: &[&str] = &["NNVerify.", "GammaCrown.", "nn_verify."];

/// Build a gamma-crown `.mathverse` shard by delegating to the clean-Native save
/// pipeline with a gamma-crown-specific configuration (#3473).
///
/// This is a thin wrapper over
/// [`crate::build_library_native::build_native_shard_with_config`]. The
/// delegation preserves the env-walking, purity-gated classification, and
/// kernel-flattening logic of the native pipeline, but stamps every header
/// with [`SourceSystem::GammaCrown`] and restricts the scan to declarations
/// whose fully-qualified name starts with one of the
/// [`GAMMA_CROWN_NAMESPACE_PREFIXES`].
///
/// The output shard is written as `gamma-crown.mathverse` inside `out_dir`.
///
/// Like
/// [`build_clean_native_library`](crate::build_library_native::build_clean_native_library),
/// this accepts only theorems with an empty transitive domain-axiom
/// dependency set (`ProofQuality::Constructive`). Trust-classified exports
/// that include `Trusted` / `Pending` / `Axiom` tiers should use
/// [`GammaCrownShardBuilder`] instead — it emits the full trust report.
///
/// # Errors
///
/// Returns an error if the output directory cannot be created or the shard /
/// sidecar cannot be written. Per-declaration flattening failures are
/// recorded in `flatten_failures` and do not abort the build.
pub fn build_gamma_crown_shard_library(
    env: &clean_kernel::env::Environment,
    out_dir: &Path,
) -> MathverseResult<CleanNativeBuildResult> {
    let config = NativeBuildConfig {
        shard_filename: "gamma-crown.mathverse",
        metadata_system_name: "GammaCrown",
        source_system: SourceSystem::GammaCrown,
        namespace_prefixes: Some(
            GAMMA_CROWN_NAMESPACE_PREFIXES
                .iter()
                .map(|s| (*s).to_string())
                .collect(),
        ),
        // The gamma-crown shard is the intended home for NN-verification
        // content; its namespace filter already scopes it, so leave the
        // gate-clean filtering off to keep FLOAT_APPROX | NN_ABSTRACTION content.
        gate_clean: false,
    };
    build_native_shard_with_config(env, out_dir, &config)
}

// ---------------------------------------------------------------------------
// GammaCrownShardEntry
// ---------------------------------------------------------------------------

/// Input entry for the gamma-crown shard builder.
///
/// Represents a single declaration to be exported, with pre-extracted
/// proof quality data and string-encoded type/value expressions.
#[derive(Clone, Debug)]
pub struct GammaCrownShardEntry {
    /// Fully qualified declaration name.
    pub name: String,
    /// Pre-extracted proof quality from the kernel axiom audit.
    pub proof_quality: ProofQuality,
    /// Whether the declaration uses `sorry`.
    pub has_sorry: bool,
}

// ---------------------------------------------------------------------------
// GammaCrownShardBuilder
// ---------------------------------------------------------------------------

/// Builder for gamma-crown `.mathverse` shard files.
///
/// Collects declarations, classifies them via the trust accounting system,
/// and writes them to a `.mathverse` shard with correct trust metadata.
///
/// This is a lightweight builder that stores declaration metadata only (names
/// and trust classification). For full expression export, use
/// [`crate::export::kernel_export::KernelShardBuilder`] directly.
pub struct GammaCrownShardBuilder {
    writer: ShardWriter,
    entries: Vec<GammaCrownShardEntry>,
    trust_summaries: Vec<DeclarationTrustSummary>,
}

impl GammaCrownShardBuilder {
    /// Create a new builder.
    #[must_use]
    pub fn new() -> Self {
        Self {
            writer: ShardWriter::new(),
            entries: Vec::new(),
            trust_summaries: Vec::new(),
        }
    }

    /// Add a declaration entry to the shard.
    ///
    /// The declaration is classified via the trust accounting system and
    /// a constant header is written to the shard with appropriate metadata.
    ///
    /// Returns the constant index in the shard.
    pub fn add_entry(&mut self, entry: GammaCrownShardEntry) -> u32 {
        let trust_summary =
            classify_declaration(&entry.name, &entry.proof_quality, entry.has_sorry);

        // Add name to string table.
        let name_idx = self.writer.add_string(&entry.name);
        // The header uses `type_idx: 0` and `value_idx: 0` as placeholders
        // for a builder that doesn't carry type-expression data. The
        // shard reader's validator requires every type_idx be < expr_count
        // and every non-NO_VALUE value_idx be < expr_count, so we must
        // guarantee at least one expression exists at index 0. Dedup
        // makes subsequent calls a no-op.
        let _ = self.writer.add_expr(clean_kernel::flat::FlatExpr::sort(0));

        // Map trust classification to import confidence.
        let import_confidence = match trust_summary.classification {
            TrustClassification::Constructive => ImportConfidence::KernelVerified,
            TrustClassification::Trusted => ImportConfidence::Translated,
            TrustClassification::Pending => ImportConfidence::Unverified,
            TrustClassification::Axiom => ImportConfidence::Axiomatized,
        };

        let header = MathverseConstantHeader {
            name_idx,
            type_idx: 0, // placeholder — no expression data in this builder
            value_idx: if trust_summary.classification == TrustClassification::Axiom
                || trust_summary.classification == TrustClassification::Pending
            {
                NO_VALUE
            } else {
                0 // placeholder
            },
            source_system: SourceSystem::GammaCrown as u8,
            import_confidence: import_confidence as u8,
            content_domain: ContentDomain::NnVerification as u8,
            decl_kind: match trust_summary.classification {
                TrustClassification::Constructive | TrustClassification::Trusted => 0, // Theorem
                TrustClassification::Pending => 0, // Theorem (unchecked)
                TrustClassification::Axiom => 2,   // Axiom
            },
            axiom_profile: trust_summary.axiom_profile,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        };

        let const_idx = self.writer.add_constant(header);

        self.trust_summaries.push(trust_summary);
        self.entries.push(entry);

        const_idx
    }

    /// Build the trust report for all added declarations.
    #[must_use]
    pub fn trust_report(&self) -> GammaCrownTrustReport {
        build_trust_report(&self.trust_summaries)
    }

    /// Format the trust report as markdown.
    #[must_use]
    pub fn format_report(&self) -> String {
        format_trust_report(&self.trust_report())
    }

    /// Number of entries added.
    #[inline]
    #[must_use]
    pub fn entry_count(&self) -> usize {
        self.entries.len()
    }

    /// Access the trust summaries for all added declarations.
    pub fn trust_summaries(&self) -> &[DeclarationTrustSummary] {
        &self.trust_summaries
    }

    /// Write the shard to a file.
    pub fn write_to_file(&self, path: impl AsRef<Path>) -> MathverseResult<()> {
        self.writer.write_to_file(path)
    }

    /// Write the shard to a byte buffer (for tests).
    pub fn write_to_bytes(&self) -> MathverseResult<Vec<u8>> {
        let mut buf = Vec::new();
        self.writer.write(&mut buf)?;
        Ok(buf)
    }

    /// Harvest gamma-crown declarations from a kernel [`clean_kernel::env::Environment`].
    ///
    /// For each constant whose name begins with one of the supplied namespace
    /// prefixes (e.g. `"NNVerify."`, `"NNVerification."`), classifies the
    /// declaration via [`clean_kernel::env::Environment::proof_quality`] and
    /// adds a shard entry with the correct trust metadata.
    ///
    /// This is the primary bridge between a type-checked kernel environment
    /// and the Mathverse shard format. Returns the number of entries added.
    ///
    /// # Example
    ///
    /// ```text
    /// use clean_kernel::env::Environment;
    /// use clean_mathverse::gamma_crown_shard::GammaCrownShardBuilder;
    ///
    /// // env_with_c001() is a fixture that loads the C001 declarations into
    /// // a kernel Environment (env.init_nn_verify_c001() is pub(crate) in
    /// // clean-kernel, so this snippet shows the conceptual shape rather than
    /// // running as a doctest).
    /// let env = env_with_c001();
    ///
    /// let mut builder = GammaCrownShardBuilder::new();
    /// let added = builder.add_environment(&env, &["NNVerify."]);
    /// assert!(added > 0, "expected C001 declarations in environment");
    /// ```
    pub fn add_environment(
        &mut self,
        env: &clean_kernel::env::Environment,
        namespace_prefixes: &[&str],
    ) -> usize {
        let mut added = 0usize;
        let names: Vec<String> = env
            .constants()
            .map(|c| c.name.to_string())
            .filter(|s| {
                namespace_prefixes
                    .iter()
                    .any(|prefix| s.starts_with(prefix))
            })
            .collect();

        for fq_name in names {
            let kernel_name = clean_kernel::name::Name::from_string(&fq_name);
            let Some(kernel_quality) = env.proof_quality(&kernel_name) else {
                continue;
            };
            let entry = GammaCrownShardEntry {
                name: fq_name,
                proof_quality: ProofQuality::from(kernel_quality),
                has_sorry: false,
            };
            self.add_entry(entry);
            added += 1;
        }

        added
    }
}

impl Default for GammaCrownShardBuilder {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Shard export statistics
// ---------------------------------------------------------------------------

/// Statistics from a gamma-crown shard export.
#[derive(Clone, Debug, Default)]
pub struct GammaCrownExportStats {
    /// Total declarations exported.
    pub total_entries: usize,
    /// Constructive (fully proved) entries.
    pub constructive_count: usize,
    /// Trusted (axiom-dependent) entries.
    pub trusted_count: usize,
    /// Pending (sorry/unchecked) entries.
    pub pending_count: usize,
    /// Axiom entries.
    pub axiom_count: usize,
    /// Distinct domain-specific axioms across all entries.
    pub domain_axiom_count: usize,
    /// Per-conjecture summary (conjecture_id -> is_fully_constructive).
    pub conjecture_status: HashMap<String, bool>,
}

impl From<&GammaCrownTrustReport> for GammaCrownExportStats {
    fn from(report: &GammaCrownTrustReport) -> Self {
        Self {
            total_entries: report.all_declarations.len(),
            constructive_count: report.total_constructive,
            trusted_count: report.total_trusted,
            pending_count: report.total_pending,
            axiom_count: report.total_axioms,
            domain_axiom_count: report.total_domain_axioms,
            conjecture_status: report
                .conjecture_summaries
                .iter()
                .map(|(id, s)| (id.clone(), s.is_fully_constructive))
                .collect(),
        }
    }
}

// ---------------------------------------------------------------------------
// Tests — extracted to gamma_crown_shard_tests.rs (#3379) to keep this
// file under the 500-line production cap.
// ---------------------------------------------------------------------------

#[cfg(test)]
#[path = "gamma_crown_shard_tests.rs"]
mod tests;
