// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean 4 `.olean` to `.mathverse` shard importer.
//!
//! High-level API that bridges `clean-olean`'s `.olean` parser to mathverse
//! shard output. Loads `.olean` files via [`clean_olean::parse_module_file`],
//! converts constants through [`crate::lean4::olean::alpha::import_module`], and
//! writes `.mathverse` shards via [`ShardWriter`].
//!
//! # Axiom profile mapping
//!
//! Lean 4's three foundational axioms are mapped to `AxiomProfile` bits:
//!
//! | Lean 4 axiom         | Profile bit       |
//! |---------------------|-------------------|
//! | `Classical.choice`  | `CHOICE`          |
//! | `propext`           | `PROP_EXT`        |
//! | `Quot.*`            | `QUOT`            |
//!
//! Any `Axiom` or `Opaque` constant also gets `AXIOMATIZED`.
//!
//! # Example
//!
//! ```rust,no_run
//! use clean_mathverse::importers::lean4_olean::Lean4OleanImporter;
//! use std::path::Path;
//!
//! let importer = Lean4OleanImporter::new();
//! let result = importer.import_file(
//!     Path::new("Init/Prelude.olean"),
//!     Path::new("output/lean4.mathverse"),
//! ).expect("import failed");
//! assert!(result.stats.total > 0);
//! ```

use std::path::Path;

use clean_olean::module::ParsedModule;
use clean_olean::parse_module_file;

use crate::error::{MathverseError, MathverseResult};
use crate::lean4::olean::alpha::{
    import_module, import_with_provenance, ImportStats, Lean4ImportConfig,
};
use crate::provenance::ProvenanceRecord;
use crate::shard::{ShardReader, ShardWriter};

// ---------------------------------------------------------------------------
// Lean4OleanImporter
// ---------------------------------------------------------------------------

/// High-level importer that converts Lean 4 `.olean` files to `.mathverse` shards.
///
/// Wraps the lower-level [`import_module`] pipeline with file I/O and
/// configurable filtering options.
pub struct Lean4OleanImporter {
    config: Lean4ImportConfig,
}

impl Lean4OleanImporter {
    /// Create a new importer with default settings.
    pub fn new() -> Self {
        Self {
            config: Lean4ImportConfig::default(),
        }
    }

    /// Create a new importer with the given configuration.
    pub fn with_config(config: Lean4ImportConfig) -> Self {
        Self { config }
    }

    /// Import a single `.olean` file and write a `.mathverse` shard.
    ///
    /// Parses the `.olean` file via `clean-olean`, converts all constants
    /// into `MathverseConstantHeader`s with axiom profiles, and writes the
    /// result to the specified output path.
    pub fn import_file(
        &self,
        olean_path: &Path,
        output_path: &Path,
    ) -> MathverseResult<ImportResult> {
        let module = parse_olean(olean_path)?;
        let mut writer = ShardWriter::new();

        let (stats, provenance) = import_with_provenance(&module, &mut writer, &self.config)?;

        writer.write_to_file(output_path)?;

        let dedup = writer.dedup_stats();

        Ok(ImportResult {
            stats,
            provenance,
            dedup_stats: DedupSummary {
                exprs_total: dedup.exprs_total,
                exprs_deduped: dedup.exprs_deduped,
                levels_total: dedup.levels_total,
                levels_deduped: dedup.levels_deduped,
                strings_total: dedup.strings_total,
                strings_deduped: dedup.strings_deduped,
            },
        })
    }

    /// Import a single `.olean` file into an existing `ShardWriter`.
    ///
    /// Use this when combining multiple `.olean` files into one shard.
    /// The caller is responsible for writing the shard afterward.
    pub fn import_into(
        &self,
        olean_path: &Path,
        writer: &mut ShardWriter,
    ) -> MathverseResult<ImportStats> {
        let module = parse_olean(olean_path)?;
        import_module(&module, writer)
    }

    /// Import a pre-parsed `ParsedModule` and write a `.mathverse` shard.
    ///
    /// Use this when you already have a `ParsedModule` from `clean-olean`
    /// (e.g., from a cached parse or a module loaded into memory).
    pub fn import_parsed_module(
        &self,
        module: &ParsedModule,
        output_path: &Path,
    ) -> MathverseResult<ImportResult> {
        let mut writer = ShardWriter::new();

        let (stats, provenance) = import_with_provenance(module, &mut writer, &self.config)?;

        writer.write_to_file(output_path)?;

        let dedup = writer.dedup_stats();

        Ok(ImportResult {
            stats,
            provenance,
            dedup_stats: DedupSummary {
                exprs_total: dedup.exprs_total,
                exprs_deduped: dedup.exprs_deduped,
                levels_total: dedup.levels_total,
                levels_deduped: dedup.levels_deduped,
                strings_total: dedup.strings_total,
                strings_deduped: dedup.strings_deduped,
            },
        })
    }

    /// Import a pre-parsed `ParsedModule` into an existing `ShardWriter`.
    pub fn import_parsed_into(
        &self,
        module: &ParsedModule,
        writer: &mut ShardWriter,
    ) -> MathverseResult<ImportStats> {
        import_module(module, writer)
    }

    /// Import multiple `.olean` files into a single `.mathverse` shard.
    ///
    /// All constants are merged into one shard with shared string tables,
    /// level pools, and expression arenas for maximum deduplication.
    pub fn import_files(
        &self,
        olean_paths: &[&Path],
        output_path: &Path,
    ) -> MathverseResult<ImportResult> {
        let mut writer = ShardWriter::new();
        let mut total_stats = ImportStats::default();
        let mut all_provenance = Vec::new();

        for path in olean_paths {
            let module = parse_olean(path)?;
            let (stats, prov) = import_with_provenance(&module, &mut writer, &self.config)?;

            total_stats.total += stats.total;
            total_stats.kernel_verified += stats.kernel_verified;
            total_stats.axiomatized += stats.axiomatized;
            total_stats.skipped += stats.skipped;
            all_provenance.extend(prov);
        }

        writer.write_to_file(output_path)?;

        let dedup = writer.dedup_stats();

        Ok(ImportResult {
            stats: total_stats,
            provenance: all_provenance,
            dedup_stats: DedupSummary {
                exprs_total: dedup.exprs_total,
                exprs_deduped: dedup.exprs_deduped,
                levels_total: dedup.levels_total,
                levels_deduped: dedup.levels_deduped,
                strings_total: dedup.strings_total,
                strings_deduped: dedup.strings_deduped,
            },
        })
    }

    /// Verify a previously written `.mathverse` shard by reading it back and
    /// checking structural invariants.
    pub fn verify_shard(path: &Path) -> MathverseResult<ShardVerification> {
        let reader = ShardReader::from_file(path)?;

        let mut axiomatized = 0u32;
        let mut kernel_verified = 0u32;
        let mut trust_gated = 0u32;

        for constant in &reader.constants {
            if !constant.has_value() {
                axiomatized += 1;
            } else {
                kernel_verified += 1;
            }
            if constant.is_trust_gated() {
                trust_gated += 1;
            }
        }

        Ok(ShardVerification {
            constant_count: reader.header.constant_count,
            expr_count: reader.header.expr_count,
            level_count: reader.header.level_count,
            string_count: reader.header.string_count,
            axiomatized,
            kernel_verified,
            trust_gated,
            has_sorted_index: reader.has_sorted_index(),
        })
    }
}

impl Default for Lean4OleanImporter {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Result types
// ---------------------------------------------------------------------------

/// Result of importing one or more `.olean` files into an `.mathverse` shard.
#[derive(Clone, Debug)]
pub struct ImportResult {
    /// Per-constant import statistics.
    pub stats: ImportStats,
    /// Provenance records (one per constant, in order).
    pub provenance: Vec<ProvenanceRecord>,
    /// Deduplication statistics for expressions, levels, and strings.
    pub dedup_stats: DedupSummary,
}

/// Summary of hash-consing deduplication during shard writing.
#[derive(Clone, Debug, Default)]
pub struct DedupSummary {
    pub exprs_total: u64,
    pub exprs_deduped: u64,
    pub levels_total: u64,
    pub levels_deduped: u64,
    pub strings_total: u64,
    pub strings_deduped: u64,
}

/// Result of verifying a `.mathverse` shard.
#[derive(Clone, Debug)]
pub struct ShardVerification {
    pub constant_count: u32,
    pub expr_count: u32,
    pub level_count: u32,
    pub string_count: u32,
    pub axiomatized: u32,
    pub kernel_verified: u32,
    pub trust_gated: u32,
    pub has_sorted_index: bool,
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Parse an `.olean` file into a `ParsedModule`.
fn parse_olean(path: &Path) -> MathverseResult<ParsedModule> {
    parse_module_file(path).map_err(|e| MathverseError::ImportFailed {
        system: "Lean4".to_string(),
        reason: format!("{}: {e}", path.display()),
    })
}

#[cfg(test)]
mod tests;
