// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean 4 shard builder: accumulates constants from parsed `.olean` modules
//! and produces `.mathverse` shard bytes with full provenance.
//!
//! Higher-level than the raw [`crate::lean4::olean::olean_bridge`] functions. The
//! [`Lean4ShardBuilder`] provides a stateful, incremental API:
//!
//! ```text
//! let mut builder = Lean4ShardBuilder::new();
//! builder.add_module(&module1, "Init.Core")?;
//! builder.add_module(&module2, "Init.Data.Nat")?;
//! let (shard_bytes, stats) = builder.build_shard()?;
//! ```

use std::time::SystemTime;

use clean_kernel::flat::{FlatExpr, FlatLevel};
use clean_olean::module::{ConstantKind, ParsedConstant, ParsedModule};

use crate::error::MathverseResult;
use crate::lean4::olean::alpha::LoweringCtx;
use crate::lean4::olean::axiom_profile::compute_lean4_axiom_profile;
use crate::provenance::{add_provenance, ProvenanceBuilder, ProvenanceSidecar};
use crate::shard::ShardWriter;
use crate::types::{
    ContentDomain, DeclKind, ImportConfidence, MathverseConstantHeader, SourceSystem, NO_VALUE,
};

// ---------------------------------------------------------------------------
// ModuleStats
// ---------------------------------------------------------------------------

/// Statistics from adding a single module to the shard builder.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ModuleStats {
    /// Module name (dot-separated path).
    pub module_name: String,
    /// Total constants in this module.
    pub total: u32,
    /// Constants with kernel-verified confidence.
    pub kernel_verified: u32,
    /// Constants with axiomatized confidence.
    pub axiomatized: u32,
    /// Constants that were skipped.
    pub skipped: u32,
    /// Number of theorems (ConstantKind::Theorem).
    pub theorems: u32,
    /// Number of definitions (ConstantKind::Definition).
    pub definitions: u32,
    /// Number of inductives.
    pub inductives: u32,
    /// Number of axioms.
    pub axioms: u32,
}

// ---------------------------------------------------------------------------
// ShardBuildStats
// ---------------------------------------------------------------------------

/// Aggregate statistics from building a complete shard.
#[derive(Clone, Debug, Default)]
pub struct ShardBuildStats {
    /// Per-module statistics.
    pub modules: Vec<ModuleStats>,
    /// Total constants across all modules.
    pub total_constants: u32,
    /// Total kernel-verified constants.
    pub total_kernel_verified: u32,
    /// Total axiomatized constants.
    pub total_axiomatized: u32,
    /// Total skipped constants.
    pub total_skipped: u32,
    /// Total provenance records.
    pub total_provenance_records: u32,
    /// Size of the output shard in bytes.
    pub shard_size_bytes: usize,
}

// ---------------------------------------------------------------------------
// Lean4ShardBuilder
// ---------------------------------------------------------------------------

/// Accumulates constants from parsed `.olean` modules and produces `.mathverse` shards.
///
/// Usage:
/// 1. Create with [`Lean4ShardBuilder::new`].
/// 2. Add modules with [`add_module`].
/// 3. Call [`build_shard`] to produce shard bytes and statistics.
pub struct Lean4ShardBuilder {
    writer: ShardWriter,
    sidecar: ProvenanceSidecar,
    module_stats: Vec<ModuleStats>,
    total_constants: u32,
    total_kernel_verified: u32,
    total_axiomatized: u32,
    total_skipped: u32,
}

impl Lean4ShardBuilder {
    /// Create a new empty shard builder.
    #[must_use]
    pub fn new() -> Self {
        Self {
            writer: ShardWriter::new(),
            sidecar: ProvenanceSidecar::new(),
            module_stats: Vec::new(),
            total_constants: 0,
            total_kernel_verified: 0,
            total_axiomatized: 0,
            total_skipped: 0,
        }
    }

    /// Add all constants from a parsed module to the shard.
    ///
    /// Each constant gets:
    /// - A lowered type and value expression in the flat arena
    /// - An axiom profile computed from its name and kind
    /// - A provenance record with module path and import timestamp
    /// - Proper confidence classification (KernelVerified / Axiomatized)
    ///
    /// Returns statistics for the module.
    pub fn add_module(
        &mut self,
        module: &ParsedModule,
        module_name: &str,
    ) -> MathverseResult<ModuleStats> {
        // Use the free function that takes writer and sidecar as separate args
        // to avoid borrow-checker issues (LoweringCtx borrows writer, but we
        // also need sidecar access in the same loop).
        let stats =
            import_module_to_shard(module, module_name, &mut self.writer, &mut self.sidecar)?;

        // Update aggregates.
        self.total_constants += stats.total;
        self.total_kernel_verified += stats.kernel_verified;
        self.total_axiomatized += stats.axiomatized;
        self.total_skipped += stats.skipped;
        self.module_stats.push(stats.clone());

        Ok(stats)
    }

    /// Number of modules added so far.
    #[must_use]
    pub fn module_count(&self) -> usize {
        self.module_stats.len()
    }

    /// Total constants accumulated so far.
    #[must_use]
    pub fn constant_count(&self) -> u32 {
        self.total_constants
    }

    /// Consume the builder and produce the `.mathverse` shard as bytes.
    ///
    /// Attaches the provenance sidecar to the shard and serializes
    /// everything into a complete `.mathverse` file.
    pub fn build_shard(mut self) -> MathverseResult<(Vec<u8>, ShardBuildStats)> {
        // Close axiom profiles over the in-shard dependency graph so transitive
        // axiom usage is captured in each constant's header before writing.
        self.writer.finalize_axiom_profiles();

        // Attach provenance sidecar.
        let prov_bytes = self.sidecar.to_bytes()?;
        self.writer.set_provenance(prov_bytes);

        // Serialize shard.
        let mut buf = Vec::new();
        self.writer.write(&mut buf)?;

        let stats = ShardBuildStats {
            modules: self.module_stats,
            total_constants: self.total_constants,
            total_kernel_verified: self.total_kernel_verified,
            total_axiomatized: self.total_axiomatized,
            total_skipped: self.total_skipped,
            total_provenance_records: self.sidecar.len() as u32,
            shard_size_bytes: buf.len(),
        };

        Ok((buf, stats))
    }
}

impl Default for Lean4ShardBuilder {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Free function: import module into writer + sidecar
// ---------------------------------------------------------------------------

/// Import a parsed module into a `ShardWriter` and `ProvenanceSidecar`.
///
/// Takes writer and sidecar as separate parameters to satisfy the borrow
/// checker (LoweringCtx borrows writer, provenance operations borrow sidecar).
fn import_module_to_shard(
    module: &ParsedModule,
    module_name: &str,
    writer: &mut ShardWriter,
    sidecar: &mut ProvenanceSidecar,
) -> MathverseResult<ModuleStats> {
    let mut stats = ModuleStats {
        module_name: module_name.to_string(),
        ..Default::default()
    };

    let now_ts = SystemTime::now()
        .duration_since(SystemTime::UNIX_EPOCH)
        .unwrap_or_default()
        .as_secs();

    let mut ctx = LoweringCtx::new(writer);

    for constant in &module.constants {
        // SOUNDNESS: skip Lean compiler-IR stage decls (`._cstage1`/`._cstage2`)
        // — non-kernel-checkable code-generator artifacts; see
        // `clean_olean::import::is_compiler_ir_name`.
        if clean_olean::import::is_compiler_ir_name(&constant.name) {
            continue;
        }
        let name_idx = ctx.intern_string(&constant.name);
        let confidence = confidence_for_constant(constant);
        let profile = compute_lean4_axiom_profile(constant);

        // Lower the type expression.
        let type_idx: u32 = match &constant.type_ {
            Some(type_expr) => ctx.lower_expr(type_expr),
            None => {
                let l0 = ctx.writer.add_level(FlatLevel::zero());
                ctx.writer.add_expr(FlatExpr::sort(l0))
            }
        };

        // Lower the value expression if present.
        let value_idx: u32 = if has_value_for(constant) {
            match &constant.value {
                Some(val_expr) => ctx.lower_expr(val_expr),
                None => {
                    let l0 = ctx.writer.add_level(FlatLevel::zero());
                    ctx.writer.add_expr(FlatExpr::sort(l0))
                }
            }
        } else {
            NO_VALUE
        };

        // Store level parameter names as a CONTIGUOUS string-table block (a
        // plain intern loop dedups and scatters them, corrupting the
        // `[start..start+count)` window). See `add_level_param_block`.
        let (lp_start, lp_count) = ctx.add_level_param_block(&constant.level_params);

        // Build provenance record.
        let record = ProvenanceBuilder::new(&constant.name)
            .module_path(module_name)
            .import_timestamp(now_ts)
            .pipeline_version(1)
            .note(&format!("kind: {:?}", constant.kind))
            .build();
        let (prov_idx, digest) = add_provenance(sidecar, record);

        let header = MathverseConstantHeader {
            name_idx,
            type_idx,
            value_idx,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: confidence as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: decl_kind_from_constant_kind(&constant.kind) as u8,
            axiom_profile: profile,
            sidecar_digest: digest,
            provenance_idx: prov_idx,
            level_params_start: lp_start,
            level_params_count: lp_count,
            _pad2: [0u8; 26],
        };

        ctx.writer.add_constant(header);

        stats.total += 1;
        match confidence {
            ImportConfidence::KernelVerified | ImportConfidence::SourceVerified => {
                stats.kernel_verified += 1;
            }
            ImportConfidence::Axiomatized => stats.axiomatized += 1,
            _ => stats.skipped += 1,
        }
        match constant.kind {
            ConstantKind::Theorem => stats.theorems += 1,
            ConstantKind::Definition => stats.definitions += 1,
            ConstantKind::Inductive => stats.inductives += 1,
            ConstantKind::Axiom => stats.axioms += 1,
            _ => {}
        }
    }

    Ok(stats)
}

// ---------------------------------------------------------------------------
// Internal helpers (mirrors lean4_olean_bridge.rs logic)
// ---------------------------------------------------------------------------

/// Determine confidence for a parsed constant.
///
/// This is the *un-typechecked* heuristic path (no OUR-kernel check runs
/// here), so it must NOT emit `KernelVerified`. It returns `SourceVerified`
/// at most — Lean 4's own type checker accepted the source, but the
/// reconstructed mathverse representation has not been independently
/// kernel-checked. Mirrors the honest
/// [`crate::lean4::olean::alpha::confidence_for`].
fn confidence_for_constant(constant: &ParsedConstant) -> ImportConfidence {
    match constant.kind {
        ConstantKind::Axiom | ConstantKind::Opaque => ImportConfidence::Axiomatized,
        ConstantKind::Theorem | ConstantKind::Definition => {
            if constant.value.is_some() {
                ImportConfidence::SourceVerified
            } else {
                ImportConfidence::Axiomatized
            }
        }
        ConstantKind::Inductive | ConstantKind::Constructor | ConstantKind::Recursor => {
            ImportConfidence::SourceVerified
        }
        ConstantKind::Quot => ImportConfidence::SourceVerified,
        _ => ImportConfidence::Unverified,
    }
}

/// Map a parsed-olean `ConstantKind` to the shard-level `DeclKind`.
///
/// Delegates to the shared [`crate::lean4::olean::decl_kind::decl_kind_from_olean`] —
/// single source of truth across all Lean 4 shard emitters.
fn decl_kind_from_constant_kind(kind: &ConstantKind) -> DeclKind {
    crate::lean4::olean::decl_kind::decl_kind_from_olean(kind)
}

/// Determine whether a constant has a meaningful value.
fn has_value_for(constant: &ParsedConstant) -> bool {
    match constant.kind {
        ConstantKind::Theorem | ConstantKind::Definition => constant.value.is_some(),
        ConstantKind::Inductive | ConstantKind::Constructor | ConstantKind::Recursor => true,
        ConstantKind::Quot => true,
        ConstantKind::Axiom | ConstantKind::Opaque => false,
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    include!("shard_tests.rs");
}
