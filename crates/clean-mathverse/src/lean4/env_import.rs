// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Environment-based Lean 4 `.olean` to `.mathverse` importer.
//!
//! Converts a loaded kernel `Environment` (with `ConstantInfo` containing
//! kernel `Expr`/`Level` types) into `.mathverse` shard format via `ShardWriter`.
//!
//! This complements `lean4_alpha.rs` which operates on `ParsedModule` /
//! `ParsedExpr` (the pre-type-checked representation). This module works on
//! the post-type-checked `Environment`, giving access to fully elaborated
//! types and values.
//!
//! Pipeline: `.olean` -> `clean-olean` parse -> `Environment` (register)
//!   -> **this module** -> `.mathverse` shard

use std::collections::HashMap;
use std::path::Path;

use clean_kernel::env::Environment;
use clean_kernel::expr::{BinderInfo, ExprKind, Literal};
use clean_kernel::flat::{FlatExpr, FlatLevel};
use clean_kernel::{ConstantInfo, ConstantKind};

use crate::error::{MathverseError, MathverseResult};
use crate::provenance::{add_provenance, ProvenanceBuilder, ProvenanceRecord, ProvenanceSidecar};
use crate::shard::ShardWriter;
use crate::types::{
    AxiomProfile, ContentDomain, DeclKind, ImportConfidence, MathverseConstantHeader, SourceSystem,
    NO_VALUE,
};

// ---------------------------------------------------------------------------
// ImportStats
// ---------------------------------------------------------------------------

/// Statistics from an Environment import.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct EnvImportStats {
    /// Total number of constants processed.
    pub total: u32,
    /// Constants with proof terms (kernel-verified confidence).
    pub kernel_verified: u32,
    /// Constants without proof terms (axiomatized confidence).
    pub axiomatized: u32,
    /// Constants that were skipped (unsupported or filtered).
    pub skipped: u32,
    /// Constants with axiom dependencies (CHOICE, PROP_EXT, QUOT, etc.).
    pub axiom_dependent: u32,
    /// Constants that are trust-gated (axiomatized + trust-sensitive bits).
    pub trust_gated: u32,
}

impl EnvImportStats {
    /// Total non-skipped constants.
    pub fn imported(&self) -> u32 {
        self.kernel_verified + self.axiomatized
    }
}

// ---------------------------------------------------------------------------
// EnvImportConfig
// ---------------------------------------------------------------------------

/// Configuration for Environment-based import.
#[derive(Clone, Debug)]
pub struct EnvImportConfig {
    /// Include private constants (those with `._private` in the name).
    pub include_private: bool,
    /// Source file path to record in provenance (e.g., the `.olean` path).
    pub source_file: Option<String>,
    /// Source system version string (e.g., "Lean 4.3.0").
    pub source_version: Option<String>,
    /// Content domain classification for all constants in this import.
    pub content_domain: ContentDomain,
}

impl Default for EnvImportConfig {
    fn default() -> Self {
        Self {
            include_private: false,
            source_file: None,
            source_version: None,
            content_domain: ContentDomain::PureMath,
        }
    }
}

// ---------------------------------------------------------------------------
// Axiom profile computation
// ---------------------------------------------------------------------------

/// Compute the axiom profile for a kernel constant.
///
/// Recognizes well-known Lean 4 axioms by name:
/// - `Classical.choice` -> CHOICE | CLASSICAL
/// - `propext` -> PROP_EXT
/// - `Quot` / `Quot.mk` / `Quot.ind` / `Quot.lift` -> QUOT
///
/// Axioms (no value) also get the AXIOMATIZED bit.
pub(crate) fn compute_env_axiom_profile(ci: &ConstantInfo) -> AxiomProfile {
    let mut profile = AxiomProfile::NONE;
    let name_str = ci.name.to_string();

    match name_str.as_str() {
        "Classical.choice" => {
            profile |= AxiomProfile::CHOICE;
            profile |= AxiomProfile::CLASSICAL;
        }
        "propext" => {
            profile |= AxiomProfile::PROP_EXT;
        }
        "Quot" | "Quot.mk" | "Quot.ind" | "Quot.lift" => {
            profile |= AxiomProfile::QUOT;
        }
        _ => {}
    }

    // Axioms get the AXIOMATIZED bit.
    if ci.kind == ConstantKind::Axiom {
        profile |= AxiomProfile::AXIOMATIZED;
    }
    // Opaque constants are also axiomatized from a trust perspective.
    if ci.kind == ConstantKind::Opaque {
        profile |= AxiomProfile::AXIOMATIZED;
    }

    profile
}

/// Determine import confidence for a kernel constant.
fn confidence_for(ci: &ConstantInfo) -> ImportConfidence {
    match ci.kind {
        ConstantKind::Axiom | ConstantKind::Opaque => ImportConfidence::Axiomatized,
        ConstantKind::Theorem | ConstantKind::Definition => {
            if ci.value.is_some() {
                ImportConfidence::KernelVerified
            } else {
                ImportConfidence::Axiomatized
            }
        }
    }
}

// ---------------------------------------------------------------------------
// KernelLoweringCtx — converts kernel Expr/Level directly to ShardWriter
// ---------------------------------------------------------------------------

/// Lowering context that converts kernel `Expr`/`Level` trees directly into
/// `FlatExpr`/`FlatLevel` entries in a `ShardWriter`.
///
/// This mirrors `LoweringCtx` in `lean4_alpha.rs` but operates on kernel
/// types (post-type-check) instead of `ParsedExpr`/`ParsedLevel`.
///
/// All indices returned by lowering methods are valid within the
/// `ShardWriter`'s pools, so they can be stored directly in
/// `MathverseConstantHeader.type_idx` / `value_idx`.
struct KernelLoweringCtx<'a> {
    writer: &'a mut ShardWriter,
    /// Cache: string value -> string table index (dedup).
    string_cache: HashMap<String, u32>,
}

impl<'a> KernelLoweringCtx<'a> {
    fn new(writer: &'a mut ShardWriter) -> Self {
        Self {
            writer,
            string_cache: HashMap::new(),
        }
    }

    /// Add a string to the shard writer's string table, deduplicating.
    fn intern_string(&mut self, s: &str) -> u32 {
        if let Some(&idx) = self.string_cache.get(s) {
            return idx;
        }
        let idx = self.writer.add_string(s);
        self.string_cache.insert(s.to_string(), idx);
        idx
    }

    /// Append a constant's universe-parameter names as a CONTIGUOUS string-table
    /// block, returning `(start, count)`. The shard format reads level params as
    /// the half-open window `[start..start+count)`, so they must occupy
    /// consecutive slots; interning them one-by-one dedups names already present
    /// (e.g. a `u_1` seen earlier in the decl's type), scattering the rest and
    /// making the window read unrelated strings as universe parameters — a
    /// spurious `UndefinedLevelParam` rejection. `add_string_block` guarantees
    /// contiguity.
    fn add_level_param_block(&mut self, params: &[clean_kernel::name::Name]) -> (u32, u16) {
        if params.is_empty() {
            return (0, 0);
        }
        let names: Vec<String> = params.iter().map(ToString::to_string).collect();
        let refs: Vec<&str> = names.iter().map(String::as_str).collect();
        let start = self.writer.add_string_block(&refs);
        (start, refs.len() as u16)
    }

    /// Lower a kernel `Level` into the shard writer's level pool.
    fn lower_level(&mut self, level: &clean_kernel::level::Level) -> u32 {
        use clean_kernel::level::Level;
        match level {
            Level::Zero => self.writer.add_level(FlatLevel::zero()),
            Level::Succ(inner) => {
                let inner_idx = self.lower_level(inner);
                self.writer.add_level(FlatLevel::succ(inner_idx))
            }
            Level::Max(l, r) => {
                let left_idx = self.lower_level(l);
                let right_idx = self.lower_level(r);
                self.writer.add_level(FlatLevel::max(left_idx, right_idx))
            }
            Level::IMax(l, r) => {
                let left_idx = self.lower_level(l);
                let right_idx = self.lower_level(r);
                let mut flat = FlatLevel::max(left_idx, right_idx);
                flat.tag = FlatLevel::TAG_IMAX;
                self.writer.add_level(flat)
            }
            Level::Param(name) => {
                let name_idx = self.intern_string(&name.to_string());
                self.writer.add_level(FlatLevel::param(name_idx))
            }
        }
    }

    /// Lower a kernel `Expr` into the shard writer's expression arena.
    ///
    /// Returns `Ok(expr_idx)` on success, or `Err` if a BigNat literal
    /// exceeds u64::MAX.
    fn lower_expr(&mut self, expr: &clean_kernel::expr::Expr) -> Result<u32, MathverseError> {
        match expr.kind() {
            ExprKind::BVar(n) => {
                let flat = FlatExpr::bvar(*n);
                Ok(self.writer.add_expr(flat))
            }
            ExprKind::FVar(fvar_id) => {
                let flat = FlatExpr::fvar(fvar_id.as_u64());
                Ok(self.writer.add_expr(flat))
            }
            ExprKind::Sort(level) => {
                let level_idx = self.lower_level(level);
                let flat = FlatExpr::sort(level_idx);
                Ok(self.writer.add_expr(flat))
            }
            ExprKind::Const(name, levels) => {
                let name_idx = self.intern_string(&name.to_string());
                // Lower the universe levels into the pool and LINK them through
                // the shard's `level_lists` table so universe-polymorphic
                // references round-trip as `Const(name, [u, v, ...])`.
                //
                // A stale earlier version discarded the lowered levels and wrote
                // `u32::MAX` (no levels) here, on the since-outdated premise that
                // "the mathverse shard format does not yet have a level_lists
                // table". It does (`ShardWriter::add_level_list`, and the reader
                // resolves it in `shard_verify::reconstruct_single_expr`), so
                // dropping the list collapsed every `Const(T, [u])` to
                // `Const(T, [])` — reconstructing `T` with zero level args and
                // failing every reference to a universe-polymorphic constant with
                // "Level count mismatch for T: declared N level params, got 0".
                let levels_list_idx = if levels.is_empty() {
                    u32::MAX
                } else {
                    let level_idxs: Vec<u32> =
                        levels.iter().map(|lvl| self.lower_level(lvl)).collect();
                    self.writer.add_level_list(&level_idxs)
                };
                let flat = FlatExpr::const_ref(name_idx, levels_list_idx);
                Ok(self.writer.add_expr(flat))
            }
            ExprKind::App(f, a) => {
                let fn_idx = self.lower_expr(f)?;
                let arg_idx = self.lower_expr(a)?;
                let flat = FlatExpr::app(fn_idx, arg_idx);
                Ok(self.writer.add_expr(flat))
            }
            ExprKind::Lam(bi, ty, body) => {
                let ty_idx = self.lower_expr(ty)?;
                let body_idx = self.lower_expr(body)?;
                let flat = FlatExpr::lam(binder_info_to_u8(bi.info), ty_idx, body_idx);
                Ok(self.writer.add_expr(flat))
            }
            ExprKind::Pi(bi, ty, body) => {
                let ty_idx = self.lower_expr(ty)?;
                let body_idx = self.lower_expr(body)?;
                let flat = FlatExpr::pi(binder_info_to_u8(bi.info), ty_idx, body_idx);
                Ok(self.writer.add_expr(flat))
            }
            ExprKind::Let(_, ty, val, body, _) => {
                let ty_idx = self.lower_expr(ty)?;
                let val_idx = self.lower_expr(val)?;
                let body_idx = self.lower_expr(body)?;
                let flat = FlatExpr::let_expr(ty_idx, val_idx, body_idx);
                Ok(self.writer.add_expr(flat))
            }
            ExprKind::Lit(lit) => match lit {
                Literal::Nat(n) => {
                    // A Nat literal exceeding u64::MAX (e.g. `UInt64.size = 2^64`)
                    // does not fit FlatExpr's inline u64. Erroring here dropped
                    // the whole constant and cascaded "Unknown constant" to every
                    // dependent (all of UInt64/USize arithmetic). Match the
                    // canonical encoder (`clean_kernel::flat::convert`, and the
                    // production `alpha.rs` path) EXACTLY: store the little-endian
                    // u64 limbs as a comma-separated decimal string and flag
                    // NAT_BIG, so the BigNat round-trips losslessly
                    // (`BigNat::from_limbs` / `parse_bignat_limbs` on read).
                    let flat = match n.to_u64() {
                        Some(val) => FlatExpr::lit_nat(val),
                        None => {
                            let limbs = n
                                .limbs()
                                .iter()
                                .map(|l| l.to_string())
                                .collect::<Vec<_>>()
                                .join(",");
                            let str_idx = self.intern_string(&limbs);
                            let mut flat = FlatExpr::lit_nat(0);
                            flat.data[0..4].copy_from_slice(&str_idx.to_le_bytes());
                            flat.flags |= clean_kernel::flat::FlatFlags::NAT_BIG.bits();
                            flat
                        }
                    };
                    Ok(self.writer.add_expr(flat))
                }
                Literal::String(s) => {
                    let str_idx = self.intern_string(s);
                    let flat = FlatExpr::lit_str(str_idx);
                    Ok(self.writer.add_expr(flat))
                }
            },
            ExprKind::Proj(name, field, e) => {
                let name_idx = self.intern_string(&name.to_string());
                let expr_idx = self.lower_expr(e)?;
                let flat = FlatExpr::proj(name_idx, *field as u16, expr_idx);
                Ok(self.writer.add_expr(flat))
            }
            // MData is transparent -- lower the inner expression directly.
            ExprKind::MData(_, inner) => self.lower_expr(inner),
            // Mode extensions are not supported in mathverse shard format.
            // Encode as Sort(0) with UNSUPPORTED flag (0x10).
            ExprKind::SProp
            | ExprKind::Squash(_)
            | ExprKind::CubicalInterval
            | ExprKind::CubicalI0
            | ExprKind::CubicalI1
            | ExprKind::CubicalPath { .. }
            | ExprKind::CubicalPathLam { .. }
            | ExprKind::CubicalPathApp { .. }
            | ExprKind::CubicalHComp { .. }
            | ExprKind::CubicalTransp { .. }
            | ExprKind::CubicalCoe { .. }
            | ExprKind::ZFCSet(_)
            | ExprKind::ZFCMem { .. }
            | ExprKind::ZFCComprehension { .. } => {
                let level_idx = self.writer.add_level(FlatLevel::zero());
                let mut flat = FlatExpr::sort(level_idx);
                // 0x10 = FlatFlags::UNSUPPORTED (pub(crate), accessed by raw value)
                flat.flags |= 0x10;
                Ok(self.writer.add_expr(flat))
            }
        }
    }
}

/// Convert BinderInfo to u8 for flat format.
fn binder_info_to_u8(bi: BinderInfo) -> u8 {
    match bi {
        BinderInfo::Default => 0,
        BinderInfo::Implicit => 1,
        BinderInfo::StrictImplicit => 2,
        BinderInfo::InstImplicit => 3,
    }
}

// ---------------------------------------------------------------------------
// Core import function
// ---------------------------------------------------------------------------

/// Import all constants from a kernel `Environment` into an `.mathverse` shard.
///
/// Each constant is converted to an `MathverseConstantHeader` with:
/// - Lowered type and value expressions via `KernelLoweringCtx`
/// - Axiom profile computed from the constant's name and kind
/// - Provenance record with source metadata
///
/// Returns import statistics and the list of provenance records.
pub fn import_environment(
    env: &Environment,
    writer: &mut ShardWriter,
    config: &EnvImportConfig,
) -> MathverseResult<(EnvImportStats, Vec<ProvenanceRecord>)> {
    let mut stats = EnvImportStats::default();
    let mut records = Vec::new();
    let mut sidecar = ProvenanceSidecar::new();

    // Collect and sort constants by name for deterministic output.
    let mut constants: Vec<&ConstantInfo> = env.constants().collect();
    constants.sort_by_key(|a| a.name.to_string());

    // KernelLoweringCtx writes directly to the ShardWriter, so all
    // FlatExpr/FlatLevel indices are valid within the writer's pools.
    let mut ctx = KernelLoweringCtx::new(writer);

    for ci in &constants {
        let name_str = ci.name.to_string();

        // Filter private constants.
        if !config.include_private && name_str.contains("._private") {
            stats.total += 1;
            stats.skipped += 1;
            records.push(
                ProvenanceBuilder::new(&name_str)
                    .note("skipped: private constant")
                    .build(),
            );
            continue;
        }

        let confidence = confidence_for(ci);
        let profile = compute_env_axiom_profile(ci);

        // Lower type expression directly into ShardWriter.
        let type_idx = match ctx.lower_expr(&ci.type_) {
            Ok(idx) => idx,
            Err(e) => {
                stats.total += 1;
                stats.skipped += 1;
                records.push(
                    ProvenanceBuilder::new(&name_str)
                        .note(&format!("skipped: type lowering failed: {e}"))
                        .build(),
                );
                continue;
            }
        };

        // Lower value expression (if present).
        let value_idx = match &ci.value {
            Some(val) => match ctx.lower_expr(val) {
                Ok(idx) => idx,
                Err(e) => {
                    stats.total += 1;
                    stats.skipped += 1;
                    records.push(
                        ProvenanceBuilder::new(&name_str)
                            .note(&format!("skipped: value lowering failed: {e}"))
                            .build(),
                    );
                    continue;
                }
            },
            None => NO_VALUE,
        };

        // Add the name to the shard writer's string table.
        let name_idx = ctx.intern_string(&name_str);

        // Store level parameter names as a CONTIGUOUS string-table block (a
        // plain intern loop dedups and scatters them, corrupting the
        // `[start..start+count)` window). See `add_level_param_block`.
        let (lp_start, lp_count) = ctx.add_level_param_block(&ci.level_params);

        // Build provenance record.
        let mut prov_builder = ProvenanceBuilder::new(&name_str)
            .note(&format!("kind: {:?}", ci.kind))
            .pipeline_version(1);
        if let Some(ref src) = config.source_file {
            prov_builder = prov_builder.source_file(src);
        }
        if let Some(ref ver) = config.source_version {
            prov_builder = prov_builder.source_version(ver);
        }
        let prov_record = prov_builder.build();
        let (prov_idx, sidecar_digest) = add_provenance(&mut sidecar, prov_record.clone());

        // Inductive-family membership is tracked by the kernel's dedicated
        // registries (`get_inductive`/`get_constructor`/`get_recursor`), NOT by
        // `ConstantKind` — which only distinguishes Definition/Theorem/Opaque/
        // Axiom. A value-less inductive type / constructor / recursor would
        // otherwise be lowered as `decl_kind_from_kernel(ci.kind)` = Axiom, and
        // the incremental verifier (`verify_shard_incremental`) would never
        // group or checked-replay the family: it would drop EVERY family to an
        // axiom fallback and then withhold trust from every dependent proof.
        //
        // Consult the registries so the family carries `DeclKind::Inductive/
        // Constructor/Recursor` and the inductive ROOT carries the typed
        // `num_params` (+ mutual-block `all_names`) stamp the checked
        // `add_inductive` replay needs to fix its param/index boundary. Extract
        // the owned metadata up front so the `&env` borrow is released before
        // `ctx.writer` is mutated below.
        let (decl_kind, inductive_meta): (DeclKind, Option<(u32, Vec<String>)>) =
            if let Some(iv) = env.get_inductive(&ci.name) {
                let num_params = iv.num_params;
                let all_names = iv.all_names.iter().map(|n| n.to_string()).collect();
                (DeclKind::Inductive, Some((num_params, all_names)))
            } else if env.get_constructor(&ci.name).is_some() {
                (DeclKind::Constructor, None)
            } else if env.get_recursor(&ci.name).is_some() {
                (DeclKind::Recursor, None)
            } else {
                (
                    crate::lean4::olean::decl_kind::decl_kind_from_kernel(ci.kind),
                    None,
                )
            };

        let mut header = MathverseConstantHeader {
            name_idx,
            type_idx,
            value_idx,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: confidence as u8,
            content_domain: config.content_domain as u8,
            decl_kind: decl_kind as u8,
            axiom_profile: profile,
            sidecar_digest,
            provenance_idx: prov_idx,
            level_params_start: lp_start,
            level_params_count: lp_count,
            _pad2: [0u8; 26],
        };

        if let Some((num_params, all_names)) = inductive_meta {
            header.set_inductive_decl_num_params(num_params);
            if !all_names.is_empty() && all_names.len() <= u16::MAX as usize {
                let refs: Vec<&str> = all_names.iter().map(String::as_str).collect();
                let start = ctx.writer.add_string_block(&refs);
                header.set_inductive_decl_all_names(start, refs.len() as u16);
            }
        }

        ctx.writer.add_constant(header);
        records.push(prov_record);

        stats.total += 1;
        match confidence {
            ImportConfidence::KernelVerified => stats.kernel_verified += 1,
            ImportConfidence::Axiomatized => stats.axiomatized += 1,
            _ => stats.skipped += 1,
        }
        if !profile.is_pure() {
            stats.axiom_dependent += 1;
        }
        if profile.is_trust_gated() {
            stats.trust_gated += 1;
        }
    }

    // Set provenance sidecar on the writer.
    if !sidecar.is_empty() {
        let prov_bytes = sidecar.to_bytes()?;
        ctx.writer.set_provenance(prov_bytes);
    }

    Ok((stats, records))
}

/// Convenience function: import an Environment and write directly to a `.mathverse` file.
pub fn export_environment_to_file(
    env: &Environment,
    output_path: impl AsRef<Path>,
    config: &EnvImportConfig,
) -> MathverseResult<EnvImportStats> {
    let mut writer = ShardWriter::new();
    let (stats, _records) = import_environment(env, &mut writer, config)?;
    writer.write_to_file(output_path)?;
    Ok(stats)
}

#[cfg(test)]
#[path = "env_import_tests.rs"]
mod tests;
