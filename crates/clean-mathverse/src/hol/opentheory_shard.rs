// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! OpenTheory shard writer: routes Declaration objects from the OpenTheory
//! bridge into `.mathverse` shard files via [`ShardWriter`].
//!
//! The existing [`OtMathverseBridge`] produces `Vec<MathverseImportedConstant>` with
//! kernel `Expr` types. This module bridges the gap by lowering those kernel
//! expressions into `FlatExpr` and writing them to shards with proper metadata.

use std::path::Path;

use clean_kernel::flat::{FlatExpr, FlatLevel};
use clean_kernel::level::Level;
use clean_kernel::{BinderInfo, Expr, ExprKind, Literal};

use crate::shard::ShardWriter;
use crate::types::{
    ContentDomain, DeclKind, ImportConfidence, MathverseConstantHeader, SourceSystem, NO_VALUE,
};

use super::error::HolResult;
use super::opentheory_bridge::{
    ImportStatistics, ImportedConstantKind, MathverseImportedConstant, OtMathverseBridge,
};

/// Metadata returned after writing OpenTheory declarations to a shard.
#[derive(Clone, Debug, Default)]
pub struct OtShardMetadata {
    /// Number of declarations written to the shard.
    pub declaration_count: usize,
    /// Names of all written declarations.
    pub names: Vec<String>,
    /// Import statistics from the bridge.
    pub statistics: ImportStatistics,
}

/// Write OpenTheory declarations to a [`ShardWriter`].
///
/// Takes the constants produced by [`OtMathverseBridge::import_article`] (or
/// similar), lowers their kernel `Expr` types to `FlatExpr`, and adds them
/// to the shard writer with proper `MathverseConstantHeader` metadata.
///
/// Returns metadata about what was written.
pub fn write_ot_constants_to_shard(
    constants: &[MathverseImportedConstant],
    statistics: &ImportStatistics,
    writer: &mut ShardWriter,
) -> OtShardMetadata {
    let mut metadata = OtShardMetadata {
        statistics: statistics.clone(),
        ..Default::default()
    };

    for constant in constants {
        let name_str = constant.name.to_string();
        let name_idx = writer.add_string(&name_str);

        // Lower the type expression from kernel Expr to FlatExpr.
        let type_idx = lower_kernel_expr(&constant.type_expr, writer);

        // OpenTheory constants are axiomatized (no proof term value).
        let value_idx = NO_VALUE;

        let confidence = match constant.kind {
            ImportedConstantKind::Theorem => ImportConfidence::Translated,
            ImportedConstantKind::Assumption | ImportedConstantKind::Support => {
                ImportConfidence::Axiomatized
            }
        };

        let header = MathverseConstantHeader {
            name_idx,
            type_idx,
            value_idx,
            source_system: SourceSystem::HolLight as u8,
            import_confidence: confidence as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: decl_kind_from_ot_kind(constant.kind) as u8,
            axiom_profile: constant.axiom_profile,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        };

        writer.add_constant(header);
        metadata.names.push(name_str);
        metadata.declaration_count += 1;
    }

    metadata
}

/// Import an OpenTheory article file and write its declarations to a shard.
///
/// Combines the bridge import and shard writing into a single step.
pub fn import_and_write_ot_file(
    path: &Path,
    bridge: &OtMathverseBridge,
    writer: &mut ShardWriter,
) -> HolResult<OtShardMetadata> {
    let (constants, statistics) = bridge.import_file(path)?;
    Ok(write_ot_constants_to_shard(&constants, &statistics, writer))
}

/// Import an OpenTheory article from text and write its declarations to a shard.
pub fn import_and_write_ot_text(
    text: &str,
    bridge: &OtMathverseBridge,
    writer: &mut ShardWriter,
) -> HolResult<OtShardMetadata> {
    let (constants, statistics) = bridge.import_article_text(text)?;
    Ok(write_ot_constants_to_shard(&constants, &statistics, writer))
}

// ---------------------------------------------------------------------------
// Kernel Expr -> FlatExpr lowering
// ---------------------------------------------------------------------------

/// Lower a kernel `Expr` to a `FlatExpr` index in the shard writer.
///
/// This is the shared lowering logic used by both OpenTheory and Isabelle
/// shard writers. It handles all kernel expression kinds by recursively
/// lowering sub-expressions and levels.
pub(crate) fn lower_kernel_expr(expr: &Expr, writer: &mut ShardWriter) -> u32 {
    match expr.kind() {
        ExprKind::BVar(n) => {
            let flat = FlatExpr::bvar(*n);
            writer.add_expr(flat)
        }
        ExprKind::FVar(fvar_id) => {
            let flat = FlatExpr::fvar(fvar_id.as_u64());
            writer.add_expr(flat)
        }
        ExprKind::Sort(level) => {
            let level_idx = lower_kernel_level(level, writer);
            let flat = FlatExpr::sort(level_idx);
            writer.add_expr(flat)
        }
        ExprKind::Const(name, levels) => lower_kernel_const(name, levels, writer),
        ExprKind::App(func, arg) => {
            let fn_idx = lower_kernel_expr(func, writer);
            let arg_idx = lower_kernel_expr(arg, writer);
            let flat = FlatExpr::app(fn_idx, arg_idx);
            writer.add_expr(flat)
        }
        ExprKind::Lam(binder_data, ty, body) => {
            lower_kernel_binder(binder_data.info, ty, body, true, writer)
        }
        ExprKind::Pi(binder_data, ty, body) => {
            lower_kernel_binder(binder_data.info, ty, body, false, writer)
        }
        ExprKind::Let(_name, ty, val, body, _nondep) => {
            let ty_idx = lower_kernel_expr(ty, writer);
            let val_idx = lower_kernel_expr(val, writer);
            let body_idx = lower_kernel_expr(body, writer);
            let flat = FlatExpr::let_expr(ty_idx, val_idx, body_idx);
            writer.add_expr(flat)
        }
        ExprKind::Lit(lit) => lower_kernel_lit(lit, writer),
        ExprKind::Proj(struct_name, field_idx, inner) => {
            let name_idx = writer.add_string(&struct_name.to_string());
            let inner_idx = lower_kernel_expr(inner, writer);
            let flat = FlatExpr::proj(name_idx, *field_idx as u16, inner_idx);
            writer.add_expr(flat)
        }
        ExprKind::MData(_metadata, inner) => {
            // MData is transparent — lower the inner expression directly.
            lower_kernel_expr(inner, writer)
        }
        // Extended kernel expression kinds (SProp, Squash, Cubical, etc.)
        // are not produced by HOL/Isabelle translators. Lower as Prop
        // placeholder to keep the shard structurally valid.
        _ => {
            let prop = Expr::prop();
            lower_kernel_expr(&prop, writer)
        }
    }
}

/// Lower a `Const` expression (name + universe levels) to a FlatExpr index.
fn lower_kernel_const(
    name: &clean_kernel::Name,
    levels: &clean_kernel::LevelVec,
    writer: &mut ShardWriter,
) -> u32 {
    let name_idx = writer.add_string(&name.to_string());
    // Lower all universe levels into the pool. Store u32::MAX as
    // levels_list_idx since the shard format lacks a level_lists table.
    for lvl in levels.iter() {
        let _level_idx = lower_kernel_level(lvl, writer);
    }
    let flat = FlatExpr::const_ref(name_idx, u32::MAX);
    writer.add_expr(flat)
}

/// Lower a binder expression (Lam or Pi) to a FlatExpr index.
fn lower_kernel_binder(
    info: BinderInfo,
    ty: &Expr,
    body: &Expr,
    is_lam: bool,
    writer: &mut ShardWriter,
) -> u32 {
    let ty_idx = lower_kernel_expr(ty, writer);
    let body_idx = lower_kernel_expr(body, writer);
    let bi = kernel_binder_info_to_u8(info);
    let flat = if is_lam {
        FlatExpr::lam(bi, ty_idx, body_idx)
    } else {
        FlatExpr::pi(bi, ty_idx, body_idx)
    };
    writer.add_expr(flat)
}

/// Lower a literal expression to a FlatExpr index.
fn lower_kernel_lit(lit: &Literal, writer: &mut ShardWriter) -> u32 {
    match lit {
        Literal::Nat(bignat) => {
            let value = bignat.to_u64().unwrap_or(u64::MAX);
            let flat = FlatExpr::lit_nat(value);
            writer.add_expr(flat)
        }
        Literal::String(s) => {
            let string_idx = writer.add_string(s);
            let flat = FlatExpr::lit_str(string_idx);
            writer.add_expr(flat)
        }
    }
}

/// Lower a kernel `Level` to a `FlatLevel` index in the shard writer.
pub(crate) fn lower_kernel_level(level: &Level, writer: &mut ShardWriter) -> u32 {
    match level {
        Level::Zero => {
            let flat = FlatLevel::zero();
            writer.add_level(flat)
        }
        Level::Succ(inner) => {
            let inner_idx = lower_kernel_level(inner, writer);
            let flat = FlatLevel::succ(inner_idx);
            writer.add_level(flat)
        }
        Level::Max(left, right) => {
            let left_idx = lower_kernel_level(left, writer);
            let right_idx = lower_kernel_level(right, writer);
            let flat = FlatLevel::max(left_idx, right_idx);
            writer.add_level(flat)
        }
        Level::IMax(left, right) => {
            let left_idx = lower_kernel_level(left, writer);
            let right_idx = lower_kernel_level(right, writer);
            let mut flat = FlatLevel::max(left_idx, right_idx);
            flat.tag = FlatLevel::TAG_IMAX;
            writer.add_level(flat)
        }
        Level::Param(name) => {
            let name_idx = writer.add_string(&name.to_string());
            let flat = FlatLevel::param(name_idx);
            writer.add_level(flat)
        }
    }
}

/// Map an OpenTheory [`ImportedConstantKind`] to the shard [`DeclKind`] tag.
///
/// - `Theorem` — a proved theorem (article `thm` entry) → [`DeclKind::Theorem`]
/// - `Assumption` — an axiom without proof within the article → [`DeclKind::Axiom`]
/// - `Support` — an uninterpreted type/constant appearing in theorems, treated
///   as axiomatized because it carries no definitional body → [`DeclKind::Axiom`]
pub(crate) fn decl_kind_from_ot_kind(kind: ImportedConstantKind) -> DeclKind {
    match kind {
        ImportedConstantKind::Theorem => DeclKind::Theorem,
        ImportedConstantKind::Assumption | ImportedConstantKind::Support => DeclKind::Axiom,
    }
}

/// Map kernel `BinderInfo` to the u8 encoding used in `FlatExpr`.
fn kernel_binder_info_to_u8(info: BinderInfo) -> u8 {
    match info {
        BinderInfo::Default => 0,
        BinderInfo::Implicit => 1,
        BinderInfo::StrictImplicit => 2,
        BinderInfo::InstImplicit => 3,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::Name as LeanName;

    use crate::hol::opentheory_bridge::ImportedConstantKind;
    use crate::shard::ShardReader;
    use crate::types::{Provenance, TrustLevel};

    /// Build a minimal MathverseImportedConstant for testing.
    fn make_test_constant(name: &str, kind: ImportedConstantKind) -> MathverseImportedConstant {
        MathverseImportedConstant {
            type_expr: Expr::prop(),
            name: LeanName::from_string(name),
            axiom_profile: super::super::opentheory_bridge::HOL_BASE_PROFILE,
            provenance: Provenance {
                source: SourceSystem::HolLight,
                original_name: name.to_string(),
                source_file: None,
                axiom_profile: super::super::opentheory_bridge::HOL_BASE_PROFILE,
            },
            trust_level: TrustLevel::CertificateReplayed,
            kind,
        }
    }

    #[test]
    fn test_write_ot_constants_to_shard_basic() {
        let constants = vec![
            make_test_constant("OT.thm1", ImportedConstantKind::Theorem),
            make_test_constant("OT.ax1", ImportedConstantKind::Assumption),
            make_test_constant("OT.const1", ImportedConstantKind::Support),
        ];
        let stats = ImportStatistics {
            support_count: 1,
            assumption_count: 1,
            theorem_count: 1,
        };

        let mut writer = ShardWriter::new();
        let metadata = write_ot_constants_to_shard(&constants, &stats, &mut writer);

        assert_eq!(metadata.declaration_count, 3);
        assert_eq!(metadata.names.len(), 3);
        assert_eq!(metadata.statistics.total(), 3);

        // Write and read back to verify the shard is valid.
        let mut buf = Vec::new();
        writer.write(&mut buf).expect("shard write should succeed");
        let reader = ShardReader::from_bytes(&buf).expect("shard read should succeed");

        assert_eq!(reader.header.constant_count, 3);
        assert!(reader.lookup_name("OT.thm1").is_some());
        assert!(reader.lookup_name("OT.ax1").is_some());
        assert!(reader.lookup_name("OT.const1").is_some());
    }

    #[test]
    fn test_write_ot_constants_empty() {
        let mut writer = ShardWriter::new();
        let metadata = write_ot_constants_to_shard(&[], &ImportStatistics::default(), &mut writer);
        assert_eq!(metadata.declaration_count, 0);
        assert!(metadata.names.is_empty());
    }

    #[test]
    fn test_lower_kernel_expr_sort() {
        let mut writer = ShardWriter::new();
        let expr = Expr::sort(Level::Zero);
        let idx = lower_kernel_expr(&expr, &mut writer);
        // Sort(Zero) should produce a valid index.
        assert!(idx < u32::MAX);
    }

    #[test]
    fn test_lower_kernel_expr_const() {
        let mut writer = ShardWriter::new();
        let expr = Expr::const_str("Nat.add");
        let idx = lower_kernel_expr(&expr, &mut writer);
        assert!(idx < u32::MAX);
    }

    #[test]
    fn test_lower_kernel_expr_arrow() {
        let mut writer = ShardWriter::new();
        let prop = Expr::prop();
        let arrow = Expr::arrow(prop.clone(), prop);
        let idx = lower_kernel_expr(&arrow, &mut writer);
        assert!(idx < u32::MAX);
    }

    #[test]
    fn test_lower_kernel_level_succ() {
        let mut writer = ShardWriter::new();
        let level = Level::Succ(std::sync::Arc::new(Level::Zero));
        let idx = lower_kernel_level(&level, &mut writer);
        assert!(idx < u32::MAX);
    }

    #[test]
    fn test_ot_shard_confidence_mapping() {
        let thm = make_test_constant("proved", ImportedConstantKind::Theorem);
        let axiom = make_test_constant("assumed", ImportedConstantKind::Assumption);

        let mut writer = ShardWriter::new();
        let stats = ImportStatistics {
            theorem_count: 1,
            assumption_count: 1,
            support_count: 0,
        };
        write_ot_constants_to_shard(&[thm, axiom], &stats, &mut writer);

        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();
        let reader = ShardReader::from_bytes(&buf).unwrap();

        // Theorem should have Translated confidence.
        let (_, hdr) = reader.lookup_name("proved").unwrap();
        assert_eq!(hdr.import_confidence, ImportConfidence::Translated as u8);

        // Assumption should have Axiomatized confidence.
        let (_, hdr) = reader.lookup_name("assumed").unwrap();
        assert_eq!(hdr.import_confidence, ImportConfidence::Axiomatized as u8);
    }

    /// Regression test for #3521: each OpenTheory `ImportedConstantKind`
    /// round-trips to the correct shard [`DeclKind`]. Previously every
    /// constant was tagged as `DeclKind::Theorem` (discriminant 0).
    #[test]
    fn test_ot_shard_decl_kind_round_trips() {
        use crate::types::DeclKind;

        let thm = make_test_constant("OT.thm", ImportedConstantKind::Theorem);
        let assumption = make_test_constant("OT.ax", ImportedConstantKind::Assumption);
        let support = make_test_constant("OT.support", ImportedConstantKind::Support);

        let mut writer = ShardWriter::new();
        let stats = ImportStatistics {
            theorem_count: 1,
            assumption_count: 1,
            support_count: 1,
        };
        write_ot_constants_to_shard(&[thm, assumption, support], &stats, &mut writer);

        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();
        let reader = ShardReader::from_bytes(&buf).unwrap();

        let (_, hdr) = reader.lookup_name("OT.thm").unwrap();
        assert_eq!(
            hdr.decl_kind().unwrap(),
            DeclKind::Theorem,
            "Theorem kind should serialize as DeclKind::Theorem",
        );

        let (_, hdr) = reader.lookup_name("OT.ax").unwrap();
        assert_eq!(
            hdr.decl_kind().unwrap(),
            DeclKind::Axiom,
            "Assumption kind should serialize as DeclKind::Axiom",
        );

        let (_, hdr) = reader.lookup_name("OT.support").unwrap();
        assert_eq!(
            hdr.decl_kind().unwrap(),
            DeclKind::Axiom,
            "Support (uninterpreted) kind should serialize as DeclKind::Axiom",
        );
    }
}
