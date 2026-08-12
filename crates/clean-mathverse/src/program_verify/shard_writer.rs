// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Program verification VC shard writer for the Mathverse Library.
//!
//! Converts parsed verification conditions into `.mathverse` shard entries in
//! the `software.mathverse` domain. Each proved VC becomes a theorem declaration;
//! each unproved VC becomes a conjecture with appropriate trust level.
//!
//! Follows the same pattern as `decision_certs/shard_writer.rs`: lower types
//! to `FlatExpr`, build `MathverseConstantHeader` entries, and add them to a
//! [`ShardWriter`].

use std::path::Path;

use clean_kernel::flat::FlatExpr;

use crate::error::MathverseResult;
use crate::shard::ShardWriter;
use crate::shard_metadata::{DeclKind, MetadataEntry, ShardMetadata};
use crate::types::{
    ContentDomain, ImportConfidence, MathverseConstantHeader, SourceSystem, NO_VALUE,
};

use super::types::{
    program_vc_axiom_profile, program_vc_trust_level, VcStatus, VerificationCondition,
};

// ---------------------------------------------------------------------------
// Shard write result
// ---------------------------------------------------------------------------

/// Statistics from writing program VCs to a shard.
#[derive(Clone, Debug, Default)]
pub struct ShardStats {
    /// Number of VCs written.
    pub vcs_written: usize,
    /// Number of proved VCs (theorem declarations).
    pub theorems: usize,
    /// Number of unproved VCs (conjecture declarations).
    pub conjectures: usize,
}

// ---------------------------------------------------------------------------
// Shard writer
// ---------------------------------------------------------------------------

/// Write program verification conditions to an `.mathverse` shard via [`ShardWriter`].
///
/// Each VC becomes an Mathverse constant with:
/// - **Name:** `progverif.<source>.<vc_name>` (unique per VC)
/// - **Type:** `FlatExpr::sort(0)` (Prop) — the formula is in the sidecar
/// - **Value:** `NO_VALUE` (axiomatized — the VC proof is external)
/// - **Source system:** Determined by `source` parameter
/// - **Import confidence:** `Translated` for proved, `Axiomatized` for unproved
/// - **Content domain:** `Software`
/// - **Axiom profile:** `SMT_ORACLE`
///
/// Returns statistics about what was written.
pub fn write_program_vcs_to_shard(
    vcs: &[VerificationCondition],
    source: SourceSystem,
    writer: &mut ShardWriter,
) -> ShardStats {
    let mut stats = ShardStats::default();

    for vc in vcs {
        let source_tag = source_system_tag(source);
        let name = format!("progverif.{source_tag}.{}", vc.name);
        let name_idx = writer.add_string(&name);

        // Type: Prop placeholder (Sort(0) = Prop).
        let type_idx = writer.add_expr(FlatExpr::sort(0));

        // Value: axiomatized (proof is external to the shard).
        let value_idx = NO_VALUE;

        // All VCs use Sort(0) placeholder types — the real verification condition
        // is external. Unverified is the honest label (consistent with DTT fix #3360).
        let confidence = match vc.status {
            VcStatus::Proved => {
                stats.theorems += 1;
                ImportConfidence::Unverified
            }
            VcStatus::Unknown | VcStatus::Failed => {
                stats.conjectures += 1;
                ImportConfidence::Axiomatized
            }
        };

        let kind = match vc.status {
            VcStatus::Proved => DeclKind::Theorem,
            VcStatus::Unknown | VcStatus::Failed => DeclKind::Axiom,
        };

        let header = MathverseConstantHeader {
            name_idx,
            type_idx,
            value_idx,
            source_system: source as u8,
            import_confidence: confidence as u8,
            content_domain: ContentDomain::Software as u8,
            decl_kind: kind.to_shard_kind() as u8,
            axiom_profile: program_vc_axiom_profile(),
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        };

        writer.add_constant(header);
        stats.vcs_written += 1;
    }

    stats
}

/// Write program verification conditions to an `.mathverse` shard file on disk.
///
/// Creates the shard file and an accompanying `.mathverse.json` metadata sidecar.
///
/// # Errors
///
/// Returns an error if the shard file or metadata sidecar cannot be written.
pub fn write_program_vcs_to_file(
    vcs: &[VerificationCondition],
    source: SourceSystem,
    path: &Path,
) -> MathverseResult<ShardStats> {
    let mut writer = ShardWriter::new();
    let stats = write_program_vcs_to_shard(vcs, source, &mut writer);

    // Write the shard binary.
    let mut file = std::fs::File::create(path)?;
    writer.write(&mut file)?;

    // Write metadata sidecar.
    let source_tag = source_system_tag(source);
    let system_name = format!("ProgramVerify-{source_tag}");
    let mut metadata = ShardMetadata::new(&system_name);

    for vc in vcs {
        let kind = match vc.status {
            VcStatus::Proved => DeclKind::Theorem,
            VcStatus::Unknown | VcStatus::Failed => DeclKind::Axiom,
        };
        let trust = program_vc_trust_level(vc.status);
        metadata.push(MetadataEntry {
            name: format!("progverif.{source_tag}.{}", vc.name),
            kind: Some(kind),
            type_signature: Some(format!("VC({name}) [{trust:?}]", name = vc.name,)),
            source_file: vc.source_file.clone(),
            line_number: vc.source_line,
        });
    }

    crate::shard_metadata::write_metadata(path, &metadata)?;

    Ok(stats)
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Map a `SourceSystem` to a short tag for naming.
fn source_system_tag(source: SourceSystem) -> &'static str {
    match source {
        SourceSystem::Dafny => "dafny",
        SourceSystem::Boogie => "boogie",
        SourceSystem::Why3 => "why3",
        SourceSystem::FStar => "fstar",
        SourceSystem::Key => "key",
        SourceSystem::FramaC => "framac",
        SourceSystem::Spark => "spark",
        SourceSystem::Verus => "verus",
        SourceSystem::Creusot => "creusot",
        SourceSystem::Prusti => "prusti",
        SourceSystem::Viper => "viper",
        _ => "generic",
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::program_verify::types::VcFormula;
    use crate::shard::ShardReader;

    fn make_proved_vc(name: &str) -> VerificationCondition {
        VerificationCondition {
            name: name.to_string(),
            source_file: Some("test.dfy".to_string()),
            source_line: Some(10),
            formula: VcFormula::bool_lit(true),
            status: VcStatus::Proved,
        }
    }

    fn make_failed_vc(name: &str) -> VerificationCondition {
        VerificationCondition {
            name: name.to_string(),
            source_file: None,
            source_line: None,
            formula: VcFormula::bool_lit(false),
            status: VcStatus::Failed,
        }
    }

    fn make_unknown_vc(name: &str) -> VerificationCondition {
        VerificationCondition {
            name: name.to_string(),
            source_file: None,
            source_line: None,
            formula: VcFormula::var("x"),
            status: VcStatus::Unknown,
        }
    }

    #[test]
    fn test_write_program_vcs_to_shard_empty() {
        let mut writer = ShardWriter::new();
        let stats = write_program_vcs_to_shard(&[], SourceSystem::Dafny, &mut writer);
        assert_eq!(stats.vcs_written, 0);
        assert_eq!(stats.theorems, 0);
        assert_eq!(stats.conjectures, 0);
    }

    #[test]
    fn test_write_program_vcs_to_shard_proved() {
        let vcs = vec![make_proved_vc("vc1")];
        let mut writer = ShardWriter::new();
        let stats = write_program_vcs_to_shard(&vcs, SourceSystem::Dafny, &mut writer);

        assert_eq!(stats.vcs_written, 1);
        assert_eq!(stats.theorems, 1);
        assert_eq!(stats.conjectures, 0);

        // Verify the shard is readable.
        let mut buf = Vec::new();
        writer.write(&mut buf).expect("shard write should succeed");
        let reader = ShardReader::from_bytes(&buf).expect("shard read should succeed");
        assert_eq!(reader.header.constant_count, 1);
    }

    #[test]
    fn test_write_program_vcs_to_shard_mixed() {
        let vcs = vec![
            make_proved_vc("proved_vc"),
            make_failed_vc("failed_vc"),
            make_unknown_vc("unknown_vc"),
        ];
        let mut writer = ShardWriter::new();
        let stats = write_program_vcs_to_shard(&vcs, SourceSystem::Why3, &mut writer);

        assert_eq!(stats.vcs_written, 3);
        assert_eq!(stats.theorems, 1);
        assert_eq!(stats.conjectures, 2);

        let mut buf = Vec::new();
        writer.write(&mut buf).expect("shard write should succeed");
        let reader = ShardReader::from_bytes(&buf).expect("shard read should succeed");
        assert_eq!(reader.header.constant_count, 3);
    }

    #[test]
    fn test_write_program_vcs_to_shard_confidence_levels() {
        let vcs = vec![make_proved_vc("proved"), make_failed_vc("failed")];
        let mut writer = ShardWriter::new();
        write_program_vcs_to_shard(&vcs, SourceSystem::Dafny, &mut writer);

        let mut buf = Vec::new();
        writer.write(&mut buf).expect("shard write should succeed");
        let reader = ShardReader::from_bytes(&buf).expect("shard read should succeed");

        // Proved VC — Sort(0) placeholder type, honest label is Unverified.
        let (_, hdr0) = reader
            .lookup_name("progverif.dafny.proved")
            .expect("should find proved VC");
        assert_eq!(hdr0.import_confidence, ImportConfidence::Unverified as u8);

        // Failed VC should be Axiomatized confidence.
        let (_, hdr1) = reader
            .lookup_name("progverif.dafny.failed")
            .expect("should find failed VC");
        assert_eq!(hdr1.import_confidence, ImportConfidence::Axiomatized as u8);
    }

    #[test]
    fn test_write_program_vcs_to_shard_content_domain() {
        let vcs = vec![make_proved_vc("vc")];
        let mut writer = ShardWriter::new();
        write_program_vcs_to_shard(&vcs, SourceSystem::Dafny, &mut writer);

        let mut buf = Vec::new();
        writer.write(&mut buf).expect("shard write should succeed");
        let reader = ShardReader::from_bytes(&buf).expect("shard read should succeed");

        let (_, hdr) = reader
            .lookup_name("progverif.dafny.vc")
            .expect("should find VC");
        assert_eq!(hdr.content_domain, ContentDomain::Software as u8);
    }

    #[test]
    fn test_write_program_vcs_to_file() {
        let dir = tempfile::tempdir().expect("create temp dir");
        let shard_path = dir.path().join("program_vcs.mathverse");

        let vcs = vec![make_proved_vc("vc1"), make_unknown_vc("vc2")];
        let stats = write_program_vcs_to_file(&vcs, SourceSystem::Dafny, &shard_path)
            .expect("should write shard");

        assert_eq!(stats.vcs_written, 2);
        assert_eq!(stats.theorems, 1);
        assert_eq!(stats.conjectures, 1);
        assert!(shard_path.exists());

        // Check the metadata sidecar was written.
        let sidecar_path = crate::shard_metadata::sidecar_path_for(&shard_path);
        assert!(sidecar_path.exists());

        let metadata =
            crate::shard_metadata::load_metadata(&shard_path).expect("should load metadata");
        assert_eq!(metadata.system_name, "ProgramVerify-dafny");
        assert_eq!(metadata.declaration_count, 2);
    }

    #[test]
    fn test_source_system_tag() {
        assert_eq!(source_system_tag(SourceSystem::Dafny), "dafny");
        assert_eq!(source_system_tag(SourceSystem::Boogie), "boogie");
        assert_eq!(source_system_tag(SourceSystem::Why3), "why3");
        assert_eq!(source_system_tag(SourceSystem::Verus), "verus");
        assert_eq!(source_system_tag(SourceSystem::Lean4), "generic");
    }
}
