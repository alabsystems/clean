// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shard writer for DTT imports: writes Agda, Idris 2, and F* declarations
//! to a shared `dtt.mathverse` shard file.
//!
//! This module bridges [`DttDeclaration`] values (from the system-specific
//! parsers) to the [`ShardWriter`] format. Each declaration is lowered to:
//! - A string table entry for the name
//! - A `FlatExpr` placeholder for the type (opaque, since DTT types are not
//!   yet fully lowered to clean kernel expressions)
//! - An optional `FlatExpr` placeholder for the value
//! - An `MathverseConstantHeader` with proper source system, axiom profile, etc.

use clean_kernel::flat::FlatExpr;

use crate::shard::ShardWriter;
use crate::types::{
    ContentDomain, ImportConfidence, MathverseConstantHeader, SourceSystem, NO_VALUE,
};

use super::types::{DttDeclaration, DttImportStats, DttSystem};

/// Metadata returned after writing DTT declarations to a shard.
#[derive(Clone, Debug, Default)]
pub struct DttShardMetadata {
    /// Number of Agda declarations written.
    pub agda_written: usize,
    /// Number of Idris 2 declarations written.
    pub idris2_written: usize,
    /// Number of F* declarations written.
    pub fstar_written: usize,
    /// Names of all written declarations.
    pub names: Vec<String>,
    /// Import statistics.
    pub stats: DttImportStats,
}

impl DttShardMetadata {
    /// Total declarations written across all systems.
    #[must_use]
    pub fn total(&self) -> usize {
        self.agda_written + self.idris2_written + self.fstar_written
    }
}

/// Write a batch of [`DttDeclaration`] values to a [`ShardWriter`].
///
/// Each declaration is lowered to a constant header with:
/// - Name from the declaration
/// - Type as an opaque `FlatExpr::Sort` placeholder (universe 0)
/// - Value as opaque placeholder if present, `NO_VALUE` if axiom
/// - Source system from the DTT system
/// - Axiom profile propagated from the declaration
pub fn write_dtt_decls_to_shard(
    decls: &[DttDeclaration],
    writer: &mut ShardWriter,
) -> DttShardMetadata {
    let mut metadata = DttShardMetadata::default();

    for decl in decls {
        write_single_decl(decl, writer, &mut metadata);
    }

    metadata
}

/// Write DTT declarations grouped by system, returning combined metadata.
pub fn write_dtt_decls_by_system(
    agda_decls: &[DttDeclaration],
    idris2_decls: &[DttDeclaration],
    fstar_decls: &[DttDeclaration],
    writer: &mut ShardWriter,
) -> DttShardMetadata {
    let mut metadata = DttShardMetadata::default();

    for decl in agda_decls {
        write_single_decl(decl, writer, &mut metadata);
    }
    for decl in idris2_decls {
        write_single_decl(decl, writer, &mut metadata);
    }
    for decl in fstar_decls {
        write_single_decl(decl, writer, &mut metadata);
    }

    metadata.stats.agda_count = metadata.agda_written;
    metadata.stats.idris2_count = metadata.idris2_written;
    metadata.stats.fstar_count = metadata.fstar_written;

    metadata
}

/// Write a single DTT declaration to the shard.
fn write_single_decl(
    decl: &DttDeclaration,
    writer: &mut ShardWriter,
    metadata: &mut DttShardMetadata,
) {
    let name_idx = writer.add_string(&decl.name);

    // Type: use a Sort(0) placeholder since DTT types are not yet
    // fully lowered to kernel FlatExpr. Because these are opaque
    // placeholders (not real type expressions), all DTT imports are
    // labeled `Unverified` — there is no type preservation proof and
    // the kernel cannot check these expressions. See #3360.
    let type_flat = FlatExpr::sort(0);
    let type_idx = writer.add_expr(type_flat);

    // Value: placeholder if present, NO_VALUE for axioms.
    let value_idx = if decl.has_value() {
        let val_flat = FlatExpr::sort(0); // placeholder
        writer.add_expr(val_flat)
    } else {
        NO_VALUE
    };

    let source_system = match decl.system {
        DttSystem::Agda => SourceSystem::Agda,
        DttSystem::Idris2 => SourceSystem::Idris2,
        DttSystem::Fstar => SourceSystem::FStar,
    };

    // All DTT imports use Sort(0) placeholder types and values, so
    // neither axioms nor definitions have real kernel-checkable content.
    // `Unverified` is the honest label — `Translated` would falsely
    // claim a type-preservation proof exists. See #3360.
    let import_confidence = ImportConfidence::Unverified;

    let header = MathverseConstantHeader {
        name_idx,
        type_idx,
        value_idx,
        source_system: source_system as u8,
        import_confidence: import_confidence as u8,
        content_domain: ContentDomain::PureMath as u8,
        // DTT surface records only is_axiom (no inductive/constructor tags);
        // axioms map to Axiom, everything with a body maps to Definition.
        decl_kind: if decl.is_axiom {
            crate::types::DeclKind::Axiom as u8
        } else {
            crate::types::DeclKind::Definition as u8
        },
        axiom_profile: decl.axiom_profile,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    };

    writer.add_constant(header);

    // Update metadata counters.
    metadata.names.push(decl.name.clone());
    match decl.system {
        DttSystem::Agda => metadata.agda_written += 1,
        DttSystem::Idris2 => metadata.idris2_written += 1,
        DttSystem::Fstar => metadata.fstar_written += 1,
    }

    // Track axiomatization reasons in stats.
    if decl.is_cubical() {
        metadata.stats.cubical_axiomatized += 1;
    }
    if decl.is_qtt() {
        metadata.stats.qtt_axiomatized += 1;
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::AxiomProfile;

    fn make_test_decl(
        name: &str,
        system: DttSystem,
        is_axiom: bool,
        profile: AxiomProfile,
    ) -> DttDeclaration {
        use super::super::types::DttExpr;
        DttDeclaration {
            name: name.to_owned(),
            type_expr: DttExpr::Sort(0),
            value_expr: if is_axiom {
                None
            } else {
                Some(DttExpr::var("placeholder"))
            },
            system,
            axiom_profile: profile,
            is_axiom,
            source_file: None,
            module_name: None,
        }
    }

    #[test]
    fn test_write_dtt_decls_basic() {
        let decls = vec![
            make_test_decl("Agda.Nat", DttSystem::Agda, false, AxiomProfile::NONE),
            make_test_decl("Idris.Nat", DttSystem::Idris2, false, AxiomProfile::NONE),
            make_test_decl("FStar.nat", DttSystem::Fstar, false, AxiomProfile::NONE),
        ];

        let mut writer = ShardWriter::new();
        let meta = write_dtt_decls_to_shard(&decls, &mut writer);

        assert_eq!(meta.total(), 3);
        assert_eq!(meta.agda_written, 1);
        assert_eq!(meta.idris2_written, 1);
        assert_eq!(meta.fstar_written, 1);
        assert_eq!(meta.names.len(), 3);
    }

    #[test]
    fn test_write_dtt_decls_axiomatized() {
        let decls = vec![make_test_decl(
            "postulate",
            DttSystem::Agda,
            true,
            AxiomProfile::AXIOMATIZED,
        )];

        let mut writer = ShardWriter::new();
        let meta = write_dtt_decls_to_shard(&decls, &mut writer);

        assert_eq!(meta.total(), 1);
        assert_eq!(meta.agda_written, 1);
    }

    #[test]
    fn test_write_dtt_decls_cubical_tracking() {
        let decls = vec![make_test_decl(
            "transport",
            DttSystem::Agda,
            true,
            AxiomProfile::AGDA_CUBICAL,
        )];

        let mut writer = ShardWriter::new();
        let meta = write_dtt_decls_to_shard(&decls, &mut writer);

        assert_eq!(meta.stats.cubical_axiomatized, 1);
    }

    #[test]
    fn test_write_dtt_decls_qtt_tracking() {
        let decls = vec![make_test_decl(
            "linFn",
            DttSystem::Idris2,
            true,
            AxiomProfile::IDRIS_QTT,
        )];

        let mut writer = ShardWriter::new();
        let meta = write_dtt_decls_to_shard(&decls, &mut writer);

        assert_eq!(meta.stats.qtt_axiomatized, 1);
    }

    #[test]
    fn test_write_dtt_decls_by_system() {
        let agda = vec![make_test_decl(
            "A",
            DttSystem::Agda,
            false,
            AxiomProfile::NONE,
        )];
        let idris = vec![make_test_decl(
            "B",
            DttSystem::Idris2,
            false,
            AxiomProfile::NONE,
        )];
        let fstar = vec![
            make_test_decl("C", DttSystem::Fstar, false, AxiomProfile::NONE),
            make_test_decl("D", DttSystem::Fstar, true, AxiomProfile::AXIOMATIZED),
        ];

        let mut writer = ShardWriter::new();
        let meta = write_dtt_decls_by_system(&agda, &idris, &fstar, &mut writer);

        assert_eq!(meta.total(), 4);
        assert_eq!(meta.agda_written, 1);
        assert_eq!(meta.idris2_written, 1);
        assert_eq!(meta.fstar_written, 2);
        assert_eq!(meta.stats.agda_count, 1);
        assert_eq!(meta.stats.idris2_count, 1);
        assert_eq!(meta.stats.fstar_count, 2);
    }

    #[test]
    fn test_write_dtt_decls_empty() {
        let mut writer = ShardWriter::new();
        let meta = write_dtt_decls_to_shard(&[], &mut writer);
        assert_eq!(meta.total(), 0);
        assert!(meta.names.is_empty());
    }

    #[test]
    fn test_metadata_total() {
        let meta = DttShardMetadata {
            agda_written: 10,
            idris2_written: 5,
            fstar_written: 8,
            ..Default::default()
        };
        assert_eq!(meta.total(), 23);
    }

    /// All DTT imports must be labeled `Unverified` because they use
    /// Sort(0) placeholders instead of real type expressions. See #3360.
    #[test]
    fn test_dtt_imports_get_unverified_confidence() {
        use crate::shard::ShardReader;

        let decls = vec![
            // Non-axiom definitions from each system
            make_test_decl("Agda.Nat", DttSystem::Agda, false, AxiomProfile::NONE),
            make_test_decl("Idris.Nat", DttSystem::Idris2, false, AxiomProfile::NONE),
            make_test_decl("FStar.nat", DttSystem::Fstar, false, AxiomProfile::NONE),
            // Axioms from each system
            make_test_decl(
                "Agda.postulate",
                DttSystem::Agda,
                true,
                AxiomProfile::AXIOMATIZED,
            ),
            make_test_decl(
                "Idris.believe_me",
                DttSystem::Idris2,
                true,
                AxiomProfile::AXIOMATIZED,
            ),
            make_test_decl(
                "FStar.assume",
                DttSystem::Fstar,
                true,
                AxiomProfile::AXIOMATIZED,
            ),
        ];

        let mut writer = ShardWriter::new();
        write_dtt_decls_to_shard(&decls, &mut writer);

        // Write shard to temp file, read back, and verify all headers.
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("dtt_trust.mathverse");
        writer.write_to_file(&path).expect("write shard");

        let reader = ShardReader::from_file(&path).expect("open shard");
        assert_eq!(reader.constants.len(), 6);

        // Every DTT constant must be Unverified, never Translated or KernelVerified.
        for (i, header) in reader.constants.iter().enumerate() {
            let confidence = ImportConfidence::try_from(header.import_confidence)
                .unwrap_or_else(|v| panic!("invalid confidence {v} at index {i}"));
            assert_eq!(
                confidence,
                ImportConfidence::Unverified,
                "DTT import at index {i} has confidence {confidence:?}, expected Unverified (Sort(0) placeholder types cannot be Translated)"
            );
        }
    }
}
