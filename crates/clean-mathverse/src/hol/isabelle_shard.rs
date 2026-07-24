// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Isabelle shard writer: routes translated Isabelle theorems into `.mathverse`
//! shard files via [`ShardWriter`].
//!
//! The existing [`IsabelleImporter`] produces `Vec<IsaImportedConstant>` with
//! kernel `Expr` types (via the translator). This module bridges the gap by
//! lowering those kernel expressions into `FlatExpr` and writing them to shards.

use std::path::Path;

use crate::shard::ShardWriter;
use crate::types::{
    ContentDomain, DeclKind, ImportConfidence, MathverseConstantHeader, SourceSystem, TrustLevel,
    NO_VALUE,
};

use super::opentheory_shard::lower_kernel_expr;
use crate::hol::isabelle::importer::{
    IsaImportedConstant, IsabelleImportConfig, IsabelleImportError, IsabelleImportResult,
    IsabelleImporter,
};
use crate::hol::isabelle::types::ProofStatus;

/// Metadata returned after writing Isabelle declarations to a shard.
#[derive(Clone, Debug, Default)]
pub struct IsaShardMetadata {
    /// Number of declarations written to the shard.
    pub declaration_count: usize,
    /// Names of all written declarations.
    pub names: Vec<String>,
    /// Number of translation errors encountered.
    pub translation_errors: usize,
    /// Number of theories processed.
    pub theories_processed: usize,
}

/// Write Isabelle imported constants to a [`ShardWriter`].
///
/// Takes the constants produced by [`IsabelleImporter::import_theory`] and
/// lowers their kernel `Expr` types to `FlatExpr`, adding them to the shard
/// writer with proper `MathverseConstantHeader` metadata.
pub fn write_isa_constants_to_shard(
    constants: &[IsaImportedConstant],
    writer: &mut ShardWriter,
) -> IsaShardMetadata {
    let mut metadata = IsaShardMetadata::default();

    for constant in constants {
        let name_idx = writer.add_string(&constant.name);

        // Lower the type expression from kernel Expr to FlatExpr.
        let type_idx = lower_kernel_expr(&constant.translated.type_expr, writer);

        // Isabelle theorems are axiomatized — no proof term available.
        let value_idx = NO_VALUE;

        let confidence = trust_level_to_confidence(constant.trust_level);
        let decl_kind = decl_kind_from_proof_status(constant.translated.proof_status);

        let header = MathverseConstantHeader {
            name_idx,
            type_idx,
            value_idx,
            source_system: SourceSystem::Isabelle as u8,
            import_confidence: confidence as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: decl_kind as u8,
            axiom_profile: constant.axiom_profile,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        };

        writer.add_constant(header);
        metadata.names.push(constant.name.clone());
        metadata.declaration_count += 1;
    }

    metadata
}

/// Write an entire [`IsabelleImportResult`] to a shard.
///
/// Convenience wrapper that extracts constants and statistics from the
/// import result.
pub fn write_isa_result_to_shard(
    result: &IsabelleImportResult,
    writer: &mut ShardWriter,
) -> IsaShardMetadata {
    let mut metadata = write_isa_constants_to_shard(&result.constants, writer);
    metadata.translation_errors = result.statistics.translation_errors;
    metadata.theories_processed = result.statistics.theories_processed;
    metadata
}

/// Import Isabelle YXML content and write declarations directly to a shard.
///
/// Combines the import and shard writing into a single step.
pub fn import_and_write_isa_yxml(
    yxml_content: &str,
    writer: &mut ShardWriter,
) -> Result<IsaShardMetadata, IsabelleImportError> {
    let importer = IsabelleImporter::with_defaults();
    let result = importer.import_yxml(yxml_content)?;
    Ok(write_isa_result_to_shard(&result, writer))
}

/// Import from an Isabelle `.yxml` file and write declarations to a shard.
pub fn import_and_write_isa_file(
    path: &Path,
    writer: &mut ShardWriter,
) -> Result<IsaShardMetadata, IsabelleImportError> {
    let importer = IsabelleImporter::with_defaults();
    let result = importer.import_file(path)?;
    Ok(write_isa_result_to_shard(&result, writer))
}

/// Import all `.yxml` files from a directory and write to a shard.
pub fn import_and_write_isa_directory(
    dir: &Path,
    config: IsabelleImportConfig,
    writer: &mut ShardWriter,
) -> Result<IsaShardMetadata, IsabelleImportError> {
    let importer = IsabelleImporter::new(config);
    let result = importer.import_directory(dir)?;
    Ok(write_isa_result_to_shard(&result, writer))
}

/// Map `TrustLevel` to `ImportConfidence` for shard headers.
///
/// Isabelle constants are translated from a foreign type system. A *proved*
/// theorem was checked by Isabelle's own LCF kernel at export time, but the
/// mathverse reconstruction (statement-level term, no proof value, foreign
/// foundation) has NOT been independently re-checked by clean's CIC kernel.
/// That is exactly the semantics of [`ImportConfidence::SourceVerified`]:
/// "source system verified this constant, but the mathverse reconstruction has
/// not been independently kernel-checked" (see `types.rs`). This mirrors the
/// Lean 4 importer's own `confidence_for` convention (value present →
/// `SourceVerified`; axiom/opaque → `Axiomatized`). `KernelVerified` stays
/// reserved for clean-kernel-reconstructed constants only, so no trust is
/// inflated to that tier.
///
/// Proof-erased / axiomatized theorems (Pure axioms, `axiomatization`,
/// definitional axioms) carry no kernel guarantee beyond their statement and
/// map to [`ImportConfidence::Axiomatized`].
fn trust_level_to_confidence(trust: TrustLevel) -> ImportConfidence {
    match trust {
        TrustLevel::KernelVerified
        | TrustLevel::AxiomDependent
        | TrustLevel::CertificateReplayed => ImportConfidence::SourceVerified,
        TrustLevel::PartiallyAxiomatized | TrustLevel::TrustedOracle => {
            ImportConfidence::Axiomatized
        }
    }
}

/// Map Isabelle [`ProofStatus`] to the shard [`DeclKind`] tag.
///
/// - `Proved` — theorem retained a proof in Isabelle's LCF kernel → [`DeclKind::Theorem`]
/// - `Axiomatized` — proof erased during export (LCF opaque proof, not
///   reconstructible) → [`DeclKind::Axiom`]
fn decl_kind_from_proof_status(status: ProofStatus) -> DeclKind {
    match status {
        ProofStatus::Proved => DeclKind::Theorem,
        ProofStatus::Axiomatized => DeclKind::Axiom,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::Expr;

    use crate::hol::isabelle::importer::IsaImportedConstant;
    use crate::hol::isabelle::translate::TranslatedTheorem;
    use crate::hol::isabelle::types::ProofStatus;
    use crate::shard::ShardReader;
    use crate::types::{AxiomProfile, Provenance, SourceSystem};

    /// Build a minimal IsaImportedConstant for testing.
    fn make_test_isa_constant(name: &str, proved: bool) -> IsaImportedConstant {
        let trust = if proved {
            TrustLevel::CertificateReplayed
        } else {
            TrustLevel::PartiallyAxiomatized
        };
        let profile = AxiomProfile(
            AxiomProfile::CLASSICAL.0
                | AxiomProfile::EXTENSIONALITY.0
                | AxiomProfile::ISABELLE_LCF_ERASED.0,
        );

        IsaImportedConstant {
            name: name.to_string(),
            translated: TranslatedTheorem {
                name: name.to_string(),
                type_expr: Expr::prop(),
                proof_status: if proved {
                    ProofStatus::Proved
                } else {
                    ProofStatus::Axiomatized
                },
                axiom_profile: profile,
                trust_level: trust,
                provenance: Provenance {
                    source: SourceSystem::Isabelle,
                    original_name: name.to_string(),
                    source_file: Some("Test.thy".to_string()),
                    axiom_profile: profile,
                },
            },
            provenance: Provenance {
                source: SourceSystem::Isabelle,
                original_name: name.to_string(),
                source_file: Some("Test.thy".to_string()),
                axiom_profile: profile,
            },
            trust_level: trust,
            axiom_profile: profile,
        }
    }

    #[test]
    fn test_write_isa_constants_to_shard_basic() {
        let constants = vec![
            make_test_isa_constant("HOL.conjI", true),
            make_test_isa_constant("HOL.disjE", true),
            make_test_isa_constant("HOL.ext", false),
        ];

        let mut writer = ShardWriter::new();
        let metadata = write_isa_constants_to_shard(&constants, &mut writer);

        assert_eq!(metadata.declaration_count, 3);
        assert_eq!(metadata.names.len(), 3);
        assert_eq!(metadata.names[0], "HOL.conjI");

        // Write and read back to verify.
        let mut buf = Vec::new();
        writer.write(&mut buf).expect("shard write should succeed");
        let reader = ShardReader::from_bytes(&buf).expect("shard read should succeed");

        assert_eq!(reader.header.constant_count, 3);
        assert!(reader.lookup_name("HOL.conjI").is_some());
        assert!(reader.lookup_name("HOL.disjE").is_some());
        assert!(reader.lookup_name("HOL.ext").is_some());
    }

    #[test]
    fn test_write_isa_constants_empty() {
        let mut writer = ShardWriter::new();
        let metadata = write_isa_constants_to_shard(&[], &mut writer);
        assert_eq!(metadata.declaration_count, 0);
        assert!(metadata.names.is_empty());
    }

    #[test]
    fn test_isa_source_system_tag() {
        let constants = vec![make_test_isa_constant("HOL.TrueI", true)];

        let mut writer = ShardWriter::new();
        write_isa_constants_to_shard(&constants, &mut writer);

        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();
        let reader = ShardReader::from_bytes(&buf).unwrap();

        let (_, hdr) = reader.lookup_name("HOL.TrueI").unwrap();
        assert_eq!(hdr.source_system, SourceSystem::Isabelle as u8);
    }

    #[test]
    fn test_isa_trust_level_mapping() {
        let proved = make_test_isa_constant("proved_thm", true);
        let axiom = make_test_isa_constant("axiom_thm", false);

        let mut writer = ShardWriter::new();
        write_isa_constants_to_shard(&[proved, axiom], &mut writer);

        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();
        let reader = ShardReader::from_bytes(&buf).unwrap();

        let (_, hdr) = reader.lookup_name("proved_thm").unwrap();
        assert_eq!(
            hdr.import_confidence,
            ImportConfidence::SourceVerified as u8
        );

        let (_, hdr) = reader.lookup_name("axiom_thm").unwrap();
        assert_eq!(hdr.import_confidence, ImportConfidence::Axiomatized as u8);
    }

    #[test]
    fn test_trust_level_to_confidence_all_variants() {
        // Proved (source-kernel-verified) Isabelle theorems map to
        // SourceVerified — the source kernel checked them but clean's CIC
        // kernel has not re-checked the lossy reconstruction. KernelVerified
        // stays reserved for clean-kernel-reconstructed constants, so trust is
        // not inflated to that tier.
        assert_eq!(
            trust_level_to_confidence(TrustLevel::KernelVerified),
            ImportConfidence::SourceVerified
        );
        assert_eq!(
            trust_level_to_confidence(TrustLevel::AxiomDependent),
            ImportConfidence::SourceVerified
        );
        assert_eq!(
            trust_level_to_confidence(TrustLevel::CertificateReplayed),
            ImportConfidence::SourceVerified
        );
        assert_eq!(
            trust_level_to_confidence(TrustLevel::PartiallyAxiomatized),
            ImportConfidence::Axiomatized
        );
        assert_eq!(
            trust_level_to_confidence(TrustLevel::TrustedOracle),
            ImportConfidence::Axiomatized
        );
    }

    /// Regression test for #3521: proved theorems round-trip as
    /// [`DeclKind::Theorem`] and proof-erased theorems as
    /// [`DeclKind::Axiom`]. Previously every Isabelle constant was tagged
    /// as `DeclKind::Theorem` (discriminant 0).
    #[test]
    fn test_isa_shard_decl_kind_round_trips() {
        use crate::types::DeclKind;

        let proved = make_test_isa_constant("HOL.conjI", true);
        let axiomatized = make_test_isa_constant("HOL.ext", false);

        let mut writer = ShardWriter::new();
        write_isa_constants_to_shard(&[proved, axiomatized], &mut writer);

        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();
        let reader = ShardReader::from_bytes(&buf).unwrap();

        let (_, hdr) = reader.lookup_name("HOL.conjI").unwrap();
        assert_eq!(
            hdr.decl_kind().unwrap(),
            DeclKind::Theorem,
            "ProofStatus::Proved should serialize as DeclKind::Theorem",
        );

        let (_, hdr) = reader.lookup_name("HOL.ext").unwrap();
        assert_eq!(
            hdr.decl_kind().unwrap(),
            DeclKind::Axiom,
            "ProofStatus::Axiomatized should serialize as DeclKind::Axiom",
        );
    }

    #[test]
    fn test_decl_kind_from_proof_status_all_variants() {
        use crate::types::DeclKind;

        assert_eq!(
            decl_kind_from_proof_status(ProofStatus::Proved),
            DeclKind::Theorem,
        );
        assert_eq!(
            decl_kind_from_proof_status(ProofStatus::Axiomatized),
            DeclKind::Axiom,
        );
    }
}
