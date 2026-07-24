// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Mizar shard writer: routes [`MizImportedConstant`] objects from the Mizar
//! importer into `.mathverse` shard files via [`ShardWriter`].
//!
//! Follows the same pattern as [`opentheory_shard`] and [`coq_shard`]:
//! lowers kernel `Expr` types into `FlatExpr` and writes them to shards
//! with proper `MathverseConstantHeader` metadata.
//!
//! [`opentheory_shard`]: crate::hol::opentheory_shard
//! [`coq_shard`]: crate::coq::shard

use super::importer::{MizConstantKind, MizImportedConstant, MizarImportResult, MizarImporter};
use crate::hol::opentheory_shard::lower_kernel_expr;
use crate::shard::ShardWriter;
use crate::types::{
    ContentDomain, DeclKind, ImportConfidence, MathverseConstantHeader, SourceSystem, NO_VALUE,
};

// ════════════════════════════════════════════════════════════════════════════
// Shard metadata
// ════════════════════════════════════════════════════════════════════════════

/// Metadata returned after writing Mizar declarations to a shard.
#[derive(Clone, Debug, Default)]
pub struct MizarShardMetadata {
    /// Number of declarations written to the shard.
    pub declaration_count: usize,
    /// Names of all written declarations.
    pub names: Vec<String>,
    /// Number of theorems written.
    pub theorems: usize,
    /// Number of definitions written.
    pub definitions: usize,
    /// Number of schemes written.
    pub schemes: usize,
    /// Number of registrations written.
    pub registrations: usize,
    /// Number of constants that were axiomatized (no kernel type expr).
    pub axiomatized: usize,
}

impl MizarShardMetadata {
    /// Total declarations written.
    #[must_use]
    pub fn total(&self) -> usize {
        self.declaration_count
    }

    /// Whether any declarations were written.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.declaration_count == 0
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Shard writing
// ════════════════════════════════════════════════════════════════════════════

/// Write Mizar imported constants to a [`ShardWriter`].
///
/// Takes the constants produced by [`MizarImporter::import_article_xml`],
/// lowers their kernel `Expr` types to `FlatExpr`, and adds them to the
/// shard writer with proper `MathverseConstantHeader` metadata.
///
/// Constants without a `kernel_type_expr` are written with a Prop placeholder
/// type and marked as axiomatized.
pub fn write_mizar_constants_to_shard(
    constants: &[MizImportedConstant],
    writer: &mut ShardWriter,
) -> MizarShardMetadata {
    let mut metadata = MizarShardMetadata::default();

    for constant in constants {
        let name_idx = writer.add_string(&constant.name);

        // Lower the type expression from kernel Expr to FlatExpr.
        let type_idx = if let Some(ref expr) = constant.kernel_type_expr {
            lower_kernel_expr(expr, writer)
        } else {
            // No kernel type: write Prop as placeholder.
            let prop = clean_kernel::Expr::prop();
            metadata.axiomatized += 1;
            lower_kernel_expr(&prop, writer)
        };

        // Mizar constants are axiomatized (no proof term value).
        let value_idx = NO_VALUE;

        // Classify Mizar constants into header DeclKind alongside import
        // confidence. Schemes are second-order axiom schemas (Axiom);
        // registrations assert cluster adherences (Axiom); notations (which
        // should not reach here) are synonyms (Definition-like).
        let (confidence, decl_kind) = match constant.kind {
            MizConstantKind::Theorem => {
                metadata.theorems += 1;
                (
                    mizar_import_confidence(&constant.trust_level),
                    DeclKind::Theorem,
                )
            }
            MizConstantKind::Definition => {
                metadata.definitions += 1;
                (ImportConfidence::Translated, DeclKind::Definition)
            }
            MizConstantKind::Scheme => {
                metadata.schemes += 1;
                (ImportConfidence::Translated, DeclKind::Axiom)
            }
            MizConstantKind::Registration => {
                metadata.registrations += 1;
                (ImportConfidence::Translated, DeclKind::Axiom)
            }
            MizConstantKind::Notation => {
                // Notations should not reach here (filtered by importer),
                // but handle gracefully.
                (ImportConfidence::Axiomatized, DeclKind::Definition)
            }
        };

        let header = MathverseConstantHeader {
            name_idx,
            type_idx,
            value_idx,
            source_system: SourceSystem::Mizar as u8,
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

/// Write an entire Mizar import result to a shard.
///
/// Convenience wrapper around [`write_mizar_constants_to_shard`] that takes
/// a [`MizarImportResult`] directly.
pub fn write_mizar_import_to_shard(
    result: &MizarImportResult,
    writer: &mut ShardWriter,
) -> MizarShardMetadata {
    write_mizar_constants_to_shard(&result.constants, writer)
}

/// Import a Mizar article from XML and write directly to a shard.
///
/// Combines parsing, translation, and shard writing into a single step.
///
/// # Errors
///
/// Returns an error if XML parsing or translation fails.
pub fn import_and_write_mizar_article(
    article_name: &str,
    xml: &str,
    writer: &mut ShardWriter,
) -> Result<MizarShardMetadata, super::translate::MizTranslateError> {
    let importer = MizarImporter::with_defaults(article_name);
    let result = importer.import_article_xml(xml)?;
    Ok(write_mizar_import_to_shard(&result, writer))
}

// ════════════════════════════════════════════════════════════════════════════
// Helpers
// ════════════════════════════════════════════════════════════════════════════

/// Map Mizar trust level to import confidence for shard headers.
fn mizar_import_confidence(trust_level: &crate::types::TrustLevel) -> ImportConfidence {
    match trust_level {
        crate::types::TrustLevel::KernelVerified => ImportConfidence::KernelVerified,
        crate::types::TrustLevel::CertificateReplayed => ImportConfidence::Translated,
        crate::types::TrustLevel::AxiomDependent => ImportConfidence::Translated,
        crate::types::TrustLevel::PartiallyAxiomatized => ImportConfidence::Axiomatized,
        crate::types::TrustLevel::TrustedOracle => ImportConfidence::Axiomatized,
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Tests
// ════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use crate::shard::ShardReader;
    use crate::types::{AxiomProfile, Provenance, TrustLevel};

    /// Build a minimal MizImportedConstant for testing.
    fn make_test_constant(name: &str, kind: MizConstantKind) -> MizImportedConstant {
        MizImportedConstant {
            name: name.to_owned(),
            type_expr: "Prop".to_owned(),
            kernel_type_expr: Some(clean_kernel::Expr::prop()),
            kind,
            axiom_profile: AxiomProfile::MIZAR_SOFT_TYPE,
            trust_level: TrustLevel::AxiomDependent,
            provenance: Provenance {
                source: SourceSystem::Mizar,
                original_name: name.to_owned(),
                source_file: Some("TEST.miz".to_owned()),
                axiom_profile: AxiomProfile::MIZAR_SOFT_TYPE,
            },
        }
    }

    #[test]
    fn test_write_mizar_constants_to_shard_basic() {
        let constants = vec![
            make_test_constant("Mizar.TEST.T1", MizConstantKind::Theorem),
            make_test_constant("Mizar.TEST.Mode.Nat", MizConstantKind::Definition),
            make_test_constant("Mizar.TEST.Sch.Ind", MizConstantKind::Scheme),
            make_test_constant("Mizar.TEST.Reg.exist", MizConstantKind::Registration),
        ];

        let mut writer = ShardWriter::new();
        let metadata = write_mizar_constants_to_shard(&constants, &mut writer);

        assert_eq!(metadata.declaration_count, 4);
        assert_eq!(metadata.theorems, 1);
        assert_eq!(metadata.definitions, 1);
        assert_eq!(metadata.schemes, 1);
        assert_eq!(metadata.registrations, 1);
        assert_eq!(metadata.names.len(), 4);
        assert!(!metadata.is_empty());

        // Write and read back to verify the shard is valid.
        let mut buf = Vec::new();
        writer.write(&mut buf).expect("shard write should succeed");
        let reader = ShardReader::from_bytes(&buf).expect("shard read should succeed");

        assert_eq!(reader.header.constant_count, 4);
        assert!(reader.lookup_name("Mizar.TEST.T1").is_some());
        assert!(reader.lookup_name("Mizar.TEST.Mode.Nat").is_some());
    }

    #[test]
    fn test_write_mizar_constants_empty() {
        let mut writer = ShardWriter::new();
        let metadata = write_mizar_constants_to_shard(&[], &mut writer);
        assert_eq!(metadata.declaration_count, 0);
        assert!(metadata.is_empty());
        assert!(metadata.names.is_empty());
    }

    #[test]
    fn test_write_mizar_constant_without_kernel_expr() {
        let mut constant = make_test_constant("Mizar.TEST.T1", MizConstantKind::Theorem);
        constant.kernel_type_expr = None;

        let mut writer = ShardWriter::new();
        let metadata = write_mizar_constants_to_shard(&[constant], &mut writer);

        assert_eq!(metadata.declaration_count, 1);
        assert_eq!(metadata.axiomatized, 1);
    }

    #[test]
    fn test_import_and_write_mizar_article() {
        let xml = r#"<Article aid="TEST">
  <Theorem nr="1">
    <Pred kind="R" nr="1"/>
  </Theorem>
</Article>"#;

        let mut writer = ShardWriter::new();
        let metadata = import_and_write_mizar_article("TEST", xml, &mut writer)
            .expect("should import and write");

        assert_eq!(metadata.declaration_count, 1);
        assert_eq!(metadata.theorems, 1);

        let mut buf = Vec::new();
        writer.write(&mut buf).expect("shard write should succeed");
        let reader = ShardReader::from_bytes(&buf).expect("shard read should succeed");
        assert_eq!(reader.header.constant_count, 1);
    }

    #[test]
    fn test_mizar_shard_source_system() {
        let constants = vec![make_test_constant("Mizar.T1", MizConstantKind::Theorem)];

        let mut writer = ShardWriter::new();
        write_mizar_constants_to_shard(&constants, &mut writer);

        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();
        let reader = ShardReader::from_bytes(&buf).unwrap();

        let (_, hdr) = reader.lookup_name("Mizar.T1").unwrap();
        assert_eq!(hdr.source_system, SourceSystem::Mizar as u8);
        assert_eq!(hdr.content_domain, ContentDomain::PureMath as u8);
    }

    #[test]
    fn test_mizar_shard_confidence_mapping() {
        let axiomatized = MizImportedConstant {
            trust_level: TrustLevel::PartiallyAxiomatized,
            ..make_test_constant("Mizar.Ax", MizConstantKind::Theorem)
        };
        let translated = MizImportedConstant {
            trust_level: TrustLevel::CertificateReplayed,
            ..make_test_constant("Mizar.Tr", MizConstantKind::Theorem)
        };

        let mut writer = ShardWriter::new();
        write_mizar_constants_to_shard(&[axiomatized, translated], &mut writer);

        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();
        let reader = ShardReader::from_bytes(&buf).unwrap();

        let (_, hdr) = reader.lookup_name("Mizar.Ax").unwrap();
        assert_eq!(hdr.import_confidence, ImportConfidence::Axiomatized as u8);

        let (_, hdr) = reader.lookup_name("Mizar.Tr").unwrap();
        assert_eq!(hdr.import_confidence, ImportConfidence::Translated as u8);
    }

    /// Regression for #3522: every Mizar shard header must carry a
    /// `decl_kind` derived from `MizConstantKind`, not the hardcoded 0.
    #[test]
    fn test_mizar_shard_decl_kind_round_trip() {
        let constants = vec![
            make_test_constant("Mizar.Decl.Thm", MizConstantKind::Theorem),
            make_test_constant("Mizar.Decl.Def", MizConstantKind::Definition),
            make_test_constant("Mizar.Decl.Sch", MizConstantKind::Scheme),
            make_test_constant("Mizar.Decl.Reg", MizConstantKind::Registration),
            make_test_constant("Mizar.Decl.Not", MizConstantKind::Notation),
        ];

        let mut writer = ShardWriter::new();
        write_mizar_constants_to_shard(&constants, &mut writer);

        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();
        let reader = ShardReader::from_bytes(&buf).unwrap();

        let (_, hdr) = reader.lookup_name("Mizar.Decl.Thm").unwrap();
        assert_eq!(hdr.decl_kind, DeclKind::Theorem as u8);
        assert_eq!(hdr.decl_kind().unwrap(), DeclKind::Theorem);

        let (_, hdr) = reader.lookup_name("Mizar.Decl.Def").unwrap();
        assert_eq!(hdr.decl_kind, DeclKind::Definition as u8);

        // Schemes and registrations are axiom-like (not theorems).
        let (_, hdr) = reader.lookup_name("Mizar.Decl.Sch").unwrap();
        assert_eq!(hdr.decl_kind, DeclKind::Axiom as u8);

        let (_, hdr) = reader.lookup_name("Mizar.Decl.Reg").unwrap();
        assert_eq!(hdr.decl_kind, DeclKind::Axiom as u8);

        // Notations are definition-like (synonyms).
        let (_, hdr) = reader.lookup_name("Mizar.Decl.Not").unwrap();
        assert_eq!(hdr.decl_kind, DeclKind::Definition as u8);

        // None of the entries should retain the legacy 0 (Theorem) default
        // on non-theorem constants.
        let (_, def_hdr) = reader.lookup_name("Mizar.Decl.Def").unwrap();
        assert_ne!(def_hdr.decl_kind, DeclKind::Theorem as u8);
    }
}
