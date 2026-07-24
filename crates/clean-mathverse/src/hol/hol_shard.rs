// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unified HOL family shard aggregator: routes HOL Light, HOL4, and Isabelle
//! constants into a single `.mathverse` shard file via [`ShardWriter`].
//!
//! This module aggregates constants from all three HOL family importers into
//! one shard, tagging each with its [`SourceSystem`] so downstream consumers
//! can distinguish provenance while operating on a unified constant pool.

use super::opentheory_bridge::{ImportStatistics, MathverseImportedConstant};
use super::opentheory_shard::{decl_kind_from_ot_kind, lower_kernel_expr};
use crate::hol::isabelle::types::ProofStatus;
use crate::shard::ShardWriter;
use crate::types::{
    ContentDomain, DeclKind, ImportConfidence, MathverseConstantHeader, SourceSystem, TrustLevel,
    NO_VALUE,
};

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct HolFamilyShardStats {
    pub(crate) hol_light_count: usize,
    pub(crate) hol4_count: usize,
    pub(crate) isabelle_count: usize,
    pub(crate) total_count: usize,
    pub(crate) names: Vec<String>,
}

#[must_use]
pub(crate) fn trust_to_confidence(trust: TrustLevel) -> ImportConfidence {
    // HOL constants are translated from a foreign type system into clean's
    // format. Even when the source HOL kernel verified them, that is a
    // foreign kernel — not OUR clean kernel. Use `Translated` (not
    // `KernelVerified`) to avoid trust inflation.
    match trust {
        TrustLevel::KernelVerified | TrustLevel::AxiomDependent => ImportConfidence::Translated,
        TrustLevel::CertificateReplayed => ImportConfidence::Translated,
        TrustLevel::PartiallyAxiomatized | TrustLevel::TrustedOracle => {
            ImportConfidence::Axiomatized
        }
    }
}

pub(crate) fn write_hol_family_shard(
    hol_light_constants: &[MathverseImportedConstant],
    hol_light_stats: &ImportStatistics,
    hol4_constants: &[MathverseImportedConstant],
    hol4_stats: &ImportStatistics,
    isa_constants: &[crate::hol::isabelle::importer::IsaImportedConstant],
    writer: &mut ShardWriter,
) -> HolFamilyShardStats {
    let mut stats = HolFamilyShardStats {
        names: Vec::with_capacity(
            hol_light_stats.total() + hol4_stats.total() + isa_constants.len(),
        ),
        ..Default::default()
    };
    stats.hol_light_count = write_ot_constants(
        hol_light_constants,
        SourceSystem::HolLight,
        writer,
        &mut stats.names,
    );
    stats.hol4_count =
        write_ot_constants(hol4_constants, SourceSystem::Hol4, writer, &mut stats.names);
    stats.isabelle_count = write_isa_constants(isa_constants, writer, &mut stats.names);
    stats.total_count = stats.hol_light_count + stats.hol4_count + stats.isabelle_count;
    stats
}

fn write_ot_constants(
    constants: &[MathverseImportedConstant],
    source_system: SourceSystem,
    writer: &mut ShardWriter,
    names: &mut Vec<String>,
) -> usize {
    for constant in constants {
        push_constant(
            &constant.name.to_string(),
            &constant.type_expr,
            source_system,
            constant.trust_level,
            decl_kind_from_ot_kind(constant.kind),
            constant.axiom_profile,
            writer,
            names,
        );
    }
    constants.len()
}

fn write_isa_constants(
    constants: &[crate::hol::isabelle::importer::IsaImportedConstant],
    writer: &mut ShardWriter,
    names: &mut Vec<String>,
) -> usize {
    for constant in constants {
        let decl_kind = match constant.translated.proof_status {
            ProofStatus::Proved => DeclKind::Theorem,
            ProofStatus::Axiomatized => DeclKind::Axiom,
        };
        push_constant(
            &constant.name,
            &constant.translated.type_expr,
            SourceSystem::Isabelle,
            constant.trust_level,
            decl_kind,
            constant.axiom_profile,
            writer,
            names,
        );
    }
    constants.len()
}

fn push_constant(
    name: &str,
    type_expr: &clean_kernel::Expr,
    source_system: SourceSystem,
    trust_level: TrustLevel,
    decl_kind: DeclKind,
    axiom_profile: crate::types::AxiomProfile,
    writer: &mut ShardWriter,
    names: &mut Vec<String>,
) {
    let name_idx = writer.add_string(name);
    let type_idx = lower_kernel_expr(type_expr, writer);
    writer.add_constant(MathverseConstantHeader {
        name_idx,
        type_idx,
        value_idx: NO_VALUE,
        source_system: source_system as u8,
        import_confidence: trust_to_confidence(trust_level) as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: decl_kind as u8,
        axiom_profile,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    });
    names.push(name.to_owned());
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hol::isabelle::translate::TranslatedTheorem;
    use crate::hol::isabelle::types::ProofStatus;
    use crate::hol::opentheory_bridge::{ImportedConstantKind, HOL_BASE_PROFILE};
    use crate::shard::ShardReader;
    use crate::types::{AxiomProfile, Provenance};
    use clean_kernel::{Expr, Name as LeanName};

    fn ot(name: &str, source: SourceSystem, trust: TrustLevel) -> MathverseImportedConstant {
        ot_with_kind(name, source, trust, ImportedConstantKind::Theorem)
    }

    fn ot_with_kind(
        name: &str,
        source: SourceSystem,
        trust: TrustLevel,
        kind: ImportedConstantKind,
    ) -> MathverseImportedConstant {
        MathverseImportedConstant {
            type_expr: Expr::prop(),
            name: LeanName::from_string(name),
            axiom_profile: HOL_BASE_PROFILE,
            provenance: Provenance {
                source,
                original_name: name.to_owned(),
                source_file: None,
                axiom_profile: HOL_BASE_PROFILE,
            },
            trust_level: trust,
            kind,
        }
    }

    fn isa_with_status(
        name: &str,
        trust: TrustLevel,
        status: ProofStatus,
    ) -> crate::hol::isabelle::importer::IsaImportedConstant {
        let profile = AxiomProfile(
            AxiomProfile::CLASSICAL.0
                | AxiomProfile::EXTENSIONALITY.0
                | AxiomProfile::ISABELLE_LCF_ERASED.0,
        );
        let provenance = Provenance {
            source: SourceSystem::Isabelle,
            original_name: name.to_owned(),
            source_file: Some("Test.thy".to_owned()),
            axiom_profile: profile,
        };
        crate::hol::isabelle::importer::IsaImportedConstant {
            name: name.to_owned(),
            translated: TranslatedTheorem {
                name: name.to_owned(),
                type_expr: Expr::prop(),
                proof_status: status,
                axiom_profile: profile,
                trust_level: trust,
                provenance: provenance.clone(),
            },
            provenance,
            trust_level: trust,
            axiom_profile: profile,
        }
    }

    fn isa(name: &str, trust: TrustLevel) -> crate::hol::isabelle::importer::IsaImportedConstant {
        let profile = AxiomProfile(
            AxiomProfile::CLASSICAL.0
                | AxiomProfile::EXTENSIONALITY.0
                | AxiomProfile::ISABELLE_LCF_ERASED.0,
        );
        let provenance = Provenance {
            source: SourceSystem::Isabelle,
            original_name: name.to_owned(),
            source_file: Some("Test.thy".to_owned()),
            axiom_profile: profile,
        };
        crate::hol::isabelle::importer::IsaImportedConstant {
            name: name.to_owned(),
            translated: TranslatedTheorem {
                name: name.to_owned(),
                type_expr: Expr::prop(),
                proof_status: ProofStatus::Proved,
                axiom_profile: profile,
                trust_level: trust,
                provenance: provenance.clone(),
            },
            provenance,
            trust_level: trust,
            axiom_profile: profile,
        }
    }

    fn reader(writer: &mut ShardWriter) -> ShardReader {
        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();
        ShardReader::from_bytes(&buf).unwrap()
    }

    #[test]
    fn test_write_hol_family_shard_empty() {
        let mut writer = ShardWriter::new();
        let stats = write_hol_family_shard(
            &[],
            &ImportStatistics::default(),
            &[],
            &ImportStatistics::default(),
            &[],
            &mut writer,
        );
        assert_eq!(stats, HolFamilyShardStats::default());
    }

    #[test]
    fn test_write_hol_family_shard_hol_light_only() {
        let constants = vec![
            ot(
                "HOL.True",
                SourceSystem::HolLight,
                TrustLevel::CertificateReplayed,
            ),
            ot(
                "HOL.ext",
                SourceSystem::HolLight,
                TrustLevel::PartiallyAxiomatized,
            ),
        ];
        let mut writer = ShardWriter::new();
        let stats = write_hol_family_shard(
            &constants,
            &ImportStatistics {
                support_count: 1,
                assumption_count: 0,
                theorem_count: 1,
            },
            &[],
            &ImportStatistics::default(),
            &[],
            &mut writer,
        );
        let shard = reader(&mut writer);
        assert_eq!(stats.hol_light_count, 2);
        assert_eq!(stats.hol4_count + stats.isabelle_count, 0);
        assert_eq!(stats.total_count, 2);
        assert_eq!(shard.header.constant_count, 2);
        assert_eq!(
            shard.lookup_name("HOL.True").unwrap().1.source_system,
            SourceSystem::HolLight as u8
        );
        assert_eq!(
            shard.lookup_name("HOL.True").unwrap().1.import_confidence,
            ImportConfidence::Translated as u8
        );
        assert_eq!(
            shard.lookup_name("HOL.ext").unwrap().1.import_confidence,
            ImportConfidence::Axiomatized as u8
        );
    }

    #[test]
    fn test_write_hol_family_shard_mixed_systems() {
        let hol_light = vec![ot(
            "HL.eq_mp",
            SourceSystem::HolLight,
            TrustLevel::CertificateReplayed,
        )];
        let hol4 = vec![ot(
            "H4.bool_case",
            SourceSystem::Hol4,
            TrustLevel::AxiomDependent,
        )];
        let isa = vec![isa("Isa.conjI", TrustLevel::TrustedOracle)];
        let mut writer = ShardWriter::new();
        let stats = write_hol_family_shard(
            &hol_light,
            &ImportStatistics {
                support_count: 0,
                assumption_count: 0,
                theorem_count: 1,
            },
            &hol4,
            &ImportStatistics {
                support_count: 0,
                assumption_count: 1,
                theorem_count: 0,
            },
            &isa,
            &mut writer,
        );
        let shard = reader(&mut writer);
        assert_eq!(
            (
                stats.hol_light_count,
                stats.hol4_count,
                stats.isabelle_count,
                stats.total_count
            ),
            (1, 1, 1, 3)
        );
        assert_eq!(stats.names, vec!["HL.eq_mp", "H4.bool_case", "Isa.conjI"]);
        assert_eq!(
            shard.lookup_name("HL.eq_mp").unwrap().1.source_system,
            SourceSystem::HolLight as u8
        );
        assert_eq!(
            shard.lookup_name("H4.bool_case").unwrap().1.source_system,
            SourceSystem::Hol4 as u8
        );
        assert_eq!(
            shard.lookup_name("Isa.conjI").unwrap().1.source_system,
            SourceSystem::Isabelle as u8
        );
        assert_eq!(
            shard
                .lookup_name("H4.bool_case")
                .unwrap()
                .1
                .import_confidence,
            ImportConfidence::Translated as u8
        );
        assert_eq!(
            shard.lookup_name("Isa.conjI").unwrap().1.import_confidence,
            ImportConfidence::Axiomatized as u8
        );
    }

    /// Regression test for #3521: each HOL-family constant round-trips with
    /// the correct `DeclKind`. Previously `push_constant` hardcoded
    /// `decl_kind: 0` (Theorem) for all entries regardless of source kind.
    #[test]
    fn test_hol_family_shard_decl_kind_round_trips() {
        let hol_light = vec![
            ot_with_kind(
                "HL.thm",
                SourceSystem::HolLight,
                TrustLevel::CertificateReplayed,
                ImportedConstantKind::Theorem,
            ),
            ot_with_kind(
                "HL.axiom",
                SourceSystem::HolLight,
                TrustLevel::PartiallyAxiomatized,
                ImportedConstantKind::Assumption,
            ),
            ot_with_kind(
                "HL.support",
                SourceSystem::HolLight,
                TrustLevel::PartiallyAxiomatized,
                ImportedConstantKind::Support,
            ),
        ];
        let hol4 = vec![ot_with_kind(
            "H4.axiom",
            SourceSystem::Hol4,
            TrustLevel::AxiomDependent,
            ImportedConstantKind::Assumption,
        )];
        let isa = vec![
            isa_with_status(
                "Isa.proved",
                TrustLevel::CertificateReplayed,
                ProofStatus::Proved,
            ),
            isa_with_status(
                "Isa.opaque",
                TrustLevel::TrustedOracle,
                ProofStatus::Axiomatized,
            ),
        ];

        let mut writer = ShardWriter::new();
        let _stats = write_hol_family_shard(
            &hol_light,
            &ImportStatistics {
                support_count: 1,
                assumption_count: 1,
                theorem_count: 1,
            },
            &hol4,
            &ImportStatistics {
                support_count: 0,
                assumption_count: 1,
                theorem_count: 0,
            },
            &isa,
            &mut writer,
        );
        let shard = reader(&mut writer);

        // OpenTheory/HOL Light kinds.
        assert_eq!(
            shard.lookup_name("HL.thm").unwrap().1.decl_kind().unwrap(),
            DeclKind::Theorem,
        );
        assert_eq!(
            shard
                .lookup_name("HL.axiom")
                .unwrap()
                .1
                .decl_kind()
                .unwrap(),
            DeclKind::Axiom,
        );
        assert_eq!(
            shard
                .lookup_name("HL.support")
                .unwrap()
                .1
                .decl_kind()
                .unwrap(),
            DeclKind::Axiom,
        );

        // HOL4 (shared OT bridge).
        assert_eq!(
            shard
                .lookup_name("H4.axiom")
                .unwrap()
                .1
                .decl_kind()
                .unwrap(),
            DeclKind::Axiom,
        );

        // Isabelle proof status mapping.
        assert_eq!(
            shard
                .lookup_name("Isa.proved")
                .unwrap()
                .1
                .decl_kind()
                .unwrap(),
            DeclKind::Theorem,
        );
        assert_eq!(
            shard
                .lookup_name("Isa.opaque")
                .unwrap()
                .1
                .decl_kind()
                .unwrap(),
            DeclKind::Axiom,
        );
    }
}
