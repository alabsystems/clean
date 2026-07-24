// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! SAT certificate shard writer for the Mathverse Library.
//!
//! Converts verified SAT certificates into `.mathverse` shard entries. Each
//! certificate produces an axiomatized constant whose type encodes the
//! original CNF formula as a Prop-valued statement (unsatisfiability claim).
//!
//! The shard writer follows the same pattern as `hol/opentheory_shard.rs`:
//! lower types to `FlatExpr`, build `MathverseConstantHeader` entries, and add
//! them to a [`ShardWriter`].

use std::path::Path;

use clean_kernel::flat::FlatExpr;

use crate::error::MathverseResult;
use crate::shard::ShardWriter;
use crate::shard_metadata::{DeclKind, MetadataEntry, ShardMetadata};
use crate::types::{
    ContentDomain, ImportConfidence, MathverseConstantHeader, SourceSystem, NO_VALUE,
};

use super::types::{sat_cert_axiom_profile, sat_cert_trust_level, SatCertFormat, SatCertificate};

// ---------------------------------------------------------------------------
// Shard write result
// ---------------------------------------------------------------------------

/// Statistics from writing SAT certificates to a shard.
#[derive(Clone, Debug, Default)]
pub struct ShardStats {
    /// Number of certificates written.
    pub certs_written: usize,
    /// Number of DRAT certificates.
    pub drat_count: usize,
    /// Number of LRAT certificates.
    pub lrat_count: usize,
    /// Total formula variables across all certificates.
    pub total_variables: u64,
    /// Total formula clauses across all certificates.
    pub total_clauses: u64,
}

// ---------------------------------------------------------------------------
// Shard writer
// ---------------------------------------------------------------------------

/// Write SAT certificates to an `.mathverse` shard via [`ShardWriter`].
///
/// Each verified certificate becomes an Mathverse constant with:
/// - **Name:** `sat_cert.<format>.<vars>v.<clauses>c.<idx>` (unique per cert)
/// - **Type:** A `FlatExpr::sort(0)` placeholder representing the Prop-valued
///   unsatisfiability claim (the full CNF formula is in the provenance sidecar)
/// - **Value:** `NO_VALUE` (axiomatized — the certificate IS the proof)
/// - **Source system:** `SatSolver`
/// - **Import confidence:** `Translated` for LRAT, `Axiomatized` for DRAT
/// - **Axiom profile:** `SAT_CERT`
///
/// Returns statistics about what was written.
pub fn write_sat_certs_to_shard(certs: &[SatCertificate], writer: &mut ShardWriter) -> ShardStats {
    let mut stats = ShardStats::default();

    for (idx, cert) in certs.iter().enumerate() {
        let format_tag = match cert.format {
            SatCertFormat::DratText => {
                stats.drat_count += 1;
                "drat_text"
            }
            SatCertFormat::DratBinary => {
                stats.drat_count += 1;
                "drat_binary"
            }
            SatCertFormat::LratText => {
                stats.lrat_count += 1;
                "lrat_text"
            }
        };

        stats.total_variables += u64::from(cert.formula.num_vars);
        stats.total_clauses += cert.formula.num_clauses() as u64;

        let name = format!(
            "sat_cert.{fmt}.{vars}v.{cls}c.{idx}",
            fmt = format_tag,
            vars = cert.formula.num_vars,
            cls = cert.formula.num_clauses(),
        );

        let name_idx = writer.add_string(&name);

        // Type: Prop placeholder (Sort(0) = Prop in Lean type theory).
        // The actual formula is stored in the provenance sidecar.
        let type_idx = writer.add_expr(FlatExpr::sort(0));

        // Value: axiomatized (the certificate IS the proof, stored externally).
        let value_idx = NO_VALUE;

        // All SAT certificate types use Sort(0) placeholder types — the real
        // formula is in the provenance sidecar, not in a kernel-checkable FlatExpr.
        // Unverified is the honest label (consistent with DTT fix #3360).
        let confidence = match cert.format {
            SatCertFormat::LratText => ImportConfidence::Unverified,
            SatCertFormat::DratText | SatCertFormat::DratBinary => ImportConfidence::Axiomatized,
        };

        let header = MathverseConstantHeader {
            name_idx,
            type_idx,
            value_idx,
            source_system: SourceSystem::SatSolver as u8,
            import_confidence: confidence as u8,
            content_domain: ContentDomain::Logic as u8,
            // SAT certificates carry external proofs; the kernel-visible
            // constant is an opaque axiom whose witness lives in the sidecar.
            decl_kind: crate::types::DeclKind::Axiom as u8,
            axiom_profile: sat_cert_axiom_profile(),
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        };

        writer.add_constant(header);
        stats.certs_written += 1;
    }

    stats
}

/// Write SAT certificates to an `.mathverse` shard file on disk.
///
/// Creates the shard file and an accompanying `.mathverse.json` metadata sidecar.
///
/// # Errors
///
/// Returns an error if the shard file or metadata sidecar cannot be written.
pub fn write_sat_certs_to_file(
    certs: &[SatCertificate],
    path: &Path,
) -> MathverseResult<ShardStats> {
    let mut writer = ShardWriter::new();
    let stats = write_sat_certs_to_shard(certs, &mut writer);

    // Write the shard binary
    let mut file = std::fs::File::create(path)?;
    writer.write(&mut file)?;

    // Write metadata sidecar
    let mut metadata = ShardMetadata::new("SatSolver");
    for (idx, cert) in certs.iter().enumerate() {
        let format_tag = match cert.format {
            SatCertFormat::DratText => "drat_text",
            SatCertFormat::DratBinary => "drat_binary",
            SatCertFormat::LratText => "lrat_text",
        };
        let trust = sat_cert_trust_level(cert.format);
        metadata.push(MetadataEntry {
            name: format!(
                "sat_cert.{fmt}.{vars}v.{cls}c.{idx}",
                fmt = format_tag,
                vars = cert.formula.num_vars,
                cls = cert.formula.num_clauses(),
            ),
            kind: Some(DeclKind::Axiom),
            type_signature: Some(format!(
                "UNSAT({vars} vars, {cls} clauses) [{trust:?}]",
                vars = cert.formula.num_vars,
                cls = cert.formula.num_clauses(),
            )),
            source_file: None,
            line_number: None,
        });
    }
    crate::shard_metadata::write_metadata(path, &metadata)?;

    Ok(stats)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::decision_certs::types::CnfFormula;
    use crate::shard::ShardReader;

    fn make_drat_cert(num_vars: u32, num_clauses: usize) -> SatCertificate {
        let clauses = (0..num_clauses)
            .map(|i| vec![(i as i32) + 1, -((i as i32) + 2)])
            .collect();
        SatCertificate {
            formula: CnfFormula::new(num_vars, clauses),
            drat_steps: vec![
                super::super::types::DratStep::add(vec![1]),
                super::super::types::DratStep::delete(vec![1, -2]),
            ],
            lrat_steps: Vec::new(),
            format: SatCertFormat::DratText,
            verifier_tool: Some("drat-trim".to_string()),
        }
    }

    fn make_lrat_cert(num_vars: u32, num_clauses: usize) -> SatCertificate {
        let clauses = (0..num_clauses)
            .map(|i| vec![(i as i32) + 1, -((i as i32) + 2)])
            .collect();
        SatCertificate {
            formula: CnfFormula::new(num_vars, clauses),
            drat_steps: Vec::new(),
            lrat_steps: vec![
                super::super::types::LratStep::add(1, vec![1], vec![]),
                super::super::types::LratStep::delete(2, vec![1]),
            ],
            format: SatCertFormat::LratText,
            verifier_tool: Some("cake_lpr".to_string()),
        }
    }

    #[test]
    fn test_write_sat_certs_to_shard_empty() {
        let mut writer = ShardWriter::new();
        let stats = write_sat_certs_to_shard(&[], &mut writer);
        assert_eq!(stats.certs_written, 0);
        assert_eq!(stats.drat_count, 0);
        assert_eq!(stats.lrat_count, 0);
    }

    #[test]
    fn test_write_sat_certs_to_shard_drat() {
        let certs = vec![make_drat_cert(10, 5)];
        let mut writer = ShardWriter::new();
        let stats = write_sat_certs_to_shard(&certs, &mut writer);

        assert_eq!(stats.certs_written, 1);
        assert_eq!(stats.drat_count, 1);
        assert_eq!(stats.lrat_count, 0);
        assert_eq!(stats.total_variables, 10);
        assert_eq!(stats.total_clauses, 5);

        // Verify the shard is readable
        let mut buf = Vec::new();
        writer.write(&mut buf).expect("shard write should succeed");
        let reader = ShardReader::from_bytes(&buf).expect("shard read should succeed");
        assert_eq!(reader.header.constant_count, 1);
    }

    #[test]
    fn test_write_sat_certs_to_shard_lrat() {
        let certs = vec![make_lrat_cert(20, 10)];
        let mut writer = ShardWriter::new();
        let stats = write_sat_certs_to_shard(&certs, &mut writer);

        assert_eq!(stats.certs_written, 1);
        assert_eq!(stats.drat_count, 0);
        assert_eq!(stats.lrat_count, 1);
        assert_eq!(stats.total_variables, 20);
        assert_eq!(stats.total_clauses, 10);
    }

    #[test]
    fn test_write_sat_certs_to_shard_mixed() {
        let certs = vec![
            make_drat_cert(10, 5),
            make_lrat_cert(20, 10),
            make_drat_cert(30, 15),
        ];
        let mut writer = ShardWriter::new();
        let stats = write_sat_certs_to_shard(&certs, &mut writer);

        assert_eq!(stats.certs_written, 3);
        assert_eq!(stats.drat_count, 2);
        assert_eq!(stats.lrat_count, 1);
        assert_eq!(stats.total_variables, 60);
        assert_eq!(stats.total_clauses, 30);

        let mut buf = Vec::new();
        writer.write(&mut buf).expect("shard write should succeed");
        let reader = ShardReader::from_bytes(&buf).expect("shard read should succeed");
        assert_eq!(reader.header.constant_count, 3);
    }

    #[test]
    fn test_write_sat_certs_to_shard_confidence() {
        let certs = vec![make_drat_cert(5, 2), make_lrat_cert(5, 2)];
        let mut writer = ShardWriter::new();
        write_sat_certs_to_shard(&certs, &mut writer);

        let mut buf = Vec::new();
        writer.write(&mut buf).expect("shard write should succeed");
        let reader = ShardReader::from_bytes(&buf).expect("shard read should succeed");

        // First cert (DRAT) should be Axiomatized
        let name0 = "sat_cert.drat_text.5v.2c.0".to_string();
        let (_, hdr0) = reader.lookup_name(&name0).expect("should find DRAT cert");
        assert_eq!(hdr0.import_confidence, ImportConfidence::Axiomatized as u8);

        // Second cert (LRAT) — Sort(0) placeholder type, honest label is Unverified
        let name1 = "sat_cert.lrat_text.5v.2c.1".to_string();
        let (_, hdr1) = reader.lookup_name(&name1).expect("should find LRAT cert");
        assert_eq!(hdr1.import_confidence, ImportConfidence::Unverified as u8);
    }

    #[test]
    fn test_write_sat_certs_to_file() {
        let dir = tempfile::tempdir().expect("create temp dir");
        let shard_path = dir.path().join("sat_certs.mathverse");

        let certs = vec![make_drat_cert(10, 5)];
        let stats = write_sat_certs_to_file(&certs, &shard_path).expect("should write shard");

        assert_eq!(stats.certs_written, 1);
        assert!(shard_path.exists());

        // Check the metadata sidecar was written
        let sidecar_path = crate::shard_metadata::sidecar_path_for(&shard_path);
        assert!(sidecar_path.exists());

        let metadata =
            crate::shard_metadata::load_metadata(&shard_path).expect("should load metadata");
        assert_eq!(metadata.system_name, "SatSolver");
        assert_eq!(metadata.declaration_count, 1);
        assert!(metadata.declarations[0].name.contains("sat_cert"));
    }
}
