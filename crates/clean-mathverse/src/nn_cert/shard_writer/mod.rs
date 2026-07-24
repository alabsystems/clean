// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shard writer for NN verification certificates.
//!
//! Converts [`NNVerificationCert`] instances into Mathverse shard entries with proper
//! constant headers, trust levels, and axiom profile bits. Writes to a
//! `nn_verif.mathverse` shard file with an accompanying `.mathverse.json` metadata sidecar.

use std::path::Path;

use clean_kernel::flat::FlatExpr;

use crate::error::MathverseResult;
use crate::shard::ShardWriter;
use crate::shard_metadata::{DeclKind, MetadataEntry, ShardMetadata};
use crate::types::{ContentDomain, ImportConfidence, MathverseConstantHeader, NO_VALUE};

use super::types::{NNVerificationCert, NnCertImportStats, VerificationResult};

// ---------------------------------------------------------------------------
// Shard statistics
// ---------------------------------------------------------------------------

/// Statistics returned after writing NN certificates to a shard.
#[derive(Clone, Debug, Default)]
pub struct ShardStats {
    /// Number of shard entries written.
    pub entries_written: usize,
    /// Number of verified certificates.
    pub verified_count: usize,
    /// Number of counterexample certificates.
    pub counterexample_count: usize,
    /// Number of unknown-result certificates.
    pub unknown_count: usize,
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Write NN verification certificates to a shard file at `output_path`.
///
/// Creates both `output_path` (the `.mathverse` binary shard) and
/// `output_path.json` (the metadata sidecar).
///
/// Each certificate produces three shard entries:
/// 1. **Type declaration**: the network architecture as a type constant.
/// 2. **Proposition**: the robustness property as a proposition constant.
/// 3. **Axiom**: the proof result with trust level and axiom profile bits.
///
/// # Errors
///
/// Returns an error if the shard cannot be written to disk.
pub fn write_nn_certs_to_shard(
    certs: &[NNVerificationCert],
    output_path: &Path,
) -> MathverseResult<ShardStats> {
    let mut writer = ShardWriter::new();
    let mut metadata = ShardMetadata::new("NNVerification");
    let mut stats = ShardStats::default();

    for cert in certs {
        write_single_cert(cert, &mut writer, &mut metadata, &mut stats);
    }

    // Write the shard binary.
    let mut shard_bytes = Vec::new();
    writer.write(&mut shard_bytes)?;
    std::fs::write(output_path, &shard_bytes)?;

    // Write the metadata sidecar.
    crate::shard_metadata::write_metadata(output_path, &metadata)?;

    Ok(stats)
}

/// Write NN certificates to a [`ShardWriter`] without touching disk.
///
/// Useful for integration with other importers that combine multiple sources
/// into a single shard.
pub fn write_nn_certs_to_writer(
    certs: &[NNVerificationCert],
    writer: &mut ShardWriter,
) -> NnCertImportStats {
    let mut stats = NnCertImportStats::default();
    let mut shard_stats = ShardStats::default();
    // We don't need the sidecar metadata when writing to an in-memory writer,
    // but we still use a temporary one to keep the logic unified.
    let mut metadata = ShardMetadata::new("NNVerification");

    for cert in certs {
        write_single_cert(cert, writer, &mut metadata, &mut shard_stats);

        stats.total_parsed += 1;
        stats.total_neurons += cert.total_neurons();
        match cert.result {
            VerificationResult::Verified => stats.verified_count += 1,
            VerificationResult::Counterexample => stats.counterexample_count += 1,
            VerificationResult::Unknown => stats.unknown_count += 1,
        }
    }

    stats.entries_written = shard_stats.entries_written;
    stats
}

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

/// Write a single certificate as three shard entries.
fn write_single_cert(
    cert: &NNVerificationCert,
    writer: &mut ShardWriter,
    metadata: &mut ShardMetadata,
    stats: &mut ShardStats,
) {
    let base_name = sanitize_name(&cert.network_name);
    let profile = cert.axiom_profile();
    let source_system = cert.verifier_tool.source_system() as u8;

    // Entry 1: Network type declaration.
    let type_name = format!("{base_name}.NetworkType");
    write_type_decl(&type_name, cert, source_system, profile, writer, metadata);
    stats.entries_written += 1;

    // Entry 2: Property proposition.
    let prop_name = format!("{base_name}.RobustnessProperty");
    write_property_decl(&prop_name, cert, source_system, profile, writer, metadata);
    stats.entries_written += 1;

    // Entry 3: Proof axiom.
    let proof_name = format!("{base_name}.Proof");
    write_proof_axiom(&proof_name, cert, source_system, profile, writer, metadata);
    stats.entries_written += 1;

    match cert.result {
        VerificationResult::Verified => stats.verified_count += 1,
        VerificationResult::Counterexample => stats.counterexample_count += 1,
        VerificationResult::Unknown => stats.unknown_count += 1,
    }
}

/// Write the network architecture as a type declaration.
fn write_type_decl(
    name: &str,
    cert: &NNVerificationCert,
    source_system: u8,
    profile: crate::types::AxiomProfile,
    writer: &mut ShardWriter,
    metadata: &mut ShardMetadata,
) {
    let name_idx = writer.add_string(name);

    // Build a simple type expression: `NNNetwork(input_dim, output_dim, num_layers)`
    let type_sig = format!(
        "NNNetwork {} {} {}",
        cert.network_spec.input_dim,
        cert.network_spec.output_dim,
        cert.network_spec.layers.len()
    );
    let type_str_idx = writer.add_string(&type_sig);
    let type_idx = writer.add_expr(FlatExpr::lit_str(type_str_idx));

    let header = MathverseConstantHeader {
        name_idx,
        type_idx,
        value_idx: type_idx, // type decl has value = type
        source_system,
        import_confidence: ImportConfidence::Translated as u8,
        content_domain: ContentDomain::NnVerification as u8,
        decl_kind: crate::types::DeclKind::Definition as u8,
        axiom_profile: profile,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    };
    writer.add_constant(header);

    metadata.push(MetadataEntry {
        name: name.to_string(),
        kind: Some(DeclKind::Definition),
        type_signature: Some(type_sig),
        source_file: None,
        line_number: None,
    });
}

/// Write the robustness property as a proposition declaration.
fn write_property_decl(
    name: &str,
    cert: &NNVerificationCert,
    source_system: u8,
    profile: crate::types::AxiomProfile,
    writer: &mut ShardWriter,
    metadata: &mut ShardMetadata,
) {
    let name_idx = writer.add_string(name);

    let prop_sig = format_property_signature(&cert.property);
    let prop_str_idx = writer.add_string(&prop_sig);
    let type_idx = writer.add_expr(FlatExpr::lit_str(prop_str_idx));

    let header = MathverseConstantHeader {
        name_idx,
        type_idx,
        value_idx: NO_VALUE, // proposition, no proof term
        source_system,
        import_confidence: ImportConfidence::Axiomatized as u8,
        content_domain: ContentDomain::NnVerification as u8,
        decl_kind: crate::types::DeclKind::Axiom as u8,
        axiom_profile: profile,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    };
    writer.add_constant(header);

    metadata.push(MetadataEntry {
        name: name.to_string(),
        kind: Some(DeclKind::Axiom),
        type_signature: Some(prop_sig),
        source_file: None,
        line_number: None,
    });
}

/// Write the proof result as an axiom with trust level.
fn write_proof_axiom(
    name: &str,
    cert: &NNVerificationCert,
    source_system: u8,
    profile: crate::types::AxiomProfile,
    writer: &mut ShardWriter,
    metadata: &mut ShardMetadata,
) {
    let name_idx = writer.add_string(name);

    // The "type" of the proof is the property it proves.
    let proof_sig = format!(
        "{}({:?})",
        format_property_signature(&cert.property),
        cert.result
    );
    let proof_str_idx = writer.add_string(&proof_sig);
    let type_idx = writer.add_expr(FlatExpr::lit_str(proof_str_idx));

    let confidence = match cert.result {
        VerificationResult::Verified => ImportConfidence::Translated,
        VerificationResult::Counterexample => ImportConfidence::Axiomatized,
        VerificationResult::Unknown => ImportConfidence::Unverified,
    };

    let kind = match cert.result {
        VerificationResult::Verified => DeclKind::Theorem,
        VerificationResult::Counterexample | VerificationResult::Unknown => DeclKind::Axiom,
    };

    let header = MathverseConstantHeader {
        name_idx,
        type_idx,
        value_idx: NO_VALUE, // proof is axiomatized (external tool)
        source_system,
        import_confidence: confidence as u8,
        content_domain: ContentDomain::NnVerification as u8,
        decl_kind: kind.to_shard_kind() as u8,
        axiom_profile: profile,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    };
    writer.add_constant(header);

    metadata.push(MetadataEntry {
        name: name.to_string(),
        kind: Some(kind),
        type_signature: Some(proof_sig),
        source_file: None,
        line_number: None,
    });
}

/// Format a robustness property into a human-readable type signature.
fn format_property_signature(prop: &super::types::RobustnessProperty) -> String {
    let region = match &prop.input_region {
        super::types::InputRegion::EpsilonBall { epsilon, norm, .. } => {
            format!("Ball({norm:?}, {epsilon})")
        }
    };

    let constraint = match &prop.output_constraint {
        super::types::OutputConstraint::ClassificationPreserved { original_class } => {
            format!("ClassPreserved({original_class})")
        }
        super::types::OutputConstraint::NeuronBound {
            neuron_idx,
            lower,
            upper,
        } => format!("NeuronBound({neuron_idx}, {lower:?}, {upper:?})"),
    };

    format!("Robust({region}, {constraint})")
}

/// Sanitize a network name for use as an Mathverse constant name.
///
/// Replaces non-alphanumeric characters (except `.` and `_`) with `_`.
fn sanitize_name(name: &str) -> String {
    name.chars()
        .map(|c| {
            if c.is_alphanumeric() || c == '.' || c == '_' {
                c
            } else {
                '_'
            }
        })
        .collect()
}

#[cfg(test)]
mod tests;
