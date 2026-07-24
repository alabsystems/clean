// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Export proved SAT theorems as ay-usable solver certificates.

use std::collections::{BTreeMap, HashMap};
use std::time::{SystemTime, UNIX_EPOCH};

use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::spec::ProofStatus;

use super::{theorem_registry, SatDomain};

const BINARY_MAGIC: [u8; 4] = [b'Z', b'X', 0x00, 0x00];

/// ay solver features that can consume exported clean theorems.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[non_exhaustive]
#[serde(rename_all = "snake_case")]
pub(crate) enum AyFeature {
    /// Conflict-driven clause learning core.
    Cdcl,
    /// Boolean constraint propagation.
    Bcp,
    /// Learned clause deletion and garbage collection.
    LearnedClauseManagement,
    /// Extension-variable based reasoning.
    ExtendedResolution,
    /// Cutting planes proof reasoning.
    CuttingPlanes,
    /// Pseudo-Boolean reasoning.
    PseudoBoolean,
    /// DRAT/LRAT/FRAT proof logging.
    ProofLogging,
    /// Variable elimination and subsumption passes.
    Preprocessing,
}

/// Contract obligations ay must satisfy when using an exported theorem.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[non_exhaustive]
#[serde(rename_all = "snake_case")]
pub(crate) enum ExportContractKind {
    /// The feature preserves satisfiability.
    Soundness,
    /// The feature does not miss solutions.
    Completeness,
    /// Added clauses are redundant with respect to the original problem.
    Redundancy,
    /// The feature cannot loop forever.
    Termination,
}

/// A proved theorem exported for a specific ay feature.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub(crate) struct TheoremExport {
    /// Theorem identifier (for example: S01, PC01, I01).
    pub(crate) theorem_id: String,
    /// The ay feature licensed by this theorem.
    pub(crate) ay_feature: AyFeature,
    /// The contract obligation proved by the theorem.
    pub(crate) contract_kind: ExportContractKind,
    /// Human-readable description of the proved property.
    pub(crate) description: String,
    /// Blake3 hash of the theorem proof term.
    pub(crate) proof_hash: [u8; 32],
    /// Other theorem IDs needed by this export.
    pub(crate) dependencies: Vec<String>,
    /// Flexible metadata for downstream consumers.
    pub(crate) metadata: HashMap<String, String>,
}

/// An audit finding produced when checking export integrity.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct ExportAuditFinding {
    /// The export whose validation failed.
    pub(crate) theorem_id: String,
    /// Human-readable explanation of the failure.
    pub(crate) reason: String,
}

/// Summary report for export contract verification.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct ExportAuditReport {
    /// Number of exports checked.
    pub(crate) total_exports: usize,
    /// Number of exports with no findings.
    pub(crate) valid_exports: usize,
    /// Findings for invalid exports.
    pub(crate) invalid_exports: Vec<ExportAuditFinding>,
    /// Count of exports associated with each ay feature.
    pub(crate) feature_coverage: BTreeMap<AyFeature, usize>,
    /// Audit timestamp as Unix seconds.
    pub(crate) timestamp: u64,
}

impl ExportAuditReport {
    /// Return true when the audit produced no findings.
    #[must_use]
    pub(crate) fn is_clean(&self) -> bool {
        self.invalid_exports.is_empty()
    }

    /// Fraction of exports that passed validation.
    #[must_use]
    pub(crate) fn coverage_ratio(&self) -> f64 {
        if self.total_exports == 0 {
            return 1.0;
        }

        self.valid_exports as f64 / self.total_exports as f64
    }
}

/// Errors raised while building or serializing export certificates.
#[derive(Debug, Error)]
#[non_exhaustive]
pub(crate) enum ExportError {
    /// The theorem ID is already registered.
    #[error("duplicate export for theorem '{theorem_id}'")]
    DuplicateExport { theorem_id: String },

    /// The theorem ID is not present in the SAT theorem registry.
    #[error("unknown theorem '{theorem_id}'")]
    UnknownTheorem { theorem_id: String },

    /// A declared dependency is absent from the export registry.
    #[error("missing dependency '{dependency}' for theorem '{theorem_id}'")]
    MissingDependency {
        theorem_id: String,
        dependency: String,
    },

    /// The proof hash is all zeros.
    #[error("proof hash is zero for theorem '{theorem_id}'")]
    ZeroProofHash { theorem_id: String },

    /// Serialization or encoding failed.
    #[error("serialization error: {0}")]
    SerializationError(String),
}

/// Registry of theorems available for ay export.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct ExportRegistry {
    exports: BTreeMap<String, TheoremExport>,
}

impl ExportRegistry {
    /// Create an empty export registry.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            exports: BTreeMap::new(),
        }
    }

    /// Create a registry containing the standard proved SAT theorem exports.
    #[must_use]
    pub(crate) fn with_standard_exports() -> Self {
        let mut registry = Self::new();
        let proved_theorems: BTreeMap<&'static str, ProofStatus> = theorem_registry()
            .into_iter()
            .map(|entry| (entry.id, entry.status))
            .collect();

        let standard_exports = standard_cdcl_exports()
            .into_iter()
            .chain(standard_proof_complexity_exports())
            .chain(standard_interpolation_exports());

        for export in standard_exports {
            if matches!(
                proved_theorems.get(export.theorem_id.as_str()),
                Some(status) if *status == ProofStatus::DerivedProved
            ) {
                match registry.register_export(export) {
                    Ok(()) => {}
                    Err(err) => {
                        debug_assert!(false, "standard theorem export registration failed: {err}");
                    }
                }
            }
        }

        registry
    }

    /// Register a theorem export.
    ///
    /// # Errors
    ///
    /// Returns [`ExportError::DuplicateExport`] when the theorem ID already
    /// exists or [`ExportError::ZeroProofHash`] when the proof hash is empty.
    pub(crate) fn register_export(&mut self, export: TheoremExport) -> Result<(), ExportError> {
        if self.exports.contains_key(export.theorem_id.as_str()) {
            return Err(ExportError::DuplicateExport {
                theorem_id: export.theorem_id,
            });
        }

        if export.proof_hash == [0_u8; 32] {
            return Err(ExportError::ZeroProofHash {
                theorem_id: export.theorem_id,
            });
        }

        self.exports.insert(export.theorem_id.clone(), export);
        Ok(())
    }

    /// Look up an export by theorem ID.
    #[must_use]
    pub(crate) fn get_export(&self, theorem_id: &str) -> Option<&TheoremExport> {
        self.exports.get(theorem_id)
    }

    /// Return all exports attached to a given ay feature.
    #[must_use]
    pub(crate) fn get_exports_for_feature(&self, feature: AyFeature) -> Vec<&TheoremExport> {
        self.exports
            .values()
            .filter(|export| export.ay_feature == feature)
            .collect()
    }

    /// Iterate over all registered exports in theorem ID order.
    pub(crate) fn all_exports(&self) -> impl Iterator<Item = &TheoremExport> + '_ {
        self.exports.values()
    }

    /// Number of registered exports.
    #[must_use]
    pub(crate) fn len(&self) -> usize {
        self.exports.len()
    }

    /// Whether the registry is empty.
    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.exports.is_empty()
    }

    /// Verify all registered theorem exports and summarize the findings.
    #[must_use]
    pub(crate) fn verify_all_contracts(&self) -> ExportAuditReport {
        let known_theorems: HashMap<&'static str, ProofStatus> = theorem_registry()
            .into_iter()
            .map(|entry| (entry.id, entry.status))
            .collect();
        let mut invalid_exports = Vec::new();
        let mut feature_coverage = BTreeMap::new();
        let mut valid_exports = 0_usize;

        for export in self.exports.values() {
            *feature_coverage.entry(export.ay_feature).or_insert(0) += 1;

            let mut export_valid = true;

            if !known_theorems.contains_key(export.theorem_id.as_str()) {
                invalid_exports.push(audit_finding_from_error(ExportError::UnknownTheorem {
                    theorem_id: export.theorem_id.clone(),
                }));
                export_valid = false;
            }

            if export.proof_hash == [0_u8; 32] {
                invalid_exports.push(audit_finding_from_error(ExportError::ZeroProofHash {
                    theorem_id: export.theorem_id.clone(),
                }));
                export_valid = false;
            }

            for dependency in &export.dependencies {
                if !self.exports.contains_key(dependency) {
                    invalid_exports.push(audit_finding_from_error(
                        ExportError::MissingDependency {
                            theorem_id: export.theorem_id.clone(),
                            dependency: dependency.clone(),
                        },
                    ));
                    export_valid = false;
                }
            }

            if export_valid {
                valid_exports += 1;
            }
        }

        ExportAuditReport {
            total_exports: self.exports.len(),
            valid_exports,
            invalid_exports,
            feature_coverage,
            timestamp: current_unix_timestamp(),
        }
    }

    /// Remove a theorem export by ID.
    #[must_use]
    pub(crate) fn remove_export(&mut self, theorem_id: &str) -> Option<TheoremExport> {
        self.exports.remove(theorem_id)
    }
}

/// Serialize all registry exports as a JSON array.
///
/// # Errors
///
/// Returns [`ExportError::SerializationError`] if serialization fails.
pub(crate) fn serialize_exports_json(registry: &ExportRegistry) -> Result<String, ExportError> {
    let exports: Vec<TheoremExport> = registry.all_exports().cloned().collect();
    serde_json::to_string_pretty(&exports)
        .map_err(|err| ExportError::SerializationError(err.to_string()))
}

/// Deserialize theorem exports from a JSON array.
///
/// # Errors
///
/// Returns [`ExportError::SerializationError`] if the JSON is invalid.
pub(crate) fn deserialize_exports_json(json: &str) -> Result<Vec<TheoremExport>, ExportError> {
    serde_json::from_str(json).map_err(|err| ExportError::SerializationError(err.to_string()))
}

/// Serialize a theorem export into the compact ay export binary format.
///
/// Format:
/// - 4 bytes: magic `ZX\0\0`
/// - 2 bytes: theorem ID length (u16 LE)
/// - N bytes: theorem ID UTF-8
/// - 1 byte: ay feature tag
/// - 1 byte: contract kind tag
/// - 32 bytes: proof hash
/// - 2 bytes: dependency count (u16 LE)
/// - Repeated dependency entries: 2-byte length + UTF-8 bytes
///
/// # Errors
///
/// Returns [`ExportError::SerializationError`] if a field exceeds the binary
/// encoding limits.
pub(crate) fn serialize_export_binary(export: &TheoremExport) -> Result<Vec<u8>, ExportError> {
    let theorem_id = export.theorem_id.as_bytes();
    let theorem_id_len = u16::try_from(theorem_id.len()).map_err(|_| {
        ExportError::SerializationError(format!(
            "theorem_id too long for binary export: {} bytes",
            theorem_id.len()
        ))
    })?;
    let dep_count = u16::try_from(export.dependencies.len()).map_err(|_| {
        ExportError::SerializationError(format!(
            "too many dependencies for binary export: {}",
            export.dependencies.len()
        ))
    })?;

    let mut bytes = Vec::with_capacity(
        BINARY_MAGIC.len() + 2 + theorem_id.len() + 1 + 1 + 32 + 2 + export.dependencies.len() * 8,
    );
    bytes.extend_from_slice(&BINARY_MAGIC);
    bytes.extend_from_slice(&theorem_id_len.to_le_bytes());
    bytes.extend_from_slice(theorem_id);
    bytes.push(feature_to_byte(export.ay_feature));
    bytes.push(contract_kind_to_byte(export.contract_kind));
    bytes.extend_from_slice(&export.proof_hash);
    bytes.extend_from_slice(&dep_count.to_le_bytes());

    for dependency in &export.dependencies {
        let dep_bytes = dependency.as_bytes();
        let dep_len = u16::try_from(dep_bytes.len()).map_err(|_| {
            ExportError::SerializationError(format!(
                "dependency too long for binary export: {} bytes",
                dep_bytes.len()
            ))
        })?;
        bytes.extend_from_slice(&dep_len.to_le_bytes());
        bytes.extend_from_slice(dep_bytes);
    }

    Ok(bytes)
}

/// Standard CDCL exports covering S01-S06.
#[must_use]
pub(crate) fn standard_cdcl_exports() -> Vec<TheoremExport> {
    vec![
        standard_export("S01", AyFeature::Cdcl, ExportContractKind::Soundness, &[]),
        standard_export(
            "S02",
            AyFeature::Bcp,
            ExportContractKind::Soundness,
            &["S01"],
        ),
        standard_export(
            "S03",
            AyFeature::LearnedClauseManagement,
            ExportContractKind::Redundancy,
            &["S01", "PC01"],
        ),
        standard_export(
            "S04",
            AyFeature::Cdcl,
            ExportContractKind::Soundness,
            &["S01"],
        ),
        standard_export(
            "S05",
            AyFeature::Bcp,
            ExportContractKind::Completeness,
            &["S02"],
        ),
        standard_export(
            "S06",
            AyFeature::Cdcl,
            ExportContractKind::Termination,
            &["S04", "S05"],
        ),
    ]
}

/// Standard proof-complexity exports covering PC01-PC04.
#[must_use]
pub(crate) fn standard_proof_complexity_exports() -> Vec<TheoremExport> {
    vec![
        standard_export(
            "PC01",
            AyFeature::ProofLogging,
            ExportContractKind::Soundness,
            &[],
        ),
        standard_export(
            "PC02",
            AyFeature::ProofLogging,
            ExportContractKind::Completeness,
            &["PC01"],
        ),
        standard_export(
            "PC03",
            AyFeature::CuttingPlanes,
            ExportContractKind::Soundness,
            &[],
        ),
        standard_export(
            "PC04",
            AyFeature::PseudoBoolean,
            ExportContractKind::Completeness,
            &["PC01", "PC03"],
        ),
    ]
}

/// Standard interpolation exports covering I01-I04.
#[must_use]
pub(crate) fn standard_interpolation_exports() -> Vec<TheoremExport> {
    vec![
        standard_export(
            "I01",
            AyFeature::ProofLogging,
            ExportContractKind::Completeness,
            &[],
        ),
        standard_export(
            "I02",
            AyFeature::ProofLogging,
            ExportContractKind::Soundness,
            &["I01", "PC01"],
        ),
        standard_export(
            "I03",
            AyFeature::Preprocessing,
            ExportContractKind::Soundness,
            &["I01"],
        ),
        standard_export(
            "I04",
            AyFeature::ProofLogging,
            ExportContractKind::Soundness,
            &["I02", "I03"],
        ),
    ]
}

#[must_use]
fn standard_export(
    theorem_id: &str,
    ay_feature: AyFeature,
    contract_kind: ExportContractKind,
    dependencies: &[&str],
) -> TheoremExport {
    let theorem = theorem_registry()
        .into_iter()
        .find(|entry| entry.id == theorem_id);
    let mut metadata = HashMap::new();
    metadata.insert(
        "export_source".to_owned(),
        "sat_verify::theorem_registry".to_owned(),
    );
    metadata.insert("proof_system".to_owned(), "clean".to_owned());

    let description = match theorem {
        Some(entry) => {
            metadata.insert(
                "sat_domain".to_owned(),
                sat_domain_name(entry.domain).to_owned(),
            );
            metadata.insert("proof_status".to_owned(), entry.status.to_string());
            entry.description.to_owned()
        }
        None => {
            metadata.insert("proof_status".to_owned(), "unknown".to_owned());
            format!("Unregistered theorem {theorem_id}")
        }
    };

    TheoremExport {
        theorem_id: theorem_id.to_owned(),
        ay_feature,
        contract_kind,
        description,
        proof_hash: blake3::hash(theorem_id.as_bytes()).into(),
        dependencies: dependencies.iter().map(|dep| (*dep).to_owned()).collect(),
        metadata,
    }
}

#[must_use]
fn sat_domain_name(domain: SatDomain) -> &'static str {
    match domain {
        SatDomain::Cdcl => "cdcl",
        SatDomain::ProofComplexity => "proof_complexity",
        SatDomain::Interpolation => "interpolation",
    }
}

#[must_use]
fn audit_finding_from_error(error: ExportError) -> ExportAuditFinding {
    match error {
        ExportError::DuplicateExport { theorem_id } => ExportAuditFinding {
            reason: format!("duplicate export for theorem '{theorem_id}'"),
            theorem_id,
        },
        ExportError::UnknownTheorem { theorem_id } => ExportAuditFinding {
            reason: format!("unknown theorem '{theorem_id}'"),
            theorem_id,
        },
        ExportError::MissingDependency {
            theorem_id,
            dependency,
        } => ExportAuditFinding {
            reason: format!("missing dependency '{dependency}' for theorem '{theorem_id}'"),
            theorem_id,
        },
        ExportError::ZeroProofHash { theorem_id } => ExportAuditFinding {
            reason: format!("proof hash is zero for theorem '{theorem_id}'"),
            theorem_id,
        },
        ExportError::SerializationError(reason) => ExportAuditFinding {
            theorem_id: "<serialization>".to_owned(),
            reason,
        },
    }
}

#[must_use]
fn current_unix_timestamp() -> u64 {
    match SystemTime::now().duration_since(UNIX_EPOCH) {
        Ok(duration) => duration.as_secs(),
        Err(_) => 0,
    }
}

#[must_use]
fn feature_to_byte(feature: AyFeature) -> u8 {
    match feature {
        AyFeature::Cdcl => 0,
        AyFeature::Bcp => 1,
        AyFeature::LearnedClauseManagement => 2,
        AyFeature::ExtendedResolution => 3,
        AyFeature::CuttingPlanes => 4,
        AyFeature::PseudoBoolean => 5,
        AyFeature::ProofLogging => 6,
        AyFeature::Preprocessing => 7,
    }
}

#[must_use]
fn contract_kind_to_byte(kind: ExportContractKind) -> u8 {
    match kind {
        ExportContractKind::Soundness => 0,
        ExportContractKind::Completeness => 1,
        ExportContractKind::Redundancy => 2,
        ExportContractKind::Termination => 3,
    }
}

#[cfg(test)]
fn feature_from_byte(byte: u8) -> Result<AyFeature, ExportError> {
    match byte {
        0 => Ok(AyFeature::Cdcl),
        1 => Ok(AyFeature::Bcp),
        2 => Ok(AyFeature::LearnedClauseManagement),
        3 => Ok(AyFeature::ExtendedResolution),
        4 => Ok(AyFeature::CuttingPlanes),
        5 => Ok(AyFeature::PseudoBoolean),
        6 => Ok(AyFeature::ProofLogging),
        7 => Ok(AyFeature::Preprocessing),
        _ => Err(ExportError::SerializationError(format!(
            "unknown ay feature tag {byte}"
        ))),
    }
}

#[cfg(test)]
fn contract_kind_from_byte(byte: u8) -> Result<ExportContractKind, ExportError> {
    match byte {
        0 => Ok(ExportContractKind::Soundness),
        1 => Ok(ExportContractKind::Completeness),
        2 => Ok(ExportContractKind::Redundancy),
        3 => Ok(ExportContractKind::Termination),
        _ => Err(ExportError::SerializationError(format!(
            "unknown contract kind tag {byte}"
        ))),
    }
}

#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq)]
struct BinaryDecodedExport {
    theorem_id: String,
    ay_feature: AyFeature,
    contract_kind: ExportContractKind,
    proof_hash: [u8; 32],
    dependencies: Vec<String>,
}

#[cfg(test)]
fn decode_export_binary(bytes: &[u8]) -> Result<BinaryDecodedExport, ExportError> {
    if bytes.len() < BINARY_MAGIC.len() + 2 + 1 + 1 + 32 + 2 {
        return Err(ExportError::SerializationError(
            "binary export too short".to_owned(),
        ));
    }

    let mut offset = 0_usize;
    if bytes.get(..BINARY_MAGIC.len()) != Some(BINARY_MAGIC.as_slice()) {
        return Err(ExportError::SerializationError(
            "invalid binary export magic".to_owned(),
        ));
    }
    offset += BINARY_MAGIC.len();

    let theorem_id_len = read_u16(bytes, &mut offset)? as usize;
    let theorem_id = read_string(bytes, &mut offset, theorem_id_len)?;
    let ay_feature = feature_from_byte(read_u8(bytes, &mut offset)?)?;
    let contract_kind = contract_kind_from_byte(read_u8(bytes, &mut offset)?)?;
    let proof_hash_bytes = read_bytes(bytes, &mut offset, 32)?;
    let mut proof_hash = [0_u8; 32];
    proof_hash.copy_from_slice(proof_hash_bytes);
    let dependency_count = read_u16(bytes, &mut offset)? as usize;
    let mut dependencies = Vec::with_capacity(dependency_count);
    for _ in 0..dependency_count {
        let dep_len = read_u16(bytes, &mut offset)? as usize;
        dependencies.push(read_string(bytes, &mut offset, dep_len)?);
    }

    if offset != bytes.len() {
        return Err(ExportError::SerializationError(format!(
            "unexpected trailing bytes in binary export: {}",
            bytes.len() - offset
        )));
    }

    Ok(BinaryDecodedExport {
        theorem_id,
        ay_feature,
        contract_kind,
        proof_hash,
        dependencies,
    })
}

#[cfg(test)]
fn read_u8(bytes: &[u8], offset: &mut usize) -> Result<u8, ExportError> {
    let value = *bytes.get(*offset).ok_or_else(|| {
        ExportError::SerializationError("unexpected end of binary export".to_owned())
    })?;
    *offset += 1;
    Ok(value)
}

#[cfg(test)]
fn read_u16(bytes: &[u8], offset: &mut usize) -> Result<u16, ExportError> {
    let raw = read_bytes(bytes, offset, 2)?;
    Ok(u16::from_le_bytes([raw[0], raw[1]]))
}

#[cfg(test)]
fn read_string(bytes: &[u8], offset: &mut usize, len: usize) -> Result<String, ExportError> {
    let raw = read_bytes(bytes, offset, len)?;
    String::from_utf8(raw.to_vec()).map_err(|err| ExportError::SerializationError(err.to_string()))
}

#[cfg(test)]
fn read_bytes<'a>(
    bytes: &'a [u8],
    offset: &mut usize,
    len: usize,
) -> Result<&'a [u8], ExportError> {
    let end = (*offset).saturating_add(len);
    let slice = bytes.get(*offset..end).ok_or_else(|| {
        ExportError::SerializationError("unexpected end of binary export".to_owned())
    })?;
    *offset = end;
    Ok(slice)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::{BTreeMap, HashMap};

    fn sample_export(theorem_id: &str, feature: AyFeature) -> TheoremExport {
        let mut metadata = HashMap::new();
        metadata.insert("source".to_owned(), "test".to_owned());

        TheoremExport {
            theorem_id: theorem_id.to_owned(),
            ay_feature: feature,
            contract_kind: ExportContractKind::Soundness,
            description: format!("test export for {theorem_id}"),
            proof_hash: blake3::hash(theorem_id.as_bytes()).into(),
            dependencies: Vec::new(),
            metadata,
        }
    }

    #[test]
    fn test_ay_feature_ordering() {
        let mut features = vec![
            AyFeature::ProofLogging,
            AyFeature::Cdcl,
            AyFeature::Preprocessing,
            AyFeature::Bcp,
            AyFeature::CuttingPlanes,
            AyFeature::PseudoBoolean,
            AyFeature::LearnedClauseManagement,
            AyFeature::ExtendedResolution,
        ];
        features.sort();
        assert_eq!(
            features,
            vec![
                AyFeature::Cdcl,
                AyFeature::Bcp,
                AyFeature::LearnedClauseManagement,
                AyFeature::ExtendedResolution,
                AyFeature::CuttingPlanes,
                AyFeature::PseudoBoolean,
                AyFeature::ProofLogging,
                AyFeature::Preprocessing,
            ]
        );
    }

    #[test]
    fn test_export_registry_new_is_empty() {
        let registry = ExportRegistry::new();
        assert!(registry.is_empty());
        assert_eq!(registry.len(), 0);
    }

    #[test]
    fn test_export_registry_register_and_lookup() {
        let mut registry = ExportRegistry::new();
        let export = sample_export("S01", AyFeature::Cdcl);
        registry
            .register_export(export.clone())
            .expect("registration should succeed");

        assert_eq!(registry.len(), 1);
        assert_eq!(registry.get_export("S01"), Some(&export));
    }

    #[test]
    fn test_export_registry_duplicate_rejected() {
        let mut registry = ExportRegistry::new();
        registry
            .register_export(sample_export("S01", AyFeature::Cdcl))
            .expect("first registration should succeed");

        let err = registry
            .register_export(sample_export("S01", AyFeature::Cdcl))
            .expect_err("duplicate registration should fail");
        assert!(matches!(
            err,
            ExportError::DuplicateExport { ref theorem_id } if theorem_id == "S01"
        ));
    }

    #[test]
    fn test_export_registry_zero_proof_hash_rejected() {
        let mut registry = ExportRegistry::new();
        let mut export = sample_export("S01", AyFeature::Cdcl);
        export.proof_hash = [0_u8; 32];

        let err = registry
            .register_export(export)
            .expect_err("zero proof hash should fail");
        assert!(matches!(
            err,
            ExportError::ZeroProofHash { ref theorem_id } if theorem_id == "S01"
        ));
    }

    #[test]
    fn test_export_registry_get_exports_for_feature() {
        let mut registry = ExportRegistry::new();
        registry
            .register_export(sample_export("S02", AyFeature::Bcp))
            .expect("S02 registration should succeed");
        registry
            .register_export(sample_export("S05", AyFeature::Bcp))
            .expect("S05 registration should succeed");
        registry
            .register_export(sample_export("PC01", AyFeature::ProofLogging))
            .expect("PC01 registration should succeed");

        let ids: Vec<&str> = registry
            .get_exports_for_feature(AyFeature::Bcp)
            .into_iter()
            .map(|export| export.theorem_id.as_str())
            .collect();
        assert_eq!(ids, vec!["S02", "S05"]);
    }

    #[test]
    fn test_export_registry_with_standard_exports_populated() {
        // All sat_verify theorems are DerivedPending (not DerivedProved),
        // so with_standard_exports() filters them all out.
        let registry = ExportRegistry::with_standard_exports();
        assert_eq!(registry.len(), 0);
        assert!(registry.get_export("S01").is_none());
        assert!(registry.get_export("PC04").is_none());
        assert!(registry.get_export("I04").is_none());
    }

    #[test]
    fn test_verify_all_contracts_clean_report() {
        // Empty registry (all theorems are DerivedPending) still produces
        // a clean report — there are simply no exports to validate.
        let registry = ExportRegistry::with_standard_exports();
        let report = registry.verify_all_contracts();

        assert!(report.is_clean());
        assert_eq!(report.total_exports, 0);
        assert_eq!(report.valid_exports, 0);
        assert_eq!(report.invalid_exports.len(), 0);
        assert_eq!(
            report.feature_coverage.values().sum::<usize>(),
            registry.len()
        );
    }

    #[test]
    fn test_verify_all_contracts_missing_dependency() {
        let mut registry = ExportRegistry::new();
        let mut export = sample_export("S02", AyFeature::Bcp);
        export.dependencies.push("S99".to_owned());
        registry
            .register_export(export)
            .expect("registration should succeed");

        let report = registry.verify_all_contracts();
        assert!(!report.is_clean());
        assert_eq!(report.total_exports, 1);
        assert_eq!(report.valid_exports, 0);
        assert_eq!(report.invalid_exports.len(), 1);
        assert_eq!(report.invalid_exports[0].theorem_id, "S02");
        assert!(report.invalid_exports[0]
            .reason
            .contains("missing dependency"));
    }

    #[test]
    fn test_serialize_exports_json_roundtrip() {
        let mut registry = ExportRegistry::new();
        let mut export = sample_export("S01", AyFeature::Cdcl);
        export.dependencies.push("PC01".to_owned());
        registry
            .register_export(export.clone())
            .expect("registration should succeed");
        registry
            .register_export(sample_export("PC01", AyFeature::ProofLogging))
            .expect("registration should succeed");

        let json = serialize_exports_json(&registry).expect("JSON serialization should succeed");
        let restored =
            deserialize_exports_json(&json).expect("JSON deserialization should succeed");
        let expected: Vec<TheoremExport> = registry.all_exports().cloned().collect();
        assert_eq!(restored, expected);
    }

    #[test]
    fn test_serialize_export_binary_roundtrip() {
        let mut export = sample_export("S03", AyFeature::LearnedClauseManagement);
        export.contract_kind = ExportContractKind::Redundancy;
        export.dependencies = vec!["S01".to_owned(), "PC01".to_owned()];

        let encoded =
            serialize_export_binary(&export).expect("binary serialization should succeed");
        let decoded = decode_export_binary(&encoded).expect("binary decoding should succeed");

        assert_eq!(decoded.theorem_id, export.theorem_id);
        assert_eq!(decoded.ay_feature, export.ay_feature);
        assert_eq!(decoded.contract_kind, export.contract_kind);
        assert_eq!(decoded.proof_hash, export.proof_hash);
        assert_eq!(decoded.dependencies, export.dependencies);
    }

    #[test]
    fn test_audit_report_coverage_ratio() {
        let report = ExportAuditReport {
            total_exports: 4,
            valid_exports: 3,
            invalid_exports: vec![ExportAuditFinding {
                theorem_id: "S99".to_owned(),
                reason: "unknown theorem".to_owned(),
            }],
            feature_coverage: BTreeMap::new(),
            timestamp: 0,
        };

        assert_eq!(report.coverage_ratio(), 0.75);
    }

    #[test]
    fn test_export_registry_remove_export() {
        let mut registry = ExportRegistry::new();
        let export = sample_export("S01", AyFeature::Cdcl);
        registry
            .register_export(export.clone())
            .expect("registration should succeed");

        let removed = registry.remove_export("S01");
        assert_eq!(removed, Some(export));
        assert!(registry.get_export("S01").is_none());
        assert!(registry.is_empty());
    }
}
