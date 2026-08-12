// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! MathMap bundle manifest schema and mandatory-field validation.
//!
//! The manifest is UNTRUSTED input. Parsing is deliberately strict: unknown
//! fields are rejected, duplicate JSON keys are rejected (so a signer and a
//! verifier can never disagree about which value is "the" value), and every
//! trust-relevant field must be present and non-empty before any downstream
//! gate is allowed to run.

use serde::de::{MapAccess, Visitor};
use serde::{Deserialize, Deserializer, Serialize};
use std::collections::BTreeSet;
use std::fmt;

/// Parsed `manifest.json` from an untrusted MathMap patch bundle.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct BundleManifest {
    /// Bundle contract version declared by the producing service.
    pub schema_version: Option<String>,
    /// Producer-assigned job identifier.
    pub job_id: Option<String>,
    /// Producing service name, matched against the trusted-key registry.
    pub service: Option<String>,
    /// Producing service version.
    pub service_version: Option<String>,
    /// Optional producing service revision.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub service_revision: Option<String>,
    /// RFC3339 issue timestamp, required whenever a bundle-age policy is set.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub issued_at: Option<String>,
    /// Repository the patches are pinned against.
    #[serde(default)]
    pub target_repo: TargetRepo,
    /// Theorems this bundle claims to close or repair.
    #[serde(default)]
    pub targets: Vec<BundleTarget>,
    /// Trust envelope the producer declares for this bundle.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub declared_trust: Option<DeclaredTrust>,
    /// Patch files carried in the bundle, with their content hashes.
    #[serde(default)]
    pub patches: Vec<PatchEntry>,
    /// Opaque producer certificates, carried but not interpreted here.
    #[serde(default)]
    pub certificates: Vec<serde_json::Value>,
    /// Optional digest binding the bundle's `prompt/` tree.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub prompt_digest: Option<String>,
    /// Optional digest binding the bundle's `solver_artifacts/` tree.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub solver_artifacts_digest: Option<String>,
}

// Strict JSON parsing that rejects duplicate keys. `serde_json`'s derived
// impl silently keeps the LAST occurrence of a repeated key, which opens a
// semantic gap between whatever the signer hashed and whatever the verifier
// parsed. We drive the map access manually and track seen keys instead.
impl<'de> Deserialize<'de> for BundleManifest {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        enum Field {
            SchemaVersion,
            JobId,
            Service,
            ServiceVersion,
            ServiceRevision,
            IssuedAt,
            TargetRepo,
            Targets,
            DeclaredTrust,
            Patches,
            Certificates,
            PromptDigest,
            SolverArtifactsDigest,
        }

        impl<'de> Deserialize<'de> for Field {
            fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
            where
                D: Deserializer<'de>,
            {
                struct FieldVisitor;
                impl<'de> Visitor<'de> for FieldVisitor {
                    type Value = Field;
                    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                        formatter.write_str("manifest field")
                    }
                    fn visit_str<E>(self, value: &str) -> Result<Field, E>
                    where
                        E: serde::de::Error,
                    {
                        match value {
                            "schema_version" => Ok(Field::SchemaVersion),
                            "job_id" => Ok(Field::JobId),
                            "service" => Ok(Field::Service),
                            "service_version" => Ok(Field::ServiceVersion),
                            "service_revision" => Ok(Field::ServiceRevision),
                            "issued_at" => Ok(Field::IssuedAt),
                            "target_repo" => Ok(Field::TargetRepo),
                            "targets" => Ok(Field::Targets),
                            "declared_trust" => Ok(Field::DeclaredTrust),
                            "patches" => Ok(Field::Patches),
                            "certificates" => Ok(Field::Certificates),
                            "prompt_digest" => Ok(Field::PromptDigest),
                            "solver_artifacts_digest" => Ok(Field::SolverArtifactsDigest),
                            _ => Err(serde::de::Error::unknown_field(value, FIELDS)),
                        }
                    }
                }
                deserializer.deserialize_identifier(FieldVisitor)
            }
        }

        const FIELDS: &[&str] = &[
            "schema_version",
            "job_id",
            "service",
            "service_version",
            "service_revision",
            "issued_at",
            "target_repo",
            "targets",
            "declared_trust",
            "patches",
            "certificates",
            "prompt_digest",
            "solver_artifacts_digest",
        ];

        struct ManifestVisitor;
        impl<'de> Visitor<'de> for ManifestVisitor {
            type Value = BundleManifest;
            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("struct BundleManifest")
            }
            fn visit_map<V>(self, mut map: V) -> Result<BundleManifest, V::Error>
            where
                V: MapAccess<'de>,
            {
                let mut schema_version = None;
                let mut job_id = None;
                let mut service = None;
                let mut service_version = None;
                let mut service_revision = None;
                let mut issued_at = None;
                let mut target_repo = None;
                let mut targets = None;
                let mut declared_trust = None;
                let mut patches = None;
                let mut certificates = None;
                let mut prompt_digest = None;
                let mut solver_artifacts_digest = None;

                let mut seen = BTreeSet::new();

                while let Some(key) = map.next_key::<Field>()? {
                    let key_str = match key {
                        Field::SchemaVersion => "schema_version",
                        Field::JobId => "job_id",
                        Field::Service => "service",
                        Field::ServiceVersion => "service_version",
                        Field::ServiceRevision => "service_revision",
                        Field::IssuedAt => "issued_at",
                        Field::TargetRepo => "target_repo",
                        Field::Targets => "targets",
                        Field::DeclaredTrust => "declared_trust",
                        Field::Patches => "patches",
                        Field::Certificates => "certificates",
                        Field::PromptDigest => "prompt_digest",
                        Field::SolverArtifactsDigest => "solver_artifacts_digest",
                    };
                    if !seen.insert(key_str) {
                        return Err(serde::de::Error::custom(format!(
                            "duplicate field `{key_str}` in manifest"
                        )));
                    }
                    match key {
                        Field::SchemaVersion => schema_version = Some(map.next_value()?),
                        Field::JobId => job_id = Some(map.next_value()?),
                        Field::Service => service = Some(map.next_value()?),
                        Field::ServiceVersion => service_version = Some(map.next_value()?),
                        Field::ServiceRevision => service_revision = Some(map.next_value()?),
                        Field::IssuedAt => issued_at = Some(map.next_value()?),
                        Field::TargetRepo => target_repo = Some(map.next_value()?),
                        Field::Targets => targets = Some(map.next_value()?),
                        Field::DeclaredTrust => declared_trust = Some(map.next_value()?),
                        Field::Patches => patches = Some(map.next_value()?),
                        Field::Certificates => certificates = Some(map.next_value()?),
                        Field::PromptDigest => prompt_digest = Some(map.next_value()?),
                        Field::SolverArtifactsDigest => {
                            solver_artifacts_digest = Some(map.next_value()?);
                        }
                    }
                }

                Ok(BundleManifest {
                    schema_version: schema_version.flatten(),
                    job_id: job_id.flatten(),
                    service: service.flatten(),
                    service_version: service_version.flatten(),
                    service_revision: service_revision.flatten(),
                    issued_at: issued_at.flatten(),
                    target_repo: target_repo.unwrap_or_default(),
                    targets: targets.unwrap_or_default(),
                    declared_trust: declared_trust.flatten(),
                    patches: patches.unwrap_or_default(),
                    certificates: certificates.unwrap_or_default(),
                    prompt_digest: prompt_digest.flatten(),
                    solver_artifacts_digest: solver_artifacts_digest.flatten(),
                })
            }
        }

        deserializer.deserialize_struct("BundleManifest", FIELDS, ManifestVisitor)
    }
}

/// Repository pin the bundle's patches were produced against.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TargetRepo {
    /// Repository URL.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub url: Option<String>,
    /// Pinned revision the patches apply to.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub rev: Option<String>,
    /// Pinned Lake/Lean toolchain.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub lake_toolchain: Option<String>,
}

/// One theorem the bundle claims to close or repair.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct BundleTarget {
    /// Theorem name.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub theorem: Option<String>,
    /// Module the theorem lives in.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub module: Option<String>,
    /// Target kind, matched against the policy allow/deny lists.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub kind: Option<String>,
    /// Statement hash the target MUST still have after the patch.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub expected_statement_hash: Option<String>,
}

/// Trust envelope declared by the producing service.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DeclaredTrust {
    /// Whether the patch introduces new axioms.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub introduces_new_axioms: Option<bool>,
    /// Whether the patch introduces new opaque constants.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub introduces_new_opaques: Option<bool>,
    /// Whether the patch introduces `unsafe` declarations.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub introduces_unsafe: Option<bool>,
    /// External solvers the patch is allowed to trust.
    #[serde(default)]
    pub external_solvers: Vec<String>,
    /// Whether proof terms in the patch were machine-generated.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub generated_proof_terms: Option<bool>,
}

/// One patch file carried in the bundle.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PatchEntry {
    /// Bundle-relative path of the patch file.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub path: Option<String>,
    /// SHA-256 of the patch bytes, optionally `sha256:`-prefixed.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub sha256: Option<String>,
}

/// Mandatory-field validation failure for an untrusted manifest.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ManifestValidationError {
    /// A mandatory field was absent.
    MissingMandatoryField {
        /// Field path, e.g. `targets[].theorem`.
        field: &'static str,
    },
    /// A mandatory field was present but blank.
    EmptyMandatoryField {
        /// Field path, e.g. `service`.
        field: &'static str,
    },
    /// `targets` was empty.
    EmptyTargets,
    /// `patches` was empty.
    EmptyPatches,
    /// A patch path escaped the bundle root or was otherwise unsafe.
    InvalidPatchPath {
        /// The rejected path.
        path: String,
    },
}

impl fmt::Display for ManifestValidationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingMandatoryField { field } => {
                write!(f, "missing mandatory manifest field `{field}`")
            }
            Self::EmptyMandatoryField { field } => {
                write!(f, "mandatory manifest field `{field}` must not be empty")
            }
            Self::EmptyTargets => write!(f, "manifest `targets` must contain at least one target"),
            Self::EmptyPatches => write!(f, "manifest `patches` must contain at least one patch"),
            Self::InvalidPatchPath { path } => {
                write!(
                    f,
                    "manifest patch path `{path}` is not a safe relative path"
                )
            }
        }
    }
}

impl std::error::Error for ManifestValidationError {}

impl BundleManifest {
    /// Fail-closed check that every trust-relevant manifest field is present.
    ///
    /// No downstream gate may run against a manifest that has not passed this.
    pub fn validate_mandatory_fields(&self) -> Result<(), ManifestValidationError> {
        require_text("schema_version", self.schema_version.as_deref())?;
        require_text("job_id", self.job_id.as_deref())?;
        require_text("service", self.service.as_deref())?;
        require_text("service_version", self.service_version.as_deref())?;
        require_text("target_repo.rev", self.target_repo.rev.as_deref())?;
        require_text(
            "target_repo.lake_toolchain",
            self.target_repo.lake_toolchain.as_deref(),
        )?;

        if self.targets.is_empty() {
            return Err(ManifestValidationError::EmptyTargets);
        }
        for target in &self.targets {
            require_text("targets[].theorem", target.theorem.as_deref())?;
            require_text("targets[].module", target.module.as_deref())?;
            require_text("targets[].kind", target.kind.as_deref())?;
            require_text(
                "targets[].expected_statement_hash",
                target.expected_statement_hash.as_deref(),
            )?;
        }

        let Some(declared_trust) = self.declared_trust.as_ref() else {
            return Err(ManifestValidationError::MissingMandatoryField {
                field: "declared_trust",
            });
        };
        require_bool(
            "declared_trust.introduces_new_axioms",
            declared_trust.introduces_new_axioms,
        )?;
        require_bool(
            "declared_trust.introduces_new_opaques",
            declared_trust.introduces_new_opaques,
        )?;
        require_bool(
            "declared_trust.introduces_unsafe",
            declared_trust.introduces_unsafe,
        )?;
        require_bool(
            "declared_trust.generated_proof_terms",
            declared_trust.generated_proof_terms,
        )?;

        if self.patches.is_empty() {
            return Err(ManifestValidationError::EmptyPatches);
        }
        for patch in &self.patches {
            let path = require_text("patches[].path", patch.path.as_deref())?;
            require_text("patches[].sha256", patch.sha256.as_deref())?;
            if !is_safe_relative_path(path) {
                return Err(ManifestValidationError::InvalidPatchPath {
                    path: path.to_owned(),
                });
            }
        }

        Ok(())
    }

    /// Trimmed producing service name.
    #[must_use]
    pub fn service(&self) -> Option<&str> {
        self.service.as_deref().map(str::trim)
    }

    /// Trimmed producer job identifier.
    #[must_use]
    pub fn job_id(&self) -> Option<&str> {
        self.job_id.as_deref().map(str::trim)
    }
}

fn require_text<'a>(
    field: &'static str,
    value: Option<&'a str>,
) -> Result<&'a str, ManifestValidationError> {
    let Some(value) = value else {
        return Err(ManifestValidationError::MissingMandatoryField { field });
    };
    if value.trim().is_empty() {
        return Err(ManifestValidationError::EmptyMandatoryField { field });
    }
    Ok(value)
}

fn require_bool(field: &'static str, value: Option<bool>) -> Result<bool, ManifestValidationError> {
    value.ok_or(ManifestValidationError::MissingMandatoryField { field })
}

/// Whether `path` is a bundle-relative path that cannot escape the bundle root.
///
/// Rejects absolute paths, backslashes, empty components, `.` and `..`.
#[must_use]
pub fn is_safe_relative_path(path: &str) -> bool {
    if path.is_empty() || path.starts_with('/') || path.starts_with('\\') {
        return false;
    }
    if path.contains('\\') {
        return false;
    }
    !path
        .split('/')
        .any(|part| part.is_empty() || part == "." || part == "..")
}
