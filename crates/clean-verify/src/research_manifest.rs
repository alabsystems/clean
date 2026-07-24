// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Research-program manifest model and validation helpers.
//!
//! The manifest is a machine-readable inventory of research obligations that
//! sit outside the normal proved-theorem registry. It deliberately tracks
//! partial evidence levels such as executable checks and proof-carrying
//! certificates without conflating them with kernel proof status.

use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::Path;
use thiserror::Error;

/// Repository-relative path for the seeded research-program manifest.
pub const DEFAULT_RESEARCH_MANIFEST_PATH: &str = "data/research_program_manifest.json";

/// Current JSON schema version for [`ResearchManifest`].
pub const RESEARCH_MANIFEST_SCHEMA_VERSION: u32 = 1;

/// Research maturity status for a manifest item.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum ResearchStatus {
    /// The claim has been refuted or the prior statement is known false.
    Refuted,
    /// Empirical evidence exists, but no executable checker is authoritative.
    EmpiricalTested,
    /// A deterministic executable checker validates instances or witnesses.
    ExecutableChecked,
    /// Machine-checkable certificates exist, but the kernel proof is not closed.
    ProofCarrying,
    /// The claim is closed by a kernel-checked proof without open axioms.
    KernelProved,
    /// The claim is represented as an explicit axiom or honest assumption.
    Axiomatized,
    /// A spec/proof object exists, but the constructive proof is still pending.
    DerivedPending,
}

/// Current state of the artifact/replay surface for a manifest item.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum ResearchArtifactState {
    /// No cross-repo artifact applies to this theorem or spec item.
    NotApplicable,
    /// Producer/export work is planned but not yet landed.
    Planned,
    /// Wrapped or source fixtures exist, but the artifact path is not yet
    /// replay-ready.
    FixtureOnly,
    /// A proof-artifact path exists and can be replayed or imported.
    Replayable,
}

impl ResearchArtifactState {
    /// Stable display string for dashboards and reports.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::NotApplicable => "NotApplicable",
            Self::Planned => "Planned",
            Self::FixtureOnly => "FixtureOnly",
            Self::Replayable => "Replayable",
        }
    }
}

/// The current gate blocking promotion or closeout for a manifest item.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum PromotionGate {
    /// The item is blocked on kernel proof closure and honest axiom/audit
    /// accounting.
    KernelProofAndAxiomAudit,
    /// The item is blocked on trust-report agreement for guarded promotions.
    TrustReportAgreement,
    /// The item is blocked on artifact replay and kernel-import integration.
    ArtifactReplayAndKernelImport,
}

impl PromotionGate {
    /// Stable display string for dashboards and reports.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::KernelProofAndAxiomAudit => "KernelProofAndAxiomAudit",
            Self::TrustReportAgreement => "TrustReportAgreement",
            Self::ArtifactReplayAndKernelImport => "ArtifactReplayAndKernelImport",
        }
    }
}

/// A dependency edge between manifest items.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ResearchDependency {
    /// Manifest item identifier this item depends on.
    pub id: String,
    /// Why the dependency is relevant.
    pub reason: String,
}

impl ResearchDependency {
    /// Construct a dependency edge.
    #[must_use]
    pub fn new(id: impl Into<String>, reason: impl Into<String>) -> Self {
        Self {
            id: id.into(),
            reason: reason.into(),
        }
    }
}

/// One tracked research obligation, theorem family, or certificate family.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ResearchManifestItem {
    /// Stable item identifier, for example `C004`, `S40`, or `ZT01`.
    pub id: String,
    /// Human-readable item title.
    pub title: String,
    /// Owning repository for the next real execution step.
    pub owner_repo: String,
    /// Coarse owning domain, for example `gamma-crown` or `sat-frontier`.
    pub domain: String,
    /// Family name used for grouping related manifest items.
    pub family: String,
    /// Current maturity status.
    pub status: ResearchStatus,
    /// Current state of the artifact/replay surface.
    pub artifact_state: ResearchArtifactState,
    /// Current gate blocking promotion or closeout.
    pub promotion_gate: PromotionGate,
    /// Concise statement of the tracked claim or certificate family.
    pub summary: String,
    /// Manifest-local dependencies.
    #[serde(default)]
    pub dependencies: Vec<ResearchDependency>,
    /// Code, data, or audit references that support the status assignment.
    #[serde(default)]
    pub evidence: Vec<String>,
    /// Issue numbers, designs, papers, or other external references.
    #[serde(default)]
    pub references: Vec<String>,
    /// Free-form tags for filtering.
    #[serde(default)]
    pub tags: Vec<String>,
}

impl ResearchManifestItem {
    /// Construct a manifest item with no dependencies or references.
    #[must_use]
    pub fn new(
        id: impl Into<String>,
        title: impl Into<String>,
        domain: impl Into<String>,
        family: impl Into<String>,
        status: ResearchStatus,
        summary: impl Into<String>,
    ) -> Self {
        Self {
            id: id.into(),
            title: title.into(),
            owner_repo: "alabsystems/clean".to_owned(),
            domain: domain.into(),
            family: family.into(),
            status,
            artifact_state: ResearchArtifactState::NotApplicable,
            promotion_gate: PromotionGate::KernelProofAndAxiomAudit,
            summary: summary.into(),
            dependencies: Vec::new(),
            evidence: Vec::new(),
            references: Vec::new(),
            tags: Vec::new(),
        }
    }

    /// Set the owning repository for this item.
    #[must_use]
    pub fn with_owner_repo(mut self, owner_repo: impl Into<String>) -> Self {
        self.owner_repo = owner_repo.into();
        self
    }

    /// Set the artifact/replay state for this item.
    #[must_use]
    pub fn with_artifact_state(mut self, artifact_state: ResearchArtifactState) -> Self {
        self.artifact_state = artifact_state;
        self
    }

    /// Set the current promotion gate for this item.
    #[must_use]
    pub fn with_promotion_gate(mut self, promotion_gate: PromotionGate) -> Self {
        self.promotion_gate = promotion_gate;
        self
    }
}

/// Top-level research-program manifest.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ResearchManifest {
    /// Schema version used by this manifest file.
    pub schema_version: u32,
    /// UTC timestamp or date string for the manifest snapshot.
    pub generated_at: String,
    /// Issue or project that requested the manifest.
    pub source: String,
    /// Manifest items in stable presentation order.
    pub items: Vec<ResearchManifestItem>,
}

impl ResearchManifest {
    /// Load a manifest from a JSON file.
    ///
    /// # Errors
    ///
    /// Returns [`ResearchManifestError`] if the file cannot be read or parsed.
    pub fn load(path: impl AsRef<Path>) -> Result<Self> {
        let content = fs::read_to_string(path)?;
        Ok(serde_json::from_str(&content)?)
    }

    /// Save this manifest as pretty-printed JSON after validation.
    ///
    /// # Errors
    ///
    /// Returns [`ResearchManifestError`] if validation, serialization, or file
    /// writing fails.
    pub fn save(&self, path: impl AsRef<Path>) -> Result<()> {
        self.validate()?;
        let mut content = serde_json::to_string_pretty(self)?;
        content.push('\n');
        fs::write(path, content)?;
        Ok(())
    }

    /// Validate structural manifest invariants.
    ///
    /// # Errors
    ///
    /// Returns [`ResearchManifestError`] for duplicate IDs, empty required
    /// fields, unsupported schema versions, or unresolved dependencies.
    pub fn validate(&self) -> Result<()> {
        if self.schema_version != RESEARCH_MANIFEST_SCHEMA_VERSION {
            return Err(ResearchManifestError::UnsupportedSchemaVersion {
                expected: RESEARCH_MANIFEST_SCHEMA_VERSION,
                found: self.schema_version,
            });
        }
        if self.generated_at.trim().is_empty() {
            return Err(ResearchManifestError::EmptyManifestField {
                field: "generated_at",
            });
        }
        if self.source.trim().is_empty() {
            return Err(ResearchManifestError::EmptyManifestField { field: "source" });
        }
        if self.items.is_empty() {
            return Err(ResearchManifestError::EmptyManifest);
        }

        let mut ids = BTreeSet::new();
        for item in &self.items {
            validate_required_field(&item.id, &item.id, "id")?;
            validate_required_field(&item.id, &item.title, "title")?;
            validate_required_field(&item.id, &item.owner_repo, "owner_repo")?;
            validate_required_field(&item.id, &item.domain, "domain")?;
            validate_required_field(&item.id, &item.family, "family")?;
            validate_required_field(&item.id, &item.summary, "summary")?;

            if !ids.insert(item.id.as_str()) {
                return Err(ResearchManifestError::DuplicateItemId {
                    id: item.id.clone(),
                });
            }
        }

        for item in &self.items {
            for dependency in &item.dependencies {
                validate_required_field(&item.id, &dependency.id, "dependency.id")?;
                validate_required_field(&item.id, &dependency.reason, "dependency.reason")?;

                if dependency.id == item.id {
                    return Err(ResearchManifestError::SelfDependency {
                        item_id: item.id.clone(),
                    });
                }
                if !ids.contains(dependency.id.as_str()) {
                    return Err(ResearchManifestError::UnknownDependency {
                        item_id: item.id.clone(),
                        dependency_id: dependency.id.clone(),
                    });
                }
            }
        }

        Ok(())
    }

    /// Look up an item by ID.
    #[must_use]
    pub fn item(&self, id: &str) -> Option<&ResearchManifestItem> {
        self.items.iter().find(|item| item.id == id)
    }

    /// Return true if an item is currently marked [`ResearchStatus::KernelProved`].
    #[must_use]
    pub fn is_kernel_proved(&self, id: &str) -> bool {
        self.item(id)
            .is_some_and(|item| item.status == ResearchStatus::KernelProved)
    }

    /// Return added/removed/changed status rows between two manifest snapshots.
    #[must_use]
    pub fn status_changes_from(&self, previous: &Self) -> Vec<ResearchStatusChange> {
        let previous_statuses = previous
            .items
            .iter()
            .map(|item| (item.id.as_str(), item.status))
            .collect::<BTreeMap<_, _>>();
        let current_statuses = self
            .items
            .iter()
            .map(|item| (item.id.as_str(), item.status))
            .collect::<BTreeMap<_, _>>();

        let mut ids = BTreeSet::new();
        ids.extend(previous_statuses.keys().copied());
        ids.extend(current_statuses.keys().copied());

        ids.into_iter()
            .filter_map(|id| {
                let previous_status = previous_statuses.get(id).copied();
                let current_status = current_statuses.get(id).copied();
                if previous_status == current_status {
                    None
                } else {
                    Some(ResearchStatusChange {
                        id: id.to_owned(),
                        previous_status,
                        current_status,
                    })
                }
            })
            .collect()
    }
}

/// One manifest-item status diff row for CI or nightly replay output.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ResearchStatusChange {
    /// Stable manifest item identifier.
    pub id: String,
    /// Status in the previous snapshot, if the item existed.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub previous_status: Option<ResearchStatus>,
    /// Status in the current snapshot, if the item still exists.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub current_status: Option<ResearchStatus>,
}

/// Errors from manifest loading, saving, and validation.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum ResearchManifestError {
    /// Manifest file I/O failed.
    #[error("manifest I/O error: {0}")]
    Io(#[from] std::io::Error),
    /// Manifest JSON serialization or deserialization failed.
    #[error("manifest JSON error: {0}")]
    Json(#[from] serde_json::Error),
    /// The manifest uses an unsupported schema version.
    #[error("unsupported manifest schema version {found}; expected {expected}")]
    UnsupportedSchemaVersion {
        /// Expected schema version.
        expected: u32,
        /// Found schema version.
        found: u32,
    },
    /// The manifest contains no items.
    #[error("manifest must contain at least one item")]
    EmptyManifest,
    /// A top-level manifest field is empty.
    #[error("manifest field `{field}` must be non-empty")]
    EmptyManifestField {
        /// Empty top-level field name.
        field: &'static str,
    },
    /// An item field is empty.
    #[error("manifest item `{item_id}` field `{field}` must be non-empty")]
    EmptyItemField {
        /// Item containing the empty field.
        item_id: String,
        /// Empty field name.
        field: &'static str,
    },
    /// Two items have the same ID.
    #[error("duplicate manifest item id `{id}`")]
    DuplicateItemId {
        /// Duplicate item ID.
        id: String,
    },
    /// An item depends on itself.
    #[error("manifest item `{item_id}` depends on itself")]
    SelfDependency {
        /// Item containing the self-dependency.
        item_id: String,
    },
    /// A dependency references an item that does not exist in the manifest.
    #[error("manifest item `{item_id}` depends on unknown item `{dependency_id}`")]
    UnknownDependency {
        /// Item containing the dependency edge.
        item_id: String,
        /// Missing dependency item ID.
        dependency_id: String,
    },
}

/// Protocol-local manifest result type.
pub type Result<T> = std::result::Result<T, ResearchManifestError>;

/// Load a manifest from `path`.
///
/// # Errors
///
/// Returns [`ResearchManifestError`] if reading or parsing fails.
pub fn load_research_manifest(path: impl AsRef<Path>) -> Result<ResearchManifest> {
    ResearchManifest::load(path)
}

/// Save a manifest to `path` after validating it.
///
/// # Errors
///
/// Returns [`ResearchManifestError`] if validation, serialization, or writing
/// fails.
pub fn save_research_manifest(manifest: &ResearchManifest, path: impl AsRef<Path>) -> Result<()> {
    manifest.save(path)
}

/// Validate a manifest.
///
/// # Errors
///
/// Returns [`ResearchManifestError`] if structural validation fails.
pub fn validate_research_manifest(manifest: &ResearchManifest) -> Result<()> {
    manifest.validate()
}

fn validate_required_field(item_id: &str, value: &str, field: &'static str) -> Result<()> {
    if value.trim().is_empty() {
        return Err(ResearchManifestError::EmptyItemField {
            item_id: item_id.to_string(),
            field,
        });
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    fn seed_manifest_path() -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("..")
            .join("..")
            .join(DEFAULT_RESEARCH_MANIFEST_PATH)
    }

    #[test]
    fn seed_manifest_validates() {
        let manifest =
            ResearchManifest::load(seed_manifest_path()).expect("seed manifest should load");

        manifest.validate().expect("seed manifest should validate");

        for id in ["C004", "C006", "T60", "C010", "S40", "S51", "GF01", "GF03"] {
            assert!(manifest.item(id).is_some(), "{id} should be seeded");
        }
        assert_eq!(
            manifest
                .item("GC_CERT_ENTAILMENT")
                .map(|item| item.owner_repo.as_str()),
            Some("alabsystems/gamma-crown")
        );
        assert_eq!(
            manifest
                .item("AY_DRAT_IMPORT")
                .map(|item| item.artifact_state),
            Some(ResearchArtifactState::Replayable)
        );
        assert_eq!(
            manifest.item("T60").map(|item| item.promotion_gate),
            Some(PromotionGate::TrustReportAgreement)
        );
    }

    #[test]
    fn c004_c006_t60_are_not_kernel_proved() {
        let manifest =
            ResearchManifest::load(seed_manifest_path()).expect("seed manifest should load");

        for id in ["C004", "C006", "T60"] {
            assert!(
                !manifest.is_kernel_proved(id),
                "{id} must not be marked KernelProved"
            );
        }
    }

    #[test]
    fn validation_rejects_duplicate_ids() {
        let mut manifest = minimal_manifest();
        manifest.items.push(manifest.items[0].clone());

        let err = manifest.validate().expect_err("duplicate id should fail");
        assert!(matches!(
            err,
            ResearchManifestError::DuplicateItemId { ref id } if id == "A"
        ));
    }

    #[test]
    fn validation_rejects_unknown_dependencies() {
        let mut manifest = minimal_manifest();
        manifest.items[0]
            .dependencies
            .push(ResearchDependency::new("missing", "required by test"));

        let err = manifest
            .validate()
            .expect_err("unknown dependency should fail");
        assert!(matches!(
            err,
            ResearchManifestError::UnknownDependency {
                ref item_id,
                ref dependency_id,
            } if item_id == "A" && dependency_id == "missing"
        ));
    }

    #[test]
    fn status_serializes_as_declared_variant_name() {
        let json = serde_json::to_string(&ResearchStatus::KernelProved).expect("status serializes");
        assert_eq!(json, "\"KernelProved\"");
    }

    #[test]
    fn status_change_diff_reports_added_removed_and_changed_rows() {
        let previous = ResearchManifest {
            schema_version: RESEARCH_MANIFEST_SCHEMA_VERSION,
            generated_at: "2026-04-22".to_string(),
            source: "previous".to_string(),
            items: vec![
                ResearchManifestItem::new(
                    "A",
                    "A title",
                    "test-domain",
                    "test-family",
                    ResearchStatus::DerivedPending,
                    "A summary",
                ),
                ResearchManifestItem::new(
                    "B",
                    "B title",
                    "test-domain",
                    "test-family",
                    ResearchStatus::Axiomatized,
                    "B summary",
                ),
            ],
        };
        let current = ResearchManifest {
            schema_version: RESEARCH_MANIFEST_SCHEMA_VERSION,
            generated_at: "2026-04-23".to_string(),
            source: "current".to_string(),
            items: vec![
                ResearchManifestItem::new(
                    "A",
                    "A title",
                    "test-domain",
                    "test-family",
                    ResearchStatus::KernelProved,
                    "A summary",
                ),
                ResearchManifestItem::new(
                    "C",
                    "C title",
                    "test-domain",
                    "test-family",
                    ResearchStatus::ExecutableChecked,
                    "C summary",
                ),
            ],
        };

        assert_eq!(
            current.status_changes_from(&previous),
            vec![
                ResearchStatusChange {
                    id: "A".to_string(),
                    previous_status: Some(ResearchStatus::DerivedPending),
                    current_status: Some(ResearchStatus::KernelProved),
                },
                ResearchStatusChange {
                    id: "B".to_string(),
                    previous_status: Some(ResearchStatus::Axiomatized),
                    current_status: None,
                },
                ResearchStatusChange {
                    id: "C".to_string(),
                    previous_status: None,
                    current_status: Some(ResearchStatus::ExecutableChecked),
                },
            ]
        );
    }

    #[test]
    fn validation_rejects_empty_owner_repo() {
        let mut manifest = minimal_manifest();
        manifest.items[0].owner_repo.clear();

        let err = manifest
            .validate()
            .expect_err("empty owner_repo should fail validation");
        assert!(matches!(
            err,
            ResearchManifestError::EmptyItemField {
                ref item_id,
                field: "owner_repo",
            } if item_id == "A"
        ));
    }

    fn minimal_manifest() -> ResearchManifest {
        ResearchManifest {
            schema_version: RESEARCH_MANIFEST_SCHEMA_VERSION,
            generated_at: "2026-04-23".to_string(),
            source: "test".to_string(),
            items: vec![ResearchManifestItem::new(
                "A",
                "A title",
                "test-domain",
                "test-family",
                ResearchStatus::DerivedPending,
                "A summary",
            )],
        }
    }
}
