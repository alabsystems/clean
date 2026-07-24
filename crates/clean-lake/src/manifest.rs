// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lake manifest parsing (lake-manifest.json)

use crate::error::{LakeError, LakeResult};
use serde::{Deserialize, Serialize};
use std::path::Path;

/// Lake manifest loaded from lake-manifest.json
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct LakeManifest {
    /// Manifest version. Lake has historically used a small unsigned integer
    /// (e.g. `7`), but real Lean 4 / Mathlib4 manifests now ship a semver
    /// string (e.g. `"1.2.0"`). Accept both so we can parse upstream
    /// manifests without losing precision.
    pub version: LakeManifestVersion,
    /// Packages directory (relative to project root)
    #[serde(rename = "packagesDir")]
    pub packages_dir: String,
    /// List of packages
    pub packages: Vec<ManifestPackage>,
}

/// Either-form manifest version field.
///
/// Lake originally serialized the manifest schema version as a small
/// unsigned integer; recent Lake releases emit a semver string. The
/// untagged enum lets serde dispatch on the JSON shape transparently.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(untagged)]
pub enum LakeManifestVersion {
    /// Legacy numeric schema version (e.g. `7`).
    Numeric(u32),
    /// Modern string schema version (e.g. `"1.2.0"`).
    String(String),
}

impl Default for LakeManifestVersion {
    fn default() -> Self {
        // Match the legacy default written by `LakeManifest::empty`.
        Self::Numeric(7)
    }
}

impl LakeManifestVersion {
    /// Return the numeric form if this version is encoded as an integer.
    #[must_use]
    pub fn as_numeric(&self) -> Option<u32> {
        match self {
            Self::Numeric(n) => Some(*n),
            Self::String(_) => None,
        }
    }

    /// Return the string form if this version is encoded as a string.
    #[must_use]
    pub fn as_str(&self) -> Option<&str> {
        match self {
            Self::String(s) => Some(s.as_str()),
            Self::Numeric(_) => None,
        }
    }
}

impl std::fmt::Display for LakeManifestVersion {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Numeric(n) => write!(f, "{n}"),
            Self::String(s) => f.write_str(s),
        }
    }
}

impl From<u32> for LakeManifestVersion {
    fn from(value: u32) -> Self {
        Self::Numeric(value)
    }
}

impl From<String> for LakeManifestVersion {
    fn from(value: String) -> Self {
        Self::String(value)
    }
}

impl From<&str> for LakeManifestVersion {
    fn from(value: &str) -> Self {
        Self::String(value.to_string())
    }
}

/// A package entry in the manifest
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(untagged)]
pub enum ManifestPackage {
    /// Git-based package
    Git(GitPackage),
    /// Path-based package
    Path(PathPackage),
}

/// Git-based package in manifest
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct GitPackage {
    /// Package name
    pub name: String,
    /// Git URL
    pub url: String,
    /// Git revision (commit SHA, tag, or branch)
    pub rev: String,
    /// Input revision (user-specified, e.g., "main")
    #[serde(rename = "inputRev")]
    pub input_rev: Option<String>,
    /// Subdirectory containing the package (Lake JSON key: `subDir`).
    /// Previously this field was read as `subdir` and silently dropped, since
    /// Lake serializes it camelCased as `subDir`.
    #[serde(rename = "subDir", default, skip_serializing_if = "Option::is_none")]
    pub subdir: Option<String>,
    /// Dependency scope (Lake JSON key: `scope`, e.g. "leanprover-community").
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub scope: Option<String>,
    /// Whether this dependency was transitively inherited from another package
    /// (Lake JSON key: `inherited`).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub inherited: Option<bool>,
    /// Config file that declared this package (Lake JSON key: `configFile`),
    /// e.g. "lakefile.lean" vs "lakefile.toml".
    #[serde(
        rename = "configFile",
        default,
        skip_serializing_if = "Option::is_none"
    )]
    pub config_file: Option<String>,
    /// Manifest file path for this package (Lake JSON key: `manifestFile`).
    #[serde(
        rename = "manifestFile",
        default,
        skip_serializing_if = "Option::is_none"
    )]
    pub manifest_file: Option<String>,
    /// Package kind tag emitted by Lake (JSON key: `type`, e.g. "git").
    #[serde(rename = "type", default, skip_serializing_if = "Option::is_none")]
    pub package_type: Option<String>,
}

/// Path-based package in manifest
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct PathPackage {
    /// Package name
    pub name: String,
    /// Path to the package (Lake JSON key: `dir`; legacy key `path` also accepted).
    #[serde(alias = "dir")]
    pub path: String,
    /// Dependency scope (Lake JSON key: `scope`).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub scope: Option<String>,
    /// Whether this dependency was transitively inherited (Lake key: `inherited`).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub inherited: Option<bool>,
    /// Config file that declared this package (Lake JSON key: `configFile`).
    #[serde(
        rename = "configFile",
        default,
        skip_serializing_if = "Option::is_none"
    )]
    pub config_file: Option<String>,
    /// Manifest file path for this package (Lake JSON key: `manifestFile`).
    #[serde(
        rename = "manifestFile",
        default,
        skip_serializing_if = "Option::is_none"
    )]
    pub manifest_file: Option<String>,
    /// Package kind tag emitted by Lake (JSON key: `type`, e.g. "path").
    #[serde(rename = "type", default, skip_serializing_if = "Option::is_none")]
    pub package_type: Option<String>,
}

impl LakeManifest {
    /// Load manifest from a lake-manifest.json file
    pub fn load(manifest_path: &Path) -> LakeResult<Self> {
        let content = std::fs::read_to_string(manifest_path)?;
        Self::parse(&content)
    }

    /// Parse lake-manifest.json content
    pub fn parse(content: &str) -> LakeResult<Self> {
        serde_json::from_str(content).map_err(|e| LakeError::ManifestParse(e.to_string()))
    }

    /// Save manifest to a file
    pub fn save(&self, manifest_path: &Path) -> LakeResult<()> {
        let content = serde_json::to_string_pretty(self)?;
        std::fs::write(manifest_path, content)?;
        Ok(())
    }

    /// Get a package by name
    #[must_use]
    pub fn get_package(&self, name: &str) -> Option<&ManifestPackage> {
        self.packages.iter().find(|p| p.name() == name)
    }

    /// Add or update a package
    pub fn upsert_package(&mut self, package: ManifestPackage) {
        let name = package.name().to_string();
        if let Some(existing) = self.packages.iter_mut().find(|p| p.name() == name) {
            *existing = package;
        } else {
            self.packages.push(package);
        }
    }

    /// Create an empty manifest
    #[must_use]
    pub fn empty() -> Self {
        Self {
            // Current Lake manifest version (legacy numeric form).
            version: LakeManifestVersion::Numeric(7),
            packages_dir: ".lake/packages".to_string(),
            packages: Vec::new(),
        }
    }
}

impl ManifestPackage {
    /// Get the package name
    #[must_use]
    pub fn name(&self) -> &str {
        match self {
            ManifestPackage::Git(g) => &g.name,
            ManifestPackage::Path(p) => &p.name,
        }
    }

    /// Check if this is a git package
    #[must_use]
    pub fn is_git(&self) -> bool {
        matches!(self, ManifestPackage::Git(_))
    }

    /// Check if this is a path package
    #[must_use]
    pub fn is_path(&self) -> bool {
        matches!(self, ManifestPackage::Path(_))
    }

    /// Get as git package
    #[must_use]
    pub fn as_git(&self) -> Option<&GitPackage> {
        match self {
            ManifestPackage::Git(g) => Some(g),
            _ => None,
        }
    }

    /// Get as path package
    #[must_use]
    pub fn as_path(&self) -> Option<&PathPackage> {
        match self {
            ManifestPackage::Path(p) => Some(p),
            _ => None,
        }
    }
}

impl GitPackage {
    /// Create a new git package
    #[must_use]
    pub fn new(name: &str, url: &str, rev: &str) -> Self {
        Self {
            name: name.to_string(),
            url: url.to_string(),
            rev: rev.to_string(),
            ..Default::default()
        }
    }
}

impl PathPackage {
    /// Create a new path package
    #[must_use]
    pub fn new(name: &str, path: &str) -> Self {
        Self {
            name: name.to_string(),
            path: path.to_string(),
            ..Default::default()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_empty_manifest() {
        let content = r#"{
            "version": 7,
            "packagesDir": ".lake/packages",
            "packages": []
        }"#;
        let manifest = LakeManifest::parse(content).unwrap();
        assert_eq!(manifest.version, LakeManifestVersion::Numeric(7));
        assert_eq!(manifest.version.as_numeric(), Some(7));
        assert_eq!(manifest.packages_dir, ".lake/packages");
        assert!(manifest.packages.is_empty());
    }

    #[test]
    fn test_parse_manifest_with_git_package() {
        let content = r#"{
            "version": 7,
            "packagesDir": ".lake/packages",
            "packages": [
                {
                    "name": "std",
                    "url": "https://github.com/leanprover/std4",
                    "rev": "abc123"
                }
            ]
        }"#;
        let manifest = LakeManifest::parse(content).unwrap();
        assert_eq!(manifest.packages.len(), 1);
        let pkg = &manifest.packages[0];
        assert_eq!(pkg.name(), "std");
        assert!(pkg.is_git());
        let git = pkg.as_git().unwrap();
        assert_eq!(git.url, "https://github.com/leanprover/std4");
        assert_eq!(git.rev, "abc123");
    }

    #[test]
    fn test_parse_manifest_with_path_package() {
        let content = r#"{
            "version": 7,
            "packagesDir": ".lake/packages",
            "packages": [
                {
                    "name": "local",
                    "path": "../local-pkg"
                }
            ]
        }"#;
        let manifest = LakeManifest::parse(content).unwrap();
        assert_eq!(manifest.packages.len(), 1);
        let pkg = &manifest.packages[0];
        assert_eq!(pkg.name(), "local");
        assert!(pkg.is_path());
        let path = pkg.as_path().unwrap();
        assert_eq!(path.path, "../local-pkg");
    }

    #[test]
    fn test_manifest_get_package() {
        let mut manifest = LakeManifest::empty();
        manifest.packages.push(ManifestPackage::Git(GitPackage::new(
            "test",
            "https://example.com/test",
            "main",
        )));

        assert!(
            manifest.get_package("test").is_some(),
            "should find 'test' package"
        );
        assert!(
            manifest.get_package("nonexistent").is_none(),
            "'nonexistent' should not be found"
        );
    }

    #[test]
    fn test_manifest_upsert_package() {
        let mut manifest = LakeManifest::empty();

        // Add new package
        manifest.upsert_package(ManifestPackage::Git(GitPackage::new(
            "test",
            "https://example.com/test",
            "v1",
        )));
        assert_eq!(manifest.packages.len(), 1);

        // Update existing package
        manifest.upsert_package(ManifestPackage::Git(GitPackage::new(
            "test",
            "https://example.com/test",
            "v2",
        )));
        assert_eq!(manifest.packages.len(), 1);
        let git = manifest.get_package("test").unwrap().as_git().unwrap();
        assert_eq!(git.rev, "v2");
    }

    #[test]
    fn test_manifest_roundtrip() {
        let manifest = LakeManifest {
            version: LakeManifestVersion::Numeric(7),
            packages_dir: ".lake/packages".to_string(),
            packages: vec![ManifestPackage::Git(GitPackage::new(
                "std",
                "https://github.com/leanprover/std4",
                "abc123",
            ))],
        };

        let json = serde_json::to_string(&manifest).unwrap();
        let parsed: LakeManifest = serde_json::from_str(&json).unwrap();

        assert_eq!(parsed.version, manifest.version);
        assert_eq!(parsed.packages.len(), 1);
    }

    /// Regression test for the audit finding: real Lean 4 / Mathlib4
    /// `lake-manifest.json` files ship `"version": "1.2.0"` as a string.
    /// The legacy `u32`-only schema silently dropped the manifest because
    /// the loader's `.ok()` swallowed the parse error. The untagged
    /// `LakeManifestVersion` enum must now accept both forms.
    #[test]
    fn test_parse_string_form_version() {
        let content = r#"{
            "version": "1.2.0",
            "packagesDir": ".lake/packages",
            "packages": []
        }"#;
        let manifest = LakeManifest::parse(content).expect("string-form version must parse");
        assert_eq!(
            manifest.version,
            LakeManifestVersion::String("1.2.0".to_string())
        );
        assert_eq!(manifest.version.as_str(), Some("1.2.0"));
        assert_eq!(manifest.version.as_numeric(), None);
    }

    /// Companion regression test: legacy numeric-form manifests must keep
    /// working after the untagged-enum refactor.
    #[test]
    fn test_parse_numeric_form_version() {
        let content = r#"{
            "version": 7,
            "packagesDir": ".lake/packages",
            "packages": []
        }"#;
        let manifest = LakeManifest::parse(content).expect("numeric-form version must parse");
        assert_eq!(manifest.version, LakeManifestVersion::Numeric(7));
        assert_eq!(manifest.version.as_numeric(), Some(7));
        assert_eq!(manifest.version.as_str(), None);
    }

    /// Fixture-driven regression test: load the actual Mathlib4-style
    /// `lake-manifest.json` checked in at `tests/fixtures/lake-manifest-v1_2_0.json`.
    /// This guards against future regressions of audit item 1.
    #[test]
    fn test_parse_real_mathlib_fixture() {
        let fixture_path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests")
            .join("fixtures")
            .join("lake-manifest-v1_2_0.json");
        let manifest = LakeManifest::load(&fixture_path).expect("real Mathlib manifest must parse");
        assert_eq!(manifest.version.as_str(), Some("1.2.0"));
        assert_eq!(manifest.packages_dir, ".lake/packages");
        assert!(
            !manifest.packages.is_empty(),
            "fixture should declare packages"
        );
        // mathlib is the first declared package in the upstream manifest.
        assert!(
            manifest.packages.iter().any(|p| p.name() == "mathlib"),
            "fixture should include the 'mathlib' package entry"
        );
    }

    /// Audit regression: real Lake git entries carry `subDir`, `scope`,
    /// `inherited`, `configFile`, `manifestFile`, and `type` fields that the
    /// previous schema silently dropped. They must now be captured and survive
    /// a serialize→parse round-trip.
    #[test]
    fn test_capture_full_git_package_fields() {
        let content = r#"{
            "version": "1.2.0",
            "packagesDir": ".lake/packages",
            "packages": [
                {
                    "url": "https://github.com/leanprover-community/plausible",
                    "type": "git",
                    "subDir": "sub",
                    "scope": "leanprover-community",
                    "rev": "293af9b2a383eed4d04d66b898d608d0a44b750f",
                    "name": "plausible",
                    "manifestFile": "lake-manifest.json",
                    "inputRev": "main",
                    "inherited": true,
                    "configFile": "lakefile.toml"
                }
            ]
        }"#;
        let manifest = LakeManifest::parse(content).expect("manifest with full fields must parse");
        let git = manifest.packages[0]
            .as_git()
            .expect("entry should be a git package");
        assert_eq!(git.subdir.as_deref(), Some("sub"));
        assert_eq!(git.scope.as_deref(), Some("leanprover-community"));
        assert_eq!(git.inherited, Some(true));
        assert_eq!(git.config_file.as_deref(), Some("lakefile.toml"));
        assert_eq!(git.manifest_file.as_deref(), Some("lake-manifest.json"));
        assert_eq!(git.package_type.as_deref(), Some("git"));
        assert_eq!(git.input_rev.as_deref(), Some("main"));

        // Round-trip must preserve every captured field.
        let json = serde_json::to_string(&manifest).expect("serialize");
        let reparsed = LakeManifest::parse(&json).expect("reparse");
        let git2 = reparsed.packages[0].as_git().expect("git after round-trip");
        assert_eq!(git2.subdir.as_deref(), Some("sub"));
        assert_eq!(git2.scope.as_deref(), Some("leanprover-community"));
        assert_eq!(git2.inherited, Some(true));
        assert_eq!(git2.config_file.as_deref(), Some("lakefile.toml"));
        assert_eq!(git2.manifest_file.as_deref(), Some("lake-manifest.json"));
        assert_eq!(git2.package_type.as_deref(), Some("git"));
    }

    /// Real Lake path entries use the `dir` key (not `path`) and carry the
    /// same metadata fields; ensure both the alias and the metadata parse.
    #[test]
    fn test_capture_path_package_dir_alias_and_fields() {
        let content = r#"{
            "version": "1.2.0",
            "packagesDir": ".lake/packages",
            "packages": [
                {
                    "type": "path",
                    "name": "localdep",
                    "manifestFile": "lake-manifest.json",
                    "inherited": false,
                    "configFile": "lakefile.lean",
                    "dir": "../localdep"
                }
            ]
        }"#;
        let manifest = LakeManifest::parse(content).expect("path manifest must parse");
        let p = manifest.packages[0]
            .as_path()
            .expect("entry should be a path package");
        assert_eq!(p.path, "../localdep", "dir alias maps to path");
        assert_eq!(p.inherited, Some(false));
        assert_eq!(p.config_file.as_deref(), Some("lakefile.lean"));
        assert_eq!(p.package_type.as_deref(), Some("path"));
    }
}
