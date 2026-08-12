// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Local ingest policy for untrusted MathMap bundles.
//!
//! The policy is the operator-controlled half of the ingest contract: it says
//! which schema versions, services, target kinds, imports, sizes and bundle
//! ages are acceptable, and whether a real cryptographic signature is
//! mandatory. The shipped [`DEFAULT_POLICY_TOML`](super::DEFAULT_POLICY_TOML)
//! requires one.

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use serde::{Deserialize, Serialize};

use super::manifest::BundleManifest;
use super::DEFAULT_POLICY_TOML;

/// Operator-controlled ingest policy.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct MathMapPolicy {
    /// Policy file contract version.
    pub schema_version: String,
    /// Manifest `schema_version` allowlist; empty means "any".
    #[serde(default)]
    pub allowed_schema_versions: Vec<String>,
    /// Producing-service allowlist; empty means "any".
    #[serde(default)]
    pub allowed_services: Vec<String>,
    /// Target-kind allowlist; empty means "any not denied".
    #[serde(default)]
    pub allowed_target_kinds: Vec<String>,
    /// Target-kind denylist, checked before the allowlist.
    #[serde(default)]
    pub denied_target_kinds: Vec<String>,
    /// Lean import prefixes a patch may not add.
    #[serde(default)]
    pub denied_imports: Vec<String>,
    /// Maximum decoded bundle size.
    #[serde(default = "default_max_bundle_bytes")]
    pub max_bundle_bytes: u64,
    /// Maximum bundle age; `Some` also makes `issued_at` mandatory.
    #[serde(default = "default_max_bundle_age_days")]
    pub max_bundle_age_days: Option<u64>,
    /// Require a `signatures/manifest.sig` entry.
    #[serde(default = "default_true")]
    pub require_signature: bool,
    /// Require the verified signature to name a registered active trusted key.
    #[serde(default = "default_true")]
    pub require_registered_signature: bool,
    /// Require the signature to have been verified cryptographically.
    ///
    /// Defaults to `false` for backward-compatible local policy files, but the
    /// shipped production policy sets it to `true`.
    #[serde(default)]
    pub require_cryptographic_signature: bool,
    /// Require every manifest patch hash to match the bundled patch bytes.
    #[serde(default = "default_true")]
    pub require_patch_hashes: bool,
}

/// Failure while loading a policy file.
#[derive(Debug, thiserror::Error)]
pub enum PolicyLoadError {
    /// Filesystem failure.
    #[error("failed to read MathMap policy at {path}: {source}")]
    Io {
        /// Policy path.
        path: PathBuf,
        /// Underlying error.
        #[source]
        source: std::io::Error,
    },
    /// TOML decode failure.
    #[error("failed to parse MathMap policy TOML at {path}: {source}")]
    Toml {
        /// Policy path.
        path: PathBuf,
        /// Underlying error.
        #[source]
        source: toml::de::Error,
    },
}

/// A policy rule the untrusted manifest violated.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PolicyViolation {
    /// `schema_version` is not in the allowlist.
    SchemaVersionDenied {
        /// Rejected schema version.
        schema_version: String,
    },
    /// `service` is not in the allowlist.
    ServiceDenied {
        /// Rejected service.
        service: String,
    },
    /// A target kind is explicitly denied.
    TargetKindDenied {
        /// Rejected kind.
        kind: String,
    },
    /// A target kind is not in the allowlist.
    TargetKindNotAllowed {
        /// Rejected kind.
        kind: String,
    },
    /// A patch adds a denied import.
    ImportDenied {
        /// Rejected import.
        import: String,
    },
    /// A bundle-age policy is set but `issued_at` is absent.
    MissingIssuedAt,
    /// `issued_at` is not RFC3339.
    MalformedIssuedAt {
        /// Rejected timestamp.
        issued_at: String,
    },
    /// `issued_at` is beyond the accepted clock skew.
    FutureIssuedAt {
        /// Rejected timestamp.
        issued_at: String,
    },
    /// The bundle is older than the policy allows.
    StaleBundle {
        /// Bundle timestamp.
        issued_at: String,
        /// Policy limit.
        max_age_days: u64,
    },
    /// The signature was accepted, but not cryptographically.
    NonCryptographicSignature {
        /// Producing service.
        service: String,
    },
}

impl std::fmt::Display for PolicyViolation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::SchemaVersionDenied { schema_version } => {
                write!(f, "schema version `{schema_version}` is not allowed")
            }
            Self::ServiceDenied { service } => write!(f, "service `{service}` is not allowed"),
            Self::TargetKindDenied { kind } => write!(f, "target kind `{kind}` is denied"),
            Self::TargetKindNotAllowed { kind } => {
                write!(f, "target kind `{kind}` is not in the allowlist")
            }
            Self::ImportDenied { import } => write!(f, "import `{import}` is denied"),
            Self::MissingIssuedAt => write!(f, "manifest `issued_at` is required"),
            Self::MalformedIssuedAt { issued_at } => {
                write!(
                    f,
                    "manifest `issued_at` is not valid RFC3339 UTC time: `{issued_at}`"
                )
            }
            Self::FutureIssuedAt { issued_at } => {
                write!(
                    f,
                    "manifest `issued_at` `{issued_at}` is too far in the future"
                )
            }
            Self::StaleBundle {
                issued_at,
                max_age_days,
            } => write!(
                f,
                "manifest `issued_at` `{issued_at}` is older than policy max age of {max_age_days} days"
            ),
            Self::NonCryptographicSignature { service } => write!(
                f,
                "service `{service}` signature was not cryptographically verified"
            ),
        }
    }
}

impl std::error::Error for PolicyViolation {}

impl MathMapPolicy {
    /// The policy compiled into the binary.
    ///
    /// # Panics
    ///
    /// Panics if the bundled `policy.toml` does not parse, which is a build-time
    /// invariant violation rather than a runtime condition.
    #[must_use]
    pub fn builtin() -> Self {
        Self::from_toml_str(DEFAULT_POLICY_TOML).expect("bundled MathMap policy must parse")
    }

    /// Load a policy from a TOML file.
    pub fn load(path: impl AsRef<Path>) -> Result<Self, PolicyLoadError> {
        let path = path.as_ref();
        let text = fs::read_to_string(path).map_err(|source| PolicyLoadError::Io {
            path: path.to_owned(),
            source,
        })?;
        toml::from_str(&text).map_err(|source| PolicyLoadError::Toml {
            path: path.to_owned(),
            source,
        })
    }

    /// Parse a policy from TOML text.
    pub fn from_toml_str(text: &str) -> Result<Self, toml::de::Error> {
        toml::from_str(text)
    }

    /// Validate an untrusted manifest against this policy, using the wall clock.
    pub fn validate_manifest(&self, manifest: &BundleManifest) -> Result<(), PolicyViolation> {
        self.validate_manifest_at(manifest, SystemTime::now())
    }

    /// Validate an untrusted manifest against this policy at a fixed instant.
    pub fn validate_manifest_at(
        &self,
        manifest: &BundleManifest,
        now: SystemTime,
    ) -> Result<(), PolicyViolation> {
        if let Some(schema_version) = manifest.schema_version.as_deref() {
            if !self.allowed_schema_versions.is_empty()
                && !self
                    .allowed_schema_versions
                    .iter()
                    .any(|allowed| allowed == schema_version)
            {
                return Err(PolicyViolation::SchemaVersionDenied {
                    schema_version: schema_version.to_owned(),
                });
            }
        }

        if let Some(service) = manifest.service() {
            if !self.allowed_services.is_empty()
                && !self
                    .allowed_services
                    .iter()
                    .any(|allowed| allowed == service)
            {
                return Err(PolicyViolation::ServiceDenied {
                    service: service.to_owned(),
                });
            }
        }

        if let Some(max_age_days) = self.max_bundle_age_days {
            let issued_at = manifest
                .issued_at
                .as_deref()
                .map(str::trim)
                .filter(|value| !value.is_empty())
                .ok_or(PolicyViolation::MissingIssuedAt)?;
            let issued_at_epoch = parse_rfc3339_epoch_seconds(issued_at).ok_or_else(|| {
                PolicyViolation::MalformedIssuedAt {
                    issued_at: issued_at.to_owned(),
                }
            })?;
            let now_epoch = now
                .duration_since(UNIX_EPOCH)
                .unwrap_or(Duration::ZERO)
                .as_secs() as i64;
            let max_age_seconds = max_age_days.saturating_mul(24 * 60 * 60) as i64;
            if issued_at_epoch > now_epoch.saturating_add(MAX_ISSUED_AT_FUTURE_SKEW_SECONDS) {
                return Err(PolicyViolation::FutureIssuedAt {
                    issued_at: issued_at.to_owned(),
                });
            }
            if now_epoch.saturating_sub(issued_at_epoch) > max_age_seconds {
                return Err(PolicyViolation::StaleBundle {
                    issued_at: issued_at.to_owned(),
                    max_age_days,
                });
            }
        }

        let denied: BTreeSet<&str> = self
            .denied_target_kinds
            .iter()
            .map(String::as_str)
            .collect();
        let allowed: BTreeSet<&str> = self
            .allowed_target_kinds
            .iter()
            .map(String::as_str)
            .collect();

        for target in &manifest.targets {
            let Some(kind) = target.kind.as_deref() else {
                continue;
            };
            if denied.contains(kind) {
                return Err(PolicyViolation::TargetKindDenied {
                    kind: kind.to_owned(),
                });
            }
            if !allowed.is_empty() && !allowed.contains(kind) {
                return Err(PolicyViolation::TargetKindNotAllowed {
                    kind: kind.to_owned(),
                });
            }
        }

        Ok(())
    }

    /// Reject any patch that adds a denied Lean import.
    pub fn validate_patch_imports<'a, I>(&self, patch_texts: I) -> Result<(), PolicyViolation>
    where
        I: IntoIterator<Item = &'a str>,
    {
        if self.denied_imports.is_empty() {
            return Ok(());
        }
        for patch_text in patch_texts {
            for import in added_imports(patch_text) {
                if self.import_is_denied(&import) {
                    return Err(PolicyViolation::ImportDenied { import });
                }
            }
        }
        Ok(())
    }

    /// Whether `import` is denied, matching the import itself or any descendant.
    #[must_use]
    pub fn import_is_denied(&self, import: &str) -> bool {
        self.denied_imports
            .iter()
            .any(|denied| import == denied || import.starts_with(&format!("{denied}.")))
    }
}

/// Lean imports introduced by added (`+`) lines of a unified diff.
#[must_use]
pub fn added_imports(patch_text: &str) -> Vec<String> {
    let mut imports = Vec::new();
    for line in patch_text.lines() {
        if line.starts_with("+++") || !line.starts_with('+') {
            continue;
        }
        let added = line[1..].trim_start();
        let Some(rest) = added.strip_prefix("import ") else {
            continue;
        };
        for item in rest.split_whitespace() {
            if item.starts_with("--") {
                break;
            }
            imports.push(item.trim().to_owned());
        }
    }
    imports
}

const fn default_true() -> bool {
    true
}

const fn default_max_bundle_bytes() -> u64 {
    100 * 1024 * 1024
}

const fn default_max_bundle_age_days() -> Option<u64> {
    Some(30)
}

const MAX_ISSUED_AT_FUTURE_SKEW_SECONDS: i64 = 5 * 60;

fn parse_rfc3339_epoch_seconds(value: &str) -> Option<i64> {
    let bytes = value.as_bytes();
    if bytes.len() < 20
        || bytes.get(4) != Some(&b'-')
        || bytes.get(7) != Some(&b'-')
        || !matches!(bytes.get(10), Some(b'T' | b't'))
        || bytes.get(13) != Some(&b':')
        || bytes.get(16) != Some(&b':')
    {
        return None;
    }

    let year = parse_fixed_digits(value, 0, 4)? as i64;
    let month = parse_fixed_digits(value, 5, 7)? as i64;
    let day = parse_fixed_digits(value, 8, 10)? as i64;
    let hour = parse_fixed_digits(value, 11, 13)? as i64;
    let minute = parse_fixed_digits(value, 14, 16)? as i64;
    let second = parse_fixed_digits(value, 17, 19)? as i64;

    if !(1..=12).contains(&month)
        || day < 1
        || day > days_in_month(year, month)
        || hour > 23
        || minute > 59
        || second > 59
    {
        return None;
    }

    let mut index = 19;
    if bytes.get(index) == Some(&b'.') {
        index += 1;
        let fraction_start = index;
        while bytes.get(index).is_some_and(u8::is_ascii_digit) {
            index += 1;
        }
        if index == fraction_start {
            return None;
        }
    }

    let offset_seconds = match bytes.get(index) {
        Some(b'Z' | b'z') if index + 1 == bytes.len() => 0,
        Some(sign @ (b'+' | b'-')) if index + 6 == bytes.len() => {
            if bytes.get(index + 3) != Some(&b':') {
                return None;
            }
            let offset_hour = parse_fixed_digits(value, index + 1, index + 3)? as i64;
            let offset_minute = parse_fixed_digits(value, index + 4, index + 6)? as i64;
            if offset_hour > 23 || offset_minute > 59 {
                return None;
            }
            let offset = offset_hour * 60 * 60 + offset_minute * 60;
            if *sign == b'+' {
                offset
            } else {
                -offset
            }
        }
        _ => return None,
    };

    let days = days_from_civil(year, month, day);
    Some(days * 24 * 60 * 60 + hour * 60 * 60 + minute * 60 + second - offset_seconds)
}

fn parse_fixed_digits(value: &str, start: usize, end: usize) -> Option<u32> {
    let slice = value.get(start..end)?;
    if !slice.as_bytes().iter().all(u8::is_ascii_digit) {
        return None;
    }
    slice.parse().ok()
}

const fn days_in_month(year: i64, month: i64) -> i64 {
    match month {
        1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
        4 | 6 | 9 | 11 => 30,
        2 if is_leap_year(year) => 29,
        2 => 28,
        _ => 0,
    }
}

const fn is_leap_year(year: i64) -> bool {
    (year % 4 == 0 && year % 100 != 0) || year % 400 == 0
}

fn days_from_civil(mut year: i64, month: i64, day: i64) -> i64 {
    year -= i64::from(month <= 2);
    let era = if year >= 0 { year } else { year - 399 } / 400;
    let year_of_era = year - era * 400;
    let month_prime = month + if month > 2 { -3 } else { 9 };
    let day_of_year = (153 * month_prime + 2) / 5 + day - 1;
    let day_of_era = year_of_era * 365 + year_of_era / 4 - year_of_era / 100 + day_of_year;
    era * 146_097 + day_of_era - 719_468
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_builtin_policy_requires_cryptographic_signatures() {
        let policy = MathMapPolicy::builtin();

        assert!(policy.require_cryptographic_signature);
        assert!(policy.require_signature);
        assert!(policy.require_registered_signature);
    }

    #[test]
    fn test_cryptographic_signature_requirement_defaults_to_false() {
        let policy = MathMapPolicy::from_toml_str(
            r#"
schema_version = "clean-math_map-policy-v1"
allowed_schema_versions = ["1.0.0"]
allowed_services = ["math_map"]
"#,
        )
        .expect("minimal policy parses");

        assert!(!policy.require_cryptographic_signature);
    }
}
