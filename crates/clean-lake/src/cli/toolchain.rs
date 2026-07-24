// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! lean-toolchain parsing and version resolution helpers.

use std::path::Path;

use semver::Version;

use crate::error::{LakeError, LakeResult};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct LoadedToolchain {
    pub(crate) identifier: String,
    pub(crate) resolved_version: Option<String>,
}

pub(crate) fn load_toolchain(root: &Path) -> LakeResult<Option<LoadedToolchain>> {
    let path = root.join("lean-toolchain");
    if !path.exists() {
        return Ok(None);
    }

    let content = std::fs::read_to_string(&path)?;
    let identifier = parse_toolchain_identifier(&content, &path.display().to_string())?;
    let available = clean_olean::default_toolchain_versions();

    Ok(Some(LoadedToolchain {
        resolved_version: resolve_toolchain_version(&identifier, &available),
        identifier,
    }))
}

fn parse_toolchain_identifier(content: &str, path_display: &str) -> LakeResult<String> {
    let mut identifier = None;

    for raw_line in content.lines() {
        let trimmed = raw_line.trim_start_matches('\u{feff}').trim();
        if trimmed.is_empty() || trimmed.starts_with("--") || trimmed.starts_with('#') {
            continue;
        }

        if trimmed.split_whitespace().count() != 1 {
            return Err(LakeError::InvalidConfig(format!(
                "lean-toolchain in {path_display} must contain a single toolchain identifier"
            )));
        }

        if identifier.replace(trimmed.to_string()).is_some() {
            return Err(LakeError::InvalidConfig(format!(
                "lean-toolchain in {path_display} must contain a single toolchain identifier"
            )));
        }
    }

    identifier.ok_or_else(|| {
        LakeError::InvalidConfig(format!("lean-toolchain in {path_display} is empty"))
    })
}

pub(crate) fn resolve_toolchain_version(
    identifier: &str,
    available_versions: &[String],
) -> Option<String> {
    let (owner, requested) = split_toolchain_identifier(identifier);

    if looks_like_release_version(requested) {
        if owner_is_clean(owner) && version_looks_like_lean4(requested) {
            return None;
        }
        return Some(requested.to_string());
    }

    match requested {
        "stable" => compatible_toolchain_versions(owner, available_versions)
            .find(|version| is_stable_release(version))
            .cloned(),
        "nightly" => compatible_toolchain_versions(owner, available_versions)
            .find(|version| version.starts_with("nightly"))
            .cloned(),
        _ => compatible_toolchain_versions(owner, available_versions)
            .find(|version| *version == requested)
            .cloned(),
    }
}

fn split_toolchain_identifier(identifier: &str) -> (Option<&str>, &str) {
    identifier
        .rsplit_once(':')
        .map_or((None, identifier.trim()), |(owner, version)| {
            (Some(owner.trim()), version.trim())
        })
}

fn compatible_toolchain_versions<'a>(
    owner: Option<&str>,
    available_versions: &'a [String],
) -> impl Iterator<Item = &'a String> {
    let clean_owner = owner_is_clean(owner);
    available_versions
        .iter()
        .filter(move |version| !clean_owner || !version_looks_like_lean4(version))
}

fn owner_is_clean(owner: Option<&str>) -> bool {
    owner.is_some_and(|owner| owner == "clean" || owner.ends_with("/clean"))
}

fn version_looks_like_lean4(version: &str) -> bool {
    version.trim_start_matches('v').starts_with("4.") || version.starts_with("nightly")
}

fn parse_semver(version: &str) -> Option<Version> {
    Version::parse(version.trim_start_matches('v')).ok()
}

fn looks_like_release_version(version: &str) -> bool {
    parse_semver(version).is_some()
}

fn is_stable_release(version: &str) -> bool {
    parse_semver(version).is_some_and(|version| version.pre.is_empty())
}

#[cfg(test)]
mod tests {
    use super::{parse_toolchain_identifier, resolve_toolchain_version};
    use std::fs;
    use tempfile::TempDir;

    #[test]
    fn parses_identifier_while_ignoring_comments_and_blank_lines() {
        let content = "\n# comment\n-- another comment\nleanprover/lean4:v4.29.1\n";
        let parsed = parse_toolchain_identifier(content, "/tmp/lean-toolchain").unwrap();
        assert_eq!(parsed, "leanprover/lean4:v4.29.1");
    }

    #[test]
    fn rejects_multiple_non_comment_identifiers() {
        let content = "leanprover/lean4:v4.29.1\nleanprover/lean4:v4.28.0\n";
        let err = parse_toolchain_identifier(content, "/tmp/lean-toolchain").unwrap_err();
        assert!(err
            .to_string()
            .contains("must contain a single toolchain identifier"));
    }

    #[test]
    fn rejects_whitespace_after_identifier() {
        let content = "leanprover/lean4:v4.29.1 trailing\n";
        let err = parse_toolchain_identifier(content, "/tmp/lean-toolchain").unwrap_err();
        assert!(err
            .to_string()
            .contains("must contain a single toolchain identifier"));
    }

    #[test]
    fn resolves_exact_versions_without_installed_toolchain_scan() {
        let version = resolve_toolchain_version("leanprover/lean4:v4.29.1", &[]);
        assert_eq!(version.as_deref(), Some("v4.29.1"));
    }

    #[test]
    fn resolves_stable_to_first_stable_version_in_priority_order() {
        let available = vec![
            "v4.27.0".to_string(),
            "v4.30.0-rc2".to_string(),
            "v4.29.1".to_string(),
        ];
        let version = resolve_toolchain_version("leanprover/lean4:stable", &available);
        assert_eq!(version.as_deref(), Some("v4.27.0"));
    }

    #[test]
    fn resolves_clean_stable_alias_without_lean4_owner_prefix() {
        let available = vec!["v4.29.1".to_string(), "v1.1.0".to_string()];
        let version = resolve_toolchain_version("clean:stable", &available);
        assert_eq!(version.as_deref(), Some("v1.1.0"));
    }

    #[test]
    fn refuses_to_resolve_clean_aliases_to_lean4_toolchains() {
        let available = vec!["v4.29.1".to_string(), "nightly-2026-04-21".to_string()];

        assert!(resolve_toolchain_version("clean:stable", &available).is_none());
        assert!(resolve_toolchain_version("clean:nightly", &available).is_none());
        assert!(resolve_toolchain_version("clean:v4.29.1", &available).is_none());
        assert_eq!(
            resolve_toolchain_version("clean:v1.1.0", &available).as_deref(),
            Some("v1.1.0")
        );
    }

    #[test]
    fn leaves_unknown_aliases_unresolved() {
        let available = vec!["v4.29.1".to_string()];
        let version = resolve_toolchain_version("leanprover/lean4:nightly", &available);
        assert!(version.is_none());
    }

    #[test]
    fn resolves_nightly_from_active_search_path_order() {
        let available = vec![
            "v4.29.1".to_string(),
            "nightly-2026-04-21".to_string(),
            "nightly-2026-04-20".to_string(),
        ];
        let version = resolve_toolchain_version("leanprover/lean4:nightly", &available);
        assert_eq!(version.as_deref(), Some("nightly-2026-04-21"));
    }

    #[test]
    fn leaves_aliases_unresolved_when_higher_priority_stdlib_path_is_unversioned() {
        let temp = TempDir::new().expect("tempdir");
        let unversioned = temp.path().join("overlay/lib/lean");
        let versioned = temp
            .path()
            .join(".elan/toolchains/leanprover--lean4---v4.29.1/lib/lean");
        fs::create_dir_all(unversioned.join("Init")).expect("create unversioned init dir");
        fs::create_dir_all(versioned.join("Init")).expect("create versioned init dir");
        fs::write(unversioned.join("Init/Prelude.olean"), []).expect("write unversioned fixture");
        fs::write(versioned.join("Init/Prelude.olean"), []).expect("write versioned fixture");
        let paths = vec![unversioned, versioned];
        let available =
            clean_olean::alias_resolvable_toolchain_versions(&paths).unwrap_or_default();

        let version = resolve_toolchain_version("leanprover/lean4:stable", &available);

        assert!(version.is_none());
    }
}
