// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Startup helpers for workspace lean-toolchain discovery.

use std::path::Path;

use clean_olean::ActiveStdlibToolchain;
use semver::Version;
use tracing::warn;

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct WorkspaceToolchain {
    pub(crate) identifier: Option<String>,
    pub(crate) resolved_version: Option<String>,
}

pub(crate) fn read_workspace_toolchain(root: Option<&Path>) -> WorkspaceToolchain {
    let Some(root) = root else {
        return WorkspaceToolchain::default();
    };

    let path = root.join("lean-toolchain");
    if !path.exists() {
        return WorkspaceToolchain::default();
    }

    let content = match std::fs::read_to_string(&path) {
        Ok(content) => content,
        Err(error) => {
            warn!("Failed to read {}: {error}", path.display());
            return WorkspaceToolchain::default();
        }
    };

    let path_display = path.display().to_string();
    let identifier = match parse_toolchain_identifier(&content, &path_display) {
        Ok(identifier) => identifier,
        Err(error) => {
            warn!("{error}; ignoring malformed lean-toolchain for server startup");
            return WorkspaceToolchain::default();
        }
    };

    let search_paths = clean_olean::default_search_paths();
    let active_stdlib = clean_olean::active_stdlib_toolchain(&search_paths);
    let alias_resolution_versions = clean_olean::alias_resolvable_toolchain_versions(&search_paths);
    let resolved_version = resolve_toolchain_version(
        &identifier,
        alias_resolution_versions.as_deref().unwrap_or_default(),
    );

    if let Some(message) = toolchain_warning(
        &path_display,
        &identifier,
        resolved_version.as_deref(),
        active_stdlib.as_ref(),
    ) {
        warn!("{message}");
    }

    WorkspaceToolchain {
        identifier: Some(identifier),
        resolved_version,
    }
}

fn parse_toolchain_identifier(content: &str, path_display: &str) -> Result<String, String> {
    let mut identifier = None;

    for raw_line in content.lines() {
        let trimmed = raw_line.trim_start_matches('\u{feff}').trim();
        if trimmed.is_empty() || trimmed.starts_with("--") || trimmed.starts_with('#') {
            continue;
        }

        if trimmed.split_whitespace().count() != 1 {
            return Err(format!(
                "lean-toolchain in {path_display} must contain a single toolchain identifier"
            ));
        }

        if identifier.replace(trimmed.to_string()).is_some() {
            return Err(format!(
                "lean-toolchain in {path_display} must contain a single toolchain identifier"
            ));
        }
    }

    identifier.ok_or_else(|| format!("lean-toolchain in {path_display} is empty"))
}

fn resolve_toolchain_version(identifier: &str, available_versions: &[String]) -> Option<String> {
    let requested = identifier
        .rsplit_once(':')
        .map_or(identifier, |(_, version)| version)
        .trim();

    if parse_semver(requested).is_some() {
        return Some(requested.to_string());
    }

    match requested {
        "stable" => available_versions
            .iter()
            .find(|version| is_stable_release(version))
            .cloned(),
        "nightly" => available_versions
            .iter()
            .find(|version| version.starts_with("nightly"))
            .cloned(),
        _ => available_versions
            .iter()
            .find(|version| *version == requested)
            .cloned(),
    }
}

fn toolchain_warning(
    path_display: &str,
    identifier: &str,
    resolved_version: Option<&str>,
    active_stdlib: Option<&ActiveStdlibToolchain>,
) -> Option<String> {
    match active_stdlib {
        Some(ActiveStdlibToolchain::Versioned { path, version: active_version }) => {
            match resolved_version {
                Some(version) if version == active_version => None,
                Some(version) => Some(format!(
                    "lean-toolchain in {path_display} resolves '{identifier}' to {version}, but active Lean stdlib at {} is {active_version}; server startup may load a mismatched stdlib",
                    path.display()
                )),
                None if is_version_alias(identifier) => Some(format!(
                    "lean-toolchain in {path_display} uses unresolved identifier '{identifier}', but active Lean stdlib at {} is {active_version}",
                    path.display()
                )),
                None => None,
            }
        }
        Some(ActiveStdlibToolchain::UnversionedPath(path)) => match resolved_version {
            Some(version) => Some(format!(
                "lean-toolchain in {path_display} resolves '{identifier}' to {version}, but active Lean stdlib at {} does not expose a toolchain version; server startup may load a mismatched stdlib",
                path.display()
            )),
            None if is_version_alias(identifier) => Some(format!(
                "lean-toolchain in {path_display} uses unresolved identifier '{identifier}'; active Lean stdlib at {} does not expose a toolchain version, so alias resolution is disabled",
                path.display()
            )),
            None => None,
        },
        None => match resolved_version {
            Some(version) => Some(format!(
                "lean-toolchain in {path_display} resolves '{identifier}' to {version}, but no active Lean stdlib source is discoverable"
            )),
            None if is_version_alias(identifier) => Some(format!(
                "lean-toolchain in {path_display} uses unresolved identifier '{identifier}'; no active Lean stdlib source is discoverable"
            )),
            None => None,
        },
    }
}

fn is_version_alias(identifier: &str) -> bool {
    let requested = identifier
        .rsplit_once(':')
        .map_or(identifier, |(_, version)| version)
        .trim();
    !requested.is_empty() && parse_semver(requested).is_none()
}

fn parse_semver(version: &str) -> Option<Version> {
    Version::parse(version.trim_start_matches('v')).ok()
}

fn is_stable_release(version: &str) -> bool {
    parse_semver(version).is_some_and(|version| version.pre.is_empty())
}

#[cfg(test)]
mod tests {
    use super::{
        parse_toolchain_identifier, resolve_toolchain_version, toolchain_warning,
        ActiveStdlibToolchain,
    };
    use std::path::PathBuf;

    #[test]
    fn parses_comments_and_blank_lines() {
        let content = "\n# comment\n-- note\nleanprover/lean4:v4.29.1\n";
        let parsed = parse_toolchain_identifier(content, "/tmp/lean-toolchain").unwrap();
        assert_eq!(parsed, "leanprover/lean4:v4.29.1");
    }

    #[test]
    fn rejects_multiple_identifiers() {
        let content = "leanprover/lean4:v4.29.1\nleanprover/lean4:v4.28.0\n";
        let err = parse_toolchain_identifier(content, "/tmp/lean-toolchain").unwrap_err();
        assert!(err.contains("must contain a single toolchain identifier"));
    }

    #[test]
    fn resolves_stable_to_first_stable_version_in_priority_order() {
        let available = vec![
            "v4.28.0".to_string(),
            "v4.30.0-rc2".to_string(),
            "v4.29.1".to_string(),
        ];
        let version = resolve_toolchain_version("leanprover/lean4:stable", &available);
        assert_eq!(version.as_deref(), Some("v4.28.0"));
    }

    #[test]
    fn extracts_search_path_versions_in_order() {
        let paths = vec![
            PathBuf::from("/tmp/mathlib/build/lib"),
            PathBuf::from("./.elan/toolchains/leanprover--lean4---v4.28.0/lib/lean"),
            PathBuf::from("./.elan/toolchains/leanprover--lean4---v4.29.1/lib/lean"),
            PathBuf::from("./.elan/toolchains/leanprover--lean4---v4.28.0/lib/lean"),
        ];
        let versions = clean_olean::toolchain_versions_from_search_paths(&paths);
        assert_eq!(versions, vec!["v4.28.0", "v4.29.1"]);
    }

    #[test]
    fn reports_preferred_toolchain_mismatch() {
        let warning = toolchain_warning(
            "/tmp/lean-toolchain",
            "leanprover/lean4:stable",
            Some("v4.29.1"),
            Some(&ActiveStdlibToolchain::Versioned {
                path: PathBuf::from("./.elan/toolchains/leanprover--lean4---v4.28.0/lib/lean"),
                version: "v4.28.0".to_string(),
            }),
        );
        let warning = warning.expect("mismatch should produce a warning");
        assert!(warning.contains("resolves 'leanprover/lean4:stable' to v4.29.1"));
        assert!(warning.contains("is v4.28.0"));
    }

    #[test]
    fn reports_unresolved_aliases() {
        let warning = toolchain_warning(
            "/tmp/lean-toolchain",
            "leanprover/lean4:nightly",
            None,
            None,
        );
        let warning = warning.expect("unresolved alias should warn");
        assert!(warning.contains("unresolved identifier"));
        assert!(warning.contains("nightly"));
    }

    #[test]
    fn reports_ambiguous_higher_priority_search_paths() {
        let warning = toolchain_warning(
            "/tmp/lean-toolchain",
            "leanprover/lean4:stable",
            None,
            Some(&ActiveStdlibToolchain::UnversionedPath(PathBuf::from(
                "/opt/lean-current/lib/lean",
            ))),
        )
        .expect("ambiguous active stdlib should warn");
        assert!(warning.contains("/opt/lean-current/lib/lean"));
        assert!(warning.contains("stable"));
    }
}
