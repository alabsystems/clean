// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! lean-toolchain parsing and version resolution helpers.

use std::path::Path;

use semver::Version;

use crate::error::{LakeError, LakeResult};

/// The toolchain identifier written into a freshly scaffolded project.
///
/// Public so `clean lake new` / `clean lake init` — which live in `clean-cli`,
/// not here — write the SAME value the library scaffold writes. A second
/// spelling in the CLI is how the two `init` implementations drifted apart in
/// the first place.
///
/// The spelling is chosen for what elan does with it (plan item
/// `devsurface-lake-env-no-silent-lean`): the bare name `clean` is a custom
/// toolchain when one is linked (`elan toolchain link clean <dir>`) and
/// otherwise the Lean release `clean`, which does not exist, so `lean` or
/// `lake` run through elan in the project fails loudly. The old `clean:stable`
/// is outside elan's name grammar, and elan 4.2.1 skipped such a file and ran
/// its default Lean toolchain with no message. The measurement is
/// `reports/lake-new-elan-toolchain-2026-10-25/`, pinned by
/// `test_default_toolchain_matches_the_measured_elan_probe`.
pub const DEFAULT_CLEAN_TOOLCHAIN: &str = "clean\n";

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

    #[test]
    fn test_resolve_toolchain_version_bare_clean_never_resolves_to_lean4() {
        let available = vec![
            "v4.29.1".to_string(),
            "v4.30.0-rc2".to_string(),
            "nightly-2026-04-21".to_string(),
        ];
        assert!(resolve_toolchain_version("clean", &available).is_none());
        assert!(resolve_toolchain_version("clean", &[]).is_none());
    }

    /// elan's name lookup, read from its source at v4.2.1 and v4.2.4
    /// (`src/elan/toolchain.rs`, `lookup_unresolved_toolchain_desc`;
    /// `src/elan-dist/src/dist.rs`, `ToolchainDesc::from_resolved_str`), which
    /// agree for every name below. A name outside the grammar
    /// `^(?:owner/repo:)?[a-zA-Z0-9-.]+$` is unparseable, and elan 4.2.1 skips an
    /// unparseable `lean-toolchain` and falls back to its default toolchain
    /// (`clean:stable` did exactly that). The names `stable`, `beta`, `nightly`
    /// and `lean-toolchain` are channels, which fall back to an installed
    /// toolchain when the release query fails. A version-shaped name names a
    /// real Lean release. Any name is first tried as a path relative to the
    /// project (`try_parse_path_toolchain`), used only when
    /// `<project>/<name>/bin/lean` is a file. Otherwise a bare name in the
    /// grammar is a linked custom toolchain when one exists and else the
    /// release `leanprover/lean4:<name>`, which is only installed by
    /// downloading it. This model explains the spelling; the measurement is
    /// [`test_default_toolchain_matches_the_measured_elan_probe`].
    #[test]
    fn test_default_toolchain_is_a_bare_elan_name_not_a_channel_path_or_version() {
        let name = super::DEFAULT_CLEAN_TOOLCHAIN
            .strip_suffix('\n')
            .expect("the scaffold toolchain is one newline-terminated line");
        assert!(
            !name.is_empty()
                && name
                    .chars()
                    .all(|c| c.is_ascii_alphanumeric() || c == '-' || c == '.'),
            "`{name}` is outside elan's bare-name grammar; elan 4.2.1 would skip the \
             file and fall back to its default toolchain"
        );
        assert!(
            !["stable", "beta", "nightly", "lean-toolchain"].contains(&name),
            "`{name}` is an elan channel, which falls back to an installed toolchain offline"
        );
        assert!(
            !name.starts_with("nightly")
                && !name.starts_with(|c: char| c.is_ascii_digit())
                && super::parse_semver(name).is_none(),
            "`{name}` is shaped like a Lean release"
        );
    }

    /// The committed measurement of what real elan does in a `clean lake new`
    /// project (`scripts/probe_lake_new_elan_toolchain.py`, run sealed with a
    /// dead proxy). Changing the scaffold spelling without re-measuring fails
    /// here.
    const ELAN_PROBE_REPORT: &str = "reports/lake-new-elan-toolchain-2026-10-25/offline-fixed.json";

    fn elan_version(run: &serde_json::Value) -> (u64, u64, u64) {
        let text = run["elan_version"]
            .as_str()
            .expect("elan_version is a string");
        let number = text
            .strip_prefix("elan ")
            .and_then(|rest| rest.split_whitespace().next())
            .unwrap_or_else(|| panic!("unexpected elan version line `{text}`"));
        let parts: Vec<u64> = number
            .split('.')
            .map(|p| p.parse().expect("numeric elan version part"))
            .collect();
        assert_eq!(
            parts.len(),
            3,
            "elan version `{number}` is major.minor.patch"
        );
        (parts[0], parts[1], parts[2])
    }

    fn fired(case: &serde_json::Value, key: &str) -> bool {
        case["steps"]
            .as_array()
            .expect("steps")
            .iter()
            .any(|s| s[key].as_bool().expect("a sentinel flag"))
    }

    #[test]
    fn test_default_toolchain_matches_the_measured_elan_probe() {
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let raw = fs::read_to_string(root.join(ELAN_PROBE_REPORT))
            .unwrap_or_else(|e| panic!("read {ELAN_PROBE_REPORT}: {e}"));
        let report: serde_json::Value = serde_json::from_str(&raw).expect("probe report is JSON");
        let runs = report["runs"].as_array().expect("report has runs");
        let mut versions = Vec::new();
        for run in runs {
            let version = elan_version(run);
            versions.push(version);
            let cases = run["cases"].as_array().expect("run has cases");
            assert_eq!(cases.len(), 4, "four cases per elan: {version:?}");
            for case in cases {
                let verdict = case["verdict"].as_str().expect("verdict");
                match case["case"].as_str().expect("case name") {
                    "clean lake new" => {
                        assert_eq!(
                            case["lean_toolchain"].as_str(),
                            Some(super::DEFAULT_CLEAN_TOOLCHAIN),
                            "the report measured a different spelling than the scaffold writes"
                        );
                        assert_eq!(verdict, "refused", "elan {version:?}");
                        assert!(
                            !fired(case, "sentinel_fired"),
                            "elan {version:?} ran the fake leanprover lean"
                        );
                    }
                    "legacy clean:stable" => {
                        // The defect this spelling replaced: 4.2.1 falls back
                        // silently, 4.2.2 and later refuse the name.
                        let expected = if version < (4, 2, 2) {
                            "ran-leanprover"
                        } else {
                            "refused"
                        };
                        assert_eq!(verdict, expected, "legacy spelling under {version:?}");
                    }
                    "positive control" => {
                        assert_eq!(verdict, "ran-leanprover", "harness blind at {version:?}");
                        assert!(
                            fired(case, "sentinel_fired"),
                            "the control's sentinel fired"
                        );
                    }
                    "linked clean" => {
                        // `elan toolchain link clean <dir>` is how a user
                        // points the scaffold's name at a Clean shim.
                        assert_eq!(
                            case["lean_toolchain"].as_str(),
                            Some(super::DEFAULT_CLEAN_TOOLCHAIN)
                        );
                        assert_eq!(verdict, "ran-linked", "elan {version:?}");
                        assert!(!fired(case, "sentinel_fired"), "elan {version:?}");
                    }
                    other => panic!("unknown probe case `{other}`"),
                }
            }
        }
        for needed in [(4, 2, 1), (4, 2, 2)] {
            assert!(
                versions.contains(&needed),
                "the probe covers elan {needed:?}, the last silent fallback and the first \
                 refusal of an unparseable name: {versions:?}"
            );
        }
        assert!(
            versions.iter().any(|v| *v >= (4, 2, 3)),
            "the probe covers an elan at or after 4.2.3: {versions:?}"
        );
    }
}
