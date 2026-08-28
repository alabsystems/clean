// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `lakefile.toml` parsing — the TOML configuration form Lake accepts alongside
//! `lakefile.lean`.
//!
//! Native Rust, no Lean toolchain (plan Phase 5 / decision 3: full Lake
//! reimplementation in Rust). The schema is verified against the Lean 4
//! v4.30.0-rc2 source: the decoders in `src/lake/Lake/Load/Toml.lean`
//! (`Dependency.decodeToml`, the `name` / `version` / `defaultTargets` / `scope`
//! / `require` keys) and the canonical templates emitted by
//! `src/lake/Lake/CLI/Init.lean` (`[[lean_lib]]`, `[[lean_exe]]`, `[[require]]`).
//!
//! Decoding is intentionally lenient and forward-compatible: unknown keys are
//! ignored (no `deny_unknown_fields`) and every field defaults, mirroring Lake's
//! own "decode what you recognize" behavior so a newer `lakefile.toml` still
//! loads its recognized fields rather than failing wholesale.

use crate::config::{Dependency, LakeConfig, LakefileParseMode, LeanExe, LeanLib, PackageConfig};
use crate::error::{LakeError, LakeResult};
use serde::Deserialize;
use std::path::{Path, PathBuf};

/// Raw deserialization shape of a package `lakefile.toml`.
#[derive(Debug, Clone, Default, Deserialize)]
#[serde(default)]
struct RawTomlLakefile {
    name: String,
    version: Option<String>,
    description: Option<String>,
    keywords: Vec<String>,
    #[serde(rename = "defaultTargets")]
    default_targets: Vec<String>,
    #[serde(rename = "srcDir")]
    src_dir: Option<String>,
    #[serde(rename = "buildDir")]
    build_dir: Option<String>,
    #[serde(rename = "leanVersion")]
    lean_version: Option<String>,
    toolchain: Option<String>,
    #[serde(rename = "moreLeanArgs")]
    more_lean_args: Vec<String>,
    #[serde(rename = "moreLinkArgs")]
    more_link_args: Vec<String>,
    require: Vec<RawRequire>,
    lean_lib: Vec<RawLeanLib>,
    lean_exe: Vec<RawLeanExe>,
}

/// A `[[require]]` dependency entry. Lake accepts several source spellings
/// (`git` as a bare string or a `{ url, rev, subDir }` table, a `path` string,
/// or a nested `source` table with a `type` discriminator); all are normalized
/// to [`Dependency`].
#[derive(Debug, Clone, Default, Deserialize)]
#[serde(default)]
struct RawRequire {
    name: String,
    scope: Option<String>,
    version: Option<String>,
    rev: Option<String>,
    git: Option<RawGit>,
    path: Option<String>,
    #[serde(rename = "subDir")]
    sub_dir: Option<String>,
    source: Option<RawSource>,
}

/// `git = "url"` or `git = { url = "...", rev = "...", subDir = "..." }`.
#[derive(Debug, Clone, Deserialize)]
#[serde(untagged)]
enum RawGit {
    Url(String),
    Table {
        url: String,
        #[serde(default)]
        rev: Option<String>,
        #[serde(default, rename = "subDir")]
        sub_dir: Option<String>,
    },
}

/// Nested `[require.source]` table (`{ type = "git"|"path", url/rev/subDir/dir }`).
#[derive(Debug, Clone, Default, Deserialize)]
#[serde(default)]
struct RawSource {
    #[serde(rename = "type")]
    source_type: Option<String>,
    url: Option<String>,
    rev: Option<String>,
    #[serde(rename = "subDir")]
    sub_dir: Option<String>,
    dir: Option<String>,
}

/// A `[[lean_lib]]` target entry.
#[derive(Debug, Clone, Default, Deserialize)]
#[serde(default)]
struct RawLeanLib {
    name: String,
    #[serde(rename = "srcDir")]
    src_dir: Option<String>,
    roots: Vec<String>,
    globs: Vec<String>,
    #[serde(rename = "defaultFacets")]
    default_facets: Vec<String>,
    #[serde(rename = "moreLeanArgs")]
    more_lean_args: Vec<String>,
}

/// A `[[lean_exe]]` target entry.
#[derive(Debug, Clone, Default, Deserialize)]
#[serde(default)]
struct RawLeanExe {
    name: String,
    #[serde(rename = "srcDir")]
    src_dir: Option<String>,
    root: Option<String>,
    #[serde(rename = "moreLeanArgs")]
    more_lean_args: Vec<String>,
    #[serde(rename = "moreLinkArgs")]
    more_link_args: Vec<String>,
}

impl RawRequire {
    /// Normalize the several accepted source spellings into a [`Dependency`].
    fn into_dependency(self) -> Dependency {
        let mut git: Option<String> = None;
        let mut rev: Option<String> = self.rev;
        let mut path: Option<String> = self.path;

        let mut sub_dir: Option<String> = None;

        match self.git {
            Some(RawGit::Url(url)) => git = Some(url),
            Some(RawGit::Table {
                url,
                rev: r,
                sub_dir: sd,
            }) => {
                git = Some(url);
                if rev.is_none() {
                    rev = r;
                }
                sub_dir = sd;
            }
            None => {}
        }

        if let Some(src) = self.source {
            match src.source_type.as_deref() {
                Some("git") => {
                    if git.is_none() {
                        git = src.url;
                    }
                    if rev.is_none() {
                        rev = src.rev;
                    }
                    if sub_dir.is_none() {
                        sub_dir = src.sub_dir;
                    }
                }
                Some("path") if path.is_none() => {
                    path = src.dir;
                }
                _ => {}
            }
        }

        // Scope-only (Reservoir) require — the shape ALL of real Mathlib's
        // lakefile.toml dependencies use: no git URL and no path, only
        // `scope = "..."`. Derive the git URL from the scope offline; parsing
        // must never reach the network. A wrong derivation surfaces at clone
        // time with an error naming the scope-only require
        // (`fetch::resolve_single_dependency`).
        if git.is_none() && path.is_none() {
            if let Some(scope) = self.scope.as_deref().filter(|s| !s.is_empty()) {
                git = Some(reservoir_offline_git_url(scope, &self.name));
            }
        }

        Dependency {
            name: self.name,
            git,
            rev,
            path: path.map(PathBuf::from),
            version: self.version,
            scope: self.scope,
            sub_dir: sub_dir.map(PathBuf::from),
        }
    }
}

/// Reservoir packages whose GitHub repository name differs from the package
/// name, making the `https://github.com/{scope}/{name}` convention wrong for
/// them. Keys are exact `(scope, name)` pairs as they appear in `[[require]]`
/// entries. Spellings verified against a real Mathlib checkout's
/// `lake-manifest.json` (mathlib4 @ 43ad0e9d2e14) and the Lake audit journal.
/// `mathlib` itself is listed because the convention would
/// resolve it to `leanprover-community/mathlib` — the Lean 3 repository.
const RESERVOIR_REPO_OVERRIDES: &[(&str, &str, &str)] = &[
    (
        "leanprover-community",
        "importGraph",
        "https://github.com/leanprover-community/import-graph",
    ),
    (
        "leanprover-community",
        "proofwidgets",
        "https://github.com/leanprover-community/ProofWidgets4",
    ),
    (
        "leanprover-community",
        "Qq",
        "https://github.com/leanprover-community/quote4",
    ),
    (
        "leanprover",
        "Cli",
        "https://github.com/leanprover/lean4-cli",
    ),
    (
        "leanprover-community",
        "mathlib",
        "https://github.com/leanprover-community/mathlib4",
    ),
];

/// Map a scope-only (Reservoir) require to a concrete git URL with no network
/// access: the `https://github.com/{scope}/{name}` convention, except for the
/// [`RESERVOIR_REPO_OVERRIDES`] entries.
///
/// INTERIM: the full fix is the Reservoir registry lookup
/// (`GET https://reservoir.lean-lang.org/api/v1/packages/{scope}/{name}`) with
/// this mapping as the offline fallback. Until that lands, a wrong derivation
/// fails at clone time with an error naming the scope/name and stating that
/// the Reservoir API was not consulted.
pub(crate) fn reservoir_offline_git_url(scope: &str, name: &str) -> String {
    RESERVOIR_REPO_OVERRIDES
        .iter()
        .find(|(s, n, _)| *s == scope && *n == name)
        .map(|(_, _, url)| (*url).to_string())
        .unwrap_or_else(|| format!("https://github.com/{scope}/{name}"))
}

impl RawTomlLakefile {
    fn into_lake_config(self) -> LakeConfig {
        let dependencies = self
            .require
            .into_iter()
            .map(RawRequire::into_dependency)
            .collect();

        let package = PackageConfig {
            name: self.name,
            version: self.version,
            description: self.description,
            dependencies,
            src_dir: self.src_dir.map(PathBuf::from),
            build_dir: self.build_dir.map(PathBuf::from),
            // `leanVersion` is the modern key; older lakefiles used `toolchain`.
            lean_version: self.lean_version.or(self.toolchain),
            more_lean_args: self.more_lean_args,
            more_link_args: self.more_link_args,
            ..Default::default()
        };

        let libs = self
            .lean_lib
            .into_iter()
            .map(|lib| {
                // Lake defaults a library's root to its own name when `roots` is
                // omitted.
                let roots = if lib.roots.is_empty() {
                    vec![lib.name.clone()]
                } else {
                    lib.roots
                };
                LeanLib {
                    name: lib.name,
                    roots,
                    globs: lib.globs,
                    more_lean_args: lib.more_lean_args,
                    default_facets: lib.default_facets,
                    src_dir: lib.src_dir.map(PathBuf::from),
                    pre_compile_hooks: Vec::new(),
                }
            })
            .collect();

        let exes = self
            .lean_exe
            .into_iter()
            .map(|exe| {
                // Lake defaults an executable's root module to its own name.
                let root = exe.root.unwrap_or_else(|| exe.name.clone());
                LeanExe {
                    name: exe.name,
                    root,
                    more_lean_args: exe.more_lean_args,
                    more_link_args: exe.more_link_args,
                    src_dir: exe.src_dir.map(PathBuf::from),
                    supported_backends: Vec::new(),
                }
            })
            .collect();

        LakeConfig {
            package,
            libs,
            exes,
            tests: Vec::new(),
            scripts: Vec::new(),
            default_targets: self.default_targets,
            diagnostics: Vec::new(),
        }
    }
}

impl LakeConfig {
    /// Parse `lakefile.toml` content into a [`LakeConfig`].
    pub fn parse_toml(content: &str) -> LakeResult<Self> {
        let raw: RawTomlLakefile = toml::from_str(content)
            .map_err(|e| LakeError::LakefileParse(format!("lakefile.toml: {e}")))?;
        Ok(raw.into_lake_config())
    }

    /// Load and parse a `lakefile.toml` file.
    pub(crate) fn load_toml(lakefile_path: &Path) -> LakeResult<Self> {
        if !lakefile_path.exists() {
            return Err(LakeError::LakefileNotFound(lakefile_path.to_path_buf()));
        }
        let content = std::fs::read_to_string(lakefile_path)?;
        Self::parse_toml(&content)
    }

    /// Load a package configuration from a project directory, preferring
    /// `lakefile.toml` over `lakefile.lean` when both are present (Lake itself
    /// disallows both, so the preference only matters for malformed projects).
    pub fn load_from_dir(dir: &Path) -> LakeResult<Self> {
        Self::load_from_dir_with_mode(dir, LakefileParseMode::Lenient)
    }

    /// Like [`Self::load_from_dir`], with an explicit `lakefile.lean` parse
    /// mode. The TOML decoder is deliberately lenient about unknown keys
    /// (mirroring Lake itself), so the mode only affects the `lakefile.lean`
    /// fallback path.
    pub fn load_from_dir_with_mode(dir: &Path, mode: LakefileParseMode) -> LakeResult<Self> {
        let toml_path = dir.join("lakefile.toml");
        if toml_path.is_file() {
            return Self::load_toml(&toml_path);
        }
        let lean_path = dir.join("lakefile.lean");
        if lean_path.is_file() {
            return Self::load_with_mode(&lean_path, mode);
        }
        Err(LakeError::LakefileNotFound(dir.to_path_buf()))
    }
}

#[cfg(test)]
#[path = "toml_config_tests.rs"]
mod toml_config_tests;
