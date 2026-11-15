// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lake configuration parsing
//!
//! Parses lakefile.lean to extract package configuration. The line scraper
//! itself ([`LakeConfig::parse_with_mode`] and the helpers only it calls)
//! lives in the `lakefile` submodule.

mod lakefile;
mod lean_options;
mod option_scan;

pub use lean_options::{LeanOption, LeanOptionValue};

use crate::error::{LakeError, LakeResult};
use crate::manifest::{LakeManifest, ManifestPackage};
use semver::{Version, VersionReq};
use serde::{Deserialize, Serialize};
use std::path::{Path, PathBuf};

/// Lake configuration loaded from lakefile.lean
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct LakeConfig {
    /// Package configuration
    pub package: PackageConfig,
    /// Lean libraries
    pub libs: Vec<LeanLib>,
    /// Lean executables
    pub exes: Vec<LeanExe>,
    /// Lean tests
    pub tests: Vec<LeanTest>,
    /// Lake scripts
    pub scripts: Vec<LakeScript>,
    /// Default targets
    pub default_targets: Vec<String>,
    /// Top-level `lakefile.lean` constructs the simplified parser skipped.
    /// Empty for `lakefile.toml` projects and fully-understood lakefiles.
    pub diagnostics: Vec<SkippedConstruct>,
}

/// A top-level `lakefile.lean` construct the simplified parser skipped.
///
/// The line scraper in [`LakeConfig::parse`] models Lake's declarative subset
/// (`package` / `require` / `lean_lib` / `lean_exe` / `lean_test` / `script`);
/// anything else at top level (e.g. `abbrev`, custom `target` declarations,
/// meta code) is recorded here instead of vanishing silently.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct SkippedConstruct {
    /// 1-based line number in the lakefile
    pub line: usize,
    /// Leading token of the skipped line (e.g. `abbrev`, `target`)
    pub token: String,
    /// Full trimmed text of the skipped line
    pub text: String,
}

/// How [`LakeConfig::parse_with_mode`] treats unrecognized top-level
/// constructs.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[non_exhaustive]
pub enum LakefileParseMode {
    /// Record skipped constructs in [`LakeConfig::diagnostics`] and continue.
    #[default]
    Lenient,
    /// Fail with [`LakeError::UnrecognizedConstructs`] when any top-level
    /// construct is not understood, so programmatic lakefiles can never
    /// silently under-parse.
    Strict,
}

impl LakefileParseMode {
    /// Environment variable selecting strict lakefile.lean parsing.
    pub const STRICT_ENV: &str = "CLEAN_LAKE_STRICT_LAKEFILE";

    /// Resolve the mode from the process environment: any value of
    /// [`Self::STRICT_ENV`] other than unset, empty, or `0` selects
    /// [`Self::Strict`].
    #[must_use]
    pub fn from_env() -> Self {
        match std::env::var(Self::STRICT_ENV) {
            Ok(value) if !value.is_empty() && value != "0" => Self::Strict,
            _ => Self::Lenient,
        }
    }
}

/// Package configuration
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
#[non_exhaustive]
pub struct PackageConfig {
    /// Package name
    pub name: String,
    /// Package version (optional)
    pub version: Option<String>,
    /// Package description (optional)
    pub description: Option<String>,
    /// Package dependencies
    pub dependencies: Vec<Dependency>,
    /// Source directory (defaults to ".")
    pub src_dir: Option<PathBuf>,
    /// Build directory (defaults to ".lake/build")
    pub build_dir: Option<PathBuf>,
    /// Lean version constraint
    pub lean_version: Option<String>,
    /// `leanOptions`: passed to `lean` as `-D<name>=<value>` before
    /// `moreLeanArgs` (Lake's order; see `config/lean_options.rs`).
    #[serde(default)]
    pub lean_options: Vec<LeanOption>,
    /// Extra compiler options
    pub more_lean_args: Vec<String>,
    /// Extra linker options
    pub more_link_args: Vec<String>,
    /// `weakLeanArgs`: Lake 4.8 passes them to `lean` BEFORE the `leanArgs`
    /// (`mod.weakLeanArgs ++ mod.leanArgs`), so a `-D` in them is applied
    /// unless a `leanOptions` / `moreLeanArgs` entry sets the same name.
    #[serde(default)]
    pub weak_lean_args: Vec<String>,
    /// `leanOptions` / `moreLeanArgs` / `weakLeanArgs` values the parser could
    /// not read (e.g. Mathlib's `leanOptions := mathlibLeanOptions`, or a
    /// field written where the line scraper does not attribute it to a
    /// target). A build refuses every module they would govern rather than
    /// compile it under options it never saw.
    #[serde(skip)]
    pub unreadable_lean_args: Vec<String>,
}

/// A package dependency
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct Dependency {
    /// Dependency name
    pub name: String,
    /// Git repository URL
    pub git: Option<String>,
    /// Git revision (commit, branch, or tag)
    pub rev: Option<String>,
    /// Path to local dependency
    pub path: Option<PathBuf>,
    /// Version constraint
    pub version: Option<String>,
    /// Reservoir scope (`scope = "..."` in a `[[require]]` entry). Recorded so
    /// the fetch layer can attribute a clone failure to the interim offline
    /// scope-to-GitHub mapping (`toml_config::reservoir_offline_git_url`) when
    /// the git URL was derived from the scope rather than written explicitly.
    #[serde(default)]
    pub scope: Option<String>,
    /// Subdirectory of a git dependency holding the package root (Lake's
    /// `subDir`). When set, the clone is only the transport: the package the
    /// require names lives at `<clone>/<subDir>`, which is how monorepos
    /// publish several Lake packages from one repository.
    #[serde(default, rename = "subDir")]
    pub sub_dir: Option<PathBuf>,
}

/// Lean library configuration
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct LeanLib {
    /// Library name
    pub name: String,
    /// Root modules (e.g., #[`MyLib, `MyLib.Extra])
    pub roots: Vec<String>,
    /// Glob patterns for source files
    pub globs: Vec<String>,
    /// Extra Lean arguments
    pub more_lean_args: Vec<String>,
    /// Whether this is the default target
    pub default_facets: Vec<String>,
    /// Source directory override
    pub src_dir: Option<PathBuf>,
    /// Pre-compilation hooks
    pub pre_compile_hooks: Vec<String>,
    /// `leanOptions`: passed to `lean` as `-D<name>=<value>` before
    /// `moreLeanArgs` (Lake's order; see `config/lean_options.rs`).
    #[serde(default)]
    pub lean_options: Vec<LeanOption>,
    /// `weakLeanArgs`: Lake 4.8 passes them to `lean` BEFORE the `leanArgs`
    /// (`mod.weakLeanArgs ++ mod.leanArgs`), so a `-D` in them is applied
    /// unless a `leanOptions` / `moreLeanArgs` entry sets the same name.
    #[serde(default)]
    pub weak_lean_args: Vec<String>,
    /// `leanOptions` / `moreLeanArgs` / `weakLeanArgs` values the parser could
    /// not read (e.g. Mathlib's `leanOptions := mathlibLeanOptions`, or a
    /// field written where the line scraper does not attribute it to a
    /// target). A build refuses every module they would govern rather than
    /// compile it under options it never saw.
    #[serde(skip)]
    pub unreadable_lean_args: Vec<String>,
}

/// Lean executable configuration
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct LeanExe {
    /// Executable name
    pub name: String,
    /// Root module
    pub root: String,
    /// Extra Lean arguments
    pub more_lean_args: Vec<String>,
    /// Extra linker arguments
    pub more_link_args: Vec<String>,
    /// Source directory override
    pub src_dir: Option<PathBuf>,
    /// Support backends
    pub supported_backends: Vec<String>,
    /// `leanOptions`: passed to `lean` as `-D<name>=<value>` before
    /// `moreLeanArgs` (Lake's order; see `config/lean_options.rs`).
    #[serde(default)]
    pub lean_options: Vec<LeanOption>,
    /// `weakLeanArgs`: Lake 4.8 passes them to `lean` BEFORE the `leanArgs`
    /// (`mod.weakLeanArgs ++ mod.leanArgs`), so a `-D` in them is applied
    /// unless a `leanOptions` / `moreLeanArgs` entry sets the same name.
    #[serde(default)]
    pub weak_lean_args: Vec<String>,
    /// `leanOptions` / `moreLeanArgs` / `weakLeanArgs` values the parser could
    /// not read (e.g. Mathlib's `leanOptions := mathlibLeanOptions`, or a
    /// field written where the line scraper does not attribute it to a
    /// target). A build refuses every module they would govern rather than
    /// compile it under options it never saw.
    #[serde(skip)]
    pub unreadable_lean_args: Vec<String>,
}

/// Lean test configuration
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct LeanTest {
    /// Test name
    pub name: String,
    /// Root module
    pub root: String,
    /// Extra Lean arguments
    pub more_lean_args: Vec<String>,
    /// Source directory override
    pub src_dir: Option<PathBuf>,
}

/// Lake script configuration
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct LakeScript {
    /// Script name
    pub name: String,
    /// Argument binder declared by the script, verbatim and without the
    /// surrounding parentheses (`args` for Lean's `script s (args) do`).
    ///
    /// `None` when the script declares no binder. Lake scripts have type
    /// `List String → IO UInt32`, so the binder is the name the body uses for
    /// its argv; a consumer that cannot bind it must say so rather than
    /// elaborate a body with a free variable in it.
    pub args: Option<String>,
    /// Script body (Lean code to execute)
    pub body: String,
    /// Script documentation
    pub doc: Option<String>,
}

/// A `script` declaration header, split into its parts.
///
/// Lean's Lake spells a script three ways, and all three reach this parser:
///
/// ```text
/// script <name> [(args)] do    -- body on the following indented lines
/// script <name> := <term>      -- `:= do` opens a do-block body
/// script <name> where          -- Clean's declarative block form
/// ```
///
/// The `do` form used to fall through the name split, so the WHOLE remainder
/// (`greet (args) do`) became the name and the body was never collected —
/// a silent drop, since the body lines are indented and therefore not recorded
/// as skipped top-level constructs either.
#[derive(Debug, PartialEq, Eq)]
struct ScriptHeader<'a> {
    /// Bare script name: never carries the binder or a trailing keyword.
    name: &'a str,
    /// Argument binder as written, parentheses stripped (`args`).
    args: Option<&'a str>,
    /// Text on the header line that already opens the body — `do` for the
    /// `do` forms, or an inline term for `script s := <term>`.
    inline_body: Option<&'a str>,
    /// Whether a block continues on the following lines.
    has_block: bool,
}

impl LakeConfig {
    /// Load configuration from a lakefile.lean file (lenient mode)
    pub fn load(lakefile_path: &Path) -> LakeResult<Self> {
        Self::load_with_mode(lakefile_path, LakefileParseMode::Lenient)
    }

    /// Load configuration from a lakefile.lean file with an explicit handling
    /// mode for unrecognized top-level constructs
    pub(crate) fn load_with_mode(
        lakefile_path: &Path,
        mode: LakefileParseMode,
    ) -> LakeResult<Self> {
        if !lakefile_path.exists() {
            return Err(LakeError::LakefileNotFound(lakefile_path.to_path_buf()));
        }

        let content = std::fs::read_to_string(lakefile_path)?;
        Self::parse_with_mode(&content, mode)
    }

    /// Alias for load - load configuration from a lakefile.lean file
    pub fn from_file(lakefile_path: &Path) -> LakeResult<Self> {
        Self::load(lakefile_path)
    }

    /// Parse lakefile.lean content (lenient mode: skipped top-level constructs
    /// are recorded in [`LakeConfig::diagnostics`])
    pub fn parse(content: &str) -> LakeResult<Self> {
        Self::parse_with_mode(content, LakefileParseMode::Lenient)
    }

    /// Split the text after `script ` into name, argument binder, and body head.
    ///
    /// See [`ScriptHeader`] for the three spellings this must handle. The
    /// `do` form is the one Lean itself prints in every `lake new` template,
    /// and it is the one this parser used to swallow whole.
    fn split_script_header(rest: &str) -> ScriptHeader<'_> {
        let rest = rest.trim();

        let (head, inline_body, has_block) = if let Some(idx) = rest.find(" where") {
            (&rest[..idx], None, true)
        } else if let Some(idx) = rest.find(" :=") {
            let tail = rest[idx + " :=".len()..].trim();
            let inline = if tail.is_empty() { None } else { Some(tail) };
            (&rest[..idx], inline, true)
        } else if let Some(head) = Self::strip_trailing_do(rest) {
            // `script <name> [(args)] do` — `do` opens the body, whose
            // statements follow on the indented lines beneath.
            (head, Some("do"), true)
        } else {
            // Bare `script <name>`: a declaration with no body at all.
            (rest, None, false)
        };

        // The binder (if any) starts at the first space or `(` after the name.
        let head = head.trim();
        let (name, args) = match head.find(|c: char| c.is_whitespace() || c == '(') {
            Some(idx) => {
                let binder = head[idx..]
                    .trim()
                    .trim_start_matches('(')
                    .trim_end_matches(')');
                let binder = binder.trim();
                let binder = if binder.is_empty() {
                    None
                } else {
                    Some(binder)
                };
                (head[..idx].trim(), binder)
            }
            None => (head, None),
        };

        ScriptHeader {
            name,
            args,
            inline_body,
            has_block,
        }
    }

    /// Strip a trailing standalone `do` keyword from a `script` header.
    ///
    /// Returns `None` when the header does not end in a `do` TOKEN, so that a
    /// name merely ending in those letters (`script tornado`) is left intact.
    fn strip_trailing_do(header: &str) -> Option<&str> {
        let head = header.strip_suffix("do")?;
        // `script do` has no name; and `tornado` must not split as `torna`+`do`.
        if !head.ends_with(|c: char| c.is_whitespace()) {
            return None;
        }
        let head = head.trim_end();
        if head.is_empty() {
            return None;
        }
        Some(head)
    }

    /// Parse a Lean name array like #[`Name1, `Name2]
    fn parse_name_array(s: &str) -> Vec<String> {
        let s = s.trim();
        if !s.starts_with("#[") || !s.ends_with(']') {
            // Single value
            return vec![s.trim_start_matches('`').to_string()];
        }
        let inner = &s[2..s.len() - 1];
        inner
            .split(',')
            .map(|part| part.trim().trim_start_matches('`').to_string())
            .filter(|s| !s.is_empty())
            .collect()
    }

    /// Parse a string array like #["str1", "str2"]
    fn parse_string_array(s: &str) -> Vec<String> {
        let s = s.trim();
        if !s.starts_with("#[") || !s.ends_with(']') {
            return vec![s.trim_matches('"').to_string()];
        }
        let inner = &s[2..s.len() - 1];
        inner
            .split(',')
            .map(|part| part.trim().trim_matches('"').to_string())
            .filter(|s| !s.is_empty())
            .collect()
    }

    /// Get the source directory for the package
    #[must_use]
    pub(crate) fn src_dir(&self) -> PathBuf {
        self.package
            .src_dir
            .clone()
            .unwrap_or_else(|| PathBuf::from("."))
    }

    /// Get the build directory for the package
    #[must_use]
    pub(crate) fn build_dir(&self) -> PathBuf {
        self.package
            .build_dir
            .clone()
            .unwrap_or_else(|| PathBuf::from(".lake/build"))
    }

    /// Validate that declared dependencies are satisfied by the manifest
    pub(crate) fn validate_manifest(&self, manifest: &LakeManifest) -> LakeResult<()> {
        self.package.validate_manifest(manifest)
    }
}

impl PackageConfig {
    /// Create a minimal package configuration
    #[must_use]
    pub fn minimal(name: &str) -> Self {
        Self {
            name: name.to_string(),
            ..Default::default()
        }
    }

    /// Validate that all declared dependencies are satisfied by the manifest
    pub(crate) fn validate_manifest(&self, manifest: &LakeManifest) -> LakeResult<()> {
        for dep in &self.dependencies {
            let pkg =
                manifest
                    .get_package(&dep.name)
                    .ok_or_else(|| LakeError::DependencyNotFound {
                        name: dep.name.clone(),
                    })?;
            dep.matches_manifest(pkg)?;
        }
        Ok(())
    }
}

impl LeanLib {
    /// Create a minimal library configuration
    #[must_use]
    pub fn minimal(name: &str) -> Self {
        Self {
            name: name.to_string(),
            roots: vec![name.to_string()],
            ..Default::default()
        }
    }

    /// Get the root modules for this library
    #[must_use]
    pub(crate) fn root_modules(&self) -> Vec<String> {
        if self.roots.is_empty() {
            vec![self.name.clone()]
        } else {
            self.roots.clone()
        }
    }
}

impl LeanExe {
    /// Create a minimal executable configuration
    #[must_use]
    pub fn minimal(name: &str, root: &str) -> Self {
        Self {
            name: name.to_string(),
            root: root.to_string(),
            ..Default::default()
        }
    }
}

impl LeanTest {
    /// Create a minimal test configuration
    #[must_use]
    pub fn minimal(name: &str, root: &str) -> Self {
        Self {
            name: name.to_string(),
            root: root.to_string(),
            ..Default::default()
        }
    }
}

impl Dependency {
    /// Check if this dependency is satisfied by the manifest entry
    pub(crate) fn matches_manifest(&self, pkg: &ManifestPackage) -> LakeResult<()> {
        match pkg {
            ManifestPackage::Git(g) => {
                if let Some(path) = &self.path {
                    return Err(LakeError::DependencyMismatch {
                        name: self.name.clone(),
                        reason: format!(
                            "expected path dependency at {}, found git",
                            path.display()
                        ),
                    });
                }

                if let Some(dep_url) = &self.git {
                    if Self::normalize_git_url(dep_url) != Self::normalize_git_url(&g.url) {
                        return Err(LakeError::DependencyMismatch {
                            name: self.name.clone(),
                            reason: format!(
                                "git URL mismatch (expected {}, found {})",
                                dep_url, g.url
                            ),
                        });
                    }
                }

                if let Some(req_rev) = &self.rev {
                    if !(g.rev.starts_with(req_rev) || req_rev.starts_with(&g.rev)) {
                        return Err(LakeError::DependencyMismatch {
                            name: self.name.clone(),
                            reason: format!(
                                "revision mismatch (required {}, manifest has {})",
                                req_rev, g.rev
                            ),
                        });
                    }
                }

                if let Some(version_req) = &self.version {
                    let req = VersionReq::parse(version_req).map_err(|e| {
                        LakeError::InvalidConfig(format!(
                            "invalid version requirement for {}: {}",
                            self.name, e
                        ))
                    })?;

                    let version =
                        Version::parse(&g.rev).map_err(|_| LakeError::DependencyMismatch {
                            name: self.name.clone(),
                            reason: format!(
                                "manifest revision '{}' is not a semantic version",
                                g.rev
                            ),
                        })?;

                    if !req.matches(&version) {
                        return Err(LakeError::DependencyMismatch {
                            name: self.name.clone(),
                            reason: format!(
                                "version constraint {version_req} not satisfied by {version}"
                            ),
                        });
                    }
                }

                Ok(())
            }
            ManifestPackage::Path(p) => {
                if self.git.is_some() || self.rev.is_some() {
                    return Err(LakeError::DependencyMismatch {
                        name: self.name.clone(),
                        reason: "expected git dependency, manifest has path".to_string(),
                    });
                }
                if let Some(expected) = &self.path {
                    if Path::new(&p.path) != expected.as_path() {
                        return Err(LakeError::DependencyMismatch {
                            name: self.name.clone(),
                            reason: format!(
                                "path mismatch (expected {}, found {})",
                                expected.display(),
                                p.path
                            ),
                        });
                    }
                }
                if self.version.is_some() {
                    return Err(LakeError::DependencyMismatch {
                        name: self.name.clone(),
                        reason: "version constraints are not supported for path dependencies"
                            .to_string(),
                    });
                }
                Ok(())
            }
        }
    }

    fn normalize_git_url(url: &str) -> String {
        url.trim_end_matches(".git")
            .trim_end_matches('/')
            .to_string()
    }
}

#[cfg(test)]
mod tests;
