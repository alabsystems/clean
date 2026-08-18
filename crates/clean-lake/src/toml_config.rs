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
        #[allow(dead_code)]
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
    #[allow(dead_code)]
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

        match self.git {
            Some(RawGit::Url(url)) => git = Some(url),
            Some(RawGit::Table { url, rev: r, .. }) => {
                git = Some(url);
                if rev.is_none() {
                    rev = r;
                }
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
                }
                Some("path") if path.is_none() => {
                    path = src.dir;
                }
                _ => {}
            }
        }

        Dependency {
            name: self.name,
            git,
            rev,
            path: path.map(PathBuf::from),
            version: self.version,
        }
    }
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
    pub fn load_toml(lakefile_path: &Path) -> LakeResult<Self> {
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
mod tests {
    use super::*;

    /// The canonical Mathlib-dependent template emitted by Lake's own
    /// `lake init … math` (verified against `src/lake/Lake/CLI/Init.lean`).
    #[test]
    fn parse_mathlib_template() {
        let content = r#"
name = "myproject"
version = "0.1.0"
keywords = ["math"]
defaultTargets = ["MyProject"]

[leanOptions]
pp.unicode.fun = true
relaxedAutoImplicit = false

[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "v4.30.0"

[[lean_lib]]
name = "MyProject"
"#;
        let cfg = LakeConfig::parse_toml(content).expect("template must parse");
        assert_eq!(cfg.package.name, "myproject");
        assert_eq!(cfg.package.version.as_deref(), Some("0.1.0"));
        assert_eq!(cfg.default_targets, vec!["MyProject".to_string()]);

        assert_eq!(cfg.package.dependencies.len(), 1);
        let dep = &cfg.package.dependencies[0];
        assert_eq!(dep.name, "mathlib");
        // `rev` with no explicit git/version is preserved as the revision.
        assert_eq!(dep.rev.as_deref(), Some("v4.30.0"));

        assert_eq!(cfg.libs.len(), 1);
        assert_eq!(cfg.libs[0].name, "MyProject");
        // Root defaults to the lib name when `roots` is omitted.
        assert_eq!(cfg.libs[0].roots, vec!["MyProject".to_string()]);
    }

    #[test]
    fn parse_exe_with_default_root() {
        let content = r#"
name = "tool"
defaultTargets = ["tool"]

[[lean_exe]]
name = "tool"
"#;
        let cfg = LakeConfig::parse_toml(content).expect("exe lakefile must parse");
        assert_eq!(cfg.exes.len(), 1);
        assert_eq!(cfg.exes[0].name, "tool");
        // Executable root defaults to the exe name.
        assert_eq!(cfg.exes[0].root, "tool");
    }

    #[test]
    fn parse_require_git_string_and_path_forms() {
        let content = r#"
name = "p"

[[require]]
name = "depgit"
git = "https://github.com/example/dep"
rev = "abc123"

[[require]]
name = "deplocal"
path = "../local-dep"
"#;
        let cfg = LakeConfig::parse_toml(content).expect("git/path requires must parse");
        assert_eq!(cfg.package.dependencies.len(), 2);

        let g = &cfg.package.dependencies[0];
        assert_eq!(g.git.as_deref(), Some("https://github.com/example/dep"));
        assert_eq!(g.rev.as_deref(), Some("abc123"));

        let p = &cfg.package.dependencies[1];
        assert_eq!(p.path.as_deref(), Some(Path::new("../local-dep")));
        assert!(p.git.is_none());
    }

    #[test]
    fn parse_require_git_table_form() {
        let content = r#"
name = "p"

[[require]]
name = "deptable"
git = { url = "https://github.com/example/dep", rev = "deadbeef" }
"#;
        let cfg = LakeConfig::parse_toml(content).expect("git-table require must parse");
        let d = &cfg.package.dependencies[0];
        assert_eq!(d.git.as_deref(), Some("https://github.com/example/dep"));
        assert_eq!(d.rev.as_deref(), Some("deadbeef"));
    }

    #[test]
    fn parse_require_source_table_form() {
        let content = r#"
name = "p"

[[require]]
name = "depsrc"

[require.source]
type = "git"
url = "https://github.com/example/src"
rev = "f00"
"#;
        let cfg = LakeConfig::parse_toml(content).expect("source-table require must parse");
        let d = &cfg.package.dependencies[0];
        assert_eq!(d.git.as_deref(), Some("https://github.com/example/src"));
        assert_eq!(d.rev.as_deref(), Some("f00"));
    }

    /// Forward-compatibility: unknown top-level and per-target keys must be
    /// ignored, not rejected, so a newer `lakefile.toml` still loads.
    #[test]
    fn unknown_keys_are_ignored() {
        let content = r#"
name = "p"
someFutureKey = "whatever"
platformIndependent = true

[[lean_lib]]
name = "L"
futureLibKey = 42
"#;
        let cfg = LakeConfig::parse_toml(content).expect("unknown keys must be tolerated");
        assert_eq!(cfg.package.name, "p");
        assert_eq!(cfg.libs[0].name, "L");
    }

    #[test]
    fn explicit_roots_and_globs_preserved() {
        let content = r#"
name = "p"

[[lean_lib]]
name = "L"
srcDir = "src"
roots = ["L", "L.Extra"]
globs = ["L.+"]
"#;
        let cfg = LakeConfig::parse_toml(content).expect("lib with roots/globs must parse");
        let lib = &cfg.libs[0];
        assert_eq!(lib.roots, vec!["L".to_string(), "L.Extra".to_string()]);
        assert_eq!(lib.globs, vec!["L.+".to_string()]);
        assert_eq!(lib.src_dir.as_deref(), Some(Path::new("src")));
    }

    #[test]
    fn toolchain_falls_back_to_lean_version() {
        let content = r#"
name = "p"
toolchain = "leanprover/lean4:v4.30.0-rc2"
"#;
        let cfg = LakeConfig::parse_toml(content).expect("toolchain key must parse");
        assert_eq!(
            cfg.package.lean_version.as_deref(),
            Some("leanprover/lean4:v4.30.0-rc2")
        );
    }
}
