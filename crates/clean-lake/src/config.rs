// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lake configuration parsing
//!
//! Parses lakefile.lean to extract package configuration.

use crate::error::{LakeError, LakeResult};
use crate::interpolate::{contains_reference, InterpContext};
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
    /// Extra compiler options
    pub more_lean_args: Vec<String>,
    /// Extra linker options
    pub more_link_args: Vec<String>,
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
    pub fn load_with_mode(lakefile_path: &Path, mode: LakefileParseMode) -> LakeResult<Self> {
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

    /// Parse lakefile.lean content with an explicit handling mode for
    /// unrecognized top-level constructs
    pub fn parse_with_mode(content: &str, mode: LakefileParseMode) -> LakeResult<Self> {
        let mut config = LakeConfig::default();

        // Parse Lean surface syntax and extract DSL constructs
        // This is a simplified parser - a full implementation would use clean-parser

        let lines: Vec<&str> = content.lines().collect();
        let mut i = 0;
        // Track if the next declaration should be marked as default target
        let mut next_is_default = false;

        while i < lines.len() {
            let line = lines[i].trim();

            // Skip comments and empty lines
            if line.is_empty()
                || line.starts_with("--")
                || line.starts_with("import")
                || line.starts_with("open ")
            {
                i += 1;
                continue;
            }

            // Skip block comments (`/- … -/`, including `/--` doc comments and
            // `/-!` module docs), which may span multiple lines. Nested block
            // comments are not modeled; lakefiles do not use them in practice.
            if line.starts_with("/-") {
                while i < lines.len() && !lines[i].contains("-/") {
                    i += 1;
                }
                // Move past the line carrying the terminator (or the end of
                // the file when the comment is unterminated).
                i += 1;
                continue;
            }

            if let Some(dep) = Self::parse_require_line(line) {
                config.package.dependencies.push(dep);
                i += 1;
                continue;
            }

            // Parse package declaration
            if let Some(rest) = line.strip_prefix("package ") {
                let rest = rest.trim();
                // Handle "package name where" or "package name"
                let name = if let Some(idx) = rest.find(" where") {
                    &rest[..idx]
                } else {
                    rest.trim()
                };
                config.package.name = name.to_string();

                // Parse package block if present
                if rest.contains("where") {
                    i += 1;
                    while i < lines.len() {
                        let block_line = lines[i].trim();
                        if block_line.is_empty() || block_line.starts_with("--") {
                            i += 1;
                            continue;
                        }
                        if Self::skip_block_comment(&lines, &mut i) {
                            continue;
                        }
                        // Check for next top-level declaration
                        if !block_line.starts_with("--")
                            && (block_line.starts_with("@[")
                                || block_line.starts_with("require ")
                                || block_line.starts_with("lean_lib")
                                || block_line.starts_with("lean_exe")
                                || block_line.starts_with("lean_test")
                                || block_line.starts_with("script")
                                || block_line.starts_with("package"))
                        {
                            break;
                        }
                        // Parse package fields
                        if !Self::parse_package_field(&mut config.package, block_line) {
                            Self::record_unknown_block_field(
                                &mut config.diagnostics,
                                i,
                                block_line,
                            );
                        }
                        i += 1;
                    }
                    continue;
                }
                i += 1;
                continue;
            }

            // Parse @[default_target] attribute - affects next declaration
            if line.starts_with("@[default_target]") {
                next_is_default = true;
                i += 1;
                continue;
            }

            // Parse lean_lib declaration
            if let Some(rest) = line.strip_prefix("lean_lib ") {
                let rest = rest.trim();
                let name = Self::parse_decl_name(rest);

                let mut lib = LeanLib {
                    name: name.to_string(),
                    ..Default::default()
                };

                // Parse lib block if present
                if rest.contains("where") {
                    i += 1;
                    while i < lines.len() {
                        let block_line = lines[i].trim();
                        if block_line.is_empty() || block_line.starts_with("--") {
                            i += 1;
                            continue;
                        }
                        if Self::skip_block_comment(&lines, &mut i) {
                            continue;
                        }
                        // Check for next top-level declaration
                        if !block_line.starts_with("--")
                            && (block_line.starts_with("@[")
                                || block_line.starts_with("require ")
                                || block_line.starts_with("lean_lib")
                                || block_line.starts_with("lean_exe")
                                || block_line.starts_with("lean_test")
                                || block_line.starts_with("script")
                                || block_line.starts_with("package"))
                        {
                            break;
                        }
                        if !Self::parse_lib_field(&mut lib, block_line) {
                            Self::record_unknown_block_field(
                                &mut config.diagnostics,
                                i,
                                block_line,
                            );
                        }
                        i += 1;
                    }
                } else {
                    i += 1;
                }

                if next_is_default {
                    config.default_targets.push(lib.name.clone());
                    next_is_default = false;
                }
                config.libs.push(lib);
                continue;
            }

            // Parse lean_exe declaration
            if let Some(rest) = line.strip_prefix("lean_exe ") {
                let rest = rest.trim();
                let name = Self::parse_decl_name(rest);

                let mut exe = LeanExe {
                    name: name.to_string(),
                    ..Default::default()
                };

                // Parse exe block if present
                if rest.contains("where") {
                    i += 1;
                    while i < lines.len() {
                        let block_line = lines[i].trim();
                        if block_line.is_empty() || block_line.starts_with("--") {
                            i += 1;
                            continue;
                        }
                        if Self::skip_block_comment(&lines, &mut i) {
                            continue;
                        }
                        // Check for next top-level declaration
                        if !block_line.starts_with("--")
                            && (block_line.starts_with("@[")
                                || block_line.starts_with("require ")
                                || block_line.starts_with("lean_lib")
                                || block_line.starts_with("lean_exe")
                                || block_line.starts_with("lean_test")
                                || block_line.starts_with("script")
                                || block_line.starts_with("package"))
                        {
                            break;
                        }
                        if !Self::parse_exe_field(&mut exe, block_line) {
                            Self::record_unknown_block_field(
                                &mut config.diagnostics,
                                i,
                                block_line,
                            );
                        }
                        i += 1;
                    }
                } else {
                    i += 1;
                }

                if next_is_default {
                    config.default_targets.push(exe.name.clone());
                    next_is_default = false;
                }
                config.exes.push(exe);
                continue;
            }

            // Parse lean_test declaration
            if let Some(rest) = line.strip_prefix("lean_test ") {
                let rest = rest.trim();
                let name = if let Some(idx) = rest.find(" where") {
                    &rest[..idx]
                } else {
                    rest.trim()
                };

                let mut test = LeanTest {
                    name: name.to_string(),
                    ..Default::default()
                };

                // Parse test block if present
                if rest.contains("where") {
                    i += 1;
                    while i < lines.len() {
                        let block_line = lines[i].trim();
                        if block_line.is_empty() || block_line.starts_with("--") {
                            i += 1;
                            continue;
                        }
                        if Self::skip_block_comment(&lines, &mut i) {
                            continue;
                        }
                        // Check for next top-level declaration
                        if !block_line.starts_with("--")
                            && (block_line.starts_with("@[")
                                || block_line.starts_with("require ")
                                || block_line.starts_with("lean_lib")
                                || block_line.starts_with("lean_exe")
                                || block_line.starts_with("lean_test")
                                || block_line.starts_with("script")
                                || block_line.starts_with("package"))
                        {
                            break;
                        }
                        if !Self::parse_test_field(&mut test, block_line) {
                            Self::record_unknown_block_field(
                                &mut config.diagnostics,
                                i,
                                block_line,
                            );
                        }
                        i += 1;
                    }
                } else {
                    i += 1;
                }

                config.tests.push(test);
                continue;
            }

            // Parse script declaration
            if let Some(rest) = line.strip_prefix("script ") {
                let header = Self::split_script_header(rest);

                let mut script = LakeScript {
                    name: header.name.to_string(),
                    args: header.args.map(str::to_string),
                    ..Default::default()
                };

                // Parse script block if present
                if header.has_block {
                    i += 1;
                    // A `do` (or an inline `:=` term) on the header line is
                    // the first line of the body, not decoration: dropping it
                    // turns `script s := do` into a bare statement sequence.
                    let mut body_lines: Vec<String> =
                        header.inline_body.map(str::to_string).into_iter().collect();
                    while i < lines.len() {
                        let block_line = lines[i].trim();
                        if block_line.is_empty() {
                            i += 1;
                            continue;
                        }
                        // The block ends at the first line that returns to
                        // column 0: a script body is indented under its
                        // header, and swallowing the next declaration would
                        // both corrupt the body and hide that declaration from
                        // the skipped-construct diagnostics.
                        if !lines[i].starts_with(|c: char| c.is_whitespace()) {
                            break;
                        }
                        // Check for next top-level declaration
                        if !block_line.starts_with("--")
                            && (block_line.starts_with("@[")
                                || block_line.starts_with("require ")
                                || block_line.starts_with("lean_lib")
                                || block_line.starts_with("lean_exe")
                                || block_line.starts_with("lean_test")
                                || block_line.starts_with("script")
                                || block_line.starts_with("package"))
                        {
                            break;
                        }
                        // Collect script body
                        if let Some(doc_rest) = block_line.strip_prefix("doc :=") {
                            script.doc = Some(doc_rest.trim().trim_matches('"').to_string());
                        } else if !block_line.starts_with("--") {
                            body_lines.push(block_line.to_string());
                        }
                        i += 1;
                    }
                    script.body = body_lines.join("\n");
                } else {
                    i += 1;
                }

                config.scripts.push(script);
                continue;
            }

            // Unrecognized line: the declarative subset cannot model it.
            // Account for every skipped TOP-LEVEL construct (column-0 lines
            // that are not a dangling closing bracket) so nothing is dropped
            // silently; indented lines are continuations of the construct
            // already recorded and are skipped without their own entry.
            let starts_indented = lines[i].starts_with(|c: char| c.is_whitespace());
            let leading = line.split_whitespace().next().unwrap_or_default();
            let is_closing_bracket = matches!(leading, "]" | ")" | "}");
            if !starts_indented && !is_closing_bracket && !leading.is_empty() {
                config.diagnostics.push(SkippedConstruct {
                    line: i + 1,
                    token: leading.to_string(),
                    text: line.to_string(),
                });
            }
            i += 1;
        }

        // Strict mode: any unrecognized top-level construct is a hard error,
        // so programmatic lakefiles can no longer silently under-parse.
        if mode == LakefileParseMode::Strict && !config.diagnostics.is_empty() {
            let summary = config
                .diagnostics
                .iter()
                .map(|skipped| format!("line {}: `{}`", skipped.line, skipped.token))
                .collect::<Vec<_>>()
                .join(", ");
            return Err(LakeError::UnrecognizedConstructs {
                count: config.diagnostics.len(),
                summary,
            });
        }

        // Validate configuration
        if config.package.name.is_empty() {
            return Err(LakeError::MissingField {
                field: "name".to_string(),
                context: "package".to_string(),
            });
        }

        // Expand variable references (`$(VAR)` / `${VAR}`) in string values,
        // resolving against built-in variables and the process environment.
        config.interpolate()?;

        Ok(config)
    }

    /// Expand `$(VAR)` / `${VAR}` references in string configuration values.
    ///
    /// Built-in variables (`PACKAGE_NAME`, plus the package version when set)
    /// are seeded into the resolution context; unresolved names fall back to
    /// process environment variables. Unknown names and reference cycles raise a
    /// typed error rather than silently expanding to nothing.
    fn interpolate(&mut self) -> LakeResult<()> {
        let mut ctx = InterpContext::new();
        // The package name is resolved before interpolation runs, so it can be
        // exposed as a built-in for other values to reference.
        ctx.set("PACKAGE_NAME", self.package.name.clone());
        if let Some(version) = &self.package.version {
            ctx.set("PACKAGE_VERSION", version.clone());
        }

        // Package-level string fields.
        expand_opt(&ctx, &mut self.package.version)?;
        expand_opt(&ctx, &mut self.package.description)?;
        expand_opt(&ctx, &mut self.package.lean_version)?;
        expand_opt_path(&ctx, &mut self.package.src_dir)?;
        expand_opt_path(&ctx, &mut self.package.build_dir)?;
        expand_vec(&ctx, &mut self.package.more_lean_args)?;
        expand_vec(&ctx, &mut self.package.more_link_args)?;

        for dep in &mut self.package.dependencies {
            expand_opt(&ctx, &mut dep.git)?;
            expand_opt(&ctx, &mut dep.rev)?;
            expand_opt(&ctx, &mut dep.version)?;
            expand_opt_path(&ctx, &mut dep.path)?;
        }

        for lib in &mut self.libs {
            expand_vec(&ctx, &mut lib.globs)?;
            expand_vec(&ctx, &mut lib.more_lean_args)?;
            expand_vec(&ctx, &mut lib.default_facets)?;
            expand_vec(&ctx, &mut lib.pre_compile_hooks)?;
            expand_opt_path(&ctx, &mut lib.src_dir)?;
        }

        for exe in &mut self.exes {
            expand_vec(&ctx, &mut exe.more_lean_args)?;
            expand_vec(&ctx, &mut exe.more_link_args)?;
            expand_vec(&ctx, &mut exe.supported_backends)?;
            expand_opt_path(&ctx, &mut exe.src_dir)?;
        }

        for test in &mut self.tests {
            expand_vec(&ctx, &mut test.more_lean_args)?;
            expand_opt_path(&ctx, &mut test.src_dir)?;
        }

        Ok(())
    }

    /// Parse a field in the package block.
    ///
    /// Returns `false` when the field name is not in the modelled set, so the
    /// caller can account for it instead of dropping it. See
    /// [`LakeConfig::record_unknown_block_field`].
    fn parse_package_field(package: &mut PackageConfig, line: &str) -> bool {
        if let Some(rest) = line.strip_prefix("version :=") {
            package.version = Some(rest.trim().trim_matches('"').to_string());
        } else if let Some(rest) = line.strip_prefix("description :=") {
            package.description = Some(rest.trim().trim_matches('"').to_string());
        } else if let Some(rest) = line.strip_prefix("srcDir :=") {
            package.src_dir = Some(PathBuf::from(rest.trim().trim_matches('"')));
        } else if let Some(rest) = line.strip_prefix("buildDir :=") {
            package.build_dir = Some(PathBuf::from(rest.trim().trim_matches('"')));
        } else if let Some(rest) = line.strip_prefix("leanVersion :=") {
            package.lean_version = Some(rest.trim().trim_matches('"').to_string());
        } else if let Some(rest) = line.strip_prefix("dependencies :=") {
            let deps = Self::parse_dependency_array(rest.trim());
            package.dependencies.extend(deps);
        } else if let Some(rest) = line.strip_prefix("moreLeanArgs :=") {
            package.more_lean_args = Self::parse_string_array(rest.trim());
        } else if let Some(rest) = line.strip_prefix("moreLinkArgs :=") {
            package.more_link_args = Self::parse_string_array(rest.trim());
        } else {
            return false;
        }
        true
    }

    /// Parse a field in a lean_lib block.
    ///
    /// Returns `false` for a field name outside the modelled set.
    fn parse_lib_field(lib: &mut LeanLib, line: &str) -> bool {
        if let Some(rest) = line.strip_prefix("roots :=") {
            // Parse #[`Module1, `Module2] syntax
            lib.roots = Self::parse_name_array(rest.trim());
        } else if let Some(rest) = line.strip_prefix("globs :=") {
            lib.globs = Self::parse_string_array(rest.trim());
        } else if let Some(rest) = line.strip_prefix("srcDir :=") {
            lib.src_dir = Some(PathBuf::from(rest.trim().trim_matches('"')));
        } else if let Some(rest) = line.strip_prefix("defaultFacets :=") {
            lib.default_facets = Self::parse_string_array(rest.trim());
        } else if let Some(rest) = line.strip_prefix("preCompileHooks :=") {
            lib.pre_compile_hooks = Self::parse_string_array(rest.trim());
        } else {
            return false;
        }
        true
    }

    /// Parse a field in a lean_exe block.
    ///
    /// Returns `false` for a field name outside the modelled set.
    fn parse_exe_field(exe: &mut LeanExe, line: &str) -> bool {
        if let Some(rest) = line.strip_prefix("root :=") {
            exe.root = rest.trim().trim_start_matches('`').to_string();
        } else if let Some(rest) = line.strip_prefix("srcDir :=") {
            exe.src_dir = Some(PathBuf::from(rest.trim().trim_matches('"')));
        } else if let Some(rest) = line.strip_prefix("supportedBackends :=") {
            exe.supported_backends = Self::parse_string_array(rest.trim());
        } else {
            return false;
        }
        true
    }

    /// Parse a field in a lean_test block.
    ///
    /// Returns `false` for a field name outside the modelled set.
    fn parse_test_field(test: &mut LeanTest, line: &str) -> bool {
        if let Some(rest) = line.strip_prefix("root :=") {
            test.root = rest.trim().trim_start_matches('`').to_string();
        } else if let Some(rest) = line.strip_prefix("srcDir :=") {
            test.src_dir = Some(PathBuf::from(rest.trim().trim_matches('"')));
        } else {
            return false;
        }
        true
    }

    /// Skip a `/- … -/` or `/-- … -/` comment starting at `lines[*i]`,
    /// advancing `*i` past its closing delimiter.
    ///
    /// Returns `true` when a comment was consumed. Lake allows doc comments and
    /// section headers inside a `where` block, and the block loops previously
    /// filtered only `--` line comments, so these lines reached the field
    /// parsers and were silently ignored. Once an unmodelled field becomes a
    /// diagnostic, ignoring them is no longer harmless: `/-! ## Libraries -/`
    /// would be reported as a dropped field. Comments are not fields, so they
    /// are consumed here rather than accounted for.
    fn skip_block_comment(lines: &[&str], i: &mut usize) -> bool {
        let start = lines[*i].trim();
        if !start.starts_with("/-") {
            return false;
        }
        // A comment that opens and closes on its own line consumes just that
        // line; `/-` alone is not a closing delimiter for its own opener.
        if start.len() > 2 && start.ends_with("-/") {
            *i += 1;
            return true;
        }
        *i += 1;
        while *i < lines.len() {
            let line = lines[*i].trim();
            *i += 1;
            if line.ends_with("-/") {
                break;
            }
        }
        true
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

    /// Account for a `where`-block field the declarative subset does not model.
    ///
    /// Lake configuration lives as much INSIDE `where` blocks as at column 0,
    /// and a dropped `testDriver` or `leanOptions` is not a cosmetic loss: it
    /// silently changes what gets built and how. These entries therefore go
    /// into the same [`LakeConfig::diagnostics`] as top-level skips, so
    /// `CLEAN_LAKE_STRICT_LAKEFILE=1` refuses them too and the lenient path
    /// still warns rather than under-parsing in silence.
    ///
    /// A `where` block is entered only after blank lines and `--` comments are
    /// filtered and after the next top-level construct has been ruled out, so
    /// every line reaching here is a real field the parser chose not to model.
    fn record_unknown_block_field(
        diagnostics: &mut Vec<SkippedConstruct>,
        line_index: usize,
        line: &str,
    ) {
        let leading = line
            .split_whitespace()
            .next()
            .unwrap_or_default()
            .trim_end_matches(":=");
        if leading.is_empty() || matches!(leading, "]" | ")" | "}") {
            return;
        }
        diagnostics.push(SkippedConstruct {
            line: line_index + 1,
            token: leading.to_string(),
            text: line.to_string(),
        });
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
    pub fn src_dir(&self) -> PathBuf {
        self.package
            .src_dir
            .clone()
            .unwrap_or_else(|| PathBuf::from("."))
    }

    /// Get the build directory for the package
    #[must_use]
    pub fn build_dir(&self) -> PathBuf {
        self.package
            .build_dir
            .clone()
            .unwrap_or_else(|| PathBuf::from(".lake/build"))
    }

    /// Validate that declared dependencies are satisfied by the manifest
    pub fn validate_manifest(&self, manifest: &LakeManifest) -> LakeResult<()> {
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
    pub fn validate_manifest(&self, manifest: &LakeManifest) -> LakeResult<()> {
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
    pub fn root_modules(&self) -> Vec<String> {
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
    pub fn matches_manifest(&self, pkg: &ManifestPackage) -> LakeResult<()> {
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

/// Expand variable references in an optional string field in place.
fn expand_opt(ctx: &InterpContext, value: &mut Option<String>) -> LakeResult<()> {
    if let Some(s) = value {
        if contains_reference(s) {
            *s = ctx.expand(s)?;
        }
    }
    Ok(())
}

/// Expand variable references in an optional path field in place.
fn expand_opt_path(ctx: &InterpContext, value: &mut Option<PathBuf>) -> LakeResult<()> {
    if let Some(path) = value {
        let original = path.to_string_lossy();
        if contains_reference(&original) {
            let expanded = ctx.expand(&original)?;
            *path = PathBuf::from(expanded);
        }
    }
    Ok(())
}

/// Expand variable references across each entry of a string vector in place.
fn expand_vec(ctx: &InterpContext, values: &mut [String]) -> LakeResult<()> {
    for value in values.iter_mut() {
        if contains_reference(value) {
            *value = ctx.expand(value)?;
        }
    }
    Ok(())
}

/// Tokenize a require line, treating "/" and "@" as separate tokens
fn tokenize_require(input: &str) -> Vec<String> {
    let mut tokens = vec![];
    let mut current = String::new();
    let mut in_quote = false;

    for c in input.chars() {
        match c {
            '"' => {
                in_quote = !in_quote;
                current.push(c);
            }
            '/' if !in_quote => {
                if !current.is_empty() {
                    tokens.push(current.clone());
                    current.clear();
                }
                tokens.push("/".to_string());
            }
            '@' if !in_quote => {
                if !current.is_empty() {
                    tokens.push(current.clone());
                    current.clear();
                }
                tokens.push("@".to_string());
            }
            ch if ch.is_whitespace() && !in_quote => {
                if !current.is_empty() {
                    tokens.push(current.clone());
                    current.clear();
                }
            }
            _ => current.push(c),
        }
    }

    if !current.is_empty() {
        tokens.push(current);
    }

    tokens
}

impl LakeConfig {
    fn parse_require_line(line: &str) -> Option<Dependency> {
        if !line.starts_with("require ") {
            return None;
        }

        let rest = line.strip_prefix("require ")?.trim();
        // Stop at "with" clause or line comment
        let rest = rest.split(" with ").next()?.trim();
        let rest = rest.split(" -- ").next()?.trim();
        let tokens = tokenize_require(rest);
        if tokens.is_empty() {
            return None;
        }

        let mut iter = tokens.into_iter().peekable();
        let mut dep = Dependency::default();

        // Parse the name: either "owner" / "repo" format or just name
        let first = iter.next()?;

        // Check if it's the new "owner" / "repo" format
        if iter.peek().map(String::as_str) == Some("/") {
            // New format: "owner" / "repo"
            let owner = first.trim_matches('"');
            iter.next(); // consume "/"
            let repo_str = iter.next()?;
            let repo = repo_str.trim_matches('"');
            dep.name = repo.to_string();
            // Construct github URL from owner/repo
            dep.git = Some(format!("https://github.com/{owner}/{repo}"));
        } else {
            // Old format: just name
            dep.name = first;
        }

        while let Some(tok) = iter.next() {
            match tok.as_str() {
                "from" => {
                    if let Some(source) = iter.next() {
                        match source.as_str() {
                            "git" => {
                                dep.git = iter.next().map(|s| s.trim_matches('"').to_string());
                            }
                            "path" => {
                                dep.path = iter.next().map(|s| PathBuf::from(s.trim_matches('"')));
                            }
                            _ => {}
                        }
                    }
                }
                "@" => {
                    // New format: @ git "branch" or old format @ "version"
                    if let Some(val) = iter.next() {
                        if val == "git" {
                            // @ git "branch" format (new Mathlib style)
                            if let Some(branch) = iter.next() {
                                dep.rev = Some(branch.trim_matches('"').to_string());
                            }
                        } else {
                            // @ "version" or @ "rev" format
                            let cleaned = val.trim_matches('"');
                            if VersionReq::parse(cleaned).is_ok() {
                                dep.version = Some(cleaned.to_string());
                            } else {
                                dep.rev = Some(cleaned.to_string());
                            }
                        }
                    }
                }
                _ => {}
            }
        }

        Some(dep)
    }

    /// Extract name from lean_lib/lean_exe declaration, handling guillemet names
    fn parse_decl_name(rest: &str) -> &str {
        let rest = rest.trim();
        // Handle guillemet names: «name» -> name
        // « is U+00AB (2 bytes in UTF-8), » is U+00BB (2 bytes in UTF-8)
        if rest.starts_with('«') {
            if let Some(end_char_idx) = rest.find('»') {
                // Get byte index after the opening «
                let start_byte = '«'.len_utf8();
                return &rest[start_byte..end_char_idx];
            }
        }
        // Regular name extraction
        if let Some(idx) = rest.find(" where") {
            &rest[..idx]
        } else {
            rest.split_whitespace()
                .next()
                .unwrap_or_else(|| rest.trim())
        }
    }

    fn parse_dependency_array(spec: &str) -> Vec<Dependency> {
        // Very small parser for #[{ name := "...", git := "...", rev := "..." }, ...]
        // Primarily for tests and simple lakefile usage
        let mut deps = vec![];
        let trimmed = spec.trim();
        if !trimmed.starts_with("#[") || !trimmed.ends_with(']') {
            return deps;
        }

        let inner = &trimmed[2..trimmed.len() - 1];
        for entry in inner.split("},") {
            let mut dep = Dependency::default();
            for field in entry.split(',') {
                let kv: Vec<_> = field.split(":=").map(str::trim).collect();
                if kv.len() != 2 {
                    continue;
                }
                match kv[0] {
                    "name" => dep.name = kv[1].trim_matches('"').to_string(),
                    "git" => dep.git = Some(kv[1].trim_matches('"').to_string()),
                    "rev" => dep.rev = Some(kv[1].trim_matches('"').to_string()),
                    "path" => dep.path = Some(PathBuf::from(kv[1].trim_matches('"'))),
                    "version" => dep.version = Some(kv[1].trim_matches('"').to_string()),
                    _ => {}
                }
            }
            if !dep.name.is_empty() {
                deps.push(dep);
            }
        }

        deps
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::manifest::{GitPackage, LakeManifestVersion};

    #[test]
    fn test_parse_minimal_lakefile() {
        let content = r"
import Lake
open Lake DSL

package test
lean_lib Test
";
        let config = LakeConfig::parse(content).unwrap();
        assert_eq!(config.package.name, "test");
        assert_eq!(config.libs.len(), 1);
        assert_eq!(config.libs[0].name, "Test");
    }

    #[test]
    fn test_parse_lakefile_with_where() {
        let content = r#"
import Lake
open Lake DSL

package myproject where
  version := "0.1.0"

@[default_target]
lean_lib MyLib where
  roots := #[`MyLib]

lean_exe myexe where
  root := `Main
"#;
        let config = LakeConfig::parse(content).unwrap();
        assert_eq!(config.package.name, "myproject");
        assert_eq!(config.package.version, Some("0.1.0".to_string()));
        assert_eq!(config.libs.len(), 1);
        assert_eq!(config.libs[0].name, "MyLib");
        assert_eq!(config.libs[0].roots, vec!["MyLib"]);
        assert_eq!(config.exes.len(), 1);
        assert_eq!(config.exes[0].name, "myexe");
        assert_eq!(config.exes[0].root, "Main");
        assert_eq!(config.default_targets, vec!["MyLib"]);
    }

    #[test]
    fn test_parse_name_array() {
        assert_eq!(
            LakeConfig::parse_name_array("#[`A, `B, `C]"),
            vec!["A", "B", "C"]
        );
        assert_eq!(LakeConfig::parse_name_array("`Single"), vec!["Single"]);
    }

    #[test]
    fn test_package_config_minimal() {
        let pkg = PackageConfig::minimal("test");
        assert_eq!(pkg.name, "test");
        assert!(
            pkg.version.is_none(),
            "minimal package should have no version"
        );
    }

    #[test]
    fn test_parse_more_lean_args() {
        let content = r#"
import Lake
open Lake DSL

package test where
  moreLeanArgs := #["-DautoImplicit=false", "-Dpp.all"]
  moreLinkArgs := #["-L/usr/local/lib", "-lmylib"]

lean_lib Test
"#;
        let config = LakeConfig::parse(content).unwrap();
        assert_eq!(config.package.name, "test");
        assert_eq!(
            config.package.more_lean_args,
            vec!["-DautoImplicit=false", "-Dpp.all"]
        );
        assert_eq!(
            config.package.more_link_args,
            vec!["-L/usr/local/lib", "-lmylib"]
        );
    }

    #[test]
    fn test_lean_lib_root_modules() {
        let lib = LeanLib::minimal("MyLib");
        assert_eq!(lib.root_modules(), vec!["MyLib"]);

        let lib_with_roots = LeanLib {
            name: "MyLib".to_string(),
            roots: vec!["MyLib.Core".to_string(), "MyLib.Utils".to_string()],
            ..Default::default()
        };
        assert_eq!(
            lib_with_roots.root_modules(),
            vec!["MyLib.Core", "MyLib.Utils"]
        );
    }

    #[test]
    fn test_parse_require_git_dependency() {
        let content = r#"
import Lake
open Lake DSL

require std from git "https://github.com/leanprover/std4" @ "1.2.3"

package demo
lean_lib Demo
"#;
        let config = LakeConfig::parse(content).unwrap();
        assert_eq!(config.package.dependencies.len(), 1);
        let dep = &config.package.dependencies[0];
        assert_eq!(dep.name, "std");
        assert_eq!(
            dep.git.as_deref(),
            Some("https://github.com/leanprover/std4")
        );
        assert_eq!(dep.version.as_deref(), Some("1.2.3"));
    }

    #[test]
    fn test_validate_manifest_semver_constraint() {
        let dep = Dependency {
            name: "std".to_string(),
            git: Some("https://github.com/leanprover/std4".to_string()),
            rev: None,
            path: None,
            version: Some("^1.2".to_string()),
            scope: None,
            sub_dir: None,
        };

        let manifest = LakeManifest {
            version: LakeManifestVersion::Numeric(7),
            packages_dir: ".lake/packages".to_string(),
            packages: vec![ManifestPackage::Git(GitPackage {
                name: "std".to_string(),
                url: "https://github.com/leanprover/std4".to_string(),
                rev: "1.2.5".to_string(),
                input_rev: None,
                ..Default::default()
            })],
        };

        PackageConfig {
            name: "demo".to_string(),
            dependencies: vec![dep],
            ..Default::default()
        }
        .validate_manifest(&manifest)
        .unwrap();
    }

    #[test]
    fn test_validate_manifest_mismatch() {
        let dep = Dependency {
            name: "std".to_string(),
            git: Some("https://github.com/leanprover/std4".to_string()),
            rev: Some("main".to_string()),
            path: None,
            version: None,
            scope: None,
            sub_dir: None,
        };

        let manifest = LakeManifest {
            version: LakeManifestVersion::Numeric(7),
            packages_dir: ".lake/packages".to_string(),
            packages: vec![ManifestPackage::Git(GitPackage {
                name: "std".to_string(),
                url: "https://github.com/leanprover/std4".to_string(),
                rev: "dev-branch".to_string(),
                input_rev: None,
                ..Default::default()
            })],
        };

        let result = PackageConfig {
            name: "demo".to_string(),
            dependencies: vec![dep],
            ..Default::default()
        }
        .validate_manifest(&manifest);

        assert!(
            matches!(result, Err(LakeError::DependencyMismatch { .. })),
            "expected DependencyMismatch, got: {result:?}"
        );
    }

    #[test]
    fn test_parse_lakefile_with_tests() {
        let content = r"
import Lake
open Lake DSL

package myproject

lean_lib MyLib

lean_test mytest where
  root := `Test.Main

lean_test integration where
  root := `Test.Integration
";
        let config = LakeConfig::parse(content).unwrap();
        assert_eq!(config.package.name, "myproject");
        assert_eq!(config.libs.len(), 1);
        assert_eq!(config.tests.len(), 2);
        assert_eq!(config.tests[0].name, "mytest");
        assert_eq!(config.tests[0].root, "Test.Main");
        assert_eq!(config.tests[1].name, "integration");
        assert_eq!(config.tests[1].root, "Test.Integration");
    }

    #[test]
    fn test_lean_test_minimal() {
        let test = LeanTest::minimal("unit", "Test.Unit");
        assert_eq!(test.name, "unit");
        assert_eq!(test.root, "Test.Unit");
    }

    #[test]
    fn test_parse_lakefile_with_scripts() {
        let content = r#"
import Lake
open Lake DSL

package myproject

lean_lib MyLib

script hello where
  doc := "Prints hello"
  IO.println "Hello, World!"

script build_docs :=
  do
    IO.println "Building docs..."
    pure 0
"#;
        let config = LakeConfig::parse(content).unwrap();
        assert_eq!(config.package.name, "myproject");
        assert_eq!(config.scripts.len(), 2);
        assert_eq!(config.scripts[0].name, "hello");
        assert_eq!(config.scripts[0].doc, Some("Prints hello".to_string()));
        assert!(config.scripts[0].body.contains("IO.println"));
        assert_eq!(config.scripts[1].name, "build_docs");
        assert!(config.scripts[1].body.contains("Building docs"));
    }

    #[test]
    fn test_lake_script_default() {
        let script = LakeScript::default();
        assert!(script.name.is_empty());
        assert!(script.body.is_empty());
        assert!(
            script.doc.is_none(),
            "default LakeScript should have no doc"
        );
        assert!(
            script.args.is_none(),
            "default LakeScript should declare no argument binder"
        );
    }

    /// Lean's `script <name> do` form: the name is the NAME, and the body is
    /// kept.
    ///
    /// Measured 2026-08-27 against the shipped binary before this fix:
    /// `clean lake script list` printed `hello do` and `clean lake script doc
    /// "hello do"` printed an empty body — the whole header remainder became
    /// the name and every indented body line was dropped without a
    /// diagnostic (body lines are indented, so they are not recorded as
    /// skipped top-level constructs either).
    #[test]
    fn test_parse_script_do_form_keeps_name_and_body() {
        let content =
            "package demo\n\nscript hello do\n  IO.println \"hello\"\n  IO.println \"again\"\n";
        let config = LakeConfig::parse(content).expect("do-form script should parse");

        assert_eq!(config.scripts.len(), 1);
        assert_eq!(config.scripts[0].name, "hello", "name must not carry ` do`");
        assert_eq!(
            config.scripts[0].body, "do\nIO.println \"hello\"\nIO.println \"again\"",
            "the `do` opens the body and both statements must survive"
        );
        assert!(config.scripts[0].args.is_none());
    }

    /// `script <name> (args) do`: the binder is recorded, not folded into the
    /// name.
    #[test]
    fn test_parse_script_do_form_with_binder_records_binder_separately() {
        let content = "package demo\n\nscript greet (args) do\n  IO.println \"hi\"\n";
        let config = LakeConfig::parse(content).expect("binder do-form should parse");

        assert_eq!(config.scripts.len(), 1);
        assert_eq!(config.scripts[0].name, "greet");
        assert_eq!(config.scripts[0].args.as_deref(), Some("args"));
        assert!(config.scripts[0].body.contains("IO.println \"hi\""));
    }

    /// A name that merely ENDS in the letters `do` is not a `do` form.
    #[test]
    fn test_parse_script_name_ending_in_do_is_not_split() {
        let config = LakeConfig::parse("package demo\n\nscript tornado\n")
            .expect("bare script should parse");
        assert_eq!(config.scripts.len(), 1);
        assert_eq!(config.scripts[0].name, "tornado");
        assert!(config.scripts[0].body.is_empty());
    }

    /// `script <name> := do` puts the `do` on the header line; dropping it
    /// would leave a bare statement sequence that no longer sequences.
    #[test]
    fn test_parse_script_inline_assign_head_opens_the_body() {
        let content = "package demo\n\nscript build := do\n  IO.println \"building\"\n";
        let config = LakeConfig::parse(content).expect("`:= do` script should parse");

        assert_eq!(config.scripts.len(), 1);
        assert_eq!(config.scripts[0].name, "build");
        assert_eq!(
            config.scripts[0].body, "do\nIO.println \"building\"",
            "the header-line `do` must head the body"
        );
    }

    /// A single-expression `script <name> := <term>` keeps the term.
    #[test]
    fn test_parse_script_inline_assign_term_is_the_body() {
        let config = LakeConfig::parse("package demo\n\nscript p := IO.println \"x\"\n")
            .expect("inline-term script should parse");
        assert_eq!(config.scripts[0].name, "p");
        assert_eq!(config.scripts[0].body, "IO.println \"x\"");
    }

    /// A script block ends at column 0: a following declaration must not be
    /// swallowed into the body (and must still be accounted as skipped).
    #[test]
    fn test_parse_script_block_stops_at_column_zero() {
        let content =
            "package demo\n\nscript hello do\n  IO.println \"hi\"\n\ndef leftover := 1\n\nlean_lib MyLib\n";
        let config = LakeConfig::parse(content).expect("parse");

        assert_eq!(config.scripts.len(), 1);
        assert_eq!(config.scripts[0].body, "do\nIO.println \"hi\"");
        assert_eq!(
            config.libs.len(),
            1,
            "the lean_lib after the script is kept"
        );
        assert!(
            config
                .diagnostics
                .iter()
                .any(|d| d.token == "def" && d.text.contains("leftover")),
            "the dedented `def` is a skipped top-level construct, not script body: {:?}",
            config.diagnostics
        );
    }

    #[test]
    fn test_split_script_header_forms() {
        let do_form = LakeConfig::split_script_header("hello do");
        assert_eq!(do_form.name, "hello");
        assert_eq!(do_form.args, None);
        assert_eq!(do_form.inline_body, Some("do"));
        assert!(do_form.has_block);

        let binder = LakeConfig::split_script_header("greet (args) do");
        assert_eq!(binder.name, "greet");
        assert_eq!(binder.args, Some("args"));

        let where_form = LakeConfig::split_script_header("hello where");
        assert_eq!(where_form.name, "hello");
        assert_eq!(where_form.inline_body, None);
        assert!(where_form.has_block);

        let bare = LakeConfig::split_script_header("hello");
        assert_eq!(bare.name, "hello");
        assert!(!bare.has_block);
    }

    #[test]
    fn test_parse_mathlib_style_lakefile() {
        // Test parsing a Mathlib-style lakefile with modern require syntax
        let content = r#"
import Lake

open Lake DSL

/-!
## Dependencies
-/

require "leanprover-community" / "batteries" @ git "main"
require "leanprover-community" / "Qq" @ git "master"
require "leanprover-community" / "aesop" @ git "master"

package mathlib where
  testDriver := "MathlibTest"

/-!
## Libraries
-/

@[default_target]
lean_lib Mathlib where
  leanOptions := mathlibLeanOptions

lean_lib Cache
lean_lib LongestPole

lean_lib MathlibTest where
  globs := #[.submodules `MathlibTest]

/-- Documentation library -/
lean_lib docs where
  roots := #[`docs]

/-!
## Executables
-/

/-- Adds labels to PRs -/
lean_exe autolabel where
  srcDir := "scripts"

lean_exe cache where
  root := `Cache.Main

lean_exe «check-yaml» where
  srcDir := "scripts"
  supportInterpreter := true

lean_exe mk_all where
  srcDir := "scripts"
  supportInterpreter := true
  weakLinkArgs := #["-lLake"]
"#;
        let config = LakeConfig::parse(content).unwrap();

        // Check package
        assert_eq!(config.package.name, "mathlib");

        // Check dependencies - should parse "owner" / "repo" format
        assert!(
            config.package.dependencies.len() >= 3,
            "Expected at least 3 dependencies, got {}",
            config.package.dependencies.len()
        );

        // Check libraries
        assert!(
            config.libs.len() >= 5,
            "Expected at least 5 libraries, got {}",
            config.libs.len()
        );
        let lib_names: Vec<_> = config.libs.iter().map(|l| l.name.as_str()).collect();
        assert!(lib_names.contains(&"Mathlib"));
        assert!(lib_names.contains(&"Cache"));
        assert!(lib_names.contains(&"docs"));

        // Check executables - should handle guillemet names
        assert!(
            config.exes.len() >= 4,
            "Expected at least 4 executables, got {}",
            config.exes.len()
        );
        let exe_names: Vec<_> = config.exes.iter().map(|e| e.name.as_str()).collect();
        assert!(exe_names.contains(&"autolabel"));
        assert!(exe_names.contains(&"cache"));
        assert!(exe_names.contains(&"mk_all"));

        // Check default target
        assert!(config.default_targets.contains(&"Mathlib".to_string()));

        // Every TOP-LEVEL construct in this fixture is modeled. The fields
        // inside `where` blocks are not, and this assertion is the point of the
        // fixture: a real Mathlib lakefile carries `testDriver`, `leanOptions`,
        // `supportInterpreter` and `weakLinkArgs`, none of which the
        // declarative subset models. They used to be dropped in silence, so the
        // config looked fully understood while `lake test` reported "No test
        // targets defined in lakefile.lean". They are now accounted for.
        let skipped: Vec<&str> = config
            .diagnostics
            .iter()
            .map(|d| d.token.as_str())
            .collect();
        assert_eq!(
            skipped,
            vec![
                "testDriver",
                "leanOptions",
                "supportInterpreter",
                "supportInterpreter",
                "weakLinkArgs",
            ],
            "unmodelled `where`-block fields must be accounted for, not dropped: {:?}",
            config.diagnostics
        );
        // Doc comments and section headers inside a `where` block are comments,
        // not fields, and must not be reported as skipped.
        assert!(
            !config
                .diagnostics
                .iter()
                .any(|d| d.token.starts_with("/-") || d.token.starts_with("##")),
            "comments inside a `where` block must not be reported: {:?}",
            config.diagnostics
        );
    }

    #[test]
    fn test_parse_records_skipped_top_level_constructs() {
        let content = r"import Lake
open Lake DSL

package demo

abbrev extraOptions := #[]

lean_lib Demo
";
        let config = LakeConfig::parse(content).expect("lenient parse should succeed");
        assert_eq!(config.package.name, "demo");
        assert_eq!(config.libs.len(), 1);
        assert_eq!(
            config.diagnostics.len(),
            1,
            "exactly the abbrev should be skipped: {:?}",
            config.diagnostics
        );
        assert_eq!(config.diagnostics[0].line, 6);
        assert_eq!(config.diagnostics[0].token, "abbrev");
        assert_eq!(config.diagnostics[0].text, "abbrev extraOptions := #[]");
    }

    #[test]
    fn test_parse_records_unmodelled_where_block_fields() {
        let content = r#"import Lake
open Lake DSL

package demo where
  testDriver := "DemoTest"
  moreLeanArgs := #["-DwarningAsError=true"]

lean_lib Demo where
  roots := #[`Demo]
  precompileModules := true
"#;
        let config = LakeConfig::parse(content).expect("lenient parse should succeed");
        // The modelled field is still parsed.
        assert_eq!(config.package.more_lean_args, vec!["-DwarningAsError=true"]);
        assert_eq!(config.libs[0].roots, vec!["Demo"]);
        // The two unmodelled ones are accounted for rather than dropped.
        let skipped: Vec<(usize, &str)> = config
            .diagnostics
            .iter()
            .map(|d| (d.line, d.token.as_str()))
            .collect();
        assert_eq!(skipped, vec![(5, "testDriver"), (10, "precompileModules")]);
    }

    #[test]
    fn test_parse_strict_mode_errors_on_unmodelled_where_block_field() {
        // A dropped `testDriver` is why a TOML/lean project with a test driver
        // reported "No test targets defined"; strict mode must refuse it rather
        // than under-parse, exactly as it refuses an unmodelled top-level
        // construct.
        let content = r#"import Lake
open Lake DSL

package demo where
  testDriver := "DemoTest"

lean_lib Demo
"#;
        match LakeConfig::parse_with_mode(content, LakefileParseMode::Strict) {
            Err(LakeError::UnrecognizedConstructs { count, summary }) => {
                assert_eq!(count, 1, "only testDriver is unmodelled");
                assert!(
                    summary.contains("testDriver"),
                    "summary should name the field: {summary}"
                );
            }
            other => panic!("strict mode must reject an unmodelled field, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_strict_mode_errors_on_unrecognized_construct() {
        let content = r"import Lake
open Lake DSL

package demo

target customStep pkg : Unit := do
  pure ()

lean_lib Demo
";
        let result = LakeConfig::parse_with_mode(content, LakefileParseMode::Strict);
        match result {
            Err(LakeError::UnrecognizedConstructs { count, summary }) => {
                assert_eq!(count, 1, "only the target declaration is unrecognized");
                assert!(
                    summary.contains("line 6: `target`"),
                    "summary should name the construct and line: {summary}"
                );
            }
            other => panic!("expected UnrecognizedConstructs, got: {other:?}"),
        }
    }

    #[test]
    fn test_parse_strict_mode_accepts_fully_modeled_lakefile() {
        let content = r"
import Lake
open Lake DSL

package test
lean_lib Test
";
        let config = LakeConfig::parse_with_mode(content, LakefileParseMode::Strict)
            .expect("strict parse of a fully-modeled lakefile should succeed");
        assert!(config.diagnostics.is_empty(), "no skipped constructs");
    }

    #[test]
    fn test_parse_block_comments_produce_no_diagnostics() {
        let content = r"import Lake
open Lake DSL

/-!
## Module docs spanning
several lines
-/

/-- Single-line doc comment -/
package demo

lean_lib Demo
";
        let config = LakeConfig::parse_with_mode(content, LakefileParseMode::Strict)
            .expect("block comments must not count as skipped constructs");
        assert_eq!(config.package.name, "demo");
        assert!(config.diagnostics.is_empty());
    }

    #[test]
    fn test_parse_indented_continuation_lines_not_double_counted() {
        // A multi-line skipped construct is accounted once (its head line);
        // indented continuations and a dangling closing bracket carry no
        // entries of their own.
        let content = r"import Lake
open Lake DSL

package demo

abbrev linters : Array LeanOption := #[
  first,
  second
]

lean_lib Demo
";
        let config = LakeConfig::parse(content).expect("lenient parse should succeed");
        let heads: Vec<(usize, &str)> = config
            .diagnostics
            .iter()
            .map(|skipped| (skipped.line, skipped.token.as_str()))
            .collect();
        assert_eq!(
            heads,
            vec![(6, "abbrev")],
            "only the construct head line is recorded"
        );
    }

    #[test]
    fn test_lakefile_parse_mode_from_env() {
        crate::test_env::with_serialized_env_vars(&[(LakefileParseMode::STRICT_ENV, "1")], || {
            assert_eq!(LakefileParseMode::from_env(), LakefileParseMode::Strict)
        });
        crate::test_env::with_serialized_env_vars(&[(LakefileParseMode::STRICT_ENV, "0")], || {
            assert_eq!(LakefileParseMode::from_env(), LakefileParseMode::Lenient)
        });
        crate::test_env::with_serialized_env_vars(&[(LakefileParseMode::STRICT_ENV, "")], || {
            assert_eq!(LakefileParseMode::from_env(), LakefileParseMode::Lenient)
        });
    }

    #[test]
    fn test_parse_require_new_syntax() {
        // Test the new "owner" / "repo" @ git "branch" syntax
        let content = r#"
import Lake
open Lake DSL

require "leanprover-community" / "batteries" @ git "main"
require "leanprover-community" / "Qq" @ git "v1.0.0"

package test
lean_lib Test
"#;
        let config = LakeConfig::parse(content).unwrap();
        assert_eq!(config.package.dependencies.len(), 2);

        let batteries = &config.package.dependencies[0];
        assert_eq!(batteries.name, "batteries");
        assert!(batteries.git.is_some(), "batteries dep should have git url");
        assert_eq!(batteries.rev.as_deref(), Some("main"));

        let qq = &config.package.dependencies[1];
        assert_eq!(qq.name, "Qq");
        assert!(qq.git.is_some(), "Qq dep should have git url");
    }

    #[test]
    fn test_parse_interpolates_package_name_builtin() {
        // A value referencing the built-in PACKAGE_NAME variable resolves.
        let content = r#"
import Lake
open Lake DSL

package demo where
  description := "library for $(PACKAGE_NAME)"

lean_lib Demo
"#;
        let config = LakeConfig::parse(content).unwrap();
        assert_eq!(config.package.name, "demo");
        assert_eq!(
            config.package.description.as_deref(),
            Some("library for demo")
        );
    }

    #[test]
    fn test_parse_interpolates_env_variable() {
        // A value referencing an environment variable resolves via fallback.
        let key = "CLEAN_LAKE_CONFIG_INTERP_TEST";
        let content = format!(
            r#"
import Lake
open Lake DSL

package demo where
  srcDir := "${{{key}}}/src"

lean_lib Demo
"#
        );
        let config = crate::test_env::with_serialized_env_vars(&[(key, "envroot")], || {
            LakeConfig::parse(&content)
        })
        .unwrap();
        assert_eq!(config.package.src_dir, Some(PathBuf::from("envroot/src")));
    }

    #[test]
    fn test_parse_interpolation_unknown_variable_errors() {
        let content = r#"
import Lake
open Lake DSL

package demo where
  description := "needs $(DEFINITELY_NOT_SET_VARIABLE_XYZ)"

lean_lib Demo
"#;
        let result = LakeConfig::parse(content);
        assert!(
            matches!(
                result,
                Err(LakeError::UnknownVariable { ref name, .. })
                    if name == "DEFINITELY_NOT_SET_VARIABLE_XYZ"
            ),
            "expected UnknownVariable, got: {result:?}"
        );
    }

    #[test]
    fn test_parse_interpolation_in_more_lean_args() {
        let content = r#"
import Lake
open Lake DSL

package demo where
  moreLeanArgs := #["-Dname=$(PACKAGE_NAME)", "-Dplain"]

lean_lib Demo
"#;
        let config = LakeConfig::parse(content).unwrap();
        assert_eq!(
            config.package.more_lean_args,
            vec!["-Dname=demo", "-Dplain"]
        );
    }

    #[test]
    fn test_parse_no_interpolation_leaves_value_unchanged() {
        // A literal value with no references must pass through untouched,
        // including a lone dollar sign.
        let content = r#"
import Lake
open Lake DSL

package demo where
  description := "cost is $5 flat"

lean_lib Demo
"#;
        let config = LakeConfig::parse(content).unwrap();
        assert_eq!(
            config.package.description.as_deref(),
            Some("cost is $5 flat")
        );
    }

    #[test]
    fn test_parse_guillemet_name() {
        // Test parsing names with guillemets (French quotes) «name»
        let content = r"
import Lake
open Lake DSL

package test

lean_exe «check-yaml» where
  root := `CheckYaml
";
        let config = LakeConfig::parse(content).unwrap();
        assert_eq!(config.exes.len(), 1);
        assert_eq!(config.exes[0].name, "check-yaml");
    }

    #[test]
    fn test_parse_lib_default_facets_and_pre_compile_hooks_populated() {
        let content = r#"
import Lake
open Lake DSL

package test

lean_lib MyLib where
  roots := #[`MyLib]
  defaultFacets := #["leanArts", "static"]
  preCompileHooks := #["gen-headers", "codegen"]

lean_exe runner where
  root := `Main
  supportedBackends := #["native", "llvm"]
"#;
        let config = LakeConfig::parse(content).unwrap();
        assert_eq!(config.libs.len(), 1);
        assert_eq!(
            config.libs[0].default_facets,
            vec!["leanArts", "static"],
            "defaultFacets must be parsed into the lib struct"
        );
        assert_eq!(
            config.libs[0].pre_compile_hooks,
            vec!["gen-headers", "codegen"],
            "preCompileHooks must be parsed into the lib struct"
        );
        assert_eq!(config.exes.len(), 1);
        assert_eq!(
            config.exes[0].supported_backends,
            vec!["native", "llvm"],
            "supportedBackends must be parsed into the exe struct"
        );
    }

    #[test]
    fn test_parse_lib_exe_without_extra_fields_defaults_empty() {
        // Regression: a lakefile that does not declare the new fields must keep
        // them at their empty defaults rather than gaining spurious entries.
        let content = r#"
import Lake
open Lake DSL

package test

lean_lib MyLib where
  roots := #[`MyLib]

lean_exe runner where
  root := `Main
"#;
        let config = LakeConfig::parse(content).unwrap();
        assert_eq!(config.libs.len(), 1);
        assert!(
            config.libs[0].default_facets.is_empty(),
            "default_facets should default empty when undeclared"
        );
        assert!(
            config.libs[0].pre_compile_hooks.is_empty(),
            "pre_compile_hooks should default empty when undeclared"
        );
        assert_eq!(config.exes.len(), 1);
        assert!(
            config.exes[0].supported_backends.is_empty(),
            "supported_backends should default empty when undeclared"
        );
    }

    #[test]
    fn test_parse_interpolation_in_lib_default_facets() {
        // The interpolate loop must cover the newly-parsed fields so that
        // declared $(VAR) references are honored rather than left raw.
        let content = r#"
import Lake
open Lake DSL

package demo

lean_lib MyLib where
  defaultFacets := #["$(PACKAGE_NAME)-arts"]

lean_exe runner where
  root := `Main
  supportedBackends := #["$(PACKAGE_NAME)-backend"]
"#;
        let config = LakeConfig::parse(content).unwrap();
        assert_eq!(config.libs[0].default_facets, vec!["demo-arts"]);
        assert_eq!(config.exes[0].supported_backends, vec!["demo-backend"]);
    }
}
