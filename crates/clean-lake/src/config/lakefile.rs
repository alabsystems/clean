// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The `lakefile.lean` line scraper behind [`LakeConfig::parse_with_mode`]:
//! the declarative-subset parser, its `where`-block field readers, `require`
//! parsing, and `$(VAR)` interpolation of the parsed values. Split out of
//! `config.rs` so that file stays under the 1000-line cap; the configuration
//! types and their small helpers stay there.

use super::lean_options::{join_field_lines, join_inline_field, parse_option_field, OptionSlots};
use super::option_scan::unattributed_option_mentions;
use super::{
    Dependency, LakeConfig, LakeScript, LakefileParseMode, LeanExe, LeanLib, LeanTest,
    PackageConfig, SkippedConstruct,
};
use crate::error::{LakeError, LakeResult};
use crate::interpolate::{contains_reference, InterpContext};
use semver::VersionReq;
use std::path::PathBuf;

impl LakeConfig {
    /// Parse lakefile.lean content with an explicit handling mode for
    /// unrecognized top-level constructs
    pub fn parse_with_mode(content: &str, mode: LakefileParseMode) -> LakeResult<Self> {
        let mut config = LakeConfig::default();

        // Parse Lean surface syntax and extract DSL constructs
        // This is a simplified parser - a full implementation would use clean-parser

        let lines: Vec<&str> = content.lines().collect();
        // Lines a package / lean_lib / lean_exe field was read from: an option
        // field anywhere else is one this scraper never attributed (G50).
        let mut consumed = vec![false; lines.len()];
        let mut i = 0;
        // Track if the next declaration should be marked as default target
        let mut next_is_default = false;

        while i < lines.len() {
            let mut line = lines[i].trim();

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

            // `@[default_target]` marks the next declaration, which may follow
            // on the same line (`@[default_target] lean_lib X where`).
            if let Some(after) = line.strip_prefix("@[default_target]") {
                next_is_default = true;
                line = after.trim();
                if line.is_empty() {
                    i += 1;
                    continue;
                }
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
                    match Self::inline_where_field(rest) {
                        Some(inline) => {
                            let (field, next) = join_inline_field(&lines, i, inline);
                            if !Self::parse_package_field(&mut config.package, &field) {
                                Self::record_unknown_block_field(
                                    &mut config.diagnostics,
                                    i,
                                    &field,
                                );
                            }
                            Self::mark_option_field(&mut consumed, &field, i, next);
                            i = next;
                        }
                        None => i += 1,
                    }
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
                        // A field's value may span lines (`leanOptions := #[`
                        // … `]`, an `if … then … else …`): read it whole.
                        let (field, next) = join_field_lines(&lines, i);
                        if !Self::parse_package_field(&mut config.package, &field) {
                            Self::record_unknown_block_field(&mut config.diagnostics, i, &field);
                        }
                        Self::mark_option_field(&mut consumed, &field, i, next);
                        i = next;
                    }
                    continue;
                }
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
                    match Self::inline_where_field(rest) {
                        Some(inline) => {
                            let (field, next) = join_inline_field(&lines, i, inline);
                            if !Self::parse_lib_field(&mut lib, &field) {
                                Self::record_unknown_block_field(
                                    &mut config.diagnostics,
                                    i,
                                    &field,
                                );
                            }
                            Self::mark_option_field(&mut consumed, &field, i, next);
                            i = next;
                        }
                        None => i += 1,
                    }
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
                        // A field's value may span lines (`leanOptions := #[`
                        // … `]`, an `if … then … else …`): read it whole.
                        let (field, next) = join_field_lines(&lines, i);
                        if !Self::parse_lib_field(&mut lib, &field) {
                            Self::record_unknown_block_field(&mut config.diagnostics, i, &field);
                        }
                        Self::mark_option_field(&mut consumed, &field, i, next);
                        i = next;
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
                    match Self::inline_where_field(rest) {
                        Some(inline) => {
                            let (field, next) = join_inline_field(&lines, i, inline);
                            if !Self::parse_exe_field(&mut exe, &field) {
                                Self::record_unknown_block_field(
                                    &mut config.diagnostics,
                                    i,
                                    &field,
                                );
                            }
                            Self::mark_option_field(&mut consumed, &field, i, next);
                            i = next;
                        }
                        None => i += 1,
                    }
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
                        // A field's value may span lines (`leanOptions := #[`
                        // … `]`, an `if … then … else …`): read it whole.
                        let (field, next) = join_field_lines(&lines, i);
                        if !Self::parse_exe_field(&mut exe, &field) {
                            Self::record_unknown_block_field(&mut config.diagnostics, i, &field);
                        }
                        Self::mark_option_field(&mut consumed, &field, i, next);
                        i = next;
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
                        // A field's value may span lines (`leanOptions := #[`
                        // … `]`, an `if … then … else …`): read it whole.
                        let (field, next) = join_field_lines(&lines, i);
                        if !Self::parse_test_field(&mut test, &field) {
                            Self::record_unknown_block_field(&mut config.diagnostics, i, &field);
                        }
                        i = next;
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

        // An option field the scraper never attributed to a target (a `{ }`
        // structure instance, a `def`, a layout it does not read) still sets
        // the language Lake compiles in: refuse every module (G50).
        for (index, text) in unattributed_option_mentions(content, &consumed) {
            config
                .package
                .unreadable_lean_args
                .push(format!("lakefile.lean:{}: {text}", index + 1));
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
        } else if let Some(parsed) = parse_option_field(
            line,
            OptionSlots {
                lean_options: &mut package.lean_options,
                more_lean_args: &mut package.more_lean_args,
                weak_lean_args: &mut package.weak_lean_args,
                more_link_args: Some(&mut package.more_link_args),
                unreadable: &mut package.unreadable_lean_args,
            },
        ) {
            return parsed;
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
        } else if let Some(parsed) = parse_option_field(
            line,
            OptionSlots {
                lean_options: &mut lib.lean_options,
                more_lean_args: &mut lib.more_lean_args,
                weak_lean_args: &mut lib.weak_lean_args,
                more_link_args: None,
                unreadable: &mut lib.unreadable_lean_args,
            },
        ) {
            return parsed;
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
        } else if let Some(parsed) = parse_option_field(
            line,
            OptionSlots {
                lean_options: &mut exe.lean_options,
                more_lean_args: &mut exe.more_lean_args,
                weak_lean_args: &mut exe.weak_lean_args,
                more_link_args: Some(&mut exe.more_link_args),
                unreadable: &mut exe.unreadable_lean_args,
            },
        ) {
            return parsed;
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

    /// Mark lines `from..to` as read when they hold an option field
    /// (`leanOptions` / `moreLeanArgs` / `weakLeanArgs`): those went through
    /// `parse_option_field`, which either read them or recorded them as
    /// unreadable. Any other field is left unmarked, so an option field
    /// hidden in it (a column-0 `def` a block swallowed as an unknown field)
    /// is still caught by the scan.
    fn mark_option_field(consumed: &mut [bool], field: &str, from: usize, to: usize) {
        let is_option_field = ["leanOptions", "moreLeanArgs", "weakLeanArgs"]
            .iter()
            .any(|name| {
                field
                    .strip_prefix(name)
                    .is_some_and(|r| r.trim_start().starts_with(":="))
            });
        if is_option_field {
            if let Some(lines) = consumed.get_mut(from..to) {
                lines.fill(true);
            }
        }
    }

    /// The field written on a declaration's own line after `where`
    /// (`package p where leanOptions := …`), when there is one.
    fn inline_where_field(rest: &str) -> Option<&str> {
        let at = rest.find(" where")?;
        let after = rest[at + " where".len()..].trim();
        (!after.is_empty() && !after.starts_with("--")).then_some(after)
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
