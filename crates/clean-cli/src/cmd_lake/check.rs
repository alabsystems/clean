// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Dry-run checks for build, test, and lint.

use super::lint::{lint_source, LintSummary};
use crate::cmd_core::resolve_project_dir;
use std::path::PathBuf;

/// Run linters on the project.
///
/// Lints each library root module by running the default lint rule set over
/// its parsed surface syntax (see [`super::lint`]). The pass reports
/// parse/type-level errors plus the cheap, sound semantic warnings
/// (unused/shadowed bindings, missing docs on public declarations) with
/// per-issue line/column locations and a structured per-module summary.
///
/// Deeper, elaboration-driven rules (unsolved-goal diagnostics, dead `simp`
/// lemmas, environment-resolved unused imports) are deferred follow-ups; this
/// pass is intentionally portable (no network, no `.olean` resolution).
pub(super) fn lake_lint(
    target: Option<String>,
    verbose: bool,
    dir: Option<PathBuf>,
) -> anyhow::Result<()> {
    use clean_lake::Workspace;

    let cwd = resolve_project_dir(dir)?;
    let config = super::load_project_config(&cwd)?;

    if verbose {
        println!("Running linters...");
    }

    let ws = Workspace::from_config(&cwd, config);

    let targets: Vec<String> = if let Some(ref name) = target {
        ws.config()
            .libs
            .iter()
            .filter(|l| l.name == *name)
            .flat_map(clean_lake::LeanLib::root_modules)
            .collect()
    } else {
        ws.config()
            .libs
            .iter()
            .flat_map(clean_lake::LeanLib::root_modules)
            .collect()
    };

    if targets.is_empty() {
        println!("No targets to lint.");
        return Ok(());
    }

    let mut total = LintSummary::default();
    let mut modules_with_issues = 0usize;

    for root in &targets {
        let Some(module_path) = ws.find_module(root) else {
            eprintln!("  {root} - source not found (skipped)");
            continue;
        };
        if verbose {
            println!("Linting: {}", module_path.display());
        }

        let source = std::fs::read_to_string(&module_path)
            .map_err(|e| anyhow::anyhow!("failed to read module {}: {e}", module_path.display()))?;
        let report = lint_source(&source);
        let summary = report.summary();

        if report.issues.is_empty() {
            println!("  {root} - OK");
        } else {
            modules_with_issues += 1;
            println!(
                "  {root} - {} error(s), {} warning(s)",
                summary.errors, summary.warnings
            );
            for issue in &report.issues {
                let kind = if issue.rule.is_error() {
                    "error"
                } else {
                    "warning"
                };
                println!(
                    "    {}:{}:{}: {kind} [{}]: {}",
                    module_path.display(),
                    issue.line,
                    issue.column,
                    issue.rule,
                    issue.message
                );
            }
        }

        total.errors += summary.errors;
        total.warnings += summary.warnings;
    }

    if total.total() == 0 {
        println!("No lint issues found.");
        Ok(())
    } else {
        eprintln!(
            "{} lint issue(s) found across {} module(s): {} error(s), {} warning(s).",
            total.total(),
            modules_with_issues,
            total.errors,
            total.warnings
        );
        if total.errors > 0 {
            anyhow::bail!("lint found {} error(s)", total.errors);
        }
        Ok(())
    }
}

/// Check if build would succeed (dry run)
pub(super) fn lake_check_build(
    target: Option<String>,
    verbose: bool,
    dir: Option<PathBuf>,
) -> anyhow::Result<()> {
    use clean_lake::{BuildContext, BuildOptions, Workspace};

    let cwd = resolve_project_dir(dir)?;
    let config = super::load_project_config(&cwd)?;

    if verbose {
        println!("Checking build...");
    }

    let ws = Workspace::from_config(&cwd, config);
    let mut ctx = BuildContext::new(ws).with_options(
        BuildOptions::new()
            .with_verbose(verbose)
            .with_check_only(true),
    );

    let result = if let Some(ref name) = target {
        ctx.build_target(name)?
    } else {
        ctx.build_all()?
    };

    if result.failed.is_empty() {
        println!("Build check passed.");
        Ok(())
    } else {
        for (module, err) in &result.failed {
            eprintln!("  Error in {module}: {err}");
        }
        anyhow::bail!("Build check failed with {} error(s)", result.failed.len())
    }
}

/// Check if tests would pass (dry run)
pub(super) fn lake_check_test(
    target: Option<String>,
    verbose: bool,
    dir: Option<PathBuf>,
) -> anyhow::Result<()> {
    let cwd = resolve_project_dir(dir)?;
    let config = super::load_project_config(&cwd)?;

    if verbose {
        println!("Checking tests...");
    }

    // Check that build succeeds first
    if config.tests.is_empty() {
        println!("No test targets defined.");
        return Ok(());
    }

    let tests_to_check: Vec<_> = if let Some(ref name) = target {
        let selected: Vec<_> = config
            .tests
            .iter()
            .filter(|t| t.name == *name)
            .cloned()
            .collect();
        // A name that matches nothing used to yield "Would run 0 test(s)" and
        // exit 0, so a typo'd target reported success. Fail closed instead, and
        // name what IS declared.
        if selected.is_empty() {
            let declared: Vec<&str> = config.tests.iter().map(|t| t.name.as_str()).collect();
            anyhow::bail!(
                "No test target named '{name}'. Declared test targets: {}",
                if declared.is_empty() {
                    "(none)".to_string()
                } else {
                    declared.join(", ")
                }
            );
        }
        selected
    } else {
        config.tests.clone()
    };

    // "Would pass" has to be backed by something. Elaborating the targets under
    // `check_only` is exactly what `check-build` does, and it is what makes the
    // answer a check rather than an inventory: a test target whose module does
    // not elaborate cannot pass, and this reports that before anything is run.
    check_targets_elaborate(&cwd, config, target.as_deref(), verbose)?;

    println!("Would run {} test(s):", tests_to_check.len());
    for test in &tests_to_check {
        println!("  - {}", test.name);
    }

    Ok(())
}

/// Check if linting would pass (dry run)
pub(super) fn lake_check_lint(
    target: Option<String>,
    verbose: bool,
    dir: Option<PathBuf>,
) -> anyhow::Result<()> {
    let cwd = resolve_project_dir(dir)?;
    let config = super::load_project_config(&cwd)?;

    if verbose {
        println!("Checking lint...");
    }

    let targets: Vec<_> = if let Some(ref name) = target {
        let selected: Vec<_> = config
            .libs
            .iter()
            .filter(|l| l.name == *name)
            .map(|l| l.name.clone())
            .collect();
        // Same fail-open as check-test: an unknown name printed
        // "Would lint 0 target(s)" and succeeded.
        if selected.is_empty() {
            let declared: Vec<&str> = config.libs.iter().map(|l| l.name.as_str()).collect();
            anyhow::bail!(
                "No library target named '{name}'. Declared libraries: {}",
                if declared.is_empty() {
                    "(none)".to_string()
                } else {
                    declared.join(", ")
                }
            );
        }
        selected
    } else {
        config.libs.iter().map(|l| l.name.clone()).collect()
    };

    check_targets_elaborate(&cwd, config, target.as_deref(), verbose)?;

    println!("Would lint {} target(s):", targets.len());
    for t in &targets {
        println!("  - {t}");
    }

    Ok(())
}

/// Elaborate `target` (or the whole workspace) under `check_only`, so a
/// "would pass" answer is backed by a real check rather than a target listing.
fn check_targets_elaborate(
    cwd: &std::path::Path,
    config: clean_lake::LakeConfig,
    target: Option<&str>,
    verbose: bool,
) -> anyhow::Result<()> {
    use clean_lake::{BuildContext, BuildOptions, Workspace};

    let ws = Workspace::from_config(cwd, config);
    let mut ctx = BuildContext::new(ws).with_options(
        BuildOptions::new()
            .with_verbose(verbose)
            .with_check_only(true),
    );
    let result = match target {
        Some(name) => ctx.build_target(name)?,
        None => ctx.build_all()?,
    };
    if !result.failed.is_empty() {
        for (module, err) in &result.failed {
            eprintln!("  Error in {module}: {err}");
        }
        anyhow::bail!("Check failed with {} error(s)", result.failed.len());
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Write a minimal lake project with a single library `Demo` whose root
    /// module is `Demo.lean` containing `source`. Returns the temp dir so the
    /// caller keeps it alive for the duration of the test.
    fn lake_project_with_module(source: &str) -> tempfile::TempDir {
        let dir = tempfile::tempdir().expect("tempdir");
        std::fs::write(
            dir.path().join("lakefile.lean"),
            "package demo\nlean_lib Demo\n",
        )
        .expect("write lakefile");
        std::fs::write(dir.path().join("Demo.lean"), source).expect("write module");
        dir
    }

    /// An unknown target name used to print "Would lint 0 target(s)" and exit
    /// 0 — a typo reported success. Both dry-run checks must fail closed and
    /// name what IS declared, so the mistake is visible.
    #[test]
    fn test_lake_check_lint_unknown_target_is_an_error() {
        let dir = lake_project_with_module("def f (x : Nat) : Nat := x\n");
        let err = lake_check_lint(
            Some("Nonexistent".to_string()),
            false,
            Some(dir.path().to_path_buf()),
        )
        .expect_err("an unknown library target must not report success");
        let msg = err.to_string();
        assert!(
            msg.contains("Nonexistent"),
            "error should name the missing target: {msg}"
        );
        assert!(
            msg.contains("Demo"),
            "error should list the declared libraries: {msg}"
        );
    }

    #[test]
    fn test_lake_check_test_unknown_target_is_an_error() {
        let dir = lake_project_with_module("def f (x : Nat) : Nat := x\n");
        // No `lean_test` is declared, so the early "No test targets defined."
        // path would return Ok. Declare one so target selection is reached.
        std::fs::write(
            dir.path().join("lakefile.lean"),
            "package demo\nlean_lib Demo\nlean_test DemoTest\n",
        )
        .expect("rewrite lakefile");

        let err = lake_check_test(
            Some("Nonexistent".to_string()),
            false,
            Some(dir.path().to_path_buf()),
        )
        .expect_err("an unknown test target must not report success");
        assert!(
            err.to_string().contains("Nonexistent"),
            "error should name the missing target: {err}"
        );
    }

    /// A module that does not elaborate cannot pass its tests. `check-test`
    /// used to print "Would run N test(s)" and exit 0 regardless.
    #[test]
    fn test_lake_check_test_fails_when_the_module_does_not_elaborate() {
        let dir = tempfile::tempdir().expect("tempdir");
        std::fs::write(
            dir.path().join("lakefile.lean"),
            "package demo\nlean_lib Demo\nlean_test DemoTest\n",
        )
        .expect("write lakefile");
        std::fs::write(
            dir.path().join("Demo.lean"),
            "def f : Nat := this_identifier_does_not_exist\n",
        )
        .expect("write module");

        let result = lake_check_test(None, false, Some(dir.path().to_path_buf()));
        assert!(
            result.is_err(),
            "a module that does not elaborate must not report that tests would pass: {result:?}"
        );
    }

    #[test]
    fn test_lake_lint_clean_module_succeeds() {
        let dir = lake_project_with_module("/-- Doc. -/\ndef f (x : Nat) : Nat := x\n");
        let result = lake_lint(None, false, Some(dir.path().to_path_buf()));
        assert!(
            result.is_ok(),
            "clean module should lint without error: {result:?}"
        );
    }

    #[test]
    fn test_lake_lint_unused_binding_does_not_error_but_is_a_warning() {
        // A warning-only module still exits Ok (warnings do not fail the lint),
        // but the lint engine must detect the unused binding. The semicolon
        // `let v := e; body` form parses to a `Let` node.
        let dir = lake_project_with_module("/-- Doc. -/\ndef f : Nat := let y := 5; 3\n");
        let result = lake_lint(None, false, Some(dir.path().to_path_buf()));
        assert!(
            result.is_ok(),
            "warning-only module should not fail lint: {result:?}"
        );

        use crate::cmd_lake::lint::LintRule;
        let report = lint_source(
            &std::fs::read_to_string(dir.path().join("Demo.lean")).expect("read module"),
        );
        assert!(
            report
                .issues
                .iter()
                .any(|i| i.rule == LintRule::UnusedBinding),
            "engine should detect the unused binding: {:?}",
            report.issues
        );
    }

    #[test]
    fn test_lake_lint_parse_error_module_fails() {
        let dir = lake_project_with_module("def f : := \n");
        let result = lake_lint(None, false, Some(dir.path().to_path_buf()));
        assert!(
            result.is_err(),
            "module with a parse error should fail the lint"
        );
    }

    #[test]
    fn test_lake_lint_missing_lakefile_errors() {
        let dir = tempfile::tempdir().expect("tempdir");
        let result = lake_lint(None, false, Some(dir.path().to_path_buf()));
        assert!(result.is_err(), "lint without a lakefile.lean should error");
    }

    #[test]
    fn test_lake_lint_unknown_target_reports_no_targets() {
        let dir = lake_project_with_module("/-- Doc. -/\ndef f (x : Nat) : Nat := x\n");
        // Filtering on a non-existent library yields no targets, which is not
        // an error (nothing to lint).
        let result = lake_lint(
            Some("Nope".to_string()),
            false,
            Some(dir.path().to_path_buf()),
        );
        assert!(
            result.is_ok(),
            "unknown target should be a no-op, not an error: {result:?}"
        );
    }
}
