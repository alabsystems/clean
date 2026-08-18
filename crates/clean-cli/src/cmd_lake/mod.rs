// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lake build system command handlers.
//!
//! ## Module Structure
//!
//! - `build`: Project creation, initialization, building, and cleaning
//! - `deps`: Dependency fetching, updating, resolution, and environment info
//! - `run`: Executable running, testing, and Lean interpreter integration
//! - `scripts`: Script listing, execution, and documentation
//! - `cache`: Cache management and .olean pack/unpack/upload
//! - `check`: Dry-run checks for build, test, and lint
//! - `smoke`: Lake replacement smoke evidence generator (#3707)
//! - `serve`: Lake-compatible editor entry point (stdio LSP server)

mod build;
mod cache;
mod check;
mod deps;
mod goodness;
mod lint;
mod run;
mod scripts;
mod serve;
mod smoke;
mod verify_fresh;

pub(crate) use serve::lake_serve;

use crate::cli_args::{CacheCommands, LakeCommands, ScriptCommands};
use clean_lake::{LakeConfig, LakeError, LakefileParseMode};
use std::path::{Path, PathBuf};
use std::process::ExitStatus;

/// Friendly hint shared by the project-config loaders when no lakefile is found.
const NO_LAKEFILE_HINT: &str = "No lakefile.toml or lakefile.lean found in current directory.\n\
     Run 'clean lake new <name>' to create a new project or \
     'clean lake init' to initialize in this directory.";

/// Load the project's lake configuration from `cwd`, preferring `lakefile.toml`
/// and falling back to `lakefile.lean` (via [`LakeConfig::load_from_dir`]).
///
/// On a missing lakefile this surfaces the friendly two-line hint mentioning
/// both `lakefile.toml` and `lakefile.lean`; parse and IO errors propagate so
/// malformed lakefiles still fail loudly. Top-level `lakefile.lean` constructs
/// the declarative parser skipped are surfaced as warnings by default;
/// setting `CLEAN_LAKE_STRICT_LAKEFILE=1` upgrades them to a hard error.
pub(super) fn load_project_config(cwd: &Path) -> anyhow::Result<LakeConfig> {
    load_project_config_with_mode(cwd, LakefileParseMode::from_env())
}

/// [`load_project_config`] with an explicit lakefile.lean parse mode (the
/// public entry resolves the mode from `CLEAN_LAKE_STRICT_LAKEFILE`).
fn load_project_config_with_mode(
    cwd: &Path,
    mode: LakefileParseMode,
) -> anyhow::Result<LakeConfig> {
    match LakeConfig::load_from_dir_with_mode(cwd, mode) {
        Ok(config) => {
            warn_skipped_constructs(&config);
            Ok(config)
        }
        Err(LakeError::LakefileNotFound(_)) => anyhow::bail!("{NO_LAKEFILE_HINT}"),
        Err(other) => Err(anyhow::Error::new(other)
            .context(format!("failed to load lakefile in {}", cwd.display()))),
    }
}

/// Best-effort variant of [`load_project_config`] for the non-bail surfaces
/// (`lake clean`, `lake env`): returns `Ok(None)` when no lakefile is present so
/// callers can fall through to their no-project branch, while still surfacing
/// parse/IO errors so a malformed lakefile is never silently ignored.
pub(super) fn try_load_project_config(cwd: &Path) -> anyhow::Result<Option<LakeConfig>> {
    match LakeConfig::load_from_dir_with_mode(cwd, LakefileParseMode::from_env()) {
        Ok(config) => {
            warn_skipped_constructs(&config);
            Ok(Some(config))
        }
        Err(LakeError::LakefileNotFound(_)) => Ok(None),
        Err(other) => Err(anyhow::Error::new(other)
            .context(format!("failed to load lakefile in {}", cwd.display()))),
    }
}

/// Surface `lakefile.lean` constructs the declarative parser skipped as
/// warnings so programmatic lakefiles no longer under-parse silently. In
/// strict mode (`CLEAN_LAKE_STRICT_LAKEFILE=1`) parsing already failed inside
/// `clean-lake` before this point, so a loaded config only ever carries
/// lenient-mode diagnostics.
fn warn_skipped_constructs(config: &LakeConfig) {
    for skipped in &config.diagnostics {
        eprintln!(
            "warning: lakefile.lean:{}: skipped unrecognized top-level construct `{}` \
             (set CLEAN_LAKE_STRICT_LAKEFILE=1 to make this an error)",
            skipped.line, skipped.token
        );
    }
}

#[derive(Debug)]
struct ForwardedProcessExit {
    status: ExitStatus,
}

impl ForwardedProcessExit {
    fn code(&self) -> Option<i32> {
        self.status.code()
    }
}

impl std::fmt::Display for ForwardedProcessExit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Child process exited with status {}", self.status)
    }
}

impl std::error::Error for ForwardedProcessExit {}

pub(crate) fn native_executable_exit_code(err: &anyhow::Error) -> Option<i32> {
    err.downcast_ref::<ForwardedProcessExit>()
        .and_then(ForwardedProcessExit::code)
        .or_else(|| run::native_executable_exit_code(err))
}

pub(super) fn forwarded_process_exit(status: ExitStatus) -> anyhow::Error {
    ForwardedProcessExit { status }.into()
}

/// Handle Lake subcommands
pub(crate) fn handle_lake_command(
    command: LakeCommands,
    dir: Option<PathBuf>,
) -> anyhow::Result<()> {
    match command {
        LakeCommands::Build {
            target,
            verbose,
            force,
            jobs,
            permissive_imports,
        } => build::lake_build(target, verbose, force, jobs, permissive_imports, dir),
        LakeCommands::New { name, lib, exe } => build::lake_new(&name, lib, exe),
        LakeCommands::Clean { verbose } => build::lake_clean(verbose, dir),
        LakeCommands::Init { name } => build::lake_init(name, dir),
        LakeCommands::Fetch { verbose } => deps::lake_fetch(verbose, dir),
        LakeCommands::Update { package, verbose } => deps::lake_update(package, verbose, dir),
        LakeCommands::Env {
            command, verbose, ..
        } => deps::lake_env(&command, verbose, dir),
        LakeCommands::Run {
            target,
            args,
            verbose,
            jobs,
            ..
        } => run::lake_run(target, &args, verbose, jobs, dir),
        LakeCommands::Resolve { verbose, dry_run } => deps::lake_resolve(verbose, dry_run, dir),
        LakeCommands::Exe {
            name,
            args,
            verbose,
        } => run::lake_exe(&name, &args, verbose, dir),
        LakeCommands::Test {
            target,
            args,
            verbose,
            jobs,
            ..
        } => run::lake_test_with_args(target, &args, verbose, jobs, dir),
        LakeCommands::Script(script_cmd) => handle_script_command(script_cmd, dir),
        LakeCommands::Cache(cache_cmd) => handle_cache_command(cache_cmd, dir),
        LakeCommands::Lint { target, verbose } => check::lake_lint(target, verbose, dir),
        LakeCommands::CheckBuild { target, verbose } => {
            check::lake_check_build(target, verbose, dir)
        }
        LakeCommands::CheckTest { target, verbose } => check::lake_check_test(target, verbose, dir),
        LakeCommands::CheckLint { target, verbose } => check::lake_check_lint(target, verbose, dir),
        LakeCommands::Pack { output, verbose } => cache::lake_pack(output, verbose, dir),
        LakeCommands::Unpack { archive, verbose } => cache::lake_unpack(&archive, verbose, dir),
        LakeCommands::Upload { verbose, dry_run } => cache::lake_upload(verbose, dry_run, dir),
        LakeCommands::Smoke { report, verbose } => smoke::lake_smoke(&report, verbose),
        LakeCommands::VerifyFresh {
            source_root,
            module,
            olean_search_path,
            json,
        } => verify_fresh::lake_verify_fresh(source_root, module, olean_search_path, json),
        LakeCommands::Goodness {
            module,
            olean_search_path,
            constant,
            json,
        } => goodness::lake_goodness(module, olean_search_path, constant, json),
        // Fail-closed guard, not a handler: `lake serve` runs the async stdio
        // language server and is dispatched in `lib.rs::run()` BEFORE this
        // synchronous Lake dispatcher (mirroring `clean lsp`). Reaching this
        // arm means the async pre-dispatch was bypassed — refuse loudly
        // instead of silently doing nothing.
        LakeCommands::Serve { .. } => anyhow::bail!(
            "`clean lake serve` must be dispatched through the async CLI entry point \
             (lib.rs::run); the synchronous Lake dispatcher cannot host the stdio \
             language server"
        ),
    }
}

/// Handle script subcommands
fn handle_script_command(cmd: ScriptCommands, dir: Option<PathBuf>) -> anyhow::Result<()> {
    match cmd {
        ScriptCommands::List => scripts::lake_script_list(dir),
        ScriptCommands::Run { name, args } => scripts::lake_script_run(&name, &args, dir),
        ScriptCommands::Doc { name } => scripts::lake_script_doc(&name, dir),
    }
}

/// Handle cache subcommands
fn handle_cache_command(cmd: CacheCommands, dir: Option<PathBuf>) -> anyhow::Result<()> {
    match cmd {
        CacheCommands::Get { verbose } => cache::lake_cache_get(verbose, dir),
        CacheCommands::Put { verbose } => cache::lake_cache_put(verbose, dir),
        CacheCommands::Add { files, verbose } => cache::lake_cache_add(&files, verbose, dir),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A lakefile with a custom `target` declaration — a construct the
    /// declarative lakefile.lean parser does not model.
    const CUSTOM_TARGET_LAKEFILE: &str = r#"import Lake
open Lake DSL

package demo

lean_lib Demo

target generateAssets pkg : System.FilePath := do
  pure (pkg.buildDir / "assets")
"#;

    #[test]
    fn test_load_project_config_lenient_records_custom_target_diagnostic() {
        let dir = tempfile::tempdir().expect("tempdir");
        std::fs::write(dir.path().join("lakefile.lean"), CUSTOM_TARGET_LAKEFILE)
            .expect("write lakefile");
        let config = load_project_config_with_mode(dir.path(), LakefileParseMode::Lenient)
            .expect("lenient load should succeed with diagnostics");
        assert_eq!(
            config.diagnostics.len(),
            1,
            "exactly the target declaration should be skipped: {:?}",
            config.diagnostics
        );
        assert_eq!(config.diagnostics[0].token, "target");
        assert_eq!(config.diagnostics[0].line, 8);
    }

    #[test]
    fn test_load_project_config_strict_errors_on_custom_target() {
        // The strict-mode error propagates as anyhow::Err through
        // handle_lake_command, which is exactly what makes the `clean lake`
        // process exit nonzero.
        let dir = tempfile::tempdir().expect("tempdir");
        std::fs::write(dir.path().join("lakefile.lean"), CUSTOM_TARGET_LAKEFILE)
            .expect("write lakefile");
        let err = load_project_config_with_mode(dir.path(), LakefileParseMode::Strict)
            .expect_err("strict load must fail on a custom target declaration");
        let chain = format!("{err:#}");
        assert!(
            chain.contains("`target`"),
            "error should name the unrecognized construct: {chain}"
        );
    }

    #[test]
    fn test_load_project_config_strict_clean_lakefile_no_diagnostics() {
        let dir = tempfile::tempdir().expect("tempdir");
        std::fs::write(
            dir.path().join("lakefile.lean"),
            "import Lake\nopen Lake DSL\n\npackage demo\n\nlean_lib Demo\n",
        )
        .expect("write lakefile");
        let config = load_project_config_with_mode(dir.path(), LakefileParseMode::Strict)
            .expect("fully-modeled lakefile should load in strict mode");
        assert!(config.diagnostics.is_empty(), "no skipped constructs");
    }
}
