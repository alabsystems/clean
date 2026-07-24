// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Portable library dispatch and per-verb handlers for [`super::LakeCommand`].
//!
//! Each public handler consumes the matching `*Args` struct defined in
//! [`super`] and returns a human-readable summary. Tests in [`super::tests`]
//! exercise these handlers directly against a `TempDir` project.
//!
//! ## Relationship to the advertised CLI surface
//!
//! [`super::LakeCommand`] and [`run_lake`] cover the *portable subset* of the
//! Lake verbs — the nine that need no process spawning or stdout side effects
//! and so can be returned as a `String`: `build`, `clean`, `init`, `fetch`,
//! `run`, `exe`, `test`, `env`, `update`. They are a library convenience for
//! embedders that want to drive Lake without going through clap or the unified
//! binary.
//!
//! The full advertised contract lives in [`super::FEATURES`] (24 leaf verbs,
//! including `new`, `resolve`, `script {list,run,doc}`, `cache {get,put,add}`,
//! `lint`, `check-{build,test,lint}`, `pack`, `unpack`, `upload`). The `clean`
//! binary does **not** route through [`run_lake`]; it parses the
//! [`super::LakeCommands`] clap tree and dispatches every advertised verb
//! through `clean_cli::cmd_lake::handle_lake_command`, whose handlers own the
//! process/stdout/exit-code semantics those verbs require. The clap tree and
//! [`super::FEATURES`] are kept in lockstep by the `feature_coverage_matches_clap`
//! drift gate in `crates/clean-cli/tests/feature_coverage.rs`, and the
//! [`super::tests::run_lake_subset_matches_advertised_features`] test pins which
//! advertised verbs `run_lake` is responsible for versus which the binary
//! front-end owns.

use std::path::{Path, PathBuf};

use crate::build::{BuildContext, BuildOptions, BuildResult};
use crate::config::LeanExe;
use crate::error::{LakeError, LakeResult};
use crate::fetch::FetchManager;
use crate::manifest::LakeManifest;
use crate::workspace::Workspace;

use super::{
    BuildArgs, CleanArgs, EnvArgs, ExeArgs, FetchArgs, InitArgs, LakeCommand, RunArgs, TestArgs,
    UpdateArgs,
};

const DEFAULT_CLEAN_TOOLCHAIN: &str = "clean:stable\n";

/// Run a portable Lake command and return a human-readable summary.
///
/// This is the library entry point for the portable subset of Lake verbs (see
/// the module docs): the nine commands that produce no process/stdout side
/// effects and can be returned as a `String`. It is *not* the path the unified
/// `clean` binary takes — that parses [`super::LakeCommands`] and dispatches the
/// full advertised verb set through `clean_cli::cmd_lake::handle_lake_command`.
pub fn run_lake(cmd: &LakeCommand) -> LakeResult<String> {
    match cmd {
        LakeCommand::Build(args) => lake_build(args),
        LakeCommand::Clean(args) => lake_clean(args),
        LakeCommand::Init(args) => lake_init(args),
        LakeCommand::Fetch(args) => lake_fetch(args),
        LakeCommand::Run(args) => lake_run(args),
        LakeCommand::Exe(args) => lake_exe(args),
        LakeCommand::Test(args) => lake_test(args),
        LakeCommand::Env(args) => lake_env(args),
        LakeCommand::Update(args) => lake_update(args),
    }
}

// ---------------------------------------------------------------------------
// Build
// ---------------------------------------------------------------------------

/// Execute `lake build` — find the lakefile, resolve deps, and build.
pub(super) fn lake_build(args: &BuildArgs) -> LakeResult<String> {
    let dir = resolve_project_dir(args.dir.as_deref())?;
    let ws = Workspace::load(&dir)?;

    let options = BuildOptions::new()
        .with_jobs(args.jobs)
        .with_verbose(args.verbose)
        .with_force(args.force)
        .with_check_only(args.check_only);

    let mut ctx = BuildContext::new(ws).with_options(options);
    let result = ctx.build_all()?;

    let mut summary = String::new();
    if let Some(identifier) = ctx.workspace().toolchain() {
        match ctx.workspace().toolchain_version() {
            Some(version) if version != identifier => {
                summary.push_str(&format!("Toolchain: {version} ({identifier})\n"));
            }
            Some(version) => summary.push_str(&format!("Toolchain: {version}\n")),
            None => summary.push_str(&format!("Toolchain: {identifier} (unresolved)\n")),
        }
    }
    summary.push_str(&format_build_result(&result));

    Ok(summary)
}

/// Format a [`BuildResult`] into a human-readable summary string.
pub(super) fn format_build_result(result: &BuildResult) -> String {
    let mut out = String::new();

    if result.is_success() {
        out.push_str(&format!(
            "Build succeeded: {} built, {} up-to-date ({:.2?})\n",
            result.built.len(),
            result.skipped.len(),
            result.duration,
        ));
    } else {
        out.push_str(&format!(
            "Build finished with errors: {} built, {} up-to-date, {} failed ({:.2?})\n",
            result.built.len(),
            result.skipped.len(),
            result.failed.len(),
            result.duration,
        ));
        for (module, err) in &result.failed {
            out.push_str(&format!("  FAIL {module}: {err}\n"));
        }
    }

    out
}

// ---------------------------------------------------------------------------
// clean
// ---------------------------------------------------------------------------

/// Execute `lake clean` — remove build artifacts from the project.
pub(super) fn lake_clean(args: &CleanArgs) -> LakeResult<String> {
    let dir = resolve_project_dir(args.dir.as_deref())?;
    let ws = Workspace::load(&dir)?;

    let build_dir = ws.build_dir();
    let mut removed: Vec<PathBuf> = Vec::new();

    if build_dir.exists() {
        std::fs::remove_dir_all(&build_dir)?;
        removed.push(build_dir);
    }

    // Also clean .lake/packages if present (fetched deps)
    let packages_dir = ws.packages_dir();
    if packages_dir.exists() {
        std::fs::remove_dir_all(&packages_dir)?;
        removed.push(packages_dir);
    }

    if removed.is_empty() {
        Ok("Nothing to clean.\n".to_string())
    } else {
        let paths: Vec<String> = removed.iter().map(|p| p.display().to_string()).collect();
        Ok(format!("cleaned: {}\n", paths.join(", ")))
    }
}

// ---------------------------------------------------------------------------
// Init
// ---------------------------------------------------------------------------

/// Execute `lake init` — scaffold a new Lean project.
pub(super) fn lake_init(args: &InitArgs) -> LakeResult<String> {
    let dir = args
        .dir
        .clone()
        .unwrap_or_else(|| PathBuf::from(".").join(&args.name));
    let dir = std::env::current_dir()
        .unwrap_or_else(|_| PathBuf::from("."))
        .join(&dir);

    if dir.join("lakefile.lean").exists() {
        return Err(LakeError::InvalidConfig(format!(
            "lakefile.lean already exists in {}",
            dir.display()
        )));
    }

    std::fs::create_dir_all(&dir)?;

    write_lakefile(&dir, &args.name, args.lib)?;
    write_lean_toolchain(&dir)?;

    if args.lib {
        write_lib_scaffold(&dir, &args.name)?;
    } else {
        write_exe_scaffold(&dir, &args.name)?;
    }

    Ok(format!(
        "Created new Lean project '{}' in {}\n",
        args.name,
        dir.display()
    ))
}

/// Write `lakefile.lean` for a new project.
fn write_lakefile(dir: &Path, name: &str, is_lib: bool) -> LakeResult<()> {
    let mut content =
        format!("import Lake\nopen Lake DSL\n\npackage {name} where\n  leanOptions := #[]\n\n");

    if is_lib {
        content.push_str(&format!(
            "@[default_target]\nlean_lib {name} where\n  roots := #[`{name}]\n"
        ));
    } else {
        content.push_str(&format!(
            "@[default_target]\nlean_exe {name} where\n  root := `Main\n"
        ));
    }

    std::fs::write(dir.join("lakefile.lean"), content)?;
    Ok(())
}

/// Write `lean-toolchain` for a new project.
fn write_lean_toolchain(dir: &Path) -> LakeResult<()> {
    std::fs::write(dir.join("lean-toolchain"), DEFAULT_CLEAN_TOOLCHAIN)?;
    Ok(())
}

/// Write library scaffold: `<Name>.lean` root module.
fn write_lib_scaffold(dir: &Path, name: &str) -> LakeResult<()> {
    let module_content =
        format!("-- {name}: auto-generated by clean lake init\n\ndef hello := \"world\"\n");
    std::fs::write(dir.join(format!("{name}.lean")), module_content)?;
    Ok(())
}

/// Write executable scaffold: `Main.lean`.
fn write_exe_scaffold(dir: &Path, name: &str) -> LakeResult<()> {
    let main_content = format!(
        "-- {name}: auto-generated by clean lake init\n\n\
         def main : IO Unit :=\n  IO.println \"Hello, {name}!\"\n"
    );
    std::fs::write(dir.join("Main.lean"), main_content)?;
    Ok(())
}

// ---------------------------------------------------------------------------
// Update
// ---------------------------------------------------------------------------

/// Execute `lake update` — pull latest revisions for all git deps.
pub(super) fn lake_update(args: &UpdateArgs) -> LakeResult<String> {
    let dir = resolve_project_dir(args.dir.as_deref())?;
    let ws = Workspace::load(&dir)?;

    let manifest = ws.manifest().cloned().unwrap_or_else(LakeManifest::empty);

    if manifest.packages.is_empty() {
        return Ok("No dependencies to update.\n".to_string());
    }

    let fm = FetchManager::new(ws.root(), &ws.packages_dir());
    let (new_manifest, results) = fm.update_all(&manifest)?;

    // Persist the updated manifest
    let manifest_path = ws.root().join("lake-manifest.json");
    new_manifest.save(&manifest_path)?;

    Ok(format_update_results(&results))
}

/// Format update results into a human-readable summary.
pub(super) fn format_update_results(results: &[crate::fetch::UpdateResult]) -> String {
    use crate::fetch::UpdateStatus;

    let mut out = String::new();
    let mut updated = 0u32;
    let mut up_to_date = 0u32;
    let mut errors = 0u32;

    for r in results {
        match &r.status {
            UpdateStatus::Updated => {
                out.push_str(&format!(
                    "  Updated {}: {} -> {}\n",
                    r.name,
                    short_rev(&r.old_rev),
                    short_rev(&r.new_rev),
                ));
                updated += 1;
            }
            UpdateStatus::UpToDate => {
                up_to_date += 1;
            }
            UpdateStatus::Skipped => {}
            UpdateStatus::Error(msg) => {
                out.push_str(&format!("  ERROR {}: {msg}\n", r.name));
                errors += 1;
            }
        }
    }

    out.push_str(&format!(
        "Update complete: {updated} updated, {up_to_date} up-to-date, {errors} errors\n"
    ));
    out
}

/// Abbreviate a git SHA to (at most) 12 characters.
///
/// Truncation is on a UTF-8 **character** boundary, not a raw byte offset. For a
/// well-formed git SHA (40 ASCII hex chars) this yields exactly the first 12
/// bytes, unchanged. But `rev` originates from an unvalidated `rev` string in
/// `lake-manifest.json` (see `manifest::GitPackage::rev`); a non-ASCII value
/// whose byte index 12 lands mid-codepoint would make `&rev[..12]` panic
/// (`byte index 12 is not a char boundary`). Slicing at the 12th `char` boundary
/// avoids that while preserving the fast, correct ASCII path.
pub(super) fn short_rev(rev: &str) -> &str {
    match rev.char_indices().nth(12) {
        Some((byte_idx, _)) => &rev[..byte_idx],
        // Fewer than 13 chars: nothing to truncate.
        None => rev,
    }
}

// ---------------------------------------------------------------------------
// Fetch
// ---------------------------------------------------------------------------

/// Execute `lake fetch` — prefetch every dependency source.
///
/// Unlike [`lake_update`], this never rewrites `lake-manifest.json`; it only
/// clones/checks out the revisions already pinned in the manifest so that a
/// subsequent build has all sources available offline.
pub(super) fn lake_fetch(args: &FetchArgs) -> LakeResult<String> {
    let dir = resolve_project_dir(args.dir.as_deref())?;
    let ws = Workspace::load(&dir)?;

    let manifest = ws.manifest().cloned().unwrap_or_else(LakeManifest::empty);

    if manifest.packages.is_empty() {
        return Ok("No dependencies to fetch.\n".to_string());
    }

    if manifest
        .packages
        .iter()
        .any(crate::manifest::ManifestPackage::is_git)
        && !FetchManager::git_available()
    {
        return Err(LakeError::GitError {
            operation: "fetch".to_string(),
            message: "git is not available; install git to fetch dependencies".to_string(),
        });
    }

    let fm = FetchManager::new(ws.root(), &ws.packages_dir());
    let fetched = fm.fetch_all(&manifest)?;

    Ok(format_fetch_results(&fetched))
}

/// Format the names returned by [`FetchManager::fetch_all`] into a summary.
pub(super) fn format_fetch_results(fetched: &[String]) -> String {
    if fetched.is_empty() {
        return "All dependencies already present.\n".to_string();
    }

    let mut out = format!("Fetched {} dependencies:\n", fetched.len());
    for name in fetched {
        out.push_str(&format!("  {name}\n"));
    }
    out
}

// ---------------------------------------------------------------------------
// Run
// ---------------------------------------------------------------------------

/// Execute `lake run` — build an executable target and locate its binary.
///
/// This builds the selected target via [`BuildContext`] and then resolves the
/// path to the produced native executable. It does not itself spawn the binary;
/// instead it returns a summary naming the resolved executable and the command
/// line that would run it (including any forwarded `args`). Spawning is left to
/// the binary front-end, which owns process/exit-code forwarding semantics.
pub(super) fn lake_run(args: &RunArgs) -> LakeResult<String> {
    let dir = resolve_project_dir(args.dir.as_deref())?;
    let ws = Workspace::load(&dir)?;

    let exe = select_executable(ws.config(), args.target.as_deref())?;

    let options = BuildOptions::new()
        .with_jobs(args.jobs)
        .with_verbose(args.verbose);
    let mut ctx = BuildContext::new(ws).with_options(options);
    let result = ctx.build_target(&exe.name)?;

    let mut summary = String::new();
    summary.push_str(&format_build_result(&result));

    if !result.is_success() {
        return Err(LakeError::BuildFailed {
            module: exe.name.clone(),
            reason: format!("{} module(s) failed to build", result.failed.len()),
        });
    }

    match native_executable_path(ctx.workspace(), &exe.name) {
        Some(path) => {
            summary.push_str(&format!("Executable: {}\n", path.display()));
            summary.push_str(&format!(
                "Would run: {}\n",
                format_run_command(&path, &args.args)
            ));
        }
        None => {
            let expected = native_executable_build_path(ctx.workspace(), &exe.name);
            summary.push_str(&format!(
                "Built target '{}' but no native executable artifact was found at {}.\n",
                exe.name,
                expected.display()
            ));
        }
    }

    Ok(summary)
}

/// Select the executable target to run.
///
/// Resolution order: explicit `target` name, then a `@[default_target]` that is
/// an executable, then the sole executable if exactly one is defined.
pub(super) fn select_executable(
    config: &crate::config::LakeConfig,
    target: Option<&str>,
) -> LakeResult<LeanExe> {
    if let Some(name) = target {
        return config
            .exes
            .iter()
            .find(|e| e.name == name)
            .cloned()
            .ok_or_else(|| LakeError::ModuleNotFound(name.to_string()));
    }

    if let Some(default) = config
        .default_targets
        .iter()
        .find_map(|t| config.exes.iter().find(|exe| &exe.name == t).cloned())
    {
        return Ok(default);
    }

    match config.exes.as_slice() {
        [single] => Ok(single.clone()),
        [] => Err(LakeError::InvalidConfig(
            "no executable targets defined; declare one with `lean_exe` in lakefile.lean"
                .to_string(),
        )),
        _ => Err(LakeError::InvalidConfig(
            "multiple executables found; specify one with `lake run <target>`".to_string(),
        )),
    }
}

/// Expected location of the native executable produced for a target.
pub(super) fn native_executable_build_path(workspace: &Workspace, name: &str) -> PathBuf {
    workspace
        .build_dir()
        .join("bin")
        .join(native_executable_file_name(name))
}

/// Resolve the produced native executable, checking the canonical `bin/`
/// location first and the `lib/` fallback second.
pub(super) fn native_executable_path(workspace: &Workspace, name: &str) -> Option<PathBuf> {
    let primary = native_executable_build_path(workspace, name);
    if primary.exists() {
        return Some(primary);
    }

    let fallback = workspace
        .build_dir()
        .join("lib")
        .join(native_executable_file_name(name));
    fallback.exists().then_some(fallback)
}

/// Platform-specific executable file name (adds `.exe` on Windows).
fn native_executable_file_name(name: &str) -> String {
    #[cfg(windows)]
    {
        format!("{name}.exe")
    }
    #[cfg(not(windows))]
    {
        name.to_string()
    }
}

/// Render the command line that would launch `path` with `args`.
pub(super) fn format_run_command(path: &Path, args: &[String]) -> String {
    let mut cmd = path.display().to_string();
    for arg in args {
        cmd.push(' ');
        cmd.push_str(arg);
    }
    cmd
}

// ---------------------------------------------------------------------------
// Exe
// ---------------------------------------------------------------------------

/// Execute `lake exe` — locate a named executable target's native binary.
///
/// Unlike [`lake_run`], this does not rebuild the target; it resolves the
/// executable by name in the lakefile and reports the produced native artifact
/// (or that no artifact was found). Spawning is left to the binary front-end,
/// which owns process/exit-code forwarding semantics.
pub(super) fn lake_exe(args: &ExeArgs) -> LakeResult<String> {
    let dir = resolve_project_dir(args.dir.as_deref())?;
    let ws = Workspace::load(&dir)?;

    // Resolve strictly by name: `lake exe` always names its target explicitly.
    let exe = select_executable(ws.config(), Some(&args.name))?;

    let mut summary = String::new();
    match native_executable_path(&ws, &exe.name) {
        Some(path) => {
            summary.push_str(&format!("Executable: {}\n", path.display()));
            summary.push_str(&format!(
                "Would run: {}\n",
                format_run_command(&path, &args.args)
            ));
        }
        None => {
            let expected = native_executable_build_path(&ws, &exe.name);
            summary.push_str(&format!(
                "Target '{}' has no native executable artifact at {}; \
                 run `lake run {}` (or `lake build`) to produce it first.\n",
                exe.name,
                expected.display(),
                exe.name,
            ));
        }
    }

    Ok(summary)
}

// ---------------------------------------------------------------------------
// Test
// ---------------------------------------------------------------------------

/// Execute `lake test` — build the package test targets and locate their
/// produced native binaries.
///
/// Resolution mirrors `lake run`: when `target` is `None`, every `lean_test`
/// declared in the lakefile is selected; when set, an exact name match is tried
/// first, then a substring filter. Each selected test target is built and its
/// native executable artifact is located. As in [`lake_run`], this crate has no
/// native runtime, so the handler reports the resolved test binary and the
/// command line that would run it rather than spawning it; spawning is owned by
/// the binary front-end.
pub(super) fn lake_test(args: &TestArgs) -> LakeResult<String> {
    let dir = resolve_project_dir(args.dir.as_deref())?;
    let ws = Workspace::load(&dir)?;

    let tests = select_tests(ws.config(), args.target.as_deref())?;

    let options = BuildOptions::new()
        .with_jobs(args.jobs)
        .with_verbose(args.verbose);
    let mut ctx = BuildContext::new(ws).with_options(options);

    let mut summary = format!("Running {} test target(s)\n", tests.len());
    for test in &tests {
        summary.push_str(&format!("Test '{}' (root {})\n", test.name, test.root));

        let result = ctx.build_target(&test.name)?;
        summary.push_str(&format_build_result(&result));

        if !result.is_success() {
            return Err(LakeError::BuildFailed {
                module: test.name.clone(),
                reason: format!("{} module(s) failed to build", result.failed.len()),
            });
        }

        match native_executable_path(ctx.workspace(), &test.name) {
            Some(path) => {
                summary.push_str(&format!("  Test executable: {}\n", path.display()));
                summary.push_str(&format!(
                    "  Would run: {}\n",
                    format_run_command(&path, &args.args)
                ));
            }
            None => {
                let expected = native_executable_build_path(ctx.workspace(), &test.name);
                summary.push_str(&format!(
                    "  Built test target '{}' but no native executable artifact was found at {}.\n",
                    test.name,
                    expected.display()
                ));
            }
        }
    }

    Ok(summary)
}

/// Select the test targets to run.
///
/// With no `target`, every declared test is returned. With a `target`, an exact
/// name match wins; otherwise a substring filter is applied. An error is
/// returned when no tests are declared or the filter matches nothing.
pub(super) fn select_tests(
    config: &crate::config::LakeConfig,
    target: Option<&str>,
) -> LakeResult<Vec<crate::config::LeanTest>> {
    if config.tests.is_empty() {
        return Err(LakeError::InvalidConfig(
            "no test targets defined; declare one with `lean_test` in lakefile.lean".to_string(),
        ));
    }

    let Some(target) = target else {
        return Ok(config.tests.clone());
    };

    if let Some(test) = config.tests.iter().find(|t| t.name == target) {
        return Ok(vec![test.clone()]);
    }

    let matches: Vec<_> = config
        .tests
        .iter()
        .filter(|t| t.name.contains(target))
        .cloned()
        .collect();
    if matches.is_empty() {
        return Err(LakeError::ModuleNotFound(target.to_string()));
    }
    Ok(matches)
}

// ---------------------------------------------------------------------------
// Env
// ---------------------------------------------------------------------------

/// Execute `lake env` — print the resolved Lake environment as `key=value`
/// lines.
///
/// The output is portable and never touches the network. It exposes the search
/// path Clean would assemble for a build (`LEAN_PATH`), the workspace root, the
/// resolved toolchain, and the package source directories. Each line is
/// `KEY=VALUE` so callers can parse it with a simple split or `eval`.
pub(super) fn lake_env(args: &EnvArgs) -> LakeResult<String> {
    let dir = resolve_project_dir(args.dir.as_deref())?;
    let ws = Workspace::load(&dir)?;

    Ok(format_env(&ws))
}

/// Render the resolved Lake environment for [`Workspace`] as `key=value` lines.
pub(super) fn format_env(ws: &Workspace) -> String {
    let mut out = String::new();

    out.push_str(&format!("LAKE_PACKAGE={}\n", ws.config().package.name));
    out.push_str(&format!("LAKE_ROOT={}\n", ws.root().display()));
    out.push_str(&format!("LEAN_PATH={}\n", format_lean_path(ws)));
    out.push_str(&format!("LEAN_SRC_PATH={}\n", ws.src_dir().display()));

    match ws.toolchain_version().or_else(|| ws.toolchain()) {
        Some(toolchain) => out.push_str(&format!("LEAN_TOOLCHAIN={toolchain}\n")),
        None => out.push_str("LEAN_TOOLCHAIN=\n"),
    }

    out
}

/// Assemble the `LEAN_PATH` search list: the workspace lib (`.olean`) directory
/// first, then each fetched/path dependency package directory, joined by the
/// platform path separator.
fn format_lean_path(ws: &Workspace) -> String {
    let mut entries: Vec<PathBuf> = vec![ws.lib_dir()];
    entries.extend(ws.package_dirs());

    let joined = entries
        .iter()
        .map(|p| p.display().to_string())
        .collect::<Vec<_>>()
        .join(lean_path_separator());
    joined
}

/// Platform path-list separator (`;` on Windows, `:` elsewhere).
fn lean_path_separator() -> &'static str {
    if cfg!(windows) {
        ";"
    } else {
        ":"
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Resolve the project directory, defaulting to the current working directory.
/// Returns an error if the resolved directory does not contain `lakefile.lean`.
pub(super) fn resolve_project_dir(dir: Option<&Path>) -> LakeResult<PathBuf> {
    let dir = match dir {
        Some(d) => d.to_path_buf(),
        None => std::env::current_dir().map_err(LakeError::Io)?,
    };

    let lakefile = dir.join("lakefile.lean");
    if !lakefile.exists() {
        return Err(LakeError::LakefileNotFound(dir));
    }

    Ok(dir)
}
