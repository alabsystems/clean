// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Executable running, testing, and Lean interpreter integration.

use crate::cmd_core::resolve_project_dir;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus};

#[derive(Debug)]
struct NativeExecutableExit {
    status: ExitStatus,
}

impl NativeExecutableExit {
    fn code(&self) -> Option<i32> {
        self.status.code()
    }
}

impl std::fmt::Display for NativeExecutableExit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Executable exited with status {}", self.status)
    }
}

impl std::error::Error for NativeExecutableExit {}

#[derive(Debug)]
struct NativeTestFailures {
    failures: Vec<(String, String)>,
    forwarded_code: Option<i32>,
}

impl NativeTestFailures {
    fn code(&self) -> Option<i32> {
        self.forwarded_code
    }
}

impl std::fmt::Display for NativeTestFailures {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} test(s) failed:\n{}",
            self.failures.len(),
            format_test_failures(&self.failures)
        )
    }
}

impl std::error::Error for NativeTestFailures {}

pub(crate) fn native_executable_exit_code(err: &anyhow::Error) -> Option<i32> {
    err.downcast_ref::<NativeExecutableExit>()
        .and_then(NativeExecutableExit::code)
        .or_else(|| {
            err.downcast_ref::<NativeTestFailures>()
                .and_then(NativeTestFailures::code)
        })
}

/// Run an executable target
pub(super) fn lake_run(
    target: Option<String>,
    args: &[String],
    verbose: bool,
    jobs: usize,
    dir: Option<PathBuf>,
) -> anyhow::Result<()> {
    use clean_lake::{BuildContext, BuildOptions, Workspace};

    let cwd = resolve_project_dir(dir)?;
    let config = super::load_project_config(&cwd)?;
    let exe = select_executable(&config, target.as_deref(), &cwd)?;

    if verbose {
        println!("Running executable target '{}'", exe.name);
    }

    let ws = Workspace::from_config(&cwd, config);
    let mut ctx = BuildContext::new(ws)
        .with_options(BuildOptions::new().with_jobs(jobs).with_verbose(verbose));

    let result = ctx.build_target(&exe.name)?;
    if !result.failed.is_empty() {
        match ensure_and_run_executable(ctx.workspace(), &exe, args, verbose) {
            Ok(()) => return Ok(()),
            Err(native_err) => {
                if native_executable_exit_code(&native_err).is_some() {
                    return Err(native_err);
                }
                for (module, err) in &result.failed {
                    eprintln!("build error in {module}: {err}");
                }
                let build_failures = format_build_failures(&result.failed);
                anyhow::bail!(
                    "build failed and native executable production failed; aborting run.\n\
                     Native blocker: {native_err:#}\n\
                     Build failures:\n{build_failures}"
                );
            }
        }
    }

    if verbose {
        println!(
            "Built executable in {:.2}s ({} modules)",
            result.duration.as_secs_f64(),
            result.total()
        );
    }

    ensure_and_run_executable(ctx.workspace(), &exe, args, verbose)
}

fn select_executable(
    config: &clean_lake::LakeConfig,
    target: Option<&str>,
    workspace_root: &Path,
) -> anyhow::Result<clean_lake::LeanExe> {
    if let Some(name) = target {
        if let Some(exe) = config.exes.iter().find(|e| e.name == name) {
            return Ok(exe.clone());
        }
        anyhow::bail!(
            "clean lake run is fail-closed: executable target '{name}' not found in workspace {}",
            workspace_root.display()
        );
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
        [] => anyhow::bail!("No executable targets defined. Use `lean_exe` in lakefile.lean."),
        _ => {
            anyhow::bail!("Multiple executables found. Specify one with `clean lake run <target>`.")
        }
    }
}

fn ensure_and_run_executable(
    workspace: &clean_lake::Workspace,
    exe: &clean_lake::LeanExe,
    args: &[String],
    verbose: bool,
) -> anyhow::Result<()> {
    let module_path = workspace
        .find_module(&exe.root)
        .ok_or_else(|| anyhow::anyhow!("Root module '{}' not found", exe.root))?;

    if verbose {
        println!(
            "Prepared executable target '{}' (root module {})",
            exe.name,
            module_path.display()
        );
    }

    super::build::ensure_native_artifacts_for_executable_targets(workspace, Some(&exe.name))?;

    if let Some(native_path) = native_executable_path(workspace, &exe.name) {
        return run_native_executable(workspace, &native_path, args, verbose);
    }

    anyhow::bail!(
        "clean lake run is fail-closed: clean can build target '{}' but cannot \
         execute root module '{}' without a native clean runtime/interpreter bridge. \
         Refusing to delegate to external `lean --run`, and no native executable artifact was found \
         at {}. Built artifacts are available under {}.",
        exe.name,
        exe.root,
        native_executable_build_path(workspace, &exe.name).display(),
        workspace.build_dir().display()
    )
}

pub(super) fn native_executable_build_path(
    workspace: &clean_lake::Workspace,
    name: &str,
) -> PathBuf {
    let exe_name = native_executable_file_name(name);
    workspace.build_dir().join("bin").join(exe_name)
}

pub(super) fn native_executable_path(
    workspace: &clean_lake::Workspace,
    name: &str,
) -> Option<PathBuf> {
    let exe_path = native_executable_build_path(workspace, name);
    if exe_path.exists() {
        return Some(exe_path);
    }

    let alt_exe_path = workspace
        .build_dir()
        .join("lib")
        .join(native_executable_file_name(name));
    alt_exe_path.exists().then_some(alt_exe_path)
}

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

/// Run a native executable by name
pub(super) fn lake_exe(
    name: &str,
    args: &[String],
    verbose: bool,
    dir: Option<PathBuf>,
) -> anyhow::Result<()> {
    use clean_lake::{BuildContext, BuildOptions, Workspace};

    let cwd = resolve_project_dir(dir)?;
    let config = super::load_project_config(&cwd)?;

    // Find the executable target
    let exe = config.exes.iter().find(|e| e.name == name).ok_or_else(|| {
        anyhow::anyhow!(
            "clean lake exe is fail-closed: executable target '{name}' not found in workspace {}",
            cwd.display()
        )
    })?;

    if verbose {
        println!("Running native executable '{name}'");
    }

    // Build the executable first
    let ws = Workspace::from_config(&cwd, config.clone());
    let mut ctx = BuildContext::new(ws).with_options(BuildOptions::new().with_verbose(verbose));

    let result = ctx.build_target(&exe.name)?;
    if !result.failed.is_empty() {
        match ensure_and_run_executable(ctx.workspace(), exe, args, verbose) {
            Ok(()) => return Ok(()),
            Err(native_err) => {
                if native_executable_exit_code(&native_err).is_some() {
                    return Err(native_err);
                }
                for (module, err) in &result.failed {
                    eprintln!("build error in {module}: {err}");
                }
                let build_failures = format_build_failures(&result.failed);
                anyhow::bail!(
                    "build failed and native executable production failed; aborting exe.\n\
                     Native blocker: {native_err:#}\n\
                     Build failures:\n{build_failures}"
                );
            }
        }
    }

    ensure_and_run_executable(ctx.workspace(), exe, args, verbose)
}

/// Run a native executable at the given path
fn run_native_executable(
    workspace: &clean_lake::Workspace,
    path: &Path,
    args: &[String],
    verbose: bool,
) -> anyhow::Result<()> {
    if verbose {
        println!(
            "Executing {path:?} {args:?} from {}",
            workspace.root().display()
        );
    }

    let status = Command::new(path)
        .current_dir(workspace.root())
        .args(args)
        .status()
        .map_err(|e| anyhow::anyhow!("Failed to execute {path:?}: {e}"))?;

    if !status.success() {
        return Err(NativeExecutableExit { status }.into());
    }

    Ok(())
}

/// Build (if needed) and execute a synthetic native executable target, forwarding
/// `args` to it and preserving the child exit code via [`native_executable_exit_code`].
///
/// This is the shared run path for surfaces that synthesize a `main : IO Unit`
/// executable target on the fly (for example `lake script run`, where the script
/// body is lowered into a `def main` module) rather than reading a `lean_exe`
/// declaration straight from the lakefile.
pub(super) fn build_and_run_synthetic_executable(
    workspace: &clean_lake::Workspace,
    exe: &clean_lake::LeanExe,
    args: &[String],
    verbose: bool,
) -> anyhow::Result<()> {
    let native_path = super::build::ensure_native_artifact_for_executable(workspace, exe)?;
    run_native_executable(workspace, &native_path, args, verbose)
}

fn format_build_failures(failed: &[(String, String)]) -> String {
    failed
        .iter()
        .map(|(module, err)| format!("build failed for {module}: {err}"))
        .collect::<Vec<_>>()
        .join("\n")
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum NativeTestRootShape {
    BoundedNativeMain,
    UnsupportedMainSignatureBoundary,
    UnsupportedMainArgsBoundary,
    UnsupportedMainExceptionHandlingBoundary,
    UnsupportedMainCurrentDirBoundary,
    UnsupportedMainExitBoundary,
    UnsupportedMainRuntimeBoundary,
    UnsupportedMainEnvBoundary,
    UnsupportedMainFileBoundary,
    UnsupportedMainHandleBoundary,
    UnsupportedMainProcessBoundary,
    UnsupportedMainTaskBoundary,
    UnsupportedMainTimeBoundary,
    UnsupportedMainRefBoundary,
    UnsupportedMainStdinBoundary,
    UnsupportedMainStderrBoundary,
    AssertionDiscoveryBoundary,
    OtherNonMain,
}

fn module_source_native_test_shape(module_path: &Path) -> anyhow::Result<NativeTestRootShape> {
    let source = std::fs::read_to_string(module_path).map_err(|err| {
        anyhow::anyhow!(
            "could not read test root module '{}' before native Lake test handoff: {err}",
            module_path.display()
        )
    })?;

    let declares_main = source.lines().any(|line| {
        let line = line.trim_start();
        line.strip_prefix("def main").is_some_and(
            |rest| matches!(rest.chars().next(), Some(c) if c.is_whitespace() || c == ':'),
        )
    });
    let declares_bounded_main = source.lines().any(|line| {
        let line = line.trim_start();
        line.strip_prefix("def main").is_some_and(
            |rest| matches!(rest.chars().next(), Some(c) if c.is_whitespace() || c == ':'),
        ) && line.contains(": IO Unit")
    });
    if declares_bounded_main {
        let contains_unsupported_main_signature = source.lines().any(|line| {
            let line = line.trim_start();
            line.strip_prefix("def main")
                .is_some_and(|rest| rest.trim_start().starts_with('('))
                && line.contains(": IO Unit")
        });
        if contains_unsupported_main_signature {
            return Ok(NativeTestRootShape::UnsupportedMainSignatureBoundary);
        }

        let contains_unsupported_stderr_runtime =
            source.lines().any(|line| line.contains("IO.eprintln"));
        if contains_unsupported_stderr_runtime {
            return Ok(NativeTestRootShape::UnsupportedMainStderrBoundary);
        }

        let contains_unsupported_stdin_runtime =
            source.lines().any(|line| line.contains("IO.getLine"));
        if contains_unsupported_stdin_runtime {
            return Ok(NativeTestRootShape::UnsupportedMainStdinBoundary);
        }

        let contains_unsupported_env_runtime =
            source.lines().any(|line| line.contains("IO.getEnv"));
        if contains_unsupported_env_runtime {
            return Ok(NativeTestRootShape::UnsupportedMainEnvBoundary);
        }

        let contains_unsupported_file_runtime = source.lines().any(|line| line.contains("IO.FS."));
        if contains_unsupported_file_runtime {
            return Ok(NativeTestRootShape::UnsupportedMainFileBoundary);
        }

        let contains_unsupported_handle_runtime = source.lines().any(|line| {
            line.contains("IO.getStdout")
                || line.contains("IO.getStderr")
                || line.contains("IO.getStdin")
        });
        if contains_unsupported_handle_runtime {
            return Ok(NativeTestRootShape::UnsupportedMainHandleBoundary);
        }

        let contains_unsupported_process_runtime = source.lines().any(|line| {
            line.contains("IO.Process.")
                && !line.contains("IO.Process.exit")
                && !line.contains("IO.Process.ExitCode")
        });
        if contains_unsupported_process_runtime {
            return Ok(NativeTestRootShape::UnsupportedMainProcessBoundary);
        }

        let contains_unsupported_args_runtime =
            source.lines().any(|line| line.contains("IO.getArgs"));
        if contains_unsupported_args_runtime {
            return Ok(NativeTestRootShape::UnsupportedMainArgsBoundary);
        }

        let contains_unsupported_time_runtime = source.lines().any(|line| {
            line.contains("IO.sleep")
                || line.contains("IO.mono")
                || line.contains("IO.getTime")
                || line.contains("IO.msleep")
        });
        if contains_unsupported_time_runtime {
            return Ok(NativeTestRootShape::UnsupportedMainTimeBoundary);
        }

        let contains_unsupported_task_runtime = source.lines().any(|line| {
            line.contains("asTask")
                || line.contains("Task.")
                || line.contains("IO.Promise")
                || line.contains("BaseIO.asTask")
        });
        if contains_unsupported_task_runtime {
            return Ok(NativeTestRootShape::UnsupportedMainTaskBoundary);
        }

        let contains_unsupported_exception_handling = source.lines().any(|line| {
            let line = line.trim_start();
            line.starts_with("catch ") || line.starts_with("catch_") || line.contains(" catch ")
        });
        if contains_unsupported_exception_handling {
            return Ok(NativeTestRootShape::UnsupportedMainExceptionHandlingBoundary);
        }

        let contains_unsupported_ref_runtime = source
            .lines()
            .any(|line| line.contains("IO.mkRef") || line.contains("IO.Ref"));
        if contains_unsupported_ref_runtime {
            return Ok(NativeTestRootShape::UnsupportedMainRefBoundary);
        }

        let contains_unsupported_current_dir_runtime = source
            .lines()
            .any(|line| line.contains("IO.currentDir") || line.contains("IO.setCurrentDir"));
        if contains_unsupported_current_dir_runtime {
            return Ok(NativeTestRootShape::UnsupportedMainCurrentDirBoundary);
        }

        let contains_unsupported_exit_runtime =
            source.lines().any(|line| line.contains("IO.Process.exit"));
        if contains_unsupported_exit_runtime {
            return Ok(NativeTestRootShape::UnsupportedMainExitBoundary);
        }

        let contains_unsupported_main_runtime = source.lines().any(|line| {
            line.contains("IO.throw")
                || line.contains("IO.userError")
                || line.contains("assert!")
                || line.contains("panic!")
                || line.contains("panic ")
        });
        if contains_unsupported_main_runtime {
            return Ok(NativeTestRootShape::UnsupportedMainRuntimeBoundary);
        }
        return Ok(NativeTestRootShape::BoundedNativeMain);
    }
    if declares_main {
        return Ok(NativeTestRootShape::UnsupportedMainSignatureBoundary);
    }

    let contains_assertion_discovery_surface = source.lines().any(|line| {
        let line = line.trim_start();
        line.starts_with("example ")
            || line.starts_with("theorem ")
            || line.starts_with("#eval")
            || line.starts_with("#check")
    });
    if contains_assertion_discovery_surface {
        return Ok(NativeTestRootShape::AssertionDiscoveryBoundary);
    }

    Ok(NativeTestRootShape::OtherNonMain)
}

/// Run tests
#[cfg(test)]
pub(super) fn lake_test(
    target: Option<String>,
    verbose: bool,
    jobs: usize,
    dir: Option<PathBuf>,
) -> anyhow::Result<()> {
    lake_test_with_args(target, &[], verbose, jobs, dir)
}

/// Run tests with arguments forwarded to the native test executable.
pub(super) fn lake_test_with_args(
    target: Option<String>,
    args: &[String],
    verbose: bool,
    jobs: usize,
    dir: Option<PathBuf>,
) -> anyhow::Result<()> {
    use clean_lake::{BuildContext, BuildOptions, Workspace};

    let cwd = resolve_project_dir(dir)?;
    let config = super::load_project_config(&cwd)?;

    if config.tests.is_empty() {
        anyhow::bail!("No test targets defined in lakefile.lean. Use `lean_test` to define tests.");
    }

    let tests_to_run = select_tests_to_run(&config, target.as_deref(), &cwd)?;

    if verbose {
        println!("Running {} test(s)...", tests_to_run.len());
    }

    let ws = Workspace::from_config(&cwd, config.clone());
    let ctx = BuildContext::new(ws)
        .with_options(BuildOptions::new().with_jobs(jobs).with_verbose(verbose));

    let mut total_passed = 0;
    let mut test_failures = Vec::new();
    let mut forwarded_code = None;
    let start = std::time::Instant::now();

    for test in &tests_to_run {
        if verbose {
            println!("Running test: {}", test.name);
        }

        // Resolve the test module so missing roots are reported before the
        // fail-closed runtime boundary.
        let module_path = ctx
            .workspace()
            .find_module(&test.root)
            .ok_or_else(|| anyhow::anyhow!("Test root module '{}' not found", test.root))?;

        match module_source_native_test_shape(&module_path)? {
            NativeTestRootShape::BoundedNativeMain => {}
            NativeTestRootShape::UnsupportedMainSignatureBoundary => {
                anyhow::bail!(
                    "clean lake test is fail-closed for test target '{}': clean resolved \
                     test root '{}' at '{}' and found an unsupported `main` signature. The \
                     native Lake test bridge currently supports only the bounded no-argument \
                     entrypoint `main : IO Unit`; unsupported or parameterized `main` signatures \
                     are not implemented for native test execution. Refusing to delegate to \
                     external `lean --run`.",
                    test.name,
                    test.root,
                    module_path.display()
                );
            }
            NativeTestRootShape::UnsupportedMainArgsBoundary => {
                anyhow::bail!(
                    "clean lake test is fail-closed for test target '{}': clean resolved \
                     test root '{}' at '{}' and found `main : IO Unit`, but Lean-authored \
                     command-line argument reads such as IO.getArgs are not implemented by the \
                     native Lake executable bridge. This path currently supports stdout \
                     IO.print/IO.println only. Refusing to delegate to external `lean --run`.",
                    test.name,
                    test.root,
                    module_path.display()
                );
            }
            NativeTestRootShape::UnsupportedMainTimeBoundary => {
                anyhow::bail!(
                    "clean lake test is fail-closed for test target '{}': clean resolved \
                     test root '{}' at '{}' and found `main : IO Unit`, but Lean-authored \
                     sleep/time runtime such as IO.sleep is not implemented by the native Lake \
                     executable bridge. This path currently supports stdout IO.print/IO.println \
                     only. Refusing to delegate to external `lean --run`.",
                    test.name,
                    test.root,
                    module_path.display()
                );
            }
            NativeTestRootShape::UnsupportedMainTaskBoundary => {
                anyhow::bail!(
                    "clean lake test is fail-closed for test target '{}': clean resolved \
                     test root '{}' at '{}' and found `main : IO Unit`, but Lean-authored \
                     task/thread runtime such as IO.asTask is not implemented by the native Lake \
                     executable bridge. This path currently supports stdout IO.print/IO.println \
                     only. Refusing to delegate to external `lean --run`.",
                    test.name,
                    test.root,
                    module_path.display()
                );
            }
            NativeTestRootShape::UnsupportedMainExceptionHandlingBoundary => {
                anyhow::bail!(
                    "clean lake test is fail-closed for test target '{}': clean resolved \
                     test root '{}' at '{}' and found `main : IO Unit`, but Lean-authored \
                     exception handling such as try/catch is not implemented by the native Lake \
                     executable bridge. This path currently supports stdout IO.print/IO.println \
                     only. Refusing to delegate to external `lean --run`.",
                    test.name,
                    test.root,
                    module_path.display()
                );
            }
            NativeTestRootShape::UnsupportedMainRefBoundary => {
                anyhow::bail!(
                    "clean lake test is fail-closed for test target '{}': clean resolved \
                     test root '{}' at '{}' and found `main : IO Unit`, but Lean-authored \
                     mutable reference runtime such as IO.mkRef is not implemented by the native \
                     Lake executable bridge. This path currently supports stdout \
                     IO.print/IO.println only. Refusing to delegate to external `lean --run`.",
                    test.name,
                    test.root,
                    module_path.display()
                );
            }
            NativeTestRootShape::UnsupportedMainCurrentDirBoundary => {
                anyhow::bail!(
                    "clean lake test is fail-closed for test target '{}': clean resolved \
                     test root '{}' at '{}' and found `main : IO Unit`, but Lean-authored \
                     current-directory runtime such as IO.currentDir is not implemented by the \
                     native Lake executable bridge. This path currently supports stdout \
                     IO.print/IO.println only. Refusing to delegate to external `lean --run`.",
                    test.name,
                    test.root,
                    module_path.display()
                );
            }
            NativeTestRootShape::UnsupportedMainHandleBoundary => {
                anyhow::bail!(
                    "clean lake test is fail-closed for test target '{}': clean resolved \
                     test root '{}' at '{}' and found `main : IO Unit`, but Lean-authored \
                     standard stream handles such as IO.getStdout are not implemented by the \
                     native Lake executable bridge. This path currently supports direct stdout \
                     IO.print/IO.println only. Refusing to delegate to external `lean --run`.",
                    test.name,
                    test.root,
                    module_path.display()
                );
            }
            NativeTestRootShape::UnsupportedMainExitBoundary => {
                anyhow::bail!(
                    "clean lake test is fail-closed for test target '{}': clean resolved \
                     test root '{}' at '{}' and found `main : IO Unit`, but Lean-authored \
                     exit/exception propagation such as IO.Process.exit is not implemented by \
                     the native Lake executable bridge. Refusing to delegate to external \
                     `lean --run`.",
                    test.name,
                    test.root,
                    module_path.display()
                );
            }
            NativeTestRootShape::UnsupportedMainRuntimeBoundary => {
                anyhow::bail!(
                    "clean lake test is fail-closed for test target '{}': clean resolved \
                     test root '{}' at '{}' and found `main : IO Unit`, but Lean-authored \
                     failure/exception propagation such as IO.Process.exit, IO.throw, \
                     assert!, or panic is not implemented by the native Lake executable bridge. \
                     Refusing to delegate to external `lean --run`.",
                    test.name,
                    test.root,
                    module_path.display()
                );
            }
            NativeTestRootShape::UnsupportedMainEnvBoundary => {
                anyhow::bail!(
                    "clean lake test is fail-closed for test target '{}': clean resolved \
                     test root '{}' at '{}' and found `main : IO Unit`, but Lean-authored \
                     environment reads such as IO.getEnv are not implemented by the native Lake \
                     executable bridge. This path currently supports stdout IO.print/IO.println \
                     only. Refusing to delegate to external `lean --run`.",
                    test.name,
                    test.root,
                    module_path.display()
                );
            }
            NativeTestRootShape::UnsupportedMainFileBoundary => {
                anyhow::bail!(
                    "clean lake test is fail-closed for test target '{}': clean resolved \
                     test root '{}' at '{}' and found `main : IO Unit`, but Lean-authored \
                     file IO such as IO.FS.readFile is not implemented by the native Lake \
                     executable bridge. This path currently supports stdout IO.print/IO.println \
                     only. Refusing to delegate to external `lean --run`.",
                    test.name,
                    test.root,
                    module_path.display()
                );
            }
            NativeTestRootShape::UnsupportedMainProcessBoundary => {
                anyhow::bail!(
                    "clean lake test is fail-closed for test target '{}': clean resolved \
                     test root '{}' at '{}' and found `main : IO Unit`, but Lean-authored \
                     process spawning such as IO.Process.output is not implemented by the native \
                     Lake executable bridge. This path currently supports stdout \
                     IO.print/IO.println only. Refusing to delegate to external `lean --run`.",
                    test.name,
                    test.root,
                    module_path.display()
                );
            }
            NativeTestRootShape::UnsupportedMainStdinBoundary => {
                anyhow::bail!(
                    "clean lake test is fail-closed for test target '{}': clean resolved \
                     test root '{}' at '{}' and found `main : IO Unit`, but Lean-authored \
                     stdin reads such as IO.getLine are not implemented by the native Lake \
                     executable bridge. This path currently supports stdout IO.print/IO.println \
                     only. Refusing to delegate to external `lean --run`.",
                    test.name,
                    test.root,
                    module_path.display()
                );
            }
            NativeTestRootShape::UnsupportedMainStderrBoundary => {
                anyhow::bail!(
                    "clean lake test is fail-closed for test target '{}': clean resolved \
                     test root '{}' at '{}' and found `main : IO Unit`, but Lean-authored \
                     stderr emission such as IO.eprintln is not implemented by the native Lake \
                     executable bridge. This path currently supports stdout IO.print/IO.println \
                     only. Refusing to delegate to external `lean --run`.",
                    test.name,
                    test.root,
                    module_path.display()
                );
            }
            NativeTestRootShape::AssertionDiscoveryBoundary => {
                anyhow::bail!(
                    "clean lake test is fail-closed for assertion/discovery-style declarations \
                     in test target '{}': clean resolved test root '{}' at '{}' but native Lake \
                     test discovery/assertion semantics are not implemented. This path only \
                     supports modules that define the bounded native entrypoint `main : IO Unit`. \
                     Refusing to delegate to external `lean --run`.",
                    test.name,
                    test.root,
                    module_path.display()
                );
            }
            NativeTestRootShape::OtherNonMain => {
                anyhow::bail!(
                    "clean lake test is fail-closed for non-main test target '{}': clean resolved \
                 test root '{}' at '{}' but the module does not define the bounded native \
                 entrypoint `main : IO Unit`. native Lake test discovery/assertion semantics \
                 for non-main `lean_test` roots are not implemented. Refusing to delegate to \
                 external `lean --run`.",
                    test.name,
                    test.root,
                    module_path.display()
                );
            }
        }

        let exe = clean_lake::LeanExe {
            name: test.name.clone(),
            root: test.root.clone(),
            more_lean_args: test.more_lean_args.clone(),
            src_dir: test.src_dir.clone(),
            ..Default::default()
        };
        let native_path =
            super::build::ensure_native_artifact_for_executable(ctx.workspace(), &exe).map_err(
                |err| {
                    anyhow::anyhow!(
                        "clean lake test is fail-closed for test target '{}': clean resolved \
                         test root '{}' at '{}' but could not produce the bounded native \
                         test executable at {}. This path only supports test roots that define \
                         `main : IO Unit`. Refusing to delegate to external `lean --run`.\n\
                         Native blocker: {err:#}",
                        test.name,
                        test.root,
                        module_path.display(),
                        native_executable_build_path(ctx.workspace(), &test.name).display()
                    )
                },
            )?;
        match run_native_executable(ctx.workspace(), &native_path, args, verbose) {
            Ok(()) => total_passed += 1,
            Err(err) => {
                if forwarded_code.is_none() {
                    forwarded_code = native_executable_exit_code(&err);
                }
                test_failures.push((test.name.clone(), format!("{err:#}")));
            }
        }
    }

    let elapsed = start.elapsed();
    let total_failed = test_failures.len();
    println!();
    println!(
        "Test results: {} passed, {} failed ({:.2}s)",
        total_passed,
        total_failed,
        elapsed.as_secs_f64()
    );

    if total_failed > 0 {
        return Err(NativeTestFailures {
            failures: test_failures,
            forwarded_code,
        }
        .into());
    }

    Ok(())
}

fn format_test_failures(failures: &[(String, String)]) -> String {
    failures
        .iter()
        .map(|(target, err)| format!("test target {target}: {err}"))
        .collect::<Vec<_>>()
        .join("\n")
}

fn format_available_test_targets(tests: &[clean_lake::LeanTest]) -> String {
    tests
        .iter()
        .map(|test| test.name.as_str())
        .collect::<Vec<_>>()
        .join(", ")
}

fn select_tests_to_run(
    config: &clean_lake::LakeConfig,
    target_or_filter: Option<&str>,
    workspace_root: &Path,
) -> anyhow::Result<Vec<clean_lake::LeanTest>> {
    let Some(target_or_filter) = target_or_filter else {
        return Ok(config.tests.clone());
    };

    if let Some(test) = config
        .tests
        .iter()
        .find(|test| test.name == target_or_filter)
    {
        return Ok(vec![test.clone()]);
    }

    let matches = config
        .tests
        .iter()
        .filter(|test| test.name.contains(target_or_filter))
        .cloned()
        .collect::<Vec<_>>();
    if !matches.is_empty() {
        return Ok(matches);
    }

    anyhow::bail!(
        "Test target or substring filter '{target_or_filter}' not found in lakefile.lean for \
         workspace {}. Available test targets: {}. Refusing to delegate to external \
         `lean --run`.",
        workspace_root.display(),
        format_available_test_targets(&config.tests)
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_lake::Workspace;

    fn write_executable_project(package_name: &str, main_source: &str) -> tempfile::TempDir {
        let dir = tempfile::tempdir().expect("tempdir");
        std::fs::write(
            dir.path().join("lakefile.lean"),
            format!(
                r#"import Lake
open Lake DSL

package {package_name} where
  version := "0.1.0"

@[default_target]
lean_exe {package_name} where
  root := `Main
"#
            ),
        )
        .expect("write lakefile");
        std::fs::write(dir.path().join("Main.lean"), main_source).expect("write Main.lean");
        dir
    }

    fn write_trivial_executable_project() -> tempfile::TempDir {
        write_executable_project("native_run_surface", "def main : IO Unit := pure ()\n")
    }

    /// Write an executable project whose config lives in `lakefile.toml`
    /// (the schema accepted by `LakeConfig::load_from_dir`), proving the unified
    /// loader is wired into the `lake run` surface.
    fn write_toml_executable_project(package_name: &str, main_source: &str) -> tempfile::TempDir {
        let dir = tempfile::tempdir().expect("tempdir");
        std::fs::write(
            dir.path().join("lakefile.toml"),
            format!(
                r#"name = "{package_name}"
defaultTargets = ["{package_name}"]

[[lean_exe]]
name = "{package_name}"
root = "Main"
"#
            ),
        )
        .expect("write lakefile.toml");
        std::fs::write(dir.path().join("Main.lean"), main_source).expect("write Main.lean");
        dir
    }

    /// Regression+fix proof: a `lakefile.toml` project routes through the unified
    /// loader (`load_project_config`) and `lake run` links and executes its
    /// `main : IO Unit`, printing the literal payload. Before the wiring fix the
    /// run surface only probed `lakefile.lean` and bailed with "No lakefile.lean".
    #[test]
    fn lake_run_executes_lakefile_toml_project() {
        let dir = write_toml_executable_project(
            "toml_run_surface",
            "def main : IO Unit := IO.println \"toml works\"\n",
        );

        // The unified loader must recognize the toml project and parse an exe target.
        let config = super::super::load_project_config(dir.path())
            .expect("load_project_config should parse a lakefile.toml project");
        assert_eq!(config.package.name, "toml_run_surface");
        assert_eq!(config.exes.len(), 1, "toml project should expose one exe");
        assert_eq!(config.exes[0].root, "Main");

        lake_run(
            Some("toml_run_surface".to_string()),
            &[],
            false,
            1,
            Some(dir.path().to_path_buf()),
        )
        .expect("lake run should link and execute a lakefile.toml project's main");

        let ws = Workspace::from_config(dir.path(), config);
        let artifact = native_executable_build_path(&ws, "toml_run_surface");
        assert!(
            artifact.exists(),
            "lake run on a toml project should produce a native executable at {}",
            artifact.display()
        );

        let output = Command::new(&artifact)
            .output()
            .expect("linked toml-project artifact should execute");
        assert!(
            output.status.success(),
            "linked toml-project artifact should exit successfully: {output:?}"
        );
        assert_eq!(
            String::from_utf8_lossy(&output.stdout),
            "toml works\n",
            "lake run on a toml project should print the literal payload"
        );
    }

    /// Missing-lakefile diagnostic now mentions both lakefile flavors, since the
    /// unified loader accepts either. A directory with neither must bail with the
    /// friendly hint naming lakefile.toml and lakefile.lean.
    #[test]
    fn lake_run_missing_any_lakefile_names_both_flavors() {
        let dir = tempfile::tempdir().expect("tempdir");
        let err = lake_run(None, &[], false, 1, Some(dir.path().to_path_buf()))
            .expect_err("lake run should bail when no lakefile of either flavor exists");
        let msg = format!("{err:#}");
        assert!(
            msg.contains("lakefile.toml") && msg.contains("lakefile.lean"),
            "missing-lakefile diagnostic should name both flavors: {msg}"
        );
    }

    #[test]
    fn lake_run_missing_executable_target_names_target_and_workspace() {
        let dir = write_trivial_executable_project();

        let err = lake_run(
            Some("missing_target".to_string()),
            &[],
            false,
            1,
            Some(dir.path().to_path_buf()),
        )
        .expect_err("lake run should reject a missing executable target before native handoff");
        let msg = format!("{err:#}");

        assert!(
            msg.contains("missing_target"),
            "diagnostic should name requested target: {msg}"
        );
        assert!(
            msg.contains(&dir.path().display().to_string()),
            "diagnostic should name workspace path: {msg}"
        );
        assert!(
            msg.contains("clean lake run is fail-closed"),
            "diagnostic should name the fail-closed command boundary: {msg}"
        );
    }

    #[test]
    fn lake_exe_missing_executable_target_names_target_and_workspace() {
        let dir = write_trivial_executable_project();

        let err = lake_exe("missing_target", &[], false, Some(dir.path().to_path_buf()))
            .expect_err("lake exe should reject a missing executable target before native handoff");
        let msg = format!("{err:#}");

        assert!(
            msg.contains("missing_target"),
            "diagnostic should name requested target: {msg}"
        );
        assert!(
            msg.contains(&dir.path().display().to_string()),
            "diagnostic should name workspace path: {msg}"
        );
        assert!(
            msg.contains("clean lake exe is fail-closed"),
            "diagnostic should name the fail-closed command boundary: {msg}"
        );
    }

    fn write_test_project(test_name: &str, test_source: &str) -> tempfile::TempDir {
        let dir = tempfile::tempdir().expect("tempdir");
        std::fs::write(
            dir.path().join("lakefile.lean"),
            format!(
                r#"import Lake
open Lake DSL

package native_test_surface where
  version := "0.1.0"

lean_test {test_name} where
  root := `Main
"#
            ),
        )
        .expect("write lakefile");
        std::fs::write(dir.path().join("Main.lean"), test_source).expect("write Main.lean");
        dir
    }

    fn write_multi_test_project() -> tempfile::TempDir {
        let dir = tempfile::tempdir().expect("tempdir");
        std::fs::write(
            dir.path().join("lakefile.lean"),
            r#"import Lake
open Lake DSL

package native_test_surface where
  version := "0.1.0"

lean_test native_test_first where
  root := `First

lean_test native_test_second where
  root := `Second
"#,
        )
        .expect("write lakefile");
        std::fs::write(
            dir.path().join("First.lean"),
            "def main : IO Unit := IO.println \"first ok\"\n",
        )
        .expect("write First.lean");
        std::fs::write(
            dir.path().join("Second.lean"),
            "def main : IO Unit := IO.println \"second ok\"\n",
        )
        .expect("write Second.lean");
        dir
    }

    #[test]
    fn native_executable_path_prefers_build_bin_artifact() {
        let dir = tempfile::tempdir().expect("tempdir");
        let ws = Workspace::new(dir.path(), "native_handoff");
        let exe_path = native_executable_build_path(&ws, "hello");
        std::fs::create_dir_all(exe_path.parent().expect("bin dir")).expect("create bin dir");
        std::fs::write(&exe_path, "").expect("write native artifact");

        assert_eq!(native_executable_path(&ws, "hello"), Some(exe_path));
    }

    #[cfg(unix)]
    #[test]
    fn run_native_executable_executes_existing_artifact() {
        use std::os::unix::fs::PermissionsExt;

        let dir = tempfile::tempdir().expect("tempdir");
        let marker = dir.path().join("marker.txt");
        let exe_path = dir.path().join("hello");
        std::fs::write(
            &exe_path,
            format!("#!/bin/sh\nprintf native > {}\n", marker.display()),
        )
        .expect("write executable script");
        let mut perms = std::fs::metadata(&exe_path)
            .expect("script metadata")
            .permissions();
        perms.set_mode(0o755);
        std::fs::set_permissions(&exe_path, perms).expect("chmod script");

        let ws = Workspace::new(dir.path(), "native_handoff");
        run_native_executable(&ws, &exe_path, &[], false).expect("native artifact should run");

        assert_eq!(
            std::fs::read_to_string(&marker).expect("marker should be written"),
            "native"
        );
    }

    #[test]
    fn lake_run_links_and_executes_trivial_native_artifact() {
        let dir = write_trivial_executable_project();

        lake_run(
            Some("native_run_surface".to_string()),
            &[],
            false,
            1,
            Some(dir.path().to_path_buf()),
        )
        .expect("lake run should link and execute trivial native artifact without Lean4");

        let ws = Workspace::new(dir.path(), "native_run_surface");
        let artifact = native_executable_build_path(&ws, "native_run_surface");
        assert!(
            artifact.exists(),
            "lake run should produce native executable at {}",
            artifact.display()
        );
    }

    #[test]
    fn lake_exe_links_and_executes_trivial_native_artifact() {
        let dir = write_executable_project("native_exe_surface", "def main : IO Unit := pure ()\n");

        lake_exe(
            "native_exe_surface",
            &[],
            false,
            Some(dir.path().to_path_buf()),
        )
        .expect("lake exe should link and execute trivial native artifact without Lean4");

        let ws = Workspace::new(dir.path(), "native_exe_surface");
        let artifact = native_executable_build_path(&ws, "native_exe_surface");
        assert!(
            artifact.exists(),
            "lake exe should produce native executable at {}",
            artifact.display()
        );
    }

    #[test]
    fn lake_run_links_and_executes_println_native_shim_artifact() {
        let dir = write_executable_project(
            "native_run_nontrivial_io",
            "def main : IO Unit := IO.println \"hi\"\n",
        );

        lake_run(
            Some("native_run_nontrivial_io".to_string()),
            &[],
            false,
            1,
            Some(dir.path().to_path_buf()),
        )
        .expect("IO.println native shim should link and execute without Lean4");

        let ws = Workspace::new(dir.path(), "native_run_nontrivial_io");
        let artifact = native_executable_build_path(&ws, "native_run_nontrivial_io");
        let source = dir
            .path()
            .join(".lake/build/native/c/native_run_nontrivial_io.c");
        let emitted_source =
            std::fs::read_to_string(&source).expect("nontrivial IO should emit C source");
        assert!(
            emitted_source.contains("#include <stdio.h>"),
            "IO.println shim should include stdio declarations: {emitted_source}"
        );
        assert!(
            emitted_source.contains("clean_obj* l_IO_println"),
            "IO.println emitted source should include the shared native-build shim: {emitted_source}"
        );
        assert!(
            emitted_source.contains("l_IO_println("),
            "IO.println emitted source should call the native shim: {emitted_source}"
        );
        assert!(
            emitted_source.contains("clean_mk_string(\"hi\")"),
            "IO.println emitted source should lower the string literal payload: {emitted_source}"
        );
        assert!(
            !emitted_source.contains("l_IO_println(clean_box(0))"),
            "IO.println emitted source should pass the string payload instead of erased unit: {emitted_source}"
        );
        assert!(
            artifact.exists(),
            "IO.println run should leave a native executable artifact at {}",
            artifact.display()
        );

        let output = Command::new(&artifact)
            .output()
            .expect("linked IO.println artifact should execute for stdout check");
        assert!(
            output.status.success(),
            "linked IO.println artifact should exit successfully: {output:?}"
        );
        assert_eq!(
            String::from_utf8_lossy(&output.stdout),
            "hi\n",
            "linked IO.println artifact should print the literal payload"
        );
    }

    fn cc_available() -> bool {
        let cc = std::env::var("CLEAN_CC")
            .ok()
            .filter(|v| !v.trim().is_empty())
            .or_else(|| std::env::var("CC").ok().filter(|v| !v.trim().is_empty()))
            .unwrap_or_else(|| "cc".to_string());
        Command::new(cc)
            .arg("--version")
            .output()
            .map(|o| o.status.success())
            .unwrap_or(false)
    }

    /// Reuse-closes-the-gap proof: a single-module `Main` that computes (typeclass
    /// `+`) and renders via `toString` previously could fail at link under the
    /// Lake path's narrow trivial-IO prelude, while `clean run` on the same file
    /// succeeded. Now that `clean lake run` routes through the shared native-build
    /// engine (which carries the NAT/TYPECLASS/`toString` shim tables), it must
    /// build, link, and run, printing the computed value `2`. Gated on `cc`.
    #[test]
    fn lake_run_computes_and_prints_via_shared_native_build_engine() {
        if !cc_available() {
            eprintln!(
                "skipping lake_run_computes_and_prints_via_shared_native_build_engine: no cc"
            );
            return;
        }
        let dir = write_executable_project(
            "native_run_compute_io",
            "def main : IO Unit := IO.println (toString (1 + 1))\n",
        );

        lake_run(
            Some("native_run_compute_io".to_string()),
            &[],
            false,
            1,
            Some(dir.path().to_path_buf()),
        )
        .expect("compute+toString single-module main should link and run via the shared engine");

        let ws = Workspace::new(dir.path(), "native_run_compute_io");
        let artifact = native_executable_build_path(&ws, "native_run_compute_io");
        assert!(
            artifact.exists(),
            "lake run should write a native executable at {}",
            artifact.display()
        );

        // The persisted C source must carry the shared engine's compute shims —
        // proving the Lake path reused cmd_run's richer tables, not a name-only
        // shellout to external lean/lake.
        let source = dir
            .path()
            .join(".lake/build/native/c/native_run_compute_io.c");
        let emitted_source =
            std::fs::read_to_string(&source).expect("compute IO should emit C source");
        assert!(
            emitted_source.contains("clean_obj* l_toString"),
            "compute source should include the shared toString shim: {emitted_source}"
        );

        let output = Command::new(&artifact)
            .output()
            .expect("linked compute artifact should execute");
        assert!(
            output.status.success(),
            "linked compute artifact should exit 0: {output:?}"
        );
        assert_eq!(
            String::from_utf8_lossy(&output.stdout),
            "2\n",
            "lake run should compute 1 + 1 and print 2 via the shared engine"
        );
    }

    #[test]
    fn lake_run_println_preserves_escaped_string_payload() {
        let dir = write_executable_project(
            "native_run_escaped_io",
            "def main : IO Unit := IO.println \"hi\\nthere\"\n",
        );

        lake_run(
            Some("native_run_escaped_io".to_string()),
            &[],
            false,
            1,
            Some(dir.path().to_path_buf()),
        )
        .expect("IO.println native shim should preserve escaped string payload");

        let ws = Workspace::new(dir.path(), "native_run_escaped_io");
        let artifact = native_executable_build_path(&ws, "native_run_escaped_io");
        let source = dir
            .path()
            .join(".lake/build/native/c/native_run_escaped_io.c");
        let emitted_source =
            std::fs::read_to_string(&source).expect("escaped IO should emit C source");
        assert!(
            emitted_source.contains("clean_mk_string(\"hi\\nthere\")"),
            "escaped IO.println source should preserve the newline payload as a C escape: {emitted_source}"
        );
        assert!(
            !emitted_source.contains("l_IO_println(clean_box(0))"),
            "escaped IO.println source should not erase the payload: {emitted_source}"
        );

        let output = Command::new(&artifact)
            .output()
            .expect("linked escaped IO.println artifact should execute");
        assert!(
            output.status.success(),
            "linked escaped IO.println artifact should exit successfully: {output:?}"
        );
        assert_eq!(
            String::from_utf8_lossy(&output.stdout),
            "hi\nthere\n",
            "linked escaped IO.println artifact should print the decoded literal payload"
        );
    }

    #[test]
    fn lake_run_print_preserves_string_payload_without_newline() {
        let dir = write_executable_project(
            "native_run_print_io",
            "def main : IO Unit := IO.print \"hi\"\n",
        );

        lake_run(
            Some("native_run_print_io".to_string()),
            &[],
            false,
            1,
            Some(dir.path().to_path_buf()),
        )
        .expect("IO.print native shim should link and execute without Lean4");

        let ws = Workspace::new(dir.path(), "native_run_print_io");
        let artifact = native_executable_build_path(&ws, "native_run_print_io");
        let source = dir
            .path()
            .join(".lake/build/native/c/native_run_print_io.c");
        let emitted_source =
            std::fs::read_to_string(&source).expect("IO.print should emit C source");
        assert!(
            emitted_source.contains("clean_obj* l_IO_print"),
            "IO.print emitted source should include the shared native-build shim: {emitted_source}"
        );
        assert!(
            emitted_source.contains("clean_mk_string(\"hi\")"),
            "IO.print emitted source should allocate the literal payload: {emitted_source}"
        );
        assert!(
            emitted_source.contains("l_IO_print("),
            "IO.print emitted source should pass a payload object to the shim: {emitted_source}"
        );
        assert!(
            !emitted_source.contains("l_IO_print(clean_box(0))"),
            "IO.print emitted source should not erase the payload: {emitted_source}"
        );

        let output = Command::new(&artifact)
            .output()
            .expect("linked IO.print artifact should execute");
        assert!(
            output.status.success(),
            "linked IO.print artifact should exit successfully: {output:?}"
        );
        assert_eq!(
            String::from_utf8_lossy(&output.stdout),
            "hi",
            "linked IO.print artifact should print the literal payload without a newline"
        );
    }

    #[test]
    fn lake_run_eprintln_preserves_string_payload_on_stderr() {
        let dir = write_executable_project(
            "native_run_eprintln_io",
            "def main : IO Unit := IO.eprintln \"warn\"\n",
        );

        lake_run(
            Some("native_run_eprintln_io".to_string()),
            &[],
            false,
            1,
            Some(dir.path().to_path_buf()),
        )
        .expect("IO.eprintln native shim should link and execute without Lean4");

        let ws = Workspace::new(dir.path(), "native_run_eprintln_io");
        let artifact = native_executable_build_path(&ws, "native_run_eprintln_io");
        let source = dir
            .path()
            .join(".lake/build/native/c/native_run_eprintln_io.c");
        let emitted_source =
            std::fs::read_to_string(&source).expect("IO.eprintln should emit C source");
        assert!(
            emitted_source.contains("clean_obj* l_IO_eprintln"),
            "IO.eprintln emitted source should include the shared native-build stderr shim: {emitted_source}"
        );
        assert!(
            emitted_source.contains("clean_mk_string(\"warn\")"),
            "IO.eprintln emitted source should allocate the literal payload: {emitted_source}"
        );
        assert!(
            emitted_source.contains("l_IO_eprintln("),
            "IO.eprintln emitted source should pass a payload object to the shim: {emitted_source}"
        );
        assert!(
            !emitted_source.contains("l_IO_eprintln(clean_box(0))"),
            "IO.eprintln emitted source should not erase the payload: {emitted_source}"
        );

        let output = Command::new(&artifact)
            .output()
            .expect("linked IO.eprintln artifact should execute");
        assert!(
            output.status.success(),
            "linked IO.eprintln artifact should exit successfully: {output:?}"
        );
        assert_eq!(
            String::from_utf8_lossy(&output.stdout),
            "",
            "linked IO.eprintln artifact should not write the payload to stdout"
        );
        assert_eq!(
            String::from_utf8_lossy(&output.stderr),
            "warn\n",
            "linked IO.eprintln artifact should print the literal payload on stderr"
        );
    }

    #[test]
    fn lake_run_sequence_executes_bounded_native_bind_shim() {
        let dir = write_executable_project(
            "native_run_sequence_io",
            "def main : IO Unit := do\n  IO.print \"hi\"\n  IO.println \" there\"\n",
        );

        lake_run(
            Some("native_run_sequence_io".to_string()),
            &[],
            false,
            1,
            Some(dir.path().to_path_buf()),
        )
        .expect("sequenced IO should link and execute through the bounded native bind shim");

        let ws = Workspace::new(dir.path(), "native_run_sequence_io");
        let artifact = native_executable_build_path(&ws, "native_run_sequence_io");
        let source = dir
            .path()
            .join(".lake/build/native/c/native_run_sequence_io.c");
        let emitted_source =
            std::fs::read_to_string(&source).expect("sequenced IO C source should be emitted");
        assert!(
            emitted_source.contains("clean_alloc_closure"),
            "sequenced IO should lower the continuation lambda to a closure value: {emitted_source}"
        );
        assert!(
            emitted_source.contains("l_Bind_bind("),
            "sequenced IO should call the desugared bind symbol: {emitted_source}"
        );
        assert!(
            emitted_source.contains("clean_obj* l_Bind_bind"),
            "sequenced IO should include the shared native-build bind shim: {emitted_source}"
        );

        let output = Command::new(&artifact)
            .output()
            .expect("linked sequenced IO artifact should execute");
        assert!(
            output.status.success(),
            "linked sequenced IO artifact should exit successfully: {output:?}"
        );
        assert_eq!(
            String::from_utf8_lossy(&output.stdout),
            "hi there\n",
            "linked sequenced IO artifact should print both IO actions in order"
        );
    }

    #[test]
    fn lake_run_explicit_bind_executes_bounded_native_bind_shim() {
        let dir = write_executable_project(
            "native_run_explicit_bind_io",
            "def main : IO Unit := IO.bind (IO.print \"hi\") (fun _ => IO.println \" there\")\n",
        );

        lake_run(
            Some("native_run_explicit_bind_io".to_string()),
            &[],
            false,
            1,
            Some(dir.path().to_path_buf()),
        )
        .expect("explicit IO.bind should link and execute through the bounded native bind shim");

        let ws = Workspace::new(dir.path(), "native_run_explicit_bind_io");
        let artifact = native_executable_build_path(&ws, "native_run_explicit_bind_io");
        let source = dir
            .path()
            .join(".lake/build/native/c/native_run_explicit_bind_io.c");
        let emitted_source =
            std::fs::read_to_string(&source).expect("explicit IO.bind C source should be emitted");
        assert!(
            emitted_source.contains("clean_alloc_closure"),
            "explicit IO.bind should lower the continuation lambda to a closure value: {emitted_source}"
        );
        assert!(
            emitted_source.contains("l_IO_bind("),
            "explicit IO.bind source should call the IO.bind shim symbol: {emitted_source}"
        );
        assert!(
            emitted_source.contains("clean_obj* l_IO_bind"),
            "explicit IO.bind should include the shared native-build IO.bind shim: {emitted_source}"
        );

        let output = Command::new(&artifact)
            .output()
            .expect("linked explicit IO.bind artifact should execute");
        assert!(
            output.status.success(),
            "linked explicit IO.bind artifact should exit successfully: {output:?}"
        );
        assert_eq!(
            String::from_utf8_lossy(&output.stdout),
            "hi there\n",
            "linked explicit IO.bind artifact should print both IO actions in order"
        );
    }

    #[test]
    fn lake_runtime_lambda_argument_lowers_to_local_function_public_api() {
        use clean_compiler::{
            constant_to_decl,
            lcnf::{Arg, Code, DeclValue, LetValue},
        };
        use clean_kernel::{
            BinderInfo, ConstantInfo, ConstantKind, Environment, Expr, Name, Reducibility,
        };

        let env = Environment::default();
        let lambda_arg = Expr::lam(BinderInfo::Default, Expr::const_str("Nat"), Expr::bvar(0));
        let value = Expr::app(Expr::const_str("takesFn"), lambda_arg);
        let info = ConstantInfo {
            name: Name::from_string("lambdaArgSmoke"),
            level_params: Vec::new(),
            type_: Expr::const_str("Nat"),
            value: Some(value),
            is_reducible: true,
            reducibility: Reducibility::Reducible,
            kind: ConstantKind::Definition,
        };

        let decl = constant_to_decl(&env, &info)
            .expect("lambda argument should lower through the public compiler API")
            .expect("definition should produce an L5CNF declaration");
        let DeclValue::Code(code) = &decl.body else {
            panic!("expected code declaration");
        };

        let Code::Fun(lambda_fun, rest) = code.as_ref() else {
            panic!("lambda argument should be emitted as a local LCNF function: {code:?}");
        };
        assert_eq!(
            lambda_fun.params.len(),
            1,
            "lambda argument should preserve its runtime parameter"
        );

        let Code::Let(app_decl, _) = rest.as_ref() else {
            panic!("application using the lowered lambda should remain let-bound: {rest:?}");
        };
        let LetValue::Const { name, args, .. } = &app_decl.value else {
            panic!("expected takesFn application after local lambda: {app_decl:?}");
        };
        assert_eq!(name, &Name::from_string("takesFn"));
        assert_eq!(
            args.first(),
            Some(&Arg::FVar(lambda_fun.fvar_id)),
            "application should pass the local lambda function as a runtime argument"
        );
    }

    #[test]
    fn lake_test_fails_closed_at_native_runtime_boundary() {
        let dir = write_test_project("native_test_surface", "def smoke : Unit := ()\n");

        let err = lake_test(
            Some("native_test_surface".to_string()),
            false,
            1,
            Some(dir.path().to_path_buf()),
        )
        .expect_err("lake test should fail closed until native test execution exists");

        let msg = format!("{err:#}");
        assert!(
            msg.contains("clean lake test is fail-closed"),
            "diagnostic should name the lake test fail-closed boundary: {msg}"
        );
        assert!(
            msg.contains("main : IO Unit"),
            "diagnostic should name the bounded native test shape: {msg}"
        );
        assert!(
            msg.contains("non-main test target"),
            "diagnostic should classify this as the non-main test-root boundary: {msg}"
        );
        assert!(
            msg.contains("native Lake test discovery/assertion semantics"),
            "diagnostic should name the missing native test semantics: {msg}"
        );
        assert!(
            msg.contains("Refusing to delegate to external `lean --run`"),
            "diagnostic should explicitly reject Lean4 delegation: {msg}"
        );
        assert!(
            !dir.path()
                .join(".lake/build/native/c/native_test_surface.c")
                .exists(),
            "non-main lake test should fail closed before native C source emission"
        );
    }

    #[test]
    fn lake_test_rejects_non_main_io_test_decl_before_native_handoff() {
        let dir = write_test_project(
            "native_test_io_decl_surface",
            "def smoke : IO Unit := IO.println \"assertion-like test body\"\n",
        );

        let err = lake_test(
            Some("native_test_io_decl_surface".to_string()),
            false,
            1,
            Some(dir.path().to_path_buf()),
        )
        .expect_err("lake test should reject non-main IO test declarations before native handoff");

        let msg = format!("{err:#}");
        assert!(
            msg.contains("clean lake test is fail-closed"),
            "diagnostic should name the lake test fail-closed boundary: {msg}"
        );
        assert!(
            msg.contains("non-main test target"),
            "diagnostic should classify this as the non-main test-root boundary: {msg}"
        );
        assert!(
            msg.contains("main : IO Unit"),
            "diagnostic should state that only the bounded main entrypoint is supported: {msg}"
        );
        assert!(
            msg.contains("native Lake test discovery/assertion semantics"),
            "diagnostic should name the missing native assertion discovery semantics: {msg}"
        );
        assert!(
            msg.contains("Refusing to delegate to external `lean --run`"),
            "diagnostic should preserve the native replacement boundary: {msg}"
        );
        assert!(
            !dir.path()
                .join(".lake/build/native/c/native_test_io_decl_surface.c")
                .exists(),
            "non-main IO lake test should fail closed before native C source emission"
        );
        assert!(
            !dir.path()
                .join(".lake/build/bin/native_test_io_decl_surface")
                .exists(),
            "non-main IO lake test should fail closed before native artifact emission"
        );
    }

    #[test]
    fn lake_test_rejects_assertion_discovery_surface_before_native_handoff() {
        let dir = write_test_project(
            "native_test_assertion_surface",
            "example : True := trivial\n#eval IO.println \"assertion discovery\"\n",
        );

        let err = lake_test(
            Some("native_test_assertion_surface".to_string()),
            false,
            1,
            Some(dir.path().to_path_buf()),
        )
        .expect_err("lake test should reject assertion discovery surfaces before native handoff");

        let msg = format!("{err:#}");
        assert!(
            msg.contains("clean lake test is fail-closed"),
            "diagnostic should name the lake test fail-closed boundary: {msg}"
        );
        assert!(
            msg.contains("assertion/discovery-style declarations"),
            "diagnostic should classify assertion discovery syntax explicitly: {msg}"
        );
        assert!(
            msg.contains("native Lake test discovery/assertion semantics"),
            "diagnostic should name the missing native assertion discovery semantics: {msg}"
        );
        assert!(
            msg.contains("main : IO Unit"),
            "diagnostic should state that only the bounded main entrypoint is supported: {msg}"
        );
        assert!(
            msg.contains("Refusing to delegate to external `lean --run`"),
            "diagnostic should preserve the native replacement boundary: {msg}"
        );
        assert!(
            !dir.path()
                .join(".lake/build/native/c/native_test_assertion_surface.c")
                .exists(),
            "assertion discovery lake test should fail closed before native C source emission"
        );
        assert!(
            !dir.path()
                .join(".lake/build/bin/native_test_assertion_surface")
                .exists(),
            "assertion discovery lake test should fail closed before native artifact emission"
        );
    }

    #[test]
    fn lake_test_executes_bounded_native_main_smoke() {
        let dir = write_test_project(
            "native_test_main_surface",
            "def main : IO Unit := IO.println \"test ok\"\n",
        );

        lake_test(
            Some("native_test_main_surface".to_string()),
            false,
            1,
            Some(dir.path().to_path_buf()),
        )
        .expect("lake test should execute a bounded native main smoke without Lean4");

        let ws = Workspace::new(dir.path(), "native_test_surface");
        let artifact = native_executable_build_path(&ws, "native_test_main_surface");
        let source = dir
            .path()
            .join(".lake/build/native/c/native_test_main_surface.c");
        let emitted_source =
            std::fs::read_to_string(&source).expect("native lake test should emit C source");
        assert!(
            emitted_source.contains("clean_obj* l_IO_println"),
            "native lake test should include the bounded IO.println shim: {emitted_source}"
        );
        assert!(
            emitted_source.contains("clean_mk_string(\"test ok\")"),
            "native lake test should preserve the test stdout payload: {emitted_source}"
        );

        let output = Command::new(&artifact)
            .output()
            .expect("linked native lake test artifact should execute");
        assert!(
            output.status.success(),
            "linked native lake test artifact should exit successfully: {output:?}"
        );
        assert_eq!(
            String::from_utf8_lossy(&output.stdout),
            "test ok\n",
            "linked native lake test artifact should print the test payload"
        );
    }

    #[test]
    fn lake_test_sequence_executes_bounded_native_bind_shim() {
        let dir = write_test_project(
            "native_test_sequence_io",
            "def main : IO Unit := do\n  IO.print \"hi\"\n  IO.println \" there\"\n",
        );

        lake_test(
            Some("native_test_sequence_io".to_string()),
            false,
            1,
            Some(dir.path().to_path_buf()),
        )
        .expect(
            "sequenced lake test IO should link and execute through the bounded native bind shim",
        );

        let ws = Workspace::new(dir.path(), "native_test_surface");
        let artifact = native_executable_build_path(&ws, "native_test_sequence_io");
        let source = dir
            .path()
            .join(".lake/build/native/c/native_test_sequence_io.c");
        let emitted_source = std::fs::read_to_string(&source)
            .expect("sequenced lake test C source should be emitted");

        assert!(
            emitted_source.contains("clean_alloc_closure"),
            "sequenced lake test IO should lower the continuation lambda to a closure value: {emitted_source}"
        );
        assert!(
            emitted_source.contains("l_Bind_bind("),
            "sequenced lake test IO should call the desugared bind symbol: {emitted_source}"
        );
        assert!(
            emitted_source.contains("clean_obj* l_Bind_bind"),
            "sequenced lake test IO should include the shared native-build bind shim: {emitted_source}"
        );

        let output = Command::new(&artifact)
            .output()
            .expect("linked sequenced lake test artifact should execute");
        assert!(
            output.status.success(),
            "linked sequenced lake test artifact should exit successfully: {output:?}"
        );
        assert_eq!(
            String::from_utf8_lossy(&output.stdout),
            "hi there\n",
            "linked sequenced lake test artifact should print both IO actions in order"
        );
    }

    #[test]
    fn lake_test_rejects_lean_authored_exit_before_native_handoff() {
        let dir = write_test_project(
            "native_test_exit_surface",
            "def main : IO Unit := IO.Process.exit 7\n",
        );

        let err = lake_test(
            Some("native_test_exit_surface".to_string()),
            false,
            1,
            Some(dir.path().to_path_buf()),
        )
        .expect_err("lake test should reject Lean-authored process exit before native handoff");

        let msg = format!("{err:#}");
        assert!(
            msg.contains("clean lake test is fail-closed"),
            "diagnostic should name the lake test fail-closed boundary: {msg}"
        );
        assert!(
            msg.contains("Lean-authored exit/exception propagation"),
            "diagnostic should name the unsupported runtime semantic: {msg}"
        );
        assert!(
            msg.contains("IO.Process.exit"),
            "diagnostic should name the unsupported source form: {msg}"
        );
        assert!(
            msg.contains("main : IO Unit"),
            "diagnostic should preserve that the root has the bounded main shape: {msg}"
        );
        assert!(
            msg.contains("Refusing to delegate to external `lean --run`"),
            "diagnostic should preserve the native replacement boundary: {msg}"
        );
        assert!(
            !dir.path()
                .join(".lake/build/native/c/native_test_exit_surface.c")
                .exists(),
            "Lean-authored exit lake test should fail closed before native C source emission"
        );
        assert!(
            !dir.path()
                .join(".lake/build/bin/native_test_exit_surface")
                .exists(),
            "Lean-authored exit lake test should fail closed before native artifact emission"
        );
    }

    #[test]
    fn lake_test_rejects_lean_authored_assertion_before_native_handoff() {
        let dir = write_test_project(
            "native_test_assert_failure_surface",
            "def main : IO Unit := assert! false\n",
        );

        let err = lake_test(
            Some("native_test_assert_failure_surface".to_string()),
            false,
            1,
            Some(dir.path().to_path_buf()),
        )
        .expect_err(
            "lake test should reject Lean-authored assertion failure before native handoff",
        );

        let msg = format!("{err:#}");
        assert!(
            msg.contains("clean lake test is fail-closed"),
            "diagnostic should name the lake test fail-closed boundary: {msg}"
        );
        assert!(
            msg.contains("Lean-authored failure/exception propagation"),
            "diagnostic should name the unsupported runtime semantic: {msg}"
        );
        assert!(
            msg.contains("assert!"),
            "diagnostic should name the unsupported assertion source form: {msg}"
        );
        assert!(
            msg.contains("main : IO Unit"),
            "diagnostic should preserve that the root has the bounded main shape: {msg}"
        );
        assert!(
            msg.contains("Refusing to delegate to external `lean --run`"),
            "diagnostic should preserve the native replacement boundary: {msg}"
        );
        assert!(
            !dir.path()
                .join(".lake/build/native/c/native_test_assert_failure_surface.c")
                .exists(),
            "Lean-authored assertion lake test should fail closed before native C source emission"
        );
        assert!(
            !dir.path()
                .join(".lake/build/bin/native_test_assert_failure_surface")
                .exists(),
            "Lean-authored assertion lake test should fail closed before native artifact emission"
        );
    }

    #[test]
    fn lake_test_rejects_stderr_runtime_before_native_handoff() {
        let dir = write_test_project(
            "native_test_stderr_surface",
            "def main : IO Unit := IO.eprintln \"stderr unsupported\"\n",
        );

        let err = lake_test(
            Some("native_test_stderr_surface".to_string()),
            false,
            1,
            Some(dir.path().to_path_buf()),
        )
        .expect_err("lake test should reject stderr emission before native handoff");

        let msg = format!("{err:#}");
        assert!(
            msg.contains("clean lake test is fail-closed"),
            "diagnostic should name the lake test fail-closed boundary: {msg}"
        );
        assert!(
            msg.contains("Lean-authored stderr emission"),
            "diagnostic should name the unsupported stderr runtime boundary: {msg}"
        );
        assert!(
            msg.contains("IO.eprintln"),
            "diagnostic should name the unsupported stderr source form: {msg}"
        );
        assert!(
            msg.contains("Refusing to delegate to external `lean --run`"),
            "diagnostic should preserve the native replacement boundary: {msg}"
        );
        assert!(
            !dir.path()
                .join(".lake/build/native/c/native_test_stderr_surface.c")
                .exists(),
            "stderr lake test should fail closed before native C source emission"
        );
        assert!(
            !dir.path()
                .join(".lake/build/bin/native_test_stderr_surface")
                .exists(),
            "stderr lake test should fail closed before native artifact emission"
        );
    }

    #[test]
    fn lake_test_rejects_stdin_runtime_before_native_handoff() {
        let dir = write_test_project(
            "native_test_stdin_surface",
            "def main : IO Unit := do\n  let line <- IO.getLine\n  IO.println line\n",
        );

        let err = lake_test(
            Some("native_test_stdin_surface".to_string()),
            false,
            1,
            Some(dir.path().to_path_buf()),
        )
        .expect_err("lake test should reject stdin reads before native handoff");

        let msg = format!("{err:#}");
        assert!(
            msg.contains("clean lake test is fail-closed"),
            "diagnostic should name the lake test fail-closed boundary: {msg}"
        );
        assert!(
            msg.contains("Lean-authored stdin reads"),
            "diagnostic should name the unsupported stdin runtime boundary: {msg}"
        );
        assert!(
            msg.contains("IO.getLine"),
            "diagnostic should name the unsupported stdin source form: {msg}"
        );
        assert!(
            msg.contains("Refusing to delegate to external `lean --run`"),
            "diagnostic should preserve the native replacement boundary: {msg}"
        );
        assert!(
            !dir.path()
                .join(".lake/build/native/c/native_test_stdin_surface.c")
                .exists(),
            "stdin lake test should fail closed before native C source emission"
        );
        assert!(
            !dir.path()
                .join(".lake/build/bin/native_test_stdin_surface")
                .exists(),
            "stdin lake test should fail closed before native artifact emission"
        );
    }

    #[test]
    fn lake_test_rejects_env_runtime_before_native_handoff() {
        let dir = write_test_project(
            "native_test_env_surface",
            "def main : IO Unit := do\n  let home <- IO.getEnv \"HOME\"\n  IO.println home\n",
        );

        let err = lake_test(
            Some("native_test_env_surface".to_string()),
            false,
            1,
            Some(dir.path().to_path_buf()),
        )
        .expect_err("lake test should reject environment reads before native handoff");

        let msg = format!("{err:#}");
        assert!(
            msg.contains("clean lake test is fail-closed"),
            "diagnostic should name the lake test fail-closed boundary: {msg}"
        );
        assert!(
            msg.contains("Lean-authored environment reads"),
            "diagnostic should name the unsupported environment runtime boundary: {msg}"
        );
        assert!(
            msg.contains("IO.getEnv"),
            "diagnostic should name the unsupported environment source form: {msg}"
        );
        assert!(
            msg.contains("Refusing to delegate to external `lean --run`"),
            "diagnostic should preserve the native replacement boundary: {msg}"
        );
        assert!(
            !dir.path()
                .join(".lake/build/native/c/native_test_env_surface.c")
                .exists(),
            "environment lake test should fail closed before native C source emission"
        );
        assert!(
            !dir.path()
                .join(".lake/build/bin/native_test_env_surface")
                .exists(),
            "environment lake test should fail closed before native artifact emission"
        );
    }

    #[test]
    fn lake_test_rejects_file_runtime_before_native_handoff() {
        let dir = write_test_project(
            "native_test_file_surface",
            "def main : IO Unit := do\n  let contents <- IO.FS.readFile \"input.txt\"\n  IO.println contents\n",
        );

        let err = lake_test(
            Some("native_test_file_surface".to_string()),
            false,
            1,
            Some(dir.path().to_path_buf()),
        )
        .expect_err("lake test should reject file IO before native handoff");

        let msg = format!("{err:#}");
        assert!(
            msg.contains("clean lake test is fail-closed"),
            "diagnostic should name the lake test fail-closed boundary: {msg}"
        );
        assert!(
            msg.contains("Lean-authored file IO"),
            "diagnostic should name the unsupported file runtime boundary: {msg}"
        );
        assert!(
            msg.contains("IO.FS"),
            "diagnostic should name the unsupported file IO namespace: {msg}"
        );
        assert!(
            msg.contains("Refusing to delegate to external `lean --run`"),
            "diagnostic should preserve the native replacement boundary: {msg}"
        );
        assert!(
            !dir.path()
                .join(".lake/build/native/c/native_test_file_surface.c")
                .exists(),
            "file IO lake test should fail closed before native C source emission"
        );
        assert!(
            !dir.path()
                .join(".lake/build/bin/native_test_file_surface")
                .exists(),
            "file IO lake test should fail closed before native artifact emission"
        );
    }

    #[test]
    fn lake_test_rejects_process_runtime_before_native_handoff() {
        let dir = write_test_project(
            "native_test_process_surface",
            "def main : IO Unit := do\n  let output <- IO.Process.output {cmd := \"echo\", args := #[\"hi\"]}\n  IO.println output.stdout\n",
        );

        let err = lake_test(
            Some("native_test_process_surface".to_string()),
            false,
            1,
            Some(dir.path().to_path_buf()),
        )
        .expect_err("lake test should reject process spawning before native handoff");

        let msg = format!("{err:#}");
        assert!(
            msg.contains("clean lake test is fail-closed"),
            "diagnostic should name the lake test fail-closed boundary: {msg}"
        );
        assert!(
            msg.contains("Lean-authored process spawning"),
            "diagnostic should name the unsupported process runtime boundary: {msg}"
        );
        assert!(
            msg.contains("IO.Process"),
            "diagnostic should name the unsupported process namespace: {msg}"
        );
        assert!(
            msg.contains("Refusing to delegate to external `lean --run`"),
            "diagnostic should preserve the native replacement boundary: {msg}"
        );
        assert!(
            !dir.path()
                .join(".lake/build/native/c/native_test_process_surface.c")
                .exists(),
            "process lake test should fail closed before native C source emission"
        );
        assert!(
            !dir.path()
                .join(".lake/build/bin/native_test_process_surface")
                .exists(),
            "process lake test should fail closed before native artifact emission"
        );
    }

    #[test]
    fn lake_test_rejects_args_runtime_before_native_handoff() {
        let dir = write_test_project(
            "native_test_args_surface",
            "def main : IO Unit := do\n  let args <- IO.getArgs\n  IO.println (toString args.size)\n",
        );

        let err = lake_test(
            Some("native_test_args_surface".to_string()),
            false,
            1,
            Some(dir.path().to_path_buf()),
        )
        .expect_err("lake test should reject command-line argument reads before native handoff");

        let msg = format!("{err:#}");
        assert!(
            msg.contains("clean lake test is fail-closed"),
            "diagnostic should name the lake test fail-closed boundary: {msg}"
        );
        assert!(
            msg.contains("Lean-authored command-line argument reads"),
            "diagnostic should name the unsupported argv runtime boundary: {msg}"
        );
        assert!(
            msg.contains("IO.getArgs"),
            "diagnostic should name the unsupported argument source form: {msg}"
        );
        assert!(
            msg.contains("Refusing to delegate to external `lean --run`"),
            "diagnostic should preserve the native replacement boundary: {msg}"
        );
        assert!(
            !dir.path()
                .join(".lake/build/native/c/native_test_args_surface.c")
                .exists(),
            "argument lake test should fail closed before native C source emission"
        );
        assert!(
            !dir.path()
                .join(".lake/build/bin/native_test_args_surface")
                .exists(),
            "argument lake test should fail closed before native artifact emission"
        );
    }

    #[test]
    fn lake_test_rejects_time_runtime_before_native_handoff() {
        let dir = write_test_project(
            "native_test_time_surface",
            "def main : IO Unit := do\n  IO.sleep 1\n  IO.println \"awake\"\n",
        );

        let err = lake_test(
            Some("native_test_time_surface".to_string()),
            false,
            1,
            Some(dir.path().to_path_buf()),
        )
        .expect_err("lake test should reject sleep/time runtime before native handoff");

        let msg = format!("{err:#}");
        assert!(
            msg.contains("clean lake test is fail-closed"),
            "diagnostic should name the lake test fail-closed boundary: {msg}"
        );
        assert!(
            msg.contains("Lean-authored sleep/time runtime"),
            "diagnostic should name the unsupported sleep/time runtime boundary: {msg}"
        );
        assert!(
            msg.contains("IO.sleep"),
            "diagnostic should name the unsupported sleep source form: {msg}"
        );
        assert!(
            msg.contains("Refusing to delegate to external `lean --run`"),
            "diagnostic should preserve the native replacement boundary: {msg}"
        );
        assert!(
            !dir.path()
                .join(".lake/build/native/c/native_test_time_surface.c")
                .exists(),
            "sleep/time lake test should fail closed before native C source emission"
        );
        assert!(
            !dir.path()
                .join(".lake/build/bin/native_test_time_surface")
                .exists(),
            "sleep/time lake test should fail closed before native artifact emission"
        );
    }

    #[test]
    fn lake_test_rejects_task_runtime_before_native_handoff() {
        let dir = write_test_project(
            "native_test_task_surface",
            "def main : IO Unit := do\n  let task <- IO.asTask (IO.println \"background\")\n  IO.println \"scheduled\"\n",
        );

        let err = lake_test(
            Some("native_test_task_surface".to_string()),
            false,
            1,
            Some(dir.path().to_path_buf()),
        )
        .expect_err("lake test should reject task runtime before native handoff");

        let msg = format!("{err:#}");
        assert!(
            msg.contains("clean lake test is fail-closed"),
            "diagnostic should name the lake test fail-closed boundary: {msg}"
        );
        assert!(
            msg.contains("Lean-authored task/thread runtime"),
            "diagnostic should name the unsupported task/thread runtime boundary: {msg}"
        );
        assert!(
            msg.contains("IO.asTask"),
            "diagnostic should name the unsupported task source form: {msg}"
        );
        assert!(
            msg.contains("Refusing to delegate to external `lean --run`"),
            "diagnostic should preserve the native replacement boundary: {msg}"
        );
        assert!(
            !dir.path()
                .join(".lake/build/native/c/native_test_task_surface.c")
                .exists(),
            "task lake test should fail closed before native C source emission"
        );
        assert!(
            !dir.path()
                .join(".lake/build/bin/native_test_task_surface")
                .exists(),
            "task lake test should fail closed before native artifact emission"
        );
    }

    #[test]
    fn lake_test_rejects_exception_handling_before_native_handoff() {
        let dir = write_test_project(
            "native_test_catch_surface",
            "def main : IO Unit := do\n  try\n    IO.println \"body\"\n  catch e =>\n    IO.println \"caught\"\n",
        );

        let err = lake_test(
            Some("native_test_catch_surface".to_string()),
            false,
            1,
            Some(dir.path().to_path_buf()),
        )
        .expect_err("lake test should reject exception handling before native handoff");

        let msg = format!("{err:#}");
        assert!(
            msg.contains("clean lake test is fail-closed"),
            "diagnostic should name the lake test fail-closed boundary: {msg}"
        );
        assert!(
            msg.contains("Lean-authored exception handling"),
            "diagnostic should name the unsupported exception handling boundary: {msg}"
        );
        assert!(
            msg.contains("try/catch"),
            "diagnostic should name the unsupported exception handling source form: {msg}"
        );
        assert!(
            msg.contains("Refusing to delegate to external `lean --run`"),
            "diagnostic should preserve the native replacement boundary: {msg}"
        );
        assert!(
            !dir.path()
                .join(".lake/build/native/c/native_test_catch_surface.c")
                .exists(),
            "exception handling lake test should fail closed before native C source emission"
        );
        assert!(
            !dir.path()
                .join(".lake/build/bin/native_test_catch_surface")
                .exists(),
            "exception handling lake test should fail closed before native artifact emission"
        );
    }

    #[test]
    fn lake_test_rejects_ref_runtime_before_native_handoff() {
        let dir = write_test_project(
            "native_test_ref_surface",
            "def main : IO Unit := do\n  let ref <- IO.mkRef 0\n  let value <- ref.get\n  IO.println (toString value)\n",
        );

        let err = lake_test(
            Some("native_test_ref_surface".to_string()),
            false,
            1,
            Some(dir.path().to_path_buf()),
        )
        .expect_err("lake test should reject IO.Ref runtime before native handoff");

        let msg = format!("{err:#}");
        assert!(
            msg.contains("clean lake test is fail-closed"),
            "diagnostic should name the lake test fail-closed boundary: {msg}"
        );
        assert!(
            msg.contains("Lean-authored mutable reference runtime"),
            "diagnostic should name the unsupported mutable reference boundary: {msg}"
        );
        assert!(
            msg.contains("IO.mkRef"),
            "diagnostic should name the unsupported reference source form: {msg}"
        );
        assert!(
            msg.contains("Refusing to delegate to external `lean --run`"),
            "diagnostic should preserve the native replacement boundary: {msg}"
        );
        assert!(
            !dir.path()
                .join(".lake/build/native/c/native_test_ref_surface.c")
                .exists(),
            "IO.Ref lake test should fail closed before native C source emission"
        );
        assert!(
            !dir.path()
                .join(".lake/build/bin/native_test_ref_surface")
                .exists(),
            "IO.Ref lake test should fail closed before native artifact emission"
        );
    }

    #[test]
    fn lake_test_rejects_current_dir_runtime_before_native_handoff() {
        let dir = write_test_project(
            "native_test_current_dir_surface",
            "def main : IO Unit := do\n  let cwd <- IO.currentDir\n  IO.println cwd.toString\n",
        );

        let err = lake_test(
            Some("native_test_current_dir_surface".to_string()),
            false,
            1,
            Some(dir.path().to_path_buf()),
        )
        .expect_err("lake test should reject current-directory runtime before native handoff");

        let msg = format!("{err:#}");
        assert!(
            msg.contains("clean lake test is fail-closed"),
            "diagnostic should name the lake test fail-closed boundary: {msg}"
        );
        assert!(
            msg.contains("Lean-authored current-directory runtime"),
            "diagnostic should name the unsupported current-directory boundary: {msg}"
        );
        assert!(
            msg.contains("IO.currentDir"),
            "diagnostic should name the unsupported current-directory source form: {msg}"
        );
        assert!(
            msg.contains("Refusing to delegate to external `lean --run`"),
            "diagnostic should preserve the native replacement boundary: {msg}"
        );
        assert!(
            !dir.path()
                .join(".lake/build/native/c/native_test_current_dir_surface.c")
                .exists(),
            "current-directory lake test should fail closed before native C source emission"
        );
        assert!(
            !dir.path()
                .join(".lake/build/bin/native_test_current_dir_surface")
                .exists(),
            "current-directory lake test should fail closed before native artifact emission"
        );
    }

    #[test]
    fn lake_test_rejects_handle_runtime_before_native_handoff() {
        let dir = write_test_project(
            "native_test_handle_surface",
            "def main : IO Unit := do\n  let stdout <- IO.getStdout\n  stdout.putStrLn \"handle unsupported\"\n",
        );

        let err = lake_test(
            Some("native_test_handle_surface".to_string()),
            false,
            1,
            Some(dir.path().to_path_buf()),
        )
        .expect_err("lake test should reject standard stream handles before native handoff");

        let msg = format!("{err:#}");
        assert!(
            msg.contains("clean lake test is fail-closed"),
            "diagnostic should name the lake test fail-closed boundary: {msg}"
        );
        assert!(
            msg.contains("Lean-authored standard stream handles"),
            "diagnostic should name the unsupported stream handle boundary: {msg}"
        );
        assert!(
            msg.contains("IO.getStdout"),
            "diagnostic should name the unsupported handle source form: {msg}"
        );
        assert!(
            msg.contains("Refusing to delegate to external `lean --run`"),
            "diagnostic should preserve the native replacement boundary: {msg}"
        );
        assert!(
            !dir.path()
                .join(".lake/build/native/c/native_test_handle_surface.c")
                .exists(),
            "standard stream handle lake test should fail closed before native C source emission"
        );
        assert!(
            !dir.path()
                .join(".lake/build/bin/native_test_handle_surface")
                .exists(),
            "standard stream handle lake test should fail closed before native artifact emission"
        );
    }

    #[test]
    fn lake_test_rejects_parameterized_main_before_native_handoff() {
        let dir = write_test_project(
            "native_test_parameterized_main",
            "def main (args : List String) : IO Unit := IO.println \"args unsupported\"\n",
        );

        let err = lake_test(
            Some("native_test_parameterized_main".to_string()),
            false,
            1,
            Some(dir.path().to_path_buf()),
        )
        .expect_err("lake test should reject parameterized main before native handoff");

        let msg = format!("{err:#}");
        assert!(
            msg.contains("clean lake test is fail-closed"),
            "diagnostic should name the lake test fail-closed boundary: {msg}"
        );
        assert!(
            msg.contains("parameterized `main` signatures"),
            "diagnostic should name the unsupported main signature shape: {msg}"
        );
        assert!(
            msg.contains("main : IO Unit"),
            "diagnostic should state the currently supported bounded test entrypoint: {msg}"
        );
        assert!(
            msg.contains("Refusing to delegate to external `lean --run`"),
            "diagnostic should preserve the native replacement boundary: {msg}"
        );
        assert!(
            !dir.path()
                .join(".lake/build/native/c/native_test_parameterized_main.c")
                .exists(),
            "parameterized main lake test should fail closed before native C source emission"
        );
        assert!(
            !dir.path()
                .join(".lake/build/bin/native_test_parameterized_main")
                .exists(),
            "parameterized main lake test should fail closed before native artifact emission"
        );
    }

    #[test]
    fn lake_test_rejects_non_unit_main_before_native_handoff() {
        let dir = write_test_project("native_test_non_unit_main", "def main : Nat := 0\n");

        let err = lake_test(
            Some("native_test_non_unit_main".to_string()),
            false,
            1,
            Some(dir.path().to_path_buf()),
        )
        .expect_err("lake test should reject non-IO-Unit main before native handoff");

        let msg = format!("{err:#}");
        assert!(
            msg.contains("clean lake test is fail-closed"),
            "diagnostic should name the lake test fail-closed boundary: {msg}"
        );
        assert!(
            msg.contains("unsupported `main` signature"),
            "diagnostic should name the unsupported main signature shape: {msg}"
        );
        assert!(
            msg.contains("main : IO Unit"),
            "diagnostic should state the currently supported bounded test entrypoint: {msg}"
        );
        assert!(
            msg.contains("Refusing to delegate to external `lean --run`"),
            "diagnostic should preserve the native replacement boundary: {msg}"
        );
        assert!(
            !dir.path()
                .join(".lake/build/native/c/native_test_non_unit_main.c")
                .exists(),
            "non-Unit main lake test should fail closed before native C source emission"
        );
        assert!(
            !dir.path()
                .join(".lake/build/bin/native_test_non_unit_main")
                .exists(),
            "non-Unit main lake test should fail closed before native artifact emission"
        );
    }

    #[test]
    fn lake_test_executes_all_bounded_native_main_targets() {
        let dir = write_multi_test_project();

        lake_test(None, false, 1, Some(dir.path().to_path_buf()))
            .expect("lake test should execute all bounded native main targets without Lean4");

        let ws = Workspace::new(dir.path(), "native_test_surface");
        for (target, expected) in [
            ("native_test_first", "first ok\n"),
            ("native_test_second", "second ok\n"),
        ] {
            let artifact = native_executable_build_path(&ws, target);
            assert!(
                artifact.exists(),
                "lake test should produce native artifact for {target} at {}",
                artifact.display()
            );

            let output = Command::new(&artifact)
                .output()
                .expect("linked native lake test artifact should execute");
            assert!(
                output.status.success(),
                "linked native lake test artifact {target} should exit successfully: {output:?}"
            );
            assert_eq!(
                String::from_utf8_lossy(&output.stdout),
                expected,
                "linked native lake test artifact {target} should print its payload"
            );
        }
    }

    #[test]
    fn lake_test_executes_only_selected_bounded_native_main_target() {
        let dir = write_multi_test_project();

        lake_test(
            Some("native_test_first".to_string()),
            false,
            1,
            Some(dir.path().to_path_buf()),
        )
        .expect("lake test should execute the selected bounded native main target without Lean4");

        let ws = Workspace::new(dir.path(), "native_test_surface");
        let selected_artifact = native_executable_build_path(&ws, "native_test_first");
        assert!(
            selected_artifact.exists(),
            "lake test should produce native artifact for the selected target at {}",
            selected_artifact.display()
        );

        let output = Command::new(&selected_artifact)
            .output()
            .expect("selected linked native lake test artifact should execute");
        assert!(
            output.status.success(),
            "selected linked native lake test artifact should exit successfully: {output:?}"
        );
        assert_eq!(
            String::from_utf8_lossy(&output.stdout),
            "first ok\n",
            "selected linked native lake test artifact should print only its payload"
        );

        let unselected_artifact = native_executable_build_path(&ws, "native_test_second");
        assert!(
            !unselected_artifact.exists(),
            "lake test should not produce native artifact for unselected target at {}",
            unselected_artifact.display()
        );
        assert!(
            !dir.path()
                .join(".lake/build/native/c/native_test_second.c")
                .exists(),
            "lake test should not emit native C source for the unselected test target"
        );
    }

    #[test]
    fn lake_test_reports_selected_native_main_failure() {
        let dir = write_test_project(
            "native_test_failure_surface",
            "def main : IO Unit := IO.println \"should not run\"\n",
        );
        let ws = Workspace::new(dir.path(), "native_test_surface");
        let artifact = native_executable_build_path(&ws, "native_test_failure_surface");
        std::fs::create_dir_all(artifact.parent().expect("artifact parent"))
            .expect("create build bin");
        std::fs::write(&artifact, "#!/bin/sh\necho selected failure >&2\nexit 7\n")
            .expect("write failing native artifact");
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let mut perms = std::fs::metadata(&artifact)
                .expect("failing native artifact metadata")
                .permissions();
            perms.set_mode(0o755);
            std::fs::set_permissions(&artifact, perms).expect("chmod failing native artifact");
        }
        // Stage a matching freshness sidecar so the freshness gate (#42) reuses
        // the hand-written failing artifact verbatim instead of rebuilding it.
        super::super::build::write_fresh_source_closure_sidecar_for_test(
            &ws,
            "native_test_failure_surface",
            "Main",
        );

        let err = lake_test(
            Some("native_test_failure_surface".to_string()),
            false,
            1,
            Some(dir.path().to_path_buf()),
        )
        .expect_err("lake test should report the selected native artifact failure");

        let msg = format!("{err:#}");
        assert!(
            msg.contains("1 test(s) failed"),
            "diagnostic should summarize failed native tests: {msg}"
        );
        assert!(
            msg.contains("native_test_failure_surface"),
            "diagnostic should name the failed Lake test target: {msg}"
        );
        assert!(
            msg.contains("Executable exited with status"),
            "diagnostic should preserve the native process status: {msg}"
        );
    }

    #[test]
    fn lake_test_pattern_filter_executes_matching_bounded_native_main_target() {
        let dir = write_multi_test_project();

        lake_test(
            Some("first".to_string()),
            false,
            1,
            Some(dir.path().to_path_buf()),
        )
        .expect("lake test should execute the matching substring-filtered native target");

        let ws = Workspace::new(dir.path(), "native_test_surface");
        let selected_artifact = native_executable_build_path(&ws, "native_test_first");
        assert!(
            selected_artifact.exists(),
            "substring-filtered lake test should produce native artifact for the matching target"
        );

        let output = Command::new(&selected_artifact)
            .output()
            .expect("substring-filtered native lake test artifact should execute");
        assert!(
            output.status.success(),
            "substring-filtered native lake test artifact should exit successfully: {output:?}"
        );
        assert_eq!(
            String::from_utf8_lossy(&output.stdout),
            "first ok\n",
            "substring-filtered native lake test artifact should print the selected payload"
        );

        let unselected_artifact = native_executable_build_path(&ws, "native_test_second");
        assert!(
            !unselected_artifact.exists(),
            "substring-filtered lake test should not produce native artifact for unselected target"
        );
        assert!(
            !dir.path()
                .join(".lake/build/native/c/native_test_second.c")
                .exists(),
            "substring-filtered lake test should not emit native C source for the unselected target"
        );
    }

    // ----------------------------------------------------------------------
    // Native binary freshness (#42): editing a source in the import closure
    // must invalidate the reused binary; an unchanged closure must reuse it.
    // ----------------------------------------------------------------------

    /// Write an executable project where `Main` imports a sibling `Lib` and
    /// prints `toString Lib.val`. Returns the tempdir; `Lib.lean` holds the
    /// editable value.
    fn write_two_module_value_project(package_name: &str, val: u64) -> tempfile::TempDir {
        let dir = tempfile::tempdir().expect("tempdir");
        std::fs::write(
            dir.path().join("lakefile.lean"),
            format!(
                r#"import Lake
open Lake DSL

package {package_name} where
  version := "0.1.0"

@[default_target]
lean_exe {package_name} where
  root := `Main
"#
            ),
        )
        .expect("write lakefile");
        std::fs::write(
            dir.path().join("Lib.lean"),
            format!("def val : Nat := {val}\n"),
        )
        .expect("write Lib.lean");
        std::fs::write(
            dir.path().join("Main.lean"),
            "import Lib\ndef main : IO Unit := IO.println (toString val)\n",
        )
        .expect("write Main.lean");
        dir
    }

    fn run_and_capture_stdout(dir: &Path, target: &str) -> String {
        lake_run(
            Some(target.to_string()),
            &[],
            false,
            1,
            Some(dir.to_path_buf()),
        )
        .expect("lake run should link and execute");
        let ws = Workspace::new(dir, target);
        let artifact = native_executable_build_path(&ws, target);
        let output = Command::new(&artifact)
            .output()
            .expect("linked artifact should execute for stdout capture");
        String::from_utf8_lossy(&output.stdout).into_owned()
    }

    /// Reproduction of #42: after editing the imported `Lib.lean` value, a second
    /// `clean lake run` must rebuild and print the NEW value (not the stale one),
    /// and a further edit must propagate again.
    #[test]
    fn lake_run_rebuilds_when_imported_module_value_changes() {
        if !cc_available() {
            eprintln!("skipping lake_run_rebuilds_when_imported_module_value_changes: no cc");
            return;
        }
        let dir = write_two_module_value_project("freshness_lib_edit", 10);

        assert_eq!(
            run_and_capture_stdout(dir.path(), "freshness_lib_edit"),
            "10\n",
            "first run should print the initial imported value"
        );

        // Edit the IMPORTED module (not the root) 10 -> 20.
        std::fs::write(dir.path().join("Lib.lean"), "def val : Nat := 20\n")
            .expect("rewrite Lib.lean to 20");
        assert_eq!(
            run_and_capture_stdout(dir.path(), "freshness_lib_edit"),
            "20\n",
            "editing the imported Lib.lean must invalidate the stale binary and print 20"
        );

        // Edit again 20 -> 30 to prove repeated propagation.
        std::fs::write(dir.path().join("Lib.lean"), "def val : Nat := 30\n")
            .expect("rewrite Lib.lean to 30");
        assert_eq!(
            run_and_capture_stdout(dir.path(), "freshness_lib_edit"),
            "30\n",
            "a second edit to the imported module must propagate to a fresh rebuild printing 30"
        );
    }

    /// No source change → the binary is reused, not relinked. We assert the
    /// artifact's mtime is unchanged across a second run (a rebuild would rewrite
    /// the file). This is the happy path the freshness gate must not regress.
    #[test]
    fn lake_run_reuses_binary_when_source_unchanged() {
        if !cc_available() {
            eprintln!("skipping lake_run_reuses_binary_when_source_unchanged: no cc");
            return;
        }
        let dir = write_two_module_value_project("freshness_no_edit", 7);
        let ws = Workspace::new(dir.path(), "freshness_no_edit");
        let artifact = native_executable_build_path(&ws, "freshness_no_edit");

        assert_eq!(
            run_and_capture_stdout(dir.path(), "freshness_no_edit"),
            "7\n",
            "first run should build and print the value"
        );
        let first_mtime = std::fs::metadata(&artifact)
            .expect("artifact metadata after first build")
            .modified()
            .expect("mtime");

        // Sleep briefly so a rebuild (if it happened) would yield a distinct mtime.
        std::thread::sleep(std::time::Duration::from_millis(1100));

        assert_eq!(
            run_and_capture_stdout(dir.path(), "freshness_no_edit"),
            "7\n",
            "second run with unchanged source should still print the value"
        );
        let second_mtime = std::fs::metadata(&artifact)
            .expect("artifact metadata after second run")
            .modified()
            .expect("mtime");

        assert_eq!(
            first_mtime, second_mtime,
            "unchanged source must reuse the binary verbatim (no relink → mtime unchanged)"
        );
    }

    /// Transitive closure: a 3-module chain `Main` imports `Mid` imports `Leaf`.
    /// Editing the DEEPEST module (`Leaf`) must propagate a rebuild of `Main`'s
    /// binary, proving freshness covers the transitive (not just direct) closure.
    #[test]
    fn lake_run_rebuilds_on_transitively_imported_module_edit() {
        if !cc_available() {
            eprintln!("skipping lake_run_rebuilds_on_transitively_imported_module_edit: no cc");
            return;
        }
        let dir = tempfile::tempdir().expect("tempdir");
        std::fs::write(
            dir.path().join("lakefile.lean"),
            r#"import Lake
open Lake DSL

package freshness_chain where
  version := "0.1.0"

@[default_target]
lean_exe freshness_chain where
  root := `Main
"#,
        )
        .expect("write lakefile");
        std::fs::write(dir.path().join("Leaf.lean"), "def leaf : Nat := 1\n")
            .expect("write Leaf.lean");
        std::fs::write(
            dir.path().join("Mid.lean"),
            "import Leaf\ndef mid : Nat := leaf\n",
        )
        .expect("write Mid.lean");
        std::fs::write(
            dir.path().join("Main.lean"),
            "import Mid\ndef main : IO Unit := IO.println (toString mid)\n",
        )
        .expect("write Main.lean");

        assert_eq!(
            run_and_capture_stdout(dir.path(), "freshness_chain"),
            "1\n",
            "first run should print the leaf value threaded through the chain"
        );

        // Edit the deepest module Leaf 1 -> 9.
        std::fs::write(dir.path().join("Leaf.lean"), "def leaf : Nat := 9\n")
            .expect("rewrite Leaf.lean to 9");
        assert_eq!(
            run_and_capture_stdout(dir.path(), "freshness_chain"),
            "9\n",
            "editing the transitively-imported Leaf.lean must rebuild Main's binary and print 9"
        );
    }

    /// Closure is import-scoped: editing a sibling `.lean` that is NOT in the
    /// import closure must NOT invalidate the binary. We assert the artifact mtime
    /// is unchanged after touching an unrelated file.
    #[test]
    fn lake_run_does_not_rebuild_on_non_imported_sibling_edit() {
        if !cc_available() {
            eprintln!("skipping lake_run_does_not_rebuild_on_non_imported_sibling_edit: no cc");
            return;
        }
        let dir = write_two_module_value_project("freshness_unrelated", 5);
        // A sibling module Main does not import.
        std::fs::write(dir.path().join("Unrelated.lean"), "def noise : Nat := 0\n")
            .expect("write Unrelated.lean");
        let ws = Workspace::new(dir.path(), "freshness_unrelated");
        let artifact = native_executable_build_path(&ws, "freshness_unrelated");

        assert_eq!(
            run_and_capture_stdout(dir.path(), "freshness_unrelated"),
            "5\n",
            "first run should build and print the value"
        );
        let first_mtime = std::fs::metadata(&artifact)
            .expect("artifact metadata after first build")
            .modified()
            .expect("mtime");

        std::thread::sleep(std::time::Duration::from_millis(1100));

        // Edit the NON-imported sibling.
        std::fs::write(dir.path().join("Unrelated.lean"), "def noise : Nat := 42\n")
            .expect("rewrite Unrelated.lean");
        assert_eq!(
            run_and_capture_stdout(dir.path(), "freshness_unrelated"),
            "5\n",
            "non-imported sibling edit should not change behavior"
        );
        let second_mtime = std::fs::metadata(&artifact)
            .expect("artifact metadata after sibling edit")
            .modified()
            .expect("mtime");

        assert_eq!(
            first_mtime, second_mtime,
            "edit to a non-imported sibling must not force a rebuild (closure is import-scoped)"
        );
    }
}
