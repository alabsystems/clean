// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared harness for the Lake parity battery: fixture writers, in-process
//! build entry points, a filesystem-only git fixture builder, and the
//! `.olean` triple assertion. Split out of `parity_battery.rs` for file size;
//! the row modules are its only callers.

use std::fs;
use std::path::Path;
use std::process::Command;

use clean_lake::cli::{RunArgs, TestArgs};
use clean_lake::{BuildContext, BuildOptions, BuildResult, LakeError, Workspace};
// ---------------------------------------------------------------------------
// Harness helpers (mirroring the idiom of the build.rs / fetch.rs unit tests)
// ---------------------------------------------------------------------------

/// Write a fixture file, creating parent directories as needed.
pub(crate) fn write_file(path: &Path, content: &str) {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).expect("create fixture parent dir");
    }
    fs::write(path, content).expect("write fixture file");
}

/// The Lean world `clean lake build` selects for a fixture project, all of
/// which live under the system temporary directory with no `lean-toolchain`
/// above them: the checkout's pin.
fn builder_world() -> clean_olean::SourceWorldDecision {
    clean_olean::source_world_for_file(&std::env::temp_dir().join("Builder.lean"), None)
        .expect("the builder's Lean world")
}

/// A fresh copy of the environment `clean lake build` starts a module
/// without `prelude` from: genuine Init of the builder's world, as Lean's
/// implicit `import Init`.
pub(crate) fn genuine_init_env() -> clean_kernel::Environment {
    static INIT: std::sync::OnceLock<clean_kernel::Environment> = std::sync::OnceLock::new();
    INIT.get_or_init(|| {
        use clean_elab::module_driver::{EnvironmentSetup, SourceModuleSetup};
        SourceModuleSetup::new(EnvironmentSetup::default(), &builder_world())
            .expect("the builder's backbone")
            .initial_environment(&clean_parser::FileHeader::default())
            .expect("genuine Init")
    })
    .clone()
}

/// Where a built artifact's imports resolve: the build directory, then the
/// builder's world library, which holds the `Init` every artifact records,
/// as for an artifact Lean wrote.
pub(crate) fn artifact_load_paths(lib_dir: &Path) -> Vec<std::path::PathBuf> {
    let mut paths = vec![lib_dir.to_path_buf()];
    paths.extend(clean_olean::search_paths_in_world(
        builder_world().imports().expect("an admitted world"),
    ));
    paths
}

/// Load the workspace at `root` and run a full build with `options`.
pub(crate) fn build_all_with(root: &Path, options: BuildOptions) -> BuildResult {
    let ws = Workspace::load(root).expect("workspace should load");
    let mut ctx = BuildContext::new(ws).with_options(options);
    ctx.build_all().expect("build_all should return a result")
}

/// Load the workspace at `root` and run a full default-options build.
pub(crate) fn build_all(root: &Path) -> BuildResult {
    build_all_with(root, BuildOptions::new())
}

/// Load the workspace at `root` and run a full build, returning the error
/// instead of panicking (for the fail-closed rows).
pub(crate) fn try_build_all(root: &Path) -> Result<BuildResult, LakeError> {
    let ws = Workspace::load(root).expect("workspace should load");
    let mut ctx = BuildContext::new(ws);
    ctx.build_all()
}

/// Sort a name list for order-independent comparison (parallel build levels
/// make within-level completion order nondeterministic).
pub(crate) fn sorted(mut names: Vec<String>) -> Vec<String> {
    names.sort();
    names
}

/// Assert the full `.olean` triple (`.olean` / `.olean.server` /
/// `.olean.private`) exists for `module` and the base part is non-empty.
pub(crate) fn assert_olean_triple(ws: &Workspace, module: &str) {
    for path in [
        ws.olean_path(module).expect("valid module output path"),
        ws.olean_server_path(module)
            .expect("valid server output path"),
        ws.olean_private_path(module)
            .expect("valid private output path"),
    ] {
        assert!(
            path.exists(),
            "expected build artifact {} for module {module}",
            path.display()
        );
    }
    let base_len = fs::metadata(ws.olean_path(module).expect("valid module output path"))
        .expect("stat base .olean")
        .len();
    assert!(base_len > 0, "base .olean for {module} must not be empty");
}

/// Run a git subcommand in `dir`, panicking with stderr on failure.
pub(crate) fn git(dir: &Path, args: &[&str]) {
    let out = Command::new("git")
        .arg("-C")
        .arg(dir)
        .args(args)
        .output()
        .expect("git should be runnable in the test environment");
    assert!(
        out.status.success(),
        "git {args:?} failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
}

/// Turn `dir` into a single-commit git repo on branch `main`, so it can serve
/// as a local "remote" for clone-based rows (constraint: no network).
pub(crate) fn git_init_commit(dir: &Path) {
    git(dir, &["init", "-q", "-b", "main"]);
    git(dir, &["add", "-A"]);
    git(
        dir,
        &[
            "-c",
            "user.email=parity@example.com",
            "-c",
            "user.name=Parity",
            "-c",
            "commit.gpgsign=false",
            "commit",
            "-q",
            "-m",
            "init",
        ],
    );
}

/// Build `RunArgs` for the portable `lake run` verb.
///
/// The portable arg structs are `#[non_exhaustive]`, so an external crate has
/// no struct-literal syntax for them; Default-then-assign is the supported
/// construction path (clippy's `field_reassign_with_default` does not fire on
/// non-exhaustive structs from another crate).
pub(crate) fn run_args(dir: &Path, target: Option<&str>) -> RunArgs {
    let mut args = RunArgs::default();
    args.dir = Some(dir.to_path_buf());
    args.target = target.map(str::to_string);
    args.jobs = 1;
    args
}

/// Build `TestArgs` for the portable `lake test` verb (see [`run_args`] for
/// why Default-then-assign construction is used).
pub(crate) fn test_args(dir: &Path, target: Option<&str>) -> TestArgs {
    let mut args = TestArgs::default();
    args.dir = Some(dir.to_path_buf());
    args.target = target.map(str::to_string);
    args.jobs = 1;
    args
}

// ---------------------------------------------------------------------------
// Row 01 — lakefile.toml lib build emits the .olean triple and round-trips
// ---------------------------------------------------------------------------
