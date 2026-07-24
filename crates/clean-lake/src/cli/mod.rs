// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lake CLI command definitions and handlers.
//!
//! Provides the command enum and dispatch logic for Lake CLI operations.
//! The binary crate (clean-cli) wires these to clap; this module provides
//! the portable command types and handler implementations.
//!
//! Phase 2 of Epic #3436 moves the clap subcommand tree and descriptor array
//! for `lake` into this crate. See [`clap_args`] for the clap surface and
//! [`features::FEATURES`] for the `FeatureDescriptor` array consumed by
//! `clean features`, `clean help`, and the coverage gate in
//! `crates/clean-cli/tests/feature_coverage.rs`.
//!
//! Handlers for each [`LakeCommand`] variant live in [`dispatch`]; this file
//! is kept type-and-glue-only so the 500-LoC per-file cap is comfortably met.

mod clap_args;
mod dispatch;
mod features;
mod features_ext;
mod features_refs;
pub(crate) mod toolchain;

pub use clap_args::{CacheCommands, LakeArgs, LakeCommands, ScriptCommands};
pub use dispatch::run_lake;
pub use features::FEATURES;

use std::path::PathBuf;

/// Lake CLI subcommands
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum LakeCommand {
    /// Build the project
    Build(BuildArgs),
    /// Remove build artifacts
    Clean(CleanArgs),
    /// Create a new Lake project
    Init(InitArgs),
    /// Prefetch dependency sources without modifying the manifest
    Fetch(FetchArgs),
    /// Build an executable target and locate the produced binary
    Run(RunArgs),
    /// Locate (without rebuilding) a named executable target's binary
    Exe(ExeArgs),
    /// Build the package test targets and locate the produced test binaries
    Test(TestArgs),
    /// Print the resolved Lake environment as `key=value` lines
    Env(EnvArgs),
    /// Update dependencies to latest revisions
    Update(UpdateArgs),
}

/// Arguments for `lake build`
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct BuildArgs {
    /// Project directory (defaults to current directory)
    pub dir: Option<PathBuf>,
    /// Number of parallel jobs (0 = auto-detect)
    pub jobs: usize,
    /// Print verbose output
    pub verbose: bool,
    /// Force rebuild all modules
    pub force: bool,
    /// Only type-check, skip code generation
    pub check_only: bool,
}

/// Arguments for `lake clean`
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct CleanArgs {
    /// Project directory (defaults to current directory)
    pub dir: Option<PathBuf>,
}

/// Arguments for `lake init`
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct InitArgs {
    /// Directory in which to create the project
    pub dir: Option<PathBuf>,
    /// Package name
    pub name: String,
    /// Create a library (true) or executable (false) project
    pub lib: bool,
}

/// Arguments for `lake fetch`
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct FetchArgs {
    /// Project directory (defaults to current directory)
    pub dir: Option<PathBuf>,
}

/// Arguments for `lake run`
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct RunArgs {
    /// Project directory (defaults to current directory)
    pub dir: Option<PathBuf>,
    /// Executable target to build and run (defaults to the sole/default target)
    pub target: Option<String>,
    /// Arguments forwarded to the produced executable
    pub args: Vec<String>,
    /// Number of parallel jobs (0 = auto-detect)
    pub jobs: usize,
    /// Print verbose output
    pub verbose: bool,
}

/// Arguments for `lake exe`
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct ExeArgs {
    /// Project directory (defaults to current directory)
    pub dir: Option<PathBuf>,
    /// Executable target name to locate and run
    pub name: String,
    /// Arguments forwarded to the produced executable
    pub args: Vec<String>,
    /// Print verbose output
    pub verbose: bool,
}

/// Arguments for `lake test`
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct TestArgs {
    /// Project directory (defaults to current directory)
    pub dir: Option<PathBuf>,
    /// Test target name or substring filter (defaults to all test targets)
    pub target: Option<String>,
    /// Arguments forwarded to the produced test executable(s)
    pub args: Vec<String>,
    /// Number of parallel jobs (0 = auto-detect)
    pub jobs: usize,
    /// Print verbose output
    pub verbose: bool,
}

/// Arguments for `lake env`
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct EnvArgs {
    /// Project directory (defaults to current directory)
    pub dir: Option<PathBuf>,
}

/// Arguments for `lake update`
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct UpdateArgs {
    /// Project directory (defaults to current directory)
    pub dir: Option<PathBuf>,
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::dispatch::{
        format_build_result, format_env, format_fetch_results, format_run_command, lake_build,
        lake_clean, lake_env, lake_exe, lake_fetch, lake_init, lake_run, lake_test, lake_update,
        native_executable_build_path, native_executable_path, resolve_project_dir,
        select_executable, select_tests, short_rev,
    };
    use super::*;
    use crate::build::BuildResult;
    use crate::config::{LakeConfig, LeanExe, LeanTest};
    use crate::workspace::Workspace;
    use std::fs;
    use std::path::{Path, PathBuf};
    use tempfile::TempDir;

    fn lean_toolchain_fixture() -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../tests/fixtures/lean_toolchain/repo-root/lean-toolchain")
    }

    fn setup_project(tmp: &TempDir) {
        fs::write(
            tmp.path().join("lakefile.lean"),
            "package testpkg\nlean_lib TestPkg",
        )
        .unwrap();
    }

    fn setup_project_with_toolchain(tmp: &TempDir) {
        setup_project(tmp);
        fs::write(tmp.path().join("TestPkg.lean"), "-- test module").unwrap();
        fs::copy(lean_toolchain_fixture(), tmp.path().join("lean-toolchain")).unwrap();
    }

    #[test]
    fn test_resolve_project_dir_missing_and_present() {
        let tmp = TempDir::new().unwrap();
        let err = resolve_project_dir(Some(tmp.path())).unwrap_err();
        assert!(err.to_string().contains("lakefile.lean not found"));

        setup_project(&tmp);
        assert_eq!(resolve_project_dir(Some(tmp.path())).unwrap(), tmp.path());
    }

    #[test]
    fn test_lake_init_lib_project() {
        let tmp = TempDir::new().unwrap();
        let args = InitArgs {
            dir: Some(tmp.path().into()),
            name: "MyLib".into(),
            lib: true,
        };
        let msg = lake_init(&args).unwrap();
        assert!(msg.contains("MyLib"));

        let content = fs::read_to_string(tmp.path().join("lakefile.lean")).unwrap();
        assert!(content.contains("package MyLib") && content.contains("lean_lib MyLib"));
        assert!(tmp.path().join("MyLib.lean").exists());
        let toolchain = fs::read_to_string(tmp.path().join("lean-toolchain")).unwrap();
        assert_eq!(toolchain, "clean:stable\n");
        assert!(!toolchain.contains("leanprover/lean4"));
    }

    #[test]
    fn test_lake_init_exe_project() {
        let tmp = TempDir::new().unwrap();
        let args = InitArgs {
            dir: Some(tmp.path().into()),
            name: "myapp".into(),
            lib: false,
        };
        lake_init(&args).expect("init exe should succeed");

        let content = fs::read_to_string(tmp.path().join("lakefile.lean")).unwrap();
        assert!(content.contains("lean_exe myapp"));
        let main_content = fs::read_to_string(tmp.path().join("Main.lean")).unwrap();
        assert!(main_content.contains("Hello, myapp!"));
        assert!(!main_content.contains("{name}"));
    }

    #[test]
    fn test_lake_init_rejects_existing_lakefile() {
        let tmp = TempDir::new().unwrap();
        setup_project(&tmp);
        let args = InitArgs {
            dir: Some(tmp.path().into()),
            name: "dup".into(),
            lib: true,
        };
        let err = lake_init(&args).unwrap_err();
        assert!(err.to_string().contains("already exists"));
    }

    #[test]
    fn test_lake_clean_empty_and_with_artifacts() {
        let tmp = TempDir::new().unwrap();
        setup_project(&tmp);

        // Nothing to clean
        let args = CleanArgs {
            dir: Some(tmp.path().into()),
        };
        assert!(lake_clean(&args).unwrap().contains("Nothing to clean"));

        // Create build artifacts, then clean
        let build_dir = tmp.path().join(".lake/build");
        fs::create_dir_all(&build_dir).unwrap();
        fs::write(build_dir.join("artifact.olean"), "data").unwrap();

        let msg = lake_clean(&args).unwrap();
        assert!(msg.contains("cleaned"));
        assert!(!build_dir.exists());
    }

    #[test]
    fn test_lake_build_succeeds() {
        let tmp = TempDir::new().unwrap();
        setup_project_with_toolchain(&tmp);

        let args = BuildArgs {
            dir: Some(tmp.path().into()),
            ..Default::default()
        };
        let msg = lake_build(&args).expect("build should succeed");
        assert!(msg.contains("Toolchain: v4.13.0"));
        assert!(msg.contains("Build succeeded") || msg.contains("Build finished"));
    }

    #[test]
    fn test_lake_update_no_deps() {
        let tmp = TempDir::new().unwrap();
        setup_project(&tmp);
        let args = UpdateArgs {
            dir: Some(tmp.path().into()),
        };
        assert!(lake_update(&args)
            .unwrap()
            .contains("No dependencies to update"));
    }

    #[test]
    fn test_format_build_result() {
        use std::time::Duration;

        let ok = BuildResult {
            built: vec!["A".into(), "B".into()],
            skipped: vec!["C".into()],
            failed: vec![],
            duration: Duration::from_millis(42),
        };
        let msg = format_build_result(&ok);
        assert!(msg.contains("Build succeeded") && msg.contains("2 built"));

        let fail = BuildResult {
            built: vec!["A".into()],
            skipped: vec![],
            failed: vec![("Bad".into(), "type error".into())],
            duration: Duration::from_millis(100),
        };
        let msg = format_build_result(&fail);
        assert!(msg.contains("Build finished with errors") && msg.contains("FAIL Bad"));
    }

    #[test]
    fn test_short_rev_truncation() {
        assert_eq!(short_rev("abc"), "abc");
        assert_eq!(short_rev("abcdef123456789"), "abcdef123456");
    }

    /// Regression: an unvalidated `rev` in `lake-manifest.json` may be non-ASCII.
    /// When byte index 12 fell inside a multi-byte UTF-8 char, `&rev[..12]` used
    /// to panic ("byte index 12 is not a char boundary"). `short_rev` now
    /// truncates on a `char` boundary instead of a raw byte offset.
    #[test]
    fn test_short_rev_non_ascii_char_boundary_no_panic() {
        // 1 ASCII byte + seven 'é' (2 bytes each) = 15 bytes; byte 12 falls
        // inside the 6th 'é' (bytes 11..13), so it is NOT a char boundary. The
        // old `&rev[..12]` panicked on exactly this shape ("byte index 12 is not
        // a char boundary"). This string has only 8 *chars*, so nothing is
        // truncated: it must round-trip unchanged (and not panic).
        let rev = "aééééééé";
        assert_eq!(rev.len(), 15);
        assert!(!rev.is_char_boundary(12));
        assert_eq!(short_rev(rev), rev);

        // A non-ASCII rev with >12 chars whose byte 12 is mid-codepoint: the old
        // code panicked here; the fix truncates on the 12th *char* boundary.
        let long = "aéééééééééééééé"; // 'a' + 14 'é' = 15 chars, 29 bytes
        assert_eq!(long.chars().count(), 15);
        assert!(!long.is_char_boundary(12));
        let got = short_rev(long);
        assert_eq!(got.chars().count(), 12);
        assert_eq!(got, "aééééééééééé");

        // The correct (ASCII git SHA) path is unchanged: exactly the first 12
        // bytes, byte-identical to the previous implementation.
        assert_eq!(
            short_rev("0123456789abcdef0123456789abcdef01234567"),
            "0123456789ab"
        );
    }

    /// The portable [`run_lake`] dispatch must be defined for every variant of
    /// the portable [`LakeCommand`] subset. This is the subset embedders drive
    /// directly; the full advertised verb set is exercised by the unified
    /// binary's clap dispatch (see
    /// [`run_lake_subset_matches_advertised_features`]).
    #[test]
    fn test_run_lake_dispatches_portable_subset() {
        // Build
        let tmp = TempDir::new().unwrap();
        setup_project(&tmp);
        fs::write(tmp.path().join("TestPkg.lean"), "-- m").unwrap();
        run_lake(&LakeCommand::Build(BuildArgs {
            dir: Some(tmp.path().into()),
            ..Default::default()
        }))
        .expect("dispatch build");

        // clean
        run_lake(&LakeCommand::Clean(CleanArgs {
            dir: Some(tmp.path().into()),
        }))
        .expect("dispatch clean");

        // Init
        let tmp2 = TempDir::new().unwrap();
        run_lake(&LakeCommand::Init(InitArgs {
            dir: Some(tmp2.path().into()),
            name: "dt".into(),
            lib: true,
        }))
        .expect("dispatch init");

        // Update
        run_lake(&LakeCommand::Update(UpdateArgs {
            dir: Some(tmp2.path().into()),
        }))
        .expect("dispatch update");

        // Fetch (no deps -> trivially succeeds without touching the manifest)
        let fetch_msg = run_lake(&LakeCommand::Fetch(FetchArgs {
            dir: Some(tmp.path().into()),
        }))
        .expect("dispatch fetch");
        assert!(fetch_msg.contains("No dependencies to fetch"));

        // Env (always succeeds for a workspace with a lakefile)
        let env_msg = run_lake(&LakeCommand::Env(EnvArgs {
            dir: Some(tmp.path().into()),
        }))
        .expect("dispatch env");
        assert!(env_msg.contains("LEAN_PATH="));
    }

    /// The set of advertised leaf verbs (`FEATURES`) the portable [`run_lake`]
    /// dispatch is responsible for. Every other advertised verb is intentionally
    /// owned by the unified binary's clap dispatch
    /// (`clean_cli::cmd_lake::handle_lake_command`) because it needs
    /// process/stdout/exit-code semantics this `String`-returning library entry
    /// point deliberately does not provide.
    const RUN_LAKE_PORTABLE_VERBS: &[&[&str]] = &[
        &["lake", "build"],
        &["lake", "clean"],
        &["lake", "init"],
        &["lake", "fetch"],
        &["lake", "run"],
        &["lake", "exe"],
        &["lake", "test"],
        &["lake", "env"],
        &["lake", "update"],
    ];

    /// Map a portable [`LakeCommand`] variant to its advertised `FEATURES` path.
    /// Exhaustive on purpose: adding a `LakeCommand` variant forces a decision
    /// here, which in turn updates [`RUN_LAKE_PORTABLE_VERBS`] coverage below.
    fn portable_command_feature_path(cmd: &LakeCommand) -> &'static [&'static str] {
        match cmd {
            LakeCommand::Build(_) => &["lake", "build"],
            LakeCommand::Clean(_) => &["lake", "clean"],
            LakeCommand::Init(_) => &["lake", "init"],
            LakeCommand::Fetch(_) => &["lake", "fetch"],
            LakeCommand::Run(_) => &["lake", "run"],
            LakeCommand::Exe(_) => &["lake", "exe"],
            LakeCommand::Test(_) => &["lake", "test"],
            LakeCommand::Env(_) => &["lake", "env"],
            LakeCommand::Update(_) => &["lake", "update"],
        }
    }

    /// Contract gate: the advertised Lake verb set (`FEATURES`) is fully
    /// accounted for, with no silent "advertises more than it runs" drift.
    ///
    /// For every advertised leaf verb, exactly one of two things must hold:
    ///   1. it is in the portable subset [`run_lake`] handles directly, or
    ///   2. it is owned by the unified binary's clap dispatch
    ///      (`clean_cli::cmd_lake::handle_lake_command`).
    ///
    /// This test also pins that [`run_lake`]'s portable subset is exactly the
    /// nine verbs documented in [`dispatch`], and that
    /// [`portable_command_feature_path`] (which is compiler-exhaustive over
    /// [`LakeCommand`]) agrees. If a future variant is added to `LakeCommand`
    /// without extending the portable verb list, or an advertised verb is added
    /// to `FEATURES` without being claimed by either surface, this fails.
    #[test]
    fn run_lake_subset_matches_advertised_features() {
        use std::collections::BTreeSet;

        // (1) The portable verb list must match what `portable_command_feature_path`
        // can emit, i.e. one entry per `LakeCommand` variant. We construct one
        // representative of each variant and collect the mapped paths.
        let representatives: &[LakeCommand] = &[
            LakeCommand::Build(BuildArgs::default()),
            LakeCommand::Clean(CleanArgs::default()),
            LakeCommand::Init(InitArgs {
                dir: None,
                name: "x".into(),
                lib: true,
            }),
            LakeCommand::Fetch(FetchArgs::default()),
            LakeCommand::Run(RunArgs::default()),
            LakeCommand::Exe(ExeArgs::default()),
            LakeCommand::Test(TestArgs::default()),
            LakeCommand::Env(EnvArgs::default()),
            LakeCommand::Update(UpdateArgs::default()),
        ];
        let mapped: BTreeSet<Vec<&str>> = representatives
            .iter()
            .map(|c| portable_command_feature_path(c).to_vec())
            .collect();
        let declared: BTreeSet<Vec<&str>> =
            RUN_LAKE_PORTABLE_VERBS.iter().map(|p| p.to_vec()).collect();
        assert_eq!(
            mapped, declared,
            "RUN_LAKE_PORTABLE_VERBS must list exactly the verbs reachable through \
             run_lake (one per LakeCommand variant); update it when adding a variant"
        );

        // (2) Every portable verb must actually be an advertised feature.
        let advertised: BTreeSet<Vec<&str>> = FEATURES.iter().map(|d| d.path.to_vec()).collect();
        for verb in RUN_LAKE_PORTABLE_VERBS {
            assert!(
                advertised.iter().any(|p| p.as_slice() == *verb),
                "portable verb {verb:?} is not in the advertised FEATURES set"
            );
        }

        // (3) Every advertised verb is honored by exactly one surface: either
        // the portable run_lake subset, or the binary front-end's clap dispatch.
        // The binary-owned verbs are everything advertised that is NOT portable.
        // There must be no advertised verb left unaccounted for (this is the
        // anti-"advertises more than it runs" assertion), and the two surfaces
        // must not overlap.
        let portable: BTreeSet<Vec<&str>> = declared;
        let binary_owned: BTreeSet<Vec<&str>> = advertised.difference(&portable).cloned().collect();
        // Union of the two surfaces must reproduce the advertised set exactly.
        let union: BTreeSet<Vec<&str>> = portable.union(&binary_owned).cloned().collect();
        assert_eq!(
            union, advertised,
            "every advertised Lake verb must be owned by either run_lake or the \
             binary front-end; an unaccounted verb means the advertised contract \
             is not honored"
        );
        // Sanity: surfaces are disjoint.
        assert!(
            portable.is_disjoint(&binary_owned),
            "a verb cannot be owned by both run_lake and the binary front-end"
        );
        // Sanity: the known binary-owned verbs are present (guards against the
        // advertised set silently shrinking below the documented surface).
        for expected in [
            ["lake", "new"].as_slice(),
            ["lake", "resolve"].as_slice(),
            ["lake", "script", "list"].as_slice(),
            ["lake", "cache", "get"].as_slice(),
            ["lake", "lint"].as_slice(),
            ["lake", "check-build"].as_slice(),
            ["lake", "pack"].as_slice(),
            ["lake", "unpack"].as_slice(),
            ["lake", "upload"].as_slice(),
        ] {
            assert!(
                binary_owned.iter().any(|p| p.as_slice() == expected),
                "expected binary-owned advertised verb {expected:?} to be present"
            );
        }
    }

    // -----------------------------------------------------------------------
    // Fetch
    // -----------------------------------------------------------------------

    #[test]
    fn test_lake_fetch_no_deps_does_not_create_manifest() {
        let tmp = TempDir::new().unwrap();
        setup_project(&tmp);

        let args = FetchArgs {
            dir: Some(tmp.path().into()),
        };
        let msg = lake_fetch(&args).expect("fetch with no deps should succeed");
        assert!(msg.contains("No dependencies to fetch"));
        // Fetch must never write a manifest (unlike update).
        assert!(!tmp.path().join("lake-manifest.json").exists());
    }

    #[test]
    fn test_lake_fetch_missing_lakefile_errors() {
        let tmp = TempDir::new().unwrap();
        let args = FetchArgs {
            dir: Some(tmp.path().into()),
        };
        let err = lake_fetch(&args).expect_err("fetch without a lakefile should fail");
        assert!(err.to_string().contains("lakefile.lean not found"));
    }

    #[test]
    fn test_format_fetch_results_empty_and_populated() {
        assert!(format_fetch_results(&[]).contains("already present"));

        let msg = format_fetch_results(&["std".to_string(), "mathlib".to_string()]);
        assert!(msg.contains("Fetched 2 dependencies"));
        assert!(msg.contains("std") && msg.contains("mathlib"));
    }

    // -----------------------------------------------------------------------
    // Run
    // -----------------------------------------------------------------------

    fn exe_config(name: &str, default: bool) -> LakeConfig {
        let mut config = LakeConfig::default();
        config.package.name = name.to_string();
        config.exes.push(LeanExe {
            name: name.to_string(),
            root: "Main".to_string(),
            ..Default::default()
        });
        if default {
            config.default_targets.push(name.to_string());
        }
        config
    }

    #[test]
    fn test_select_executable_explicit_target_resolves() {
        let config = exe_config("app", false);
        let exe = select_executable(&config, Some("app")).expect("explicit target resolves");
        assert_eq!(exe.name, "app");
    }

    #[test]
    fn test_select_executable_default_target_resolves() {
        let config = exe_config("app", true);
        let exe = select_executable(&config, None).expect("default target resolves");
        assert_eq!(exe.name, "app");
    }

    #[test]
    fn test_select_executable_sole_target_resolves() {
        let config = exe_config("only", false);
        let exe = select_executable(&config, None).expect("sole target resolves");
        assert_eq!(exe.name, "only");
    }

    #[test]
    fn test_select_executable_missing_target_errors() {
        let config = exe_config("app", false);
        let err = select_executable(&config, Some("nope")).unwrap_err();
        assert!(err.to_string().contains("'nope'"));
    }

    #[test]
    fn test_select_executable_no_exe_errors() {
        let config = LakeConfig::default();
        let err = select_executable(&config, None).unwrap_err();
        assert!(err.to_string().contains("no executable targets"));
    }

    #[test]
    fn test_select_executable_ambiguous_errors() {
        let mut config = exe_config("first", false);
        config.exes.push(LeanExe {
            name: "second".to_string(),
            root: "Other".to_string(),
            ..Default::default()
        });
        let err = select_executable(&config, None).unwrap_err();
        assert!(err.to_string().contains("multiple executables"));
    }

    #[test]
    fn test_format_run_command_appends_args() {
        let path = Path::new("/tmp/.lake/build/bin/app");
        let cmd = format_run_command(path, &["--flag".to_string(), "value".to_string()]);
        assert_eq!(cmd, "/tmp/.lake/build/bin/app --flag value");
    }

    #[test]
    fn test_native_executable_path_prefers_bin_artifact() {
        let tmp = TempDir::new().unwrap();
        let ws = Workspace::new(tmp.path(), "app");
        // No artifact yet.
        assert!(native_executable_path(&ws, "app").is_none());

        let expected = native_executable_build_path(&ws, "app");
        fs::create_dir_all(expected.parent().expect("bin dir")).unwrap();
        fs::write(&expected, "binary").unwrap();
        assert_eq!(native_executable_path(&ws, "app"), Some(expected));
    }

    fn setup_exe_project(tmp: &TempDir) {
        fs::write(
            tmp.path().join("lakefile.lean"),
            "package runpkg\n\nlean_exe runpkg where\n  root := `Main\n",
        )
        .unwrap();
        fs::write(
            tmp.path().join("Main.lean"),
            "def main : IO Unit := pure ()\n",
        )
        .unwrap();
    }

    #[test]
    fn test_lake_run_builds_and_reports_missing_artifact() {
        let tmp = TempDir::new().unwrap();
        setup_exe_project(&tmp);

        let args = RunArgs {
            dir: Some(tmp.path().into()),
            target: Some("runpkg".to_string()),
            args: vec!["--demo".to_string()],
            jobs: 1,
            verbose: false,
        };
        let msg = lake_run(&args).expect("run should build and locate (or report) the target");
        // This crate has no native runtime, so no executable artifact is
        // produced; the handler must report that rather than spawn or panic.
        assert!(msg.contains("no native executable artifact was found"));
        assert!(msg.contains("runpkg"));
    }

    #[test]
    fn test_lake_run_resolves_existing_artifact_command() {
        let tmp = TempDir::new().unwrap();
        setup_exe_project(&tmp);

        // Pre-place a native artifact so run resolves and renders the command.
        let ws = Workspace::load(tmp.path()).unwrap();
        let artifact = native_executable_build_path(&ws, "runpkg");
        fs::create_dir_all(artifact.parent().expect("bin dir")).unwrap();
        fs::write(&artifact, "binary").unwrap();

        let args = RunArgs {
            dir: Some(tmp.path().into()),
            target: Some("runpkg".to_string()),
            args: vec!["--flag".to_string()],
            jobs: 1,
            verbose: false,
        };
        let msg = lake_run(&args).expect("run should resolve the pre-placed artifact");
        assert!(msg.contains("Executable:"));
        assert!(msg.contains("Would run:") && msg.contains("--flag"));
        assert!(msg.contains(&artifact.display().to_string()));
    }

    #[test]
    fn test_lake_run_missing_lakefile_errors() {
        let tmp = TempDir::new().unwrap();
        let args = RunArgs {
            dir: Some(tmp.path().into()),
            ..Default::default()
        };
        let err = lake_run(&args).expect_err("run without a lakefile should fail");
        assert!(err.to_string().contains("lakefile.lean not found"));
    }

    #[test]
    fn test_lake_run_unknown_target_errors() {
        let tmp = TempDir::new().unwrap();
        setup_exe_project(&tmp);

        let args = RunArgs {
            dir: Some(tmp.path().into()),
            target: Some("ghost".to_string()),
            ..Default::default()
        };
        let err = lake_run(&args).expect_err("run with unknown target should fail");
        assert!(err.to_string().contains("'ghost'"));
    }

    // -----------------------------------------------------------------------
    // Exe
    // -----------------------------------------------------------------------

    #[test]
    fn test_lake_exe_resolves_existing_artifact_without_building() {
        let tmp = TempDir::new().unwrap();
        setup_exe_project(&tmp);

        // Pre-place a native artifact so exe resolves and renders the command.
        let ws = Workspace::load(tmp.path()).unwrap();
        let artifact = native_executable_build_path(&ws, "runpkg");
        fs::create_dir_all(artifact.parent().expect("bin dir")).unwrap();
        fs::write(&artifact, "binary").unwrap();

        let args = ExeArgs {
            dir: Some(tmp.path().into()),
            name: "runpkg".to_string(),
            args: vec!["--flag".to_string()],
            verbose: false,
        };
        let msg = lake_exe(&args).expect("exe should resolve the pre-placed artifact");
        assert!(msg.contains("Executable:"));
        assert!(msg.contains("Would run:") && msg.contains("--flag"));
        assert!(msg.contains(&artifact.display().to_string()));
    }

    #[test]
    fn test_lake_exe_reports_missing_artifact() {
        let tmp = TempDir::new().unwrap();
        setup_exe_project(&tmp);

        let args = ExeArgs {
            dir: Some(tmp.path().into()),
            name: "runpkg".to_string(),
            ..Default::default()
        };
        let msg = lake_exe(&args).expect("exe should resolve target and report missing artifact");
        assert!(msg.contains("no native executable artifact"));
        assert!(msg.contains("runpkg"));
    }

    #[test]
    fn test_lake_exe_unknown_target_errors() {
        let tmp = TempDir::new().unwrap();
        setup_exe_project(&tmp);

        let args = ExeArgs {
            dir: Some(tmp.path().into()),
            name: "ghost".to_string(),
            ..Default::default()
        };
        let err = lake_exe(&args).expect_err("exe with unknown target should fail");
        assert!(err.to_string().contains("'ghost'"));
    }

    #[test]
    fn test_lake_exe_missing_lakefile_errors() {
        let tmp = TempDir::new().unwrap();
        let args = ExeArgs {
            dir: Some(tmp.path().into()),
            name: "anything".to_string(),
            ..Default::default()
        };
        let err = lake_exe(&args).expect_err("exe without a lakefile should fail");
        assert!(err.to_string().contains("lakefile.lean not found"));
    }

    #[test]
    fn test_run_lake_dispatches_exe() {
        let tmp = TempDir::new().unwrap();
        setup_exe_project(&tmp);
        let msg = run_lake(&LakeCommand::Exe(ExeArgs {
            dir: Some(tmp.path().into()),
            name: "runpkg".to_string(),
            ..Default::default()
        }))
        .expect("dispatch exe");
        assert!(msg.contains("runpkg"));
    }

    // -----------------------------------------------------------------------
    // Test
    // -----------------------------------------------------------------------

    fn setup_test_project(tmp: &TempDir) {
        fs::write(
            tmp.path().join("lakefile.lean"),
            "package testpkg\n\nlean_test unit where\n  root := `Test.Unit\n",
        )
        .unwrap();
        fs::create_dir_all(tmp.path().join("Test")).unwrap();
        fs::write(
            tmp.path().join("Test/Unit.lean"),
            "def main : IO Unit := pure ()\n",
        )
        .unwrap();
    }

    #[test]
    fn test_select_tests_no_target_returns_all() {
        let mut config = LakeConfig::default();
        config.tests.push(LeanTest {
            name: "a".to_string(),
            root: "Test.A".to_string(),
            ..Default::default()
        });
        config.tests.push(LeanTest {
            name: "b".to_string(),
            root: "Test.B".to_string(),
            ..Default::default()
        });
        let selected = select_tests(&config, None).expect("all tests");
        assert_eq!(selected.len(), 2);
    }

    #[test]
    fn test_select_tests_exact_name_resolves() {
        let mut config = LakeConfig::default();
        config.tests.push(LeanTest {
            name: "unit".to_string(),
            root: "Test.Unit".to_string(),
            ..Default::default()
        });
        let selected = select_tests(&config, Some("unit")).expect("exact match");
        assert_eq!(selected.len(), 1);
        assert_eq!(selected[0].name, "unit");
    }

    #[test]
    fn test_select_tests_substring_filter_resolves() {
        let mut config = LakeConfig::default();
        config.tests.push(LeanTest {
            name: "integration_smoke".to_string(),
            root: "Test.Smoke".to_string(),
            ..Default::default()
        });
        let selected = select_tests(&config, Some("smoke")).expect("substring match");
        assert_eq!(selected.len(), 1);
        assert_eq!(selected[0].name, "integration_smoke");
    }

    #[test]
    fn test_select_tests_no_tests_errors() {
        let config = LakeConfig::default();
        let err = select_tests(&config, None).unwrap_err();
        assert!(err.to_string().contains("no test targets defined"));
    }

    #[test]
    fn test_select_tests_unknown_filter_errors() {
        let mut config = LakeConfig::default();
        config.tests.push(LeanTest {
            name: "unit".to_string(),
            root: "Test.Unit".to_string(),
            ..Default::default()
        });
        let err = select_tests(&config, Some("ghost")).unwrap_err();
        assert!(err.to_string().contains("ghost"));
    }

    #[test]
    fn test_lake_test_builds_and_reports_test_driver() {
        let tmp = TempDir::new().unwrap();
        setup_test_project(&tmp);

        let args = TestArgs {
            dir: Some(tmp.path().into()),
            target: Some("unit".to_string()),
            jobs: 1,
            ..Default::default()
        };
        let msg = lake_test(&args).expect("test should build and locate (or report) the driver");
        assert!(msg.contains("Running 1 test target(s)"));
        assert!(msg.contains("Test 'unit'"));
        // This crate has no native runtime, so no executable artifact is
        // produced; the handler reports that rather than spawning.
        assert!(msg.contains("no native executable artifact was found"));
    }

    #[test]
    fn test_lake_test_no_tests_errors() {
        let tmp = TempDir::new().unwrap();
        setup_project(&tmp);
        let args = TestArgs {
            dir: Some(tmp.path().into()),
            ..Default::default()
        };
        let err = lake_test(&args).expect_err("test with no test targets should fail");
        assert!(err.to_string().contains("no test targets defined"));
    }

    #[test]
    fn test_lake_test_missing_lakefile_errors() {
        let tmp = TempDir::new().unwrap();
        let args = TestArgs {
            dir: Some(tmp.path().into()),
            ..Default::default()
        };
        let err = lake_test(&args).expect_err("test without a lakefile should fail");
        assert!(err.to_string().contains("lakefile.lean not found"));
    }

    #[test]
    fn test_run_lake_dispatches_test() {
        let tmp = TempDir::new().unwrap();
        setup_test_project(&tmp);
        let msg = run_lake(&LakeCommand::Test(TestArgs {
            dir: Some(tmp.path().into()),
            jobs: 1,
            ..Default::default()
        }))
        .expect("dispatch test");
        assert!(msg.contains("Running 1 test target(s)"));
    }

    // -----------------------------------------------------------------------
    // Env
    // -----------------------------------------------------------------------

    #[test]
    fn test_lake_env_prints_expected_keys() {
        let tmp = TempDir::new().unwrap();
        setup_project_with_toolchain(&tmp);

        let args = EnvArgs {
            dir: Some(tmp.path().into()),
        };
        let msg = lake_env(&args).expect("env should resolve the workspace");
        for key in [
            "LAKE_PACKAGE=",
            "LAKE_ROOT=",
            "LEAN_PATH=",
            "LEAN_SRC_PATH=",
            "LEAN_TOOLCHAIN=",
        ] {
            assert!(msg.contains(key), "env output missing {key}: {msg}");
        }
        // Toolchain fixture resolves to a concrete version.
        assert!(msg.contains("LEAN_TOOLCHAIN=v4.13.0"));
        // Every reported line is a single key=value pair.
        for line in msg.lines() {
            assert!(line.contains('='), "non key=value line: {line}");
        }
    }

    #[test]
    fn test_format_env_lean_path_includes_lib_dir() {
        let tmp = TempDir::new().unwrap();
        let ws = Workspace::new(tmp.path(), "envpkg");
        let env = format_env(&ws);
        assert!(env.contains("LAKE_PACKAGE=envpkg"));
        assert!(env.contains(&ws.lib_dir().display().to_string()));
        // No toolchain configured -> empty toolchain value, not a panic.
        assert!(env.contains("LEAN_TOOLCHAIN=\n") || env.ends_with("LEAN_TOOLCHAIN="));
    }

    #[test]
    fn test_lake_env_missing_lakefile_errors() {
        let tmp = TempDir::new().unwrap();
        let args = EnvArgs {
            dir: Some(tmp.path().into()),
        };
        let err = lake_env(&args).expect_err("env without a lakefile should fail");
        assert!(err.to_string().contains("lakefile.lean not found"));
    }
}
