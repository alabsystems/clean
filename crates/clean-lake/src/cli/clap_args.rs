// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Clap subcommand tree for the `clean lake` domain.
//!
//! This is the user-facing parser for every `clean lake <verb>` invocation.
//! The top-level `clean-cli` binary attaches [`LakeArgs`] to its `Commands`
//! enum via `#[command(flatten)]`, which keeps the verb-level parsing logic
//! owned by this crate.
//!
//! Every leaf subcommand here has a matching [`crate::cli::FEATURES`]
//! descriptor. The `feature_coverage_matches_clap` drift test in
//! `crates/clean-cli/tests/feature_coverage.rs` enforces that invariant.
//!
//! Part of Epic #3436 (unified CLI feature index). See
//! `designs/2026-04-18-unified-cli-feature-index.md`.

use clap::Subcommand;
use std::path::PathBuf;

/// Top-level arguments for `clean lake`.
///
/// Holds the `--dir` override that every Lake subcommand shares and the
/// verb-level subcommand enum. The `clean-cli` binary embeds this as
/// `Commands::Lake(LakeArgs)`.
#[derive(Debug, clap::Args)]
pub struct LakeArgs {
    /// Directory containing lakefile.lean (defaults to current directory).
    #[arg(short = 'd', long = "dir", global = true)]
    pub dir: Option<PathBuf>,

    /// Verb-level subcommand.
    #[command(subcommand)]
    pub command: LakeCommands,
}

/// Top-level `lake` verbs.
///
/// Each variant corresponds to one leaf feature in `FEATURES`. The
/// `Script(..)` and `Cache(..)` variants nest further subcommand trees —
/// see [`ScriptCommands`] and [`CacheCommands`].
#[derive(Debug, Subcommand)]
pub enum LakeCommands {
    /// Build the project
    Build {
        /// Target to build (default: all targets)
        target: Option<String>,
        /// Show verbose output
        #[arg(short, long)]
        verbose: bool,
        /// Force rebuild all
        #[arg(short, long)]
        force: bool,
        /// Number of parallel jobs (0 = auto)
        #[arg(short, long, default_value = "0")]
        jobs: usize,
        /// Warn and continue when a stdlib/local-dep .olean import fails to
        /// load, instead of failing the module build (fail-closed default)
        #[arg(long)]
        permissive_imports: bool,
    },
    /// Create a new project
    New {
        /// Project name
        name: String,
        /// Library template (default)
        #[arg(long)]
        lib: bool,
        /// Executable template
        #[arg(long, conflicts_with = "lib")]
        exe: bool,
    },
    /// clean build artifacts
    Clean {
        /// Show verbose output
        #[arg(short, long)]
        verbose: bool,
    },
    /// Initialize lake in current directory
    Init {
        /// Project name (defaults to directory name)
        name: Option<String>,
    },
    /// Fetch dependencies from git
    Fetch {
        /// Show verbose output
        #[arg(short, long)]
        verbose: bool,
    },
    /// Update dependencies to latest versions
    Update {
        /// Package to update (updates all if not specified)
        package: Option<String>,
        /// Show verbose output
        #[arg(short, long)]
        verbose: bool,
    },
    /// Show build environment information or run a command in it
    Env {
        /// Show verbose output
        #[arg(short, long)]
        verbose: bool,
        /// Command and arguments to run in the Lake environment. A Lean
        /// toolchain program (`lean`, `lake`, `leanchecker`, `leanexport`,
        /// `lean4export`, `leanc`, `leanir`, `leanmake`, `leanpkg`) is refused
        /// by name, naming the Clean verb to use instead
        #[arg(trailing_var_arg = true, allow_hyphen_values = true)]
        command: Vec<String>,
    },
    /// Run a Lean executable target
    Run {
        /// Executable target name (defaults to @\[default_target\], or the SINGLE
        /// declared executable; several executables with no default is refused,
        /// naming them)
        target: Option<String>,
        /// Arguments to pass to the executable
        #[arg(trailing_var_arg = true, allow_hyphen_values = true)]
        args: Vec<String>,
        /// Show verbose output
        #[arg(short, long)]
        verbose: bool,
        /// Number of parallel jobs for the build (0 = auto)
        #[arg(short, long, default_value = "0")]
        jobs: usize,
    },
    /// Resolve dependencies and update lake-manifest.json
    Resolve {
        /// Show verbose output
        #[arg(short, long)]
        verbose: bool,
        /// Don't modify lake-manifest.json, just show what would be resolved
        #[arg(long)]
        dry_run: bool,
    },
    /// Run a built native executable
    Exe {
        /// Executable name to run
        name: String,
        /// Arguments to pass to the executable
        #[arg(trailing_var_arg = true, allow_hyphen_values = true)]
        args: Vec<String>,
        /// Show verbose output
        #[arg(short, long)]
        verbose: bool,
    },
    /// Run tests
    Test {
        /// Test target to run (default: all tests)
        target: Option<String>,
        /// Arguments to pass to the test executable
        #[arg(trailing_var_arg = true, allow_hyphen_values = true)]
        args: Vec<String>,
        /// Show verbose output
        #[arg(short, long)]
        verbose: bool,
        /// Number of parallel jobs (0 = auto)
        #[arg(short, long, default_value = "0")]
        jobs: usize,
    },
    /// Start the Clean language server over stdio for this project
    /// (Lake-compatible editor entry point: editors launch `lake serve --`)
    Serve {
        /// Arguments forwarded by the editor after `--` (accepted for Lake
        /// CLI compatibility; the transport is always stdio)
        #[arg(trailing_var_arg = true, allow_hyphen_values = true)]
        args: Vec<String>,
    },
    /// Script commands
    #[command(subcommand)]
    Script(ScriptCommands),
    /// Cache commands for .olean files
    #[command(subcommand)]
    Cache(CacheCommands),
    /// Run linters on the project
    Lint {
        /// Target to lint (default: all targets)
        target: Option<String>,
        /// Show verbose output
        #[arg(short, long)]
        verbose: bool,
    },
    /// Check if build would succeed without building
    CheckBuild {
        /// Target to check (default: all targets)
        target: Option<String>,
        /// Show verbose output
        #[arg(short, long)]
        verbose: bool,
    },
    /// Check that the test targets resolve and ELABORATE, then list them —
    /// no test body is executed, so a test that would fail at runtime still
    /// passes this check
    CheckTest {
        /// Target to check (default: all tests)
        target: Option<String>,
        /// Show verbose output
        #[arg(short, long)]
        verbose: bool,
    },
    /// Check that the lint targets resolve and ELABORATE, then list them —
    /// the lint engine is not run and no lint finding is produced
    CheckLint {
        /// Target to check (default: all targets)
        target: Option<String>,
        /// Show verbose output
        #[arg(short, long)]
        verbose: bool,
    },
    /// Pack .olean files into a pack DIRECTORY (files + manifest.json) —
    /// no archive file is produced; the command prints the `tar` invocation
    /// to compress it yourself
    Pack {
        /// Output pack directory (created; not an archive file)
        #[arg(short, long)]
        output: Option<PathBuf>,
        /// Show verbose output
        #[arg(short, long)]
        verbose: bool,
    },
    /// Unpack .olean files from a pack DIRECTORY (as `pack` writes: files + manifest.json)
    Unpack {
        /// Input pack directory (a tarball must be extracted first)
        archive: PathBuf,
        /// Show verbose output
        #[arg(short, long)]
        verbose: bool,
    },
    /// NOT IMPLEMENTED — collects the artifact list, then refuses.
    ///
    /// With artifacts present, every non-`--dry-run` path ends in an error
    /// (TODO #421); a build directory holding no `.olean`/`.ilean` reports
    /// "No artifacts found to upload." and exits 0. Use `--dry-run` to list
    /// what would be sent.
    Upload {
        /// Show verbose output
        #[arg(short, long)]
        verbose: bool,
        /// Dry run - show what would be uploaded
        #[arg(long)]
        dry_run: bool,
    },
    /// Verify that built `.olean` artifacts are exactly what their current `.lean` source
    /// builds to: Cake's import signature AND byte-identity with a fresh scratch build.
    /// Fail-closed on a stale, rewritten or non-reproducible artifact.
    VerifyFresh {
        /// Project source root holding the `.lean` files (e.g. `crown-proofs/lean`).
        #[arg(long)]
        source_root: PathBuf,
        /// Modules to check (repeatable / comma-separated), e.g. `Crownproof`.
        #[arg(long, value_delimiter = ',')]
        module: Vec<String>,
        /// `.olean` search-path roots (repeatable). Defaults to
        /// `<source_root>/.lake/build/lib/lean`, then `<source_root>/.lake/build/lib`.
        #[arg(long)]
        olean_search_path: Vec<PathBuf>,
        /// Emit JSON instead of the human-readable report.
        #[arg(long)]
        json: bool,
    },
    /// Run the governed Lake replacement smoke: init/build/test the `clean lake
    /// init` template project in a throwaway temp directory, entirely through
    /// clean-owned in-process handlers (never Lean4), and write the JSON
    /// evidence artifact the lake-workflow replacement row names.
    Smoke {
        /// Path to write the JSON evidence artifact.
        #[arg(long, default_value = "reports/lake-replacement-smoke.json")]
        report: PathBuf,
        /// Show verbose output
        #[arg(short, long)]
        verbose: bool,
    },
    /// Report a constant's Cake profile: semantic identity (defeq + rewrite digests),
    /// proof goodness (G mass + F bedrock-distance floor), and complexity. Loads the
    /// `.olean` env, so this is the queryable "how good / how far from the 3 axioms" tool.
    Goodness {
        /// Lean modules to load (repeatable / comma-separated) — the env to query.
        #[arg(long, value_delimiter = ',')]
        module: Vec<String>,
        /// `.olean` search-path roots (repeatable).
        #[arg(long)]
        olean_search_path: Vec<PathBuf>,
        /// The constant to profile, e.g. `Crownproof.network_bridge`.
        #[arg(long)]
        constant: String,
        /// Emit JSON instead of the human-readable report.
        #[arg(long)]
        json: bool,
    },
}

/// Nested `lake script ...` subcommands.
#[derive(Debug, Subcommand)]
pub enum ScriptCommands {
    /// List available scripts
    List,
    /// Run a script
    Run {
        /// Script name
        name: String,
        /// Arguments to pass to the script
        #[arg(trailing_var_arg = true)]
        args: Vec<String>,
    },
    /// Show documentation for a script
    Doc {
        /// Script name
        name: String,
    },
}

/// Nested `lake cache ...` subcommands.
#[derive(Debug, Subcommand)]
pub enum CacheCommands {
    /// Report on the local cache; does NOT fetch anything.
    ///
    /// Prints the command to run (`clean lake exe cache get`) when a cache
    /// executable is present, and otherwise entry counts or setup advice. No
    /// file is downloaded, copied or unpacked on any path. The summary read
    /// "Get cached .olean files" until 2026-08-31.
    Get {
        /// Show verbose output
        #[arg(short, long)]
        verbose: bool,
    },
    /// Copy .olean files into the LOCAL `.lake/cache`. Not a cloud upload.
    Put {
        /// Show verbose output
        #[arg(short, long)]
        verbose: bool,
    },
    /// Add files to the local cache
    Add {
        /// Files to add (default: all built files)
        files: Vec<String>,
        /// Show verbose output
        #[arg(short, long)]
        verbose: bool,
    },
}

#[cfg(test)]
mod tests {
    use super::*;
    use clap::Parser;

    #[derive(Debug, Parser)]
    struct LakeTestCli {
        #[command(flatten)]
        lake: LakeArgs,
    }

    #[test]
    fn lake_run_forwards_hyphen_leading_args_after_target() {
        let cli = LakeTestCli::try_parse_from([
            "clean lake",
            "run",
            "demo",
            "-c",
            "printf '%s\\n' \"$1\"",
            "native-sh",
            "--literal-flag",
        ])
        .expect("parse lake run with forwarded flag-like args");

        match cli.lake.command {
            LakeCommands::Run {
                target,
                args,
                verbose,
                jobs,
            } => {
                assert_eq!(target.as_deref(), Some("demo"));
                assert_eq!(
                    args,
                    ["-c", "printf '%s\\n' \"$1\"", "native-sh", "--literal-flag"]
                );
                assert!(!verbose);
                assert_eq!(jobs, 0);
            }
            other => panic!("expected lake run, got {other:?}"),
        }
    }

    #[test]
    fn lake_exe_forwards_hyphen_leading_args_after_name() {
        let cli = LakeTestCli::try_parse_from([
            "clean lake",
            "exe",
            "demo",
            "-c",
            "printf '%s\\n' \"$1\"",
            "native-sh",
            "--literal-flag",
        ])
        .expect("parse lake exe with forwarded flag-like args");

        match cli.lake.command {
            LakeCommands::Exe {
                name,
                args,
                verbose,
            } => {
                assert_eq!(name, "demo");
                assert_eq!(
                    args,
                    ["-c", "printf '%s\\n' \"$1\"", "native-sh", "--literal-flag"]
                );
                assert!(!verbose);
            }
            other => panic!("expected lake exe, got {other:?}"),
        }
    }

    #[test]
    fn lake_test_forwards_hyphen_leading_args_after_target() {
        let cli = LakeTestCli::try_parse_from([
            "clean lake",
            "test",
            "demo",
            "-c",
            "printf '%s\\n' \"$1\"",
            "native-sh",
            "--literal-flag",
        ])
        .expect("parse lake test with forwarded flag-like args");

        match cli.lake.command {
            LakeCommands::Test {
                target,
                args,
                verbose,
                jobs,
            } => {
                assert_eq!(target.as_deref(), Some("demo"));
                assert_eq!(
                    args,
                    ["-c", "printf '%s\\n' \"$1\"", "native-sh", "--literal-flag"]
                );
                assert!(!verbose);
                assert_eq!(jobs, 0);
            }
            other => panic!("expected lake test, got {other:?}"),
        }
    }

    #[test]
    fn lake_serve_parses_bare_and_with_forwarded_editor_args() {
        let cli =
            LakeTestCli::try_parse_from(["clean lake", "serve"]).expect("parse bare lake serve");
        match cli.lake.command {
            LakeCommands::Serve { args } => {
                assert!(args.is_empty(), "bare serve should forward no args");
            }
            other => panic!("expected lake serve, got {other:?}"),
        }

        // The VS Code Lean 4 extension launches `lake serve -- <args>`; the
        // `--` escape and any flag-like args must be collected, not parsed
        // as clean flags.
        let cli = LakeTestCli::try_parse_from(["clean lake", "serve", "--", "--editor-flag"])
            .expect("parse lake serve with forwarded flag-like args");
        match cli.lake.command {
            LakeCommands::Serve { args } => assert_eq!(args, ["--editor-flag"]),
            other => panic!("expected lake serve, got {other:?}"),
        }
    }

    #[test]
    fn lake_env_forwards_hyphen_leading_command_args() {
        let cli = LakeTestCli::try_parse_from([
            "clean lake",
            "env",
            "/bin/sh",
            "-c",
            "printf '%s\\n' \"$1\"",
            "native-sh",
            "--literal-flag",
        ])
        .expect("parse lake env with command and flag-like args");

        match cli.lake.command {
            LakeCommands::Env { command, verbose } => {
                assert_eq!(
                    command,
                    [
                        "/bin/sh",
                        "-c",
                        "printf '%s\\n' \"$1\"",
                        "native-sh",
                        "--literal-flag"
                    ]
                );
                assert!(!verbose);
            }
            other => panic!("expected lake env, got {other:?}"),
        }
    }

    #[test]
    fn lake_env_verbose_without_command_stays_info_mode() {
        let cli = LakeTestCli::try_parse_from(["clean lake", "env", "--verbose"])
            .expect("parse lake env verbose info mode");

        match cli.lake.command {
            LakeCommands::Env { command, verbose } => {
                assert!(command.is_empty());
                assert!(verbose);
            }
            other => panic!("expected lake env, got {other:?}"),
        }
    }
}
