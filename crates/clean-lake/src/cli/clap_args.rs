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
        /// Command and arguments to run in the Lake environment
        #[arg(trailing_var_arg = true, allow_hyphen_values = true)]
        command: Vec<String>,
    },
    /// Run a Lean executable target
    Run {
        /// Executable target name (defaults to @\[default_target\] or first executable)
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
    /// Check if tests would pass without running
    CheckTest {
        /// Target to check (default: all tests)
        target: Option<String>,
        /// Show verbose output
        #[arg(short, long)]
        verbose: bool,
    },
    /// Check if linting would pass without running
    CheckLint {
        /// Target to check (default: all targets)
        target: Option<String>,
        /// Show verbose output
        #[arg(short, long)]
        verbose: bool,
    },
    /// Pack .olean files into an archive
    Pack {
        /// Output archive file
        #[arg(short, long)]
        output: Option<PathBuf>,
        /// Show verbose output
        #[arg(short, long)]
        verbose: bool,
    },
    /// Unpack .olean files from an archive
    Unpack {
        /// Input archive file
        archive: PathBuf,
        /// Show verbose output
        #[arg(short, long)]
        verbose: bool,
    },
    /// Upload build artifacts to Reservoir
    Upload {
        /// Show verbose output
        #[arg(short, long)]
        verbose: bool,
        /// Dry run - show what would be uploaded
        #[arg(long)]
        dry_run: bool,
    },
    /// Verify that built `.olean` artifacts are content-fresh vs their `.lean` source
    /// (Cake's content-hash freshness — the import-list signature). Fail-closed on stale.
    VerifyFresh {
        /// Project source root holding the `.lean` files (e.g. `crown-proofs/lean`).
        #[arg(long)]
        source_root: PathBuf,
        /// Modules to check (repeatable / comma-separated), e.g. `Crownproof`.
        #[arg(long, value_delimiter = ',')]
        module: Vec<String>,
        /// `.olean` search-path roots (repeatable). Defaults to
        /// `<source_root>/.lake/build/lib/lean`.
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
    /// Get cached .olean files
    Get {
        /// Show verbose output
        #[arg(short, long)]
        verbose: bool,
    },
    /// Upload .olean files to cache
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
