// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Top-level `mathverse` CLI built on `clap` derive API.
//!
//! This module owns the declarative subcommand surface. Each variant of
//! [`Command`] carries the remaining raw tokens (positional + flag) for its
//! subcommand; the existing hand-rolled flag parsers in
//! `commands::*` consume those tokens unchanged so behavior of individual
//! subcommands is unaffected by the migration (#3472).
//!
//! New surface:
//! - `mathverse --help` / `-h`  — lists subcommands via clap.
//! - `mathverse --version` / `-V` — clap-emitted version string (delegates to the
//!   legacy `version` command when invoked as `mathverse version`).
//! - `mathverse completion <shell>` — emits shell completion scripts via
//!   `clap_complete`.

use std::io;

use clap::{CommandFactory, Parser, Subcommand};
use clap_complete::{generate, Shell};

use crate::commands;

/// Top-level CLI parsed via clap.
#[derive(Parser, Debug)]
#[command(
    name = "mathverse",
    version,
    about = "Mathverse Library CLI — search, browse, inspect, and manage",
    long_about = "Mathverse Library CLI — unified search and management for the\n\
                  verified mathematics corpus. Supports name/semantic search,\n\
                  tag-based discovery, dependency graphs, shard inspection,\n\
                  diffing, sampling, verification, export and release tooling.",
    disable_help_subcommand = true
)]
pub(crate) struct Cli {
    #[command(subcommand)]
    pub command: Command,
}

impl Cli {
    /// Parse process args. Exits with a clap-formatted error on failure.
    pub fn parse_args() -> Self {
        <Self as Parser>::parse()
    }

    /// Parse from an explicit iterator. Used in tests.
    #[cfg(test)]
    pub fn try_parse_from<I, T>(iter: I) -> Result<Self, clap::Error>
    where
        I: IntoIterator<Item = T>,
        T: Into<std::ffi::OsString> + Clone,
    {
        <Self as Parser>::try_parse_from(iter)
    }
}

/// Subcommands. Each variant carries its own trailing argv so the existing
/// per-subcommand flag parsers remain the source of truth for flag behavior.
#[derive(Subcommand, Debug)]
pub(crate) enum Command {
    /// Search declarations by name (fuzzy, exact, semantic, or explain).
    Search {
        /// Remaining arguments forwarded to the search handler.
        #[arg(trailing_var_arg = true, allow_hyphen_values = true)]
        args: Vec<String>,
    },
    /// Unified search (name, tags, similar, cross-system).
    Find {
        #[arg(trailing_var_arg = true, allow_hyphen_values = true)]
        args: Vec<String>,
    },
    /// Show full metadata for a declaration.
    #[command(alias = "show")]
    Inspect {
        #[arg(trailing_var_arg = true, allow_hyphen_values = true)]
        args: Vec<String>,
    },
    /// List declarations with filters.
    List {
        #[arg(trailing_var_arg = true, allow_hyphen_values = true)]
        args: Vec<String>,
    },
    /// Library statistics.
    Stats {
        #[arg(trailing_var_arg = true, allow_hyphen_values = true)]
        args: Vec<String>,
    },
    /// List source systems with counts.
    Systems {
        #[arg(trailing_var_arg = true, allow_hyphen_values = true)]
        args: Vec<String>,
    },
    /// Cross-system knowledge graph (search/overlap/stats).
    Graph {
        #[arg(trailing_var_arg = true, allow_hyphen_values = true)]
        args: Vec<String>,
    },
    /// Transitive dependency graph.
    Deps {
        #[arg(trailing_var_arg = true, allow_hyphen_values = true)]
        args: Vec<String>,
    },
    /// Reverse dependencies: declarations that USE a target (alias for
    /// `deps --reverse`), ranked by impact.
    Uses {
        #[arg(trailing_var_arg = true, allow_hyphen_values = true)]
        args: Vec<String>,
    },
    /// Deterministic sample of declarations.
    Sample {
        #[arg(trailing_var_arg = true, allow_hyphen_values = true)]
        args: Vec<String>,
    },
    /// Symmetric diff of two `.mathverse` shards by name.
    Diff {
        #[arg(trailing_var_arg = true, allow_hyphen_values = true)]
        args: Vec<String>,
    },
    /// Verify a shard directory or release.
    Verify {
        #[arg(trailing_var_arg = true, allow_hyphen_values = true)]
        args: Vec<String>,
    },
    /// Download a corpus from a release (default) or a server (`--from <url>`).
    Download {
        #[arg(trailing_var_arg = true, allow_hyphen_values = true)]
        args: Vec<String>,
    },
    /// Publish a local corpus: `upload <dir> --to release:|gcs:|server: --version <V>`.
    Upload {
        #[arg(trailing_var_arg = true, allow_hyphen_values = true)]
        args: Vec<String>,
    },
    /// Serve a local Core: `serve [--core <dir>] [--port N] [--download-base <url>]`.
    Serve {
        #[arg(trailing_var_arg = true, allow_hyphen_values = true)]
        args: Vec<String>,
    },
    /// Export library data (clean-native, arxiv, all).
    Export {
        #[arg(trailing_var_arg = true, allow_hyphen_values = true)]
        args: Vec<String>,
    },
    /// Manage releases (build, package, verify, download, info).
    Release {
        #[arg(trailing_var_arg = true, allow_hyphen_values = true)]
        args: Vec<String>,
    },
    /// Show version and library summary.
    Version {
        #[arg(trailing_var_arg = true, allow_hyphen_values = true)]
        args: Vec<String>,
    },
    /// Generate shell completion script.
    ///
    /// Example: `mathverse completion bash > _mathverse`.
    Completion {
        /// Target shell.
        #[arg(value_enum)]
        shell: Shell,
    },
}

/// Execute the parsed command.
pub(crate) fn dispatch(cli: Cli) {
    match cli.command {
        Command::Search { args } => commands::cmd_search(&args),
        Command::Find { args } => commands::cmd_find(&args),
        Command::Inspect { args } => commands::cmd_inspect(&args),
        Command::List { args } => {
            // The legacy `list` handler expects its own subcommand token at
            // position 0 (it dispatches on `args[0]` internally when invoked
            // from `main.rs` via `&args[1..]`). To keep its surface identical
            // we prepend the "list" literal so it sees `[list, <flags>...]`.
            let mut full = Vec::with_capacity(args.len() + 1);
            full.push(String::from("list"));
            full.extend(args);
            commands::cmd_list(&full);
        }
        Command::Stats { args } => commands::cmd_stats(&args),
        Command::Systems { args } => commands::cmd_systems(&args),
        Command::Graph { args } => commands::cmd_graph(&args),
        Command::Deps { args } => commands::cmd_deps(&args),
        Command::Uses { args } => commands::cmd_uses(&args),
        Command::Sample { args } => commands::cmd_sample(&args),
        Command::Diff { args } => commands::cmd_diff(&args),
        Command::Verify { args } => commands::cmd_verify(&args),
        Command::Download { args } => commands::cmd_download(&args),
        Command::Upload { args } => commands::cmd_upload(&args),
        Command::Serve { args } => commands::cmd_serve(&args),
        Command::Export { args } => commands::cmd_export(&args),
        Command::Release { args } => commands::cmd_release(&args),
        Command::Version { args } => commands::cmd_version(&args),
        Command::Completion { shell } => emit_completion(shell),
    }
}

/// Render a `clap_complete` completion script for `shell` to stdout.
pub(crate) fn emit_completion(shell: Shell) {
    let mut cmd = <Cli as CommandFactory>::command();
    let bin = cmd.get_name().to_string();
    generate(shell, &mut cmd, bin, &mut io::stdout());
}

/// Render a completion script into a user-supplied writer. Used in tests so
/// we can assert non-empty output without spawning a subprocess.
#[cfg(test)]
pub(crate) fn render_completion<W: io::Write>(shell: Shell, out: &mut W) {
    let mut cmd = <Cli as CommandFactory>::command();
    let bin = cmd.get_name().to_string();
    generate(shell, &mut cmd, bin, out);
}

#[cfg(test)]
mod tests {
    use super::*;

    // ------------------------------------------------------------------
    // Subcommand parse tests — one per subcommand, including `show` alias.
    // These assert that clap dispatches to the correct `Command` variant
    // and that trailing argv is preserved verbatim for the legacy handler.
    // ------------------------------------------------------------------

    fn parse(argv: &[&str]) -> Command {
        Cli::try_parse_from(argv)
            .unwrap_or_else(|e| panic!("parse failed for {argv:?}: {e}"))
            .command
    }

    #[test]
    fn test_cli_search_parses_and_forwards_args() {
        match parse(&["mathverse", "search", "Nat.add", "--exact", "--limit", "5"]) {
            Command::Search { args } => {
                assert_eq!(
                    args,
                    vec![
                        "Nat.add".to_string(),
                        "--exact".to_string(),
                        "--limit".to_string(),
                        "5".to_string()
                    ]
                );
            }
            other => panic!("expected Search, got {other:?}"),
        }
    }

    #[test]
    fn test_cli_find_parses() {
        match parse(&["mathverse", "find", "--tag", "arith"]) {
            Command::Find { args } => {
                assert_eq!(args, vec!["--tag".to_string(), "arith".to_string()]);
            }
            other => panic!("expected Find, got {other:?}"),
        }
    }

    #[test]
    fn test_cli_inspect_parses() {
        match parse(&["mathverse", "inspect", "Nat.succ"]) {
            Command::Inspect { args } => {
                assert_eq!(args, vec!["Nat.succ".to_string()]);
            }
            other => panic!("expected Inspect, got {other:?}"),
        }
    }

    #[test]
    fn test_cli_show_is_alias_of_inspect() {
        // The `show` surface is declared as a clap alias of `inspect`, so it
        // must parse into Command::Inspect (not a separate variant).
        match parse(&["mathverse", "show", "Nat.succ"]) {
            Command::Inspect { args } => {
                assert_eq!(args, vec!["Nat.succ".to_string()]);
            }
            other => panic!("expected Inspect (via `show` alias), got {other:?}"),
        }
    }

    #[test]
    fn test_cli_list_parses() {
        match parse(&["mathverse", "list", "--limit", "3"]) {
            Command::List { args } => {
                assert_eq!(args, vec!["--limit".to_string(), "3".to_string()]);
            }
            other => panic!("expected List, got {other:?}"),
        }
    }

    #[test]
    fn test_cli_stats_parses() {
        assert!(matches!(
            parse(&["mathverse", "stats"]),
            Command::Stats { .. }
        ));
    }

    #[test]
    fn test_cli_systems_parses() {
        assert!(matches!(
            parse(&["mathverse", "systems"]),
            Command::Systems { .. }
        ));
    }

    #[test]
    fn test_cli_graph_parses_subcommand_token() {
        match parse(&["mathverse", "graph", "stats"]) {
            Command::Graph { args } => {
                assert_eq!(args, vec!["stats".to_string()]);
            }
            other => panic!("expected Graph, got {other:?}"),
        }
    }

    #[test]
    fn test_cli_deps_parses() {
        match parse(&["mathverse", "deps", "Nat.add", "--transitive"]) {
            Command::Deps { args } => {
                assert_eq!(
                    args,
                    vec!["Nat.add".to_string(), "--transitive".to_string()]
                );
            }
            other => panic!("expected Deps, got {other:?}"),
        }
    }

    #[test]
    fn test_cli_sample_parses() {
        match parse(&["mathverse", "sample", "--n", "10"]) {
            Command::Sample { args } => {
                assert_eq!(args, vec!["--n".to_string(), "10".to_string()]);
            }
            other => panic!("expected Sample, got {other:?}"),
        }
    }

    #[test]
    fn test_cli_diff_parses() {
        match parse(&["mathverse", "diff", "a.mathverse", "b.mathverse"]) {
            Command::Diff { args } => {
                assert_eq!(
                    args,
                    vec!["a.mathverse".to_string(), "b.mathverse".to_string()]
                );
            }
            other => panic!("expected Diff, got {other:?}"),
        }
    }

    #[test]
    fn test_cli_verify_parses() {
        match parse(&["mathverse", "verify", "data/mathverse-library"]) {
            Command::Verify { args } => {
                assert_eq!(args, vec!["data/mathverse-library".to_string()]);
            }
            other => panic!("expected Verify, got {other:?}"),
        }
    }

    #[test]
    fn test_cli_download_parses() {
        match parse(&["mathverse", "download", "--force"]) {
            Command::Download { args } => {
                assert_eq!(args, vec!["--force".to_string()]);
            }
            other => panic!("expected Download, got {other:?}"),
        }
    }

    #[test]
    fn test_cli_export_parses() {
        match parse(&["mathverse", "export", "arxiv"]) {
            Command::Export { args } => {
                assert_eq!(args, vec!["arxiv".to_string()]);
            }
            other => panic!("expected Export, got {other:?}"),
        }
    }

    #[test]
    fn test_cli_release_parses() {
        match parse(&["mathverse", "release", "info"]) {
            Command::Release { args } => {
                assert_eq!(args, vec!["info".to_string()]);
            }
            other => panic!("expected Release, got {other:?}"),
        }
    }

    #[test]
    fn test_cli_version_parses() {
        assert!(matches!(
            parse(&["mathverse", "version"]),
            Command::Version { .. }
        ));
    }

    #[test]
    fn test_cli_completion_parses_bash() {
        match parse(&["mathverse", "completion", "bash"]) {
            Command::Completion { shell } => {
                assert_eq!(shell, Shell::Bash);
            }
            other => panic!("expected Completion, got {other:?}"),
        }
    }

    #[test]
    fn test_cli_completion_rejects_unknown_shell() {
        // clap's derived `ValueEnum` rejects unknown variants with a parse
        // error; ensure we do not silently dispatch something else.
        let err = Cli::try_parse_from(["mathverse", "completion", "tcsh"])
            .expect_err("unknown shell must be rejected");
        let msg = err.to_string();
        assert!(
            msg.to_lowercase().contains("tcsh") || msg.to_lowercase().contains("invalid value"),
            "error message should mention bad shell value: {msg}"
        );
    }

    #[test]
    fn test_cli_unknown_subcommand_rejected() {
        let err = Cli::try_parse_from(["mathverse", "nope"])
            .expect_err("unknown subcommand must be rejected");
        assert!(
            err.to_string().to_lowercase().contains("nope")
                || err.kind() == clap::error::ErrorKind::InvalidSubcommand
                || err.kind() == clap::error::ErrorKind::UnknownArgument
        );
    }

    // ------------------------------------------------------------------
    // Completion generation — acceptance criterion:
    // `mathverse completion bash > _mathverse` yields a non-empty script.
    // ------------------------------------------------------------------

    #[test]
    fn test_completion_bash_is_non_empty_and_mentions_subcommands() {
        let mut out = Vec::<u8>::new();
        render_completion(Shell::Bash, &mut out);
        assert!(!out.is_empty(), "bash completion output must be non-empty");
        let text = String::from_utf8(out).expect("completion output is utf-8");
        // Bash completion scripts emitted by clap_complete reference the
        // binary name and subcommand tokens. Assert on a stable anchor
        // ('mathverse') plus at least one declared subcommand.
        assert!(
            text.contains("mathverse"),
            "completion must reference bin name"
        );
        assert!(
            text.contains("search") || text.contains("inspect") || text.contains("completion"),
            "completion must reference at least one subcommand token"
        );
    }

    #[test]
    fn test_completion_zsh_is_non_empty() {
        let mut out = Vec::<u8>::new();
        render_completion(Shell::Zsh, &mut out);
        assert!(!out.is_empty(), "zsh completion output must be non-empty");
    }

    #[test]
    fn test_completion_fish_is_non_empty() {
        let mut out = Vec::<u8>::new();
        render_completion(Shell::Fish, &mut out);
        assert!(!out.is_empty(), "fish completion output must be non-empty");
    }
}
