// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean axle` — a thin wrapper around Axiom Math's **AXLE** (the Axiom Lean
//! Engine) for drafting and sanity-checking Lean 4 + Mathlib source.
//!
//! # This is a developer aid, NOT a Clean verification gate
//!
//! AXLE is a **remote, closed, third-party** service hosted at
//! `axle.axiommath.ai`. Its `verify-proof` tool only "trusts the Lean
//! environment" it runs in — it is a server-side `lake`/`lean` check, not a
//! Clean-kernel re-derivation. Every output of `clean axle` is therefore
//! **advisory**: convenient for drafting, checking syntax, stripping proofs to
//! `sorry`, splitting declarations, or hunting counterexamples — but it carries
//! **no Clean trust label**. Anything that would count toward a trust claim must
//! still be re-checked by the Clean kernel, exactly as Mathverse import-trust is
//! *not* `KernelVerified` (see the Mathverse provenance docs).
//!
//! # How it works
//!
//! Clean never re-implements the AXLE HTTP API. `clean axle` shells out to the
//! upstream `axle` CLI (PyPI `axiom-axle`), which is a thin HTTP client. AXLE
//! runs **anonymously** (no API key required); an optional `AXLE_API_KEY` in the
//! ambient environment only raises the server-side concurrency cap and is passed
//! through untouched (never read or printed by Clean).
//!
//! # Wrapped tools
//!
//! - `check` — compile/type-check Lean source server-side.
//! - `verify` — verify a candidate proof against a sorried statement
//!   (`verify-proof`).
//! - `theorem2sorry` — strip theorem proofs to `sorry`.
//! - `extract-decls` — split a file into standalone per-declaration units with
//!   dependency analysis.
//! - `disprove` — search for a counterexample by proving the negation.
//!
//! Every subcommand takes one or two Lean source **file paths** (the `axle` CLI
//! reads the file content itself). `--environment` selects the hosted Lean +
//! Mathlib toolchain (default [`DEFAULT_ENVIRONMENT`]); `--json` forces JSON
//! output; `--dry-run` prints the `axle` invocation without any network call.

use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{anyhow, bail, Context};
use clap::{Args, Subcommand};
use clean_features::{Category, Example, FeatureDescriptor, RefKind, Reference, Stability};

use thiserror::Error;

/// The external `axle` CLI binary name (PyPI `axiom-axle`).
const AXLE_BIN: &str = "axle";
/// Default hosted Lean + Mathlib environment if `--environment` is not given.
const DEFAULT_ENVIRONMENT: &str = "lean-4.29.0";

/// Errors raised while preparing or running an `axle` invocation.
///
/// Network and server-side failures surface through the child process exit
/// status (mapped to [`AxleError::ToolFailed`]); these variants cover the
/// argument-shaping and spawn boundary that Clean owns.
#[derive(Debug, Error)]
pub(crate) enum AxleError {
    /// An input Lean file does not exist or is not a regular file.
    #[error("input file `{path}` does not exist or is not a readable file")]
    MissingInput {
        /// The offending path.
        path: String,
    },
    /// The `axle` CLI could not be spawned (not installed / not on `PATH`).
    #[error(
        "failed to spawn `{bin}` — install the AXLE CLI with `pip install axiom-axle` \
         and ensure it is on PATH ({source})"
    )]
    Spawn {
        /// The binary we tried to run.
        bin: String,
        /// The underlying I/O error.
        source: std::io::Error,
    },
    /// The `axle` CLI ran but exited non-zero (a tool/network/server error).
    #[error(
        "`{bin} {tool}` exited with {status} (this is an advisory AXLE check, not a Clean gate)"
    )]
    ToolFailed {
        /// The binary that ran.
        bin: String,
        /// The AXLE tool (subcommand) that failed.
        tool: String,
        /// A human-readable status (`status N` or `a signal`).
        status: String,
    },
}

/// Which AXLE tool to drive. Names mirror the user-facing `clean axle <tool>`
/// verbs; each maps to an upstream `axle` subcommand via [`AxleTool::cli_name`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum AxleTool {
    /// Compile/type-check Lean source (`axle check`).
    Check,
    /// Verify a candidate proof against a sorried statement (`axle verify-proof`).
    Verify,
    /// Replace theorem proofs with `sorry` (`axle theorem2sorry`).
    Theorem2Sorry,
    /// Split a file into per-declaration units (`axle extract-decls`).
    ExtractDecls,
    /// Counterexample search (`axle disprove`).
    Disprove,
}

impl AxleTool {
    /// The upstream `axle` subcommand name (kebab-case).
    fn cli_name(self) -> &'static str {
        match self {
            Self::Check => "check",
            Self::Verify => "verify-proof",
            Self::Theorem2Sorry => "theorem2sorry",
            Self::ExtractDecls => "extract-decls",
            Self::Disprove => "disprove",
        }
    }

    /// Short label used in status output.
    fn label(self) -> &'static str {
        match self {
            Self::Check => "check",
            Self::Verify => "verify",
            Self::Theorem2Sorry => "theorem2sorry",
            Self::ExtractDecls => "extract-decls",
            Self::Disprove => "disprove",
        }
    }
}

/// `clean axle <tool>` verb tree. Each leaf wraps one AXLE tool.
#[derive(Debug, Subcommand)]
pub(crate) enum AxleCommands {
    /// Compile/type-check Lean source server-side (advisory, not a Clean gate).
    Check(SingleFileArgs),
    /// Verify a candidate proof against a sorried statement (`verify_proof`).
    Verify(VerifyArgs),
    /// Strip theorem proofs to `sorry` for drafting goal skeletons.
    Theorem2Sorry(SingleFileArgs),
    /// Split a file into standalone per-declaration units + dependency analysis.
    ExtractDecls(ExtractDeclsArgs),
    /// Search for a counterexample by attempting to prove the negation.
    Disprove(SingleFileArgs),
}

/// Flags shared by every `clean axle` tool: the hosted environment, JSON
/// output, and the no-network dry run.
#[derive(Debug, Clone, Args)]
pub(crate) struct CommonAxleArgs {
    /// Hosted Lean + Mathlib environment (e.g. `lean-4.29.0`). List the
    /// available environments with `axle environments`.
    #[arg(long, value_name = "ENV", default_value = DEFAULT_ENVIRONMENT)]
    pub environment: String,
    /// Force JSON output from AXLE (passes `--json` to the `axle` CLI).
    #[arg(long)]
    pub json: bool,
    /// Print the `axle` invocation instead of running it. No network call.
    #[arg(long)]
    pub dry_run: bool,
}

/// Arguments for the single-input tools (`check`, `theorem2sorry`, `disprove`).
#[derive(Debug, Clone, Args)]
pub(crate) struct SingleFileArgs {
    /// Lean source file to send to AXLE.
    #[arg(value_name = "FILE.lean")]
    pub file: PathBuf,
    #[command(flatten)]
    pub common: CommonAxleArgs,
}

/// Arguments for `clean axle verify` (`verify-proof`): a sorried statement plus
/// a candidate proof.
#[derive(Debug, Clone, Args)]
pub(crate) struct VerifyArgs {
    /// Lean file with the sorried formal statement to verify against.
    #[arg(value_name = "STATEMENT.lean")]
    pub statement: PathBuf,
    /// Lean file with the candidate proof to validate.
    #[arg(value_name = "PROOF.lean")]
    pub proof: PathBuf,
    #[command(flatten)]
    pub common: CommonAxleArgs,
}

/// Arguments for `clean axle extract-decls`: one input file and an output dir.
#[derive(Debug, Clone, Args)]
pub(crate) struct ExtractDeclsArgs {
    /// Lean source file to split into per-declaration units.
    #[arg(value_name = "FILE.lean")]
    pub file: PathBuf,
    /// Directory to write the extracted per-declaration `.lean` files into.
    #[arg(long, value_name = "DIR", default_value = "extract_decls/")]
    pub output_dir: PathBuf,
    /// Overwrite existing files in the output directory.
    #[arg(long)]
    pub force: bool,
    #[command(flatten)]
    pub common: CommonAxleArgs,
}

/// A fully-built `axle` invocation: the program plus its argv, with the chosen
/// AXLE tool recorded for diagnostics.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct AxleInvocation {
    /// The program to spawn (`axle`).
    program: String,
    /// The full argv after the program name.
    args: Vec<String>,
    /// The AXLE tool this invocation drives (for error/status text).
    tool: AxleTool,
}

impl AxleInvocation {
    /// Render the invocation as a copy-pasteable shell line (for `--dry-run`).
    fn display_line(&self) -> String {
        format!("{} {}", self.program, self.args.join(" "))
    }
}

/// Top-level dispatcher for `clean axle`.
pub(crate) fn handle_axle_command(command: AxleCommands) -> anyhow::Result<()> {
    match command {
        AxleCommands::Check(args) => run_single(AxleTool::Check, &args),
        AxleCommands::Verify(args) => run_verify(&args),
        AxleCommands::Theorem2Sorry(args) => run_single(AxleTool::Theorem2Sorry, &args),
        AxleCommands::ExtractDecls(args) => run_extract_decls(&args),
        AxleCommands::Disprove(args) => run_single(AxleTool::Disprove, &args),
    }
}

/// Run one of the single-input tools (`check`, `theorem2sorry`, `disprove`).
fn run_single(tool: AxleTool, args: &SingleFileArgs) -> anyhow::Result<()> {
    if !args.common.dry_run {
        ensure_input(&args.file)?;
    }
    let inv = build_single_invocation(tool, &args.file, &args.common);
    dispatch(&inv, &args.common)
}

/// Run `clean axle verify` (`verify-proof`).
fn run_verify(args: &VerifyArgs) -> anyhow::Result<()> {
    if !args.common.dry_run {
        ensure_input(&args.statement)?;
        ensure_input(&args.proof)?;
    }
    let inv = build_verify_invocation(&args.statement, &args.proof, &args.common);
    dispatch(&inv, &args.common)
}

/// Run `clean axle extract-decls`.
fn run_extract_decls(args: &ExtractDeclsArgs) -> anyhow::Result<()> {
    if !args.common.dry_run {
        ensure_input(&args.file)?;
    }
    let inv = build_extract_decls_invocation(args);
    dispatch(&inv, &args.common)
}

/// Either print (dry run) or execute the built invocation.
fn dispatch(inv: &AxleInvocation, common: &CommonAxleArgs) -> anyhow::Result<()> {
    if common.dry_run {
        println!("[dry-run] would run: {}", inv.display_line());
        println!(
            "[dry-run] NOTE: AXLE is a remote, closed, third-party service. \
             Its result is advisory only — re-check anything trust-bearing with the Clean kernel."
        );
        return Ok(());
    }
    run_axle(inv).with_context(|| format!("running AXLE `{}`", inv.tool.label()))
}

/// Verify an input file exists before we shell out.
fn ensure_input(path: &Path) -> anyhow::Result<()> {
    if !path.is_file() {
        return Err(AxleError::MissingInput {
            path: path.display().to_string(),
        }
        .into());
    }
    Ok(())
}

/// Build the argv for a single-input tool.
///
/// Global flags (`--json`) precede the subcommand (argparse rule in the `axle`
/// CLI); per-tool flags (`--environment`) follow the subcommand, and the file
/// path is the trailing positional (the `axle` CLI reads its contents).
fn build_single_invocation(tool: AxleTool, file: &Path, common: &CommonAxleArgs) -> AxleInvocation {
    let mut args = global_flags(common);
    args.push(tool.cli_name().to_owned());
    push_environment(&mut args, common);
    args.push(file.display().to_string());
    AxleInvocation {
        program: AXLE_BIN.to_owned(),
        args,
        tool,
    }
}

/// Build the argv for `verify-proof` (two positionals: statement then proof).
fn build_verify_invocation(
    statement: &Path,
    proof: &Path,
    common: &CommonAxleArgs,
) -> AxleInvocation {
    let mut args = global_flags(common);
    args.push(AxleTool::Verify.cli_name().to_owned());
    push_environment(&mut args, common);
    args.push(statement.display().to_string());
    args.push(proof.display().to_string());
    AxleInvocation {
        program: AXLE_BIN.to_owned(),
        args,
        tool: AxleTool::Verify,
    }
}

/// Build the argv for `extract-decls` (file positional + `--output-dir`/`-f`).
fn build_extract_decls_invocation(args: &ExtractDeclsArgs) -> AxleInvocation {
    let mut argv = global_flags(&args.common);
    argv.push(AxleTool::ExtractDecls.cli_name().to_owned());
    push_environment(&mut argv, &args.common);
    argv.push("--output-dir".to_owned());
    argv.push(args.output_dir.display().to_string());
    if args.force {
        argv.push("--force".to_owned());
    }
    argv.push(args.file.display().to_string());
    AxleInvocation {
        program: AXLE_BIN.to_owned(),
        args: argv,
        tool: AxleTool::ExtractDecls,
    }
}

/// Leading global flags shared by every invocation (before the subcommand).
fn global_flags(common: &CommonAxleArgs) -> Vec<String> {
    let mut args = Vec::new();
    if common.json {
        args.push("--json".to_owned());
    }
    args
}

/// Append the required `--environment <env>` flag (after the subcommand).
fn push_environment(args: &mut Vec<String>, common: &CommonAxleArgs) {
    args.push("--environment".to_owned());
    args.push(common.environment.clone());
}

/// Spawn the `axle` CLI, inheriting stdio so the user sees live output.
///
/// `AXLE_API_KEY` (if set in the ambient environment) is inherited untouched —
/// Clean never reads or prints it. Authentication is optional; AXLE runs
/// anonymously.
fn run_axle(inv: &AxleInvocation) -> anyhow::Result<()> {
    println!(
        "Running AXLE `{}` (remote, advisory — NOT a Clean verification gate) …",
        inv.tool.label()
    );
    let status = Command::new(&inv.program)
        .args(&inv.args)
        .status()
        .map_err(|source| AxleError::Spawn {
            bin: inv.program.clone(),
            source,
        })?;
    if !status.success() {
        let status_text = status
            .code()
            .map_or_else(|| "a signal".to_owned(), |c| format!("status {c}"));
        return Err(AxleError::ToolFailed {
            bin: inv.program.clone(),
            tool: inv.tool.cli_name().to_owned(),
            status: status_text,
        }
        .into());
    }
    Ok(())
}

const AXLE_REF: Reference = Reference {
    kind: RefKind::Doc,
    label: "AXLE (Axiom Lean Engine) — remote Lean+Mathlib dev aid (advisory only)",
    target: "docs/cli/axle-check.md",
};

const CLI_CRATE_REF: Reference = Reference {
    kind: RefKind::Crate,
    label: "clean-cli",
    target: "clean-cli",
};

/// Shared dev-aid disclaimer woven into every descriptor description so the
/// "advisory, not a trust gate" framing is unmissable in `clean features` /
/// `clean help` / the generated docs.
///
/// Kept as a string-literal macro (not a `const &str`) because
/// `FeatureDescriptor::description` is a `&'static str` built with `concat!`,
/// and `concat!` only accepts literals — see [`axle_description!`].
macro_rules! dev_aid_note {
    () => {
        "\n\nDEVELOPER AID — NOT A CLEAN VERIFICATION GATE. AXLE is a remote, closed, \
third-party service (axle.axiommath.ai) whose checks only trust the hosted Lean \
environment, not the Clean kernel. Every result is ADVISORY: useful for drafting \
and sanity-checking Lean 4 + Mathlib, but it carries no Clean trust label. \
Anything trust-bearing must still be re-checked by the Clean kernel (same posture \
as Mathverse import-trust, which is NOT KernelVerified). Runs anonymously (no API \
key); an optional ambient AXLE_API_KEY only raises the concurrency cap and is \
passed through untouched. Requires internet access."
    };
}

/// Build a descriptor `description` literal: a per-tool body followed by the
/// shared [`dev_aid_note!`] disclaimer, concatenated at compile time.
macro_rules! axle_description {
    ($body:literal) => {
        concat!($body, dev_aid_note!())
    };
}

/// Feature descriptors surfaced by the `clean axle` verb tree (one per leaf).
pub(crate) const FEATURES: &[FeatureDescriptor] = &[
    FeatureDescriptor {
        path: &["axle", "check"],
        summary: "Type-check Lean source via AXLE (advisory dev aid, not a Clean gate)",
        description: axle_description!(
            "\
Compiles/type-checks a Lean 4 + Mathlib source FILE on Axiom Math's hosted AXLE \
service and reports all messages (errors, warnings, infos). Use it to sanity-check \
syntax or see `#check`/`#eval` output without a local Lean toolchain. The file is \
read by the `axle` CLI and sent to the chosen `--environment` (default lean-4.29.0)."
        ),
        category: Category::Dev,
        stability: Stability::Building,
        examples: &[
            Example {
                cmd: "clean axle check ./Demo.lean",
                what: "type-check Demo.lean against the default hosted Lean+Mathlib environment",
            },
            Example {
                cmd: "clean axle check ./Demo.lean --environment lean-4.29.0 --json",
                what: "type-check on a pinned environment with JSON output",
            },
            Example {
                cmd: "clean axle check ./Demo.lean --dry-run",
                what: "print the axle invocation without any network call",
            },
        ],
        see_also: &["axle verify", "axle theorem2sorry", "prove run"],
        references: &[AXLE_REF, CLI_CRATE_REF],
        domain_root: Some("axle"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["axle", "verify"],
        summary: "Verify a candidate Lean proof against a sorried statement via AXLE (advisory)",
        description: axle_description!(
            "\
Validates a candidate proof FILE against a sorried formal-statement FILE using \
AXLE's `verify_proof` tool, confirming the proof conforms to the stated theorem. \
The verification only trusts the hosted Lean environment — it is NOT a Clean-kernel \
derivation, so a passing result is advisory and must be re-checked by Clean before \
it can carry a trust claim."
        ),
        category: Category::Dev,
        stability: Stability::Building,
        examples: &[
            Example {
                cmd: "clean axle verify ./Statement.lean ./Proof.lean",
                what: "verify Proof.lean against the sorried statement in Statement.lean",
            },
            Example {
                cmd: "clean axle verify ./Statement.lean ./Proof.lean --json",
                what: "verify and emit the full AXLE result as JSON",
            },
        ],
        see_also: &["axle check", "prove run", "prove status"],
        references: &[AXLE_REF, CLI_CRATE_REF],
        domain_root: Some("axle"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["axle", "theorem2sorry"],
        summary: "Strip Lean theorem proofs to `sorry` via AXLE (drafting aid)",
        description: axle_description!(
            "\
Replaces the proofs of every theorem in a Lean source FILE with `sorry`, yielding \
a goal skeleton you can hand to a prover (e.g. `clean prove`) or fill in by hand. \
A drafting convenience that runs server-side on AXLE."
        ),
        category: Category::Dev,
        stability: Stability::Building,
        examples: &[
            Example {
                cmd: "clean axle theorem2sorry ./Theorems.lean",
                what: "print Theorems.lean with every theorem proof replaced by sorry",
            },
            Example {
                cmd: "clean axle theorem2sorry ./Theorems.lean --dry-run",
                what: "print the axle invocation without sending anything",
            },
        ],
        see_also: &["axle extract-decls", "axle check", "prove run"],
        references: &[AXLE_REF, CLI_CRATE_REF],
        domain_root: Some("axle"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["axle", "extract-decls"],
        summary: "Split a Lean file into per-declaration units via AXLE (dev aid)",
        description: axle_description!(
            "\
Splits a Lean source FILE into standalone per-declaration `.lean` units, each \
carrying the dependencies it needs, and writes them under `--output-dir` \
(default extract_decls/). Works for every declaration kind (def, theorem, lemma, \
abbrev, instance, structure, …). Useful for isolating a single goal before \
drafting or proving it."
        ),
        category: Category::Dev,
        stability: Stability::Building,
        examples: &[
            Example {
                cmd: "clean axle extract-decls ./Library.lean --output-dir ./decls",
                what: "split Library.lean into per-declaration files under ./decls",
            },
            Example {
                cmd: "clean axle extract-decls ./Library.lean --force",
                what: "overwrite any existing files in the default output directory",
            },
        ],
        see_also: &["axle theorem2sorry", "axle check"],
        references: &[AXLE_REF, CLI_CRATE_REF],
        domain_root: Some("axle"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["axle", "disprove"],
        summary: "Search for a counterexample to Lean theorems via AXLE (advisory)",
        description: axle_description!(
            "\
Attempts to DISPROVE the theorems in a Lean source FILE by proving their negation \
(a counterexample search). A positive result is a strong signal that a conjecture \
is false; like every AXLE output it is advisory and not a Clean trust judgement."
        ),
        category: Category::Dev,
        stability: Stability::Building,
        examples: &[
            Example {
                cmd: "clean axle disprove ./Conjecture.lean",
                what: "search for a counterexample to the theorems in Conjecture.lean",
            },
            Example {
                cmd: "clean axle disprove ./Conjecture.lean --json",
                what: "run the counterexample search and emit JSON",
            },
        ],
        see_also: &["axle check", "axle verify"],
        references: &[AXLE_REF, CLI_CRATE_REF],
        domain_root: Some("axle"),
        alternative_forms: &[],
        feature_gate: None,
    },
];

#[cfg(test)]
mod tests {
    use super::*;

    fn common(env: &str, json: bool, dry_run: bool) -> CommonAxleArgs {
        CommonAxleArgs {
            environment: env.to_owned(),
            json,
            dry_run,
        }
    }

    #[test]
    fn test_tool_cli_names_match_axle_subcommands() {
        assert_eq!(AxleTool::Check.cli_name(), "check");
        assert_eq!(AxleTool::Verify.cli_name(), "verify-proof");
        assert_eq!(AxleTool::Theorem2Sorry.cli_name(), "theorem2sorry");
        assert_eq!(AxleTool::ExtractDecls.cli_name(), "extract-decls");
        assert_eq!(AxleTool::Disprove.cli_name(), "disprove");
    }

    #[test]
    fn test_single_invocation_puts_json_before_subcommand_and_env_after() {
        let c = common("lean-4.29.0", true, false);
        let inv = build_single_invocation(AxleTool::Check, Path::new("/tmp/Demo.lean"), &c);
        assert_eq!(inv.program, "axle");
        // --json (global) must precede the subcommand.
        let json_idx = inv.args.iter().position(|a| a == "--json").expect("json");
        let cmd_idx = inv.args.iter().position(|a| a == "check").expect("check");
        assert!(json_idx < cmd_idx, "--json must precede the subcommand");
        // --environment must come after the subcommand, with its value.
        let env_idx = inv
            .args
            .iter()
            .position(|a| a == "--environment")
            .expect("environment flag");
        assert!(
            cmd_idx < env_idx,
            "--environment must follow the subcommand"
        );
        assert_eq!(inv.args[env_idx + 1], "lean-4.29.0");
        // The file path is the trailing positional.
        assert_eq!(inv.args.last().expect("file"), "/tmp/Demo.lean");
    }

    #[test]
    fn test_single_invocation_omits_json_by_default() {
        let c = common("lean-4.29.0", false, false);
        let inv = build_single_invocation(AxleTool::Disprove, Path::new("/tmp/C.lean"), &c);
        assert!(!inv.args.iter().any(|a| a == "--json"));
        assert_eq!(inv.args[0], "disprove");
    }

    #[test]
    fn test_verify_invocation_orders_statement_then_proof() {
        let c = common("lean-4.28.0", false, false);
        let inv = build_verify_invocation(
            Path::new("/tmp/Statement.lean"),
            Path::new("/tmp/Proof.lean"),
            &c,
        );
        assert_eq!(inv.tool, AxleTool::Verify);
        assert_eq!(inv.args[0], "verify-proof");
        // Two trailing positionals: statement, then proof.
        let n = inv.args.len();
        assert_eq!(inv.args[n - 2], "/tmp/Statement.lean");
        assert_eq!(inv.args[n - 1], "/tmp/Proof.lean");
        // Environment carried through.
        let env_idx = inv
            .args
            .iter()
            .position(|a| a == "--environment")
            .expect("env");
        assert_eq!(inv.args[env_idx + 1], "lean-4.28.0");
    }

    #[test]
    fn test_extract_decls_invocation_carries_output_dir_and_force() {
        let args = ExtractDeclsArgs {
            file: PathBuf::from("/tmp/Lib.lean"),
            output_dir: PathBuf::from("/tmp/out"),
            force: true,
            common: common("lean-4.29.0", false, false),
        };
        let inv = build_extract_decls_invocation(&args);
        assert_eq!(inv.args[0], "extract-decls");
        let od_idx = inv
            .args
            .iter()
            .position(|a| a == "--output-dir")
            .expect("output-dir");
        assert_eq!(inv.args[od_idx + 1], "/tmp/out");
        assert!(inv.args.iter().any(|a| a == "--force"));
        assert_eq!(inv.args.last().expect("file"), "/tmp/Lib.lean");
    }

    #[test]
    fn test_extract_decls_omits_force_when_unset() {
        let args = ExtractDeclsArgs {
            file: PathBuf::from("/tmp/Lib.lean"),
            output_dir: PathBuf::from("extract_decls/"),
            force: false,
            common: common("lean-4.29.0", false, false),
        };
        let inv = build_extract_decls_invocation(&args);
        assert!(!inv.args.iter().any(|a| a == "--force"));
    }

    #[test]
    fn test_display_line_is_copy_pasteable() {
        let c = common("lean-4.29.0", false, true);
        let inv = build_single_invocation(AxleTool::Check, Path::new("/tmp/Demo.lean"), &c);
        let line = inv.display_line();
        assert!(line.starts_with("axle check --environment lean-4.29.0 "));
        assert!(line.ends_with("/tmp/Demo.lean"));
    }

    #[test]
    fn test_ensure_input_rejects_missing_file() {
        let err = ensure_input(Path::new("/definitely/not/here-xyz.lean"))
            .expect_err("missing file must error");
        assert!(err.to_string().contains("does not exist"));
    }

    #[test]
    fn test_ensure_input_accepts_existing_file() {
        let dir = tempfile::tempdir().expect("tempdir");
        let f = dir.path().join("ok.lean");
        std::fs::write(&f, "import Mathlib\n").expect("write");
        ensure_input(&f).expect("existing file accepted");
    }

    #[test]
    fn test_descriptions_carry_dev_aid_disclaimer() {
        for d in FEATURES {
            assert!(
                d.description.contains("NOT A CLEAN VERIFICATION GATE"),
                "descriptor {:?} must carry the dev-aid disclaimer",
                d.path
            );
            assert!(
                d.description.contains("advisory") || d.description.contains("ADVISORY"),
                "descriptor {:?} must say its output is advisory",
                d.path
            );
        }
    }

    #[test]
    fn test_features_have_unique_paths_and_examples() {
        use clean_features::{ensure_has_example, ensure_unique_paths};
        let descriptors: Vec<&FeatureDescriptor> = FEATURES.iter().collect();
        ensure_unique_paths(&descriptors).expect("axle descriptor paths are unique");
        for d in FEATURES {
            ensure_has_example(d).expect("every axle descriptor has an example");
        }
        assert_eq!(FEATURES.len(), 5);
    }
}
