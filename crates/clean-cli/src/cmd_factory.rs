// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean factory ...` release health surfaces (#3706).

use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::process::Command;

use crate::factory::{DeclIndexArgs, MergeCheckArgs, QueueCommands, TheoremIndexArgs};
use clap::{Args, Subcommand};
use clean_features::{Category, Example, FeatureDescriptor, RefKind, Reference, Stability};
use serde::Serialize;

const CHECK_PASS: &str = "pass";
const CHECK_FAIL: &str = "fail";
const AY_REPO_URL: &str = "https://github.com/alabsystems/ay";

/// Verbs under `clean factory`.
#[derive(Debug, Clone, Subcommand)]
pub(crate) enum FactoryCommands {
    /// Emit the release health manifest used by factory launch gates.
    Status(FactoryStatusArgs),
    /// Print the AI operator guide for proof-factory work.
    Guide(FactoryGuideArgs),
    /// Build a Lean declaration index for merge-policy diagnostics.
    DeclIndex(DeclIndexArgs),
    /// Emit theorem candidates for proof-factory agents.
    TheoremIndex(TheoremIndexArgs),
    /// Check a candidate revision before it lands.
    MergeCheck(MergeCheckArgs),
    /// Rust-owned transactional merge queue.
    Queue {
        /// Queue subcommand.
        #[command(subcommand)]
        command: QueueCommands,
    },
}

/// Arguments accepted by `clean factory status`.
#[derive(Debug, Clone, Args)]
pub(crate) struct FactoryStatusArgs {
    /// Emit JSON instead of compact human-readable output.
    #[arg(long)]
    pub json: bool,
}

/// Arguments accepted by `clean factory guide`.
#[derive(Debug, Clone, Args)]
pub(crate) struct FactoryGuideArgs {
    /// Emit machine-readable JSON instead of Markdown.
    #[arg(long)]
    pub json: bool,
}

/// Errors surfaced by `clean factory`.
#[derive(Debug, thiserror::Error)]
pub(crate) enum FactoryError {
    /// Serializing the health manifest failed.
    #[error("failed to serialize factory status JSON: {0}")]
    Serialize(#[from] serde_json::Error),
    /// Writing output failed.
    #[error("failed to write factory status output: {0}")]
    Io(#[from] io::Error),
    /// A release-blocking health check failed.
    #[error("factory health check failed: {0}")]
    Health(String),
    /// Rust-owned factory operation failed.
    #[error(transparent)]
    Ops(#[from] crate::factory::FactoryOpsError),
}

/// Dispatch entry point for `clean factory`.
pub(crate) fn handle_factory_command(command: FactoryCommands) -> Result<(), FactoryError> {
    match command {
        FactoryCommands::Status(args) => run_status(args),
        FactoryCommands::Guide(args) => run_guide(args),
        FactoryCommands::DeclIndex(args) => {
            crate::factory::run_decl_index(args).map_err(Into::into)
        }
        FactoryCommands::TheoremIndex(args) => {
            crate::factory::run_theorem_index(args).map_err(Into::into)
        }
        FactoryCommands::MergeCheck(args) => {
            crate::factory::run_merge_check(args).map_err(Into::into)
        }
        FactoryCommands::Queue { command } => {
            crate::factory::run_queue_command(command).map_err(Into::into)
        }
    }
}

fn run_guide(args: FactoryGuideArgs) -> Result<(), FactoryError> {
    let guide = build_guide_report();
    let stdout = io::stdout();
    let mut out = stdout.lock();
    if args.json {
        writeln!(out, "{}", serde_json::to_string_pretty(&guide)?)?;
    } else {
        render_guide_human(&mut out, &guide)?;
    }
    Ok(())
}

fn run_status(args: FactoryStatusArgs) -> Result<(), FactoryError> {
    let report = build_status_report();

    let stdout = io::stdout();
    let mut out = stdout.lock();
    if args.json {
        writeln!(out, "{}", serde_json::to_string_pretty(&report)?)?;
    } else {
        render_human(&mut out, &report)?;
    }

    if report.summary.status == CHECK_FAIL {
        return Err(FactoryError::Health(report.failure_message()));
    }
    Ok(())
}

fn render_guide_human(out: &mut impl Write, guide: &FactoryGuideReport) -> io::Result<()> {
    writeln!(out, "# Clean AI Factory Guide")?;
    writeln!(out)?;
    writeln!(out, "{}", guide.purpose)?;
    writeln!(out)?;
    writeln!(out, "## Operator Loop")?;
    for (index, step) in guide.operator_loop.iter().enumerate() {
        writeln!(out, "{}. {}", index + 1, step)?;
    }
    writeln!(out)?;
    writeln!(out, "## Command Recipes")?;
    for command in &guide.commands {
        writeln!(out, "- `{}`: {}", command.cmd, command.why)?;
    }
    writeln!(out)?;
    writeln!(out, "## Use This For")?;
    for use_case in &guide.use_cases {
        writeln!(out, "- {}", use_case)?;
    }
    writeln!(out)?;
    writeln!(out, "## Still Missing")?;
    for gap in &guide.remaining_gaps {
        writeln!(out, "- {}", gap)?;
    }
    Ok(())
}

fn build_guide_report() -> FactoryGuideReport {
    FactoryGuideReport {
        schema_version: "clean-factory-guide-v1",
        purpose: "Practical command map for AI agents using clean as a proof factory: \
align the checkout, inspect health, index declarations, gate candidate merges, \
and route proof work through trust-visible Lean tooling.",
        operator_loop: vec![
            "Pull first: `git pull --ff-only` in the clean checkout before trusting local state.",
            "Run `clean factory guide` and `clean features --search factory` to rediscover the current factory surface.",
            "Use `clean factory status --json` as the release-health and ay-dependency freshness check.",
            "Use `clean factory theorem-index --root . --json` before splitting theorem work across agents.",
            "Use `clean factory merge-check --base main --candidate HEAD --json` before landing Lean-source changes.",
            "Use `clean factory queue ...` only for clean candidate refs that should be serialized through one landing path.",
            "For proof search, pair `clean server` interactive methods with `clean auto premise`, `cert_simp`, and `cert_mathverse`; never treat a suggestion as proof until the kernel/trust report accepts it.",
        ],
        commands: vec![
            GuideCommand {
                cmd: "clean factory status --json",
                why: "machine-readable health gate: tracked lockfile, git hygiene, Rust toolchain, sibling ay path, and ay pin freshness",
            },
            GuideCommand {
                cmd: "clean factory decl-index --root . --json",
                why: "batch declaration inventory with statement/type fingerprints and trust metadata for changed Lean source",
            },
            GuideCommand {
                cmd: "clean factory theorem-index --root . --json",
                why: "agent-facing theorem candidates with module/import metadata, stable fingerprints, symbol refs, and trust records",
            },
            GuideCommand {
                cmd: "clean math project hygiene --project <math-project.json> --json",
                why: "math-project promotion gate for manifest references, trust policy, artifact replay policy, and stable violation codes",
            },
            GuideCommand {
                cmd: "clean factory merge-check --base main --candidate HEAD --json",
                why: "clean-worktree merge policy check for declaration collisions, duplicate theorem statements, dirty-source attempts, new trust debt, and referenced math-project hygiene",
            },
            GuideCommand {
                cmd: "clean factory queue push <rev> --base main",
                why: "enqueue an already prepared candidate revision for serialized landing",
            },
            GuideCommand {
                cmd: "clean factory queue process-next --verify-cmd '<cmd>' --json",
                why: "validate the next candidate in a clean worktree, optionally run verification, and fast-forward with compare-and-swap",
            },
            GuideCommand {
                cmd: "clean auto premise --goal '<goal>' --top-k 20",
                why: "current lightweight theorem-search path for goal-shaped premise shortlists",
            },
            GuideCommand {
                cmd: "clean server --port 8080",
                why: "JSON-RPC surface for proof-state, tactic application, batch verification, premise selection, and certificate operations",
            },
        ],
        use_cases: vec![
            "Coordinating multiple AI agents that add Lean theorems without silently duplicating statements or theorem names.",
            "Auditing whether a Lean-source candidate is clean enough to merge before spending review time.",
            "Building ay SAT/PB proof libraries where candidate simplification, mathverse, and certificate checker lemmas must stay trust-visible.",
            "Producing structured evidence for launch/replacement claims instead of prose-only status reports.",
        ],
        remaining_gaps: vec![
            "The interactive proof-state API is not yet a productized typed v2 contract.",
            "SAT/PB certificate libraries still need concrete checked definitions and rewrite/theorem packs.",
            "The declaration index is batch-oriented; agents still need per-goal local-context theorem retrieval.",
        ],
    }
}

#[derive(Debug, Serialize)]
struct FactoryGuideReport {
    schema_version: &'static str,
    purpose: &'static str,
    operator_loop: Vec<&'static str>,
    commands: Vec<GuideCommand>,
    use_cases: Vec<&'static str>,
    remaining_gaps: Vec<&'static str>,
}

#[derive(Debug, Serialize)]
struct GuideCommand {
    cmd: &'static str,
    why: &'static str,
}

fn render_human(out: &mut impl Write, report: &FactoryStatusReport) -> io::Result<()> {
    writeln!(out, "summary: {}", report.summary.status)?;
    writeln!(
        out,
        "cargo_lock: {} ({})",
        report.checks.cargo_lock.status, report.checks.cargo_lock.message
    )?;
    writeln!(
        out,
        "git_gc_logs: {} ({})",
        report.checks.git_gc_logs.status, report.checks.git_gc_logs.message
    )?;
    writeln!(
        out,
        "local_toolchain: {} ({})",
        report.checks.local_toolchain.status, report.checks.local_toolchain.message
    )?;
    writeln!(
        out,
        "ay_path: {} ({})",
        report.checks.ay_path.status, report.checks.ay_path.message
    )?;
    writeln!(
        out,
        "ay_updates: {} ({})",
        report.checks.ay_updates.status, report.checks.ay_updates.message
    )?;
    Ok(())
}

fn build_status_report() -> FactoryStatusReport {
    let repo_root = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    let cargo_lock = check_cargo_lock(&repo_root);
    let git_gc_logs = check_git_gc_logs(&repo_root, None);
    let local_toolchain = check_local_toolchain();
    let ay_path = check_ay_path(&repo_root);
    let ay_updates = check_ay_updates(&repo_root);
    FactoryStatusReport::from_checks(
        cargo_lock,
        git_gc_logs,
        local_toolchain,
        ay_path,
        ay_updates,
    )
}

fn check_cargo_lock(repo_root: &Path) -> HealthCheck {
    let cargo_lock = repo_root.join("Cargo.lock");

    if cargo_lock.is_file() {
        HealthCheck::pass(format!("Cargo.lock present at {}", cargo_lock.display()))
    } else {
        HealthCheck::fail(format!(
            "missing Cargo.lock at {} (release lanes must use the tracked lockfile with --locked)",
            cargo_lock.display()
        ))
    }
}

// The SMT-solver sibling repo is `ay` (alabsystems/ay) and the
// workspace now path-depends on `../ay/crates/*` (the `ay*` Cargo keys are kept
// as aliases pointing at the `ay-*` packages). The serialized check keys stay
// `ay_path` / `ay_updates` for release-readiness contract stability
// (docs/RELEASE_READINESS.md), but the checks below operate on `../ay`.

fn check_ay_path(repo_root: &Path) -> HealthCheck {
    let ay_path = repo_root.parent().unwrap_or(repo_root).join("ay");

    if ay_path.is_dir() {
        HealthCheck::pass(format!(
            "../ay path dependency present at {}",
            ay_path.display()
        ))
    } else {
        HealthCheck::fail(format!(
            "missing ../ay path dependency at {} (see Cargo.toml ay* = {{ package = \"ay-*\", path = \"../ay/crates/ay-*\" }} entries)",
            ay_path.display()
        ))
    }
}

fn check_ay_updates(repo_root: &Path) -> HealthCheck {
    // `ay` is consumed as a path dependency, so there is no pinned git rev to
    // compare. Freshness instead means: is the local `../ay` checkout at the
    // same commit as the `ay` remote HEAD? A drifted checkout means Cargo.lock
    // may not reflect upstream and must be re-resolved before release.
    let ay_path = repo_root.parent().unwrap_or(repo_root).join("ay");
    if !ay_path.is_dir() {
        return HealthCheck::fail(format!(
            "ay update freshness: missing ../ay checkout at {}",
            ay_path.display()
        ));
    }

    let local_head = match ay_local_head(&ay_path) {
        Ok(rev) => rev,
        Err(message) => return HealthCheck::fail(format!("ay update freshness: {message}")),
    };
    let remote_head = match ay_remote_head() {
        Ok(rev) => rev,
        Err(message) => return HealthCheck::fail(format!("ay update freshness: {message}")),
    };

    if revs_match(&local_head, &remote_head) {
        HealthCheck::pass(format!(
            "ay dependency is up to date: local ../ay HEAD {local_head} matches remote HEAD {remote_head}"
        ))
    } else {
        HealthCheck::fail(format!(
            "ay dependency is stale: local ../ay HEAD {local_head}, remote HEAD {remote_head}; \
             pull ../ay and re-run `cargo update` so Cargo.lock matches before release"
        ))
    }
}

fn ay_local_head(ay_path: &Path) -> Result<String, String> {
    let output = Command::new("git")
        .arg("-C")
        .arg(ay_path)
        .args(["rev-parse", "HEAD"])
        .output()
        .map_err(|error| format!("git rev-parse for local ../ay HEAD failed to start: {error}"))?;

    if !output.status.success() {
        let text = String::from_utf8_lossy(&output.stderr).trim().to_owned();
        return Err(if text.is_empty() {
            format!(
                "git rev-parse for local ../ay HEAD exited with {}",
                output.status
            )
        } else {
            format!("git rev-parse for local ../ay HEAD failed: {text}")
        });
    }

    let head = String::from_utf8_lossy(&output.stdout).trim().to_owned();
    if head.is_empty() {
        return Err("git rev-parse for local ../ay HEAD returned no revision".to_owned());
    }
    Ok(head)
}

fn ay_remote_head() -> Result<String, String> {
    let output = Command::new("git")
        .args(["ls-remote", AY_REPO_URL, "HEAD"])
        .output()
        .map_err(|error| format!("git ls-remote for ay HEAD failed to start: {error}"))?;

    let text = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    )
    .trim()
    .to_owned();

    if !output.status.success() {
        return Err(if text.is_empty() {
            format!("git ls-remote for ay HEAD exited with {}", output.status)
        } else {
            format!("git ls-remote for ay HEAD failed: {text}")
        });
    }

    let head = text
        .lines()
        .filter_map(|line| {
            let mut parts = line.split_whitespace();
            let rev = parts.next()?;
            let reference = parts.next()?;
            if reference == "HEAD" {
                Some(rev.to_owned())
            } else {
                None
            }
        })
        .next();

    head.ok_or_else(|| "git ls-remote for ay HEAD returned no HEAD revision".to_owned())
}

fn revs_match(left: &str, right: &str) -> bool {
    left == right || left.starts_with(right) || right.starts_with(left)
}

fn check_local_toolchain() -> HealthCheck {
    local_toolchain_check_from_versions(command_version("rustc"), command_version("cargo"))
}

fn command_version(program: &str) -> Result<String, String> {
    let output = Command::new(program)
        .arg("--version")
        .output()
        .map_err(|error| format!("{program} not available: {error}"))?;

    let text = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    )
    .trim()
    .to_owned();

    if output.status.success() {
        if text.is_empty() {
            Ok(format!("{program} --version returned no output"))
        } else {
            Ok(text)
        }
    } else if text.is_empty() {
        Err(format!("{program} --version exited with {}", output.status))
    } else {
        Err(text)
    }
}

fn local_toolchain_check_from_versions(
    rustc: Result<String, String>,
    cargo: Result<String, String>,
) -> HealthCheck {
    let mut versions = Vec::new();
    let mut failures = Vec::new();

    match rustc {
        Ok(version) => versions.push(version),
        Err(message) => failures.push(format!("rustc --version failed: {message}")),
    }
    match cargo {
        Ok(version) => versions.push(version),
        Err(message) => failures.push(format!("cargo --version failed: {message}")),
    }

    if failures.is_empty() {
        HealthCheck::pass(format!(
            "local Rust toolchain available: {}",
            versions.join("; ")
        ))
    } else {
        HealthCheck::fail(format!(
            "local Rust toolchain unavailable: {}",
            failures.join("; ")
        ))
    }
}

fn check_git_gc_logs(repo_root: &Path, git_common_dir: Option<&Path>) -> HealthCheck {
    let git_common_dir = match git_common_dir {
        Some(path) => path.to_owned(),
        None => match resolve_git_common_dir(repo_root) {
            Ok(path) => path,
            Err(message) => {
                return HealthCheck::fail(format!("git gc logs: could not inspect: {message}"));
            }
        },
    };

    let gc_logs = find_git_gc_logs(&git_common_dir);
    if gc_logs.is_empty() {
        return HealthCheck::pass(format!(
            "git gc logs: none found under {} or {}",
            display_git_path(&(git_common_dir.join("gc.log")), &git_common_dir),
            display_git_path(&(git_common_dir.join("worktrees")), &git_common_dir)
        ));
    }

    let paths = gc_logs
        .iter()
        .map(|path| display_git_path(path, &git_common_dir))
        .collect::<Vec<_>>()
        .join(", ");
    HealthCheck::fail(format!(
        "git gc logs: stale git gc.log file(s) found: {paths}; \
         inspect the failed git gc output before removing them"
    ))
}

fn resolve_git_common_dir(repo_root: &Path) -> Result<PathBuf, String> {
    let output = Command::new("git")
        .args(["rev-parse", "--git-common-dir"])
        .current_dir(repo_root)
        .output()
        .map_err(|error| format!("git not available: {error}"))?;

    if !output.status.success() {
        let text = String::from_utf8_lossy(&output.stderr).trim().to_owned();
        return Err(if text.is_empty() {
            format!("git rev-parse exited with {}", output.status)
        } else {
            text
        });
    }

    let text = String::from_utf8_lossy(&output.stdout).trim().to_owned();
    if text.is_empty() {
        return Err("git rev-parse --git-common-dir returned no path".to_owned());
    }

    let path = PathBuf::from(text);
    let common_dir = if path.is_absolute() {
        path
    } else {
        repo_root.join(path)
    };
    Ok(common_dir)
}

fn find_git_gc_logs(git_common_dir: &Path) -> Vec<PathBuf> {
    let mut logs = Vec::new();
    let common_gc_log = git_common_dir.join("gc.log");
    if common_gc_log.is_file() {
        logs.push(common_gc_log);
    }

    let worktrees_dir = git_common_dir.join("worktrees");
    if let Ok(entries) = std::fs::read_dir(worktrees_dir) {
        for entry in entries.flatten() {
            let path = entry.path().join("gc.log");
            if path.is_file() {
                logs.push(path);
            }
        }
    }

    logs.sort();
    logs
}

fn display_git_path(path: &Path, git_common_dir: &Path) -> String {
    let base = if git_common_dir
        .file_name()
        .is_some_and(|name| name == ".git")
    {
        git_common_dir.parent().unwrap_or(git_common_dir)
    } else {
        git_common_dir
    };
    path.strip_prefix(base)
        .unwrap_or(path)
        .to_string_lossy()
        .into_owned()
}

#[derive(Debug, Clone, Serialize)]
struct FactoryStatusReport {
    schema_version: &'static str,
    summary: HealthSummary,
    checks: HealthChecks,
}

impl FactoryStatusReport {
    fn from_checks(
        cargo_lock: HealthCheck,
        git_gc_logs: HealthCheck,
        local_toolchain: HealthCheck,
        ay_path: HealthCheck,
        ay_updates: HealthCheck,
    ) -> Self {
        let summary = HealthSummary::from_checks([
            &cargo_lock,
            &git_gc_logs,
            &local_toolchain,
            &ay_path,
            &ay_updates,
        ]);
        Self {
            schema_version: "1.0",
            summary,
            checks: HealthChecks {
                cargo_lock,
                git_gc_logs,
                local_toolchain,
                ay_path,
                ay_updates,
            },
        }
    }

    fn failure_message(&self) -> String {
        let mut messages = Vec::new();
        if self.checks.cargo_lock.status == CHECK_FAIL {
            messages.push(self.checks.cargo_lock.message.as_str());
        }
        if self.checks.git_gc_logs.status == CHECK_FAIL {
            messages.push(self.checks.git_gc_logs.message.as_str());
        }
        if self.checks.local_toolchain.status == CHECK_FAIL {
            messages.push(self.checks.local_toolchain.message.as_str());
        }
        if self.checks.ay_path.status == CHECK_FAIL {
            messages.push(self.checks.ay_path.message.as_str());
        }
        if self.checks.ay_updates.status == CHECK_FAIL {
            messages.push(self.checks.ay_updates.message.as_str());
        }
        messages.join("; ")
    }
}

#[derive(Debug, Clone, Serialize)]
struct HealthSummary {
    status: &'static str,
    passed: usize,
    warnings: usize,
    errors: usize,
    skipped: usize,
}

impl HealthSummary {
    fn from_checks<'a>(checks: impl IntoIterator<Item = &'a HealthCheck>) -> Self {
        let mut passed = 0;
        let mut errors = 0;
        for check in checks {
            match check.status {
                CHECK_PASS => passed += 1,
                CHECK_FAIL => errors += 1,
                _ => {}
            }
        }
        let status = if errors == 0 { CHECK_PASS } else { CHECK_FAIL };
        Self {
            status,
            passed,
            warnings: 0,
            errors,
            skipped: 0,
        }
    }
}

#[derive(Debug, Clone, Serialize)]
struct HealthChecks {
    cargo_lock: HealthCheck,
    git_gc_logs: HealthCheck,
    local_toolchain: HealthCheck,
    ay_path: HealthCheck,
    ay_updates: HealthCheck,
}

#[derive(Debug, Clone, Serialize)]
struct HealthCheck {
    status: &'static str,
    message: String,
}

impl HealthCheck {
    fn pass(message: String) -> Self {
        Self {
            status: CHECK_PASS,
            message,
        }
    }

    fn fail(message: String) -> Self {
        Self {
            status: CHECK_FAIL,
            message,
        }
    }
}

/// Feature descriptors surfaced by `clean factory`.
pub(crate) const FEATURES: &[FeatureDescriptor] = &[FeatureDescriptor {
    path: &["factory", "guide"],
    summary: "Print the AI operator guide for proof-factory work (Experimental)",
    description: "\
Experimental concise operational guide for AI agents using clean as a proof \
factory. The guide names the current factory loop, command recipes, intended \
use cases, and remaining gaps so agents can rediscover how to use declaration \
indexing, merge checks, queue processing, proof-state methods, and theorem \
search without reading the source tree first. `--json` emits the same contract \
as structured data for orchestration tools.",
    category: Category::Dev,
    stability: Stability::Experimental,
    examples: &[
        Example {
            cmd: "clean factory guide",
            what: "print the Markdown quick-start guide for AI proof-factory operators",
        },
        Example {
            cmd: "clean factory guide --json",
            what: "emit the guide as a machine-readable JSON contract",
        },
    ],
    see_also: &["factory status", "factory decl-index", "factory merge-check", "factory queue"],
    references: &[
        Reference {
            kind: RefKind::Doc,
            label: "AI factory quick start",
            target: "README.md#ai-factory-quick-start",
        },
        Reference {
            kind: RefKind::Doc,
            label: "Interactive proof-state theorem-search API design",
            target: "designs/2026-04-27-interactive-proof-state-theorem-search-api.md",
        },
    ],
    domain_root: Some("factory"),
    alternative_forms: &[],
    feature_gate: None,
},
FeatureDescriptor {
    path: &["factory", "status"],
    summary: "Emit Rust-owned release health status for factory launch gates (Experimental)",
    description: "\
Experimental Rust-owned release health manifest for the #3706 system-health \
migration. The initial surface emits `schema_version`, `summary.status`, and \
`checks.cargo_lock.status`, `checks.git_gc_logs.status`, \
`checks.local_toolchain.status`, `checks.ay_path.status`, plus \
`checks.ay_updates.status` so release \
automation can begin moving away from `scripts/system_health_check.py` while \
remaining fail-closed for missing tracked lockfiles, stale Git \
garbage-collection logs, unavailable local Rust toolchains, a missing sibling \
`../ay` path-dependency checkout, or an `../ay` checkout whose HEAD has drifted \
from the `ay` remote.",
    category: Category::Dev,
    stability: Stability::Experimental,
    examples: &[
        Example {
            cmd: "clean factory status",
            what: "print a compact release health summary",
        },
        Example {
            cmd: "clean factory status --json",
            what: "emit the structured factory release health manifest",
        },
    ],
    see_also: &["replacement status"],
    references: &[
        Reference {
            kind: RefKind::Issue,
            label: "System-health Rust migration #3706",
            target: "#3706",
        },
        Reference {
            kind: RefKind::Crate,
            label: "clean-cli",
            target: "clean-cli",
        },
    ],
    domain_root: Some("factory"),
    alternative_forms: &[],
    feature_gate: None,
},
FeatureDescriptor {
    path: &["factory", "decl-index"],
    summary: "Build a Rust-owned Lean declaration index for merge-policy diagnostics (Experimental)",
    description: "\
Experimental Rust implementation of the Lean declaration index used by the #3704 \
transactional merge queue. The index parses changed Lean source, attempts \
kernel elaboration in a clean environment, fingerprints theorem statements, \
and emits diagnostics for parse/elaboration failures so merge policy can fail \
closed without Python-side state.",
    category: Category::Dev,
    stability: Stability::Experimental,
    examples: &[
        Example {
            cmd: "clean factory decl-index --root . --json",
            what: "emit a structured declaration index for the checkout",
        },
        Example {
            cmd: "clean factory decl-index --path tests/soundness_gate/accept/basic_identity_const.lean",
            what: "index a single Lean source file",
        },
    ],
    see_also: &["factory merge-check", "factory queue status"],
    references: &[
        Reference {
            kind: RefKind::Issue,
            label: "Transactional module and merge queue #3704",
            target: "#3704",
        },
        Reference {
            kind: RefKind::Crate,
            label: "clean-cli",
            target: "clean-cli",
        },
    ],
    domain_root: Some("factory"),
    alternative_forms: &[],
    feature_gate: None,
},
FeatureDescriptor {
    path: &["factory", "theorem-index"],
    summary: "Emit deterministic theorem candidates for proof-factory agents (Experimental)",
    description: "\
Experimental agent-facing theorem index derived from the Rust declaration index \
and source text. The command emits stable theorem-candidate JSON with module, \
import, source span, symbol reference, fingerprint, and trust metadata so \
proof-factory agents can shortlist existing facts without depending on an \
internal Rust-only model.",
    category: Category::Dev,
    stability: Stability::Experimental,
    examples: &[
        Example {
            cmd: "clean factory theorem-index --root . --json",
            what: "emit structured theorem candidates for the checkout",
        },
        Example {
            cmd: "clean factory theorem-index --path tests/soundness_gate/accept/basic_identity_const.lean --json",
            what: "emit theorem candidates for one Lean source file",
        },
    ],
    see_also: &["factory decl-index", "factory merge-check"],
    references: &[
        Reference {
            kind: RefKind::Issue,
            label: "Transactional module and merge queue #3704",
            target: "#3704",
        },
        Reference {
            kind: RefKind::Crate,
            label: "clean-cli",
            target: "clean-cli",
        },
    ],
    domain_root: Some("factory"),
    alternative_forms: &[],
    feature_gate: None,
},
FeatureDescriptor {
    path: &["factory", "merge-check"],
    summary: "Check a candidate Git revision in clean Lean-aware worktrees before landing (Experimental)",
    description: "\
Experimental Rust-owned merge gate for #3704. The command materializes detached base and \
candidate worktrees, indexes the changed Lean declaration set, detects \
theorem-name collisions, duplicate theorem statements, and dirty-source \
attempts, checks explicitly requested math projects plus candidate-touched \
math-project manifests/references through `clean math project hygiene`, then \
emits a structured accept/reject report. Unchanged unrelated math projects in \
the candidate tree are not implicit blockers.",
    category: Category::Dev,
    stability: Stability::Experimental,
    examples: &[
        Example {
            cmd: "clean factory merge-check --base main --candidate HEAD --json",
            what: "check HEAD against main and emit a structured report",
        },
    ],
    see_also: &["factory decl-index", "factory queue process-next"],
    references: &[
        Reference {
            kind: RefKind::Issue,
            label: "Transactional module and merge queue #3704",
            target: "#3704",
        },
        Reference {
            kind: RefKind::Crate,
            label: "clean-cli",
            target: "clean-cli",
        },
    ],
    domain_root: Some("factory"),
    alternative_forms: &[],
    feature_gate: None,
},
FeatureDescriptor {
    path: &["factory", "queue"],
    summary: "Manage the Rust-owned Lean-aware merge queue (Experimental)",
    description: "\
Rust queue surface for #3704. The queue stores durable JSON state, takes an \
exclusive lock while processing, validates the next candidate with \
`factory merge-check`, carries explicit math-project hygiene inputs into the \
candidate worktree, optionally runs a verification command in a clean worktree, \
and lands fast-forward candidates with Git update-ref compare-and-swap.",
    category: Category::Dev,
    stability: Stability::Experimental,
    examples: &[
        Example {
            cmd: "clean factory queue push feature-branch --base main",
            what: "enqueue a candidate revision",
        },
        Example {
            cmd: "clean factory queue status --json",
            what: "inspect queue state",
        },
        Example {
            cmd: "clean factory queue process-next --profile proof-factory",
            what: "validate and land the next ready candidate",
        },
    ],
    see_also: &[
        "factory queue push",
        "factory queue status",
        "factory queue process-next",
    ],
    references: &[
        Reference {
            kind: RefKind::Issue,
            label: "Transactional module and merge queue #3704",
            target: "#3704",
        },
        Reference {
            kind: RefKind::Crate,
            label: "clean-cli",
            target: "clean-cli",
        },
    ],
    domain_root: Some("factory"),
    alternative_forms: &[],
    feature_gate: None,
},
FeatureDescriptor {
    path: &["factory", "queue", "push"],
    summary: "Enqueue a Git revision in the Rust-owned merge queue (Experimental)",
    description: "\
Experimental Rust queue insertion for #3704. The command records a candidate \
revision, base ref, priority, and optional note in the durable queue state so \
`factory queue process-next` can validate and land it later.",
    category: Category::Dev,
    stability: Stability::Experimental,
    examples: &[Example {
        cmd: "clean factory queue push feature-branch --base main",
        what: "enqueue a candidate revision",
    }],
    see_also: &["factory queue status", "factory queue process-next"],
    references: &[
        Reference {
            kind: RefKind::Issue,
            label: "Transactional module and merge queue #3704",
            target: "#3704",
        },
        Reference {
            kind: RefKind::Crate,
            label: "clean-cli",
            target: "clean-cli",
        },
    ],
    domain_root: Some("factory"),
    alternative_forms: &[],
    feature_gate: None,
},
FeatureDescriptor {
    path: &["factory", "queue", "status"],
    summary: "Inspect Rust-owned merge queue state (Experimental)",
    description: "\
Experimental Rust queue status surface for #3704. The command reads the durable \
queue JSON state and emits either compact human output or structured JSON for \
automation.",
    category: Category::Dev,
    stability: Stability::Experimental,
    examples: &[Example {
        cmd: "clean factory queue status --json",
        what: "inspect queue state",
    }],
    see_also: &["factory queue push", "factory queue process-next"],
    references: &[
        Reference {
            kind: RefKind::Issue,
            label: "Transactional module and merge queue #3704",
            target: "#3704",
        },
        Reference {
            kind: RefKind::Crate,
            label: "clean-cli",
            target: "clean-cli",
        },
    ],
    domain_root: Some("factory"),
    alternative_forms: &[],
    feature_gate: None,
},
FeatureDescriptor {
    path: &["factory", "queue", "process-next"],
    summary: "Validate and land the next Rust-owned queue entry (Experimental)",
    description: "\
Experimental Rust queue processor for #3704. The command locks queue state, \
runs the Lean-aware merge check for the next ready entry in a clean candidate \
worktree, records math-project hygiene diagnostics for explicit or \
candidate-touched projects, optionally runs a verification command in that \
candidate worktree, and lands accepted entries with Git compare-and-swap \
semantics.",
    category: Category::Dev,
    stability: Stability::Experimental,
    examples: &[Example {
        cmd: "clean factory queue process-next --profile proof-factory",
        what: "validate and land the next ready candidate",
    }],
    see_also: &["factory queue status", "factory merge-check"],
    references: &[
        Reference {
            kind: RefKind::Issue,
            label: "Transactional module and merge queue #3704",
            target: "#3704",
        },
        Reference {
            kind: RefKind::Crate,
            label: "clean-cli",
            target: "clean-cli",
        },
    ],
    domain_root: Some("factory"),
    alternative_forms: &[],
    feature_gate: None,
}];

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::Value;

    #[test]
    fn cargo_lock_passes_when_lockfile_exists() {
        let dir = tempfile::tempdir().expect("tempdir");
        let cargo_lock = dir.path().join("Cargo.lock");
        std::fs::write(&cargo_lock, "# locked deps\n").expect("write Cargo.lock");

        let check = check_cargo_lock(dir.path());

        assert_eq!(check.status, CHECK_PASS);
        assert!(check.message.contains("Cargo.lock present"));
        assert!(check
            .message
            .contains(cargo_lock.display().to_string().as_str()));
    }

    #[test]
    fn cargo_lock_fails_closed_when_lockfile_is_missing() {
        let dir = tempfile::tempdir().expect("tempdir");

        let check = check_cargo_lock(dir.path());

        assert_eq!(check.status, CHECK_FAIL);
        assert!(check.message.contains("missing Cargo.lock"));
        assert!(check.message.contains("--locked"));
    }

    #[test]
    fn git_gc_logs_passes_when_no_gc_logs_exist() {
        let dir = tempfile::tempdir().expect("tempdir");
        let git_common_dir = dir.path().join(".git");
        std::fs::create_dir_all(git_common_dir.join("worktrees")).expect("mkdir");

        let check = check_git_gc_logs(dir.path(), Some(&git_common_dir));

        assert_eq!(check.status, CHECK_PASS);
        assert!(check.message.contains(".git/gc.log"));
        assert!(check.message.contains(".git/worktrees"));
    }

    #[test]
    fn git_gc_logs_fails_for_common_and_worktree_gc_logs() {
        let dir = tempfile::tempdir().expect("tempdir");
        let git_common_dir = dir.path().join(".git");
        let slot_dir = git_common_dir.join("worktrees").join("slot-a");
        std::fs::create_dir_all(&slot_dir).expect("mkdir");
        std::fs::write(git_common_dir.join("gc.log"), "failed gc\n").expect("write common");
        std::fs::write(slot_dir.join("gc.log"), "failed gc\n").expect("write worktree");

        let check = check_git_gc_logs(dir.path(), Some(&git_common_dir));

        assert_eq!(check.status, CHECK_FAIL);
        assert!(check.message.contains(".git/gc.log"));
        assert!(check.message.contains(".git/worktrees/slot-a/gc.log"));
        assert!(check.message.contains("inspect the failed git gc output"));
    }

    #[test]
    fn ay_path_passes_when_sibling_checkout_exists() {
        let workspace = tempfile::tempdir().expect("tempdir");
        let repo_root = workspace.path().join("clean");
        let ay_path = workspace.path().join("ay");
        std::fs::create_dir_all(&repo_root).expect("mkdir clean");
        std::fs::create_dir_all(&ay_path).expect("mkdir ay");

        let check = check_ay_path(&repo_root);

        assert_eq!(check.status, CHECK_PASS);
        assert!(check.message.contains("../ay path dependency present"));
        let ay_display = ay_path.display().to_string();
        assert!(check.message.contains(ay_display.as_str()));
    }

    #[test]
    fn ay_path_fails_closed_when_sibling_checkout_is_missing() {
        let workspace = tempfile::tempdir().expect("tempdir");
        let repo_root = workspace.path().join("clean");
        std::fs::create_dir_all(&repo_root).expect("mkdir clean");

        let check = check_ay_path(&repo_root);

        assert_eq!(check.status, CHECK_FAIL);
        assert!(check.message.contains("missing ../ay path dependency"));
        assert!(check.message.contains("../ay/crates/ay-*"));
    }

    #[test]
    fn local_toolchain_passes_when_rustc_and_cargo_versions_are_available() {
        let check = local_toolchain_check_from_versions(
            Ok("rustc 1.93.0".to_owned()),
            Ok("cargo 1.93.0".to_owned()),
        );

        assert_eq!(check.status, CHECK_PASS);
        assert!(check.message.contains("local Rust toolchain available"));
        assert!(check.message.contains("rustc 1.93.0"));
        assert!(check.message.contains("cargo 1.93.0"));
    }

    #[test]
    fn local_toolchain_fails_closed_when_rustc_or_cargo_is_missing() {
        let check = local_toolchain_check_from_versions(
            Err("rustc not available".to_owned()),
            Ok("cargo 1.93.0".to_owned()),
        );

        assert_eq!(check.status, CHECK_FAIL);
        assert!(check.message.contains("local Rust toolchain unavailable"));
        assert!(check.message.contains("rustc --version failed"));
        assert!(check.message.contains("rustc not available"));
        assert!(!check.message.contains("cargo --version failed"));
    }

    #[test]
    fn ay_updates_fails_closed_when_ay_checkout_is_missing() {
        // No `../ay` sibling next to the repo root -> freshness cannot be
        // determined (path deps have no pinned rev to compare), so the check
        // must fail closed rather than silently passing.
        let workspace = tempfile::tempdir().expect("tempdir");
        let repo_root = workspace.path().join("clean");
        std::fs::create_dir_all(&repo_root).expect("mkdir clean");

        let check = check_ay_updates(&repo_root);

        assert_eq!(check.status, CHECK_FAIL);
        assert!(check.message.contains("ay update freshness"));
        assert!(check.message.contains("missing ../ay checkout"));
    }

    #[test]
    fn revs_match_accepts_prefix_and_exact() {
        assert!(revs_match("abc123", "abc123"));
        // git ls-remote returns the full 40-char sha; `rev-parse HEAD` also
        // returns the full sha, but accept abbreviated-prefix matches too.
        assert!(revs_match("abc123def", "abc123"));
        assert!(revs_match("abc123", "abc123def"));
        assert!(!revs_match("abc123", "xyz789"));
    }

    #[test]
    fn guide_report_names_core_factory_commands() {
        let guide = build_guide_report();
        let commands: Vec<_> = guide.commands.iter().map(|entry| entry.cmd).collect();

        assert_eq!(guide.schema_version, "clean-factory-guide-v1");
        assert!(commands.contains(&"clean factory status --json"));
        assert!(commands.contains(&"clean factory decl-index --root . --json"));
        assert!(commands.contains(&"clean factory theorem-index --root . --json"));
        assert!(
            commands.contains(&"clean math project hygiene --project <math-project.json> --json")
        );
        assert!(commands.contains(&"clean factory merge-check --base main --candidate HEAD --json"));
        assert!(commands.contains(&"clean server --port 8080"));
        assert!(guide
            .remaining_gaps
            .iter()
            .any(|gap| gap.contains("proof-state API")));
    }

    #[test]
    fn status_report_serializes_required_shape() {
        let report = FactoryStatusReport::from_checks(
            HealthCheck::pass("Cargo.lock present".to_owned()),
            HealthCheck::pass(
                "git gc logs: none found under .git/gc.log or .git/worktrees".to_owned(),
            ),
            HealthCheck::pass("local Rust toolchain available".to_owned()),
            HealthCheck::pass("../ay path dependency present".to_owned()),
            HealthCheck::pass("ay dependency is up to date".to_owned()),
        );
        let value: Value = serde_json::to_value(report).expect("json");

        assert_eq!(value["schema_version"], "1.0");
        assert_eq!(value["summary"]["status"], CHECK_PASS);
        assert_eq!(value["summary"]["passed"], 5);
        assert_eq!(value["checks"]["cargo_lock"]["status"], CHECK_PASS);
        assert_eq!(value["checks"]["git_gc_logs"]["status"], CHECK_PASS);
        assert_eq!(value["checks"]["local_toolchain"]["status"], CHECK_PASS);
        assert_eq!(value["checks"]["ay_path"]["status"], CHECK_PASS);
        assert_eq!(value["checks"]["ay_updates"]["status"], CHECK_PASS);
    }

    #[test]
    fn status_report_fails_closed_when_ay_path_is_missing() {
        let report = FactoryStatusReport::from_checks(
            HealthCheck::pass("Cargo.lock present".to_owned()),
            HealthCheck::pass(
                "git gc logs: none found under .git/gc.log or .git/worktrees".to_owned(),
            ),
            HealthCheck::pass("local Rust toolchain available".to_owned()),
            HealthCheck::fail("missing ../ay path dependency".to_owned()),
            HealthCheck::pass("ay dependency is up to date".to_owned()),
        );
        let value: Value = serde_json::to_value(&report).expect("json");

        assert_eq!(value["summary"]["status"], CHECK_FAIL);
        assert_eq!(value["summary"]["errors"], 1);
        assert_eq!(value["checks"]["ay_path"]["status"], CHECK_FAIL);
        assert!(report.failure_message().contains("missing ../ay"));
    }

    #[test]
    fn status_report_fails_closed_when_cargo_lock_is_missing() {
        let report = FactoryStatusReport::from_checks(
            HealthCheck::fail("missing Cargo.lock".to_owned()),
            HealthCheck::pass(
                "git gc logs: none found under .git/gc.log or .git/worktrees".to_owned(),
            ),
            HealthCheck::pass("local Rust toolchain available".to_owned()),
            HealthCheck::pass("../ay path dependency present".to_owned()),
            HealthCheck::pass("ay dependency is up to date".to_owned()),
        );
        let value: Value = serde_json::to_value(&report).expect("json");

        assert_eq!(value["summary"]["status"], CHECK_FAIL);
        assert_eq!(value["summary"]["errors"], 1);
        assert_eq!(value["checks"]["cargo_lock"]["status"], CHECK_FAIL);
        assert!(report.failure_message().contains("missing Cargo.lock"));
    }

    #[test]
    fn status_report_fails_closed_when_local_toolchain_is_missing() {
        let report = FactoryStatusReport::from_checks(
            HealthCheck::pass("Cargo.lock present".to_owned()),
            HealthCheck::pass(
                "git gc logs: none found under .git/gc.log or .git/worktrees".to_owned(),
            ),
            HealthCheck::fail("local Rust toolchain unavailable".to_owned()),
            HealthCheck::pass("../ay path dependency present".to_owned()),
            HealthCheck::pass("ay dependency is up to date".to_owned()),
        );
        let value: Value = serde_json::to_value(&report).expect("json");

        assert_eq!(value["summary"]["status"], CHECK_FAIL);
        assert_eq!(value["summary"]["errors"], 1);
        assert_eq!(value["checks"]["local_toolchain"]["status"], CHECK_FAIL);
        assert!(report
            .failure_message()
            .contains("local Rust toolchain unavailable"));
    }

    #[test]
    fn status_report_fails_closed_when_ay_updates_are_stale() {
        let report = FactoryStatusReport::from_checks(
            HealthCheck::pass("Cargo.lock present".to_owned()),
            HealthCheck::pass(
                "git gc logs: none found under .git/gc.log or .git/worktrees".to_owned(),
            ),
            HealthCheck::pass("local Rust toolchain available".to_owned()),
            HealthCheck::pass("../ay path dependency present".to_owned()),
            HealthCheck::fail("ay dependency is stale".to_owned()),
        );
        let value: Value = serde_json::to_value(&report).expect("json");

        assert_eq!(value["summary"]["status"], CHECK_FAIL);
        assert_eq!(value["summary"]["errors"], 1);
        assert_eq!(value["checks"]["ay_updates"]["status"], CHECK_FAIL);
        assert!(report.failure_message().contains("ay dependency is stale"));
    }
}
