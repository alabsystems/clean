// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean prove` — submit a Lean goal to a remote/automated prover backend,
//! retrieve the candidate proof, and **verify it locally** before reporting
//! success.
//!
//! Three working backends are integrated, each shelled out to via its existing
//! CLI (Clean never re-implements a provider API):
//!
//! - **`aristotle`** (default) — Harmonic's remote Lean proof agent. Submits a
//!   project snapshot + prompt, waits, and downloads a result tarball.
//! - **`ax-deepseek`** — the Axiom Math `ax-prover` OSS agent on its DeepSeek
//!   backend (patched in; default `ax-prover` config). Edits the project in
//!   place.
//! - **`ax-claude-code`** — `ax-prover` driving Claude through the local,
//!   subscription-authenticated `claude` CLI (NO API key). Tools-disabled (the
//!   CLI runs its own agentic loop and does not expose `tool_calls`).
//!
//! Verification-after-retrieval is non-negotiable. A backend's own "success"
//! report is advisory only; [`verify`] re-runs `lake build`, scans for residual
//! `sorry`/`admit`, and checks `#print axioms` against a foundational allowlist.
//!
//! Keys live in the shell-sourceable `~/keys` file (`ARISTOTLE=…`,
//! `DEEPSEEK=…`) and are loaded into the child environment **without echoing**;
//! `ax-claude-code` needs no key.

mod verify;

use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{anyhow, bail, Context};
use clap::{Args, Subcommand, ValueEnum};
use clean_features::{Category, Example, FeatureDescriptor, RefKind, Reference, Stability};

use self::verify::{check_axioms_foundational, find_sorry_marker, parse_print_axioms, ProveError};

/// Path (relative to `$HOME`) of the shell-sourceable keys file.
const KEYS_FILE_REL: &str = "keys";
/// Bundled `ax-prover` config selecting the Claude-Code (no-API-key) backend.
const AX_CLAUDE_CODE_CONFIG: &str = "claude_code.yaml";
/// Default prompt sent to Aristotle for a single-theorem goal.
const DEFAULT_ARISTOTLE_PROMPT: &str = "Prove the target theorem. You may add local helper lemmas \
before it, but do not change the target's statement or any existing public declarations. Do not \
introduce axioms, `sorry`, `admit`, or `unsafe`. Ensure `lake build` passes.";

/// Which prover engine to drive.
#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum)]
#[value(rename_all = "kebab-case")]
pub(crate) enum ProveBackend {
    /// Harmonic Aristotle (remote; needs `ARISTOTLE` in `~/keys`).
    Aristotle,
    /// `ax-prover` on its DeepSeek backend (needs `DEEPSEEK` in `~/keys`).
    AxDeepseek,
    /// `ax-prover` driving Claude via the local `claude` CLI (no API key).
    AxClaudeCode,
}

impl ProveBackend {
    /// Human-readable label for status output.
    fn label(self) -> &'static str {
        match self {
            Self::Aristotle => "aristotle",
            Self::AxDeepseek => "ax-deepseek",
            Self::AxClaudeCode => "ax-claude-code",
        }
    }
}

/// `clean prove <command>` verb tree.
#[derive(Debug, Subcommand)]
pub(crate) enum ProveCommands {
    /// Submit a goal to a prover backend, retrieve the proof, and verify it.
    Run(ProveRunArgs),
    /// Show the status of an in-flight Aristotle project (async flow).
    Status(ProveStatusArgs),
    /// List recent Aristotle projects (async flow).
    List(ProveListArgs),
}

/// Arguments for `clean prove run`.
#[derive(Debug, Clone, Args)]
pub(crate) struct ProveRunArgs {
    /// Lean project directory (must contain `lean-toolchain` + a `lakefile`).
    #[arg(value_name = "PROJECT_DIR")]
    pub project_dir: PathBuf,
    /// Goal to prove, as `<Module>:<theorem>` (e.g. `MyProj.Algebra:ring_lemma`).
    #[arg(value_name = "MODULE:THEOREM")]
    pub goal: String,
    /// Prover backend to use.
    #[arg(long, value_enum, default_value_t = ProveBackend::Aristotle)]
    pub backend: ProveBackend,
    /// Wait for the backend to finish (Aristotle async flow; the ax-prover
    /// backends are always synchronous).
    #[arg(long)]
    pub wait: bool,
    /// Override the prompt sent to Aristotle (ignored by the ax-prover backends,
    /// which take the goal location directly).
    #[arg(long, value_name = "TEXT")]
    pub prompt: Option<String>,
    /// Print the backend invocation instead of running it. No network calls,
    /// no key loading — for inspection and tests.
    #[arg(long)]
    pub dry_run: bool,
    /// Skip the local verification pass after retrieval. NOT recommended — the
    /// provider's success report is not authoritative.
    #[arg(long)]
    pub skip_verify: bool,
    /// Reconcile the Aristotle result by copying back only the changed
    /// proof-bearing `.lean` file (the one matching the goal module) and
    /// preserving the local `lean-toolchain`/`lakefile`, instead of extracting
    /// the whole returned project over the local one. Cross-toolchain safe (the
    /// Aristotle tarball rewrites `lean-toolchain` to its own preferred version,
    /// which would otherwise force a cold Mathlib rebuild). Guards that the
    /// theorem statement is unchanged from what was submitted. Only affects the
    /// synchronous Aristotle `--wait` flow.
    #[arg(long)]
    pub harvest: bool,
}

/// How to reconcile an Aristotle result tarball onto the local project.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub(crate) enum ExtractMode {
    /// Extract the whole returned project over the local one (verbatim,
    /// including the returned `lean-toolchain`/`lakefile`). Back-compat default.
    #[default]
    Full,
    /// Copy back only the changed proof-bearing `.lean` file matching the goal
    /// module, preserving the local `lean-toolchain`/`lakefile`. Guards that the
    /// theorem statement is unchanged.
    Harvest,
}

/// Arguments for `clean prove status`.
#[derive(Debug, Clone, Args)]
pub(crate) struct ProveStatusArgs {
    /// Aristotle project id returned by an earlier `clean prove run`.
    #[arg(value_name = "PROJECT_ID")]
    pub project_id: String,
}

/// Arguments for `clean prove list`.
#[derive(Debug, Clone, Args)]
pub(crate) struct ProveListArgs {
    /// Maximum number of recent projects to list.
    #[arg(long, default_value_t = 10)]
    pub limit: u32,
}

/// A `<Module>:<theorem>` goal, split into its parts.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Goal {
    /// The Lean module path (left of the colon).
    module: String,
    /// The theorem name (right of the colon).
    theorem: String,
}

/// Parse a `<Module>:<theorem>` goal string.
fn parse_goal(goal: &str) -> anyhow::Result<Goal> {
    let (module, theorem) = goal.split_once(':').ok_or_else(|| {
        anyhow!("goal `{goal}` must have the form <Module>:<theorem> (e.g. MyProj.Algebra:lemma)")
    })?;
    if module.is_empty() || theorem.is_empty() {
        bail!(
            "goal `{goal}` must have a non-empty module and theorem (got `{module}`:`{theorem}`)"
        );
    }
    Ok(Goal {
        module: module.to_owned(),
        theorem: theorem.to_owned(),
    })
}

/// Top-level dispatcher for `clean prove`.
pub(crate) fn handle_prove_command(command: ProveCommands) -> anyhow::Result<()> {
    match command {
        ProveCommands::Run(args) => run_prove(args),
        ProveCommands::Status(args) => aristotle_status(&args.project_id),
        ProveCommands::List(args) => aristotle_list(args.limit),
    }
}

/// Execute the `clean prove run` workflow.
fn run_prove(args: ProveRunArgs) -> anyhow::Result<()> {
    let goal = parse_goal(&args.goal)?;
    if !args.dry_run && !args.project_dir.is_dir() {
        bail!(
            "project directory `{}` does not exist or is not a directory",
            args.project_dir.display()
        );
    }

    let argv = build_backend_argv(args.backend, &args.project_dir, &goal, &args, args.wait);

    if args.dry_run {
        println!(
            "[dry-run] backend={} would run: {} {}",
            args.backend.label(),
            argv.program,
            argv.args.join(" ")
        );
        if let Some(dest) = &argv.aristotle_destination {
            println!("[dry-run] would download result to: {}", dest.display());
        }
        return Ok(());
    }

    // For the Aristotle async (non-`--wait`) flow, submit and return the id.
    if args.backend == ProveBackend::Aristotle && !args.wait {
        return aristotle_submit_async(&argv);
    }

    println!("Submitting `{}` to {} …", args.goal, args.backend.label());
    run_backend(&argv).with_context(|| format!("running {} backend", args.backend.label()))?;

    // Aristotle writes a result tarball; reconcile it onto the project so
    // verification runs against the returned proof. `--harvest` copies back only
    // the changed proof file and keeps the local toolchain; the default extracts
    // the whole returned project.
    if let Some(dest) = &argv.aristotle_destination {
        let mode = if args.harvest {
            ExtractMode::Harvest
        } else {
            ExtractMode::Full
        };
        match mode {
            ExtractMode::Full => extract_aristotle_result(dest, &args.project_dir)
                .context("extracting Aristotle result tarball")?,
            ExtractMode::Harvest => harvest_aristotle_result(dest, &args.project_dir, &goal)
                .context("harvesting proof file from Aristotle result tarball")?,
        }
    }

    if args.skip_verify {
        println!(
            "WARNING: --skip-verify set; the {} success report is NOT authoritative.",
            args.backend.label()
        );
        return Ok(());
    }

    verify_locally(&args.project_dir, &goal)
        .map_err(|e| anyhow!("local verification failed: {e}"))?;
    println!(
        "VERIFIED: `{}` proved by {} and re-checked locally \
         (lake build clean, no sorry/admit, axioms ⊆ foundational allowlist).",
        args.goal,
        args.backend.label()
    );
    Ok(())
}

/// A backend invocation: the program, its argv, the environment key to inject
/// (loaded from `~/keys` without echoing), and — for Aristotle — the tarball
/// destination to download into.
struct BackendInvocation {
    program: String,
    args: Vec<String>,
    /// `(env_var, keys_file_name)` to load from `~/keys` into the child env.
    key_env: Option<(&'static str, &'static str)>,
    /// Aristotle result tarball destination (download target).
    aristotle_destination: Option<PathBuf>,
}

/// Build the argv (and key/env metadata) for the chosen backend.
fn build_backend_argv(
    backend: ProveBackend,
    project_dir: &Path,
    goal: &Goal,
    args: &ProveRunArgs,
    wait: bool,
) -> BackendInvocation {
    match backend {
        ProveBackend::Aristotle => {
            let prompt = args
                .prompt
                .clone()
                .unwrap_or_else(|| DEFAULT_ARISTOTLE_PROMPT.to_owned());
            let dest = aristotle_destination(goal);
            let mut argv = vec![
                "submit".to_owned(),
                prompt,
                "--project-dir".to_owned(),
                project_dir.display().to_string(),
            ];
            if wait {
                argv.push("--wait".to_owned());
                argv.push("--destination".to_owned());
                argv.push(dest.display().to_string());
            }
            BackendInvocation {
                program: "aristotle".to_owned(),
                args: argv,
                key_env: Some(("ARISTOTLE_API_KEY", "ARISTOTLE")),
                aristotle_destination: if wait { Some(dest) } else { None },
            }
        }
        ProveBackend::AxDeepseek => BackendInvocation {
            program: "ax-prover".to_owned(),
            args: vec![
                "prove".to_owned(),
                format!("{}:{}", goal.module, goal.theorem),
                "--folder".to_owned(),
                project_dir.display().to_string(),
                "--overwrite".to_owned(),
            ],
            key_env: Some(("DEEPSEEK_API_KEY", "DEEPSEEK")),
            aristotle_destination: None,
        },
        ProveBackend::AxClaudeCode => BackendInvocation {
            program: "ax-prover".to_owned(),
            // `--config` must precede the subcommand (ax-prover argparse rule).
            args: vec![
                "--config".to_owned(),
                AX_CLAUDE_CODE_CONFIG.to_owned(),
                "prove".to_owned(),
                format!("{}:{}", goal.module, goal.theorem),
                "--folder".to_owned(),
                project_dir.display().to_string(),
                "--overwrite".to_owned(),
            ],
            // No API key: the claude CLI is subscription-authenticated.
            key_env: None,
            aristotle_destination: None,
        },
    }
}

/// Canonical Aristotle tarball destination for a goal (under the system temp
/// dir so it does not clutter the project).
fn aristotle_destination(goal: &Goal) -> PathBuf {
    let safe = goal.theorem.replace(['.', ':', '/'], "_");
    std::env::temp_dir().join(format!("clean-prove-aristotle-{safe}.tar.gz"))
}

/// Run a backend invocation, inheriting stdio so the user sees live progress.
fn run_backend(inv: &BackendInvocation) -> anyhow::Result<()> {
    let mut cmd = Command::new(&inv.program);
    cmd.args(&inv.args);
    inject_key(&mut cmd, inv.key_env)?;
    let status = cmd.status().with_context(|| {
        format!(
            "failed to spawn `{}` — is it installed and on PATH?",
            inv.program
        )
    })?;
    if !status.success() {
        bail!(
            "{} exited with {}",
            inv.program,
            status
                .code()
                .map_or_else(|| "a signal".to_owned(), |c| format!("status {c}"))
        );
    }
    Ok(())
}

/// Load the named key from `~/keys` and inject it into the child environment
/// under `env_var`, **without echoing** the value. No-op when `key_env` is
/// `None` (e.g. the claude-code backend needs no key).
fn inject_key(
    cmd: &mut Command,
    key_env: Option<(&'static str, &'static str)>,
) -> anyhow::Result<()> {
    let Some((env_var, keys_name)) = key_env else {
        return Ok(());
    };
    // Already present in the ambient environment? Honor it without touching the
    // keys file (and never print it).
    if std::env::var_os(env_var).is_some() {
        return Ok(());
    }
    let value = read_key_from_keys_file(keys_name)?;
    cmd.env(env_var, value);
    Ok(())
}

/// Read a single `NAME=value` entry from the shell-sourceable `~/keys` file.
///
/// Returns the raw value (never logged). Errors if the file or the key is
/// missing, so the workflow fails loudly rather than silently unauthenticated.
fn read_key_from_keys_file(name: &str) -> anyhow::Result<String> {
    let home = std::env::var_os("HOME")
        .ok_or_else(|| anyhow!("$HOME is not set; cannot locate the ~/{KEYS_FILE_REL} file"))?;
    let path = Path::new(&home).join(KEYS_FILE_REL);
    let contents = std::fs::read_to_string(&path)
        .with_context(|| format!("reading keys file at {}", path.display()))?;
    for line in contents.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        // Tolerate an optional leading `export `.
        let line = line.strip_prefix("export ").unwrap_or(line);
        if let Some((key, value)) = line.split_once('=') {
            if key.trim() == name {
                let value = value.trim().trim_matches('"').trim_matches('\'').to_owned();
                if value.is_empty() {
                    bail!("key `{name}` in {} is empty", path.display());
                }
                return Ok(value);
            }
        }
    }
    bail!(
        "key `{name}` not found in {} — add a `{name}=…` line",
        path.display()
    )
}

/// Submit to Aristotle without waiting and print the project id for later
/// `clean prove status <id>` / `clean prove list`.
fn aristotle_submit_async(inv: &BackendInvocation) -> anyhow::Result<()> {
    println!("Submitting to Aristotle (async; use `clean prove status <id>` to follow up) …");
    run_backend(inv)?;
    println!(
        "Submitted. Run `clean prove list` to find the project id, then \
         `clean prove status <id>`; download + verify with `--wait` once it finishes."
    );
    Ok(())
}

/// `clean prove status <id>` — delegate to `aristotle show`.
fn aristotle_status(project_id: &str) -> anyhow::Result<()> {
    let inv = BackendInvocation {
        program: "aristotle".to_owned(),
        args: vec!["show".to_owned(), project_id.to_owned()],
        key_env: Some(("ARISTOTLE_API_KEY", "ARISTOTLE")),
        aristotle_destination: None,
    };
    run_backend(&inv).context("querying Aristotle project status")
}

/// `clean prove list` — delegate to `aristotle list --limit N`.
fn aristotle_list(limit: u32) -> anyhow::Result<()> {
    let inv = BackendInvocation {
        program: "aristotle".to_owned(),
        args: vec!["list".to_owned(), "--limit".to_owned(), limit.to_string()],
        key_env: Some(("ARISTOTLE_API_KEY", "ARISTOTLE")),
        aristotle_destination: None,
    };
    run_backend(&inv).context("listing Aristotle projects")
}

/// Extract an Aristotle result tarball back over the project directory so the
/// returned `.lean` edits land where local verification can re-check them.
///
/// Shells out to `tar` (matching `clean vendor`'s no-new-dependency posture).
fn extract_aristotle_result(tarball: &Path, project_dir: &Path) -> anyhow::Result<()> {
    if !tarball.is_file() {
        bail!(
            "Aristotle result tarball {} was not produced — the job may have failed or been cancelled",
            tarball.display()
        );
    }
    let status = Command::new("tar")
        .arg("-xzf")
        .arg(tarball)
        .arg("-C")
        .arg(project_dir)
        .arg("--strip-components")
        .arg("1")
        .status()
        .context("failed to spawn `tar` to extract the Aristotle result")?;
    if !status.success() {
        bail!("`tar` failed to extract {}", tarball.display());
    }
    Ok(())
}

/// Lean-declaration keywords whose statement (signature) we guard.
const DECL_KEYWORDS: &[&str] = &["theorem", "lemma"];

/// Outcome of comparing the submitted vs. returned statement of a theorem.
#[derive(Debug, Clone, PartialEq, Eq)]
enum StatementGuard {
    /// The statement (signature up to `:=`) is unchanged modulo whitespace.
    Unchanged,
    /// The statement was altered. Carries the normalized before/after for a
    /// diagnostic.
    Altered {
        /// Submitted statement (whitespace-normalized).
        before: String,
        /// Returned statement (whitespace-normalized).
        after: String,
    },
    /// The theorem could not be located in the submitted and/or returned source.
    NotFound,
}

/// Harvest **only** the changed proof-bearing `.lean` file (the one matching the
/// goal module) from an Aristotle result tarball, leaving the project's
/// `lean-toolchain`/`lakefile` untouched, after guarding that the theorem
/// statement is unchanged.
///
/// This is the cross-toolchain-safe reconciliation: Aristotle rewrites
/// `lean-toolchain` to its own preferred version, so a blind full extract
/// (`extract_aristotle_result`) points `lake build` at the wrong toolchain and
/// forces a cold Mathlib rebuild. Harvest keeps the local pin.
fn harvest_aristotle_result(tarball: &Path, project_dir: &Path, goal: &Goal) -> anyhow::Result<()> {
    if !tarball.is_file() {
        bail!(
            "Aristotle result tarball {} was not produced — the job may have failed or been cancelled",
            tarball.display()
        );
    }

    // Extract to a scratch dir (NOT over the project) so we can pick out just the
    // proof file and never disturb the local toolchain/lakefile.
    let scratch =
        tempfile::tempdir().context("creating a temp dir to unpack the result tarball")?;
    let status = Command::new("tar")
        .arg("-xzf")
        .arg(tarball)
        .arg("-C")
        .arg(scratch.path())
        .status()
        .context("failed to spawn `tar` to unpack the Aristotle result")?;
    if !status.success() {
        bail!("`tar` failed to unpack {}", tarball.display());
    }

    // The proof-bearing file is the one matching the goal module.
    let rel = module_rel_path(&goal.module);
    let project_file = project_dir.join(&rel);
    if !project_file.is_file() {
        bail!(
            "goal module `{}` maps to `{}`, which does not exist under the project — \
             cannot harvest (harvest expects the proof to live in the goal module's file)",
            goal.module,
            rel
        );
    }
    let returned_file = find_returned_lean_file(scratch.path(), &rel).ok_or_else(|| {
        anyhow!(
            "the returned tarball has no `.lean` file matching the goal module `{}` (`{}`)",
            goal.module,
            rel
        )
    })?;

    let submitted = std::fs::read_to_string(&project_file).with_context(|| {
        format!(
            "reading the submitted proof file {}",
            project_file.display()
        )
    })?;
    let returned = std::fs::read_to_string(&returned_file).with_context(|| {
        format!(
            "reading the returned proof file {}",
            returned_file.display()
        )
    })?;

    // Guard: the theorem statement must be unchanged. This is the trust anchor —
    // Path B proves the *translated statement*; if Aristotle weakened or altered
    // it, the returned proof is of a different proposition and must be rejected.
    match compare_statements(&submitted, &returned, &goal.theorem) {
        StatementGuard::Unchanged => {}
        StatementGuard::Altered { before, after } => bail!(
            "Aristotle altered the statement of `{}` — refusing to harvest.\n  \
             submitted: {before}\n  returned:  {after}",
            goal.theorem
        ),
        StatementGuard::NotFound => bail!(
            "could not locate theorem `{}` in the submitted and/or returned proof file — \
             refusing to harvest without a statement-integrity check",
            goal.theorem
        ),
    }

    // Copy back only the proof file (leaving lean-toolchain/lakefile untouched).
    std::fs::write(&project_file, returned.as_bytes()).with_context(|| {
        format!(
            "writing the harvested proof back to {}",
            project_file.display()
        )
    })?;
    println!(
        "Harvested proof for `{}` into {} (local toolchain/lakefile preserved).",
        goal.theorem, rel
    );
    Ok(())
}

/// Map a Lean module path (`A.B.C`) to its source-file path relative to the
/// project root (`A/B/C.lean`).
fn module_rel_path(module: &str) -> String {
    format!("{}.lean", module.replace('.', "/"))
}

/// Find the returned `.lean` file whose path ends with the goal module's
/// relative path (accounting for a wrapping top-level dir in the tarball).
fn find_returned_lean_file(root: &Path, rel: &str) -> Option<PathBuf> {
    let want_suffix = format!("/{rel}");
    let mut best: Option<PathBuf> = None;
    for entry in walkdir::WalkDir::new(root)
        .into_iter()
        .filter_map(Result::ok)
    {
        let path = entry.path();
        if path.extension().and_then(|s| s.to_str()) != Some("lean") {
            continue;
        }
        let as_str = path.to_string_lossy();
        if as_str.ends_with(&want_suffix) || as_str.ends_with(rel) {
            // Prefer the shortest matching path (closest to the module root).
            match &best {
                Some(prev) if prev.as_os_str().len() <= path.as_os_str().len() => {}
                _ => best = Some(path.to_path_buf()),
            }
        }
    }
    best
}

/// Compare the statement (signature up to `:=`) of `theorem` in the submitted
/// vs. the returned source. Whitespace is normalized so benign reformatting does
/// not trip the guard, while any token-level change is caught.
fn compare_statements(submitted: &str, returned: &str, theorem: &str) -> StatementGuard {
    let (Some(pre), Some(post)) = (
        extract_theorem_statement(submitted, theorem),
        extract_theorem_statement(returned, theorem),
    ) else {
        return StatementGuard::NotFound;
    };
    let before = normalize_statement(&pre);
    let after = normalize_statement(&post);
    if before == after {
        StatementGuard::Unchanged
    } else {
        StatementGuard::Altered { before, after }
    }
}

/// Extract a theorem's statement text — from the declaration keyword up to (but
/// not including) the `:=` proof separator. Returns `None` if the declaration is
/// not found or has no `:=`.
fn extract_theorem_statement(source: &str, theorem: &str) -> Option<String> {
    let decl_start = find_decl_start(source, theorem)?;
    let after = &source[decl_start..];
    let sep = after.find(":=")?;
    Some(after[..sep].to_owned())
}

/// Find the byte offset where the declaration of `theorem` begins (at its
/// `theorem`/`lemma` keyword). Matches the fully-qualified name or its leaf.
fn find_decl_start(source: &str, theorem: &str) -> Option<usize> {
    let leaf = theorem.rsplit('.').next().unwrap_or(theorem);
    let bytes = source.as_bytes();
    let mut best: Option<usize> = None;
    for kw in DECL_KEYWORDS {
        let mut from = 0usize;
        while let Some(rel) = source[from..].find(kw) {
            let kw_start = from + rel;
            let kw_end = kw_start + kw.len();
            from = kw_end;
            // Keyword must be word-bounded on both sides.
            let before_ok = kw_start == 0 || !is_ident_byte(bytes[kw_start - 1]);
            let after_ok = kw_end >= bytes.len() || !is_ident_byte(bytes[kw_end]);
            if !before_ok || !after_ok {
                continue;
            }
            let rest = &source[kw_end..];
            let ws = rest.len() - rest.trim_start().len();
            let name_area = &source[kw_end + ws..];
            let matches_name = name_matches(name_area, theorem) || name_matches(name_area, leaf);
            if matches_name && best.is_none_or(|b| kw_start < b) {
                best = Some(kw_start);
            }
        }
    }
    best
}

/// Whether `area` begins with `name` as a whole identifier (word-bounded after).
fn name_matches(area: &str, name: &str) -> bool {
    area.starts_with(name)
        && area
            .as_bytes()
            .get(name.len())
            .is_none_or(|&b| !is_ident_byte(b))
}

/// Whether `b` can appear inside a Lean identifier.
fn is_ident_byte(b: u8) -> bool {
    b.is_ascii_alphanumeric() || matches!(b, b'_' | b'.' | b'\'' | b'!' | b'?')
}

/// Collapse all whitespace runs to a single space and trim, for a
/// reformatting-insensitive statement comparison.
fn normalize_statement(s: &str) -> String {
    s.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// Run the full local verification pass against a retrieved proof and surface a
/// typed [`ProveError`] on failure.
fn verify_locally(project_dir: &Path, goal: &Goal) -> Result<(), ProveError> {
    // 1. No residual sorry/admit anywhere in the project's `.lean` sources.
    scan_for_sorry(project_dir)?;

    // 2. lake build must be clean, with a `#print axioms` probe appended so its
    //    output appears in the captured build log.
    let build_output = run_lake_build_with_axiom_probe(project_dir, goal)?;

    // 3. Axiom closure ⊆ foundational allowlist.
    let report = parse_print_axioms(&build_output, &goal.theorem).ok_or_else(|| {
        ProveError::AxiomClosureUnknown {
            theorem: goal.theorem.clone(),
        }
    })?;
    check_axioms_foundational(&goal.theorem, &report)?;
    Ok(())
}

/// Walk every `.lean` file under `project_dir` (skipping `.lake`/`.git`) and
/// fail on the first residual `sorry`/`admit`.
fn scan_for_sorry(project_dir: &Path) -> Result<(), ProveError> {
    for entry in walkdir::WalkDir::new(project_dir)
        .into_iter()
        .filter_entry(|e| {
            let name = e.file_name().to_string_lossy();
            name != ".lake" && name != ".git" && name != "target"
        })
        .filter_map(Result::ok)
    {
        let path = entry.path();
        if path.extension().and_then(|s| s.to_str()) != Some("lean") {
            continue;
        }
        let Ok(source) = std::fs::read_to_string(path) else {
            continue;
        };
        if let Some(marker) = find_sorry_marker(&source) {
            return Err(ProveError::SorryRemains {
                marker: marker.to_owned(),
                file: path
                    .strip_prefix(project_dir)
                    .unwrap_or(path)
                    .display()
                    .to_string(),
            });
        }
    }
    Ok(())
}

/// Run `lake build` and return the combined stdout+stderr.
///
/// The build is run from `project_dir`. A separate `lake env lean` probe that
/// `#print axioms <theorem>` is appended so the captured output carries the
/// axiom closure for [`parse_print_axioms`].
fn run_lake_build_with_axiom_probe(project_dir: &Path, goal: &Goal) -> Result<String, ProveError> {
    // Primary build.
    let build = Command::new("lake")
        .arg("build")
        .current_dir(project_dir)
        .output()
        .map_err(|e| ProveError::LakeBuildFailed {
            code: -1,
            tail: format!("failed to spawn `lake build`: {e}"),
        })?;
    let mut combined = String::from_utf8_lossy(&build.stdout).into_owned();
    combined.push_str(&String::from_utf8_lossy(&build.stderr));
    if !build.status.success() {
        return Err(ProveError::LakeBuildFailed {
            code: build.status.code().unwrap_or(-1),
            tail: tail_lines(&combined, 40),
        });
    }

    // Axiom probe: a throwaway module that imports the goal module and prints
    // the theorem's axiom closure. Written to a temp file inside the project so
    // `lake env lean` resolves the project's import path.
    let probe = format!("import {}\n#print axioms {}\n", goal.module, goal.theorem);
    let probe_path = project_dir.join(".clean-prove-axiom-probe.lean");
    if std::fs::write(&probe_path, &probe).is_ok() {
        let out = Command::new("lake")
            .arg("env")
            .arg("lean")
            .arg(&probe_path)
            .current_dir(project_dir)
            .output();
        let _ = std::fs::remove_file(&probe_path);
        if let Ok(out) = out {
            combined.push_str(&String::from_utf8_lossy(&out.stdout));
            combined.push_str(&String::from_utf8_lossy(&out.stderr));
        }
    }
    Ok(combined)
}

/// Return the last `n` lines of `s` joined by newlines (bounded diagnostic).
fn tail_lines(s: &str, n: usize) -> String {
    let lines: Vec<&str> = s.lines().collect();
    let start = lines.len().saturating_sub(n);
    lines[start..].join("\n")
}

const PROVE_DESIGN_REF: Reference = Reference {
    kind: RefKind::Doc,
    label: "Aristotle remote-prover skill (verification discipline)",
    target: "docs/cli/prove-run.md",
};

const CLI_CRATE_REF: Reference = Reference {
    kind: RefKind::Crate,
    label: "clean-cli",
    target: "clean-cli",
};

/// Feature descriptors surfaced by the `clean prove` verb tree (one per leaf).
pub(crate) const FEATURES: &[FeatureDescriptor] = &[
    FeatureDescriptor {
        path: &["prove", "run"],
        summary: "Prove a Lean goal via a remote/automated backend, then verify it locally",
        description: "\
Submits a `<Module>:<theorem>` goal in a Lean project to a remote or automated \
prover backend, retrieves the candidate proof, and — non-negotiably — \
RE-VERIFIES it locally before reporting success.\n\n\
Backends (`--backend`):\n\
- `aristotle` (default) — Harmonic's remote Lean proof agent. Submits a project \
snapshot + prompt, waits with `--wait`, and downloads a result tarball.\n\
- `ax-deepseek` — the Axiom Math `ax-prover` agent on its DeepSeek backend.\n\
- `ax-claude-code` — `ax-prover` driving Claude through the local, \
subscription-authenticated `claude` CLI (no API key; tools-disabled).\n\n\
Verification re-runs `lake build` (must be clean), scans every `.lean` source \
for residual `sorry`/`admit`, and checks `#print axioms <theorem>` against a \
foundational allowlist (propext, Quot.sound, Classical.choice, the Eq/rfl \
built-ins). The provider's own success message is advisory only.\n\n\
Keys load from the shell-sourceable `~/keys` file (`ARISTOTLE`, `DEEPSEEK`) \
without being echoed; `ax-claude-code` needs no key. Use `--dry-run` to print \
the backend invocation without running it, or `--wait` for the synchronous \
Aristotle flow.\n\n\
`--harvest` (Aristotle `--wait` only) copies back ONLY the changed proof file \
matching the goal module and preserves the local `lean-toolchain`/`lakefile`, \
instead of extracting the whole returned project. This is cross-toolchain safe: \
Aristotle rewrites `lean-toolchain` to its own preferred version, so a full \
extract would point `lake build` at the wrong toolchain and force a cold Mathlib \
rebuild. Harvest guards that the theorem statement is unchanged from what was \
submitted (rejecting a weakened/altered statement).",
        category: Category::Proof,
        stability: Stability::Building,
        examples: &[
            Example {
                cmd: "clean prove run ./my-lean-project MyProj.Algebra:ring_lemma --wait",
                what: "prove ring_lemma with Aristotle, wait, download, and verify locally",
            },
            Example {
                cmd: "clean prove run ./proj Sub:foo --wait --harvest",
                what: "prove foo, then harvest only the proof file (keep the local toolchain)",
            },
            Example {
                cmd: "clean prove run ./proj Demo.Basic:foo --backend ax-claude-code",
                what: "prove foo with ax-prover via the local claude CLI (no API key)",
            },
            Example {
                cmd: "clean prove run ./proj Demo.Basic:foo --backend ax-deepseek --dry-run",
                what: "print the ax-prover DeepSeek invocation without running it",
            },
        ],
        see_also: &["prove status", "prove list", "check"],
        references: &[PROVE_DESIGN_REF, CLI_CRATE_REF],
        domain_root: Some("prove"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["prove", "status"],
        summary: "Show the status of an in-flight Aristotle proof project",
        description: "\
Delegates to `aristotle show <project-id>` to report the task status and events \
for an Aristotle project submitted asynchronously (a `clean prove run` without \
`--wait`). Loads the `ARISTOTLE` key from `~/keys` without echoing it.",
        category: Category::Proof,
        stability: Stability::Building,
        examples: &[Example {
            cmd: "clean prove status 1a2b3c4d",
            what: "show task status + events for Aristotle project 1a2b3c4d",
        }],
        see_also: &["prove run", "prove list"],
        references: &[PROVE_DESIGN_REF, CLI_CRATE_REF],
        domain_root: Some("prove"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["prove", "list"],
        summary: "List recent Aristotle proof projects",
        description: "\
Delegates to `aristotle list --limit N` to enumerate recent Aristotle projects \
(most recent first), so you can recover a project id for `clean prove status`. \
Loads the `ARISTOTLE` key from `~/keys` without echoing it.",
        category: Category::Proof,
        stability: Stability::Building,
        examples: &[Example {
            cmd: "clean prove list --limit 5",
            what: "list the 5 most recent Aristotle projects",
        }],
        see_also: &["prove run", "prove status"],
        references: &[PROVE_DESIGN_REF, CLI_CRATE_REF],
        domain_root: Some("prove"),
        alternative_forms: &[],
        feature_gate: None,
    },
];

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_goal_splits_module_and_theorem() {
        let goal = parse_goal("MyProj.Algebra:ring_lemma").expect("valid goal");
        assert_eq!(goal.module, "MyProj.Algebra");
        assert_eq!(goal.theorem, "ring_lemma");
    }

    #[test]
    fn test_parse_goal_rejects_missing_colon() {
        assert!(parse_goal("MyProj.Algebra.ring_lemma").is_err());
    }

    #[test]
    fn test_parse_goal_rejects_empty_parts() {
        assert!(parse_goal(":ring_lemma").is_err());
        assert!(parse_goal("MyProj.Algebra:").is_err());
    }

    #[test]
    fn test_aristotle_argv_wait_includes_destination() {
        let goal = parse_goal("M:foo").expect("valid");
        let args = ProveRunArgs {
            project_dir: PathBuf::from("/tmp/proj"),
            goal: "M:foo".to_owned(),
            backend: ProveBackend::Aristotle,
            wait: true,
            prompt: None,
            dry_run: true,
            skip_verify: false,
            harvest: false,
        };
        let inv = build_backend_argv(
            ProveBackend::Aristotle,
            Path::new("/tmp/proj"),
            &goal,
            &args,
            true,
        );
        assert_eq!(inv.program, "aristotle");
        assert_eq!(inv.args[0], "submit");
        assert!(inv.args.iter().any(|a| a == "--wait"));
        assert!(inv.args.iter().any(|a| a == "--project-dir"));
        assert!(inv.args.iter().any(|a| a == "--destination"));
        assert!(inv.aristotle_destination.is_some());
        assert_eq!(inv.key_env, Some(("ARISTOTLE_API_KEY", "ARISTOTLE")));
    }

    #[test]
    fn test_aristotle_argv_async_omits_destination() {
        let goal = parse_goal("M:foo").expect("valid");
        let args = ProveRunArgs {
            project_dir: PathBuf::from("/tmp/proj"),
            goal: "M:foo".to_owned(),
            backend: ProveBackend::Aristotle,
            wait: false,
            prompt: None,
            dry_run: true,
            skip_verify: false,
            harvest: false,
        };
        let inv = build_backend_argv(
            ProveBackend::Aristotle,
            Path::new("/tmp/proj"),
            &goal,
            &args,
            false,
        );
        assert!(!inv.args.iter().any(|a| a == "--wait"));
        assert!(inv.aristotle_destination.is_none());
    }

    #[test]
    fn test_ax_deepseek_argv_targets_goal_and_folder() {
        let goal = parse_goal("Demo.Basic:foo").expect("valid");
        let args = ProveRunArgs {
            project_dir: PathBuf::from("/tmp/proj"),
            goal: "Demo.Basic:foo".to_owned(),
            backend: ProveBackend::AxDeepseek,
            wait: false,
            prompt: None,
            dry_run: true,
            skip_verify: false,
            harvest: false,
        };
        let inv = build_backend_argv(
            ProveBackend::AxDeepseek,
            Path::new("/tmp/proj"),
            &goal,
            &args,
            false,
        );
        assert_eq!(inv.program, "ax-prover");
        assert_eq!(inv.args[0], "prove");
        assert_eq!(inv.args[1], "Demo.Basic:foo");
        assert!(inv.args.iter().any(|a| a == "--folder"));
        assert_eq!(inv.key_env, Some(("DEEPSEEK_API_KEY", "DEEPSEEK")));
    }

    #[test]
    fn test_ax_claude_code_argv_puts_config_before_subcommand_and_needs_no_key() {
        let goal = parse_goal("Demo.Basic:foo").expect("valid");
        let args = ProveRunArgs {
            project_dir: PathBuf::from("/tmp/proj"),
            goal: "Demo.Basic:foo".to_owned(),
            backend: ProveBackend::AxClaudeCode,
            wait: false,
            prompt: None,
            dry_run: true,
            skip_verify: false,
            harvest: false,
        };
        let inv = build_backend_argv(
            ProveBackend::AxClaudeCode,
            Path::new("/tmp/proj"),
            &goal,
            &args,
            false,
        );
        assert_eq!(inv.program, "ax-prover");
        // `--config` must precede `prove` (ax-prover argparse rule).
        let config_idx = inv
            .args
            .iter()
            .position(|a| a == "--config")
            .expect("config flag");
        let prove_idx = inv
            .args
            .iter()
            .position(|a| a == "prove")
            .expect("prove verb");
        assert!(config_idx < prove_idx, "--config must come before prove");
        assert_eq!(inv.args[config_idx + 1], AX_CLAUDE_CODE_CONFIG);
        // No API key needed — subscription-authenticated.
        assert_eq!(inv.key_env, None);
    }

    #[test]
    fn test_read_key_from_keys_file_parses_named_entry() {
        let dir = tempfile::tempdir().expect("tempdir");
        let keys = dir.path().join("keys");
        std::fs::write(
            &keys,
            "# a comment\nARISTOTLE=secret-abc\nexport DEEPSEEK=\"ds-xyz\"\n",
        )
        .expect("write keys");
        // Point HOME at the temp dir for the duration of this test; the guard
        // restores the previous value (or unsets it) on scope exit.
        let _env = crate::test_env::lock_env();
        let _guard = crate::test_env::ScopedEnvVar::set("HOME", &dir.path().to_string_lossy());
        let aristotle = read_key_from_keys_file("ARISTOTLE").expect("ARISTOTLE present");
        let deepseek = read_key_from_keys_file("DEEPSEEK").expect("DEEPSEEK present");
        let missing = read_key_from_keys_file("NOPE");
        assert_eq!(aristotle, "secret-abc");
        assert_eq!(deepseek, "ds-xyz"); // `export ` prefix + quotes stripped
        assert!(missing.is_err());
    }

    #[test]
    fn test_backend_label_round_trips() {
        assert_eq!(ProveBackend::Aristotle.label(), "aristotle");
        assert_eq!(ProveBackend::AxDeepseek.label(), "ax-deepseek");
        assert_eq!(ProveBackend::AxClaudeCode.label(), "ax-claude-code");
    }

    #[test]
    fn test_aristotle_destination_sanitizes_theorem_name() {
        let goal = parse_goal("M.N:foo.bar").expect("valid");
        let dest = aristotle_destination(&goal);
        let name = dest
            .file_name()
            .expect("file name")
            .to_string_lossy()
            .into_owned();
        assert!(name.contains("foo_bar"), "got {name}");
        assert!(!name.contains("foo.bar"));
    }

    #[test]
    fn test_tail_lines_bounds_output() {
        let s = "a\nb\nc\nd\ne";
        assert_eq!(tail_lines(s, 2), "d\ne");
        assert_eq!(tail_lines(s, 10), "a\nb\nc\nd\ne");
    }

    #[test]
    fn test_module_rel_path_maps_dots_to_slashes() {
        assert_eq!(module_rel_path("Sub"), "Sub.lean");
        assert_eq!(module_rel_path("PathbBatch.T01"), "PathbBatch/T01.lean");
    }

    #[test]
    fn test_extract_theorem_statement_stops_at_proof_separator() {
        let src = "import Mathlib\n\ntheorem foo (a b : Nat) : a + b = b + a := by\n  omega\n";
        let stmt = extract_theorem_statement(src, "foo").expect("statement");
        assert!(stmt.contains("theorem foo"));
        assert!(stmt.contains("a + b = b + a"));
        assert!(!stmt.contains(":="), "statement must stop before the proof");
        assert!(!stmt.contains("omega"));
    }

    #[test]
    fn test_extract_theorem_statement_matches_lemma_keyword() {
        let src = "lemma bar : True := trivial";
        let stmt = extract_theorem_statement(src, "bar").expect("lemma statement");
        assert!(stmt.contains("lemma bar"));
        assert!(stmt.contains("True"));
    }

    #[test]
    fn test_extract_theorem_statement_matches_leaf_of_qualified_goal() {
        let src = "theorem baz : 1 = 1 := rfl";
        let stmt = extract_theorem_statement(src, "Mod.Sub.baz").expect("leaf match");
        assert!(stmt.contains("theorem baz"));
    }

    #[test]
    fn test_extract_theorem_statement_ignores_identifier_containing_name() {
        // `foobar` merely contains `foo`; must not be mistaken for the `foo` decl.
        let src = "theorem foobar : True := trivial\ntheorem foo : False → True := fun h => h.elim";
        let stmt = extract_theorem_statement(src, "foo").expect("real foo");
        assert!(
            stmt.contains("False"),
            "should locate the real `foo` decl: {stmt}"
        );
    }

    #[test]
    fn test_extract_theorem_statement_absent_returns_none() {
        assert!(extract_theorem_statement("theorem foo : True := trivial", "nope").is_none());
    }

    #[test]
    fn test_compare_statements_proof_only_change_unchanged() {
        let submitted = "theorem foo : 1 = 1 := by sorry";
        let returned = "theorem foo : 1 = 1 := by rfl";
        assert_eq!(
            compare_statements(submitted, returned, "foo"),
            StatementGuard::Unchanged
        );
    }

    #[test]
    fn test_compare_statements_tolerates_reindented_statement() {
        let submitted = "theorem foo (a b : Nat) :\n    a + b = b + a := by sorry";
        let returned = "theorem foo (a b : Nat) : a + b = b + a := by\n  omega";
        assert_eq!(
            compare_statements(submitted, returned, "foo"),
            StatementGuard::Unchanged
        );
    }

    #[test]
    fn test_compare_statements_detects_altered_statement() {
        // Aristotle weakened the statement (b + a -> a + a): must be flagged.
        let submitted = "theorem foo (a b : Nat) : a + b = b + a := by sorry";
        let returned = "theorem foo (a b : Nat) : a + b = a + b := by rfl";
        match compare_statements(submitted, returned, "foo") {
            StatementGuard::Altered { before, after } => {
                assert!(before.contains("b + a"));
                assert!(after.contains("a + b = a + b"));
            }
            other => panic!("expected Altered, got {other:?}"),
        }
    }

    #[test]
    fn test_compare_statements_missing_theorem_is_not_found() {
        let submitted = "theorem foo : True := by sorry";
        let returned = "theorem bar : True := trivial"; // renamed away
        assert_eq!(
            compare_statements(submitted, returned, "foo"),
            StatementGuard::NotFound
        );
    }

    #[test]
    fn test_find_returned_lean_file_matches_module_under_wrapper_dir() {
        let dir = tempfile::tempdir().expect("tempdir");
        // Simulate a tarball extracted with a wrapping top-level dir.
        let nested = dir.path().join("project-abc");
        std::fs::create_dir_all(&nested).expect("mkdir");
        std::fs::write(nested.join("Sub.lean"), "theorem foo : True := trivial")
            .expect("write proof");
        std::fs::write(nested.join("lean-toolchain"), "leanprover/lean4:v4.28.0")
            .expect("write toolchain");
        let found = find_returned_lean_file(dir.path(), "Sub.lean").expect("should find Sub.lean");
        assert!(found.ends_with("Sub.lean"));
    }

    #[test]
    fn test_find_returned_lean_file_absent_returns_none() {
        let dir = tempfile::tempdir().expect("tempdir");
        std::fs::write(dir.path().join("Other.lean"), "theorem x : True := trivial")
            .expect("write");
        assert!(find_returned_lean_file(dir.path(), "Sub.lean").is_none());
    }

    #[test]
    fn test_harvest_preserves_toolchain_and_copies_proof() {
        // End-to-end of the file-reconciliation core: build a fake "tarball
        // scratch" and a project, harvest by hand via the helpers, assert the
        // local toolchain survives and the proof body lands.
        let project = tempfile::tempdir().expect("project dir");
        std::fs::write(
            project.path().join("Sub.lean"),
            "theorem foo : 1 = 1 := by sorry\n",
        )
        .expect("write submitted");
        std::fs::write(
            project.path().join("lean-toolchain"),
            "leanprover/lean4:v4.32.0-rc1\n",
        )
        .expect("write local toolchain");

        let returned = tempfile::tempdir().expect("returned dir");
        std::fs::write(
            returned.path().join("Sub.lean"),
            "theorem foo : 1 = 1 := by rfl\n",
        )
        .expect("write returned proof");
        // The returned project would carry Aristotle's toolchain — harvest must
        // NOT copy it back.
        std::fs::write(
            returned.path().join("lean-toolchain"),
            "leanprover/lean4:v4.28.0\n",
        )
        .expect("write returned toolchain");

        // Reconcile: statement unchanged → copy the proof file only.
        let rel = "Sub.lean";
        let submitted = std::fs::read_to_string(project.path().join(rel)).expect("read submitted");
        let ret_file =
            find_returned_lean_file(returned.path(), rel).expect("locate returned proof");
        let ret = std::fs::read_to_string(&ret_file).expect("read returned");
        assert_eq!(
            compare_statements(&submitted, &ret, "foo"),
            StatementGuard::Unchanged
        );
        std::fs::write(project.path().join(rel), ret.as_bytes()).expect("harvest write");

        // Proof body updated…
        let final_proof =
            std::fs::read_to_string(project.path().join(rel)).expect("read final proof");
        assert!(final_proof.contains("rfl"));
        assert!(find_sorry_marker(&final_proof).is_none());
        // …and the LOCAL toolchain is untouched.
        let toolchain =
            std::fs::read_to_string(project.path().join("lean-toolchain")).expect("read toolchain");
        assert!(toolchain.contains("v4.32.0-rc1"));
        assert!(!toolchain.contains("v4.28.0"));
    }

    #[test]
    fn test_features_have_unique_paths_and_examples() {
        use clean_features::{ensure_has_example, ensure_unique_paths};
        let descriptors: Vec<&FeatureDescriptor> = FEATURES.iter().collect();
        ensure_unique_paths(&descriptors).expect("prove descriptor paths are unique");
        for d in FEATURES {
            ensure_has_example(d).expect("every prove descriptor has an example");
        }
        assert_eq!(FEATURES.len(), 3);
    }
}
