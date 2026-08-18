// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Core command handlers: check, verify-c, eval.

use clean_c_sem::auto::ProofStatus;
use clean_c_sem::parser::CParser;
use clean_elab::agent_diagnostics::{AgentDiagnostic, AgentSourceSpan};
use clean_elab::register::reset_kernel_check_counter;
use clean_elab::{
    elaborate_decl_and_register_with_context_and_warning, kernel_check_failure_count,
    preprocess_decl_with_context, ElabCtx, ElabResult, FileContext, RegistrationWarning,
    RegistrationWarningKind, TacticError,
};
use clean_kernel::sorry::{reset_sorry_counter, sorry_count};
use clean_kernel::{Environment, TypeChecker};
use clean_parser::{parse_expr, Span, SurfaceBinder, SurfaceDecl};
use clean_server::handlers::validate_decl_read_only;
use serde::Serialize;
use std::collections::{HashMap, HashSet};
use std::fmt::Write as FmtWrite;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::sync::{Mutex, OnceLock};
use std::time::{Duration, Instant};

const CHECK_REPORT_SCHEMA_VERSION: &str = "Clean-check-report-v1";

#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
pub(crate) fn check_file(
    path: &Path,
    verbose: bool,
    allow_sorry: bool,
    prelude: clean_kernel::cli::PreludeMode,
) -> anyhow::Result<()> {
    check_file_with_json(path, verbose, allow_sorry, prelude, false)
}

#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
pub(crate) fn check_file_with_json(
    path: &Path,
    verbose: bool,
    allow_sorry: bool,
    prelude: clean_kernel::cli::PreludeMode,
    json: bool,
) -> anyhow::Result<()> {
    check_file_with_json_with_imports(path, verbose, allow_sorry, prelude, json, false)
}

pub(crate) fn check_file_with_json_with_imports(
    path: &Path,
    verbose: bool,
    allow_sorry: bool,
    prelude: clean_kernel::cli::PreludeMode,
    json: bool,
    imports_prefer_olean: bool,
) -> anyhow::Result<()> {
    let _guard = check_file_lock()
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    let _trust_counter_scope = TrustCounterScope::enter();
    let start = Instant::now();
    let verbose = verbose && !json;

    let mut env = Environment::with_prelude();
    // B07 (GAP_SWEEP_2026-07-09): per-mode monad-instance policy.
    // - Builtin: also register the Clean-native `Pure List`/`Bind List`
    //   instances (documented prelude extension; Lean core has none).
    // - Lean4Core: leave List uninstanced and enable the strict gate, so
    //   `do`-blocks over monads Lean core has no instance for (e.g. List)
    //   are rejected with a failed-to-synthesize error -- real-Lean parity
    //   (do_notation/p11 OVER_ACCEPT fix).
    match prelude {
        clean_kernel::cli::PreludeMode::Builtin => {
            env.init_monad_list_insts()
                .map_err(|e| anyhow::anyhow!("failed to initialize List monad instances: {e}"))?;
        }
        clean_kernel::cli::PreludeMode::Lean4Core => {
            env.set_lean4_core_strict_monads(true);
        }
    }
    // Register the IO operation axioms (`IO.println`, `IO.print`, `IO.getLine`,
    // IO.FS/Process ops, …) on the check path so it agrees with the
    // codegen/run/lake paths (cmd_compile.rs:348, clean-lake/src/build.rs:543).
    // Without this, a well-typed program such as
    // `def main : IO Unit := IO.println (toString (5 + 5))` fails to elaborate:
    // `IO.println` is parsed as a projection whose receiver `IO` has kind
    // `Type -> Type`, and with no registered `IO.println` constant the
    // dot-notation elaborator falls through to `get_type_name` on that Pi and
    // bails `NotImplemented` (elab_proj.rs:598 → elab_match/helpers.rs:44).
    // Registering the IO axioms (their true Lean types, opaque — identical trust
    // to the run path) resolves the projection before that point. This is an
    // elaboration-completeness fix: the elaborated `main` is still kernel-checked
    // via `add_decl`, and ill-typed IO programs remain rejected.
    env.init_io_ops()
        .map_err(|e| anyhow::anyhow!("failed to initialize IO operations: {e}"))?;
    // Register `ULift` (universe lifting) on the check path. Without it,
    // `ULift.{u} Nat` fails as an UnknownIdent and the failure path silently
    // injects a sorryAx (GAP_SWEEP_2026-07-09 universes/p20). With ULift
    // present, a *partial* universe-instance list such as `ULift.up.{1}`
    // (ULift.up has two level params) is a LOUD, typed `UniverseLevelMismatch`
    // — the intended behavior for an over-/under-specified level list.
    env.init_ulift()
        .map_err(|e| anyhow::anyhow!("failed to initialize ULift: {e}"))?;
    let mut state = ImportCheckState {
        imports_prefer_olean,
        ..ImportCheckState::default()
    };
    let mut outcome = FileCheckOutcome::default();

    check_file_recursive(
        path,
        &mut env,
        &mut state,
        &mut outcome,
        verbose,
        allow_sorry,
        json,
    )?;

    finalize_check_run(
        path,
        &outcome.module,
        outcome.decl_count,
        start.elapsed(),
        outcome.success_count,
        outcome.errors,
        outcome.trust_failures,
        outcome.kernel_failures,
        outcome.structured_failures,
        json,
    )
}

/// Schema tag for the `clean check --parse-only --json` report.
const PARSE_ONLY_REPORT_SCHEMA_VERSION: &str = "Clean-parse-only-report-v1";

/// Cap on the `first_errors` list carried by a parse-only report.
const PARSE_ONLY_MAX_FIRST_ERRORS: usize = 10;

/// Per-file outcome of a parse-only sweep (`clean check --parse-only`).
///
/// MEASUREMENT INTEGRITY (parser pillar, Mathlib parse-rate brick,
/// `docs/plans/ROADMAP_LEAN4_FULL_REPLACEMENT_2026-08-10.md`): a `RawDecl`
/// placeholder is the parser's error-recovery artifact, not a parsed
/// declaration — it always counts as a failure here, never as a parse. A
/// hard error means the file-level parser aborted entirely (e.g. the typed
/// `UniverseOffsetTooLarge` rejection, which deliberately skips `RawDecl`
/// recovery), so no per-declaration counts exist for the file.
#[derive(Debug, Default, PartialEq, Eq)]
pub(crate) struct ParseOnlyCounts {
    /// Leaf declarations seen (namespace/section/mutual bodies flattened).
    pub(crate) decls: usize,
    /// Leaves that parsed to a real surface declaration.
    pub(crate) parse_ok: usize,
    /// Leaves that are `RawDecl` recovery placeholders (parse failures).
    pub(crate) rawdecl_recovered: usize,
    /// 1 when the file-level parse aborted with a hard `ParseError`.
    pub(crate) hard_error: usize,
    /// Parser recovery diagnostics observed (e.g. a tactic-block grammar
    /// failure degraded to a synthetic sorry). These do not subtract from
    /// `parse_ok` — the surrounding declaration still parsed structurally —
    /// but they are honest parser completeness debt, reported separately and
    /// surfaced in `first_errors`.
    pub(crate) recovery_diagnostics: usize,
    /// First error signatures, capped at [`PARSE_ONLY_MAX_FIRST_ERRORS`].
    pub(crate) first_errors: Vec<String>,
}

/// Append an error signature unless the cap is already reached.
fn push_parse_only_error(first_errors: &mut Vec<String>, message: String) {
    if first_errors.len() < PARSE_ONLY_MAX_FIRST_ERRORS {
        first_errors.push(message);
    }
}

/// Count leaf parse outcomes for one surface declaration.
///
/// `Namespace` / `Section` / `Mutual` bodies (and the single-declaration
/// bodies of `open ... in` / `set_option ... in`) are flattened so each inner
/// declaration is classified individually — mirroring how the elaborating
/// check path counts leaf declarations rather than top-level blocks. A
/// recovered `RawDecl` nested inside a namespace therefore still counts as a
/// failure instead of vanishing into a "parsed" container.
fn count_parse_only_leaves(decl: &SurfaceDecl, counts: &mut ParseOnlyCounts) {
    match decl {
        SurfaceDecl::Namespace { decls, .. }
        | SurfaceDecl::Section { decls, .. }
        | SurfaceDecl::Mutual { decls, .. } => {
            for inner in decls {
                count_parse_only_leaves(inner, counts);
            }
        }
        SurfaceDecl::Open {
            body: Some(inner), ..
        }
        | SurfaceDecl::SetOption {
            body: Some(inner), ..
        } => {
            count_parse_only_leaves(inner, counts);
        }
        SurfaceDecl::RawDecl { content, .. } => {
            counts.decls += 1;
            counts.rawdecl_recovered += 1;
            // Signature: the recovered region's leading tokens, whitespace
            // normalized and truncated, so a sweep can aggregate repeats.
            let sig: String = content
                .split_whitespace()
                .collect::<Vec<_>>()
                .join(" ")
                .chars()
                .take(80)
                .collect();
            push_parse_only_error(&mut counts.first_errors, format!("rawdecl: {sig}"));
        }
        _ => {
            counts.decls += 1;
            counts.parse_ok += 1;
        }
    }
}

/// Parse `content` with the same tactic-aware file parser the elaborating
/// check path uses, and classify every leaf declaration WITHOUT elaborating.
pub(crate) fn parse_only_counts(content: &str) -> ParseOnlyCounts {
    let patterns = clean_elab::tactic::builtins::builtin_tactic_patterns();
    let mut counts = ParseOnlyCounts::default();
    match clean_parser::parse_file_with_tactics_diagnostics(content, &patterns) {
        Ok(report) => {
            for decl in &report.decls {
                count_parse_only_leaves(decl, &mut counts);
            }
            for diag in &report.diagnostics {
                counts.recovery_diagnostics += 1;
                let named = match &diag.tactic {
                    Some(tac) => format!("tactic `{tac}`"),
                    None => format!("construct `{}`", diag.construct),
                };
                push_parse_only_error(
                    &mut counts.first_errors,
                    format!(
                        "recovery[{}]: {named} at line {}: {}",
                        diag.code, diag.recovery_start.line, diag.message
                    ),
                );
            }
        }
        Err(err) => {
            counts.hard_error = 1;
            push_parse_only_error(&mut counts.first_errors, format!("hard error: {err}"));
        }
    }
    counts
}

/// JSON payload for `clean check --parse-only --json`.
#[derive(Debug, Serialize)]
struct ParseOnlyReport {
    schema_version: &'static str,
    command: &'static str,
    file: String,
    decls: usize,
    parse_ok: usize,
    rawdecl_recovered: usize,
    hard_error: usize,
    recovery_diagnostics: usize,
    first_errors: Vec<String>,
}

/// `clean check --parse-only`: parse the file, count per-declaration parse
/// outcomes, and report them WITHOUT elaborating or kernel-checking anything.
///
/// This is the measurement command behind `scripts/parser_mathlib_sweep.sh`
/// (the parser pillar's Mathlib parse-rate artifact). It never registers a
/// declaration, never runs a tactic, and never mints any verification
/// verdict — it is a parser coverage meter only. The JSON report (when
/// requested) is always printed before the failure exit, so sweep tooling can
/// consume it regardless of exit status.
pub(crate) fn parse_only_check(path: &Path, json: bool) -> anyhow::Result<()> {
    let content = std::fs::read_to_string(path)
        .map_err(|e| anyhow::anyhow!("failed to read {}: {e}", path.display()))?;
    let counts = parse_only_counts(&content);
    let failed = counts.rawdecl_recovered + counts.hard_error;

    if json {
        let report = ParseOnlyReport {
            schema_version: PARSE_ONLY_REPORT_SCHEMA_VERSION,
            command: "clean check --parse-only",
            file: path.display().to_string(),
            decls: counts.decls,
            parse_ok: counts.parse_ok,
            rawdecl_recovered: counts.rawdecl_recovered,
            hard_error: counts.hard_error,
            recovery_diagnostics: counts.recovery_diagnostics,
            first_errors: counts.first_errors,
        };
        writeln!(
            std::io::stdout(),
            "{}",
            serde_json::to_string_pretty(&report)?
        )?;
    } else {
        let mut out = std::io::stdout();
        let _ = writeln!(
            out,
            "Parsed {} declarations: {} ok, {} RawDecl-recovered, {} hard error, {} recovery diagnostics",
            counts.decls,
            counts.parse_ok,
            counts.rawdecl_recovered,
            counts.hard_error,
            counts.recovery_diagnostics
        );
        for err in &counts.first_errors {
            let _ = writeln!(out, "  {err}");
        }
    }

    if failed > 0 {
        anyhow::bail!("parse-only check: {failed} declaration(s) failed to parse");
    }
    Ok(())
}

/// Recursion state shared across all files (cache + cycle detection).
#[derive(Default)]
struct ImportCheckState {
    /// Set of canonical paths that have already been fully elaborated this run.
    /// Used to avoid quadratic re-elaboration on diamond-shaped import graphs.
    completed: HashSet<PathBuf>,
    /// Set of canonical paths currently being elaborated up the call stack.
    /// Used to detect import cycles.
    in_flight: HashSet<PathBuf>,
    /// Cache of resolved module name -> resolved path.
    resolved_modules: HashMap<String, Option<PathBuf>>,
    /// When set, an `import M.X` whose module has a discoverable prebuilt
    /// `.olean` is loaded from that artifact (via the main-loop `.olean` path)
    /// rather than recursively elaborated from its `.lean` source. Lets a file
    /// inside a large source tree (e.g. Mathlib) be checked against compiled
    /// dependency context. See `--imports-prefer-olean`.
    imports_prefer_olean: bool,
}

/// Accumulator for the outcome of checking the entry file.
///
/// We only surface diagnostics from the entry file; per-import failures bump
/// counts on the entry file's outcome (so exit-code contract still fires) but
/// are also annotated with the originating module so the user sees the chain.
#[derive(Default)]
struct FileCheckOutcome {
    module: String,
    decl_count: usize,
    success_count: usize,
    errors: Vec<String>,
    trust_failures: Vec<String>,
    kernel_failures: Vec<String>,
    structured_failures: Vec<CheckObligationFeedback>,
}

/// Maximum import recursion depth — guards against pathological resolver loops
/// even when cycle detection trips first.
const MAX_IMPORT_DEPTH: usize = 256;

fn check_file_recursive(
    path: &Path,
    env: &mut Environment,
    state: &mut ImportCheckState,
    outcome: &mut FileCheckOutcome,
    verbose: bool,
    allow_sorry: bool,
    json: bool,
) -> anyhow::Result<()> {
    if state.in_flight.len() >= MAX_IMPORT_DEPTH {
        anyhow::bail!(
            "import depth limit ({MAX_IMPORT_DEPTH}) exceeded while checking {}",
            path.display()
        );
    }

    let canonical = std::fs::canonicalize(path).unwrap_or_else(|_| path.to_path_buf());

    if state.completed.contains(&canonical) {
        // Already elaborated into `env` earlier this run; skip.
        return Ok(());
    }
    if !state.in_flight.insert(canonical.clone()) {
        anyhow::bail!(
            "import cycle detected at {}: file is already being elaborated",
            path.display()
        );
    }

    let result = check_file_body(path, env, state, outcome, verbose, allow_sorry, json);

    state.in_flight.remove(&canonical);
    if result.is_ok() {
        state.completed.insert(canonical);
    }
    result
}

fn check_file_body(
    path: &Path,
    env: &mut Environment,
    state: &mut ImportCheckState,
    outcome: &mut FileCheckOutcome,
    verbose: bool,
    allow_sorry: bool,
    json: bool,
) -> anyhow::Result<()> {
    let is_entry_file = state.in_flight.len() == 1;

    let content = std::fs::read_to_string(path)?;
    if verbose {
        println!("Read {} bytes from {:?}", content.len(), path);
    }

    let parse_start = Instant::now();
    let patterns = clean_elab::tactic::builtins::builtin_tactic_patterns();
    // MEASUREMENT INTEGRITY (T0, `docs/plans/TACTICS_TO_100_2026-07-29.md`
    // §RC-Q). `parse_file_with_tactics` DISCARDS the parser's recovery
    // diagnostics. Every tactic whose argument grammar Clean does not support
    // (`set x := e`, `conv_rhs => …`, `conv in p => …`, `module`, `simp [*]`,
    // `simp (config := …)`, `cases … with | _ =>`, `rcases … with -`, a bare
    // `rw`/`unfold`/`revert`, …) therefore recovered the whole `by` block to a
    // SyntheticSorry and the user saw exactly one line — "declaration uses
    // synthetic sorry" — with NOTHING naming the tactic that did nothing. That
    // makes the gap unmeasurable: any coverage script keyed on
    // `UnknownTactic`/`TacticFailed` under-reports it.
    //
    // Reading the report variant and surfacing each recovery as an error makes
    // the class LOUD and countable. It cannot mask a real proof: a recovery
    // event means the tactic block was replaced by a synthetic sorry (or the
    // declaration by a `RawDecl`), so the declaration was already failing —
    // this only attributes the failure.
    let report = clean_parser::parse_file_with_tactics_diagnostics(&content, &patterns)?;
    let decls = report.decls;
    for diag in &report.diagnostics {
        let named = match &diag.tactic {
            Some(tac) => format!("tactic `{tac}`"),
            None => format!("construct `{}`", diag.construct),
        };
        let diagnostic = format!(
            "parser recovery [{}]: unsupported {named} at line {}, column {}: {}",
            diag.code, diag.recovery_start.line, diag.recovery_start.column, diag.message
        );
        let diagnostic = if is_entry_file {
            diagnostic
        } else {
            format!("[{}] {diagnostic}", module_name_for_path(path))
        };
        outcome.errors.push(diagnostic);
    }
    let parse_time = parse_start.elapsed();
    if verbose {
        println!("Parsed {} declarations in {:?}", decls.len(), parse_time);
    }

    let mut file_ctx = FileContext::new();
    let import_search_paths = clean_elab::lake_import_search_paths_for_file(path);
    if verbose && !import_search_paths.is_empty() {
        println!(
            "Discovered {} Lake import search paths",
            import_search_paths.len()
        );
    }
    file_ctx.set_import_search_paths(import_search_paths);

    let module = module_name_for_path(path);
    if is_entry_file {
        outcome.module = module.clone();
    }

    // First pass: collect intra-project imports and recursively elaborate each.
    // We resolve `import M.X.Y` to a `.lean` file in the surrounding project /
    // Lake package tree. If resolution succeeds, we elaborate the imported
    // file BEFORE encountering its `Import` decl in the main loop below — by
    // the time the main loop's import decl is processed by
    // `elaborate_decl_and_register_with_warning`, the declarations from the
    // intra-project import are already present in `env`. External (.olean)
    // imports — mathlib, batteries, etc. — fall through to the existing
    // process_imports_with_search_paths path because we cannot find a .lean
    // file for them inside the project tree.
    for decl in &decls {
        collect_intra_project_imports(decl, path, env, state, outcome, verbose, allow_sorry, json)?;
    }

    // Second pass: regular elaboration of all decls. Intra-project Import
    // decls will be processed by `elaborate_decl_and_register_with_warning`
    // and routed to `process_imports_with_search_paths`. For intra-project
    // .lean files there is no .olean to load, so that path becomes a no-op —
    // which is what we want, because the relevant declarations are already
    // in `env` from the first pass above.
    // Number of leaf declarations that were *counted* by the checker, including
    // those nested inside `namespace`/`section` blocks. A namespace elaborates to
    // a single top-level `decl` yet may contain many leaf declarations; counting
    // the surface `decls.len()` alone would under-report file progress (#3xxx).
    let mut counted_leaf_decls = 0usize;
    for decl in &decls {
        let kernel_failures_before = kernel_check_failure_count();
        let processed_decl = preprocess_decl_with_context(decl, &mut file_ctx);
        // Thread `file_ctx` through elaboration (gap sweep B13): the
        // context-free variant discarded the namespace state mutated by each
        // declaration, so a STANDALONE `open Foo` / `export Foo (x)` was a
        // per-decl no-op — the aliases died with the throwaway ElabCtx and
        // subsequent declarations auto-bound / kernel-failed on the short
        // names (namespaces_scoping/p05,p07,p09,p14,p22). With the context
        // threaded, open/export aliases and file-scope macro/notation
        // registrations persist across the file's declarations (matching the
        // Lean file model), and the Lake-discovered import search paths
        // already stored on `file_ctx` reach `.olean` loading.
        match elaborate_decl_and_register_with_context_and_warning(
            env,
            &processed_decl,
            &mut file_ctx,
        ) {
            Ok(registered) => {
                // Flatten namespace/section/mutual blocks to their leaf
                // declarations so each one is type-checked, counted, and
                // reported individually. Non-block results yield a single leaf.
                let mut leaves: Vec<&ElabResult> = Vec::new();
                registered.result.leaf_decls(&mut leaves);

                if leaves.is_empty() {
                    // Purely administrative (import / set_option / open / #command):
                    // route through the single-result path so `(skipped)` results
                    // remain uncounted exactly as before.
                    let leaf = &registered.result;
                    let warning = registered.warning.clone();
                    process_single_leaf(
                        leaf,
                        warning,
                        env,
                        decl,
                        kernel_failures_before,
                        is_entry_file,
                        &module,
                        &content,
                        verbose,
                        allow_sorry,
                        json,
                        outcome,
                        &mut counted_leaf_decls,
                    );
                } else {
                    // A block (namespace/section/mutual) elaborates and kernel-
                    // checks ALL its inner decls inside the call above, before this
                    // loop runs. Every inner kernel failure therefore (a) has
                    // already incremented the global kernel-failure counter and
                    // (b) surfaces here as an explicit `ElabResult::Failed` leaf,
                    // which `process_single_leaf` reports from its own stored error.
                    //
                    // So the kernel-failure DELTA across the whole block is exactly
                    // accounted for by the `Failed` leaves. Spreading that delta
                    // onto a *successful* sibling (the old "attribute to first leaf"
                    // heuristic) would wrongly mark a passing decl as failed — the
                    // namespace-ABORT regression where `T.a` inherited `T.b`'s
                    // failure. Give every leaf a zero delta (sample the counter
                    // now, after the block has fully elaborated): successful leaves
                    // pass cleanly and each `Failed` leaf carries its own failure.
                    let kernel_before = kernel_check_failure_count();
                    for leaf in leaves {
                        let warning = leaf.declaration_name().and_then(|n| {
                            clean_elab::register::registration_warning_for_name(env, n)
                        });
                        process_single_leaf(
                            leaf,
                            warning,
                            env,
                            decl,
                            kernel_before,
                            is_entry_file,
                            &module,
                            &content,
                            verbose,
                            allow_sorry,
                            json,
                            outcome,
                            &mut counted_leaf_decls,
                        );
                    }
                }
            }
            Err(e) => {
                // Carry the failing declaration's name and start line in the
                // diagnostic so downstream verdict consumers (the tactic-family
                // gates' fail-closed attribution) can attribute the failure
                // positionally instead of falling back to a whole-word name
                // scan — which a goal dump mentioning an unrelated declaration
                // (e.g. a helper's constant inside an unsolved-goal print)
                // poisons into a false failure on a passing decl.
                let named = surface_decl_name(decl)
                    .map(|name| format!("{name}: "))
                    .unwrap_or_default();
                let position = surface_decl_span(decl)
                    .and_then(|span| source_span(&content, span))
                    .map(|span| format!(" at line {}", span.line))
                    .unwrap_or_default();
                let diagnostic = if is_entry_file {
                    format!("{named}elaboration error{position}: {e:?}")
                } else {
                    format!("[{module}] {named}elaboration error{position}: {e:?}")
                };
                outcome
                    .structured_failures
                    .push(check_feedback_from_elab_error(
                        decl,
                        &content,
                        &module,
                        &e,
                        diagnostic.clone(),
                    ));
                outcome.errors.push(diagnostic);
                // A top-level decl that fails to elaborate is still one checked
                // unit; keep it in the "Checked N declarations" tally.
                counted_leaf_decls += 1;
            }
        }
    }

    if is_entry_file {
        // Report the number of leaf declarations actually examined (nested
        // namespace/section members included) rather than the count of
        // top-level surface decls, which collapses each block to 1.
        outcome.decl_count = counted_leaf_decls;
    }

    Ok(())
}

/// Type-check and record a single leaf declaration result against the (already
/// populated) environment, updating the file outcome and the leaf tally.
///
/// `kernel_failures_before` is the kernel-check failure counter sampled before
/// this leaf's elaboration; the delta against the current counter is attributed
/// to this leaf. Administrative `(skipped)` results are not counted.
#[allow(clippy::too_many_arguments)]
fn process_single_leaf(
    leaf: &ElabResult,
    warning: Option<RegistrationWarning>,
    env: &Environment,
    decl: &SurfaceDecl,
    kernel_failures_before: u64,
    is_entry_file: bool,
    module: &str,
    content: &str,
    verbose: bool,
    allow_sorry: bool,
    json: bool,
    outcome: &mut FileCheckOutcome,
    counted_leaf_decls: &mut usize,
) {
    // A `Failed` leaf is an inner declaration (a member of a namespace / section
    // / mutual block) whose elaboration or kernel check already failed. Before
    // the namespace-ABORT fix, such a failure aborted the whole block with `?`
    // and dropped every good sibling; now it surfaces as a counted, reported
    // failure here — exactly as a top-level decl failure does in the caller's
    // `Err` arm. It is NOT registered into the kernel and never counts as a pass.
    if let ElabResult::Failed {
        name,
        decl: inner_decl,
        error,
    } = leaf
    {
        let diagnostic = if is_entry_file {
            format!("{name}: {error}")
        } else {
            format!("[{module}] {name}: {error}")
        };
        outcome.errors.push(diagnostic.clone());
        // Use the inner surface decl (not the enclosing block decl) so the
        // structured failure carries the failing member's own span/diagnostics.
        outcome
            .structured_failures
            .push(check_feedback_from_elab_error(
                inner_decl, content, module, error, diagnostic,
            ));
        // One failing inner decl is one checked unit.
        *counted_leaf_decls += 1;
        return;
    }
    match typecheck_elab_result(leaf, env) {
        Ok(name) => {
            let kernel_failures_delta =
                kernel_check_failure_count().saturating_sub(kernel_failures_before);
            let mut trust_failures = Vec::new();
            let mut kernel_failures = Vec::new();
            let mut success_count = 0;
            // `(skipped)` administrative results never reach the tally; every
            // genuine declaration leaf (pass or fail) is one checked unit.
            if name != "(skipped)" {
                *counted_leaf_decls += 1;
            }
            record_checked_decl(
                &name,
                warning.as_ref(),
                kernel_failures_delta,
                verbose,
                allow_sorry,
                !json && is_entry_file,
                &mut trust_failures,
                &mut kernel_failures,
                &mut success_count,
            );
            // Annotate non-entry diagnostics with the module of origin so a
            // failure can be traced back to the imported file rather than
            // showing only the bare declaration name.
            if is_entry_file {
                outcome.success_count += success_count;
                outcome.trust_failures.extend(trust_failures);
                outcome.kernel_failures.extend(kernel_failures);
            } else {
                outcome.trust_failures.extend(
                    trust_failures
                        .into_iter()
                        .map(|f| format!("[{module}] {f}")),
                );
                outcome.kernel_failures.extend(
                    kernel_failures
                        .into_iter()
                        .map(|f| format!("[{module}] {f}")),
                );
            }
        }
        Err(e) => {
            let diagnostic = if is_entry_file {
                format!("{}: {e}", elab_result_name(leaf))
            } else {
                format!("[{module}] {}: {e}", elab_result_name(leaf))
            };
            outcome.errors.push(diagnostic.clone());
            outcome
                .structured_failures
                .push(check_feedback_from_message(
                    decl,
                    content,
                    module,
                    CheckFailureReason::KernelValidation,
                    diagnostic,
                ));
            // A leaf that fails kernel validation is still a checked unit.
            *counted_leaf_decls += 1;
        }
    }
}

/// Walk a parsed declaration looking for `import M.X.Y` statements that resolve
/// to an intra-project `.lean` file, and recursively elaborate those files.
///
/// External imports (mathlib, batteries, proofwidgets, ...) are left for the
/// existing `process_imports_with_search_paths` path which handles `.olean`
/// loading and may silently no-op when the artifact is absent (the audit's
/// "mathlib coverage is a separate item" note).
fn collect_intra_project_imports(
    decl: &SurfaceDecl,
    parent_path: &Path,
    env: &mut Environment,
    state: &mut ImportCheckState,
    outcome: &mut FileCheckOutcome,
    verbose: bool,
    allow_sorry: bool,
    json: bool,
) -> anyhow::Result<()> {
    match decl {
        SurfaceDecl::Import { paths, .. } => {
            for module_path in paths {
                if module_path.is_empty() {
                    continue;
                }
                let module_name = module_path.join(".");
                // Lean's import model: the file under check elaborates from
                // source, but its imports load from prebuilt `.olean`s. When
                // `--imports-prefer-olean` is set and a compiled artifact for
                // this module is discoverable, skip source recursion entirely —
                // the main elaboration loop's `Import` decl then routes to
                // `process_imports_with_search_paths`, which loads the `.olean`.
                // Without this, checking a file that lives *inside* a source tree
                // (e.g. one Mathlib module) drags in the whole transitive source
                // closure because every `import Mathlib.X` resolves to a sibling
                // `.lean`.
                if state.imports_prefer_olean
                    && clean_elab::olean_available_for_module(&module_name, parent_path)
                {
                    if verbose {
                        println!(
                            "Import `{module_name}` has a prebuilt .olean; loading it instead of \
                             elaborating source (--imports-prefer-olean)"
                        );
                    }
                    continue;
                }
                let resolved = resolve_import_path(&module_name, parent_path, state);
                if let Some(import_file) = resolved {
                    if verbose {
                        println!(
                            "Resolved intra-project import `{module_name}` -> {}",
                            import_file.display()
                        );
                    }
                    check_file_recursive(
                        &import_file,
                        env,
                        state,
                        outcome,
                        verbose,
                        allow_sorry,
                        json,
                    )?;
                }
            }
        }
        // Namespaces/sections may wrap imports in unusual files; descend.
        SurfaceDecl::Namespace { decls, .. }
        | SurfaceDecl::Section { decls, .. }
        | SurfaceDecl::Mutual { decls, .. } => {
            for inner in decls {
                collect_intra_project_imports(
                    inner,
                    parent_path,
                    env,
                    state,
                    outcome,
                    verbose,
                    allow_sorry,
                    json,
                )?;
            }
        }
        SurfaceDecl::SetOption {
            body: Some(body), ..
        }
        | SurfaceDecl::Open {
            body: Some(body), ..
        } => {
            collect_intra_project_imports(
                body,
                parent_path,
                env,
                state,
                outcome,
                verbose,
                allow_sorry,
                json,
            )?;
        }
        _ => {}
    }
    Ok(())
}

/// Resolve a Lean module name (e.g. `Mathbot.ResearchProgram`) to a `.lean`
/// file on disk, looking only within the surrounding project tree.
///
/// Lookup order:
/// 1. The nearest Lake root parent of `parent_path` (project source root).
/// 2. The walked parents of `parent_path` itself (covers ad-hoc layouts).
/// 3. `.lake/packages/<pkg>/` siblings for cross-package intra-project imports.
///
/// Returns `None` if the module appears to be external (e.g. `Mathlib.X.Y`,
/// `Batteries.X.Y`, `Init.X.Y`) — those keep their existing `.olean` flow.
fn resolve_import_path(
    module: &str,
    parent_path: &Path,
    state: &mut ImportCheckState,
) -> Option<PathBuf> {
    if let Some(cached) = state.resolved_modules.get(module) {
        return cached.clone();
    }
    // Delegate to the single shared resolver in `clean-elab` so the codegen /
    // native-build path (cmd_compile.rs) and this check path agree on lookup.
    let resolved = clean_elab::resolve_intra_project_import(module, parent_path);
    state
        .resolved_modules
        .insert(module.to_owned(), resolved.clone());
    resolved
}

fn check_file_lock() -> &'static Mutex<()> {
    static LOCK: OnceLock<Mutex<()>> = OnceLock::new();
    LOCK.get_or_init(|| Mutex::new(()))
}

struct TrustCounterScope;

impl TrustCounterScope {
    fn enter() -> Self {
        // `clean check` is per-file, so start each run from a clean trust ledger.
        reset_sorry_counter();
        reset_kernel_check_counter();
        Self
    }
}

impl Drop for TrustCounterScope {
    fn drop(&mut self) {
        reset_sorry_counter();
        reset_kernel_check_counter();
    }
}

fn record_checked_decl(
    name: &str,
    warning: Option<&RegistrationWarning>,
    kernel_failures_delta: u64,
    verbose: bool,
    allow_sorry: bool,
    emit_warnings: bool,
    trust_failures: &mut Vec<String>,
    kernel_failures: &mut Vec<String>,
    success_count: &mut usize,
) {
    if let Some(warning) = warning {
        // With --allow-sorry, sorry-based warnings are counted as passes.
        // This is used by the Mathverse Engine formalization pipeline to check
        // type signatures without requiring complete proofs.
        let is_sorry = matches!(
            warning.kind,
            RegistrationWarningKind::ExplicitSorry | RegistrationWarningKind::SyntheticSorry
        );
        if allow_sorry && is_sorry {
            if verbose && name != "(skipped)" {
                let _ = writeln!(std::io::stdout(), "  \u{2713} {name} (sorry allowed)");
            }
            if name != "(skipped)" {
                *success_count += 1;
            }
            return;
        }
        if emit_warnings {
            let _ = emit_registration_warning(&mut std::io::stdout(), warning);
        }
        trust_failures.push(format!(
            "{}: declaration uses {}",
            warning.decl_name,
            registration_warning_label(&warning.kind)
        ));
        if verbose && name != "(skipped)" {
            let _ = writeln!(
                std::io::stdout(),
                "  \u{2717} {name} ({})",
                registration_warning_label(&warning.kind)
            );
        }
        return;
    }
    if kernel_failures_delta > 0 {
        kernel_failures.push(format!(
            "{name}: kernel check failures: {kernel_failures_delta}"
        ));
        if verbose && name != "(skipped)" {
            let _ = writeln!(std::io::stdout(), "  \u{2717} {name} (kernel check)");
        }
        return;
    }
    // Skipped declarations (import, set_option, open) are administrative —
    // counting them as "passed" inflates the pass count (#3078).
    if name == "(skipped)" {
        return;
    }
    if verbose {
        let _ = writeln!(std::io::stdout(), "  \u{2713} {name}");
    }
    *success_count += 1;
}

fn emit_registration_warning(
    out: &mut impl Write,
    warning: &RegistrationWarning,
) -> std::io::Result<()> {
    writeln!(
        out,
        "warning: declaration '{}' uses {}",
        warning.decl_name,
        registration_warning_label(&warning.kind)
    )
}

pub(crate) fn emit_check_summary(
    out: &mut impl Write,
    decl_count: usize,
    total_time: Duration,
    success_count: usize,
    failed_count: usize,
) -> std::io::Result<()> {
    writeln!(
        out,
        "Checked {} declarations in {:?}",
        decl_count, total_time
    )?;
    // Always emit "N passed, M failed" so external parsers (parse_lean) can
    // classify the result without exit-code heuristics (#3078).
    writeln!(out, "  {success_count} passed, {failed_count} failed")
}

fn registration_warning_label(kind: &RegistrationWarningKind) -> &'static str {
    match kind {
        RegistrationWarningKind::ExplicitSorry => "explicit sorry",
        RegistrationWarningKind::SyntheticSorry => "synthetic sorry",
        RegistrationWarningKind::TrustedArith => "trustedArith",
        RegistrationWarningKind::TrustedAy => "trustedAy",
    }
}

fn finalize_check_run(
    path: &Path,
    module: &str,
    decl_count: usize,
    total_time: Duration,
    success_count: usize,
    errors: Vec<String>,
    trust_failures: Vec<String>,
    kernel_failures: Vec<String>,
    structured_failures: Vec<CheckObligationFeedback>,
    json: bool,
) -> anyhow::Result<()> {
    let kernel_failures_total = kernel_check_failure_count();
    let failed_count = errors.len() + trust_failures.len() + kernel_failures.len();

    if json {
        let report = CheckReport {
            schema_version: CHECK_REPORT_SCHEMA_VERSION,
            command: "clean check",
            file: path.display().to_string(),
            module: module.to_owned(),
            status: if failed_count == 0 { "pass" } else { "fail" },
            decl_count,
            success_count,
            failed_count,
            trust_summary: CheckTrustSummary {
                sorry_axioms: sorry_count(),
                kernel_check_failures: kernel_failures_total,
            },
            errors,
            trust_failures,
            kernel_failures,
            proof_state_feedback: structured_failures,
        };
        writeln!(
            std::io::stdout(),
            "{}",
            serde_json::to_string_pretty(&report)?
        )?;
        if failed_count == 0 {
            return Ok(());
        }
        anyhow::bail!("check failed")
    }

    let mut out = std::io::stdout();
    let _ = emit_check_summary(
        &mut out,
        decl_count,
        total_time,
        success_count,
        failed_count,
    );
    let _ = emit_trust_summary(&mut out, sorry_count(), kernel_failures_total);

    if errors.is_empty() && trust_failures.is_empty() && kernel_failures.is_empty() {
        return Ok(());
    }

    let _ = emit_check_failures(&mut out, &errors, &trust_failures, &kernel_failures);
    anyhow::bail!("check failed")
}

#[derive(Debug, Serialize)]
struct CheckReport {
    schema_version: &'static str,
    command: &'static str,
    file: String,
    module: String,
    status: &'static str,
    decl_count: usize,
    success_count: usize,
    failed_count: usize,
    trust_summary: CheckTrustSummary,
    errors: Vec<String>,
    trust_failures: Vec<String>,
    kernel_failures: Vec<String>,
    proof_state_feedback: Vec<CheckObligationFeedback>,
}

#[derive(Debug, Serialize)]
struct CheckTrustSummary {
    sorry_axioms: u64,
    kernel_check_failures: u64,
}

#[derive(Debug, Serialize)]
struct CheckObligationFeedback {
    declaration: Option<String>,
    module: String,
    source_span: Option<AgentSourceSpan>,
    blocking_reason: String,
    diagnostic_text: String,
    normalized_goal: Option<String>,
    normalized_proof_state: Option<CheckProofStateSnapshot>,
    diagnostics: Vec<AgentDiagnostic>,
}

#[derive(Debug, Serialize)]
struct CheckProofStateSnapshot {
    goal_count: usize,
    goals: Vec<CheckGoalSnapshot>,
    text: String,
}

#[derive(Debug, Serialize)]
struct CheckGoalSnapshot {
    target: String,
    hypotheses: Vec<CheckHypothesisSnapshot>,
}

#[derive(Debug, Serialize)]
struct CheckHypothesisSnapshot {
    name: String,
    #[serde(rename = "type")]
    type_text: Option<String>,
}

enum CheckFailureReason {
    Elaboration,
    Tactic,
    KernelValidation,
}

impl CheckFailureReason {
    fn as_str(&self) -> &'static str {
        match self {
            Self::Elaboration => "elaboration_failed",
            Self::Tactic => "tactic_failed",
            Self::KernelValidation => "kernel_validation_failed",
        }
    }
}

fn check_feedback_from_elab_error(
    decl: &SurfaceDecl,
    source: &str,
    module: &str,
    error: &clean_elab::ElabError,
    diagnostic_text: String,
) -> CheckObligationFeedback {
    let span = surface_decl_span(decl).and_then(|span| source_span(source, span));
    let proof_state = normalized_proof_state_for_decl(decl, source);
    let diagnostics = error.agent_diagnostics();
    let reason = match error {
        clean_elab::ElabError::TacticFailed(tactic_error) => {
            blocking_reason_for_tactic(tactic_error)
        }
        _ => diagnostics
            .first()
            .map(|diagnostic| diagnostic.code.clone())
            .unwrap_or_else(|| CheckFailureReason::Elaboration.as_str().to_owned()),
    };

    CheckObligationFeedback {
        declaration: surface_decl_name(decl),
        module: module.to_owned(),
        source_span: span,
        blocking_reason: reason,
        diagnostic_text,
        normalized_goal: proof_state
            .as_ref()
            .and_then(|state| state.goals.first())
            .map(|goal| goal.target.clone()),
        normalized_proof_state: proof_state,
        diagnostics,
    }
}

fn check_feedback_from_message(
    decl: &SurfaceDecl,
    source: &str,
    module: &str,
    reason: CheckFailureReason,
    diagnostic_text: String,
) -> CheckObligationFeedback {
    let span = surface_decl_span(decl).and_then(|span| source_span(source, span));
    let proof_state = normalized_proof_state_for_decl(decl, source);
    CheckObligationFeedback {
        declaration: surface_decl_name(decl),
        module: module.to_owned(),
        source_span: span,
        blocking_reason: reason.as_str().to_owned(),
        diagnostic_text,
        normalized_goal: proof_state
            .as_ref()
            .and_then(|state| state.goals.first())
            .map(|goal| goal.target.clone()),
        normalized_proof_state: proof_state,
        diagnostics: Vec::new(),
    }
}

fn blocking_reason_for_tactic(error: &TacticError) -> String {
    match error {
        TacticError::NoGoals => "no_active_goal",
        TacticError::TypeMismatch { .. } => "type_mismatch",
        TacticError::GoalMismatch(_) => "goal_mismatch",
        TacticError::UnknownIdent(_) => "unknown_identifier",
        TacticError::UnknownTactic(_) => "unknown_tactic",
        TacticError::TypeCheckFailed(_) => "type_check_failed",
        TacticError::UnificationFailed(_) => "unification_failed",
        TacticError::HypothesisNotFound(_) => "missing_hypothesis",
        TacticError::MissingArgument { .. } => "missing_argument",
        TacticError::NoProgress { .. } => "no_progress",
        TacticError::RewriteNoMatch { .. } => "rewrite_no_match",
        TacticError::RewriteProofLiftFailed { .. } => "rewrite_proof_lift_failed",
        TacticError::EnvironmentMissing { .. } => "missing_environment_constant",
        TacticError::InstanceSynthesisFailed { .. } => "instance_synthesis",
        TacticError::ArithmeticFailed { .. } => "arithmetic_certification",
        TacticError::UnfoldFailed { .. } => "unfold_failed",
        TacticError::Timeout { .. } => "timeout",
        TacticError::AllTacticsFailed { .. } => "tactic_combinator_failed",
        TacticError::UnsolvedGoals { .. } => "unsolved_goals",
        TacticError::DepthExceeded { .. } => "search_depth_exceeded",
        TacticError::SearchExhausted { .. } => "search_exhausted",
        TacticError::SmtFailed { .. } => "smt_failed",
        TacticError::BridgeFailed { .. } => "solver_bridge_failed",
        TacticError::OracleFailed { .. } => "oracle_failed",
        TacticError::RuleApplicationFailed { .. } => "rule_application_failed",
        TacticError::InvalidTarget { .. } => "invalid_target",
        TacticError::ElaborationFailed { .. } => "tactic_elaboration_failed",
        TacticError::UpstreamElabError { .. } => "upstream_elaboration_failed",
        TacticError::ProofNotProduced => "proof_not_produced",
        TacticError::ParseFailed { .. } => "tactic_parse_failed",
        _ => CheckFailureReason::Tactic.as_str(),
    }
    .to_owned()
}

fn normalized_proof_state_for_decl(
    decl: &SurfaceDecl,
    source: &str,
) -> Option<CheckProofStateSnapshot> {
    let (target, hypotheses) = match decl {
        SurfaceDecl::Theorem { binders, ty, .. } => (
            Some(normalize_source_snippet(source, ty.span())),
            binder_hypotheses(binders, source),
        ),
        SurfaceDecl::Def { binders, ty, .. } => (
            ty.as_ref()
                .map(|ty| normalize_source_snippet(source, ty.span())),
            binder_hypotheses(binders, source),
        ),
        SurfaceDecl::Example { binders, ty, .. } => (
            ty.as_ref()
                .map(|ty| normalize_source_snippet(source, ty.span())),
            binder_hypotheses(binders, source),
        ),
        SurfaceDecl::Axiom { binders, ty, .. } | SurfaceDecl::Opaque { binders, ty, .. } => (
            Some(normalize_source_snippet(source, ty.span())),
            binder_hypotheses(binders, source),
        ),
        SurfaceDecl::Namespace { decls, .. }
        | SurfaceDecl::Section { decls, .. }
        | SurfaceDecl::Mutual { decls, .. } => {
            return decls
                .iter()
                .find_map(|inner| normalized_proof_state_for_decl(inner, source));
        }
        SurfaceDecl::SetOption {
            body: Some(body), ..
        }
        | SurfaceDecl::Open {
            body: Some(body), ..
        } => return normalized_proof_state_for_decl(body, source),
        _ => (None, Vec::new()),
    };

    let target = target?;
    let goal = CheckGoalSnapshot {
        target: target.clone(),
        hypotheses,
    };
    let text = format_goal_snapshot(&goal);
    Some(CheckProofStateSnapshot {
        goal_count: 1,
        goals: vec![goal],
        text,
    })
}

fn binder_hypotheses(binders: &[SurfaceBinder], source: &str) -> Vec<CheckHypothesisSnapshot> {
    binders
        .iter()
        .map(|binder| CheckHypothesisSnapshot {
            name: binder.name.clone(),
            type_text: binder
                .ty
                .as_ref()
                .map(|ty| normalize_source_snippet(source, ty.span())),
        })
        .collect()
}

fn format_goal_snapshot(goal: &CheckGoalSnapshot) -> String {
    let mut text = String::new();
    for hyp in &goal.hypotheses {
        match &hyp.type_text {
            Some(ty) => {
                let _ = writeln!(text, "{} : {}", hyp.name, ty);
            }
            None => {
                let _ = writeln!(text, "{} : <unknown>", hyp.name);
            }
        }
    }
    let _ = write!(text, "|- {}", goal.target);
    text
}

fn normalize_source_snippet(source: &str, span: Span) -> String {
    source
        .get(span.start..span.end)
        .unwrap_or_default()
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ")
}

fn source_span(source: &str, span: Span) -> Option<AgentSourceSpan> {
    if span.end < span.start || span.start > source.len() {
        return None;
    }
    let (line, column) = line_column_for_offset(source, span.start);
    Some(AgentSourceSpan {
        start: span.start,
        end: span.end.min(source.len()),
        line,
        column,
    })
}

fn line_column_for_offset(source: &str, offset: usize) -> (u32, u32) {
    let mut line = 1u32;
    let mut column = 1u32;
    for (idx, ch) in source.char_indices() {
        if idx >= offset {
            break;
        }
        if ch == '\n' {
            line += 1;
            column = 1;
        } else {
            column += 1;
        }
    }
    (line, column)
}

fn module_name_for_path(path: &Path) -> String {
    path.with_extension("")
        .components()
        .filter_map(|component| component.as_os_str().to_str())
        .filter(|part| !part.is_empty() && *part != "." && *part != "/")
        .collect::<Vec<_>>()
        .join(".")
}

fn surface_decl_name(decl: &SurfaceDecl) -> Option<String> {
    match decl {
        SurfaceDecl::Def { name, .. }
        | SurfaceDecl::Theorem { name, .. }
        | SurfaceDecl::Axiom { name, .. }
        | SurfaceDecl::Opaque { name, .. }
        | SurfaceDecl::Inductive { name, .. }
        | SurfaceDecl::Coinductive { name, .. }
        | SurfaceDecl::Structure { name, .. }
        | SurfaceDecl::Class { name, .. }
        | SurfaceDecl::Namespace { name, .. } => Some(name.clone()),
        SurfaceDecl::Instance { name, .. } => name.clone(),
        SurfaceDecl::Section { name, .. } => name.clone(),
        SurfaceDecl::Print { name, .. } => Some(name.clone()),
        SurfaceDecl::DeclareSyntaxCat { name, .. } => Some(name.clone()),
        SurfaceDecl::Syntax { name, .. } | SurfaceDecl::MacroRules { name, .. } => name.clone(),
        SurfaceDecl::SetOption {
            body: Some(body), ..
        }
        | SurfaceDecl::Open {
            body: Some(body), ..
        } => surface_decl_name(body),
        _ => None,
    }
}

fn surface_decl_span(decl: &SurfaceDecl) -> Option<Span> {
    match decl {
        SurfaceDecl::Def { span, .. }
        | SurfaceDecl::Theorem { span, .. }
        | SurfaceDecl::Axiom { span, .. }
        | SurfaceDecl::Opaque { span, .. }
        | SurfaceDecl::Inductive { span, .. }
        | SurfaceDecl::Coinductive { span, .. }
        | SurfaceDecl::Codata { span, .. }
        | SurfaceDecl::Codef { span, .. }
        | SurfaceDecl::Structure { span, .. }
        | SurfaceDecl::Class { span, .. }
        | SurfaceDecl::Instance { span, .. }
        | SurfaceDecl::Example { span, .. }
        | SurfaceDecl::Import { span, .. }
        | SurfaceDecl::Namespace { span, .. }
        | SurfaceDecl::Section { span, .. }
        | SurfaceDecl::UniverseDecl { span, .. }
        | SurfaceDecl::Variable { span, .. }
        | SurfaceDecl::Open { span, .. }
        | SurfaceDecl::Export { span, .. }
        | SurfaceDecl::DerivingInstance { span, .. }
        | SurfaceDecl::Check { span, .. }
        | SurfaceDecl::Eval { span, .. }
        | SurfaceDecl::Print { span, .. }
        | SurfaceDecl::Mutual { span, .. }
        | SurfaceDecl::Syntax { span, .. }
        | SurfaceDecl::DeclareSyntaxCat { span, .. }
        | SurfaceDecl::Macro { span, .. }
        | SurfaceDecl::MacroRules { span, .. }
        | SurfaceDecl::Notation { span, .. }
        | SurfaceDecl::Elab { span, .. }
        | SurfaceDecl::RawDecl { span, .. }
        | SurfaceDecl::Attribute { span, .. }
        | SurfaceDecl::SetOption { span, .. }
        | SurfaceDecl::DeclareAesopRuleSets { span, .. }
        | SurfaceDecl::LibraryNote { span, .. } => Some(*span),
    }
}

fn emit_trust_summary(
    out: &mut impl Write,
    sorry: u64,
    kernel_failures: u64,
) -> std::io::Result<()> {
    if sorry == 0 && kernel_failures == 0 {
        return Ok(());
    }
    writeln!(out, "Trust summary:")?;
    if sorry > 0 {
        writeln!(out, "  sorry axioms: {sorry}")?;
    }
    if kernel_failures > 0 {
        writeln!(out, "  kernel check failures: {kernel_failures}")?;
    }
    Ok(())
}

fn emit_check_failures(
    out: &mut impl Write,
    errors: &[String],
    trust_failures: &[String],
    kernel_failures: &[String],
) -> std::io::Result<()> {
    writeln!(out, "\nErrors:")?;
    for err in errors {
        writeln!(out, "  ✗ {err}")?;
    }
    for failure in trust_failures {
        writeln!(out, "  ✗ {failure}")?;
    }
    for failure in kernel_failures {
        writeln!(out, "  ✗ {failure}")?;
    }
    Ok(())
}

fn typecheck_elab_result(result: &ElabResult, env: &Environment) -> Result<String, String> {
    // A `Failed` leaf already failed elaboration/kernel checking; never report it
    // as a (false) pass. Normal flow short-circuits `Failed` before reaching here
    // (see `process_single_leaf`), but guard defensively so it can never slip
    // through as `Ok`.
    if let ElabResult::Failed { name, error, .. } = result {
        return Err(format!("{name}: {error}"));
    }
    if matches!(
        result,
        ElabResult::Skipped | ElabResult::Command(_) | ElabResult::Multiple(_)
    ) {
        return Ok("(skipped)".to_string());
    }
    let tc = TypeChecker::with_mode(env, env.mode());
    validate_decl_read_only(env, &tc, result).map(|_| elab_result_name(result))
}

fn elab_result_name(result: &ElabResult) -> String {
    match result {
        ElabResult::Definition { name, .. }
        | ElabResult::Theorem { name, .. }
        | ElabResult::Axiom { name, .. }
        | ElabResult::Opaque { name, .. }
        | ElabResult::Structure { name, .. }
        | ElabResult::Instance { name, .. }
        | ElabResult::Inductive { name, .. } => name.to_string(),
        // Anonymous by construction (Lean checks then discards it); it is
        // still ONE genuinely checked declaration and must be counted (B02).
        ElabResult::Example { .. } => "example".to_string(),
        ElabResult::MutualInductive { decl, .. } => decl
            .types
            .first()
            .map_or_else(|| "(mutual inductive)".to_string(), |t| t.name.to_string()),
        // A failing inner decl carries its own best-effort name; surface it so a
        // diagnostic that does reach this path is attributed to the right decl.
        ElabResult::Failed { name, .. } => name.clone(),
        ElabResult::Command(_) | ElabResult::Multiple(_) | ElabResult::Skipped => {
            "(skipped)".to_string()
        }
    }
}

pub(crate) fn verify_c_file(
    path: &PathBuf,
    verbose: bool,
    fail_unknown: bool,
) -> anyhow::Result<()> {
    let start = Instant::now();
    let source = std::fs::read_to_string(path)?;
    if verbose {
        println!("Read {} bytes from {:?}", source.len(), path);
    }

    let mut parser = CParser::new();
    let functions = parser.parse_translation_unit_with_specs(&source)?;

    if functions.is_empty() {
        anyhow::bail!("No functions found in {path:?}");
    }

    let mut total_vcs = 0;
    let mut proved = 0;
    let mut unverified = 0;
    let mut failed = 0;
    let mut unknown = 0;

    for vf in functions {
        if verbose {
            println!("Verifying {}...", vf.name);
        }

        let summary = vf.verify();
        total_vcs += summary.total;
        proved += summary.proved;
        unverified += summary.unverified;
        failed += summary.failed;
        unknown += summary.unknown;

        println!(
            "Function: {} ({} VCs: {} proved, {} unverified, {} failed, {} unknown)",
            vf.name,
            summary.total,
            summary.proved,
            summary.unverified,
            summary.failed,
            summary.unknown
        );

        if verbose {
            for (desc, status) in &summary.details {
                let marker = match status {
                    ProofStatus::KernelVerified(_) | ProofStatus::StructuralProved => "✓",
                    ProofStatus::Unverified(_) => "~",
                    ProofStatus::Failed(_) => "✗",
                    ProofStatus::Unknown => "?",
                };
                println!("  {marker} {desc}");
            }
        }
    }

    println!(
        "C verification summary: {} VCs ({} proved, {} unverified, {} failed, {} unknown) in {:?}",
        total_vcs,
        proved,
        unverified,
        failed,
        unknown,
        start.elapsed()
    );

    // SOUNDNESS (hole 11): fail-closed gate. A `failed` (refuted) or `unknown`
    // (unproved / unsupported gap) obligation means the program is NOT
    // verified. `unknown` must fail unconditionally — it previously passed
    // whenever `fail_unknown` was false, so a function with an un-generated or
    // unsupported obligation (total small, all trivially proved) certified.
    // `unverified` is the confirmed-sound SMT-UNSAT-without-proof-term case and
    // is accepted unless `fail_unknown` tightens it further.
    // See docs/SOUNDNESS_FINDINGS_CLEAN_C_SEM_2026-07.md holes 3,11.
    if failed > 0 || unknown > 0 || (fail_unknown && unverified > 0) {
        anyhow::bail!(format!(
            "Verification incomplete: {failed} failed, {unknown} unknown, {unverified} unverified obligations"
        ));
    }

    Ok(())
}

pub(crate) fn eval_expr(expr_str: &str, verbose: bool) -> anyhow::Result<()> {
    let start = Instant::now();

    // Parse
    let surface = parse_expr(expr_str)?;
    if verbose {
        println!("Parsed: {surface:?}");
    }

    // Elaborate
    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);
    let kernel_expr = ctx.elaborate(&surface)?;
    if verbose {
        println!("Elaborated: {kernel_expr:?}");
    }

    // Type check
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&kernel_expr)?;

    let elapsed = start.elapsed();

    // Output
    println!("Expression: {expr_str}");
    println!("Type: {ty:?}");
    if verbose {
        println!("Checked in {elapsed:?}");
    }

    Ok(())
}

/// Resolve the project directory from the --dir option or current directory
pub(crate) fn resolve_project_dir(dir: Option<PathBuf>) -> anyhow::Result<PathBuf> {
    match dir {
        Some(d) => {
            let abs_path = if d.is_absolute() {
                d
            } else {
                std::env::current_dir()?.join(&d)
            };
            if !abs_path.exists() {
                anyhow::bail!("Directory does not exist: {}", abs_path.display());
            }
            Ok(abs_path)
        }
        None => Ok(std::env::current_dir()?),
    }
}

#[cfg(test)]
mod tests {
    use super::{parse_only_counts, typecheck_elab_result};
    use clean_elab::ElabResult;
    use clean_kernel::{Environment, Expr, Name};

    /// Parse-only counting: a file with two good decls and one malformed decl
    /// classifies the malformed region as a `RawDecl` recovery failure, never
    /// as a parse (soundness of the parse-rate measurement).
    #[test]
    fn test_parse_only_counts_good_and_rawdecl_recovered() {
        // Same shape as the parser's own recovery fixture
        // (`test_file_error_recovery_skips_malformed_decls`).
        let counts = parse_only_counts("def foo := 1\ndef ??? := !!!\ndef bar := 2\n");
        assert_eq!(counts.hard_error, 0, "recovered file must not hard-error");
        assert!(
            counts.rawdecl_recovered >= 1,
            "malformed decl must surface as a RawDecl failure, got {counts:?}"
        );
        assert!(
            counts.parse_ok >= 2,
            "both valid defs must count as parsed, got {counts:?}"
        );
        assert_eq!(
            counts.decls,
            counts.parse_ok + counts.rawdecl_recovered,
            "every counted leaf is either a parse or a RawDecl failure: {counts:?}"
        );
        assert!(
            counts
                .first_errors
                .iter()
                .any(|e| e.starts_with("rawdecl: ")),
            "RawDecl failures must contribute an error signature, got {:?}",
            counts.first_errors
        );
    }

    /// Parse-only counting: a typed `UniverseOffsetTooLarge` rejection skips
    /// `RawDecl` recovery and aborts the whole file — reported as a hard
    /// error with zero per-declaration counts.
    #[test]
    fn test_parse_only_counts_hard_error_aborts_file() {
        let counts = parse_only_counts("def x : Sort (u + 9999) := x\n");
        assert_eq!(
            counts.hard_error, 1,
            "expected a hard error, got {counts:?}"
        );
        assert_eq!(counts.decls, 0, "hard error yields no decl counts");
        assert_eq!(counts.parse_ok, 0, "hard error yields no parses");
        assert!(
            counts
                .first_errors
                .iter()
                .any(|e| e.starts_with("hard error: ")),
            "hard error must contribute an error signature, got {:?}",
            counts.first_errors
        );
    }

    /// Parse-only counting flattens namespaces: a `RawDecl` recovered inside
    /// a namespace still counts as a failure, and the good sibling as a parse.
    #[test]
    fn test_parse_only_counts_flattens_namespace_leaves() {
        // Same fixture as the parser's own in-namespace recovery test
        // (`test_namespace_body_error_recovery_keeps_following_decl_scoped`):
        // the RawDecl lands INSIDE the Namespace node, never at top level.
        let counts = parse_only_counts("namespace Foo\n  def bad := \n  def good := 1\nend Foo\n");
        assert_eq!(counts.hard_error, 0, "recovered file must not hard-error");
        assert!(
            counts.rawdecl_recovered >= 1,
            "in-namespace RawDecl must count as a failure, got {counts:?}"
        );
        assert!(
            counts.parse_ok >= 1,
            "the good sibling must count as parsed, got {counts:?}"
        );
    }

    /// A fully valid file counts every declaration as parse-OK with no
    /// failures and no error signatures.
    #[test]
    fn test_parse_only_counts_all_valid_file() {
        let counts = parse_only_counts("def a := 1\ndef b := 2\naxiom c : Type\n");
        assert_eq!(counts.decls, 3, "expected 3 leaves, got {counts:?}");
        assert_eq!(counts.parse_ok, 3, "all decls must parse, got {counts:?}");
        assert_eq!(counts.rawdecl_recovered, 0, "no RawDecl expected");
        assert_eq!(counts.hard_error, 0, "no hard error expected");
        assert!(
            counts.first_errors.is_empty(),
            "no error signatures expected, got {:?}",
            counts.first_errors
        );
    }

    #[test]
    fn typecheck_elab_result_rejects_non_prop_theorem() {
        let env = Environment::try_with_prelude().expect("prelude should initialize");
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let decl = ElabResult::Theorem {
            name: Name::from_string("bad"),
            universe_params: vec![],
            ty: nat,
            proof: nat_zero,
            modifiers: clean_parser::DeclModifiers::default(),
        };
        let err = typecheck_elab_result(&decl, &env)
            .expect_err("theorem with Nat type should be rejected");
        assert!(
            err.contains("type must be a Prop"),
            "expected Prop gate error, got: {err}"
        );
    }

    #[test]
    fn typecheck_elab_result_accepts_valid_prop_theorem() {
        let env = Environment::try_with_prelude().expect("prelude should initialize");
        // theorem trivial : True := True.intro
        let true_ty = Expr::const_(Name::from_string("True"), vec![]);
        let true_intro = Expr::const_(Name::from_string("True.intro"), vec![]);
        let decl = ElabResult::Theorem {
            name: Name::from_string("trivial"),
            universe_params: vec![],
            ty: true_ty,
            proof: true_intro,
            modifiers: clean_parser::DeclModifiers::default(),
        };
        typecheck_elab_result(&decl, &env).expect("theorem with Prop type should be accepted");
    }

    #[test]
    fn typecheck_elab_result_skipped_passes() {
        let env = Environment::try_with_prelude().expect("prelude should initialize");
        let name =
            typecheck_elab_result(&ElabResult::Skipped, &env).expect("skipped should succeed");
        assert_eq!(name, "(skipped)");
    }

    #[test]
    fn emit_registration_warning_explicit() {
        use super::{emit_registration_warning, RegistrationWarning, RegistrationWarningKind};
        use clean_kernel::env::DeclarationTrustSummary;

        let w = RegistrationWarning {
            decl_name: Name::from_string("my_thm"),
            kind: RegistrationWarningKind::ExplicitSorry,
            summary: DeclarationTrustSummary {
                has_explicit_sorry: true,
                has_synthetic_sorry: false,
                trusted_arith_count: 0,
                trusted_ay_count: 0,
            },
        };
        let mut buf = Vec::new();
        emit_registration_warning(&mut buf, &w).expect("write should succeed");
        let output = String::from_utf8(buf).expect("valid utf8");
        assert_eq!(
            output, "warning: declaration 'my_thm' uses explicit sorry\n",
            "explicit sorry warning format mismatch"
        );
    }

    #[test]
    fn emit_registration_warning_synthetic() {
        use super::{emit_registration_warning, RegistrationWarning, RegistrationWarningKind};
        use clean_kernel::env::DeclarationTrustSummary;

        let w = RegistrationWarning {
            decl_name: Name::from_string("auto_gen"),
            kind: RegistrationWarningKind::SyntheticSorry,
            summary: DeclarationTrustSummary {
                has_explicit_sorry: false,
                has_synthetic_sorry: true,
                trusted_arith_count: 0,
                trusted_ay_count: 0,
            },
        };
        let mut buf = Vec::new();
        emit_registration_warning(&mut buf, &w).expect("write should succeed");
        let output = String::from_utf8(buf).expect("valid utf8");
        assert_eq!(
            output, "warning: declaration 'auto_gen' uses synthetic sorry\n",
            "synthetic sorry warning format mismatch"
        );
    }

    // -- Audit item 5: intra-project import resolution -------------------
    //
    // These tests cover `check check`'s ability to recursively elaborate
    // sibling `.lean` files brought in via `import M.X.Y`. See
    // `docs/mathbot/CLEAN-VERIFIER-AUDIT-2026-05-27.md` (item 5).

    use super::{check_file_with_json, ImportCheckState};
    use clean_elab::resolve_intra_project_import;
    use clean_kernel::cli::PreludeMode;
    use std::fs;

    /// Two-file project: `B.lean` imports `A.lean` and uses a definition
    /// from it. `clean check B.lean` must elaborate `A.lean` first so the
    /// reference in `B.lean` resolves. Before audit item 5 this returned an
    /// `UnknownIdent` error because the `import` statement only attempted
    /// `.olean` loading, never `.lean` source.
    #[test]
    fn check_file_resolves_intra_project_import_via_source() {
        let dir = tempfile::tempdir().expect("tempdir");
        let root = dir.path();
        fs::write(root.join("lakefile.lean"), "package proj\n").expect("lakefile");
        fs::write(root.join("A.lean"), "def foo : Nat := 1\n").expect("A.lean");
        // B.lean references `foo` from A. Before the audit-item-5 fix this
        // raised UnknownIdent("foo") because the import never resolved to a
        // `.lean` source file. After the fix `foo` must be in scope here.
        fs::write(root.join("B.lean"), "import A\ndef bar : Nat := foo\n").expect("B.lean");

        let b_path = root.join("B.lean");
        check_file_with_json(&b_path, false, false, PreludeMode::Builtin, false)
            .expect("B.lean should typecheck once intra-project imports resolve");
    }

    /// Run `check_file_body` on `source` written to a temp `.lean` file and
    /// return `(decl_count, success_count, errors)` from the outcome. Used to
    /// assert that declarations nested inside `namespace`/`section` blocks are
    /// counted individually rather than collapsed into one uncounted unit.
    fn count_checked_decls(source: &str) -> (usize, usize, Vec<String>) {
        use super::{check_file_body, FileCheckOutcome};
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("Entry.lean");
        fs::write(&path, source).expect("write source");

        let mut env = Environment::with_prelude();
        let mut state = ImportCheckState::default();
        state.in_flight.insert(path.clone()); // mark as entry file
        let mut outcome = FileCheckOutcome::default();
        check_file_body(
            &path,
            &mut env,
            &mut state,
            &mut outcome,
            false,
            false,
            true,
        )
        .expect("check_file_body should not hard-error");
        (outcome.decl_count, outcome.success_count, outcome.errors)
    }

    #[test]
    fn check_counts_top_level_decls() {
        let (decl_count, success_count, errors) =
            count_checked_decls("def a : Nat := 1\ndef b : Nat := 2\n");
        assert_eq!(decl_count, 2, "two top-level defs => 2 declarations");
        assert_eq!(success_count, 2, "both should pass");
        assert!(errors.is_empty(), "no errors expected: {errors:?}");
    }

    #[test]
    fn check_counts_decls_inside_namespace() {
        // Regression: a file whose body is one `namespace N … end` block must
        // report each inner declaration, not "0 declarations".
        let (decl_count, success_count, errors) =
            count_checked_decls("namespace N\ndef a : Nat := 1\ndef b : Nat := 2\nend N\n");
        assert_eq!(
            decl_count, 2,
            "namespace with two defs => 2 declarations, got {decl_count}"
        );
        assert_eq!(success_count, 2, "both namespace members should pass");
        assert!(errors.is_empty(), "no errors expected: {errors:?}");
    }

    #[test]
    fn check_counts_decls_inside_nested_namespace_and_section() {
        let src = "namespace Outer\n\
                   def a : Nat := 1\n\
                   namespace Inner\n\
                   def b : Nat := 2\n\
                   def c : Nat := 3\n\
                   end Inner\n\
                   section\n\
                   def d : Nat := 4\n\
                   end\n\
                   end Outer\n";
        let (decl_count, success_count, _errors) = count_checked_decls(src);
        assert_eq!(decl_count, 4, "four nested defs => 4 declarations");
        assert_eq!(success_count, 4, "all four should pass");
    }

    /// Track W regression: a recursive `def` whose `match` is on a **nested**
    /// inductive (a constructor carries `List Self`, inducing an auxiliary
    /// `Self._List` mutual block) and one arm makes a self-recursive call.
    ///
    /// This is the real TrustIr `Ty.bitWidth` shape: `Ty` has both
    /// `Tuple : List Ty -> Ty` (nested) and `Vector : Nat -> Ty -> Ty`
    /// (direct-recursive), and `bitWidth` recurses in the `Vector` arm. Before
    /// the telescope-driven nested minor builder, `Ty.rec`'s minor premises were
    /// reconstructed at the wrong types (the nested `Tuple` minor was confused
    /// with the `_List.cons` minor), so the kernel rejected the assembled
    /// recursor application (`KernelCheckFailed` on `bitWidth`). The fix reads
    /// each minor premise's exact expected type off the kernel-built recursor.
    ///
    /// E2E (`check_file_body`), so a pass here means the produced term genuinely
    /// kernel-checks — not merely that some intermediate elaboration succeeded.
    #[test]
    fn check_nested_recursive_match_bitwidth_shape() {
        let src = "namespace W\n\
                   structure TyId where\n\
                   \x20 index : Nat\n\
                   \x20 deriving DecidableEq, Repr\n\
                   inductive Ty where\n\
                   \x20 | I8 : Ty\n\
                   \x20 | Tuple : List Ty -> Ty\n\
                   \x20 | Vector : Nat -> Ty -> Ty\n\
                   \x20 | Ptr : Ty\n\
                   \x20 | Unit : Ty\n\
                   \x20 deriving Repr\n\
                   def Ty.bitWidth : Ty -> Option Nat\n\
                   \x20 | .I8 => some 8\n\
                   \x20 | .Vector lanes elemTy =>\n\
                   \x20   match elemTy.bitWidth with\n\
                   \x20   | some elemWidth => some (lanes * elemWidth)\n\
                   \x20   | none => none\n\
                   \x20 | .Ptr => some 64\n\
                   \x20 | _ => none\n\
                   end W\n";
        let (decl_count, success_count, errors) = count_checked_decls(src);
        assert!(
            errors.is_empty(),
            "nested recursive bitWidth must kernel-check cleanly: {errors:?}"
        );
        assert_eq!(
            decl_count, success_count,
            "every declaration must pass (decl_count={decl_count}, success_count={success_count})"
        );
        assert!(success_count >= 3, "Ty, Ty.bitWidth, and TyId should pass");
    }

    /// Cycle: A imports B, B imports A. The recursive resolver must detect
    /// this and surface an error rather than recursing forever.
    #[test]
    fn check_file_detects_import_cycle() {
        let dir = tempfile::tempdir().expect("tempdir");
        let root = dir.path();
        fs::write(root.join("lakefile.lean"), "package proj\n").expect("lakefile");
        fs::write(root.join("A.lean"), "import B\ndef a := 1\n").expect("A.lean");
        fs::write(root.join("B.lean"), "import A\ndef b := 2\n").expect("B.lean");

        let a_path = root.join("A.lean");
        let result = check_file_with_json(&a_path, false, false, PreludeMode::Builtin, false);
        let err = result.expect_err("cycle must be reported, not infinite-loop");
        let msg = format!("{err:#}");
        assert!(
            msg.contains("cycle") || msg.contains("already being elaborated"),
            "cycle diagnostic should mention the cycle: {msg}"
        );
    }

    /// Module names that look mathlib-shaped (no matching `.lean` file
    /// under the project tree) must NOT resolve as intra-project — they
    /// should fall through to the existing `.olean`-based path.
    #[test]
    fn resolve_import_path_returns_none_for_external_modules() {
        let dir = tempfile::tempdir().expect("tempdir");
        let root = dir.path();
        fs::write(root.join("lakefile.lean"), "package proj\n").expect("lakefile");
        let file = root.join("Entry.lean");
        fs::write(&file, "import Mathlib.Data.Real.Basic\n").expect("entry");

        let resolved = resolve_intra_project_import("Mathlib.Data.Real.Basic", &file);
        assert!(
            resolved.is_none(),
            "external Mathlib module should not resolve to a local .lean file"
        );
    }

    /// Resolver prefers files under the Lake root, falling back to walked
    /// parents. This test verifies the path resolution layer in isolation.
    #[test]
    fn resolve_import_path_finds_sibling_lean_file() {
        let dir = tempfile::tempdir().expect("tempdir");
        let root = dir.path();
        fs::create_dir_all(root.join("Sub")).expect("subdir");
        fs::write(root.join("lakefile.lean"), "package proj\n").expect("lakefile");
        fs::write(root.join("Sub/Inner.lean"), "def x := 1\n").expect("sub inner");
        let entry = root.join("Outer.lean");
        fs::write(&entry, "import Sub.Inner\n").expect("entry");

        let resolved = resolve_intra_project_import("Sub.Inner", &entry)
            .expect("Sub.Inner should resolve to Sub/Inner.lean under the Lake root");
        assert!(
            resolved.ends_with("Sub/Inner.lean"),
            "resolved path: {resolved:?}"
        );
    }

    /// Diamond import: `D` imports `B` and `C`, both of which import `A`.
    /// The resolver must cache the result for `A.lean` and not re-elaborate
    /// it (would otherwise hit a "constant already declared" error and waste
    /// elaboration work).
    #[test]
    fn check_file_caches_diamond_intra_project_imports() {
        let dir = tempfile::tempdir().expect("tempdir");
        let root = dir.path();
        fs::write(root.join("lakefile.lean"), "package proj\n").expect("lakefile");
        fs::write(root.join("A.lean"), "def foo : Nat := 0\n").expect("A.lean");
        fs::write(root.join("B.lean"), "import A\ndef baz : Nat := foo\n").expect("B.lean");
        fs::write(root.join("C.lean"), "import A\ndef qux : Nat := foo\n").expect("C.lean");
        fs::write(
            root.join("D.lean"),
            "import B\nimport C\ndef ok : Nat := baz\n",
        )
        .expect("D.lean");

        let d_path = root.join("D.lean");
        check_file_with_json(&d_path, false, false, PreludeMode::Builtin, false)
            .expect("diamond intra-project imports should elaborate without duplicate-decl errors");
    }

    /// `ImportCheckState` must not consider an in-flight file as "already
    /// completed" — only fully elaborated files end up in `completed`. This
    /// guards against future refactors that conflate the two sets.
    #[test]
    fn import_check_state_default_is_empty() {
        let state = ImportCheckState::default();
        assert!(state.completed.is_empty(), "fresh state has no completed");
        assert!(state.in_flight.is_empty(), "fresh state has no in-flight");
        assert!(
            state.resolved_modules.is_empty(),
            "fresh state has no resolved cache"
        );
    }
}
