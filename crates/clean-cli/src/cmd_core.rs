// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Core command handlers: check, verify-c, eval.

use anyhow::Context;
use clean_c_sem::parser::CParser;
use clean_elab::agent_diagnostics::{AgentDiagnostic, AgentSourceSpan};
use clean_elab::register::reset_kernel_check_counter;
use clean_elab::{
    kernel_check_failure_count, ElabCtx, ElabResult, FileContext, RegistrationWarning,
    RegistrationWarningKind, TacticError,
};
use clean_kernel::sorry::{reset_sorry_counter, sorry_count};
use clean_kernel::{Environment, Name, TypeChecker};
use clean_parser::{parse_expr, Span, SurfaceBinder, SurfaceDecl, SurfaceName};
use serde::Serialize;
use std::collections::{HashMap, HashSet};
use std::fmt::Write as FmtWrite;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::time::{Duration, Instant};

/// The `clean check --json` report schema.
///
/// **v2 (2026-09-28).** `trust_summary.sorry_axioms` CHANGED MEANING under v1
/// (01189665c): it was the number of sorry terms the elaborator created, and is
/// now the number of checked declarations whose constant closure reaches
/// `sorryAx` / `sorry` (in any position, behind any alias or cited lemma); the
/// old count moved to the additive `sorry_terms_minted`. A consumer comparing a
/// v1 figure with a current one was comparing two different quantities, so the
/// version moves. v2 also renders every `assumptions` axiom name unambiguously
/// (`Name::to_unambiguous_string`: a one-component `«Eq.refl»` is no longer
/// printed `Eq.refl`); ordinary names render exactly as before. No field was
/// removed or renamed: a v1 reader of any field but `sorry_axioms` reads v2
/// unchanged.
const CHECK_REPORT_SCHEMA_VERSION: &str = "Clean-check-report-v2";

mod check_observer;
#[cfg(test)]
#[path = "cmd_core_world_tests.rs"]
mod source_world_tests;

#[allow(dead_code)] // 2026-07-31: no lib-build caller; the coinductive reachability pin calls it in lib-test.
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
    check_file_with_json_with_imports(
        path,
        verbose,
        allow_sorry,
        prelude,
        json,
        false,
        clean_elab::ImportPolicy::default(),
        clean_kernel::cli::DEFAULT_DECL_BUDGET,
        clean_kernel::cli::DEFAULT_AUTOMATION_BUDGET,
        &[],
    )
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn check_file_with_json_with_imports(
    path: &Path,
    verbose: bool,
    allow_sorry: bool,
    prelude: clean_kernel::cli::PreludeMode,
    json: bool,
    imports_prefer_olean: bool,
    import_policy: clean_elab::ImportPolicy,
    decl_budget: u64,
    automation_budget: u64,
    options: &[clean_elab::command_line_options::CommandLineOption],
) -> anyhow::Result<()> {
    check_file_with_json_with_imports_in_world(
        path,
        verbose,
        allow_sorry,
        prelude,
        json,
        imports_prefer_olean,
        import_policy,
        decl_budget,
        automation_budget,
        options,
        None,
    )
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn check_file_with_json_with_imports_in_world(
    path: &Path,
    verbose: bool,
    allow_sorry: bool,
    prelude: clean_kernel::cli::PreludeMode,
    json: bool,
    imports_prefer_olean: bool,
    import_policy: clean_elab::ImportPolicy,
    decl_budget: u64,
    automation_budget: u64,
    options: &[clean_elab::command_line_options::CommandLineOption],
    explicit_world: Option<clean_kernel::lean_world::LeanWorld>,
) -> anyhow::Result<()> {
    let (outcome, elapsed) = collect_check_outcome_in_world(
        path,
        verbose,
        allow_sorry,
        prelude,
        json,
        imports_prefer_olean,
        import_policy,
        decl_budget,
        automation_budget,
        options,
        explicit_world,
    )?;

    finalize_check_run(
        path,
        outcome,
        elapsed,
        CheckBudgets {
            decl: decl_budget,
            automation: automation_budget,
        },
        json,
    )
}

/// Run the whole `clean check` pipeline and hand back the raw
/// [`FileCheckOutcome`] instead of printing and exiting.
///
/// Split out of [`check_file_with_json_with_imports`] so the per-declaration
/// budget's verdict rules are testable as VALUES — `success_count`,
/// `errors`, `diverged` — rather than by scraping stdout. Rule 2 of this
/// repo's method: a test that cannot see the three buckets separately cannot
/// prove that a diverged declaration landed in the right one.
///
/// `options` (`clean check -D`) is the initial option state of EVERY file the
/// run elaborates — the file under check and each intra-project import
/// elaborated from source — as Lake compiles every module of a package with
/// its `leanOptions`
/// ([`clean_elab::command_line_options::apply_command_line_options`]).
#[allow(clippy::too_many_arguments)]
#[cfg(test)]
pub(crate) fn collect_check_outcome(
    path: &Path,
    verbose: bool,
    allow_sorry: bool,
    prelude: clean_kernel::cli::PreludeMode,
    json: bool,
    imports_prefer_olean: bool,
    import_policy: clean_elab::ImportPolicy,
    decl_budget: u64,
    automation_budget: u64,
    options: &[clean_elab::command_line_options::CommandLineOption],
) -> anyhow::Result<(FileCheckOutcome, Duration)> {
    collect_check_outcome_in_world(
        path,
        verbose,
        allow_sorry,
        prelude,
        json,
        imports_prefer_olean,
        import_policy,
        decl_budget,
        automation_budget,
        options,
        None,
    )
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn collect_check_outcome_in_world(
    path: &Path,
    verbose: bool,
    allow_sorry: bool,
    prelude: clean_kernel::cli::PreludeMode,
    json: bool,
    imports_prefer_olean: bool,
    import_policy: clean_elab::ImportPolicy,
    decl_budget: u64,
    automation_budget: u64,
    options: &[clean_elab::command_line_options::CommandLineOption],
    explicit_world: Option<clean_kernel::lean_world::LeanWorld>,
) -> anyhow::Result<(FileCheckOutcome, Duration)> {
    let decision = clean_olean::source_world_for_file(path, explicit_world)?;
    let source_identity = std::fs::canonicalize(path).unwrap_or_else(|_| path.to_path_buf());
    let source_input = std::fs::read_to_string(path)?;
    let header = clean_parser::Parser::parse_header(&source_input)?;
    let _guard = check_file_lock();
    let _trust_counter_scope = TrustCounterScope::enter();
    let start = Instant::now();
    let verbose = verbose && !json;

    // The environment every module-driver frontend checks against (see
    // `module_environment` for the import prelude under
    // `--imports-prefer-olean`, the per-prelude `List` monad policy (B07), and
    // the IO / `ULift` registrations).
    let environment_setup = clean_elab::module_driver::EnvironmentSetup {
        prelude: match prelude {
            clean_kernel::cli::PreludeMode::Builtin => {
                clean_elab::module_driver::PreludeFlavor::Builtin
            }
            clean_kernel::cli::PreludeMode::Lean4Core => {
                clean_elab::module_driver::PreludeFlavor::Lean4Core
            }
        },
        imports: if imports_prefer_olean {
            clean_elab::module_driver::ImportArtifacts::PreferOlean
        } else {
            clean_elab::module_driver::ImportArtifacts::Source
        },
    };
    let mut source_setup = if !imports_prefer_olean
        && clean_elab::module_driver::source_closure_needs_world_setup(path)?
    {
        Some(clean_elab::module_driver::SourceModuleSetup::for_file(
            environment_setup,
            &decision,
            path,
        )?)
    } else {
        None
    };
    let setup_header = source_setup
        .as_ref()
        .map(|setup| setup.root_environment_header(&header))
        .unwrap_or_else(|| header.clone());
    let (mut env, import_base) = clean_elab::module_driver::module_environment_for_header_in_world(
        environment_setup,
        &decision,
        &setup_header,
    )?;
    if let Some(setup) = &mut source_setup {
        env = setup.initial_environment(&header)?;
    }
    let source_base = source_setup
        .as_ref()
        .map(|setup| setup.environment())
        .unwrap_or_else(|| env.clone());
    // The setup retains its kernel base before any imports, including a
    // recent world's genuine Init. Imported declarations must be re-admitted
    // before a citation is credited; a post-Init snapshot would trust them.
    let source_entry = source_setup.as_ref().map(|_| source_identity);
    let source_inputs = source_entry
        .as_ref()
        .map(|canonical| {
            HashMap::from([(
                canonical.clone(),
                std::sync::Arc::<str>::from(source_input.as_str()),
            )])
        })
        .unwrap_or_default();
    let mut state = ImportCheckState {
        source_setup,
        source_entry,
        source_inputs,
        imports_prefer_olean,
        import_policy,
        command_line_options: options.to_vec(),
        import_gate: Some(import_base),
        // Source modules implicitly import Init. Their isolated elaboration
        // needs that working environment; only the citation gate takes the
        // separate pre-import kernel base as trusted.
        base_env: Some(source_base),
        import_world: Some(decision.import_world()),
        ..ImportCheckState::default()
    };
    let mut outcome = FileCheckOutcome {
        lean_world: decision.world(),
        command_line_options: options
            .iter()
            .map(clean_elab::command_line_options::CommandLineOption::to_arg)
            .collect(),
        ..FileCheckOutcome::default()
    };

    // Arm the AMBIENT per-declaration budget on THIS thread (it is
    // thread-local by design — see `clean_kernel::tc::set_declaration_budget`)
    // and disarm it on the way out, so a `clean check` call cannot leave fuel
    // limits behind for whatever else runs on the thread afterwards (the
    // in-process test harness reuses threads).
    //
    // Armed HERE, after the prelude/IO/ULift registrars have run, and not at
    // the top of the function: the budget bounds the DECLARATIONS OF THE FILE
    // UNDER CHECK, not the fixed cost of standing up the environment they are
    // checked against. Arming it earlier made a tight `--decl-budget` starve
    // `Environment::with_prelude()` itself, which fails the whole command
    // instead of reporting a per-declaration verdict — the budget would have
    // been bounding the wrong thing.
    let _budget_scope = clean_elab::module_driver::DeclBudgetScope::enter(decl_budget);
    // The AUTOMATION work budget, armed at the same point for the same
    // reasons; the elaborator refills it once per declaration
    // (`clean_elab`'s `decl_work_budget`). Its unit is the LEAF declaration,
    // not the top-level one `DeclBudgetScope` counts: see
    // `clean_auto`'s `work_budget.rs` for why the two cannot share a pot.
    let _automation_scope = AutomationBudgetScope::enter(automation_budget);

    outcome.timing.setup = start.elapsed();
    check_file_recursive(
        path,
        &mut env,
        &mut state,
        &mut outcome,
        verbose,
        allow_sorry,
        json,
    )?;
    crate::check_env_digest::write_env_digest_if_requested(&env)?;

    // READ THE TRUST COUNTERS HERE, inside `_trust_counter_scope`'s lifetime,
    // and carry them out as VALUES.
    //
    // This is not a stylistic preference — it is the whole of task #66. These
    // two globals were the only taint evidence `Clean-check-report-v1` recorded
    // under `counting_basis = allow_sorry_success`, where a sorry-tainted
    // declaration is folded into `success_count` by `record_checked_decl`.
    // `TrustCounterScope::drop` zeroes both when this function returns, so a
    // caller that read them AFTERWARDS read structural zeros: from `d935d692e`
    // (which split this function out from `check_file_with_json_with_imports`
    // and left the reads behind in `finalize_check_run`) to the fix, every
    // report claimed `sorry_axioms: 0` and `kernel_check_failures: 0`
    // regardless of what the run observed. Three real sorry-tainted successes
    // in the pinned Mathlib slice were reported as zero — see
    // `docs/issues/2026-08-30-check-report-trust-counters-read-after-reset.md`.
    //
    // Carrying them as values also removes the race: the globals are process-
    // wide while `check_file_lock()` is only held for the duration of this
    // function, so a concurrent second run could otherwise reset them out from
    // under a late reader.
    //
    // Less what the isolated re-elaborations of imports minted (see
    // [`faithful_import_environment`]): those runs re-elaborate source this
    // run already counted, and their outcome is discarded.
    outcome.environment_lean_world = clean_olean::environment_world(&env);
    outcome.sorry_terms_minted = sorry_count().saturating_sub(state.nested_sorry_axioms);
    outcome.kernel_check_failures =
        kernel_check_failure_count().saturating_sub(state.nested_kernel_check_failures);

    Ok((outcome, start.elapsed()))
}

/// Arms `clean-auto`'s per-declaration automation work budget for one
/// `clean check` (or `clean lean`) call and disarms it on drop; thread-local for the same
/// reason as the driver's `DeclBudgetScope`.
pub(crate) struct AutomationBudgetScope;

impl AutomationBudgetScope {
    pub(crate) fn enter(limit: u64) -> Self {
        clean_auto::set_automation_budget(limit);
        Self
    }
}

impl Drop for AutomationBudgetScope {
    fn drop(&mut self) {
        clean_auto::set_automation_budget(0);
    }
}

/// The two per-declaration budgets a run was checked under, carried to the
/// report so a consumer can reproduce it.
#[derive(Debug, Clone, Copy)]
pub(crate) struct CheckBudgets {
    /// `--decl-budget`, kernel operations per top-level declaration.
    pub(crate) decl: u64,
    /// `--automation-budget`, automation work units per declaration.
    pub(crate) automation: u64,
}

/// Environment variable that turns on per-declaration budget tracing.
///
/// Set to `1` to print `decl-budget <module> <name> <ticks>` on stderr after
/// every declaration. This is the per-declaration half of the calibration
/// instrument `scripts/decl_budget_calibrate.sh`, which aggregates it into
/// `reports/decl-budget-calibration.json` — the census that would turn
/// [`clean_kernel::cli::DEFAULT_DECL_BUDGET`] from a deliberate over-estimate
/// into a derived bound. See that constant's docs for what is and is not
/// measured today.
const DECL_BUDGET_TRACE_ENV: &str = "CLEAN_CHECK_DECL_BUDGET_TRACE";

fn decl_budget_trace_enabled() -> bool {
    std::env::var(DECL_BUDGET_TRACE_ENV).is_ok_and(|v| v == "1")
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
    /// How many error signatures were OFFERED, cap included.
    ///
    /// Without this the cap is undisclosed: the vector simply stops growing at
    /// ten and the reader is shown ten errors with no way to know there were
    /// forty. A silent truncation reads as "that is all of them", which is the
    /// one thing it is not.
    pub(crate) first_errors_seen: usize,
}

/// Append an error signature unless the cap is already reached, counting every
/// offer so the cap can be disclosed rather than applied silently.
fn push_parse_only_error(counts: &mut ParseOnlyCounts, message: String) {
    counts.first_errors_seen += 1;
    if counts.first_errors.len() < PARSE_ONLY_MAX_FIRST_ERRORS {
        counts.first_errors.push(message);
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
        }
        | SurfaceDecl::GuardMsgs { cmd: inner, .. } => {
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
            push_parse_only_error(counts, format!("rawdecl: {sig}"));
        }
        _ => {
            counts.decls += 1;
            counts.parse_ok += 1;
        }
    }
}

/// Parse `content` with the same tactic-aware file parser the elaborating
/// check path uses, and classify every leaf declaration WITHOUT elaborating.
/// `seed` pre-populates the parser's notation registry with what the file's
/// imports declare (see `clean_elab::notation_imports`); an EMPTY seed makes
/// `parse_file_seeded` the same code path as
/// `parse_file_with_tactics_diagnostics`, which is what the unseeded control
/// arm of the rank-8 measurement uses.
#[cfg(test)]
pub(crate) fn parse_only_counts(
    content: &str,
    seed: &clean_parser::NotationSeed,
) -> ParseOnlyCounts {
    parse_only_counts_in_world(content, seed, clean_kernel::lean_world::LeanWorld::ORACLE)
}

fn parse_only_counts_in_world(
    content: &str,
    seed: &clean_parser::NotationSeed,
    world: clean_kernel::lean_world::LeanWorld,
) -> ParseOnlyCounts {
    let patterns = clean_elab::tactic::builtins::builtin_tactic_patterns();
    let mut counts = ParseOnlyCounts::default();
    match clean_parser::parse_file_seeded_in_world(content, &patterns, seed, world) {
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
                    &mut counts,
                    format!(
                        "recovery[{}]: {named} at line {}: {}",
                        diag.code, diag.recovery_start.line, diag.message
                    ),
                );
            }
        }
        Err(err) => {
            counts.hard_error = 1;
            push_parse_only_error(&mut counts, format!("hard error: {err}"));
        }
    }
    counts
}

/// JSON payload for `clean check --parse-only --json`.
///
/// `imported_notations` / `import_modules_read` are an ADDITIVE extension of
/// `Clean-parse-only-report-v1`: every key the version already declared keeps
/// its name, type and meaning, and the sole consumer
/// (`scripts/parser_mathlib_sweep.sh`, which pins the version string and then
/// reads keys) is unaffected. The version is therefore not bumped — a bump
/// would make every existing artifact and that pinned reader disagree for a
/// change that removes nothing.
#[derive(Debug, Serialize)]
struct ParseOnlyReport {
    lean_world: &'static str,
    schema_version: &'static str,
    command: &'static str,
    file: String,
    decls: usize,
    parse_ok: usize,
    rawdecl_recovered: usize,
    hard_error: usize,
    recovery_diagnostics: usize,
    /// Notation commands harvested from the file's transitive `.lean` import
    /// closure and seeded into the parser before this file was read.
    imported_notations: usize,
    /// Modules of that closure resolved to project-local source and read.
    import_modules_read: usize,
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
#[cfg(test)]
pub(crate) fn parse_only_check(path: &Path, json: bool) -> anyhow::Result<()> {
    parse_only_check_in_world(path, json, None)
}

pub(crate) fn parse_only_check_in_world(
    path: &Path,
    json: bool,
    explicit: Option<clean_kernel::lean_world::LeanWorld>,
) -> anyhow::Result<()> {
    let decision = clean_olean::source_world_for_file(path, explicit)?;
    let content = std::fs::read_to_string(path)
        .map_err(|e| anyhow::anyhow!("failed to read {}: {e}", path.display()))?;
    // Seed the parser with the notation the file's imports declare, so a
    // measurement of "what Clean's parser can read" is not silently a
    // measurement of "what Clean hand-wrote into its builtin grammar".
    let (seed, harvest) = clean_elab::notation_imports::seed_from_imports(path, &content);
    let counts = parse_only_counts_in_world(&content, &seed, decision.world());
    let failed = counts.rawdecl_recovered + counts.hard_error;

    if json {
        let report = ParseOnlyReport {
            schema_version: PARSE_ONLY_REPORT_SCHEMA_VERSION,
            command: "clean check --parse-only",
            lean_world: decision.world().tag(),
            file: path.display().to_string(),
            decls: counts.decls,
            parse_ok: counts.parse_ok,
            rawdecl_recovered: counts.rawdecl_recovered,
            hard_error: counts.hard_error,
            recovery_diagnostics: counts.recovery_diagnostics,
            imported_notations: harvest.notations,
            import_modules_read: harvest.modules_read,
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
        if harvest.modules_read > 0 {
            let _ = writeln!(
                out,
                "Seeded {} notation(s) from {} imported module(s)",
                harvest.notations, harvest.modules_read
            );
        }
        for err in &counts.first_errors {
            let _ = writeln!(out, "  {err}");
        }
        if counts.first_errors_seen > counts.first_errors.len() {
            let _ = writeln!(
                out,
                "  … showing the first {} of {} errors",
                counts.first_errors.len(),
                counts.first_errors_seen
            );
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
    /// Fresh source headers require independent body/outcome comparisons.
    source_setup: Option<clean_elab::module_driver::SourceModuleSetup>,
    /// Exact bytes retained when independently re-elaborating source modules.
    source_inputs: HashMap<PathBuf, std::sync::Arc<str>>,
    /// The root whose header selected the initial environment.
    source_entry: Option<PathBuf>,
    /// Set of canonical paths that have already been fully elaborated this run.
    /// Used to avoid quadratic re-elaboration on diamond-shaped import graphs.
    completed: HashSet<PathBuf>,
    /// Set of canonical paths currently being elaborated up the call stack.
    /// Used to detect import cycles.
    in_flight: HashSet<PathBuf>,
    /// Cache of resolved module name -> resolved path.
    resolved_modules: HashMap<Name, Option<PathBuf>>,
    /// Canonical path of each intra-project source import -> the module name
    /// its `import` statement wrote (Lean's `env.mainModule` for that file).
    /// The file's `private` theorems and axioms are registered as
    /// `_private.<that name>.0.<name>` (G21), so an isolated re-elaboration
    /// (which clones this map) mints the same names, and the same name tags
    /// its report lines (G14). See `lean_main_module`.
    module_names: HashMap<PathBuf, Name>,
    /// Lean main module -> the canonical path of the file this run named with
    /// it, the entry file included. Lean gives one module name to one file,
    /// and a private name is `_private.<module>.0.<name>`, so two files with
    /// one name would share each other's private declarations (G21 review:
    /// `import A` from `src/sub/B.lean` resolved by the parent-directory
    /// fallback to `src/sub/A.lean` while the entry `src/A.lean` is also `A`).
    /// A second file for a name is refused. See `claim_main_module`.
    module_owners: HashMap<Name, PathBuf>,
    /// When set, an `import M.X` whose module has a discoverable prebuilt
    /// `.olean` is loaded from that artifact (via the main-loop `.olean` path)
    /// rather than recursively elaborated from its `.lean` source. Lets a file
    /// inside a large source tree (e.g. Mathlib) be checked against compiled
    /// dependency context. See `--imports-prefer-olean`.
    imports_prefer_olean: bool,
    /// What an `import` that resolves to nothing real does. Fail-closed by
    /// default; `--permissive-imports` relaxes it. See
    /// [`clean_elab::ImportPolicy`].
    import_policy: clean_elab::ImportPolicy,
    /// `-D` overrides: the initial option state of every file this run
    /// elaborates, entry file and source-elaborated imports alike.
    command_line_options: Vec<clean_elab::command_line_options::CommandLineOption>,
    /// Module names this run satisfied by elaborating their intra-project
    /// `.lean` source. Copied onto each file's `FileContext` after that file's
    /// import-resolution pass so the fail-closed policy does not refuse an
    /// import whose declarations are demonstrably already in `env`.
    satisfied_from_source: HashSet<Name>,
    /// A source import that returned diagnostics is refused, even if some of
    /// its declarations reached the shared environment before the failure.
    refused_from_source: HashMap<Name, String>,
    /// Re-admits every declaration's cited closure over the environment this
    /// run built BEFORE any import, so an imported module's declarations are
    /// kernel-checked before a citation of them is credited (module-trust,
    /// 2026-09-24). Created once, before the first declaration is processed.
    import_gate: Option<clean_olean::ImportedConeGate>,
    /// Whether each module loaded from an artifact is the build of its
    /// source (module-trust round 27; see `import_binding.rs`).
    import_binding: crate::import_binding::ImportBinding,
    /// Per-run cache of each constant's domain-axiom closure, for disclosing
    /// assumption-bearing passes (`FileCheckOutcome::assumptions`).
    axiom_closure: clean_kernel::env::DomainAxiomClosure,
    /// The working environment before any project import, including the
    /// selected implicit prelude. This is NOT the citation gate's trusted
    /// base. An import elaborated next to modules it does not import is
    /// re-elaborated in this plus exactly its own import closure; see
    /// [`sibling_import_divergence`]. `None` only in unit tests that build a
    /// bare state: such a comparison then fails closed.
    base_env: Option<Environment>,
    /// One entry per file on the recursion stack: the canonical paths of the
    /// intra-project `.lean` imports it named that resolved to source, in the
    /// order the file names them (Lean's import order).
    import_frames: Vec<Vec<PathBuf>>,
    /// Per completed file: its transitive intra-project source-import closure.
    closures: HashMap<PathBuf, HashSet<PathBuf>>,
    /// The Lean world of the whole run (G72, R111): the one the entry file's
    /// Lake package names, selected once, since every file of the run is
    /// elaborated into one environment and Lake builds every package of a
    /// workspace with the root's toolchain. A file's own `lean-toolchain`
    /// (a nested package, a Lake dependency) never overrides it, and a
    /// refused world refuses every Lean module the run imports. `None` only
    /// in unit tests that build a bare state: each file then selects its own.
    import_world: Option<Result<clean_olean::ImportWorld, clean_olean::ImportWorldRefusal>>,
    /// Per file between the end of its own declarations and its completion:
    /// what its OWN declarations did to `env` (its imports' excluded) — see
    /// [`OwnElaboration`].
    own_elaborations: HashMap<PathBuf, OwnElaboration>,
    /// Per file: the environment its own import closure plus itself give,
    /// with what the file did there — `None` when that could not be built
    /// faithfully (a module in its closure diverged in turn).
    faithful: HashMap<PathBuf, Option<Rc<(Environment, OwnElaboration)>>>,
    /// Per completed file: the intra-project source imports it names, in
    /// source order.
    direct_imports: HashMap<PathBuf, Vec<PathBuf>>,
    /// Divergences this run found (a nested run with one is not faithful).
    divergences: usize,
    /// Trust counter increments minted by isolated re-elaborations, which
    /// re-elaborate source this run already counted.
    nested_sorry_axioms: u64,
    nested_kernel_check_failures: u64,
}

/// What one file's OWN declarations did, measured from the environment right
/// after its imports to the environment after its last declaration.
///
/// Both halves are compared between the file's elaboration next to modules it
/// does not import and its elaboration in exactly its own import closure
/// ([`sibling_import_divergence`]):
///
/// * `effect` covers EVERY component of the environment — instances,
///   attributes, simp/aesop sets, structure metadata, options, extension
///   entries, prelude flags — not only the constants the file added. The
///   constants-only comparison let `attribute [instance] c` register P's root
///   `c` next to P and `N.c` without it, with the same constants both ways
///   (round-24 verification of ff6c33c2c).
/// * `outcomes` says how each of its top-level declarations ELABORATED
///   ([`ElabOutcome`]): a file that fails in its own closure (Lean cannot
///   compile it) may elaborate cleanly next to a stranger that supplies what
///   it lacks (`attribute [instance] N.c` where only an unimported sibling
///   defines `N.c`), and the failed command changes nothing the effect would
///   see. Credit decisions (the imported-cone gate, `sorry`) are not part of
///   it: they depend on the run, not on the environment the file saw.
#[derive(Clone, Debug)]
struct OwnElaboration {
    effect: clean_kernel::env::EnvEffect,
    outcomes: Vec<ElabOutcome>,
}

/// How one top-level declaration elaborated: refused outright, or elaborated
/// with this many failed leaves (members of a `namespace` / `section` /
/// `mutual` block). Compared between a module's elaboration next to modules
/// it does not import and in exactly its own import closure, by `clean check`
/// and by `clean project check`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ElabOutcome {
    Refused,
    Elaborated { failed_leaves: usize },
}

impl ElabOutcome {
    pub(crate) fn of(
        result: &Result<clean_elab::RegisteredElabResult, clean_elab::ElabError>,
    ) -> Self {
        match result {
            Ok(registered) => Self::of_registered(registered),
            Err(_) => Self::Refused,
        }
    }

    /// The outcome of a declaration that elaborated.
    pub(crate) fn of_registered(registered: &clean_elab::RegisteredElabResult) -> Self {
        let mut leaves: Vec<&ElabResult> = Vec::new();
        registered.result.leaf_decls(&mut leaves);
        Self::Elaborated {
            failed_leaves: leaves
                .iter()
                .filter(|leaf| {
                    matches!(
                        leaf,
                        ElabResult::Failed { .. } | ElabResult::Diagnosed { .. }
                    )
                })
                .count(),
        }
    }
}

/// The first position where two elaborations' [`ElabOutcome`] sequences
/// differ, described; `None` when they are the same.
pub(crate) fn elab_outcome_difference(
    own: &[ElabOutcome],
    other: &[ElabOutcome],
) -> Option<String> {
    let position = own
        .iter()
        .zip(other)
        .position(|(a, b)| a != b)
        .or_else(|| (own.len() != other.len()).then(|| own.len().min(other.len())))?;
    let show = |outcome: Option<&ElabOutcome>| match outcome {
        None => "absent".to_string(),
        Some(ElabOutcome::Refused) => "refused".to_string(),
        Some(ElabOutcome::Elaborated { failed_leaves: 0 }) => "elaborated".to_string(),
        Some(ElabOutcome::Elaborated { failed_leaves }) => {
            format!("elaborated with {failed_leaves} failed member(s)")
        }
    };
    Some(format!(
        "its top-level declaration #{} is {} in its own import closure but {} next to \
         modules it does not import",
        position + 1,
        show(own.get(position)),
        show(other.get(position))
    ))
}

/// Accumulator for the outcome of checking the entry file.
///
/// We only surface diagnostics from the entry file; per-import failures bump
/// counts on the entry file's outcome (so exit-code contract still fires) but
/// are also annotated with the originating module so the user sees the chain.
#[derive(Debug, Default)]
pub(crate) struct FileCheckOutcome {
    lean_world: clean_kernel::lean_world::LeanWorld,
    environment_lean_world: Option<&'static str>,
    module: String,
    pub(crate) decl_count: usize,
    /// Declaration leaves checked in intra-project IMPORTED files this run.
    /// Not in `decl_count` (the entry file's denominator); read only to decide
    /// whether the run checked anything at all, so an entry file that only
    /// re-exports its imports is not refused as vacuous.
    pub(crate) imported_decl_count: usize,
    pub(crate) success_count: usize,
    pub(crate) errors: Vec<String>,
    /// Parser RECOVERY notes, which are not declaration failures and are not
    /// counted as any.
    ///
    /// They used to be pushed onto `errors`, which made the summary print a
    /// partition that is not one: `Mathlib/Order/Basic.lean` reported
    /// `Checked 207 declarations` / `69 passed, 146 failed`, and 69 + 146 is
    /// 215. The excess was exactly the eight recovery notes. A reader who adds
    /// the two numbers the summary prints is doing the obvious thing, and was
    /// getting a number bigger than the denominator.
    ///
    /// One declaration can also emit SEVERAL of these — `pending_recovery_
    /// diagnostics` is flushed as a batch — and a `RawDecl` emits one here AND
    /// a real `errors` row for the same declaration, so this bucket can never
    /// be folded back in by a count.
    ///
    /// Deliberately NOT rolled back by [`OutcomeMark`], unlike every other row
    /// vector: a recovery note describes the SOURCE TEXT, so a declaration
    /// later exhausting its budget does not make the note untrue. It also
    /// cannot be attributed to the declaration whose mark is in flight, since
    /// an imported file's parse can push here from inside that window.
    pub(crate) parser_diagnostics: Vec<String>,
    pub(crate) trust_failures: Vec<String>,
    pub(crate) kernel_failures: Vec<String>,
    /// One row per PASSED declaration whose verdict rests on a domain axiom
    /// (neither foundational nor a trust marker). Such a pass is valid under
    /// the axioms the source states, and is disclosed as assumption-bearing
    /// rather than summarised as unconditional (round-22 verification:
    /// `axiom bogus : 1 = 2` + `theorem bad : 1 = 2 := bogus` passed silently).
    pub(crate) assumptions: Vec<String>,
    /// One row per imported module whose artifact was taken AS BUILT, with
    /// no source to compare it with (or written by another tool): every
    /// statement checked against it holds of the artifact's definitions and
    /// elaborator metadata, which the imported-cone gate proves well-typed
    /// but nothing proves faithful to a source (`import_binding.rs`). A
    /// disclosure, like `assumptions`, not a failure. Not rolled back by
    /// [`OutcomeMark`]: it describes what was loaded, not a declaration.
    pub(crate) artifact_imports: Vec<String>,
    /// Declarations that spent the whole ambient per-declaration budget.
    ///
    /// Its OWN bucket, on purpose. A row here is not a pass (the work never
    /// finished, so nothing was proved) and not a failure (nothing was
    /// refuted either) — it is the absence of a verdict, recorded as such.
    /// The same doctrine `docs/SUITE_STATE.md` applies to UNKNOWN: never
    /// rounded up, never rounded down.
    pub(crate) diverged: Vec<String>,
    /// The largest ambient tick count any single declaration in this run
    /// spent — i.e. how close the run came to the budget.
    ///
    /// This is the headroom number, and it is reported on EVERY run rather
    /// than only when something diverges. A budget whose margin nobody can see
    /// is a budget nobody can calibrate: this is what
    /// `scripts/decl_budget_calibrate.sh` reads to derive
    /// `clean_kernel::cli::DEFAULT_DECL_BUDGET` from measurement, and what
    /// tells a reader of any report whether the default is still generous.
    pub(crate) peak_decl_ticks: u64,
    /// Checked declarations whose CONSTANT CLOSURE reaches `sorryAx` (or the
    /// legacy `sorry`) — in any position, behind any alias or lemma. Under
    /// `--allow-sorry` this is the evidence that a counted success was
    /// sorry-tainted, since `record_checked_decl` folds such declarations into
    /// `success_count`.
    ///
    /// CLOSURE-DERIVED since 2026-09-28. It used to be [`Self::sorry_terms_minted`]
    /// alone, which counts only sorries the ELABORATOR created, so a
    /// user-written `theorem bad : False := @sorryAx False (!true)` reported
    /// `sorry_axioms: 0` — under `--allow-sorry`, the only taint evidence the
    /// report carried said the pass was clean.
    pub(crate) sorry_axioms: u64,
    /// Sorry TERMS the elaborator created during this run, snapshotted before
    /// the run's [`TrustCounterScope`] zeroes the global counter.
    ///
    /// A VALUE, deliberately: the global it is read from is process-wide and
    /// is reset both on entry and on drop, so any reader outside
    /// [`collect_check_outcome`] gets a structural zero (task #66).
    ///
    /// It counts sorry TERMS created, not tainted declarations, and the two
    /// differ: measured 2026-08-30 on `Mathlib/Logic/Function/Basic.lean`,
    /// this reads 3 while exactly 2 declarations print `(sorry allowed)` — a
    /// declaration can mint several sorries, and a declaration that then FAILS
    /// still leaves its sorries counted. It never sees a sorry the source
    /// WROTE as a term (`@sorryAx α b`), which is why it is not the census.
    pub(crate) sorry_terms_minted: u64,
    /// Kernel type-check rejections this run observed, snapshotted alongside
    /// `sorry_axioms` and for the same reason.
    ///
    /// Not derivable from `kernel_failures`: a declaration the kernel rejects
    /// during elaboration surfaces as an `errors` row, so without this counter
    /// a kernel rejection is indistinguishable from any other elaboration
    /// error.
    ///
    /// It is a LOWER BOUND, not a census. Only
    /// `clean_elab::register::add_decl_with_kernel_check` bumps
    /// `KERNEL_CHECK_FAILURE_COUNTER`, and then only for `TypeCheckFailed` /
    /// `TheoremTypeNotProp`; `ElabError::KernelCheckFailed` is constructed at a
    /// dozen other sites that do not. Measured 2026-08-30 on
    /// `Mathlib/Logic/Basic.lean`: one `Kernel check failed …` error row, this
    /// counter 0. Do not read it as "every kernel rejection".
    pub(crate) kernel_check_failures: u64,
    /// The `-D` overrides the run was checked under, as `name=value`, in the
    /// order given. Recorded so a report says which language it checked: the
    /// same file passes or fails on `autoImplicit` alone (gap G50).
    pub(crate) command_line_options: Vec<String>,
    structured_failures: Vec<CheckObligationFeedback>,
    /// Where the run's wall time went, for `--json`'s `timing` object; see
    /// `crate::check_timing`.
    pub(crate) timing: crate::check_timing::CheckPhaseTiming,
}

/// A snapshot of `FileCheckOutcome`'s accumulators taken before a declaration
/// is processed, so everything that declaration contributed can be rolled back
/// if it turns out not to have finished.
///
/// Needed because budget exhaustion is only observable *after* the fact: an
/// intermediate elaborator layer may swallow the kernel's
/// `DeclarationBudgetExhausted` and report an ordinary unsolved goal, or even
/// return `Ok` off a `whnf` that silently under-reduced once the fuel ran out.
/// Either way the honest record is "did not finish", so whatever the run
/// recorded for this declaration is discarded and replaced.
#[derive(Clone, Copy)]
struct OutcomeMark {
    errors: usize,
    trust_failures: usize,
    kernel_failures: usize,
    structured_failures: usize,
    assumptions: usize,
    success_count: usize,
    counted_leaf_decls: usize,
}

impl OutcomeMark {
    fn take(outcome: &FileCheckOutcome, counted_leaf_decls: usize) -> Self {
        Self {
            errors: outcome.errors.len(),
            trust_failures: outcome.trust_failures.len(),
            kernel_failures: outcome.kernel_failures.len(),
            structured_failures: outcome.structured_failures.len(),
            assumptions: outcome.assumptions.len(),
            success_count: outcome.success_count,
            counted_leaf_decls,
        }
    }

    /// Discard everything the declaration recorded and replace it with one
    /// `diverged` row.
    ///
    /// FAIL CLOSED: this runs whether the declaration appeared to pass or to
    /// fail. An apparent pass off an exhausted budget is the dangerous case —
    /// the kernel's `whnf` returns its input unreduced once the fuel is gone,
    /// so a definitional-equality check can be answered on an under-reduced
    /// term — and it is precisely the case a "only override failures" rule
    /// would let through.
    ///
    /// Two things this deliberately does NOT roll back, because they are event
    /// counters rather than verdicts:
    ///
    /// * `--verbose`'s streamed per-declaration lines, which were already
    ///   printed. The authoritative record is the summary's `Did not finish:`
    ///   section, which names every diverged declaration at the end.
    /// * the global trust counters behind `trust_summary` (`sorry_axioms`,
    ///   `kernel_check_failures`). If a `sorry` was minted before the fuel ran
    ///   out, it WAS minted; hiding it would be the dishonest direction.
    fn rollback_as_diverged(
        self,
        outcome: &mut FileCheckOutcome,
        counted_leaf_decls: &mut usize,
        row: String,
    ) {
        outcome.errors.truncate(self.errors);
        outcome.trust_failures.truncate(self.trust_failures);
        outcome.kernel_failures.truncate(self.kernel_failures);
        outcome
            .structured_failures
            .truncate(self.structured_failures);
        outcome.assumptions.truncate(self.assumptions);
        outcome.success_count = self.success_count;
        // The declaration is still one unit that was looked at, so the
        // "Checked N declarations" denominator does not shrink — a diverged
        // declaration must stay visible in the count, not vanish from it.
        *counted_leaf_decls = self.counted_leaf_decls + 1;
        outcome.diverged.push(row);
    }
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
    if state.in_flight.is_empty()
        && state
            .source_entry
            .as_ref()
            .is_some_and(|expected| expected != &canonical)
    {
        anyhow::bail!(
            "source module {} changed identity after its header was read",
            path.display()
        );
    }
    if let Some(frame) = state.import_frames.last_mut() {
        if !frame.contains(&canonical) {
            frame.push(canonical.clone());
        }
    }

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

    // Every file completed before this one started is in `env` while it is
    // elaborated (an ancestor's own declarations come after its imports).
    let completed_at_start = state.completed.clone();
    state.import_frames.push(Vec::new());
    let result = check_file_body(path, env, state, outcome, verbose, allow_sorry, json);
    let direct_imports = state.import_frames.pop().unwrap_or_default();

    state.in_flight.remove(&canonical);
    // No faithful completion or sibling comparison can be minted from a run
    // with an unfinished declaration. In particular, an importer's missing
    // own record after the cutoff below is not a semantic divergence.
    if !outcome.diverged.is_empty() {
        state.own_elaborations.remove(&canonical);
        return result;
    }
    if result.is_ok() {
        let mut closure = HashSet::new();
        for import in &direct_imports {
            closure.insert(import.clone());
            if let Some(inner) = state.closures.get(import) {
                closure.extend(inner.iter().cloned());
            }
        }
        // SIBLING-IMPORT LEAK (round-24 verification of 2bcef9307). The run
        // elaborates every import into ONE environment, so a file was
        // elaborated next to files it does not import: with `X: import P;
        // import Q`, `P: instance (priority := high) three : OfNat Nat 2 :=
        // ⟨3⟩` and `Q: def two : Nat := 2`, Q's `two` was elaborated with P's
        // instance and became 3, and `M2: import X; theorem m : two = 3 :=
        // rfl` passed `clean check` although Lean 4.8.0 rejects it (in Lean,
        // Q is compiled without P). A file that saw such strangers is compared
        // with its elaboration in exactly its own import closure; any
        // difference fails the run closed.
        let saw_strangers = completed_at_start
            .iter()
            .any(|done| !closure.contains(done));
        // Recorded before the comparison, which seeds from them.
        state.closures.insert(canonical.clone(), closure);
        state
            .direct_imports
            .insert(canonical.clone(), direct_imports);
        let own = state.own_elaborations.remove(&canonical);
        if saw_strangers || (state.source_setup.is_some() && !state.in_flight.is_empty()) {
            let divergence = match &own {
                Some(own) => {
                    sibling_import_divergence(path, &canonical, env, own, state, allow_sorry)
                }
                // Its own declarations were not all elaborated (a refused
                // artifact import stopped it): nothing to compare, so it is
                // not credited as faithful.
                None => Some(
                    "its own declarations were not all elaborated, so they could not be \
                     compared with its own import closure"
                        .to_string(),
                ),
            };
            if let Some(reason) = divergence {
                state.divergences += 1;
                outcome.errors.push(format!(
                    "[{}] import_environment_divergence: {reason}; it elaborates differently \
                     next to modules it does not import than in its own import closure, so \
                     nothing that imports it is checked against the declarations Lean gives it",
                    lean_main_module(state, path).1
                ));
            }
        }
        // With no stranger in `env` and no divergence so far, `env` is exactly
        // what this file's own import closure plus itself give: keep it as the
        // seed for a later isolated re-elaboration of a file that imports it.
        // Bounded, because each is a whole environment: past the bound a
        // re-elaboration seeds from a smaller kept closure or the base, which
        // is slower and gives the same environment.
        let keep_faithful = !saw_strangers
            && own.is_some()
            && state.divergences == 0
            && !state.faithful.contains_key(&canonical)
            && state
                .faithful
                .values()
                .filter(|kept| kept.is_some())
                .count()
                < FAITHFUL_ENVIRONMENT_LIMIT;
        match own {
            Some(own) if keep_faithful => {
                state
                    .faithful
                    .insert(canonical.clone(), Some(Rc::new((env.clone(), own))));
            }
            Some(own) if state.in_flight.is_empty() => {
                // The entry file of an isolated re-elaboration: its caller
                // reads this record when the environment was not kept above.
                state.own_elaborations.insert(canonical.clone(), own);
            }
            _ => {}
        }
        state.completed.insert(canonical);
    }
    result
}

/// How many faithful import environments one `clean check` run keeps as seeds
/// (see [`faithful_import_environment`]); a measured TSL run keeps 48.
const FAITHFUL_ENVIRONMENT_LIMIT: usize = 128;

/// Why what `path` did to `env` (next to modules it does not import) differs
/// from what it does in exactly its own import closure, or `None` when an
/// importer sees exactly what Lean's import of `path` gives it.
///
/// Two things are compared (see [`OwnElaboration`]): the file's failure rows
/// and checked leaves, and its effect on EVERY environment component
/// ([`clean_kernel::env::EnvEffect::disagreement`]): each entry it changes in
/// its own closure must hold the same value in `env`, and it may change
/// nothing in `env` that it does not change in its own closure. An entry only
/// the isolated side changed may already be in `env` (a stranger ran the same
/// lazy prelude initialisation or session support first), so it is looked up,
/// not assumed missing.
fn sibling_import_divergence(
    path: &Path,
    canonical: &Path,
    env: &Environment,
    own: &OwnElaboration,
    state: &mut ImportCheckState,
    allow_sorry: bool,
) -> Option<String> {
    let Some(faithful) = faithful_import_environment(path, canonical, state, allow_sorry) else {
        return Some(
            "it could not be re-elaborated in its own import closure (a module in that \
             closure diverges in turn, or the re-elaboration failed)"
                .to_string(),
        );
    };
    let (_, isolated) = &*faithful;
    elab_outcome_difference(&isolated.outcomes, &own.outcomes)
        .or_else(|| isolated.effect.disagreement(&own.effect, env))
}

/// The environment `path`'s own import closure plus `path` itself give, and
/// the declarations `path` added there — a separate `clean check` of `path`
/// whose outcome is discarded (this run already reports `path`'s
/// declarations). Memoized per file; `None` when it could not be built
/// faithfully.
///
/// The separate run starts from the faithful environment of the FIRST direct
/// import (kept when that import completed with no
/// stranger in its environment, or built by an earlier separate run), or
/// from [`ImportCheckState::base_env`] when none is kept. The rest of the
/// closure is elaborated into it from source, and every file in that rest
/// that meets a stranger there is compared in turn, so the result is
/// faithful or `None`.
fn faithful_import_environment(
    path: &Path,
    canonical: &Path,
    state: &mut ImportCheckState,
    allow_sorry: bool,
) -> Option<Rc<(Environment, OwnElaboration)>> {
    if let Some(cached) = state.faithful.get(canonical) {
        return cached.clone();
    }
    let base = state.base_env.clone()?;
    // IMPORT ORDER (round-25 verification of 3ee5ff78e). Lean loads a
    // module's imports depth-first in the order it names them, and among
    // instances of equal priority the one loaded LAST is tried first. The seed
    // is therefore the FIRST import's environment — its closure in its own
    // order, then itself, is exactly the start of Lean's order — and the rest
    // is elaborated after it by the same depth-first walk. Seeding from the
    // import with the largest closure put a later import's instances before
    // an earlier one's.
    // The caller's implicit Init is not a source dependency. New source
    // mode always starts the independent root from the bare backbone.
    let seed = if state.source_setup.is_some() {
        None
    } else {
        state
            .direct_imports
            .get(canonical)
            .and_then(|imports| imports.first())
            .filter(|first| matches!(state.faithful.get(*first), Some(Some(_))))
            .cloned()
    };
    let (mut nested_env, completed) = match &seed {
        Some(seed) => {
            let seeded = state.faithful[seed].as_ref().map(|f| f.0.clone())?;
            let mut completed = state.closures.get(seed).cloned().unwrap_or_default();
            completed.insert(seed.clone());
            (seeded, completed)
        }
        None => (base.clone(), HashSet::new()),
    };
    let mut source_setup = state
        .source_setup
        .as_ref()
        .map(clean_elab::module_driver::SourceModuleSetup::isolated);
    if let Some(setup) = &mut source_setup {
        let input = state.source_inputs.get(canonical)?;
        let header = clean_parser::Parser::parse_header(input).ok()?;
        nested_env = setup.initial_environment(&header).ok()?;
    }
    let mut nested = ImportCheckState {
        source_setup,
        source_inputs: state.source_inputs.clone(),
        source_entry: state.source_setup.as_ref().map(|_| canonical.to_path_buf()),
        completed,
        resolved_modules: state.resolved_modules.clone(),
        module_names: state.module_names.clone(),
        imports_prefer_olean: state.imports_prefer_olean,
        import_policy: state.import_policy,
        command_line_options: state.command_line_options.clone(),
        base_env: Some(base),
        closures: std::mem::take(&mut state.closures),
        direct_imports: std::mem::take(&mut state.direct_imports),
        faithful: std::mem::take(&mut state.faithful),
        import_world: state.import_world.clone(),
        ..ImportCheckState::default()
    };
    let mut nested_outcome = FileCheckOutcome::default();
    let sorry_before = sorry_count();
    let kernel_before = kernel_check_failure_count();
    let result = check_file_recursive(
        path,
        &mut nested_env,
        &mut nested,
        &mut nested_outcome,
        false,
        allow_sorry,
        true,
    );
    // (Increments minted by runs nested inside that one are already in the
    // deltas.)
    state.nested_sorry_axioms += sorry_count().saturating_sub(sorry_before);
    state.nested_kernel_check_failures +=
        kernel_check_failure_count().saturating_sub(kernel_before);
    // Closures and direct imports are properties of the import graph, the
    // same in every run; the faithful environments the nested run kept are
    // faithful for this run too.
    state.closures = std::mem::take(&mut nested.closures);
    state.direct_imports = std::mem::take(&mut nested.direct_imports);
    state.faithful = std::mem::take(&mut nested.faithful);
    let faithful = if result.is_ok() && nested.divergences == 0 {
        state
            .faithful
            .get(canonical)
            .cloned()
            .flatten()
            .or_else(|| {
                let own = nested.own_elaborations.remove(canonical)?;
                Some(Rc::new((nested_env, own)))
            })
    } else {
        None
    };
    state
        .faithful
        .insert(canonical.to_path_buf(), faithful.clone());
    faithful
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
    if state.source_setup.is_some() {
        let canonical = std::fs::canonicalize(path).unwrap_or_else(|_| path.to_path_buf());
        if is_entry_file
            && state
                .source_entry
                .as_ref()
                .is_some_and(|expected| expected != &canonical)
        {
            anyhow::bail!(
                "source module {} changed identity after its header was read",
                path.display()
            );
        }
        if let Some(previous) = state.source_inputs.get(&canonical) {
            if previous.as_ref() != content {
                anyhow::bail!(
                    "source module {} changed during isolated elaboration",
                    path.display()
                );
            }
        } else {
            state
                .source_inputs
                .insert(canonical, std::sync::Arc::from(content.as_str()));
        }
    }
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
    //
    // NOTATION SEED (queue-B rank 8). Lean's notation is an environment
    // extension; Clean's registry was file-local, so a file could not use a
    // symbol declared in a module it imports unless Clean had hand-written it.
    // `seed_from_imports` walks the file's transitive project-local `.lean`
    // closure and registers what it declares before the file is read. See
    // `clean_elab::notation_imports` for the boundary. A file with no
    // resolvable imports gets an empty seed, and `parse_file_seeded` with an
    // empty seed IS `parse_file_with_tactics_diagnostics`.
    let (notation_seed, harvest) = clean_elab::notation_imports::seed_from_imports(path, &content);
    if verbose && harvest.modules_read > 0 {
        println!(
            "Seeded {} notation(s) from {} imported module(s) ({} unresolved)",
            harvest.notations, harvest.modules_read, harvest.modules_unresolved
        );
    }
    // A refused project world refuses the imports, not the file (R-WR):
    // its `import`s are `UnresolvedImport` below, while a file with none, or
    // whose imports are the project's own source, parses in the Oracle's
    // language (`clean_olean::source_world_of`).
    let world = match &state.import_world {
        Some(imports) => clean_olean::source_world_of(imports)?,
        None => clean_olean::source_world_for_file(path, None)?.world(),
    };
    let report =
        clean_parser::parse_file_seeded_in_world(&content, &patterns, &notation_seed, world)?;
    let decls = report.decls;
    for diag in &report.diagnostics {
        let named = match &diag.tactic {
            Some(tac) => format!("tactic `{tac}`"),
            None => format!("construct `{}`", diag.construct),
        };
        // Derive the column from the authoritative byte offset rather than
        // printing `recovery_start.column`. That field is documented in
        // `clean-parser/src/lib.rs` as NOT a uniform coordinate — older error
        // sites put either a line-relative column or an absolute byte offset in
        // it — so it printed values like `column 42634`, which is not a column
        // of anything. `recovery_start.byte` is the authoritative form and
        // `line_column_for_offset` already turns it into a real (line, column).
        let (rec_line, rec_col) = line_column_for_offset(&content, diag.recovery_start.byte);
        let diagnostic = format!(
            "parser recovery [{}]: unsupported {named} at line {rec_line}, column {rec_col}: {}",
            diag.code, diag.message
        );
        let diagnostic = if is_entry_file {
            diagnostic
        } else {
            format!("[{}] {diagnostic}", lean_main_module(state, path).1)
        };
        outcome.parser_diagnostics.push(diagnostic);
    }
    let parse_time = parse_start.elapsed();
    if is_entry_file {
        outcome.timing.parse += parse_time;
    }
    if verbose {
        println!("Parsed {} declarations in {:?}", decls.len(), parse_time);
    }

    let mut file_ctx = FileContext::new();
    file_ctx.set_file_header(&report.header);
    // `-D` overrides are this file's initial option state, exactly a leading
    // `set_option` (Lean's `lean -D`; Lake's `leanOptions`).
    clean_elab::command_line_options::apply_command_line_options(
        env,
        &mut file_ctx,
        &state.command_line_options,
    );
    // Lake roots and the run's Lean world (G72, R111): the entry file's,
    // never this file's own `lean-toolchain`.
    match &state.import_world {
        Some(world) => file_ctx.set_import_context(path, world.clone()),
        None => file_ctx.set_import_context_for_file(path),
    }
    if verbose && !file_ctx.import_search_paths().is_empty() {
        println!(
            "Discovered {} Lake import search paths",
            file_ctx.import_search_paths().len()
        );
    }
    // Lean's main module, which is also the `[tag]` of this file's report
    // lines (G14): see `lean_main_module`.
    let (main_module, module) = lean_main_module(state, path);
    claim_main_module(state, path, &main_module)?;
    file_ctx.set_main_module(main_module);
    if is_entry_file {
        outcome.module = module.clone();
    }

    let decls = match &mut state.source_setup {
        Some(setup) => setup
            .prepare(
                env,
                &report.header,
                &decls,
                &mut file_ctx,
                state.completed.is_empty() && state.command_line_options.is_empty(),
            )
            .map_err(anyhow::Error::from),
        None => clean_elab::module_driver::elaborate_prelude_header(env, &decls, &mut file_ctx)
            .map_err(anyhow::Error::from),
    }
    .with_context(|| format!("failed to initialize source module in {}", path.display()))?;

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
    for decl in decls {
        let import_start = Instant::now();
        collect_intra_project_imports(decl, path, env, state, outcome, verbose, allow_sorry, json)?;
        // Only an `import` can elaborate an intra-project module here; every
        // other declaration returns at once, so an import-free file reports
        // exactly zero import time.
        if is_entry_file && matches!(decl, SurfaceDecl::Import { .. }) {
            outcome.timing.import += import_start.elapsed();
        }
        if !outcome.diverged.is_empty() {
            break;
        }
        if let SurfaceDecl::Import { paths, .. } = decl {
            if paths
                .iter()
                .any(|path| state.refused_from_source.contains_key(path.name()))
            {
                break;
            }
        }
    }

    // A dependency's exhausted declaration budget is no verdict, not a
    // refused import. Do not credit its valid prefix or manufacture failed
    // import rows from that unfinished check; retain the existing bucket.
    if !outcome.diverged.is_empty() {
        return Ok(());
    }

    // NOT CHECKED against an environment an import diverged in: the entry
    // file's declarations would be credited with a meaning Lean never gives
    // them (`theorem m : two = 3 := rfl` with `two := 3`). The divergence is
    // already an error on the outcome; nothing here is counted or credited.
    if is_entry_file && state.divergences > 0 {
        outcome.errors.push(format!(
            "{module}: not checked — an import diverged (import_environment_divergence), so \
             this file's declarations were not checked against the declarations its imports \
             define"
        ));
        return Ok(());
    }

    // What this file's OWN declarations do is measured from here (its
    // intra-project imports are already in `env`), for the sibling-import
    // comparison in [`check_file_recursive`]: the whole environment, since an
    // effect on any component (an instance registration, an attribute) reaches
    // an importer, and the failure rows the file's own declarations add.
    let env_before_own = env.clone();

    // Hand the resolution record and the unresolved-import policy to the
    // elaborator before the second pass runs the `Import` decls for real.
    file_ctx.set_import_policy(state.import_policy);
    for module in &state.satisfied_from_source {
        file_ctx.mark_import_satisfied_from_source(module);
    }
    for (module, reason) in &state.refused_from_source {
        file_ctx.mark_import_refused_from_source(module, reason.clone());
    }

    // Second pass: regular elaboration of all decls. Intra-project Import
    // decls are elaborated like any declaration and routed to
    // `process_imports_with_search_paths`. For intra-project .lean files there
    // is no .olean to load, so that path becomes a no-op — which is what we
    // want, because the relevant declarations are already in `env` from the
    // first pass above. The observer counts LEAF declarations, nested
    // `namespace`/`section` members included: counting the surface
    // `decls.len()` alone would under-report file progress (#3xxx).
    let recording = is_entry_file.then(crate::check_timing::RecordingScope::begin);
    // The per-declaration loop is the module driver's — the one the LSP runs
    // (`clean_elab::module_driver::elaborate_decls`): per declaration it
    // refills the budget, preprocesses and elaborates against `file_ctx`
    // (threaded, gap sweep B13: standalone `open` / `export` aliases and
    // file-scope macro/notation registrations persist across declarations,
    // as in Lean's file model, and the Lake-discovered search paths reach
    // `.olean` loading), flattens `namespace` / `section` / `mutual` blocks to
    // their leaves and re-validates each read-only. `CheckObserver` renders
    // this command's rows off it and stops the file after a refused `import`.
    let mut observer = check_observer::CheckObserver::new(
        state,
        outcome,
        &content,
        &module,
        is_entry_file,
        verbose,
        allow_sorry,
        json,
        decl_budget_trace_enabled(),
    );
    clean_elab::module_driver::elaborate_decls(
        env,
        decls,
        &content,
        &mut file_ctx,
        clean_elab::module_driver::DriverOptions {
            lean_front_door: true,
            ..clean_elab::module_driver::DriverOptions::default()
        },
        &mut observer,
    );
    let check_observer::CheckObserver {
        counted_leaf_decls,
        elab_outcomes,
        body_environment,
        stopped,
        ..
    } = observer;
    if stopped {
        return Ok(());
    }
    if let Some(recording) = recording {
        outcome.timing.per_declaration =
            crate::check_timing::per_declaration(recording.finish(), &content);
    }
    // Imports nested where the loop above does not look (inside a block):
    // examined here too, so no loaded artifact escapes the binding check.
    bind_loaded_imports(state, &file_ctx, outcome, is_entry_file, &module);

    if is_entry_file {
        // Report the number of leaf declarations actually examined (nested
        // namespace/section members included) rather than the count of
        // top-level surface decls, which collapses each block to 1.
        outcome.decl_count = counted_leaf_decls;
    } else {
        outcome.imported_decl_count += counted_leaf_decls;
    }

    let own = OwnElaboration {
        // Source-mode imports (including artifacts) are the working closure.
        // Keep every body effect, without comparing a cumulative imported
        // extension state against an unrelated sibling's larger closure.
        effect: env.effect_since(body_environment.as_ref().unwrap_or(&env_before_own)),
        outcomes: elab_outcomes,
    };
    state.own_elaborations.insert(
        std::fs::canonicalize(path).unwrap_or_else(|_| path.to_path_buf()),
        own,
    );

    Ok(())
}

/// Examine the artifacts `file_ctx` loaded since the last call. Disclosures
/// go to [`FileCheckOutcome::artifact_imports`]; an artifact that is not the
/// build of the source next to it becomes an error row. Returns `true` when
/// there was such an artifact: nothing more in this file may be checked.
fn bind_loaded_imports(
    state: &mut ImportCheckState,
    file_ctx: &FileContext,
    outcome: &mut FileCheckOutcome,
    is_entry_file: bool,
    module: &str,
) -> bool {
    let findings = state.import_binding.examine(file_ctx);
    outcome.artifact_imports.extend(findings.disclosures);
    let refused = !findings.refusals.is_empty();
    for row in findings.refusals {
        outcome.errors.push(if is_entry_file {
            format!("{module}: not checked — {row}")
        } else {
            format!("[{module}] not checked — {row}")
        });
    }
    refused
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
                if module_path.is_anonymous() {
                    continue;
                }
                let module_name = module_path.name();
                let module_label = surface_name_label(module_path);
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
                    && match &state.import_world {
                        Some(world) => {
                            clean_elab::olean_available_in_world(module_name, parent_path, world)
                        }
                        None => clean_elab::olean_available_for_module(module_name, parent_path),
                    }
                {
                    if verbose {
                        println!(
                            "Import `{module_label}` has a prebuilt .olean; loading it instead of \
                             elaborating source (--imports-prefer-olean)"
                        );
                    }
                    continue;
                }
                let resolved = resolve_import_path(module_name, parent_path, state);
                if let Some(import_file) = resolved {
                    let canonical_import =
                        std::fs::canonicalize(&import_file).unwrap_or_else(|_| import_file.clone());
                    state
                        .module_names
                        .entry(canonical_import)
                        .or_insert_with(|| module_name.clone());
                    if verbose {
                        println!(
                            "Resolved intra-project import `{module_label}` -> {}",
                            import_file.display()
                        );
                    }
                    let failure_mark = (
                        outcome.errors.len(),
                        outcome.parser_diagnostics.len(),
                        outcome.trust_failures.len(),
                        outcome.kernel_failures.len(),
                        outcome.diverged.len(),
                    );
                    check_file_recursive(
                        &import_file,
                        env,
                        state,
                        outcome,
                        verbose,
                        allow_sorry,
                        json,
                    )?;
                    // This module's declarations are now in `env`, from its own
                    // source. A project with no compiled artifacts has no
                    // `.olean` for it and never will — record the resolution so
                    // the fail-closed import policy does not read that absence
                    // as an unresolvable module.
                    let reason = outcome
                        .errors
                        .get(failure_mark.0)
                        .or_else(|| outcome.parser_diagnostics.get(failure_mark.1))
                        .or_else(|| outcome.trust_failures.get(failure_mark.2))
                        .or_else(|| outcome.kernel_failures.get(failure_mark.3))
                        .or_else(|| outcome.diverged.get(failure_mark.4));
                    if let Some(reason) = reason {
                        state
                            .refused_from_source
                            .entry(module_name.clone())
                            .or_insert_with(|| reason.clone());
                    }
                    if state.refused_from_source.contains_key(module_name) {
                        state.satisfied_from_source.remove(module_name);
                        break;
                    }
                    state.satisfied_from_source.insert(module_name.clone());
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
    module: &Name,
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

/// Serialises every in-process run that resets and then reads the
/// process-wide trust counters (`sorry_count`, `kernel_check_failure_count`):
/// `clean check` and `clean export-cert`, whose verdicts both read them. It is
/// the module driver's lock, so the LSP's elaboration in the same process is
/// serialised against them too.
pub(crate) fn check_file_lock() -> std::sync::MutexGuard<'static, ()> {
    clean_elab::module_driver::module_elaboration_lock()
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
        // NOT guarded on `name != "(skipped)"`, though the pass arm above it
        // is. `typecheck_elab_result` returns "(skipped)" for `Skipped`,
        // `Command` AND `Multiple` — and `Multiple` is a MUTUAL BLOCK, a real
        // declaration group whose warning is real. Suppressing this row to make
        // the summary's three numbers partition would hide a `sorry` in every
        // mutual block in the file. The summary explains its arithmetic
        // instead; that is the cheaper side of the trade.
        trust_failures.push(format!(
            "{}: declaration uses {}{}",
            clean_elab::private_names::user_facing_name(&warning.decl_name),
            registration_warning_label(&warning.kind),
            warning.via_suffix()
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
        // Unguarded, though the pass arms nearby are guarded on
        // `name != "(skipped)"`, and the asymmetry is deliberate: a hidden
        // kernel failure is worse than a summary that has to explain its own
        // arithmetic. See the trust row above for why "(skipped)" is not a
        // safe thing to suppress on.
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
        "warning: declaration '{}' uses {}{}",
        clean_elab::private_names::user_facing_name(&warning.decl_name),
        registration_warning_label(&warning.kind),
        warning.via_suffix()
    )
}

pub(crate) fn emit_check_summary(
    out: &mut impl Write,
    decl_count: usize,
    total_time: Duration,
    success_count: usize,
    failed_count: usize,
    diverged_count: usize,
    parser_diagnostic_count: usize,
) -> std::io::Result<()> {
    writeln!(
        out,
        "Checked {} declarations in {:?}",
        decl_count, total_time
    )?;
    // Always emit "N passed, M failed" so external parsers (parse_lean) can
    // classify the result without exit-code heuristics (#3078). The
    // `, K did not finish` clause is APPENDED only when K > 0, so every
    // existing consumer of the two-number line keeps parsing it unchanged.
    if diverged_count == 0 {
        writeln!(out, "  {success_count} passed, {failed_count} failed")?;
    } else {
        writeln!(
            out,
            "  {success_count} passed, {failed_count} failed, \
             {diverged_count} did not finish"
        )?;
    }
    // Recovery notes are about the SOURCE TEXT, not about any declaration's
    // verdict, so they get their own line rather than a share of the partition
    // above. Printed only when there are some.
    if parser_diagnostic_count > 0 {
        writeln!(
            out,
            "  {parser_diagnostic_count} parser recovery note(s) (not declaration failures)"
        )?;
    }
    // THE SUMMARY MAY NEVER PRINT A PARTITION THAT IS NOT ONE.
    //
    // The three counters above are scoped to the ENTRY FILE, but a failure in
    // an intra-project import is reported here too — deliberately, so the
    // exit-code contract still fires — while that module's declarations are not
    // in the denominator. When that happens the numbers genuinely do not add
    // up, and the honest thing is to say so rather than leave a reader to
    // discover it by adding them. Silence is what let the parser-recovery
    // defect survive: nothing in the output ever admitted the sum was wrong.
    let accounted = success_count + failed_count + diverged_count;
    if accounted != decl_count {
        writeln!(
            out,
            "  note: those add to {accounted}, not {decl_count} — the difference is \
             rows from imported modules, which are reported here but whose \
             declarations are not in the count above"
        )?;
    }
    Ok(())
}

fn registration_warning_label(kind: &RegistrationWarningKind) -> &'static str {
    match kind {
        RegistrationWarningKind::ExplicitSorry => "explicit sorry",
        RegistrationWarningKind::SyntheticSorry => "synthetic sorry",
        RegistrationWarningKind::TrustedArith => "trustedArith",
        RegistrationWarningKind::TrustedAy => "trustedAy",
    }
}

/// The non-zero-exit message for a run that did not come out clean.
///
/// `"check failed"` is LOAD-BEARING TEXT, not prose: `clean check`'s own
/// fail-closed import tests and the source-elaboration gate match on it. A
/// diverged run gets its own wording — it did not fail — but the failing case
/// keeps the exact string it has always had.
pub(crate) fn check_failure_message(status: &str) -> &'static str {
    match status {
        "diverged" => {
            "check did not finish: some declarations exhausted the per-declaration budget"
        }
        "nothing_checked" => "check failed: no declaration was checked",
        _ => "check failed",
    }
}

/// Format and emit the report for one finished `clean check` run.
///
/// Takes the whole [`FileCheckOutcome`] by value rather than fourteen loose
/// fields, and — load-bearing — reads NO global trust counter of its own. It
/// runs after [`collect_check_outcome`] has returned, which is after that
/// function's [`TrustCounterScope`] has zeroed `sorry_count()` and
/// `kernel_check_failure_count()`; anything it read from those would be a
/// structural zero (task #66). It formats the counters it is HANDED.
fn finalize_check_run(
    path: &Path,
    outcome: FileCheckOutcome,
    total_time: Duration,
    budgets: CheckBudgets,
    json: bool,
) -> anyhow::Result<()> {
    let FileCheckOutcome {
        lean_world,
        environment_lean_world,
        module,
        decl_count,
        imported_decl_count,
        success_count,
        errors,
        parser_diagnostics,
        trust_failures,
        kernel_failures,
        assumptions,
        artifact_imports,
        diverged,
        peak_decl_ticks,
        sorry_axioms,
        sorry_terms_minted,
        kernel_check_failures: kernel_failures_total,
        structured_failures,
        timing,
        command_line_options,
    } = outcome;
    let failed_count = errors.len() + trust_failures.len() + kernel_failures.len();
    let diverged_count = diverged.len();
    // Three-way, never two-way. `diverged` is not folded into `failed_count`
    // (nothing was refuted) and emphatically not into `success_count` (nothing
    // was proved), so a run that could not finish some declarations reports a
    // status of its own — and still exits non-zero, because a caller that
    // treats exit 0 as "the file checks out" must not be told that.
    let status = match (failed_count, diverged_count) {
        // A run that checked NOTHING has no verdict, so it is not a pass: a
        // comment-only or `open`/`set_option`-only file used to print
        // `Checked 0 declarations … 0 passed, 0 failed` and exit 0 (round-22
        // verification of `317f48b45`). Its own status, and a non-zero exit.
        (0, 0) if decl_count + imported_decl_count == 0 => "nothing_checked",
        (0, 0) => "pass",
        (0, _) => "diverged",
        _ => "fail",
    };

    if json {
        let report = CheckReport {
            schema_version: CHECK_REPORT_SCHEMA_VERSION,
            command: "clean check",
            lean_world: lean_world.tag(),
            environment_lean_world,
            file: path.display().to_string(),
            module,
            status,
            decl_count,
            success_count,
            failed_count,
            diverged_count,
            decl_budget: budgets.decl,
            options: command_line_options,
            peak_decl_ticks,
            automation_budget: budgets.automation,
            peak_automation_work: timing
                .per_declaration
                .iter()
                .map(|d| d.automation_work)
                .max()
                .unwrap_or(0),
            timing: crate::check_timing::report(timing, total_time),
            trust_summary: CheckTrustSummary {
                sorry_axioms,
                sorry_terms_minted,
                kernel_check_failures: kernel_failures_total,
            },
            errors,
            parser_recovery: parser_diagnostics,
            trust_failures,
            kernel_failures,
            assumptions,
            artifact_imports,
            diverged,
            proof_state_feedback: structured_failures,
        };
        writeln!(
            std::io::stdout(),
            "{}",
            serde_json::to_string_pretty(&report)?
        )?;
        if status == "pass" {
            return Ok(());
        }
        anyhow::bail!("{}", check_failure_message(status))
    }

    let mut out = std::io::stdout();
    let _ = emit_check_summary(
        &mut out,
        decl_count,
        total_time,
        success_count,
        failed_count,
        diverged_count,
        parser_diagnostics.len(),
    );
    let _ = emit_trust_summary(&mut out, sorry_axioms, kernel_failures_total);
    if sorry_terms_minted != sorry_axioms && sorry_terms_minted > 0 {
        let _ = writeln!(
            out,
            "  sorry terms minted by the elaborator: {sorry_terms_minted}"
        );
    }
    if !assumptions.is_empty() {
        let _ = writeln!(
            out,
            "  {} passed declaration(s) rest on non-foundational axiom(s) (assumed, not proved):",
            assumptions.len()
        );
        for row in &assumptions {
            let _ = writeln!(out, "    - {row}");
        }
    }
    if !artifact_imports.is_empty() {
        let _ = writeln!(
            out,
            "  {} {}:",
            artifact_imports.len(),
            crate::import_binding::DISCLOSURE_HEADING
        );
        for row in artifact_imports
            .iter()
            .take(crate::import_binding::DISCLOSURE_ROWS_SHOWN)
        {
            let _ = writeln!(out, "    - {row}");
        }
        if artifact_imports.len() > crate::import_binding::DISCLOSURE_ROWS_SHOWN {
            let _ = writeln!(
                out,
                "    … and {} more (all of them are in `--json` output)",
                artifact_imports.len() - crate::import_binding::DISCLOSURE_ROWS_SHOWN
            );
        }
    }

    if status == "pass" {
        return Ok(());
    }
    if status == "nothing_checked" {
        let _ = writeln!(
            out,
            "  nothing was checked: the file holds no declaration (only comments, imports or \
             administrative commands), so there is no verdict to report"
        );
    }

    let _ = emit_check_failures(
        &mut out,
        &errors,
        &parser_diagnostics,
        &trust_failures,
        &kernel_failures,
        &diverged,
    );
    anyhow::bail!("{}", check_failure_message(status))
}

#[derive(Debug, Serialize)]
struct CheckReport {
    /// Selected source grammar. Implicit CheckoutPin keeps R81/R111 binding.
    lean_world: &'static str,
    /// The actual imported/declaration-bound environment world, if any. It
    /// can be historical under an implicit CheckoutPin's LEAN_PATH.
    environment_lean_world: Option<&'static str>,
    schema_version: &'static str,
    command: &'static str,
    file: String,
    module: String,
    /// `pass` / `diverged` / `fail` / `nothing_checked`. `nothing_checked`:
    /// no declaration was examined, so there is no verdict (non-zero exit).
    /// `diverged` is its own status: some
    /// declaration did not finish, so the file has no verdict — not a passing
    /// one and not a failing one.
    status: &'static str,
    decl_count: usize,
    success_count: usize,
    failed_count: usize,
    /// Declarations that spent the whole ambient per-declaration budget.
    /// Disjoint from both `success_count` and `failed_count`.
    diverged_count: usize,
    /// The ambient per-declaration budget this run used, in kernel
    /// operations (`0` = unlimited). Recorded so a consumer can tell a
    /// `diverged` row measured under a tight budget from one under the
    /// default, and reproduce either.
    decl_budget: u64,
    /// The `-D` overrides (`name=value`) every file of the run was elaborated
    /// under, in order; empty when none. ADDITIVE in schema v1.
    options: Vec<String>,
    /// The most ambient ticks any ONE declaration in this run spent. Read
    /// against `decl_budget` this is the run's headroom, reported whether or
    /// not anything diverged — see `scripts/decl_budget_calibrate.sh`.
    peak_decl_ticks: u64,
    /// The per-declaration AUTOMATION work budget this run used (`0` =
    /// unlimited). ADDITIVE in schema v1.
    automation_budget: u64,
    /// The most automation work any one entry-file declaration spent (the max
    /// of `timing.per_declaration[].automation_work`): the run's headroom
    /// against `automation_budget`, reported whether or not anything ran out.
    /// ADDITIVE in schema v1.
    peak_automation_work: u64,
    /// Phase and per-declaration wall time. ADDITIVE in schema v1; read by
    /// `scripts/source_elab_gate.sh`'s performance leg.
    timing: crate::check_timing::CheckTimingReport,
    trust_summary: CheckTrustSummary,
    errors: Vec<String>,
    /// Parser recovery notes. ADDITIVE in schema v1: these strings used to be
    /// mixed into `errors`, where they inflated `failed_count` past
    /// `decl_count`. A consumer that classifies them
    /// (`scripts/srcelab_classify.py`) must read BOTH arrays.
    parser_recovery: Vec<String>,
    trust_failures: Vec<String>,
    kernel_failures: Vec<String>,
    /// Passed declarations whose verdict rests on a domain axiom — each a
    /// pass under an assumption, never an unconditional one.
    assumptions: Vec<String>,
    /// Imported modules taken from artifacts as built, with no source
    /// compared (ADDITIVE in schema v1; see `import_binding.rs`).
    artifact_imports: Vec<String>,
    diverged: Vec<String>,
    proof_state_feedback: Vec<CheckObligationFeedback>,
}

#[derive(Debug, Serialize)]
struct CheckTrustSummary {
    /// Checked declarations whose constant closure reaches `sorryAx` / `sorry`
    /// (see `FileCheckOutcome::sorry_axioms`).
    sorry_axioms: u64,
    /// Sorry terms the elaborator created. ADDITIVE (late v1, kept in v2):
    /// this was `sorry_axioms`' meaning before the closure census.
    sorry_terms_minted: u64,
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
    Source,
    Elaboration,
    Tactic,
    KernelValidation,
}

impl CheckFailureReason {
    fn as_str(&self) -> &'static str {
        match self {
            Self::Source => "source_error",
            Self::Elaboration => "elaboration_failed",
            Self::Tactic => "tactic_failed",
            Self::KernelValidation => "kernel_validation_failed",
        }
    }
}

/// Render one declaration's elaboration failure.
///
/// THE SINGLE RENDERING SITE. Until 2026-08-27 there were two, and they did not
/// agree: a TOP-LEVEL declaration's failure was rendered with `{e:?}` (Debug)
/// and carried its line, while a declaration inside a namespace / section /
/// mutual block was rendered with `{e}` (Display) and carried no line. Every
/// Mathlib declaration is namespaced, so the corpus artifact carried the
/// Display form while every terminal probe on a bare fixture showed the Debug
/// form — which is why the source-elab recon's probe outputs did not match the
/// committed evidence file, and why a probe could pin a string the corpus can
/// never contain.
///
/// Display wins the unification, for the two reasons
/// `tests/fixtures/source_frontier/p17` measures. The `#[error(...)]` strings
/// are written to lead with the fact that matters (`Unknown identifier: <name>`),
/// so they survive `per_error_class`'s 400-char truncation and are classified by
/// `scripts/srcelab_classify.py` on the mechanism rather than falling into the
/// residual `other` bucket, where every `Variant { field: … }` dump lands. The
/// line number is added to BOTH paths for the same reason: the namespaced path
/// is the one the corpus uses, and it was the one without a position.
fn elaboration_error_diagnostic(
    is_entry_file: bool,
    module: &str,
    named: &str,
    position: &str,
    error: &clean_elab::ElabError,
) -> String {
    if is_entry_file {
        format!("{named}elaboration error{position}: {error}")
    } else {
        format!("[{module}] {named}elaboration error{position}: {error}")
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
    // `innermost()` looks through the tactic-attribution wrapper
    // (`ElabError::InTactic`): it names WHICH tactic failed, so the blocking
    // reason must still be the one the underlying diagnostic reports.
    let reason = match error.innermost() {
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
        TacticError::UnknownTactic(_) | TacticError::UnknownTacticWithSuggestions { .. } => {
            "unknown_tactic"
        }
        TacticError::TypeCheckFailed(_) => "type_check_failed",
        TacticError::UnificationFailed(_) => "unification_failed",
        TacticError::HypothesisNotFound(_) => "missing_hypothesis",
        // A DISTINCT class from the one above: nothing was named and nothing
        // was missing — a whole-context search found no match. Classifying
        // both as "missing_hypothesis" is what hid 11 corpus entries behind a
        // label describing a different failure.
        TacticError::NoMatchingHypothesis { .. } => "no_matching_hypothesis",
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
        }
        | SurfaceDecl::GuardMsgs { cmd: body, .. } => {
            return normalized_proof_state_for_decl(body, source)
        }
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
            name: surface_name_label(&binder.name),
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

pub(crate) fn line_column_for_offset(source: &str, offset: usize) -> (u32, u32) {
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

/// Lean's main module for `path` and its label: the name an importer's
/// `import` statement wrote for this file, else (the entry file) Lake's name
/// for it (`clean_elab::lean_module_name_for_file`: the path relative to its
/// package's `srcDir`, however the file was invoked), else, outside any Lake
/// package, `lean <file>`'s rule (`clean_elab::path_module_name`: the real
/// path relative to the working directory, `_stdin` outside it). The name
/// mints the file's `private` declarations (`_private.<module>.0.<name>`, G21)
/// and its label tags each of its report lines (`[Pkg.A] bad: …`, G14).
fn lean_main_module(state: &ImportCheckState, path: &Path) -> (Name, String) {
    let canonical_path = std::fs::canonicalize(path).unwrap_or_else(|_| path.to_path_buf());
    match state
        .module_names
        .get(&canonical_path)
        .cloned()
        .or_else(|| clean_elab::lean_module_name_for_file(path))
    {
        Some(module) => {
            let label = module.to_string();
            (module, label)
        }
        None => (
            clean_elab::path_module_name(path),
            clean_elab::path_module_label(path),
        ),
    }
}

/// Record that `path` is the file this run names `module`, and refuse a
/// second file for the same name (see `ImportCheckState::module_owners`).
/// Lean 4.8.0 never names two files alike: in the layout that reaches this
/// refusal (`import A` meaning both `src/A.lean` and `src/sub/A.lean`), `lake
/// build` reports "build cycle detected".
fn claim_main_module(
    state: &mut ImportCheckState,
    path: &Path,
    module: &Name,
) -> anyhow::Result<()> {
    let canonical = std::fs::canonicalize(path).unwrap_or_else(|_| path.to_path_buf());
    match state.module_owners.get(module) {
        Some(owner) if owner != &canonical => anyhow::bail!(
            "module name `{module}` would name two files, {} and {}: Lean gives one module \
             name to one file, and the two would share their `private` declarations \
             (`_private.{module}.0.…`); import each file by its own module name",
            owner.display(),
            canonical.display()
        ),
        Some(_) => Ok(()),
        None => {
            state.module_owners.insert(module.clone(), canonical);
            Ok(())
        }
    }
}

/// Human-facing spelling only; never use this label as a declaration/import key.
fn surface_name_label(name: &SurfaceName) -> String {
    name.source_spelling()
        .unwrap_or_else(|| format!("{:?}", name.name()))
}

pub(crate) fn surface_decl_name(decl: &SurfaceDecl) -> Option<String> {
    match decl {
        SurfaceDecl::Alias { names, .. } => names.first().map(|(name, _)| surface_name_label(name)),
        SurfaceDecl::Def { name, .. }
        | SurfaceDecl::Theorem { name, .. }
        | SurfaceDecl::Axiom { name, .. }
        | SurfaceDecl::Opaque { name, .. }
        | SurfaceDecl::Inductive { name, .. }
        | SurfaceDecl::Coinductive { name, .. }
        | SurfaceDecl::Structure { name, .. }
        | SurfaceDecl::Class { name, .. }
        | SurfaceDecl::Namespace { name, .. } => Some(surface_name_label(name)),
        SurfaceDecl::Instance { name, .. } => name.as_ref().map(surface_name_label),
        SurfaceDecl::Section { name, .. } => name.as_ref().map(surface_name_label),
        SurfaceDecl::Print { name, .. } | SurfaceDecl::PrintAxioms { name, .. } => {
            Some(surface_name_label(name))
        }
        SurfaceDecl::DeclareSyntaxCat { name, .. } => Some(surface_name_label(name)),
        SurfaceDecl::Syntax { name, .. } | SurfaceDecl::MacroRules { name, .. } => {
            name.as_ref().map(surface_name_label)
        }
        SurfaceDecl::SetOption {
            body: Some(body), ..
        }
        | SurfaceDecl::Open {
            body: Some(body), ..
        } => surface_decl_name(body),
        SurfaceDecl::GuardMsgs { cmd, .. } => surface_decl_name(cmd),
        _ => None,
    }
}

pub(crate) fn surface_decl_span(decl: &SurfaceDecl) -> Option<Span> {
    match decl {
        SurfaceDecl::Def { span, .. }
        | SurfaceDecl::Alias { span, .. }
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
        | SurfaceDecl::IncludeVars { span, .. }
        | SurfaceDecl::OmitVars { span, .. }
        | SurfaceDecl::Open { span, .. }
        | SurfaceDecl::Export { span, .. }
        | SurfaceDecl::DerivingInstance { span, .. }
        | SurfaceDecl::Check { span, .. }
        | SurfaceDecl::Eval { span, .. }
        | SurfaceDecl::Reduce { span, .. }
        | SurfaceDecl::Print { span, .. }
        | SurfaceDecl::PrintAxioms { span, .. }
        | SurfaceDecl::Guard { span, .. }
        | SurfaceDecl::GuardMsgs { span, .. }
        | SurfaceDecl::Mutual { span, .. }
        | SurfaceDecl::Syntax { span, .. }
        | SurfaceDecl::DeclareSyntaxCat { span, .. }
        | SurfaceDecl::Macro { span, .. }
        | SurfaceDecl::MacroRules { span, .. }
        | SurfaceDecl::Notation { span, .. }
        | SurfaceDecl::Elab { span, .. }
        | SurfaceDecl::Prelude { span }
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
    parser_diagnostics: &[String],
    trust_failures: &[String],
    kernel_failures: &[String],
    diverged: &[String],
) -> std::io::Result<()> {
    if !errors.is_empty() || !trust_failures.is_empty() || !kernel_failures.is_empty() {
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
    }
    if !parser_diagnostics.is_empty() {
        // Own heading, own marker. These are real and worth reading -- each one
        // is a construct the parser could not take -- but under `Errors:` with a
        // `✗` beside it, a note about the source text read as a verdict on a
        // declaration, and the failure count said the same.
        writeln!(out, "\nParser recovery:")?;
        for note in parser_diagnostics {
            writeln!(out, "  ⚠ {note}")?;
        }
    }
    if !diverged.is_empty() {
        // Under its own heading, with its own marker. A `✗` here would read as
        // "this declaration is wrong", which is exactly what the run does NOT
        // know.
        writeln!(out, "\nDid not finish:")?;
        for row in diverged {
            writeln!(out, "  ⏱ {row}")?;
        }
    }
    Ok(())
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
                println!(
                    "  {} {desc}: {}",
                    status.display_marker(),
                    status.display_text()
                );
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
    use super::parse_only_counts;

    /// `parse_only_counts` with an EMPTY notation seed — the pre-rank-8 code
    /// path, which `parse_file_seeded` reduces to exactly when nothing is
    /// seeded.
    fn unseeded_parse_only_counts(content: &str) -> super::ParseOnlyCounts {
        parse_only_counts(content, &clean_parser::NotationSeed::new())
    }
    use clean_kernel::{Environment, Name};

    /// Parse-only counting: a file with two good decls and one malformed decl
    /// classifies the malformed region as a `RawDecl` recovery failure, never
    /// as a parse (soundness of the parse-rate measurement).
    #[test]
    fn test_parse_only_counts_good_and_rawdecl_recovered() {
        // Same shape as the parser's own recovery fixture
        // (`test_file_error_recovery_skips_malformed_decls`).
        let counts = unseeded_parse_only_counts("def foo := 1\ndef ??? := !!!\ndef bar := 2\n");
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
        let counts = unseeded_parse_only_counts("def x : Sort (u + 9999) := x\n");
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
        let counts =
            unseeded_parse_only_counts("namespace Foo\n  def bad := \n  def good := 1\nend Foo\n");
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
        let counts = unseeded_parse_only_counts("def a := 1\ndef b := 2\naxiom c : Type\n");
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

    /// Queue-B rank 8, the two-file repro stated in the brick.
    ///
    /// `Lib/Defs.lean` declares `notation "‖" e "‖" => norm e`; `Use.lean`
    /// imports it and uses `‖a‖` while declaring no notation of its own.
    /// Before the notation seed this failed under BOTH `--parse-only` and full
    /// `clean check` with `unknown operator or character '‖'`, because Clean's
    /// notation registry was file-local.
    ///
    /// The control is the same file with the `import` line removed: the seed
    /// is then empty and the declaration must still be unparseable, which is
    /// what proves the import — not some unrelated grammar change — is what
    /// made it parse.
    #[test]
    fn test_parse_only_seeds_notation_from_an_imported_module() {
        use std::fs;
        let dir = tempfile::tempdir().expect("tempdir");
        let root = dir.path();
        fs::create_dir_all(root.join("Lib")).expect("mkdir Lib");
        fs::write(
            root.join("Lib/Defs.lean"),
            "notation \"‖\" e \"‖\" => norm e\n",
        )
        .expect("Lib/Defs.lean");

        let user_body = "def size (a : Nat) : Nat := ‖a‖\n";
        let with_import = root.join("Use.lean");
        fs::write(&with_import, format!("import Lib.Defs\n{user_body}")).expect("Use.lean");
        let without_import = root.join("Alone.lean");
        fs::write(&without_import, user_body).expect("Alone.lean");

        let control = {
            let content = fs::read_to_string(&without_import).expect("read");
            let (seed, stats) =
                clean_elab::notation_imports::seed_from_imports(&without_import, &content);
            assert_eq!(stats.modules_read, 0, "control imports nothing");
            assert!(seed.is_empty());
            parse_only_counts(&content, &seed)
        };
        assert_eq!(
            control.rawdecl_recovered, 1,
            "control: without the import the notation is unknown, got {control:?}"
        );
        assert_eq!(control.decls, 1, "control has one leaf, got {control:?}");

        let content = fs::read_to_string(&with_import).expect("read");
        let (seed, stats) = clean_elab::notation_imports::seed_from_imports(&with_import, &content);
        assert_eq!(stats.modules_read, 1, "Lib.Defs must resolve and be read");
        assert_eq!(stats.notations, 1, "one notation command harvested");
        let seeded = parse_only_counts(&content, &seed);
        assert_eq!(
            seeded.rawdecl_recovered, 0,
            "the imported notation must make the declaration parse, got {seeded:?}"
        );
        // TWO leaves, not one: `count_parse_only_leaves` counts the `import`
        // command itself as a declaration, so the seeded file's denominator is
        // the control's plus the import line. Pinned explicitly because a
        // parse-rate reading that silently mixes the two denominators is the
        // exact way this measurement could flatter itself.
        assert_eq!(seeded.decls, 2, "import + def, got {seeded:?}");
        assert_eq!(seeded.parse_ok, 2, "got {seeded:?}");
    }

    /// The end-to-end command, not just its counting helper: `parse_only_check`
    /// must build the seed itself, so the capability has its production caller.
    #[test]
    fn test_parse_only_check_command_uses_the_import_seed() {
        use std::fs;
        let dir = tempfile::tempdir().expect("tempdir");
        let root = dir.path();
        fs::create_dir_all(root.join("Lib")).expect("mkdir Lib");
        fs::write(root.join("Lib/Ops.lean"), "infixr:25 \" ~~> \" => Prod\n")
            .expect("Lib/Ops.lean");
        let use_path = root.join("UseOps.lean");
        fs::write(
            &use_path,
            "import Lib.Ops\ndef q (A B : Type) : Type := A ~~> B\n",
        )
        .expect("UseOps.lean");

        super::parse_only_check(&use_path, false)
            .expect("`clean check --parse-only` must parse a file using imported notation");
    }

    /// The same repro through the ELABORATING path, not the parse meter: a
    /// two-file project where the notation and its expansion head both live in
    /// the imported module. This is what makes the seed a capability rather
    /// than a measurement artefact.
    #[test]
    fn check_file_elaborates_a_use_of_imported_notation() {
        use std::fs;
        let dir = tempfile::tempdir().expect("tempdir");
        let root = dir.path();
        fs::write(root.join("lakefile.lean"), "package proj\n").expect("lakefile");
        fs::write(
            root.join("Defs.lean"),
            "def normN (n : Nat) : Nat := n\nnotation \"‖\" e \"‖\" => normN e\n",
        )
        .expect("Defs.lean");
        let use_path = root.join("UseDefs.lean");
        fs::write(&use_path, "import Defs\ndef size (a : Nat) : Nat := ‖a‖\n")
            .expect("UseDefs.lean");

        check_file_with_json(&use_path, false, false, PreludeMode::Builtin, false).expect(
            "`clean check` must elaborate a declaration that uses notation from an imported module",
        );
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
            via: Vec::new(),
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
            via: Vec::new(),
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

    use super::{check_file_with_json, check_file_with_json_with_imports, ImportCheckState};
    use clean_elab::resolve_intra_project_import;
    use clean_kernel::cli::PreludeMode;
    use clean_parser::SurfaceName;
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

    // -- Fail-closed imports (queue-B rank 1) ----------------------------
    //
    // Reproduction these pin, measured at `84129fce7` on the release binary:
    //
    //   $ printf 'import Mathlib.Utterly.Fake.Nonsense\ntheorem t3 …' > fake.lean
    //   $ ./target/release/clean check fake.lean
    //   Checked 1 declarations in 298.342125ms
    //     1 passed, 0 failed                       # exit 0
    //
    // The module does not exist. A hand-written `Ring` was substituted by the
    // `Mathlib.*` PREFIX WILDCARD in `clean-elab`'s prelude providers and the
    // file reported green — so a `clean check` PASS could not be distinguished
    // from a run against ~30 hand-written structures, and no aggregate measured
    // through this command was falsifiable.

    /// The exact negative control from the brick. Must FAIL now, naming the
    /// module.
    #[test]
    fn check_file_fails_closed_on_nonexistent_mathlib_module() {
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("Fake.lean");
        fs::write(
            &path,
            "import Mathlib.Utterly.Fake.Nonsense\n\
             theorem t3 (R : Type) [Ring R] (a : R) : a = a := rfl\n",
        )
        .expect("write fixture");

        let err = check_file_with_json_with_imports(
            &path,
            false,
            false,
            PreludeMode::Builtin,
            false,
            false,
            clean_elab::ImportPolicy::FailClosed,
            clean_kernel::cli::DEFAULT_DECL_BUDGET,
            clean_kernel::cli::DEFAULT_AUTOMATION_BUDGET,
            &[],
        )
        .expect_err("a file whose import names a nonexistent module must not report a pass");
        assert!(
            err.to_string().contains("check failed"),
            "expected the run to fail, got: {err}"
        );
    }

    /// A module that is not `Mathlib.*` and has no provider at all took the
    /// same silent path (`let _ = init_prelude_for_module(…)?; Ok(())`), so the
    /// hole was never Mathlib-specific. Measured green at `84129fce7` too:
    /// `import Totally.Fake.Module` + `theorem t4 : 1 = 1 := rfl` reported
    /// `1 passed, 0 failed`, exit 0.
    #[test]
    fn check_file_fails_closed_on_unknown_non_mathlib_module() {
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("Fake2.lean");
        fs::write(
            &path,
            "import Totally.Fake.Module\ntheorem t4 : 1 = 1 := rfl\n",
        )
        .expect("write fixture");

        check_file_with_json_with_imports(
            &path,
            false,
            false,
            PreludeMode::Builtin,
            false,
            false,
            clean_elab::ImportPolicy::FailClosed,
            clean_kernel::cli::DEFAULT_DECL_BUDGET,
            clean_kernel::cli::DEFAULT_AUTOMATION_BUDGET,
            &[],
        )
        .expect_err("an import that resolves to nothing at all must not report a pass");
    }

    /// POSITIVE CONTROL for both refusals above: the same file under
    /// `--permissive-imports` must still pass. Without this, a fixture that
    /// broke for an unrelated reason would satisfy the two `expect_err`s and
    /// they would be measuring nothing.
    ///
    /// It deliberately uses the non-`Mathlib` fixture and a theorem that needs
    /// no imported constant, because the `Mathlib.*` stub set is registered
    /// behind a PROCESS-GLOBAL `MATHLIB_INIT` flag while the environment is
    /// per-run — so asserting on it here would make the test depend on which
    /// other test in this binary ran first.
    #[test]
    fn check_file_permissive_imports_accepts_the_unresolvable_module() {
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("FakePermissive.lean");
        fs::write(
            &path,
            "import Totally.Fake.Module\ntheorem t4 : 1 = 1 := rfl\n",
        )
        .expect("write fixture");

        check_file_with_json_with_imports(
            &path,
            false,
            false,
            PreludeMode::Builtin,
            false,
            false,
            clean_elab::ImportPolicy::Permissive,
            clean_kernel::cli::DEFAULT_DECL_BUDGET,
            clean_kernel::cli::DEFAULT_AUTOMATION_BUDGET,
            &[],
        )
        .expect("--permissive-imports must keep the legacy warn-and-continue behavior");
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

        let module = SurfaceName::generated_path("Mathlib.Data.Real.Basic");
        let resolved = resolve_intra_project_import(module.name(), &file);
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

        let module = SurfaceName::generated_path("Sub.Inner");
        let resolved = resolve_intra_project_import(module.name(), &entry)
            .expect("Sub.Inner should resolve to Sub/Inner.lean under the Lake root");
        assert!(
            resolved.ends_with("Sub/Inner.lean"),
            "resolved path: {resolved:?}"
        );
    }

    #[test]
    fn import_resolution_cache_preserves_quoted_filesystem_components() {
        let dir = tempfile::tempdir().expect("tempdir");
        let root = dir.path();
        fs::write(root.join("lakefile.lean"), "package proj\n").expect("lakefile");
        fs::create_dir(root.join("A")).expect("nested directory");
        let quoted_path = root.join("A.B.lean");
        let nested_path = root.join("A/B.lean");
        fs::write(&quoted_path, "def quotedLeaf : Nat := 1\n").expect("quoted module");
        fs::write(&nested_path, "def nestedLeaf : Nat := 2\n").expect("nested module");
        // Lake-root discovery canonicalizes the entry path, including macOS's
        // /var -> /private/var alias. Compare exact canonical module paths.
        let quoted_path = quoted_path.canonicalize().expect("canonical quoted module");
        let nested_path = nested_path.canonicalize().expect("canonical nested module");
        let entry = root.join("Entry.lean");
        fs::write(&entry, "import «A.B»\nimport A.B\n").expect("entry");
        let quoted = clean_parser::parse_name("«A.B»").expect("quoted import");
        let nested = clean_parser::parse_name("A.B").expect("nested import");
        let mut state = ImportCheckState::default();
        for _ in 0..2 {
            assert_eq!(
                super::resolve_import_path(quoted.name(), &entry, &mut state),
                Some(quoted_path.clone())
            );
            assert_eq!(
                super::resolve_import_path(nested.name(), &entry, &mut state),
                Some(nested_path.clone())
            );
        }
        assert_eq!(state.resolved_modules.len(), 2);
    }

    #[test]
    fn check_file_loads_both_quoted_and_hierarchical_modules() {
        let dir = tempfile::tempdir().expect("tempdir");
        let root = dir.path();
        fs::write(root.join("lakefile.lean"), "package proj\n").expect("lakefile");
        fs::create_dir(root.join("A")).expect("nested directory");
        fs::write(root.join("A.B.lean"), "def quotedLeaf : Nat := 1\n").expect("quoted module");
        fs::write(root.join("A/B.lean"), "def nestedLeaf : Nat := 2\n").expect("nested module");
        let entry = root.join("Entry.lean");
        fs::write(
            &entry,
            "import «A.B»\nimport A.B\ndef both : Nat := Nat.add quotedLeaf nestedLeaf\n",
        )
        .expect("entry");
        check_file_with_json(&entry, false, false, PreludeMode::Builtin, false)
            .expect("both real modules");
    }

    #[test]
    fn check_file_missing_quoted_module_cannot_borrow_hierarchical_twin() {
        let dir = tempfile::tempdir().expect("tempdir");
        let root = dir.path();
        fs::write(root.join("lakefile.lean"), "package proj\n").expect("lakefile");
        fs::create_dir(root.join("A")).expect("nested directory");
        fs::write(root.join("A/B.lean"), "def nestedLeaf : Nat := 2\n").expect("nested module");
        let entry = root.join("Entry.lean");
        fs::write(
            &entry,
            "import A.B\nimport «A.B»\ndef result : Nat := nestedLeaf\n",
        )
        .expect("entry");
        check_file_with_json(&entry, false, false, PreludeMode::Builtin, false)
            .expect_err("missing exact quoted module must refuse");
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

#[cfg(test)]
mod coinductive_reachability_tests {
    use super::check_file;
    use std::path::Path;

    /// BRICK 0a of the rank-1 full-gfp plan
    /// (`designs/2026-08-25-rank1-full-gfp-lowering.md`): the `coinductive`
    /// surface must be reachable through the REAL check path — the plan's
    /// recon found NO CLI-path test existed, and the nested-local-lift
    /// episode proved green elaborator unit tests can coexist with a dead
    /// CLI route. Measured live first (2026-08-25, release binary:
    /// `Checked 13 declarations … 13 passed, 0 failed`; 16/16 since the
    /// paco/accumulation rung grew the generated family to 10 companions —
    /// `Bisim.acc` + `Bisim.coind_upto`, 2026-08-26; 24/24 since the paco
    /// parameterized-tower rung grew it to 18 — the 8-companion
    /// `Bisim.paco` tower, 2026-08-26); this pins it. The
    /// fixture's `bisim_refl` is provable ONLY in the greatest fixpoint, so
    /// this also guards against the route silently regressing to an lfp
    /// reading.
    #[test]
    fn test_coinductive_v1_reachable_through_check_path() {
        let fixture = Path::new("../../tests/fixtures/coinductive/bisim_v1_reachability.lean");
        assert!(
            fixture.is_file(),
            "committed fixture missing: {}",
            fixture.display()
        );
        check_file(
            fixture,
            false,
            false,
            clean_kernel::cli::PreludeMode::Builtin,
        )
        .expect("the v1 coinductive fixture must pass the real check path");
    }
}
