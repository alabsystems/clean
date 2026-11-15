// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Clean-native project authority checks.
//!
//! The `clean project check` verb scans a directory of `.clean` / `.lean`
//! source files, runs Clean's own parser, elaborator and kernel validation
//! over each module with external `.olean` import authority disabled, and
//! emits a deterministic JSON or human-readable report.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::io::{self, Write};
use std::path::{Path, PathBuf};

use clap::{Args, Subcommand};
use clean_elab::register::reset_kernel_check_counter;
use clean_features::{Category, Example, FeatureDescriptor, RefKind, Reference, Stability};
use clean_kernel::sorry::reset_sorry_counter;
use clean_kernel::{Environment, Name};
use clean_parser::{parse_file_with_tactics, SurfaceDecl, SurfaceName};
use serde::Serialize;
use walkdir::WalkDir;

// v2 (2026-09-17, K5 vacuous-pass fix). v1's `declarations_checked` carried the
// number of declarations that PASSED, not the number checked, and both numbers
// counted top-level blocks rather than declarations — a package whose decls all
// live inside `namespace` blocks reported `declarations_checked: 0` next to
// `status: pass`. v2 gives the three counters their plain meanings:
//
//   declarations_parsed  — leaf surface declarations the parser produced
//   declarations_checked — leaf declarations the checker examined (passed + failed)
//   declarations_passed  — of those, the ones that passed (v1's `declarations_checked`)
//   declarations_failed  — of those, the ones that failed
//
// The version string moves because the MEANING of an existing key changed; a
// reader pinned to v1 must not silently read v2 numbers as v1 numbers.
//
// v3 (2026-09-25, closure-aware credit). Two existing keys changed meaning:
//
//   declarations_passed — now counts only declarations whose cited closure the
//     `ImportedConeGate` accepts, the rule `clean check` applies. v2 credited
//     `theorem t : 1 = 2 := A.s` with `A.s := sorry`; v3 fails it with a
//     `cited_closure_not_credited` blocker.
//   modules[].status — `pass` now means: no blocker of its own, no failed
//     project-local import, and at least one declaration checked. The other
//     values are `fail`, `import_failed`, `nothing_checked` and
//     `not_checked`; v2 said `pass` for all of the first three shapes. The
//     summary gains one `modules_<status>` counter per value.
//
// v4 (2026-09-26, per-module import environments). Every counter and status
// changed population: v3 checked all modules against ONE environment in load
// order, so a module was credited through declarations and instances of
// modules it does not import (`theorem t : (2 : Nat) = 3 := rfl` passed via an
// unrelated module's `OfNat Nat 2` instance). v4 checks each module against
// the prelude plus its own import closure, and adds the module blocker kind
// `import_environment_divergence`.
//
// v5 (2026-09-26, sibling-import leak through instance registration).
// `declarations_passed` (and `declarations_passed_on_assumptions`) no longer
// count the passes of a module with a failed project-local import; those move
// to the new `declarations_not_credited`, so `declarations_checked` is
// `passed + failed + not_credited`. The divergence check behind
// `import_environment_divergence` now compares a module's effect on every
// environment component and how each of its declarations elaborated, not only
// the constants it adds.
const PROJECT_CHECK_SCHEMA_VERSION: &str = "Clean-project-check-report-v5";

mod declarations;
mod sources;
use declarations::check_project_module_with_env;
#[cfg(test)]
use declarations::typecheck_elab_result;
use sources::{
    check_project_modules, lean_import_order, project_local_dependency_indices,
    scan_project_sources, ParsedProjectModule, ProjectSource,
};
#[cfg(test)]
use sources::{count_declaration_leaves, module_identity_for_relative_path, parse_project_imports};
#[cfg(test)]
mod typed_name_tests;
#[cfg(test)]
mod vacuity_tests;
const SOURCE_EXTENSIONS: &[&str] = &["clean", "lean"];
const EXCLUDED_DIRS: &[&str] = &[
    ".cake",
    ".git",
    ".lake",
    ".mathverse",
    "build",
    "dist",
    "node_modules",
    "target",
];

const DESIGN_REF: Reference = Reference {
    kind: RefKind::Design,
    label: "Clean-native project check",
    target: "docs/cli/project-check.md",
};

const CLI_CRATE_REF: Reference = Reference {
    kind: RefKind::Crate,
    label: "clean-cli",
    target: "clean-cli",
};

#[derive(Debug, Clone, Subcommand)]
pub(crate) enum ProjectCommands {
    /// Check a Clean-native project without using Lean / Lake authority.
    Check(ProjectCheckArgs),
}

#[derive(Debug, Clone, Args)]
pub(crate) struct ProjectCheckArgs {
    /// Project root containing `.clean` or `.lean` source files.
    #[arg(value_name = "PROJECT")]
    pub(crate) project: PathBuf,
    /// Count declarations that use `sorry` as passed (they are checked either
    /// way); kernel check failures still block.
    #[arg(long)]
    pub(crate) allow_sorry: bool,
    /// Emit JSON instead of compact human-readable output.
    #[arg(long)]
    pub(crate) json: bool,
}

pub(crate) fn handle_project_command(command: ProjectCommands) -> anyhow::Result<()> {
    match command {
        ProjectCommands::Check(args) => run_project_check(args),
    }
}

fn run_project_check(args: ProjectCheckArgs) -> anyhow::Result<()> {
    let report = build_project_check_report(&args)?;
    if args.json {
        let stdout = io::stdout();
        let mut out = stdout.lock();
        writeln!(out, "{}", serde_json::to_string_pretty(&report)?)?;
    } else {
        render_project_check_human(&mut io::stdout(), &report)?;
    }

    if report.status == "pass" {
        Ok(())
    } else {
        anyhow::bail!(
            "project check failed: {} authority blocker(s), {} diagnostic(s)",
            report.summary.authority_blockers,
            report.summary.diagnostics
        )
    }
}

fn build_project_check_report(args: &ProjectCheckArgs) -> anyhow::Result<ProjectCheckReport> {
    let root = fs::canonicalize(&args.project).map_err(|err| {
        anyhow::anyhow!(
            "failed to resolve project root {}: {err}",
            args.project.display()
        )
    })?;
    if !root.is_dir() {
        anyhow::bail!("project check requires a directory: {}", root.display());
    }

    let sources = scan_project_sources(&root)?;
    let module_sources = sources
        .iter()
        .map(|source| (source.identity.clone(), source.relative_path.clone()))
        .collect::<BTreeMap<_, _>>();

    let modules = check_project_modules(&sources, &module_sources, args.allow_sorry);
    let mut diagnostics = modules
        .iter()
        .flat_map(|module| module.diagnostics.iter().cloned())
        .collect::<Vec<_>>();
    let mut authority_blockers = modules
        .iter()
        .flat_map(|module| module.authority_blockers.iter().cloned())
        .collect::<Vec<_>>();

    if sources.is_empty() {
        let blocker = AuthorityBlocker::project(
            "no_source_files",
            "project contains no .clean or .lean source files to check",
        );
        diagnostics.push(ProjectDiagnostic::from_blocker(&blocker));
        authority_blockers.push(blocker);
    }

    let declarations_parsed = modules
        .iter()
        .map(|module| module.decl_count)
        .sum::<usize>();
    let declarations_checked = modules
        .iter()
        .map(|module| module.checked_count)
        .sum::<usize>();
    if let Some(blocker) = vacuous_run_blocker(declarations_parsed, declarations_checked) {
        diagnostics.push(ProjectDiagnostic::from_blocker(&blocker));
        authority_blockers.push(blocker);
    }

    let summary = summarize_project(&modules, diagnostics.len(), authority_blockers.len());
    let status = if authority_blockers.is_empty() {
        "pass"
    } else {
        "fail"
    };

    Ok(ProjectCheckReport {
        schema_version: PROJECT_CHECK_SCHEMA_VERSION,
        command: "clean project check",
        project: root.display().to_string(),
        status,
        semantic_authority: SemanticAuthority {
            engine: "Clean",
            lean4: false,
            lake: false,
            mathlib: false,
            external_olean: false,
        },
        source_scan: SourceScan {
            root: root.display().to_string(),
            file_count: sources.len(),
            extensions: SOURCE_EXTENSIONS,
            excluded_directories: EXCLUDED_DIRS,
        },
        summary,
        modules,
        diagnostics,
        authority_blockers,
    })
}

/// FAIL CLOSED on a vacuous run (K5).
///
/// A `pass` that examined no declaration is the exact green lie this command
/// used to tell: `declarations_checked: 0, declarations_failed: 0, status:
/// pass` over a package of 1,580 declarations, because every one of them sat
/// inside a `namespace` block the checker never opened. The leaf flattening in
/// [`check_project_module_with_env`] is the fix; this is the guard that makes
/// any future regression LOUD instead of green.
///
/// It fires whenever NOTHING was checked, not only when the parser found
/// declarations: a package of comment-only or administrative-only files
/// (`open`, `set_option`, `import`) used to pass with `0 declaration(s)
/// checked`, exit 0 (round-22 verification of `317f48b45`). A check that
/// examined nothing has no verdict to report, whatever the reason.
fn vacuous_run_blocker(
    declarations_parsed: usize,
    declarations_checked: usize,
) -> Option<AuthorityBlocker> {
    (declarations_checked == 0).then(|| {
        let message = if declarations_parsed > 0 {
            format!(
                "the parser found {declarations_parsed} declaration(s) but the checker examined \
                 none; a project check that checks nothing cannot report a pass"
            )
        } else {
            "the project holds no declaration to check (only comments, imports or \
             administrative commands); a project check that checks nothing cannot report a pass"
                .to_string()
        };
        AuthorityBlocker::project("nothing_checked", message)
    })
}

fn check_project_modules_in_order(
    sources: &[ProjectSource],
    parsed_modules: Vec<ParsedProjectModule>,
    load_order: Vec<usize>,
    allow_sorry: bool,
) -> BTreeMap<String, ProjectModuleReport> {
    reset_sorry_counter();
    reset_kernel_check_counter();

    // EACH MODULE IS CHECKED IN ITS OWN IMPORT CLOSURE (round-24 verification
    // of af6ae8e4a). This function used to build ONE environment and check
    // every module against it in load order, so a module saw every
    // declaration and instance loaded before it, not only what it imports:
    // with `A.lean: instance (priority := high) three : OfNat Nat 2 := ⟨3⟩`
    // and `B.lean: theorem t : (2 : Nat) = 3 := rfl` (B imports nothing),
    // `project check` credited B's `t` and exited 0, while `clean check
    // B.lean` and Lean 4.8.0 both reject it. The leak also ran the other way
    // (a sorry instance in A failed a valid B) and let B cite A's theorems
    // without importing A.
    //
    // Now a module's environment is the prelude plus exactly its transitive
    // project-local imports. It is seeded from the snapshot taken right after
    // one direct import's own check (that import's closure plus the import);
    // every other closure module is re-elaborated into it from source. A
    // re-elaborated module sits next to modules it does not import, so it can
    // itself see a leak (a sibling import's instance); its re-elaborated
    // declarations are therefore compared with the ones its OWN check
    // produced, and any difference fails the importer closed
    // (`import_environment_divergence`) — the importer is checked against the
    // declarations Lean would give it, or not credited.
    // The prelude plus the session support the elaborator installs before a
    // module's first declaration anyway, so that what a module's check ADDS is
    // its own declarations wherever it is elaborated (otherwise `PProd` is
    // added by whichever module is elaborated first in an environment).
    let mut prelude = Environment::with_prelude();
    clean_elab::prepare_session_environment(&mut prelude);
    let index_by_path = sources
        .iter()
        .enumerate()
        .map(|(idx, source)| (source.relative_path.clone(), idx))
        .collect::<BTreeMap<_, _>>();
    let deps = parsed_modules
        .iter()
        .map(|module| project_local_dependency_indices(module, &index_by_path))
        .collect::<Vec<_>>();
    // The same imports in the order each file names them.
    let ordered_deps = parsed_modules
        .iter()
        .map(|module| {
            module
                .local_import_order
                .iter()
                .filter_map(|path| index_by_path.get(path).copied())
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    // How many loaded modules still need a module's snapshot as a seed; the
    // snapshot is dropped when this reaches zero.
    let mut pending_importers = BTreeMap::<usize, usize>::new();
    for idx in &load_order {
        if parsed_modules[*idx].parsed {
            for dep in &deps[*idx] {
                *pending_importers.entry(*dep).or_default() += 1;
            }
        }
    }
    let mut reports = parsed_modules
        .iter()
        .map(|module| {
            (
                module.source_path.clone(),
                ProjectModuleReport::from_parsed(module, false),
            )
        })
        .collect::<BTreeMap<_, _>>();
    // Per loaded module: its transitive project-local import closure, the
    // environment right after its own check, and the declarations its own
    // check added.
    let mut closures = BTreeMap::<usize, BTreeSet<usize>>::new();
    let mut snapshots = BTreeMap::<usize, Environment>::new();
    let mut own_elaborations = BTreeMap::<usize, declarations::ModuleElaboration>::new();

    for idx in load_order.iter().copied() {
        let source = &sources[idx];
        let parsed = &parsed_modules[idx];
        if !parsed.parsed {
            continue;
        }
        // A module is checked only when EVERY project-local import it names
        // was loaded, i.e. checked in its own import closure with no
        // divergence. A dependency that was never loaded (parse failure,
        // cycle member, `import_environment_divergence`, or itself refused
        // here) has no environment that holds what Lean gives it, so there is
        // nothing faithful to check this module against. This used to drop
        // the unloaded dependency and check the module anyway; for a
        // divergence refusal it worse still seeded the importer from the
        // refused module's snapshot, which held the leaked re-elaboration:
        // with `X` importing `P` (`instance … : OfNat Nat 2 := ⟨3⟩`) and `Q`
        // (`def two : Nat := 2`), `M2: import X; theorem m : two = 3 := rfl`
        // was checked with `two := 3` and credited (1/1, in
        // `declarations_passed`) although Lean 4.8.0 rejects it (round-24
        // verification of 2bcef9307). Such a module is `import_failed`,
        // unchecked, and not loaded itself, so its importers are refused too.
        let unloaded_deps = deps[idx]
            .iter()
            .copied()
            .filter(|dep| !closures.contains_key(dep))
            .collect::<Vec<_>>();
        if !unloaded_deps.is_empty() {
            let mut module_report = ProjectModuleReport::from_parsed(parsed, false);
            for dep in &unloaded_deps {
                module_report
                    .diagnostics
                    .push(ProjectDiagnostic::module_error(
                        "import_not_loaded",
                        source,
                        format!(
                        "import `{}` was not loaded (it failed to parse, is in an import cycle, \
                         or was refused without being checked), so this module was not checked",
                        sources[*dep].module
                    ),
                    ));
            }
            for dep in &deps[idx] {
                if let Some(count) = pending_importers.get_mut(dep) {
                    *count = count.saturating_sub(1);
                    if *count == 0 {
                        snapshots.remove(dep);
                    }
                }
            }
            // Unloaded imports are `fail` or `import_failed` (never `pass` or
            // `nothing_checked`), so they are named here.
            let failed_imports = deps[idx]
                .iter()
                .filter_map(|dep| {
                    let dep_report = reports.get(&sources[*dep].relative_path)?;
                    (dep_report.status != MODULE_STATUS_PASS
                        && dep_report.status != MODULE_STATUS_NOTHING_CHECKED)
                        .then(|| sources[*dep].module.clone())
                })
                .collect::<Vec<_>>();
            module_report.status = if module_report.authority_blockers.is_empty() {
                MODULE_STATUS_IMPORT_FAILED
            } else {
                MODULE_STATUS_FAIL
            };
            module_report.failed_imports = failed_imports;
            reports.insert(source.relative_path.clone(), module_report);
            continue;
        }
        let loaded_deps = deps[idx].clone();
        let mut closure = BTreeSet::new();
        for dep in &loaded_deps {
            closure.insert(*dep);
            closure.extend(closures[dep].iter().copied());
        }
        // IMPORT ORDER (round-25 verification of 3ee5ff78e). Lean loads a
        // module's imports depth-first in the order the module names them,
        // and among instances of equal priority the one loaded LAST is tried
        // first. The closure used to be re-elaborated in the PROJECT's load
        // order, and the seed was the import with the largest closure, so
        // with `M: import Q; import P` (`Q: instance i2 : C := ⟨2⟩`,
        // `P: instance i3 : C := ⟨3⟩`) M saw i2 last, and `theorem m :
        // C.v = 2 := rfl` passed where Lean 4.8.0 (and `clean check`) take i3
        // and reject it. Now the seed is the FIRST import's snapshot — its
        // own closure in its own Lean order, then itself, which is exactly
        // the start of M's order — and the rest of the closure is replayed
        // in M's Lean order.
        let lean_order = lean_import_order(idx, &ordered_deps);
        debug_assert!(lean_order.iter().all(|dep| closure.contains(dep)));
        let seed = ordered_deps[idx].first().copied();
        let (mut env, mut present) = match seed {
            Some(seed) => {
                let mut present = closures[&seed].clone();
                present.insert(seed);
                (snapshots[&seed].clone(), present)
            }
            None => (prelude.clone(), BTreeSet::new()),
        };
        let mut divergences = Vec::new();
        for dep in lean_order.iter().copied() {
            if !closure.contains(&dep) || present.contains(&dep) {
                continue;
            }
            let before = env.clone();
            let outcomes = declarations::replay_project_module(
                &parsed_modules[dep],
                &sources[dep].identity,
                &mut env,
            );
            let replayed = declarations::ModuleElaboration {
                effect: env.effect_since(&before),
                outcomes,
            };
            if let Some(difference) = own_elaborations[&dep].disagreement(&replayed, &env) {
                divergences.push(format!("`{}`: {difference}", sources[dep].module));
            }
            present.insert(dep);
        }

        let before = env.clone();
        let mut outcomes = Vec::new();
        let mut module_report;
        let loaded = divergences.is_empty();
        if loaded {
            // The closure gate's base is the prelude — the same base `clean
            // check` snapshots before its first import. One gate per module,
            // since each module has its own environment.
            let mut gate = clean_olean::ImportedConeGate::new(&prelude);
            module_report = ProjectModuleReport::from_parsed(parsed, true);
            check_project_module_with_env(
                source,
                parsed,
                &mut env,
                &mut gate,
                allow_sorry,
                &mut module_report,
                &mut outcomes,
            );
        } else {
            // NOT CHECKED against an environment its imports do not define: a
            // declaration elaborated here could be credited with a meaning
            // Lean never gives it (`theorem m : two = 3 := rfl` passed when a
            // sibling import's instance turned the imported `two` into 3).
            module_report = ProjectModuleReport::from_parsed(parsed, false);
            for divergence in divergences {
                push_blocking_diagnostic(
                    "import_environment_divergence",
                    source,
                    format!(
                        "import {divergence}: it elaborates differently next to this module's \
                         other imports than in its own import closure, so this module was not \
                         checked against the declarations its imports define"
                    ),
                    &mut module_report.diagnostics,
                    &mut module_report.authority_blockers,
                );
            }
        }
        // A module refused for divergence was not checked, and `env` holds
        // the leaked re-elaboration of its imports: it is NOT loaded, so it
        // leaves no closure, no snapshot and no declarations to seed or be
        // replayed into an importer (which is then refused above).
        if loaded {
            own_elaborations.insert(
                idx,
                declarations::ModuleElaboration {
                    effect: env.effect_since(&before),
                    outcomes,
                },
            );
            closures.insert(idx, closure);
            if pending_importers.get(&idx).copied().unwrap_or(0) > 0 {
                snapshots.insert(idx, env);
            }
        }
        for dep in &deps[idx] {
            if let Some(count) = pending_importers.get_mut(dep) {
                *count = count.saturating_sub(1);
                if *count == 0 {
                    snapshots.remove(dep);
                }
            }
        }

        // Load order is topological, so every project-local dependency's
        // status is final here (a cycle member was never loaded and keeps its
        // `fail`).
        let failed_imports = deps[idx]
            .iter()
            .filter_map(|dep| {
                let dep_report = reports.get(&sources[*dep].relative_path)?;
                matches!(
                    dep_report.status,
                    MODULE_STATUS_FAIL | MODULE_STATUS_IMPORT_FAILED
                )
                .then(|| sources[*dep].module.clone())
            })
            .collect::<Vec<_>>();
        module_report.status = module_status(&module_report, &failed_imports);
        module_report.failed_imports = failed_imports;
        reports.insert(source.relative_path.clone(), module_report);
    }

    reset_sorry_counter();
    reset_kernel_check_counter();
    reports
}

/// Module status values. `pass` is the only one that credits the module.
const MODULE_STATUS_PASS: &str = "pass";
/// The module itself holds an authority blocker.
const MODULE_STATUS_FAIL: &str = "fail";
/// The module's own declarations raised no blocker, but a project-local
/// module it imports (directly, or through a module in this state) is `fail`.
/// `clean check` on this file refuses it for the same reason, so it is not a
/// pass.
const MODULE_STATUS_IMPORT_FAILED: &str = "import_failed";
/// The module raised no blocker and checked NO declaration (an aggregator of
/// imports, or a file of comments / administrative commands). Nothing was
/// verified in it, so it is not a pass either.
const MODULE_STATUS_NOTHING_CHECKED: &str = "nothing_checked";
/// Parsed but never loaded (only reachable for a module the checker skipped).
const MODULE_STATUS_NOT_CHECKED: &str = "not_checked";

/// A module's status once it has been checked.
///
/// Before this, the status was `pass` whenever the module carried no blocker
/// of its own: TSL's aggregator `TrustIr` (45 imports, 0 declarations) was
/// `pass` with `checked_count: 0`, and modules whose imports failed were
/// `pass` although `clean check` refused them — 11 modules `pass` where
/// `clean check` passed 6 (round-24 verification of 29de4ae8b).
fn module_status(report: &ProjectModuleReport, failed_imports: &[String]) -> &'static str {
    if !report.authority_blockers.is_empty() {
        MODULE_STATUS_FAIL
    } else if !failed_imports.is_empty() {
        MODULE_STATUS_IMPORT_FAILED
    } else if report.checked_count == 0 {
        MODULE_STATUS_NOTHING_CHECKED
    } else {
        MODULE_STATUS_PASS
    }
}

fn push_blocking_diagnostic(
    kind: &'static str,
    source: &ProjectSource,
    message: String,
    diagnostics: &mut Vec<ProjectDiagnostic>,
    authority_blockers: &mut Vec<AuthorityBlocker>,
) {
    let blocker = AuthorityBlocker::module(kind, &source.module, &source.relative_path, message);
    diagnostics.push(ProjectDiagnostic::from_blocker(&blocker));
    authority_blockers.push(blocker);
}

fn summarize_project(
    modules: &[ProjectModuleReport],
    diagnostics: usize,
    authority_blockers: usize,
) -> ProjectSummary {
    ProjectSummary {
        modules_found: modules.len(),
        modules_parsed: modules.iter().filter(|module| module.parsed).count(),
        modules_checked: modules.iter().filter(|module| module.checked).count(),
        modules_passed: count_status(modules, MODULE_STATUS_PASS),
        modules_failed: count_status(modules, MODULE_STATUS_FAIL),
        modules_import_failed: count_status(modules, MODULE_STATUS_IMPORT_FAILED),
        modules_nothing_checked: count_status(modules, MODULE_STATUS_NOTHING_CHECKED),
        modules_not_checked: count_status(modules, MODULE_STATUS_NOT_CHECKED),
        declarations_parsed: modules.iter().map(|module| module.decl_count).sum(),
        declarations_checked: modules.iter().map(|module| module.checked_count).sum(),
        declarations_passed: modules
            .iter()
            .filter(|module| module.failed_imports.is_empty())
            .map(|module| module.success_count)
            .sum(),
        declarations_passed_on_assumptions: modules
            .iter()
            .filter(|module| module.failed_imports.is_empty())
            .map(|module| module.assumptions.len())
            .sum(),
        declarations_not_credited: modules
            .iter()
            .filter(|module| !module.failed_imports.is_empty())
            .map(|module| module.success_count)
            .sum(),
        declarations_failed: modules.iter().map(|module| module.failed_count).sum(),
        imports: modules.iter().map(|module| module.imports.len()).sum(),
        diagnostics,
        authority_blockers,
    }
}

fn count_status(modules: &[ProjectModuleReport], status: &str) -> usize {
    modules
        .iter()
        .filter(|module| module.status == status)
        .count()
}

fn render_project_check_human(out: &mut impl Write, report: &ProjectCheckReport) -> io::Result<()> {
    writeln!(
        out,
        "Project check {}: {} module(s), {} declaration(s) checked, {} passed, {} failed{}",
        report.status,
        report.summary.modules_found,
        report.summary.declarations_checked,
        report.summary.declarations_passed,
        report.summary.declarations_failed,
        if report.summary.declarations_not_credited > 0 {
            format!(
                ", {} not credited (a project-local import failed)",
                report.summary.declarations_not_credited
            )
        } else {
            String::new()
        }
    )?;
    writeln!(
        out,
        "  modules: {} pass, {} fail, {} import_failed, {} nothing_checked, {} not_checked",
        report.summary.modules_passed,
        report.summary.modules_failed,
        report.summary.modules_import_failed,
        report.summary.modules_nothing_checked,
        report.summary.modules_not_checked
    )?;
    writeln!(
        out,
        "  authority blockers: {}, diagnostics: {}",
        report.summary.authority_blockers, report.summary.diagnostics
    )?;
    for blocker in &report.authority_blockers {
        let location = blocker
            .source_path
            .as_deref()
            .unwrap_or(report.project.as_str());
        writeln!(
            out,
            "  - [{}] {}: {}",
            blocker.kind, location, blocker.message
        )?;
    }
    if report.summary.declarations_passed_on_assumptions > 0 {
        writeln!(
            out,
            "  {} of the passed declaration(s) rest on non-foundational axiom(s) \
             (assumed, not proved):",
            report.summary.declarations_passed_on_assumptions
        )?;
        let rows = report
            .modules
            .iter()
            .flat_map(|module| module.assumptions.iter().map(move |row| (module, row)));
        for (module, row) in rows.clone().take(ASSUMPTION_ROWS_SHOWN) {
            writeln!(out, "  - [assumption] {}: {row}", module.source_path)?;
        }
        let hidden = rows.count().saturating_sub(ASSUMPTION_ROWS_SHOWN);
        if hidden > 0 {
            writeln!(out, "  … and {hidden} more (every row is in --json)")?;
        }
    }
    Ok(())
}

/// Assumption rows printed in the human report; `--json` carries all of them.
const ASSUMPTION_ROWS_SHOWN: usize = 20;

#[derive(Debug, Serialize)]
struct ProjectCheckReport {
    schema_version: &'static str,
    command: &'static str,
    project: String,
    status: &'static str,
    semantic_authority: SemanticAuthority,
    source_scan: SourceScan,
    summary: ProjectSummary,
    modules: Vec<ProjectModuleReport>,
    diagnostics: Vec<ProjectDiagnostic>,
    authority_blockers: Vec<AuthorityBlocker>,
}

#[derive(Debug, Serialize)]
struct SemanticAuthority {
    engine: &'static str,
    lean4: bool,
    lake: bool,
    mathlib: bool,
    external_olean: bool,
}

#[derive(Debug, Serialize)]
struct SourceScan {
    root: String,
    file_count: usize,
    extensions: &'static [&'static str],
    excluded_directories: &'static [&'static str],
}

#[derive(Debug, Serialize)]
struct ProjectSummary {
    modules_found: usize,
    modules_parsed: usize,
    modules_checked: usize,
    /// Modules by status; the five partition `modules_found`.
    modules_passed: usize,
    modules_failed: usize,
    modules_import_failed: usize,
    modules_nothing_checked: usize,
    modules_not_checked: usize,
    /// Declaration-shaped SURFACE forms the parser produced, counting the
    /// members of a `namespace` / `section` / `mutual` block rather than the
    /// block. Administrative forms (`import`, `open`, `variable`, `#command`)
    /// declare nothing and are not counted.
    declarations_parsed: usize,
    /// Declaration units the checker actually examined: `declarations_passed +
    /// declarations_failed + declarations_not_credited`.
    ///
    /// This is NOT bounded by `declarations_parsed` in either direction, and
    /// the two must not be read as a ratio — they count different populations.
    /// Measured on trust-ir's Lean semantics (2026-09-17): 1,492 parsed against
    /// 1,580 checked, because a `#guard_msgs in #print axioms c` site declares
    /// nothing on the surface yet elaborates to anonymous checked units, while
    /// two modules go the other way (a surface form that elaborates to no
    /// declaration unit at all). The one relation that IS load-bearing is the
    /// vacuity gate: `declarations_checked == 0` means nothing was checked,
    /// and blocks.
    declarations_checked: usize,
    /// Declarations that passed in a module none of whose project-local
    /// imports failed. Not the sum of the modules' `success_count`: see
    /// `declarations_not_credited`.
    declarations_passed: usize,
    /// Of `declarations_passed`, those whose verdict rests on a domain axiom
    /// (each listed in its module's `assumptions`).
    declarations_passed_on_assumptions: usize,
    declarations_failed: usize,
    /// Declarations that checked in a module with a FAILED project-local
    /// import (`failed_imports` non-empty, so status `import_failed` or
    /// `fail`). They were checked against an import Clean itself refuses, so
    /// they are credited neither as passed nor as failed; `clean check` of
    /// such a module exits non-zero. Round-24 verification of ff6c33c2c
    /// measured `import_failed(1/1)` modules adding their `1` to
    /// `declarations_passed`.
    declarations_not_credited: usize,
    imports: usize,
    diagnostics: usize,
    authority_blockers: usize,
}

#[derive(Debug, Serialize)]
struct ProjectModuleReport {
    module: String,
    source_path: String,
    extension: String,
    status: &'static str,
    parsed: bool,
    checked: bool,
    decl_count: usize,
    /// Leaf declarations examined in this module (`success_count + failed_count`).
    checked_count: usize,
    success_count: usize,
    failed_count: usize,
    imports: Vec<ProjectImport>,
    diagnostics: Vec<ProjectDiagnostic>,
    trust_summary: CheckTrustSummary,
    authority_blockers: Vec<AuthorityBlocker>,
    /// One row per PASSED declaration whose verdict rests on a domain axiom
    /// (neither foundational nor a trust marker): `name: rests on axiom(s)
    /// …`. A pass listed here is assumption-bearing, not unconditional.
    assumptions: Vec<String>,
    /// Project-local imports whose status is `fail` or `import_failed`;
    /// non-empty only when this module's status is `import_failed` or `fail`
    /// (always, for `import_failed`).
    failed_imports: Vec<String>,
}

impl ProjectModuleReport {
    fn from_parsed(parsed: &ParsedProjectModule, checked: bool) -> Self {
        Self {
            module: parsed.module.clone(),
            source_path: parsed.source_path.clone(),
            extension: parsed.extension.clone(),
            // Never `pass` before the module is checked: the caller sets the
            // final status from the check (see [`module_status`]).
            status: if parsed.authority_blockers.is_empty() {
                MODULE_STATUS_NOT_CHECKED
            } else {
                MODULE_STATUS_FAIL
            },
            parsed: parsed.parsed,
            checked,
            decl_count: parsed.decl_count,
            checked_count: 0,
            success_count: 0,
            failed_count: 0,
            imports: parsed.imports.clone(),
            diagnostics: parsed.diagnostics.clone(),
            trust_summary: CheckTrustSummary::default(),
            authority_blockers: parsed.authority_blockers.clone(),
            assumptions: Vec::new(),
            failed_imports: Vec::new(),
        }
    }
}

#[derive(Debug, Clone, Serialize)]
struct ProjectImport {
    module: String,
    #[serde(skip)]
    identity: Name,
    project_local: bool,
    source_path: Option<String>,
}

#[derive(Debug, Clone, Serialize)]
struct ProjectDiagnostic {
    severity: &'static str,
    kind: String,
    module: Option<String>,
    source_path: Option<String>,
    message: String,
}

impl ProjectDiagnostic {
    /// An error about one module that is not itself an authority blocker (the
    /// module's status already refuses it for another module's blocker).
    fn module_error(kind: &str, source: &ProjectSource, message: String) -> Self {
        Self {
            severity: "error",
            kind: kind.to_string(),
            module: Some(source.module.clone()),
            source_path: Some(source.relative_path.clone()),
            message,
        }
    }

    fn from_blocker(blocker: &AuthorityBlocker) -> Self {
        Self {
            severity: "error",
            kind: blocker.kind.clone(),
            module: blocker.module.clone(),
            source_path: blocker.source_path.clone(),
            message: blocker.message.clone(),
        }
    }
}

#[derive(Debug, Clone, Serialize)]
struct AuthorityBlocker {
    kind: String,
    module: Option<String>,
    source_path: Option<String>,
    message: String,
}

impl AuthorityBlocker {
    fn project(kind: impl Into<String>, message: impl Into<String>) -> Self {
        Self {
            kind: kind.into(),
            module: None,
            source_path: None,
            message: message.into(),
        }
    }

    fn module(
        kind: impl Into<String>,
        module: &str,
        source_path: &str,
        message: impl Into<String>,
    ) -> Self {
        Self {
            kind: kind.into(),
            module: Some(module.to_owned()),
            source_path: Some(source_path.to_owned()),
            message: message.into(),
        }
    }
}

#[derive(Debug, Clone, Default, Serialize)]
struct CheckTrustSummary {
    /// Checked declarations whose constant closure reaches `sorryAx` / `sorry`.
    sorry_axioms: u64,
    /// Sorry terms the elaborator created (this field's meaning before the
    /// closure census; ADDITIVE).
    sorry_terms_minted: u64,
    kernel_check_failures: u64,
}

pub(crate) const FEATURES: &[FeatureDescriptor] = &[FeatureDescriptor {
    path: &["project", "check"],
    summary: "Check a Clean-native project without Lean/Lake authority",
    description: "\
Scans a project directory for `.clean` and `.lean` source files, skips build \
artifacts such as `.lake/` and `target/`, runs Clean's parser, elaborator, and \
kernel validation in Clean-native import mode, and emits deterministic project \
evidence. Each module is checked in an environment holding the prelude and \
exactly its transitive project-local imports, as Lean builds it; an imported \
module that elaborates differently there than in its own import closure fails \
the importer (`import_environment_divergence`) and its declarations are not \
checked. A module whose project-local import was not loaded (unparsed, in a \
cycle, or refused unchecked) is `import_failed` and not checked either \
(`import_not_loaded`), so nothing is credited against an environment its \
imports do not define. A declaration is credited only when its cited closure re-admits over \
the prelude and reaches no trust marker (a `sorry` only under `--allow-sorry`), the rule \
`clean check` applies. A module is `pass` only when it checked at least one declaration and \
no project-local import failed; otherwise it is `fail`, `import_failed` or \
`nothing_checked`. The report aggregates parsed modules, checked declarations, imports, \
diagnostics, and authority blockers. External imports are reported as \
blockers instead of being discharged by Lean 4, Lake, Mathlib, or `.olean` \
artifacts.",
    category: Category::Verification,
    stability: Stability::Building,
    examples: &[Example {
        cmd: "clean project check . --json",
        what: "emit machine-readable project check evidence for the current project",
    }],
    see_also: &["check"],
    references: &[DESIGN_REF, CLI_CRATE_REF],
    domain_root: Some("project"),
    alternative_forms: &[],
    feature_gate: None,
}];
