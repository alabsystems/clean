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
use clean_elab::{
    elaborate_decl_and_register_with_context_and_warning, kernel_check_failure_count,
    preprocess_decl_with_context, ElabResult, FileContext, RegistrationWarning,
    RegistrationWarningKind,
};
use clean_features::{Category, Example, FeatureDescriptor, RefKind, Reference, Stability};
use clean_kernel::sorry::{reset_sorry_counter, sorry_count};
use clean_kernel::{Environment, TypeChecker};
use clean_parser::{parse_file_with_tactics, SurfaceDecl};
use clean_server::handlers::validate_decl_read_only;
use serde::Serialize;
use walkdir::WalkDir;

const PROJECT_CHECK_SCHEMA_VERSION: &str = "Clean-project-check-report-v1";
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
    /// Permit declarations that use `sorry` to count as checked.
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
        .map(|source| (source.module.clone(), source.relative_path.clone()))
        .collect::<BTreeMap<_, _>>();

    let mut modules = check_project_modules(&sources, &module_sources, args.allow_sorry);
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

fn scan_project_sources(root: &Path) -> anyhow::Result<Vec<ProjectSource>> {
    let mut sources = Vec::new();
    let walker = WalkDir::new(root)
        .sort_by_file_name()
        .into_iter()
        .filter_entry(|entry| should_descend(entry.path(), root));

    for entry in walker {
        let entry = entry?;
        if !entry.file_type().is_file() || !is_source_file(entry.path()) {
            continue;
        }
        let path = entry.path().to_path_buf();
        let relative = path
            .strip_prefix(root)
            .map(Path::to_path_buf)
            .unwrap_or_else(|_| path.clone());
        let relative_path = slash_path(&relative);
        let module = module_name_for_relative_path(&relative);
        let extension = path
            .extension()
            .and_then(|ext| ext.to_str())
            .unwrap_or_default()
            .to_owned();
        sources.push(ProjectSource {
            path,
            relative_path,
            module,
            extension,
        });
    }

    sources.sort_by(|left, right| left.relative_path.cmp(&right.relative_path));
    Ok(sources)
}

fn should_descend(path: &Path, root: &Path) -> bool {
    if path == root || !path.is_dir() {
        return true;
    }
    path.file_name()
        .and_then(|name| name.to_str())
        .is_none_or(|name| !EXCLUDED_DIRS.contains(&name))
}

fn is_source_file(path: &Path) -> bool {
    if path.file_name().and_then(|name| name.to_str()) == Some("lakefile.lean") {
        return false;
    }
    path.extension()
        .and_then(|ext| ext.to_str())
        .is_some_and(|ext| SOURCE_EXTENSIONS.contains(&ext))
}

fn check_project_modules(
    sources: &[ProjectSource],
    module_sources: &BTreeMap<String, String>,
    allow_sorry: bool,
) -> Vec<ProjectModuleReport> {
    let mut parsed_modules = sources
        .iter()
        .map(|source| parse_project_module(source, module_sources))
        .collect::<Vec<_>>();

    let cycle_modules = project_module_cycles(sources, &parsed_modules);
    for idx in &cycle_modules {
        let source = &sources[*idx];
        let blocker = AuthorityBlocker::module(
            "project_import_cycle",
            &source.module,
            &source.relative_path,
            "project-local imports form a cycle; Clean project check cannot topologically load these modules as authority",
        );
        parsed_modules[*idx]
            .diagnostics
            .push(ProjectDiagnostic::from_blocker(&blocker));
        parsed_modules[*idx].authority_blockers.push(blocker);
    }

    let load_order = topological_project_module_order(sources, &parsed_modules, &cycle_modules);
    let mut checked_reports =
        check_project_modules_in_order(sources, parsed_modules, load_order, allow_sorry);
    sources
        .iter()
        .map(|source| {
            checked_reports
                .remove(&source.relative_path)
                .expect("every source should produce a module report")
        })
        .collect()
}

fn parse_project_module(
    source: &ProjectSource,
    module_sources: &BTreeMap<String, String>,
) -> ParsedProjectModule {
    let mut diagnostics = Vec::new();
    let mut authority_blockers = Vec::new();
    let mut parsed = false;
    let mut decl_count = 0;
    let mut decls = Vec::new();
    let imports = match parse_project_imports(source, module_sources) {
        Ok(scan) => {
            parsed = true;
            decl_count = scan.decl_count;
            decls = scan.decls;
            for import in &scan.imports {
                if !import.project_local {
                    let blocker = AuthorityBlocker::module(
                        "external_import",
                        &source.module,
                        &source.relative_path,
                        format!(
                            "import `{}` is not project-local; Clean project check did not use external Lean/Lake artifacts as authority",
                            import.module
                        ),
                    );
                    diagnostics.push(ProjectDiagnostic::from_blocker(&blocker));
                    authority_blockers.push(blocker);
                }
            }
            scan.imports
        }
        Err(message) => {
            let blocker = AuthorityBlocker::module(
                "parse_error",
                &source.module,
                &source.relative_path,
                message,
            );
            diagnostics.push(ProjectDiagnostic::from_blocker(&blocker));
            authority_blockers.push(blocker);
            Vec::new()
        }
    };

    ParsedProjectModule {
        module: source.module.clone(),
        source_path: source.relative_path.clone(),
        extension: source.extension.clone(),
        parsed,
        decl_count,
        decls,
        imports,
        diagnostics,
        authority_blockers,
    }
}

fn project_module_cycles(
    sources: &[ProjectSource],
    parsed_modules: &[ParsedProjectModule],
) -> BTreeSet<usize> {
    let index_by_path = sources
        .iter()
        .enumerate()
        .map(|(idx, source)| (source.relative_path.clone(), idx))
        .collect::<BTreeMap<_, _>>();
    let deps = parsed_modules
        .iter()
        .map(|module| project_local_dependency_indices(module, &index_by_path))
        .collect::<Vec<_>>();
    let mut state = vec![0_u8; sources.len()];
    let mut stack = Vec::new();
    let mut cycle_modules = BTreeSet::new();
    for idx in 0..sources.len() {
        detect_project_module_cycles(idx, &deps, &mut state, &mut stack, &mut cycle_modules);
    }
    cycle_modules
}

fn detect_project_module_cycles(
    idx: usize,
    deps: &[Vec<usize>],
    state: &mut [u8],
    stack: &mut Vec<usize>,
    cycle_modules: &mut BTreeSet<usize>,
) {
    match state[idx] {
        1 => {
            if let Some(pos) = stack.iter().position(|stack_idx| *stack_idx == idx) {
                cycle_modules.extend(stack[pos..].iter().copied());
            }
            return;
        }
        2 => return,
        _ => {}
    }
    state[idx] = 1;
    stack.push(idx);
    for dep in &deps[idx] {
        detect_project_module_cycles(*dep, deps, state, stack, cycle_modules);
    }
    stack.pop();
    state[idx] = 2;
}

fn topological_project_module_order(
    sources: &[ProjectSource],
    parsed_modules: &[ParsedProjectModule],
    cycle_modules: &BTreeSet<usize>,
) -> Vec<usize> {
    let index_by_path = sources
        .iter()
        .enumerate()
        .map(|(idx, source)| (source.relative_path.clone(), idx))
        .collect::<BTreeMap<_, _>>();
    let deps = parsed_modules
        .iter()
        .map(|module| project_local_dependency_indices(module, &index_by_path))
        .collect::<Vec<_>>();
    let mut visited = BTreeSet::new();
    let mut order = Vec::new();
    for idx in 0..sources.len() {
        push_topological_project_module(idx, &deps, cycle_modules, &mut visited, &mut order);
    }
    order
}

fn push_topological_project_module(
    idx: usize,
    deps: &[Vec<usize>],
    cycle_modules: &BTreeSet<usize>,
    visited: &mut BTreeSet<usize>,
    order: &mut Vec<usize>,
) {
    if cycle_modules.contains(&idx) || !visited.insert(idx) {
        return;
    }
    for dep in &deps[idx] {
        push_topological_project_module(*dep, deps, cycle_modules, visited, order);
    }
    order.push(idx);
}

fn project_local_dependency_indices(
    module: &ParsedProjectModule,
    index_by_path: &BTreeMap<String, usize>,
) -> Vec<usize> {
    module
        .imports
        .iter()
        .filter_map(|import| {
            if !import.project_local {
                return None;
            }
            import
                .source_path
                .as_ref()
                .and_then(|path| index_by_path.get(path))
                .copied()
        })
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn check_project_modules_in_order(
    sources: &[ProjectSource],
    parsed_modules: Vec<ParsedProjectModule>,
    load_order: Vec<usize>,
    allow_sorry: bool,
) -> BTreeMap<String, ProjectModuleReport> {
    reset_sorry_counter();
    reset_kernel_check_counter();

    let mut env = Environment::with_prelude();
    let mut reports = parsed_modules
        .iter()
        .map(|module| {
            (
                module.source_path.clone(),
                ProjectModuleReport::from_parsed(module, false),
            )
        })
        .collect::<BTreeMap<_, _>>();

    for idx in load_order {
        let source = &sources[idx];
        let parsed = &parsed_modules[idx];
        if !parsed.parsed {
            continue;
        }
        let mut module_report = ProjectModuleReport::from_parsed(parsed, true);
        check_project_module_with_env(source, parsed, &mut env, allow_sorry, &mut module_report);
        module_report.status = if module_report.authority_blockers.is_empty() {
            "pass"
        } else {
            "fail"
        };
        reports.insert(source.relative_path.clone(), module_report);
    }

    reset_sorry_counter();
    reset_kernel_check_counter();
    reports
}

fn check_project_module_with_env(
    source: &ProjectSource,
    parsed: &ParsedProjectModule,
    env: &mut Environment,
    allow_sorry: bool,
    report: &mut ProjectModuleReport,
) {
    let sorry_before = sorry_count();
    let kernel_before = kernel_check_failure_count();
    let mut file_ctx = FileContext::new();
    file_ctx.disable_external_import_search();

    for decl in &parsed.decls {
        // Skip `import` decls here: topological loading already pre-loaded
        // project-local dependencies into `env`, and external imports were
        // already flagged as authority blockers in the parse phase.
        if matches!(decl, SurfaceDecl::Import { .. }) {
            continue;
        }
        let kernel_failures_before = kernel_check_failure_count();
        let processed_decl = preprocess_decl_with_context(decl, &mut file_ctx);
        match elaborate_decl_and_register_with_context_and_warning(
            env,
            &processed_decl,
            &mut file_ctx,
        ) {
            Ok(registered) => {
                let name = elab_result_name(&registered.result);
                match typecheck_elab_result(&registered.result, env) {
                    Ok(_) => {
                        let kernel_delta =
                            kernel_check_failure_count().saturating_sub(kernel_failures_before);
                        record_project_decl(
                            source,
                            &name,
                            registered.warning.as_ref(),
                            kernel_delta,
                            allow_sorry,
                            report,
                        );
                    }
                    Err(message) => push_project_failure(
                        "checker_error",
                        source,
                        format!("{name}: {message}"),
                        report,
                    ),
                }
            }
            Err(e) => push_project_failure(
                "checker_error",
                source,
                format!("elaboration error: {e:?}"),
                report,
            ),
        }
    }

    report.trust_summary = CheckTrustSummary {
        sorry_axioms: sorry_count().saturating_sub(sorry_before),
        kernel_check_failures: kernel_check_failure_count().saturating_sub(kernel_before),
    };
}

fn record_project_decl(
    source: &ProjectSource,
    name: &str,
    warning: Option<&RegistrationWarning>,
    kernel_failures_delta: u64,
    allow_sorry: bool,
    report: &mut ProjectModuleReport,
) {
    if name == "(skipped)" {
        return;
    }
    if let Some(warning) = warning {
        let is_sorry = matches!(
            warning.kind,
            RegistrationWarningKind::ExplicitSorry | RegistrationWarningKind::SyntheticSorry
        );
        if allow_sorry && is_sorry {
            report.success_count += 1;
            return;
        }
        push_project_failure(
            "trust_failure",
            source,
            format!(
                "{}: declaration uses {}",
                warning.decl_name,
                registration_warning_label(&warning.kind)
            ),
            report,
        );
        return;
    }
    if kernel_failures_delta > 0 {
        push_project_failure(
            "kernel_check_failure",
            source,
            format!("{name}: kernel check failures: {kernel_failures_delta}"),
            report,
        );
        return;
    }
    report.success_count += 1;
}

fn push_project_failure(
    kind: &'static str,
    source: &ProjectSource,
    message: String,
    report: &mut ProjectModuleReport,
) {
    report.failed_count += 1;
    push_blocking_diagnostic(
        kind,
        source,
        message,
        &mut report.diagnostics,
        &mut report.authority_blockers,
    );
}

fn parse_project_imports(
    source: &ProjectSource,
    module_sources: &BTreeMap<String, String>,
) -> Result<ImportScan, String> {
    let text = fs::read_to_string(&source.path)
        .map_err(|err| format!("failed to read {}: {err}", source.relative_path))?;
    let patterns = clean_elab::tactic::builtins::builtin_tactic_patterns();
    let decls = parse_file_with_tactics(&text, &patterns)
        .map_err(|err| format!("parse error in {}: {err}", source.relative_path))?;
    let mut imports = Vec::new();
    collect_imports(&decls, module_sources, &mut imports);
    imports.sort_by(|left, right| left.module.cmp(&right.module));
    imports.dedup_by(|left, right| left.module == right.module);
    Ok(ImportScan {
        decl_count: decls.len(),
        imports,
        decls,
    })
}

fn collect_imports(
    decls: &[SurfaceDecl],
    module_sources: &BTreeMap<String, String>,
    imports: &mut Vec<ProjectImport>,
) {
    for decl in decls {
        match decl {
            SurfaceDecl::Import { paths, .. } => {
                for path in paths {
                    let module = path.join(".");
                    let source_path = module_sources.get(&module).cloned();
                    imports.push(ProjectImport {
                        module,
                        project_local: source_path.is_some(),
                        source_path,
                    });
                }
            }
            SurfaceDecl::Namespace { decls, .. }
            | SurfaceDecl::Section { decls, .. }
            | SurfaceDecl::Mutual { decls, .. } => collect_imports(decls, module_sources, imports),
            SurfaceDecl::Open {
                body: Some(body), ..
            }
            | SurfaceDecl::SetOption {
                body: Some(body), ..
            } => collect_imports(std::slice::from_ref(body.as_ref()), module_sources, imports),
            _ => {}
        }
    }
}

fn registration_warning_label(kind: &RegistrationWarningKind) -> &'static str {
    match kind {
        RegistrationWarningKind::ExplicitSorry => "explicit sorry",
        RegistrationWarningKind::SyntheticSorry => "synthetic sorry",
        RegistrationWarningKind::TrustedArith => "trustedArith",
        RegistrationWarningKind::TrustedAy => "trustedAy",
    }
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
        ElabResult::MutualInductive { decl, .. } => decl
            .types
            .first()
            .map_or_else(|| "(mutual inductive)".to_string(), |t| t.name.to_string()),
        ElabResult::Failed { name, .. } => name.clone(),
        // Anonymous, checked-then-discarded (B02) — still one checked unit.
        ElabResult::Example { .. } => "example".to_string(),
        ElabResult::Command(_) | ElabResult::Multiple(_) | ElabResult::Skipped => {
            "(skipped)".to_string()
        }
    }
}

fn typecheck_elab_result(result: &ElabResult, env: &Environment) -> Result<String, String> {
    // Never report a `Failed` inner decl as a (false) pass.
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
        declarations_parsed: modules.iter().map(|module| module.decl_count).sum(),
        declarations_checked: modules.iter().map(|module| module.success_count).sum(),
        declarations_failed: modules.iter().map(|module| module.failed_count).sum(),
        imports: modules.iter().map(|module| module.imports.len()).sum(),
        diagnostics,
        authority_blockers,
    }
}

fn render_project_check_human(out: &mut impl Write, report: &ProjectCheckReport) -> io::Result<()> {
    writeln!(
        out,
        "Project check {}: {} module(s), {} checked declaration(s), {} failed declaration(s)",
        report.status,
        report.summary.modules_found,
        report.summary.declarations_checked,
        report.summary.declarations_failed
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
    Ok(())
}

fn module_name_for_relative_path(path: &Path) -> String {
    let mut without_ext = path.to_path_buf();
    without_ext.set_extension("");
    without_ext
        .components()
        .filter_map(|component| component.as_os_str().to_str())
        .collect::<Vec<_>>()
        .join(".")
}

fn slash_path(path: &Path) -> String {
    path.components()
        .filter_map(|component| component.as_os_str().to_str())
        .collect::<Vec<_>>()
        .join("/")
}

#[derive(Debug, Clone)]
struct ProjectSource {
    path: PathBuf,
    relative_path: String,
    module: String,
    extension: String,
}

struct ImportScan {
    decl_count: usize,
    imports: Vec<ProjectImport>,
    decls: Vec<SurfaceDecl>,
}

#[derive(Debug, Clone)]
struct ParsedProjectModule {
    module: String,
    source_path: String,
    extension: String,
    parsed: bool,
    decl_count: usize,
    decls: Vec<SurfaceDecl>,
    imports: Vec<ProjectImport>,
    diagnostics: Vec<ProjectDiagnostic>,
    authority_blockers: Vec<AuthorityBlocker>,
}

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
    declarations_parsed: usize,
    declarations_checked: usize,
    declarations_failed: usize,
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
    success_count: usize,
    failed_count: usize,
    imports: Vec<ProjectImport>,
    diagnostics: Vec<ProjectDiagnostic>,
    trust_summary: CheckTrustSummary,
    authority_blockers: Vec<AuthorityBlocker>,
}

impl ProjectModuleReport {
    fn from_parsed(parsed: &ParsedProjectModule, checked: bool) -> Self {
        Self {
            module: parsed.module.clone(),
            source_path: parsed.source_path.clone(),
            extension: parsed.extension.clone(),
            status: if parsed.authority_blockers.is_empty() {
                "pass"
            } else {
                "fail"
            },
            parsed: parsed.parsed,
            checked,
            decl_count: parsed.decl_count,
            success_count: 0,
            failed_count: 0,
            imports: parsed.imports.clone(),
            diagnostics: parsed.diagnostics.clone(),
            trust_summary: CheckTrustSummary {
                sorry_axioms: 0,
                kernel_check_failures: 0,
            },
            authority_blockers: parsed.authority_blockers.clone(),
        }
    }
}

#[derive(Debug, Clone, Serialize)]
struct ProjectImport {
    module: String,
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

#[derive(Debug, Clone, Serialize)]
struct CheckTrustSummary {
    sorry_axioms: u64,
    kernel_check_failures: u64,
}

pub(crate) const FEATURES: &[FeatureDescriptor] = &[FeatureDescriptor {
    path: &["project", "check"],
    summary: "Check a Clean-native project without Lean/Lake authority",
    description: "\
Scans a project directory for `.clean` and `.lean` source files, skips build \
artifacts such as `.lake/` and `target/`, runs Clean's parser, elaborator, and \
kernel validation in Clean-native import mode, and emits deterministic project \
evidence. The report aggregates parsed modules, checked declarations, imports, \
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
