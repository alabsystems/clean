// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0
//! In-memory adapter of the existing ordered source/import-closure walk.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::path::PathBuf;
use std::sync::Arc;
use std::time::{Duration, Instant};

use clean_kernel::{Environment, Name};
use clean_parser::notation_seed::NotationSeed;
use clean_parser::{FileHeader, SurfaceDecl};

use super::{ElabOutcome, ImportGraph, ModuleElaboration};
use crate::module_batch::CheckedJudgment;
use crate::module_driver::{
    elaborate_decls, BudgetReading, DriverOptions, EnvironmentSetup, LeafOutcome, ModuleObserver,
    ModuleReport, SourceModuleSetup,
};
use crate::{ElabError, ElabResult, FileContext, RegisteredElabResult};

const MAX_IMPORT_DEPTH: usize = 256;

/// Exact producer input. The diagnostic path is never opened by this adapter.
#[derive(Clone, Debug)]
pub struct CapturedSourceModule {
    pub name: Name,
    pub path: PathBuf,
    pub source: Arc<str>,
}

/// A frontend's resolution of one authored import. Artifact imports use only
/// the selected world's existing loader, never a source filesystem search.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SourceImport {
    Captured(Name),
    Artifact,
}

/// Frontend resolution policy over actual captured modules. Returning Artifact
/// grants no acceptance: the ordinary pinned-world importer must still load it.
pub trait SourceImportResolver {
    fn resolve(
        &mut self,
        from: &CapturedSourceModule,
        imported: &Name,
    ) -> Result<SourceImport, SourceGraphError>;
}

impl<F> SourceImportResolver for F
where
    F: FnMut(&CapturedSourceModule, &Name) -> Result<SourceImport, SourceGraphError>,
{
    fn resolve(
        &mut self,
        from: &CapturedSourceModule,
        imported: &Name,
    ) -> Result<SourceImport, SourceGraphError> {
        self(from, imported)
    }
}

/// A source frontend refusal, not a proof-kernel verdict.
#[derive(Debug, thiserror::Error)]
pub enum SourceGraphError {
    #[error("captured source graph: {0}")]
    Input(String),
    #[error("source module {module} ({path}): {reason}")]
    Module {
        module: Name,
        path: PathBuf,
        reason: String,
    },
    #[error("source import {imported} from {module}: {reason}")]
    Import {
        module: Name,
        imported: Name,
        reason: String,
    },
}

/// All snapshots of one invocation, indexed without reopening diagnostic paths.
#[derive(Clone)]
pub struct CapturedSourceGraph {
    modules: BTreeMap<Name, CapturedSourceModule>,
    headers: BTreeMap<Name, FileHeader>,
}

/// One authored callback event. Block events retain their original outer
/// span and their actual canonical leaf names; no inner span is invented.
#[derive(Debug)]
pub struct SourceDeclarationOutput {
    pub span: clean_parser::Span,
    pub primary_name: Option<Name>,
    pub registered_names: Vec<Name>,
    pub anonymous_judgments: usize,
    pub refused: bool,
}

/// Actual body data retained for the caller's existing policy and strict replay.
#[derive(Debug)]
pub struct SourceModuleOutput {
    pub report: ModuleReport,
    pub introduced: BTreeSet<Name>,
    pub checked_judgments: Vec<CheckedJudgment>,
    pub declarations: Vec<SourceDeclarationOutput>,
    /// Source dependencies plus the ordinary artifact header processing time.
    pub import_time: Duration,
}

/// Ordinary frontend output, with no proof/authority token or source-to-code claim.
pub struct SourceGraphOutput {
    pub environment: Environment,
    pub modules: BTreeMap<Name, SourceModuleOutput>,
    pub inputs: Vec<CapturedSourceModule>,
    /// Initial environment construction; an explicit prelude may load Init
    /// only later through its actual imports, included in module import_time.
    pub initial_environment_time: Duration,
}

#[derive(Clone)]
struct ResolvedImport {
    imported: Name,
    resolution: SourceImport,
}

type ImportPlan = BTreeMap<Name, Vec<ResolvedImport>>;

impl CapturedSourceGraph {
    pub fn new(modules: Vec<CapturedSourceModule>) -> Result<Self, SourceGraphError> {
        if modules.is_empty() {
            return Err(SourceGraphError::Input("empty module inventory".into()));
        }
        let mut captured = BTreeMap::new();
        let mut paths = HashMap::new();
        let mut headers = BTreeMap::new();
        for module in modules {
            if module.name.is_anon() || module.path.as_os_str().is_empty() {
                return Err(SourceGraphError::Input("empty module name or path".into()));
            }
            if captured.contains_key(&module.name) {
                return Err(SourceGraphError::Input(format!(
                    "duplicate module name {}",
                    module.name
                )));
            }
            if let Some(previous) = paths.insert(module.path.clone(), module.name.clone()) {
                return Err(SourceGraphError::Input(format!(
                    "one captured path names both {previous} and {}",
                    module.name
                )));
            }
            let header = clean_parser::Parser::parse_header(&module.source)
                .map_err(|error| module_error(&module, error.to_string()))?;
            headers.insert(module.name.clone(), header);
            captured.insert(module.name.clone(), module);
        }
        Ok(Self {
            modules: captured,
            headers,
        })
    }

    /// Check every captured module, in the roots' authored order and the imports'
    /// declared order. The roots must reach the entire captured inventory.
    /// Decisions are frozen before elaboration and reused by isolated walks.
    pub fn elaborate(
        &self,
        roots: &[Name],
        environment_setup: EnvironmentSetup,
        decision: &clean_olean::SourceWorldDecision,
        resolver: &mut impl SourceImportResolver,
    ) -> Result<SourceGraphOutput, SourceGraphError> {
        let imports = decision
            .imports()
            .map_err(|error| SourceGraphError::Input(error.to_string()))?;
        let library_paths = selected_library_paths(imports)?;
        for module in self.modules.values() {
            match clean_olean::resolve_typed_module_path(&module.name, &library_paths) {
                Ok(_) => {
                    return Err(module_error(
                        module,
                        "captured module collides with an artifact in the selected world".into(),
                    ))
                }
                Err(clean_olean::ImportError::ModuleNotFound { .. }) => {}
                Err(error) => return Err(module_error(module, error.to_string())),
            }
        }
        // The caller supplies no opaque for_file/bootstrap snapshot. Every
        // header in this graph derives from this exact admitted world.
        let mut setup = SourceModuleSetup::new(environment_setup, decision)
            .map_err(|error| SourceGraphError::Input(error.to_string()))?
            .with_captured_artifact_paths(library_paths.clone());
        let first = roots
            .first()
            .ok_or_else(|| SourceGraphError::Input("empty root list".into()))?;
        let first_module = self.module(first)?;
        let plan = self.resolve(resolver)?;
        let started = Instant::now();
        let environment = setup
            .initial_environment(&self.headers[first])
            .map_err(|error| module_error(first_module, error.to_string()))?;
        let initial_environment_time = started.elapsed();
        let mut walk = Walk {
            captured: self,
            plan: &plan,
            decision,
            setup,
            graph: ImportGraph::default(),
            outputs: BTreeMap::new(),
            faithful_judgments: HashMap::new(),
            library_paths,
        };
        let mut environment = environment;
        for root in roots {
            walk.check(root, &mut environment)?;
        }
        if walk.outputs.len() != self.modules.len() {
            let omitted = self
                .modules
                .keys()
                .filter(|name| !walk.outputs.contains_key(*name))
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(", ");
            return Err(SourceGraphError::Input(format!(
                "mounted modules omitted from roots: {omitted}"
            )));
        }
        Ok(SourceGraphOutput {
            environment,
            modules: walk.outputs,
            inputs: self.modules.values().cloned().collect(),
            initial_environment_time,
        })
    }

    fn module(&self, name: &Name) -> Result<&CapturedSourceModule, SourceGraphError> {
        self.modules
            .get(name)
            .ok_or_else(|| SourceGraphError::Input(format!("unmounted module {name}")))
    }

    fn resolve(
        &self,
        resolver: &mut impl SourceImportResolver,
    ) -> Result<ImportPlan, SourceGraphError> {
        let mut plan = BTreeMap::new();
        for (name, module) in &self.modules {
            let mut imports = Vec::new();
            for import in &self.headers[name].imports {
                let imported = import.module.name();
                let resolution = resolver.resolve(module, imported)?;
                if let SourceImport::Captured(target) = &resolution {
                    if target != imported || !self.modules.contains_key(target) {
                        return Err(SourceGraphError::Import {
                            module: name.clone(),
                            imported: imported.clone(),
                            reason: "resolution must name that exact captured module".into(),
                        });
                    }
                } else if self.modules.contains_key(imported) {
                    return Err(SourceGraphError::Import {
                        module: name.clone(),
                        imported: imported.clone(),
                        reason: "an artifact must not replace a captured source module".into(),
                    });
                }
                imports.push(ResolvedImport {
                    imported: imported.clone(),
                    resolution,
                });
            }
            plan.insert(name.clone(), imports);
        }
        Ok(plan)
    }
}

struct Walk<'a> {
    captured: &'a CapturedSourceGraph,
    plan: &'a ImportPlan,
    decision: &'a clean_olean::SourceWorldDecision,
    setup: SourceModuleSetup,
    graph: ImportGraph,
    outputs: BTreeMap<Name, SourceModuleOutput>,
    faithful_judgments: HashMap<PathBuf, Vec<CheckedJudgment>>,
    library_paths: Vec<PathBuf>,
}

impl Walk<'_> {
    fn check(&mut self, name: &Name, env: &mut Environment) -> Result<(), SourceGraphError> {
        let module = self.captured.module(name)?;
        let Some(completed_at_start) = self
            .graph
            .enter(&module.path, MAX_IMPORT_DEPTH)
            .map_err(|reason| module_error(module, reason))?
        else {
            return Ok(());
        };
        let body = self.body(name, env);
        let imports = self.graph.leave(&module.path);
        let (own, output) = body?;
        let strangers = self
            .graph
            .record_imports(&module.path, imports, &completed_at_start);
        // Every imported source gets its own header environment. Even the first
        // dependency may otherwise inherit an ordinary parent's implicit Init.
        if strangers || !self.graph.in_flight.is_empty() {
            let (expected, judgments) = self.faithful(name)?;
            if !same_judgments(&judgments, &output.checked_judgments) {
                return Err(module_error(module, "import_environment_divergence: original anonymous judgments differ from the module's own import closure".into()));
            }
            if let Some(reason) = expected.disagreement(&own, env) {
                return Err(module_error(
                    module,
                    format!("import_environment_divergence: {reason}"),
                ));
            }
        }
        let _ = self
            .graph
            .retain_faithful(&module.path, Some(own), env, strangers, true);
        self.graph.completed.insert(module.path.clone());
        self.faithful_judgments
            .insert(module.path.clone(), output.checked_judgments.clone());
        self.outputs.insert(name.clone(), output);
        Ok(())
    }

    fn faithful(
        &mut self,
        name: &Name,
    ) -> Result<(ModuleElaboration, Vec<CheckedJudgment>), SourceGraphError> {
        let module = self.captured.module(name)?;
        if let (Some(Some(kept)), Some(judgments)) = (
            self.graph.faithful.get(&module.path),
            self.faithful_judgments.get(&module.path),
        ) {
            return Ok((kept.1.clone(), judgments.clone()));
        }
        let mut setup = self.setup.isolated();
        let mut env = setup
            .initial_environment(&self.captured.headers[name])
            .map_err(|error| module_error(module, error.to_string()))?;
        let mut isolated = Walk {
            captured: self.captured,
            plan: self.plan,
            decision: self.decision,
            setup,
            graph: ImportGraph::default(),
            outputs: BTreeMap::new(),
            faithful_judgments: HashMap::new(),
            library_paths: self.library_paths.clone(),
        };
        // This is the root of its own closure. Its imported bodies are checked
        // in turn by the same walker; no success is assumed from earlier output.
        let before = isolated
            .graph
            .enter(&module.path, MAX_IMPORT_DEPTH)
            .map_err(|reason| module_error(module, reason))?
            .ok_or_else(|| module_error(module, "isolated root unexpectedly completed".into()))?;
        let body = isolated.body(name, &mut env);
        let imports = isolated.graph.leave(&module.path);
        let (own, output) = body?;
        isolated
            .graph
            .record_imports(&module.path, imports, &before);
        self.graph.faithful.extend(isolated.graph.faithful);
        self.faithful_judgments.extend(isolated.faithful_judgments);
        // Bounded retention stays in ImportGraph; return the actual record even
        // when that cache is full, as the original frontend's isolated root did.
        let _ = self
            .graph
            .retain_faithful(&module.path, Some(own.clone()), &env, false, true);
        self.faithful_judgments
            .insert(module.path.clone(), output.checked_judgments.clone());
        Ok((own, output.checked_judgments))
    }

    fn body(
        &mut self,
        name: &Name,
        env: &mut Environment,
    ) -> Result<(ModuleElaboration, SourceModuleOutput), SourceGraphError> {
        let module = self.captured.module(name)?;
        let header = &self.captured.headers[name];
        let seed = self.notation_seed(name)?;
        let patterns = crate::tactic::builtins::builtin_tactic_patterns();
        let parsed = clean_parser::parse_file_seeded_in_world(
            &module.source,
            &patterns,
            &seed,
            self.decision.world(),
        )
        .map_err(|error| module_error(module, error.to_string()))?;
        if !parsed.diagnostics.is_empty() {
            return Err(module_error(
                module,
                format!("parser recovery: {:?}", parsed.diagnostics),
            ));
        }
        let mut context = captured_file_context(self.decision)?;
        context.set_main_module(name.clone());
        context.set_file_header(&parsed.header);
        let decls = self
            .setup
            .prepare(
                env,
                header,
                &parsed.decls,
                &mut context,
                self.graph.completed.is_empty(),
            )
            .map_err(|error| module_error(module, error.to_string()))?;
        // Only original leading header imports receive a frozen resolution.
        // A command import elsewhere must not escape the frontend resolver.
        let authored: Vec<Name> = collect_imports(decls);
        let planned: Vec<Name> = self.plan[name]
            .iter()
            .map(|entry| entry.imported.clone())
            .collect();
        if authored != planned
            || !decls
                .iter()
                .take(planned.len())
                .all(|decl| matches!(decl, SurfaceDecl::Import { .. }))
        {
            return Err(module_error(
                module,
                "import outside the original module header".into(),
            ));
        }
        let mut observer = BodyObserver::new();
        if let Some(SurfaceDecl::Prelude { span }) = parsed.decls.first() {
            // prepare has already checked this original header in its fresh
            // environment. Retain its actual administrative event for census.
            observer.declarations.push(SourceDeclarationOutput {
                span: *span,
                primary_name: None,
                registered_names: Vec::new(),
                anonymous_judgments: 0,
                refused: false,
            });
        }
        let mut report = ModuleReport::default();
        let started = Instant::now();
        // Do not commute artifacts past source modules: equal-priority
        // instances and attribute effects observe authored import order.
        for (decl, import) in decls.iter().zip(&self.plan[name]) {
            if let SourceImport::Captured(target) = &import.resolution {
                self.check(target, env)?;
                context.mark_import_satisfied_from_source(&import.imported);
            } else {
                // Artifact means actual selected-library DATA. Refuse its real
                // loader error before the ordinary command's provider fallback.
                clean_olean::load_typed_module_with_deps_bounded_shared(
                    env,
                    &import.imported,
                    &self.library_paths,
                    crate::imports::FRONTEND_OLEAN_IMPORT_MODULE_LIMIT,
                    context.import_visited_mut(),
                )
                .map_err(|error| SourceGraphError::Import {
                    module: name.clone(),
                    imported: import.imported.clone(),
                    reason: error.to_string(),
                })?;
            }
            let mut header_report = elaborate_decls(
                env,
                std::slice::from_ref(decl),
                &module.source,
                &mut context,
                DriverOptions {
                    lean_front_door: true,
                    ..DriverOptions::default()
                },
                &mut observer,
            );
            check_body_report(module, &observer, &header_report)?;
            report.peak_decl_ticks = report.peak_decl_ticks.max(header_report.peak_decl_ticks);
            report.verdicts.append(&mut header_report.verdicts);
        }
        let import_time = started.elapsed();
        // This is the exact source-body boundary, including an empty body.
        // Header effects and all dependency checks have completed.
        let baseline = env.clone();
        let mut body_report = elaborate_decls(
            env,
            &decls[planned.len()..],
            &module.source,
            &mut context,
            DriverOptions {
                lean_front_door: true,
                ..DriverOptions::default()
            },
            &mut observer,
        );
        check_body_report(module, &observer, &body_report)?;
        report.peak_decl_ticks = report.peak_decl_ticks.max(body_report.peak_decl_ticks);
        report.verdicts.append(&mut body_report.verdicts);
        let effect = env.effect_since(&baseline);
        let introduced = effect.changed_constant_names().cloned().collect();
        Ok((
            ModuleElaboration {
                effect,
                outcomes: observer.outcomes,
            },
            SourceModuleOutput {
                report,
                introduced,
                checked_judgments: observer.judgments,
                declarations: observer.declarations,
                import_time,
            },
        ))
    }

    fn notation_seed(&self, name: &Name) -> Result<NotationSeed, SourceGraphError> {
        let mut seed = NotationSeed::new();
        let mut visited = HashSet::new();
        let mut active = HashSet::new();
        self.harvest(name, &mut visited, &mut active, &mut seed, false)?;
        Ok(seed)
    }

    fn harvest(
        &self,
        name: &Name,
        visited: &mut HashSet<Name>,
        active: &mut HashSet<Name>,
        seed: &mut NotationSeed,
        include_self: bool,
    ) -> Result<(), SourceGraphError> {
        let module = self.captured.module(name)?;
        if visited.contains(name) {
            return Ok(());
        }
        if active.len() >= MAX_IMPORT_DEPTH || !active.insert(name.clone()) {
            return Err(module_error(
                module,
                "source import cycle or depth limit while seeding notation".into(),
            ));
        }
        for import in &self.plan[name] {
            if let SourceImport::Captured(target) = &import.resolution {
                self.harvest(target, visited, active, seed, true)?;
            }
        }
        active.remove(name);
        visited.insert(name.clone());
        if include_self {
            seed.harvest_module_source(&module.source);
        }
        Ok(())
    }
}

/// A lexical/import context for the same captured world. This configures no
/// environment and grants no acceptance. Callers checking future goals may
/// disable external imports and mark only their already checked source keys.
pub fn captured_file_context(
    decision: &clean_olean::SourceWorldDecision,
) -> Result<FileContext, SourceGraphError> {
    let imports = decision
        .imports()
        .map_err(|error| SourceGraphError::Input(error.to_string()))?;
    let mut context = FileContext::new();
    context.set_captured_source_world(decision, selected_library_paths(imports)?);
    Ok(context)
}

fn selected_library_paths(
    imports: &clean_olean::ImportWorld,
) -> Result<Vec<PathBuf>, SourceGraphError> {
    let library = match imports {
        clean_olean::ImportWorld::Project { lib, .. }
        | clean_olean::ImportWorld::Explicit { lib, .. } => lib.clone(),
        clean_olean::ImportWorld::CheckoutPin => {
            clean_olean::require_pinned_lean_lib_path().map_err(SourceGraphError::Input)?
        }
        _ => {
            return Err(SourceGraphError::Input(
                "unsupported captured-source artifact world".into(),
            ))
        }
    };
    Ok(vec![library])
}

fn same_judgments(left: &[CheckedJudgment], right: &[CheckedJudgment]) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .zip(right)
            .all(|(a, b)| a.type_ == b.type_ && a.value == b.value)
}

fn check_body_report(
    module: &CapturedSourceModule,
    observer: &BodyObserver,
    report: &ModuleReport,
) -> Result<(), SourceGraphError> {
    if let Some(reason) = &observer.refusal {
        return Err(module_error(module, reason.clone()));
    }
    if let Some(failure) = report
        .verdicts
        .iter()
        .find(|verdict| verdict.kind.is_failure())
    {
        return Err(module_error(
            module,
            format!(
                "{}: {:?}: {}",
                failure.name,
                failure.kind,
                failure
                    .detail
                    .as_deref()
                    .unwrap_or("source declaration refused")
            ),
        ));
    }
    Ok(())
}

fn module_error(module: &CapturedSourceModule, reason: String) -> SourceGraphError {
    SourceGraphError::Module {
        module: module.name.clone(),
        path: module.path.clone(),
        reason,
    }
}

fn collect_imports(decls: &[SurfaceDecl]) -> Vec<Name> {
    let mut names = Vec::new();
    for decl in decls {
        match decl {
            SurfaceDecl::Import { paths, .. } => {
                names.extend(paths.iter().map(|name| name.name().clone()))
            }
            SurfaceDecl::Namespace { decls, .. }
            | SurfaceDecl::Section { decls, .. }
            | SurfaceDecl::Mutual { decls, .. } => names.extend(collect_imports(decls)),
            SurfaceDecl::SetOption {
                body: Some(body), ..
            }
            | SurfaceDecl::Open {
                body: Some(body), ..
            } => names.extend(collect_imports(std::slice::from_ref(body.as_ref()))),
            _ => {}
        }
    }
    names
}

struct BodyObserver {
    outcomes: Vec<ElabOutcome>,
    judgments: Vec<CheckedJudgment>,
    declarations: Vec<SourceDeclarationOutput>,
    refusal: Option<String>,
}

impl BodyObserver {
    fn new() -> Self {
        Self {
            outcomes: Vec::new(),
            judgments: Vec::new(),
            declarations: Vec::new(),
            refusal: None,
        }
    }
}

impl ModuleObserver for BodyObserver {
    fn decl_registered(&mut self, decl: &SurfaceDecl, registered: &RegisteredElabResult) {
        self.outcomes.push(ElabOutcome::of_registered(registered));
        let mut leaves = Vec::new();
        registered.result.leaf_decls(&mut leaves);
        self.declarations.push(SourceDeclarationOutput {
            span: decl.span(),
            primary_name: registered.result.declaration_name().cloned(),
            registered_names: leaves
                .iter()
                .filter_map(|leaf| leaf.declaration_name().cloned())
                .collect(),
            anonymous_judgments: leaves
                .iter()
                .filter(|leaf| matches!(leaf, ElabResult::Example { .. }))
                .count(),
            refused: false,
        });
        self.judgments
            .extend(leaves.into_iter().filter_map(|leaf| match leaf {
                ElabResult::Example { ty, val } => Some(CheckedJudgment {
                    type_: ty.clone(),
                    value: val.clone(),
                }),
                _ => None,
            }));
    }

    fn decl_failed(&mut self, _env: &Environment, decl: &SurfaceDecl, error: &ElabError) {
        self.outcomes.push(ElabOutcome::Refused);
        self.declarations.push(SourceDeclarationOutput {
            span: decl.span(),
            primary_name: None,
            registered_names: Vec::new(),
            anonymous_judgments: 0,
            refused: true,
        });
        if matches!(decl, SurfaceDecl::Import { .. }) {
            self.refusal = Some(format!(
                "import failed; source body was not checked: {error}"
            ));
        }
    }

    fn leaf_checked(&mut self, _env: &Environment, _decl: &SurfaceDecl, leaf: &LeafOutcome<'_>) {
        match leaf {
            LeafOutcome::Failed { error, .. } => self.refusal = Some(error.to_string()),
            LeafOutcome::ValidationFailed { message, .. } => self.refusal = Some(message.clone()),
            LeafOutcome::Checked {
                source_diagnostics, ..
            } if !source_diagnostics.is_empty() => {
                self.refusal = Some(format!("source diagnostics: {source_diagnostics:?}"))
            }
            _ => {}
        }
    }

    fn after_decl(&mut self, _context: &FileContext, _decl: &SurfaceDecl, budget: &BudgetReading) {
        if budget.exhausted {
            self.refusal = Some("declaration budget exhausted; no source verdict".into());
        }
    }

    fn stop_requested(&self) -> bool {
        self.refusal.is_some()
    }
}
