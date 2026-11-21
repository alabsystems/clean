// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0
//! Fresh source headers and a matching prelude for artifact import graphs.
//!
//! A header may be validated against a fresh module only when its caller also
//! compares every imported source body's outcomes/effect with an elaboration
//! in exactly its own closure. This type supplies setup, never that evidence.

use std::collections::HashSet;
use std::path::{Path, PathBuf};

use clean_kernel::{Environment, Name};
use clean_parser::{FileHeader, SurfaceDecl};

use super::{EnvironmentSetup, ModuleSetupError};
use crate::{ElabError, FileContext};

#[cfg(test)]
mod clean_format_tests;

/// Failure preparing a source module without silently borrowing a prelude.
#[derive(Debug, thiserror::Error)]
pub enum SourceModuleError {
    /// Reading or parsing an actual source header failed.
    #[error("cannot read source module header in {path}: {reason}")]
    Header { path: PathBuf, reason: String },
    /// Format classification uses the same strict multi-part artifact reader
    /// as importing; a failed read must never select bootstrap semantics.
    #[error("cannot classify source import artifact {path}: {reason}")]
    Artifact { path: PathBuf, reason: String },
    /// The selected world's fresh setup could not be constructed.
    #[error(transparent)]
    Setup(#[from] ModuleSetupError),
    /// The original strict prelude elaborator refused the header.
    #[error(transparent)]
    Elaboration(#[from] ElabError),
    /// Implicit Init must be the selected world's actual artifact closure.
    #[error("cannot load implicit Init for an ordinary source module: {0}")]
    ImplicitInit(String),
    /// First-wins importing must not silently keep a source lookalike.
    #[error("ordinary source module's implicit Init conflicts with existing declaration `{0}`")]
    ConflictingInit(Name),
}

/// Keep source traversal iterative while distinguishing an active canonical
/// path from completed aliases in their lexical resolution contexts.
enum SourceVisit {
    Enter(PathBuf),
    Leave {
        canonical: PathBuf,
        parent: Option<PathBuf>,
    },
}

/// Whether a source graph needs isolated module setup. A prelude needs a bare
/// backbone. Artifact imports need a matching prelude: mixing genuine Init
/// with bootstrap references can change definitional equality or lose bodies.
/// Errors never choose the legacy setup as a fallback.
///
/// One import selects no world: a module Clean's hand-written prelude serves
/// by name ([`crate::prelude_providers::has_declared_prelude`]) for which no
/// artifact exists in `decision`'s search paths (the frontend importer's, in
/// its order). The importer serves such a module from that prelude, whose
/// stand-ins are built over the bootstrap prelude (`init_real_numbers`
/// declares `HAdd`, which genuine Init already holds), so it is no artifact
/// import and genuine Init has nothing to match. An artifact present for the
/// same module, or a closure that also reaches a real artifact import, still
/// selects world setup, where the stand-in is refused by name.
pub fn source_closure_needs_world_setup(
    path: &Path,
    decision: &clean_olean::SourceWorldDecision,
) -> Result<bool, SourceModuleError> {
    let mut pending = vec![SourceVisit::Enter(path.to_path_buf())];
    let mut completed = HashSet::new();
    let mut active = HashSet::new();
    while let Some(visit) = pending.pop() {
        let path = match visit {
            SourceVisit::Enter(path) => path,
            SourceVisit::Leave { canonical, parent } => {
                active.remove(&canonical);
                completed.insert((canonical, parent));
                continue;
            }
        };
        let canonical =
            std::fs::canonicalize(&path).map_err(|error| SourceModuleError::Header {
                path: path.clone(),
                reason: error.to_string(),
            })?;
        // Check the active path first: a backedge is a cycle even when an
        // earlier alias completed under this lexical parent.
        if active.contains(&canonical) {
            return Err(SourceModuleError::Header {
                path: path.clone(),
                reason: "source import cycle detected".into(),
            });
        }
        let parent = path.parent().map(Path::to_path_buf);
        if completed.contains(&(canonical.clone(), parent.clone())) {
            continue;
        }
        active.insert(canonical.clone());
        pending.push(SourceVisit::Leave { canonical, parent });
        let source = std::fs::read_to_string(&path).map_err(|error| SourceModuleError::Header {
            path: path.clone(),
            reason: error.to_string(),
        })?;
        let header = clean_parser::Parser::parse_header_in_world(&source, decision.world())
            .map_err(|error| SourceModuleError::Header {
                path: path.clone(),
                reason: error.to_string(),
            })?;
        if header.is_prelude {
            return Ok(true);
        }
        for import in header.imports {
            let module = import.module.name();
            if let Some(source) = crate::resolve_intra_project_import(module, &path) {
                pending.push(SourceVisit::Enter(source));
            } else if !served_by_declared_prelude(module, &path, decision) {
                // The world-aware artifact importer still resolves and checks
                // this import; a missing artifact is never a bootstrap fallback.
                return Ok(true);
            }
        }
    }
    Ok(false)
}

/// Whether the importer serves `module`, imported from `source_path`, from a
/// hand-written prelude Clean declares for it by name: no artifact for it
/// exists where the importer searches. A refused artifact world answers
/// `false` and keeps its existing setup (R111).
fn served_by_declared_prelude(
    module: &Name,
    source_path: &Path,
    decision: &clean_olean::SourceWorldDecision,
) -> bool {
    let Some(label) = crate::imports::canonical_prelude_label(module) else {
        return false;
    };
    if !crate::prelude_providers::has_declared_prelude(&label) {
        return false;
    }
    let Ok(imports) = decision.imports() else {
        return false;
    };
    matches!(
        clean_olean::resolve_typed_module_path_in_world(
            module,
            &artifact_search_paths(source_path, imports),
            decision.declared_world(),
        ),
        Err(clean_olean::ImportError::ModuleNotFound { .. })
    )
}

/// The frontend importer's artifact search paths for `source_path`, in its
/// order: the file's Lake paths, then the selected world's library.
fn artifact_search_paths(source_path: &Path, imports: &clean_olean::ImportWorld) -> Vec<PathBuf> {
    let mut search_paths = crate::lake_import_search_paths_for_file(source_path);
    for default in clean_olean::search_paths_in_world(imports) {
        if !search_paths.contains(&default) {
            search_paths.push(default);
        }
    }
    search_paths
}

/// The checker retains its explicit prelude policy; native programs match
/// Clean Lake's producer rather than inheriting checker-only extensions.
#[derive(Clone, Copy)]
enum BootstrapContext {
    Checker,
    Program,
}

/// Per-invocation setup for modules whose bodies are independently compared.
/// No declarations or environment extensions are copied between modules here.
#[derive(Clone)]
pub struct SourceModuleSetup {
    bare: Environment,
    init: Option<Environment>,
    init_completed_imports: Option<clean_olean::CompletedModuleImports>,
    init_present: bool,
    artifact_imports_permitted: bool,
    bootstrap_snapshot: bool,
    search_paths: Vec<PathBuf>,
}

impl SourceModuleSetup {
    /// Retain source isolation while matching the prelude of a complete
    /// Clean-format artifact closure. Since 2026-11-15 Clean's Lake producer
    /// elaborates every module without `prelude` over genuine Init and
    /// records `Init` as its first import, so such an artifact's closure
    /// reaches a genuine artifact and never takes this route. (A `prelude`
    /// module stays refused by Clean Lake, so it writes no artifact.) The
    /// route remains for closures that still rest on the built-in prelude:
    /// artifacts a Clean build wrote before that change, and those Clean
    /// Lake writes in a project whose Lean world is refused (R111), which
    /// keeps the bootstrap prelude and records no `Init`. Importing their
    /// payload over genuine Init can lose checked seed definitions (for
    /// example a body referenced by a stored instance).
    /// Only the oracle world's existing bootstrap semantics are eligible.
    /// Recent selected worlds retain their genuine-Init contract.
    pub fn for_file(
        setup: EnvironmentSetup,
        decision: &clean_olean::SourceWorldDecision,
        path: &Path,
    ) -> Result<Self, SourceModuleError> {
        Self::for_file_with_import_policy(setup, decision, path, crate::ImportPolicy::FailClosed)
    }

    /// Match an explicit checker import policy without relaxing artifact reads.
    /// Permissive source imports may be absent, but existing artifact parts and
    /// the dependencies they record must still classify successfully.
    pub fn for_file_with_import_policy(
        setup: EnvironmentSetup,
        decision: &clean_olean::SourceWorldDecision,
        path: &Path,
        import_policy: crate::ImportPolicy,
    ) -> Result<Self, SourceModuleError> {
        Self::for_file_in_context(
            setup,
            decision,
            path,
            BootstrapContext::Checker,
            import_policy,
        )
    }

    /// Match Clean Lake/native program bootstrap without checker-only List
    /// monad instances or ULift. Artifact, world and source-isolation guards
    /// are identical to the checker constructor.
    pub fn for_program_file(
        decision: &clean_olean::SourceWorldDecision,
        path: &Path,
    ) -> Result<Self, SourceModuleError> {
        Self::for_file_in_context(
            EnvironmentSetup::default(),
            decision,
            path,
            BootstrapContext::Program,
            crate::ImportPolicy::FailClosed,
        )
    }

    fn for_file_in_context(
        setup: EnvironmentSetup,
        decision: &clean_olean::SourceWorldDecision,
        path: &Path,
        context: BootstrapContext,
        import_policy: crate::ImportPolicy,
    ) -> Result<Self, SourceModuleError> {
        let mut fresh = Self::new(setup, decision)?;
        if !setup.prelude.is_pinned_init()
            && decision.world() == clean_kernel::lean_world::LeanWorld::ORACLE
            && decision.imports().is_ok()
            && match import_policy {
                crate::ImportPolicy::FailClosed => clean_format_source_closure(path, decision)?,
                crate::ImportPolicy::Permissive => {
                    clean_format_source_closure_with_import_policy(path, decision, import_policy)?
                }
            }
        {
            let mut bootstrap = match context {
                BootstrapContext::Checker => {
                    super::module_environment_for_header_in_world(
                        setup,
                        decision,
                        &FileHeader::default(),
                    )?
                    .0
                }
                BootstrapContext::Program => {
                    // This is the producer's existing program environment:
                    // with_prelude + IO operations, then session support below.
                    let mut program = Environment::with_prelude();
                    program
                        .init_io_ops()
                        .map_err(|error| ModuleSetupError::IoOperations(error.to_string()))?;
                    if let Some(world) = decision.declared_world() {
                        clean_olean::declare_environment_world(&mut program, world).map_err(
                            |error| ModuleSetupError::LeanWorld {
                                world: decision.world(),
                                reason: error.to_string(),
                            },
                        )?;
                    }
                    program
                }
            };
            clean_kernel::tc::with_declaration_budget_suspended(|| {
                crate::prepare_session_environment(&mut bootstrap);
            });
            // Enforce the chosen format on actual subsequently consumed parts.
            // Classification and loading need not read the same filesystem state.
            clean_olean::require_clean_payload_imports(&mut bootstrap);
            fresh.init = Some(bootstrap);
            fresh.bootstrap_snapshot = true;
        }
        Ok(fresh)
    }

    /// Construct the empty backbone in the entry file's selected Lean world.
    pub fn new(
        setup: EnvironmentSetup,
        decision: &clean_olean::SourceWorldDecision,
    ) -> Result<Self, SourceModuleError> {
        let mut header = FileHeader::default();
        header.is_prelude = true;
        let (bare, _) = super::module_environment_for_header_in_world(setup, decision, &header)?;
        let (init, search_paths) = match decision.imports() {
            Ok(imports) => (None, clean_olean::search_paths_in_world(imports)),
            Err(_) => {
                // R111 permits Oracle source/bootstrap semantics when the
                // project's artifact imports are refused. Keep that refusal
                // in every file context; never search another world's library.
                let (mut bootstrap, _) = super::module_environment_for_header_in_world(
                    setup,
                    decision,
                    &FileHeader::default(),
                )?;
                // Fixed session support belongs to the bootstrap environment,
                // not to the first imported source body's measured effect.
                // No artifact import is permitted here, so this cannot pre-empt
                // a genuine imported instance with a bootstrap bridge.
                clean_kernel::tc::with_declaration_budget_suspended(|| {
                    crate::prepare_session_environment(&mut bootstrap);
                });
                (Some(bootstrap), Vec::new())
            }
        };
        Ok(Self {
            bare,
            init,
            init_completed_imports: None,
            init_present: false,
            artifact_imports_permitted: decision.imports().is_ok(),
            bootstrap_snapshot: false,
            search_paths,
        })
    }

    /// A captured invocation selects its artifact roots explicitly. This is
    /// applied only to a freshly constructed setup, before any Init snapshot.
    pub(super) fn with_captured_artifact_paths(mut self, paths: Vec<PathBuf>) -> Self {
        self.search_paths = paths;
        self
    }

    /// Header used only to construct the root environment and citation base.
    /// Keep the actual header/declarations unchanged for import resolution.
    /// Denied artifact worlds must not load foundations just because a source
    /// import appears in this temporary header (R111).
    pub fn root_environment_header(&self, header: &FileHeader) -> FileHeader {
        let mut setup = header.clone();
        setup.is_prelude = self.artifact_imports_permitted || header.is_prelude;
        if !self.artifact_imports_permitted {
            setup.imports.clear();
        }
        setup
    }

    /// Start an independent elaboration. It must not inherit its caller's Init.
    pub fn environment(&self) -> Environment {
        self.bare.clone()
    }

    /// A new walk retains only the immutable Init artifact snapshot, never
    /// the parent's claim that its current working environment contains it.
    pub fn isolated(&self) -> Self {
        let mut fresh = self.clone();
        fresh.init_present = false;
        fresh
    }

    /// Create the actual root environment before source declarations/options.
    pub fn initial_environment(
        &mut self,
        header: &FileHeader,
    ) -> Result<Environment, SourceModuleError> {
        if header.is_prelude {
            self.init_present = false;
            return Ok(self.environment());
        }
        clean_kernel::tc::with_declaration_budget_suspended(|| self.ensure_init_snapshot())?;
        let env = self
            .init
            .as_ref()
            .ok_or_else(|| SourceModuleError::ImplicitInit("fresh Init was not retained".into()))?
            .clone();
        self.init_present = true;
        Ok(env)
    }

    /// Produce the same initial environment with its actual completed artifact
    /// import bookkeeping. No search or admission is enabled by this DATA.
    /// Bootstrap and explicit-prelude contexts receive no artifact completion.
    /// The caller still checks every original source body and dependency cone.
    pub fn initial_environment_and_file_context(
        &mut self,
        header: &FileHeader,
    ) -> Result<(Environment, FileContext), SourceModuleError> {
        let environment = self.initial_environment(header)?;
        let mut context = FileContext::new();
        if self.init_present && self.artifact_imports_permitted && !self.bootstrap_snapshot {
            if let Some(completed) = &self.init_completed_imports {
                context.set_preloaded_artifact_imports(completed.clone());
            }
        }
        Ok((environment, context))
    }

    /// Prepare one header before imports. The caller MUST independently
    /// validate each imported source body's complete outcome and effect.
    pub fn prepare<'a>(
        &mut self,
        env: &mut Environment,
        header: &FileHeader,
        decls: &'a [SurfaceDecl],
        context: &mut FileContext,
        pristine_backbone: bool,
    ) -> Result<&'a [SurfaceDecl], SourceModuleError> {
        if header.is_prelude {
            // Keep the strict empty-environment guard unchanged. This fresh
            // check says nothing about the later shared body's faithfulness.
            let mut fresh = self.environment();
            return Ok(super::elaborate_prelude_header(&mut fresh, decls, context)?);
        }
        if !self.init_present {
            clean_kernel::tc::with_declaration_budget_suspended(|| {
                self.implicit_init(env, pristine_backbone)
            })?;
            self.init_present = true;
        }
        Ok(decls)
    }

    fn ensure_init_snapshot(&mut self) -> Result<(), SourceModuleError> {
        if self.init.is_none() {
            let mut fresh = self.environment();
            let (_, completed) = clean_olean::load_module_with_deps_and_completed_imports(
                &mut fresh,
                "Init",
                &self.search_paths,
            )
            .map_err(|error| SourceModuleError::ImplicitInit(error.to_string()))?;
            self.init = Some(fresh);
            self.init_completed_imports = Some(completed);
        }
        Ok(())
    }

    fn implicit_init(
        &mut self,
        env: &mut Environment,
        pristine_backbone: bool,
    ) -> Result<(), SourceModuleError> {
        self.ensure_init_snapshot()?;
        let Some(init) = &self.init else {
            return Err(SourceModuleError::ImplicitInit(
                "fresh Init was not retained".into(),
            ));
        };
        // Before any source body or command-line environment option, the
        // complete validated snapshot can replace the untouched backbone.
        // Preserve all environment extensions; never copy constants alone.
        if pristine_backbone
            && env.num_constants() == self.bare.num_constants()
            && env.effect_since(&self.bare).first_change().is_none()
        {
            *env = init.clone();
            return Ok(());
        }
        for expected in init.constants() {
            if let Some(actual) = env.get_const(&expected.name) {
                let same_declaration = actual.name == expected.name
                    && actual.level_params == expected.level_params
                    && actual.type_ == expected.type_
                    && actual.value == expected.value
                    && actual.kind == expected.kind;
                if !same_declaration
                    || env.get_constant_origin(&expected.name)
                        != init.get_constant_origin(&expected.name)
                {
                    return Err(SourceModuleError::ConflictingInit(expected.name.clone()));
                }
            }
        }
        if self.bootstrap_snapshot {
            return Err(SourceModuleError::ImplicitInit(
                "Clean-format bootstrap snapshot requires a pristine source environment".into(),
            ));
        }
        clean_olean::load_module_with_deps(env, "Init", &self.search_paths)
            .map_err(|error| SourceModuleError::ImplicitInit(error.to_string()))?;
        Ok(())
    }
}

/// Classify actual resolved artifact parts and their complete typed closure.
/// Source lookup and artifact search order match the frontend importer. A
/// genuine, payload-less, or explicit-prelude member keeps genuine Init;
/// missing, malformed and inconsistent artifacts are errors. Format grants
/// no proof credit: the normal importer and citation gate still run.
fn clean_format_source_closure(
    path: &Path,
    decision: &clean_olean::SourceWorldDecision,
) -> Result<bool, SourceModuleError> {
    clean_format_source_closure_with_import_policy(path, decision, crate::ImportPolicy::FailClosed)
}

fn clean_format_source_closure_with_import_policy(
    path: &Path,
    decision: &clean_olean::SourceWorldDecision,
    import_policy: crate::ImportPolicy,
) -> Result<bool, SourceModuleError> {
    let mut sources = vec![SourceVisit::Enter(path.to_path_buf())];
    let mut completed_sources = HashSet::new();
    let mut active_sources = HashSet::new();
    let mut artifacts = Vec::new();
    while let Some(visit) = sources.pop() {
        let source_path = match visit {
            SourceVisit::Enter(path) => path,
            SourceVisit::Leave { canonical, parent } => {
                active_sources.remove(&canonical);
                completed_sources.insert((canonical, parent));
                continue;
            }
        };
        let fail = |error: String| SourceModuleError::Header {
            path: source_path.clone(),
            reason: error,
        };
        let canonical =
            std::fs::canonicalize(&source_path).map_err(|error| fail(error.to_string()))?;
        if active_sources.contains(&canonical) {
            return Err(fail("source import cycle detected".into()));
        }
        // Lake-root discovery canonicalizes, while source lookup also walks
        // lexical parents. Preserve both contexts for completed aliases.
        let parent = source_path.parent().map(Path::to_path_buf);
        if completed_sources.contains(&(canonical.clone(), parent.clone())) {
            continue;
        }
        active_sources.insert(canonical.clone());
        sources.push(SourceVisit::Leave { canonical, parent });
        let source =
            std::fs::read_to_string(&source_path).map_err(|error| fail(error.to_string()))?;
        let header = clean_parser::Parser::parse_header_in_world(&source, decision.world())
            .map_err(|error| fail(error.to_string()))?;
        if header.is_prelude {
            return Ok(false);
        }
        let search_paths = artifact_search_paths(
            &source_path,
            decision
                .imports()
                .map_err(|error| fail(error.to_string()))?,
        );
        for import in header.imports {
            if let Some(source) =
                crate::resolve_intra_project_import(import.module.name(), &source_path)
            {
                sources.push(SourceVisit::Enter(source));
            } else {
                artifacts.push((import.module.name().clone(), search_paths.clone(), true));
            }
        }
    }

    let mut seen_artifacts = HashSet::new();
    let mut found_artifact = false;
    while let Some((module, search_paths, source_import)) = artifacts.pop() {
        let artifact = match clean_olean::resolve_typed_module_path_in_world(
            &module,
            &search_paths,
            decision.declared_world(),
        ) {
            Ok(artifact) => artifact,
            Err(clean_olean::ImportError::ModuleNotFound { .. })
                if source_import && import_policy == crate::ImportPolicy::Permissive =>
            {
                // The ordinary importer still emits the policy's warning.
                // Absence contributes no artifact and cannot justify bootstrap:
                // an all-absent graph leaves found_artifact false below.
                continue;
            }
            Err(error) => {
                return Err(SourceModuleError::Artifact {
                    path: path.to_path_buf(),
                    reason: error.to_string(),
                });
            }
        };
        let canonical =
            std::fs::canonicalize(&artifact).map_err(|error| SourceModuleError::Artifact {
                path: artifact.clone(),
                reason: error.to_string(),
            })?;
        if !seen_artifacts.insert((canonical, search_paths.clone())) {
            continue;
        }
        let read = clean_olean::read_artifact(
            &module.to_string(),
            &artifact,
            clean_olean::ArtifactDepth::Records,
        )
        .map_err(|error| SourceModuleError::Artifact {
            path: artifact,
            reason: error.to_string(),
        })?;
        found_artifact = true;
        if !read.clean_payload_parts {
            // The genuine importer performs this closure's world and import
            // checks. There is no bootstrap acceptance left to justify.
            return Ok(false);
        }
        for import in read.typed_imports {
            // An existing artifact promises this dependency. Even permissive
            // source checking must not turn its absence into a format choice.
            artifacts.push((import.module_name, search_paths.clone(), false));
        }
    }
    Ok(found_artifact)
}

#[cfg(test)]
#[path = "source_modules_tests.rs"]
mod tests;
