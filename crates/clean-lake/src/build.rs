// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lake build system
//!
//! Provides incremental compilation and parallel builds.

use crate::build_trace;
use crate::error::{LakeError, LakeResult};
use crate::workspace::Workspace;
use clean_elab::ElabResult;
use clean_kernel::env::ConstantInfo;
use clean_kernel::inductive::{ConstructorVal, InductiveVal, RecursorVal};
use clean_kernel::name::Name;
use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

/// Result of building modules: (built, skipped, failed)
/// - built: List of successfully built module names
/// - skipped: List of modules whose existing artifact was reused because its
///   build trace matches every input and output file (`build_trace`)
/// - failed: List of (module_name, error_message) for failed builds
type BuildModulesResult = (Vec<String>, Vec<String>, Vec<(String, String)>);

/// A build directory that exists only for the duration of one check-only
/// build and is removed when this value is dropped.
///
/// Not `tempfile::TempDir`: `tempfile` is a dev-dependency here, and a
/// check-only build must work in a shipped binary, not just under `cargo
/// test`. The name carries the pid and a per-process counter so concurrent
/// checks — several lanes, or one process checking several targets — never
/// share a directory.
#[derive(Debug)]
struct ScratchBuildDir {
    path: std::path::PathBuf,
}

impl ScratchBuildDir {
    fn create() -> LakeResult<Self> {
        use std::sync::atomic::{AtomicU64, Ordering};
        static SEQ: AtomicU64 = AtomicU64::new(0);

        let nanos = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map_or(0, |d| d.as_nanos());
        let path = std::env::temp_dir().join(format!(
            "clean-lake-check-{}-{nanos}-{}",
            std::process::id(),
            SEQ.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir_all(&path)?;
        Ok(Self { path })
    }
}

impl Drop for ScratchBuildDir {
    fn drop(&mut self) {
        // Best effort: a check-only build must not fail because its scratch
        // could not be removed, and the path is unique per run so a leftover
        // cannot poison the next one.
        let _ = std::fs::remove_dir_all(&self.path);
    }
}

/// The three parts of the artifact whose `.olean` is `olean`, in the order
/// the trace digests them.
fn artifact_parts_at(olean: &std::path::Path) -> [std::path::PathBuf; 3] {
    let with = |suffix: &str| {
        let mut raw = olean.as_os_str().to_os_string();
        raw.push(suffix);
        std::path::PathBuf::from(raw)
    };
    [olean.to_path_buf(), with(".server"), with(".private")]
}

/// The fixed git hash `clean lake build` writes into every `.olean` header it
/// produces (40 hex characters). An artifact carrying any other hash was not
/// written by this builder, so no fresh build here can reproduce it.
pub const CLEAN_OLEAN_GIT_HASH: &str = "1ea5000000000000000000000000000000000000";

/// The three artifact files of one module as a FRESH build wrote them.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FreshModuleArtifacts {
    /// `.olean`
    pub olean: Vec<u8>,
    /// `.olean.server`
    pub server: Vec<u8>,
    /// `.olean.private`
    pub private: Vec<u8>,
}

/// Build context for a workspace
pub struct BuildContext {
    /// The workspace being built
    workspace: Workspace,
    /// Module dependency graph
    deps: HashMap<String, Vec<String>>,
    /// Build options
    options: BuildOptions,
    /// Digests of artifact files already hashed during the current
    /// [`Self::build_modules`] pass, keyed by the `.olean` path (and of
    /// toolchain root `.olean`s, keyed by that path). Every module's trace
    /// names its whole transitive closure, so without this a no-op build of
    /// a chain of N modules hashed O(N²) files (round-27 measurement: 0.042 s
    /// at 40 modules, 0.29 s at 120). Cleared at the start of each pass and
    /// invalidated for a module whenever its artifact is about to be
    /// rewritten, so a digest is never served for bytes that changed under it.
    artifact_digests: Mutex<HashMap<std::path::PathBuf, String>>,
    /// Per module of the current pass: every module its build loads, with the
    /// file it is loaded from ([`Self::loaded_closure`]). Cleared with
    /// `artifact_digests`.
    closures: Mutex<HashMap<String, Arc<Vec<LoadedImport>>>>,
    /// Per file read for its imports during the current pass.
    import_headers: Mutex<HashMap<std::path::PathBuf, Arc<Vec<Name>>>>,
    /// The admission of every module a build loads that this workspace does
    /// not build itself: the one authority `clean check` uses
    /// ([`crate::ImportAdmitter`]).
    admission: Mutex<crate::artifact_binding::ImportAdmitter>,
    /// The disclosure rows of the current pass: artifacts taken as built.
    disclosures: Mutex<std::collections::BTreeSet<String>>,
}

/// One module a build loads, and the file it is loaded from.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct LoadedImport {
    module: String,
    olean: std::path::PathBuf,
}

/// Build options
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct BuildOptions {
    /// Number of parallel jobs (0 = auto)
    pub jobs: usize,
    /// Verbose output
    pub verbose: bool,
    /// Force rebuild all
    pub force: bool,
    /// Check the project without touching its build outputs.
    ///
    /// A check-only build elaborates and kernel-checks every module in
    /// dependency order into a SCRATCH build directory that is deleted when
    /// the build returns. The project's own `.lake/build` is neither read nor
    /// written, so:
    ///
    /// - no `.olean` / `.olean.server` / `.olean.private` artifact is left
    ///   behind, and none that already existed is overwritten;
    /// - nothing is skipped as "up to date", because the check does not
    ///   consult the project's artifact timestamps at all.
    ///
    /// That second property is the point. Measured 2026-08-27 while this flag
    /// was still inert: `clean lake check-build` on a project whose source had
    /// been replaced with syntactically invalid Lean printed
    /// "Build check passed." — the modules were skipped against a newer
    /// `.olean`, so the verdict came from the cache rather than from the
    /// source. A check that can pass without reading the source is a vacuous
    /// green.
    ///
    /// The redirection (rather than a guard around the export) is what keeps
    /// inter-module imports working: `build_module` resolves a module's
    /// imports by loading `.olean` files from disk
    /// (`clean_olean::load_module_with_deps`), and under check-only those
    /// files are the ones this same run just wrote into the scratch
    /// directory.
    ///
    /// Cost: a check-only build never reuses previous work, so it is a full
    /// elaboration every time.
    pub check_only: bool,
    /// Warn and continue when a stdlib or local-dependency `.olean` import
    /// fails to load, instead of failing the module build (fail-closed default)
    pub permissive_imports: bool,
}

impl BuildOptions {
    /// Create new build options with defaults
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Set number of parallel jobs
    #[must_use]
    pub fn with_jobs(mut self, jobs: usize) -> Self {
        self.jobs = jobs;
        self
    }

    /// Enable verbose output
    #[must_use]
    pub fn with_verbose(mut self, verbose: bool) -> Self {
        self.verbose = verbose;
        self
    }

    /// Force rebuild all
    #[must_use]
    pub fn with_force(mut self, force: bool) -> Self {
        self.force = force;
        self
    }

    /// Enable check-only mode (type check without code generation)
    #[must_use]
    pub fn with_check_only(mut self, check_only: bool) -> Self {
        self.check_only = check_only;
        self
    }

    /// Warn and continue on import load failures instead of failing the build
    #[must_use]
    pub fn with_permissive_imports(mut self, permissive_imports: bool) -> Self {
        self.permissive_imports = permissive_imports;
        self
    }
}

/// Result of a build operation
#[derive(Debug, Clone)]
pub struct BuildResult {
    /// Modules that were built
    pub built: Vec<String>,
    /// Modules not rebuilt: their existing artifact was reused because this
    /// builder's trace for it matches the source, every in-workspace
    /// dependency's artifact, the toolchain import roots and the artifact
    /// itself (see `build_trace`). A timestamp alone never lands a module here.
    pub skipped: Vec<String>,
    /// Modules that failed
    pub failed: Vec<(String, String)>,
    /// Imported artifacts the build loaded and took as built — no source
    /// compared with them — one row each, as `clean check` discloses them:
    /// what the built modules state holds of those artifacts' definitions.
    pub disclosures: Vec<String>,
    /// Total build time
    pub duration: Duration,
}

impl BuildResult {
    /// Check if build was successful
    #[must_use]
    pub fn is_success(&self) -> bool {
        self.failed.is_empty()
    }

    /// Get total number of modules processed
    #[must_use]
    pub fn total(&self) -> usize {
        self.built.len() + self.skipped.len() + self.failed.len()
    }
}

impl BuildContext {
    /// Extract value from shared mutex state.
    /// Falls back to lock+clone if outstanding `Arc` refs remain.
    fn take_shared_state<T: Clone>(state: Arc<Mutex<T>>) -> T {
        match Arc::try_unwrap(state) {
            Ok(mutex) => mutex.into_inner().unwrap_or_else(|e| e.into_inner()),
            Err(state) => state.lock().unwrap_or_else(|e| e.into_inner()).clone(),
        }
    }

    /// Create a new build context for a workspace
    #[must_use]
    pub fn new(workspace: Workspace) -> Self {
        Self {
            workspace,
            deps: HashMap::new(),
            options: BuildOptions::default(),
            artifact_digests: Mutex::new(HashMap::new()),
            closures: Mutex::new(HashMap::new()),
            import_headers: Mutex::new(HashMap::new()),
            admission: Mutex::new(crate::artifact_binding::ImportAdmitter::new()),
            disclosures: Mutex::new(std::collections::BTreeSet::new()),
        }
    }

    /// Set build options
    #[must_use]
    pub fn with_options(mut self, options: BuildOptions) -> Self {
        self.options = options;
        self
    }

    /// Get the workspace
    #[must_use]
    pub fn workspace(&self) -> &Workspace {
        &self.workspace
    }

    /// Point the workspace at a scratch build directory when
    /// [`BuildOptions::check_only`] is set, so the check neither reads nor
    /// writes the project's artifacts.
    ///
    /// Returns the scratch directory, which must be handed back to
    /// [`Self::end_check_only`] when the build finishes — dropping it removes
    /// the directory.
    fn begin_check_only(&mut self) -> LakeResult<Option<ScratchBuildDir>> {
        if !self.options.check_only {
            return Ok(None);
        }
        let scratch = ScratchBuildDir::create()?;
        if self.options.verbose {
            eprintln!(
                "Check-only build: writing throwaway artifacts to {}",
                scratch.path.display()
            );
        }
        self.workspace
            .set_build_dir_override(Some(scratch.path.clone()));
        Ok(Some(scratch))
    }

    /// Restore the project's own build directory and delete the scratch one.
    ///
    /// Runs on every exit path, including a failed build: leaving the override
    /// in place would silently redirect a later build on the same context to a
    /// directory that no longer exists.
    fn end_check_only(&mut self, scratch: Option<ScratchBuildDir>) {
        if scratch.is_some() {
            self.workspace.set_build_dir_override(None);
        }
        drop(scratch);
    }

    /// Build all targets
    pub fn build_all(&mut self) -> LakeResult<BuildResult> {
        let scratch = self.begin_check_only()?;
        let result = self.build_all_inner();
        self.end_check_only(scratch);
        result
    }

    fn build_all_inner(&mut self) -> LakeResult<BuildResult> {
        let start = Instant::now();

        // Create output directories
        self.workspace.validate_dependencies()?;
        self.workspace.create_dirs()?;

        // Discover dependencies
        self.discover_dependencies()?;

        // Get modules to build in topological order
        let modules = self.topological_sort()?;

        // Build modules
        let result = self.build_modules(&modules);

        Ok(BuildResult {
            built: result.0,
            skipped: result.1,
            failed: result.2,
            disclosures: self.take_disclosures(),
            duration: start.elapsed(),
        })
    }

    /// Build a specific target (library, executable, or test)
    pub fn build_target(&mut self, target: &str) -> LakeResult<BuildResult> {
        let scratch = self.begin_check_only()?;
        let result = self.build_target_inner(target);
        self.end_check_only(scratch);
        result
    }

    fn build_target_inner(&mut self, target: &str) -> LakeResult<BuildResult> {
        let start = Instant::now();

        // Create output directories
        self.workspace.validate_dependencies()?;
        self.workspace.create_dirs()?;

        // Find target
        let modules = if let Some(lib) = self
            .workspace
            .config()
            .libs
            .iter()
            .find(|l| l.name == target)
        {
            self.workspace.lib_modules(&lib.name)?
        } else if let Some(exe) = self
            .workspace
            .config()
            .exes
            .iter()
            .find(|e| e.name == target)
        {
            vec![exe.root.clone()]
        } else if let Some(test) = self
            .workspace
            .config()
            .tests
            .iter()
            .find(|t| t.name == target)
        {
            vec![test.root.clone()]
        } else {
            return Err(LakeError::ModuleNotFound(target.to_string()));
        };

        // Discover dependencies for these modules
        for module in &modules {
            self.discover_module_deps(module)?;
        }

        // Build in dependency order
        let ordered = self.topological_sort_subset(&modules)?;
        let result = self.build_modules(&ordered);

        Ok(BuildResult {
            built: result.0,
            skipped: result.1,
            failed: result.2,
            disclosures: self.take_disclosures(),
            duration: start.elapsed(),
        })
    }

    /// Build the named source **modules** and their local dependency closure.
    ///
    /// The module-granular counterpart of [`Self::build_target`], which
    /// resolves a lakefile *target* name (a `lean_lib` / `lean_exe` /
    /// `lean_test` entry). Lean's own Lake accepts either spelling on the
    /// command line (`lake build Foo.Bar` builds a module), and Clean's
    /// project manager declares its work as a `modules` list rather than a
    /// target list — so a module-name entry point is what a native
    /// `cake build` needs in order to stop shelling out to `lake`.
    ///
    /// **Fail-closed.** A name the workspace cannot resolve to a source file
    /// is [`LakeError::ModuleNotFound`], never a silent skip: reporting
    /// "0 built, 0 failed" for a typo'd module would let a caller record a
    /// successful build of nothing.
    pub fn build_modules_named(&mut self, modules: &[String]) -> LakeResult<BuildResult> {
        let scratch = self.begin_check_only()?;
        let result = self.build_modules_named_inner(modules);
        self.end_check_only(scratch);
        result
    }

    /// Build `modules` and their in-workspace dependencies FROM SOURCE into a
    /// scratch directory, and return what that build wrote for each requested
    /// module AND each in-workspace dependency it built. The project's own
    /// build directory is neither read nor written, and nothing is skipped as
    /// up to date.
    ///
    /// This is the reference `clean lake verify-fresh` compares an artifact
    /// against: an artifact is fresh only if it is byte-identical to what the
    /// current source builds to (the builder is byte-reproducible). A module
    /// whose fresh build fails is absent from the map and listed in the
    /// result's `failed`.
    pub fn build_fresh_artifacts(
        &mut self,
        modules: &[String],
    ) -> LakeResult<(BuildResult, HashMap<String, FreshModuleArtifacts>)> {
        let scratch = ScratchBuildDir::create()?;
        self.workspace
            .set_build_dir_override(Some(scratch.path.clone()));
        let built = self.build_modules_named_inner(modules).and_then(|result| {
            let mut artifacts = HashMap::new();
            for module in modules.iter().chain(&result.built) {
                if artifacts.contains_key(module) || result.failed.iter().any(|(m, _)| m == module)
                {
                    continue;
                }
                let olean = self.workspace.olean_path(module)?;
                if !olean.exists() {
                    continue;
                }
                artifacts.insert(
                    module.clone(),
                    FreshModuleArtifacts {
                        olean: std::fs::read(&olean)?,
                        server: std::fs::read(self.workspace.olean_server_path(module)?)?,
                        private: std::fs::read(self.workspace.olean_private_path(module)?)?,
                    },
                );
            }
            Ok((result, artifacts))
        });
        self.workspace.set_build_dir_override(None);
        drop(scratch);
        built
    }

    fn build_modules_named_inner(&mut self, modules: &[String]) -> LakeResult<BuildResult> {
        let start = Instant::now();

        // Create output directories
        self.workspace.validate_dependencies()?;
        self.workspace.create_dirs()?;

        // Resolve every requested name BEFORE building anything, so a bad
        // name in the list cannot half-build the good ones.
        for module in modules {
            if self.workspace.find_module(module).is_none() {
                return Err(LakeError::ModuleNotFound(module.clone()));
            }
        }
        for module in modules {
            self.discover_module_deps(module)?;
        }

        // Build in dependency order
        let ordered = self.topological_sort_subset(modules)?;
        let result = self.build_modules(&ordered);

        Ok(BuildResult {
            built: result.0,
            skipped: result.1,
            failed: result.2,
            disclosures: self.take_disclosures(),
            duration: start.elapsed(),
        })
    }

    /// Discover all module dependencies
    fn discover_dependencies(&mut self) -> LakeResult<()> {
        self.deps.clear();

        for module in self.workspace.all_modules()? {
            self.discover_module_deps(&module)?;
        }

        Ok(())
    }

    /// Discover dependencies for a single module
    fn discover_module_deps(&mut self, module: &str) -> LakeResult<()> {
        if self.deps.contains_key(module) {
            return Ok(());
        }

        let Some(src_path) = self.workspace.find_module(module) else {
            // External module - no deps to discover
            self.deps.insert(module.to_string(), vec![]);
            return Ok(());
        };

        let content = std::fs::read_to_string(&src_path)?;
        let imports = self.extract_imports(&content)?;

        // Recursively discover deps for imported modules
        for imp in &imports {
            if !self.deps.contains_key(imp) {
                self.discover_module_deps(imp)?;
            }
        }

        self.deps.insert(module.to_string(), imports);
        Ok(())
    }

    /// Extract import statements from Lean source (for local dependency tracking)
    /// This filters out stdlib imports since they don't need to be built locally.
    fn extract_imports(&self, content: &str) -> LakeResult<Vec<String>> {
        Ok(Self::extract_all_imports(content)?
            .into_iter()
            .filter(|m| !self.is_stdlib_import(m))
            .collect())
    }

    /// Read dependency names with the same header grammar as elaboration.
    /// Line scanning loses public/meta imports, modifiers, multiline names and
    /// comments, and can mistake text in a comment for a dependency.
    fn extract_all_imports(content: &str) -> LakeResult<Vec<String>> {
        let header = clean_parser::Parser::parse_header(content)
            .map_err(|error| LakeError::Elaboration(format!("invalid module header: {error}")))?;
        Ok(header
            .imports
            .into_iter()
            .map(|import| import.module.name().to_string())
            .collect())
    }

    /// Does `module` carry one of the toolchain's reserved name prefixes?
    ///
    /// This is a NAME test only — it says nothing about who provides the
    /// module. Use [`Self::is_stdlib_import`] for the routing decision.
    fn has_stdlib_prefix(module: &str) -> bool {
        module.starts_with("Init")
            || module.starts_with("Std")
            || module.starts_with("Lean")
            || module.starts_with("Lake")
            || module.starts_with("Mathlib")
    }

    /// Check if a module must be loaded from the Lean toolchain rather than
    /// built here.
    ///
    /// A module the WORKSPACE can provide is local, whatever its name. The
    /// name prefix alone is not the answer: `Init`, `Std`, `Lean`, `Lake` and
    /// `Mathlib` are ordinary identifiers a package is free to declare
    /// (`lean_lib Std` with `Std/Mine.lean` is a legal Lake project, and
    /// batteries/std4/mathlib4 themselves are exactly such projects — the
    /// repos the drop-in goal is defined by).
    ///
    /// Consulting the workspace first closes a measured WRONG BUILD: a package
    /// declaring `lean_lib Std` built `Std.Mine`, then failed `Std.User` with
    /// `failed to load stdlib import 'Std.Mine' … not found in [elan
    /// toolchain]`, ignoring the artifact it had just produced. The silent face
    /// of the same bug is worse — under `--permissive-imports`, or wherever a
    /// same-named toolchain `.olean` exists, the project's own module is
    /// replaced by Lean's with no diagnostic at all.
    fn is_stdlib_import(&self, module: &str) -> bool {
        Self::has_stdlib_prefix(module) && self.workspace.find_module(module).is_none()
    }

    /// Topological sort of all modules
    fn topological_sort(&self) -> LakeResult<Vec<String>> {
        self.topological_sort_subset(&self.deps.keys().cloned().collect::<Vec<_>>())
    }

    /// Topological sort of a subset of modules
    fn topological_sort_subset(&self, modules: &[String]) -> LakeResult<Vec<String>> {
        let mut result = vec![];
        let mut visited = HashSet::new();
        let mut temp_marks = HashSet::new();

        fn visit(
            module: &str,
            deps: &HashMap<String, Vec<String>>,
            visited: &mut HashSet<String>,
            temp_marks: &mut HashSet<String>,
            result: &mut Vec<String>,
        ) -> Result<(), String> {
            if temp_marks.contains(module) {
                return Err(module.to_string());
            }
            if visited.contains(module) {
                return Ok(());
            }

            temp_marks.insert(module.to_string());

            if let Some(module_deps) = deps.get(module) {
                for dep in module_deps {
                    visit(dep, deps, visited, temp_marks, result)?;
                }
            }

            temp_marks.remove(module);
            visited.insert(module.to_string());
            result.push(module.to_string());
            Ok(())
        }

        for module in modules {
            if !visited.contains(module) {
                visit(
                    module,
                    &self.deps,
                    &mut visited,
                    &mut temp_marks,
                    &mut result,
                )
                .map_err(LakeError::CircularDependency)?;
            }
        }

        Ok(result)
    }

    /// Build modules in the given order (with parallel execution)
    fn build_modules(&self, modules: &[String]) -> BuildModulesResult {
        use rayon::prelude::*;

        // Digests memoized by an earlier pass may describe files rewritten
        // since; each pass starts from the files as they are.
        self.artifact_digests
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .clear();
        self.closures
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .clear();
        self.import_headers
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .clear();
        self.disclosures
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .clear();

        let built = Arc::new(Mutex::new(vec![]));
        let skipped = Arc::new(Mutex::new(vec![]));
        let failed = Arc::new(Mutex::new(vec![]));
        let built_set = Arc::new(Mutex::new(HashSet::<String>::new()));

        // Organize modules into levels for parallel execution
        // Level N contains modules that only depend on modules in levels < N
        let levels = self.compute_build_levels(modules);

        // Configure thread pool
        let num_threads = if self.options.jobs == 0 {
            rayon::current_num_threads()
        } else {
            self.options.jobs
        };

        // Build thread pool with requested thread count, falling back to default if that fails
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(num_threads)
            .build()
            .unwrap_or_else(|_| {
                rayon::ThreadPoolBuilder::new()
                    .build()
                    .expect("failed to create rayon thread pool with default settings")
            });

        // Process each level in order (all modules in a level can build in parallel)
        for level in levels {
            // Check for failures - stop processing if any module failed
            if !failed.lock().unwrap_or_else(|e| e.into_inner()).is_empty() {
                break;
            }

            pool.install(|| {
                level.par_iter().for_each(|module| {
                    // Check if already failed
                    if !failed.lock().unwrap_or_else(|e| e.into_inner()).is_empty() {
                        return;
                    }

                    // Reuse the module's artifact only when its build trace
                    // matches the files on disk now (see `build_trace`); a
                    // timestamp alone never credits a module.
                    let reuse = match self.may_reuse_artifact(module) {
                        Ok(value) => value,
                        Err(error) => {
                            failed
                                .lock()
                                .unwrap_or_else(|e| e.into_inner())
                                .push((module.clone(), error.to_string()));
                            return;
                        }
                    };
                    if reuse {
                        // A reused module rests on the same imports as a
                        // built one: admitted the same way, every pass.
                        if let Err(error) = self.admit_imports(module) {
                            failed
                                .lock()
                                .unwrap_or_else(|e| e.into_inner())
                                .push((module.clone(), error.to_string()));
                            return;
                        }
                        skipped
                            .lock()
                            .unwrap_or_else(|e| e.into_inner())
                            .push(module.clone());
                        built_set
                            .lock()
                            .unwrap_or_else(|e| e.into_inner())
                            .insert(module.clone());
                        return;
                    }

                    // Check that all dependencies are built/skipped
                    if let Some(deps) = self.deps.get(module) {
                        let done = built_set.lock().unwrap_or_else(|e| e.into_inner());
                        for dep in deps {
                            if !done.contains(dep) {
                                // Dependency not ready - this shouldn't happen if levels are correct
                                // but handle it gracefully
                                failed
                                    .lock()
                                    .unwrap_or_else(|e| e.into_inner())
                                    .push((module.clone(), format!("dependency {dep} not built")));
                                return;
                            }
                        }
                    }

                    match self.build_module(module) {
                        Ok(()) => {
                            built
                                .lock()
                                .unwrap_or_else(|e| e.into_inner())
                                .push(module.clone());
                            built_set
                                .lock()
                                .unwrap_or_else(|e| e.into_inner())
                                .insert(module.clone());
                        }
                        Err(e) => {
                            failed
                                .lock()
                                .unwrap_or_else(|e| e.into_inner())
                                .push((module.clone(), e.to_string()));
                        }
                    }
                });
            });
        }

        let built = Self::take_shared_state(built);
        let skipped = Self::take_shared_state(skipped);
        let failed = Self::take_shared_state(failed);

        (built, skipped, failed)
    }

    /// The three artifact files of `module`, in the order the trace digests them.
    fn artifact_parts(&self, module: &str) -> LakeResult<[std::path::PathBuf; 3]> {
        Ok([
            self.workspace.olean_path(module)?,
            self.workspace.olean_server_path(module)?,
            self.workspace.olean_private_path(module)?,
        ])
    }

    /// `key`'s digest from this pass's memo, computing it with `compute` on
    /// a miss.
    fn memo_digest(
        &self,
        key: &std::path::Path,
        compute: impl FnOnce() -> LakeResult<String>,
    ) -> LakeResult<String> {
        if let Some(digest) = self
            .artifact_digests
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .get(key)
        {
            return Ok(digest.clone());
        }
        let digest = compute()?;
        self.artifact_digests
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .insert(key.to_path_buf(), digest.clone());
        Ok(digest)
    }

    /// Forget the memoized digest of `module`'s artifact: it is about to be
    /// (or has just been) rewritten.
    fn forget_digest(&self, olean: &std::path::Path) {
        self.artifact_digests
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .remove(olean);
    }

    /// What `module`'s build reads, as its build trace records it: the source
    /// `content`, the artifacts of every in-workspace module in its transitive
    /// import closure, and the root `.olean` of each toolchain import.
    fn trace_inputs(&self, module: &str, content: &str) -> LakeResult<build_trace::TraceInputs> {
        let mut closure: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
        let mut stack: Vec<&String> = self.deps.get(module).into_iter().flatten().collect();
        while let Some(dep) = stack.pop() {
            if dep != module && closure.insert(dep.clone()) {
                stack.extend(self.deps.get(dep).into_iter().flatten());
            }
        }
        let mut inputs = std::collections::BTreeMap::new();
        for dep in closure {
            let parts = self.artifact_parts(&dep)?;
            let digest =
                self.memo_digest(&parts[0], || build_trace::digest_artifact_parts(&parts))?;
            inputs.insert(dep, digest);
        }
        // Every module the build loads that this workspace does not build,
        // by the file it loads and all three of its parts: a rewritten
        // module anywhere in the closure, not only a named import's root
        // `.olean`, is a changed input.
        let mut external: std::collections::BTreeMap<String, String> =
            std::collections::BTreeMap::new();
        for loaded in self.loaded_closure(module, content)?.iter() {
            if self.built_here(loaded) {
                continue;
            }
            let parts = artifact_parts_at(&loaded.olean);
            let digest =
                self.memo_digest(&loaded.olean, || build_trace::digest_artifact_parts(&parts))?;
            // One module loaded from two files (by the two search-path
            // lists the build uses) records both.
            external
                .entry(loaded.module.clone())
                .and_modify(|d| {
                    if !d.split('+').any(|x| x == digest) {
                        d.push('+');
                        d.push_str(&digest);
                    }
                })
                .or_insert(digest);
        }
        for imp in Self::extract_all_imports(content)? {
            if self.is_stdlib_import(&imp)
                && clean_olean::find_module_olean(&imp, &clean_olean::default_search_paths())
                    .is_none()
            {
                external.insert(imp, "unresolved".to_string());
            }
        }
        Ok(build_trace::TraceInputs {
            source: content.as_bytes().to_vec(),
            inputs,
            stdlib: external,
            permissive_imports: self.options.permissive_imports,
            // The language the module is compiled in: an artifact built under
            // other `leanOptions` is not this build's (Lake hashes its
            // `leanArgs` into the trace the same way).
            lean_args: self.workspace.module_lean_args(module)?,
        })
    }

    /// Whether `loaded` is a module this workspace builds, loaded from where
    /// this build writes it: built (or its trace verified) earlier in the
    /// same pass, so it needs no admission.
    fn built_here(&self, loaded: &LoadedImport) -> bool {
        self.workspace.find_module(&loaded.module).is_some()
            && self
                .workspace
                .olean_path(&loaded.module)
                .is_ok_and(|path| path == loaded.olean)
    }

    /// The imports recorded in the `.olean` at `path`, read once per pass.
    fn header_imports(&self, path: &std::path::Path) -> LakeResult<Arc<Vec<Name>>> {
        if let Some(imports) = self
            .import_headers
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .get(path)
        {
            return Ok(Arc::clone(imports));
        }
        let bytes = std::fs::read(path)?;
        let imports: Vec<Name> = clean_olean::parse_typed_imports(&bytes)
            .map_err(|e| LakeError::BuildFailed {
                module: path.display().to_string(),
                reason: format!("unreadable import header: {e}"),
            })?
            .into_iter()
            .map(|import| import.module_name)
            .collect();
        let imports = Arc::new(imports);
        self.import_headers
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .insert(path.to_path_buf(), Arc::clone(&imports));
        Ok(imports)
    }

    /// Walk the import closure of `root` exactly as the loader does
    /// (`clean_olean::load_module_with_deps` over `search_paths`: each
    /// module from the first root holding it, then the imports its `.olean`
    /// records), adding every module and file to `out`. A module that
    /// resolves nowhere is left to the load, which fails on it.
    fn walk_imports(
        &self,
        root: &str,
        search_paths: &[std::path::PathBuf],
        out: &mut std::collections::BTreeSet<LoadedImport>,
    ) -> LakeResult<()> {
        let Some(root_path) = clean_olean::find_module_olean(root, search_paths) else {
            return Ok(());
        };
        let mut seen: HashSet<Name> = HashSet::new();
        let mut stack: Vec<(String, std::path::PathBuf)> = vec![(root.to_string(), root_path)];
        while let Some((module, olean)) = stack.pop() {
            for import in self.header_imports(&olean)?.iter() {
                if !seen.insert(import.clone()) {
                    continue;
                }
                if let Ok(path) = clean_olean::resolve_typed_module_path(import, search_paths) {
                    stack.push((import.to_string(), path));
                }
            }
            out.insert(LoadedImport { module, olean });
        }
        Ok(())
    }

    // A stopped loader may already have inserted part of a module. Continuing
    // would use that partial environment as though the import had finished.
    fn import_allows_fallback(e: &clean_olean::ImportError) -> bool {
        !e.is_world_refusal() && !e.is_resource_refusal()
    }

    /// The opt-out a failed import load names: none for a refused Lean
    /// world, which `--permissive-imports` does not continue past (R81).
    fn import_failure_hint(e: &clean_olean::ImportError) -> &'static str {
        if e.is_world_refusal() {
            "(no import policy continues past a refused Lean world, docs/DECISIONS.md R81)"
        } else if e.is_resource_refusal() {
            "(resource exhaustion or interruption leaves an incomplete import; retry in a fresh environment)"
        } else {
            "(pass --permissive-imports to warn and continue)"
        }
    }

    /// Every module `module`'s build loads, with the file it is loaded
    /// from — what [`Self::build_module`] loads: each toolchain-named import
    /// the workspace does not provide, with its closure over the default
    /// search paths, and each in-workspace dependency already built, with
    /// its closure over the build directory then those paths.
    /// An import of `module` whose artifact cannot be read while its closure
    /// is walked. Fail-closed by default, exactly as the load below it: the
    /// module fails, naming the import and the opt-out. Under the explicit
    /// `--permissive-imports` opt-out it is a warning and the walk goes on
    /// without it; the load then meets the same artifact and warns again.
    fn unreadable_import(&self, module: &str, what: &str) -> LakeResult<()> {
        if !self.options.permissive_imports {
            return Err(LakeError::BuildFailed {
                module: module.to_string(),
                reason: format!("{what} (pass --permissive-imports to warn and continue)"),
            });
        }
        eprintln!("  Warning: {what}");
        Ok(())
    }

    fn loaded_closure(&self, module: &str, content: &str) -> LakeResult<Arc<Vec<LoadedImport>>> {
        if let Some(closure) = self
            .closures
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .get(module)
        {
            return Ok(Arc::clone(closure));
        }
        let defaults = clean_olean::default_search_paths();
        let mut out = std::collections::BTreeSet::new();
        for imp in Self::extract_all_imports(content)? {
            if self.is_stdlib_import(&imp) {
                if let Err(e) = self.walk_imports(&imp, &defaults, &mut out) {
                    self.unreadable_import(
                        module,
                        &format!("failed to load stdlib import '{imp}': {e}"),
                    )?;
                }
            }
        }
        let mut dep_search_paths = vec![self.workspace.lib_dir()];
        dep_search_paths.extend(defaults);
        for dep in self.deps.get(module).into_iter().flatten() {
            let olean_path = self.workspace.olean_path(dep)?;
            if olean_path.exists() {
                if let Err(e) = self.walk_imports(dep, &dep_search_paths, &mut out) {
                    self.unreadable_import(
                        module,
                        &format!(
                            "failed to load dependency '{dep}' from {}: {e}",
                            olean_path.display()
                        ),
                    )?;
                }
            }
        }
        let closure = Arc::new(out.into_iter().collect::<Vec<_>>());
        self.closures
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .insert(module.to_string(), Arc::clone(&closure));
        Ok(closure)
    }

    /// Admit every module `module`'s build loads that this workspace does
    /// not build itself, through the authority `clean check` uses
    /// ([`crate::ImportAdmitter`]): the pinned toolchain's own build (by
    /// digest) is the base; an artifact that is not the build of the source
    /// beside it refuses the module; one with no source to compare, or
    /// written by another tool, is taken as built and disclosed. A module's
    /// name grants nothing: `Mathlib.*`, `Std.*` or `Init.*` outside the
    /// pinned toolchain is an artifact like any other.
    fn admit_imports(&self, module: &str) -> LakeResult<()> {
        let src_path = self
            .workspace
            .find_module(module)
            .ok_or_else(|| LakeError::ModuleNotFound(module.to_string()))?;
        let content = std::fs::read_to_string(&src_path)?;
        let closure = self.loaded_closure(module, &content)?;
        let mut admission = self.admission.lock().unwrap_or_else(|e| e.into_inner());
        let mut refusals = Vec::new();
        for loaded in closure.iter() {
            if self.built_here(loaded) {
                continue;
            }
            match admission.admit(&loaded.module, &loaded.olean) {
                crate::artifact_binding::ImportAdmission::Toolchain
                | crate::artifact_binding::ImportAdmission::Bound => {}
                crate::artifact_binding::ImportAdmission::Refused(row) => refusals.push(row),
                crate::artifact_binding::ImportAdmission::Disclosed(row) => {
                    self.disclosures
                        .lock()
                        .unwrap_or_else(|e| e.into_inner())
                        .insert(row);
                }
            }
        }
        if refusals.is_empty() {
            Ok(())
        } else {
            Err(LakeError::BuildFailed {
                module: module.to_string(),
                reason: refusals.join("; "),
            })
        }
    }

    /// The disclosure rows of the pass that just ran.
    fn take_disclosures(&self) -> Vec<String> {
        std::mem::take(&mut *self.disclosures.lock().unwrap_or_else(|e| e.into_inner()))
            .into_iter()
            .collect()
    }

    /// Why `module`'s artifact in this workspace's build directory is not
    /// what this builder recorded building from its current source; `None`
    /// when its build trace matches every input and output file now.
    ///
    /// The consumer-side twin of the reuse decision below, for a consumer
    /// (`clean check`, `clean export-cert`) that loads the artifact instead
    /// of building it (see [`crate::artifact_binding`]). The comparison is
    /// always the strict one: a trace written under `--permissive-imports`
    /// does not bind.
    pub(crate) fn artifact_trace_refusal(
        &mut self,
        module: &str,
    ) -> LakeResult<Option<&'static str>> {
        let src_path = self
            .workspace
            .find_module(module)
            .ok_or_else(|| LakeError::ModuleNotFound(module.to_string()))?;
        self.discover_module_deps(module)?;
        let content = std::fs::read_to_string(&src_path)?;
        let parts = self.artifact_parts(module)?;
        let mut current = self.trace_inputs(module, &content)?;
        current.permissive_imports = false;
        build_trace::reuse_refusal(&parts[0], &parts, current)
    }

    /// May `module`'s existing artifact be counted as built without building
    /// it? Only when this builder's trace for it matches every input and
    /// output file as it is now; `--force` never reuses.
    fn may_reuse_artifact(&self, module: &str) -> LakeResult<bool> {
        // `needs_rebuild` first, whatever `--force` says: it validates the
        // module's output identity, and an invalid one fails the module.
        if self.workspace.needs_rebuild(module)? || self.options.force {
            return Ok(false);
        }
        let src_path = self
            .workspace
            .find_module(module)
            .ok_or_else(|| LakeError::ModuleNotFound(module.to_string()))?;
        let content = std::fs::read_to_string(&src_path)?;
        let parts = self.artifact_parts(module)?;
        let refusal =
            build_trace::reuse_refusal(&parts[0], &parts, self.trace_inputs(module, &content)?)?;
        if let Some(reason) = refusal {
            if self.options.verbose {
                eprintln!("Rebuilding {module}: existing artifact not reused ({reason})");
            }
            return Ok(false);
        }
        Ok(true)
    }

    /// Compute build levels for parallel execution
    /// Returns a vector of levels, where each level contains modules that can be built in parallel
    fn compute_build_levels(&self, modules: &[String]) -> Vec<Vec<String>> {
        let module_set: HashSet<_> = modules.iter().cloned().collect();
        let mut levels: Vec<Vec<String>> = vec![];
        let mut assigned: HashSet<String> = HashSet::new();

        // Keep assigning modules to levels until all are assigned
        while assigned.len() < modules.len() {
            let mut current_level = vec![];

            for module in modules {
                if assigned.contains(module) {
                    continue;
                }

                // Check if all dependencies are either:
                // 1. Not in the module set (external), or
                // 2. Already assigned to a previous level
                let deps_ready = self.deps.get(module).is_none_or(|deps| {
                    deps.iter()
                        .all(|dep| !module_set.contains(dep) || assigned.contains(dep))
                });

                if deps_ready {
                    current_level.push(module.clone());
                }
            }

            // If no progress was made, there's a cycle or missing dependency
            if current_level.is_empty() && assigned.len() < modules.len() {
                // Add remaining modules to final level (will fail on missing deps)
                for module in modules {
                    if !assigned.contains(module) {
                        current_level.push(module.clone());
                    }
                }
            }

            for m in &current_level {
                assigned.insert(m.clone());
            }

            if !current_level.is_empty() {
                levels.push(current_level);
            }
        }

        levels
    }

    /// Build a single module
    fn build_module(&self, module: &str) -> LakeResult<()> {
        let src_path = self
            .workspace
            .find_module(module)
            .ok_or_else(|| LakeError::ModuleNotFound(module.to_string()))?;

        if self.options.verbose {
            eprintln!("Building {module}");
        }

        // Read source
        let content = std::fs::read_to_string(&src_path)?;

        // What this build reads, recorded BEFORE anything is loaded, and the
        // old trace removed before anything is written: a failed build must
        // not leave a trace that still names the old artifact.
        let trace_inputs = self.trace_inputs(module, &content)?;
        let artifact_parts = self.artifact_parts(module)?;
        build_trace::remove_trace(&artifact_parts[0])?;
        self.forget_digest(&artifact_parts[0]);
        // Every module this build is about to load that the workspace does
        // not build itself is admitted first, as `clean check` admits it.
        self.admit_imports(module)?;
        let admitted = self.loaded_closure(module, &content)?;

        // Parse
        let parsed = clean_parser::parse_file_with_diagnostics(&content).map_err(|e| {
            LakeError::BuildFailed {
                module: module.to_string(),
                reason: format!("parse error: {e}"),
            }
        })?;

        let header = parsed.header;
        let surface = parsed.decls;

        // Create environment with imported modules
        let mut env = clean_kernel::Environment::with_prelude();
        env.init_io_ops().map_err(|e| LakeError::BuildFailed {
            module: module.to_string(),
            reason: format!("IO operation initialization failed: {e}"),
        })?;
        // The environment as this build constructed it, BEFORE any import:
        // everything loaded below — stdlib and local dependency artifacts
        // alike — enters structurally (never type-checked), so before this
        // module is exported its declarations' cited closure is re-admitted
        // by the kernel over exactly this base (module-trust, 2026-09-24).
        let mut import_gate = clean_olean::ImportedConeGate::new(&env);

        // Extract ALL imports (including stdlib) from this file
        let all_imports = Self::extract_all_imports(&content)?;

        // Load stdlib imports from the Lean toolchain
        let stdlib_imports: Vec<_> = all_imports
            .iter()
            .filter(|m| self.is_stdlib_import(m))
            .collect();

        if !stdlib_imports.is_empty() {
            let search_paths = clean_olean::default_search_paths();
            if self.options.verbose && !search_paths.is_empty() {
                eprintln!("  Stdlib search paths: {:?}", search_paths);
            }

            for imp in &stdlib_imports {
                match clean_olean::load_module_with_deps(&mut env, imp, &search_paths) {
                    Ok(summaries) => {
                        Self::loaded_as_admitted(module, &summaries, &admitted)?;
                        if self.options.verbose {
                            let total_consts: usize =
                                summaries.iter().map(|s| s.added_constants).sum();
                            eprintln!(
                                "  Loaded stdlib {} ({} constants from {} modules)",
                                imp,
                                total_consts,
                                summaries.len()
                            );
                        }
                    }
                    Err(e) => {
                        // Fail-closed by default: a module must not "build"
                        // against a silently incomplete environment. The
                        // explicit --permissive-imports opt-out restores the
                        // legacy warn-and-continue behavior, except past a
                        // part of a refused or second Lean world (R38, R81), or
                        // a resource stop leaving a partially loaded environment.
                        if !self.options.permissive_imports || !Self::import_allows_fallback(&e) {
                            return Err(LakeError::BuildFailed {
                                module: module.to_string(),
                                reason: format!(
                                    "failed to load stdlib import '{imp}': {e} {}",
                                    Self::import_failure_hint(&e)
                                ),
                            });
                        }
                        eprintln!("  Warning: failed to load stdlib {imp}: {e}");
                        // Permissive mode: continue - might still succeed if
                        // the import isn't critical
                    }
                }
            }
        }

        // Collect local import names for .olean export
        let import_names: Vec<String> = self.deps.get(module).cloned().unwrap_or_default();

        // Load local project dependencies from .olean files — with their
        // TRANSITIVE import closure, exactly as the stdlib branch above does.
        // Loading only the direct dep's single .olean was a measured WRONG
        // BUILD: in an A→B→C require chain, A's environment held B's
        // constants but never C's, so any A-value reaching through B to C was
        // definitionally stuck (`theorem a_eq : a = 5 := rfl` failed while
        // `clean lake build` reported success on every module). The closure
        // loader walks each dep's imports through the workspace lib dir
        // (every package's modules land there) and falls back to the stdlib
        // search paths for deps that import Init/Std.
        let mut dep_search_paths = vec![self.workspace.lib_dir()];
        dep_search_paths.extend(clean_olean::default_search_paths());
        for dep in &import_names {
            let olean_path = self.workspace.olean_path(dep)?;
            if olean_path.exists() {
                match clean_olean::load_module_with_deps(&mut env, dep, &dep_search_paths) {
                    Ok(summaries) => {
                        Self::loaded_as_admitted(module, &summaries, &admitted)?;
                        if self.options.verbose {
                            let total: usize = summaries.iter().map(|s| s.added_constants).sum();
                            eprintln!(
                                "  Loaded {} (+{} modules, {} constants)",
                                dep,
                                summaries.len().saturating_sub(1),
                                total
                            );
                        }
                    }
                    Err(e) => {
                        // Fail-closed by default (see the stdlib branch above).
                        if !self.options.permissive_imports || !Self::import_allows_fallback(&e) {
                            return Err(LakeError::BuildFailed {
                                module: module.to_string(),
                                reason: format!(
                                    "failed to load dependency '{dep}' from {}: {e} {}",
                                    olean_path.display(),
                                    Self::import_failure_hint(&e)
                                ),
                            });
                        }
                        eprintln!("  Warning: failed to load {dep}.olean: {e}");
                        // Permissive mode: continue - the elaboration may still
                        // succeed if the dep isn't actually used
                    }
                }
            } else if self.options.verbose {
                eprintln!("  Note: dependency {dep} not yet built");
            }
        }

        // Session support the elaborator seeds into the environment (PProd, the
        // `instHAdd`-family bridge instances) is fixed repo-authored setup, not
        // this module's declarations: seed it BEFORE the census below so it is
        // neither exported into this module's artifact nor re-exported by every
        // module of the package. `prepare_declaration_environment` is idempotent
        // and is what the elaborator entry repeats per declaration.
        if let Some(first) = surface
            .iter()
            .find(|d| !matches!(d, clean_parser::SurfaceDecl::Import { .. }))
        {
            clean_elab::prepare_declaration_environment(&mut env, first);
        }

        // Snapshot environment before elaboration so we can capture only new declarations
        let baseline_consts: HashSet<Name> = env.constants().map(|c| c.name.clone()).collect();
        let baseline_inds: HashSet<Name> = env.inductives().map(|i| i.name.clone()).collect();
        let baseline_ctors: HashSet<Name> = env.constructors().map(|c| c.name.clone()).collect();
        let baseline_recs: HashSet<Name> = env.recursors().map(|r| r.name.clone()).collect();
        let baseline_exports = ModuleExportBaseline::take(&env);

        // The `leanOptions` / `moreLeanArgs` Lake compiles this module with,
        // installed as the initial option state of its file (gap G50).
        let lean_args = self.module_lean_options(module)?;
        let (example_roots, global_readds) =
            Self::elaborate_module(module, &surface, &header, &mut env, &lean_args)?;

        Self::gate_module_examples(module, &env, &mut import_gate, &example_roots)?;
        Self::gate_module_closure(module, &env, &mut import_gate, &baseline_consts)?;

        // Collect newly added declarations for payload/export
        let mut new_inductives: Vec<InductiveVal> = env
            .inductives()
            .filter(|i| !baseline_inds.contains(&i.name))
            .cloned()
            .collect();
        let mut new_constructors: Vec<ConstructorVal> = env
            .constructors()
            .filter(|c| !baseline_ctors.contains(&c.name))
            .cloned()
            .collect();
        let mut new_recursors: Vec<RecursorVal> = env
            .recursors()
            .filter(|r| !baseline_recs.contains(&r.name))
            .cloned()
            .collect();

        let inductive_names: HashSet<Name> =
            new_inductives.iter().map(|i| i.name.clone()).collect();
        let ctor_names: HashSet<Name> = new_constructors.iter().map(|c| c.name.clone()).collect();
        let recursor_names: HashSet<Name> = new_recursors.iter().map(|r| r.name.clone()).collect();

        let mut new_constants: Vec<ConstantInfo> = env
            .constants()
            .filter(|c| !baseline_consts.contains(&c.name))
            .filter(|c| {
                !inductive_names.contains(&c.name)
                    && !ctor_names.contains(&c.name)
                    && !recursor_names.contains(&c.name)
            })
            .cloned()
            .collect();

        // Sort for deterministic output
        new_inductives.sort_by_key(|a| a.name.to_string());
        new_constructors.sort_by_key(|a| a.name.to_string());
        new_recursors.sort_by_key(|a| a.name.to_string());
        new_constants.sort_by_key(|a| a.name.to_string());

        let mut structure_fields = Vec::new();
        for ind in &new_inductives {
            if let Some(fields) = env.get_structure_field_names(&ind.name) {
                structure_fields.push((ind.name.clone(), fields.to_vec()));
            }
        }

        let mut export_const_names: Vec<String> = Vec::new();
        export_const_names.extend(new_inductives.iter().map(|i| i.name.to_string()));
        export_const_names.extend(new_constructors.iter().map(|c| c.name.to_string()));
        export_const_names.extend(new_recursors.iter().map(|r| r.name.to_string()));
        export_const_names.extend(new_constants.iter().map(|c| c.name.to_string()));
        export_const_names.sort();
        export_const_names.dedup();

        // Create output directory
        let olean_path = self.workspace.olean_path(module)?;
        if let Some(parent) = olean_path.parent() {
            std::fs::create_dir_all(parent)?;
        }

        // Generate .olean file using the exporter
        let imports: Vec<(&str, bool)> = import_names.iter().map(|s| (s.as_str(), false)).collect();
        let const_refs: Vec<&str> = export_const_names.iter().map(String::as_str).collect();

        // The module's `protected` / `private` marks travel with its
        // declarations: without them an importer's `open N; w` reached a
        // protected `N.w`, and a `private` declaration was nameable from
        // every importer (round-25 verification: `protterm_3`,
        // `privshadow2_3` built where Lean 4.8.0 rejects them).
        let exported: HashSet<Name> = new_inductives
            .iter()
            .map(|i| i.name.clone())
            .chain(new_constructors.iter().map(|c| c.name.clone()))
            .chain(new_recursors.iter().map(|r| r.name.clone()))
            .chain(new_constants.iter().map(|c| c.name.clone()))
            .collect();
        let mut protected_decls: Vec<Name> = exported
            .iter()
            .filter(|name| env.is_protected(name))
            .cloned()
            .collect();
        protected_decls.sort_by_key(ToString::to_string);
        let mut private_decls: Vec<Name> = exported
            .iter()
            .filter(|name| env.is_private(name))
            .cloned()
            .collect();
        private_decls.sort_by_key(ToString::to_string);

        // The module's own `@[implemented_by]` / `@[extern]` bindings travel
        // with its declarations (payload version 5): without them a program
        // importing this artifact compiled the logical body where Lean runs
        // the implementation (`docs/DECISIONS.md` R149). Elaboration binds only
        // a declaration of this run, so the module's new names are all there is.
        let own_names = || {
            new_inductives
                .iter()
                .map(|i| &i.name)
                .chain(new_constructors.iter().map(|c| &c.name))
                .chain(new_recursors.iter().map(|r| &r.name))
                .chain(new_constants.iter().map(|c| &c.name))
        };
        let mut implemented_by: Vec<(Name, Name)> = own_names()
            .filter_map(|name| {
                env.get_implemented_by(name)
                    .map(|target| (name.clone(), target.clone()))
            })
            .collect();
        implemented_by.sort_by_key(|(name, _)| name.to_string());
        let mut externs: Vec<(Name, String)> = own_names()
            .filter_map(|name| {
                env.get_extern(name)
                    .map(|symbol| (name.clone(), symbol.clone()))
            })
            .collect();
        externs.sort_by_key(|(name, _)| name.to_string());
        // The module's own constants a late `attribute [implemented_by]`
        // command of the module came too late for: an importer must refuse
        // to compile them as this build's own lanes do (`docs/DECISIONS.md`
        // R149). A row for an imported constant is its own module's, and an
        // importer reads it from that module's payload.
        let own: HashSet<&Name> = own_names().collect();
        let mut implemented_by_order: Vec<(Name, Name, Name)> = env
            .compiled_before_record()
            .into_iter()
            .flatten()
            .filter(|(referrer, _)| own.contains(referrer))
            .map(|(referrer, why)| (referrer.clone(), why.rebound.clone(), why.via.clone()))
            .collect();
        implemented_by_order.sort_by_key(|(referrer, _, _)| referrer.to_string());

        let module_exports = baseline_exports.exports(&env, &global_readds);
        let definition_exposure = clean_kernel::env::exposure::definitions(&env)
            .into_iter()
            .filter(|(name, _)| own.contains(name))
            .collect();
        let payload = clean_olean::CleanPayload {
            constants: new_constants,
            inductives: new_inductives,
            constructors: new_constructors,
            recursors: new_recursors,
            structure_fields,
            protected_decls,
            private_decls,
            classes: module_exports.classes,
            global_instances: module_exports.global_instances,
            scoped_instances: module_exports.scoped_instances,
            export_aliases: module_exports.export_aliases,
            namespaces: module_exports.namespaces,
            implemented_by,
            externs,
            implemented_by_order,
            csimp: clean_kernel::env::csimp::export_compilation_snapshot(&env),
            definition_exposure,
        };

        const CLEAN_GIT_HASH: &str = CLEAN_OLEAN_GIT_HASH;

        // Export all three .olean parts for Lean 4 compatibility:
        // - .olean (exported): constants and public extension entries
        // - .olean.server: server-specific extension entries (LSP metadata)
        // - .olean.private: private implementation extension entries
        //
        // See designs/2026-02-03-olean-parts-support.md for rationale.
        // Source: Lean 4 `writeModule` in Environment.lean:1825-1833

        // Export base .olean (exported level) with all constants
        let olean_bytes = clean_olean::OleanExporter::export_with_payload(
            &imports,
            &const_refs,
            &[], // No exported extension entries for now
            CLEAN_GIT_HASH,
            &payload,
        )
        .map_err(|e| LakeError::BuildFailed {
            module: module.to_string(),
            reason: format!("olean export error: {e}"),
        })?;
        std::fs::write(&olean_path, &olean_bytes)?;

        // Export .olean.server (server level) - empty for now
        // This file will contain LSP-specific extension entries when supported
        let server_path = self.workspace.olean_server_path(module)?;
        let empty_payload = clean_olean::CleanPayload {
            constants: vec![],
            inductives: vec![],
            constructors: vec![],
            recursors: vec![],
            structure_fields: vec![],
            protected_decls: vec![],
            private_decls: vec![],
            ..clean_olean::CleanPayload::default()
        };
        // Incremental companions must occupy distinct pointer ranges, including
        // the complete preceding file's payload/footer and alignment padding.
        let server_bytes = clean_olean::OleanExporter::export_with_payload_after(
            &olean_bytes,
            &imports,
            &[], // No constants in server part
            &[], // No server extension entries for now
            CLEAN_GIT_HASH,
            &empty_payload,
        )
        .map_err(|e| LakeError::BuildFailed {
            module: module.to_string(),
            reason: format!("olean server export error: {e}"),
        })?;
        std::fs::write(&server_path, &server_bytes)?;

        // Export .olean.private (private level) - empty for now
        // This file will contain private implementation extension entries when supported
        let private_path = self.workspace.olean_private_path(module)?;
        let private_bytes = clean_olean::OleanExporter::export_with_payload_after(
            &server_bytes,
            &imports,
            &[], // No constants in private part
            &[], // No private extension entries for now
            CLEAN_GIT_HASH,
            &empty_payload,
        )
        .map_err(|e| LakeError::BuildFailed {
            module: module.to_string(),
            reason: format!("olean private export error: {e}"),
        })?;
        std::fs::write(&private_path, &private_bytes)?;

        // Only now, with the module elaborated, kernel-checked, gated and
        // all three parts written, may its artifact be reused by a later build.
        build_trace::write_trace(&olean_path, &artifact_parts, trace_inputs)?;
        self.forget_digest(&artifact_parts[0]);

        Ok(())
    }

    /// Every module a load call loaded (its summaries' labels, a
    /// companion part's `M._server` / `M._private` counted as `M`) must be
    /// one [`Self::loaded_closure`] walked for `module` — the set admitted
    /// before the load. The walk follows the loader's own rule; a module it
    /// did not see was loaded unexamined, and fails the build closed.
    fn loaded_as_admitted(
        module: &str,
        summaries: &[clean_olean::LoadSummary],
        admitted: &[LoadedImport],
    ) -> LakeResult<()> {
        let labels: HashSet<&str> = summaries
            .iter()
            .filter_map(|s| s.module_name.as_deref())
            .collect();
        for label in &labels {
            let base = ["._server", "._private"]
                .iter()
                .find_map(|suffix| {
                    label
                        .strip_suffix(suffix)
                        .filter(|base| labels.contains(base))
                })
                .unwrap_or(label);
            if !admitted.iter().any(|loaded| loaded.module == base) {
                return Err(LakeError::BuildFailed {
                    module: module.to_string(),
                    reason: format!(
                        "loaded `{base}`, which the import admission did not examine; \
                         nothing is built against it"
                    ),
                });
            }
        }
        Ok(())
    }

    /// Refuse to export a module whose declarations' cited closure does not
    /// re-admit over the build's own base, reaches a trust marker (`sorry`,
    /// `sorryAx`, `trustedArith`, `trustedAy`), or rests on an axiom another
    /// module declared (whatever its name: only the base's own declaration of
    /// a foundational axiom is taken as given). The module's OWN axioms are reported,
    /// not refused: they are in the source being built.
    fn gate_module_closure(
        module: &str,
        env: &clean_kernel::Environment,
        gate: &mut clean_olean::ImportedConeGate,
        baseline_consts: &HashSet<Name>,
    ) -> LakeResult<()> {
        let roots: std::collections::BTreeSet<Name> = env
            .constants()
            .filter(|c| !baseline_consts.contains(&c.name))
            .map(|c| c.name.clone())
            .collect();
        if roots.is_empty() {
            return Ok(());
        }
        let verdict = gate.check(env, &roots);
        if !verdict.passed(false) {
            return Err(LakeError::BuildFailed {
                module: module.to_string(),
                reason: format!(
                    "cited closure not credited: {}",
                    verdict.refusal_summary(false)
                ),
            });
        }
        let own_axioms: Vec<String> = roots
            .iter()
            .filter(|n| {
                // Every own axiom, whatever its name: a citing module accepts
                // an axiom only when its own base holds that very
                // declaration, and a module's own axiom is never in a
                // citer's base.
                env.get_const(n)
                    .is_some_and(|c| c.kind == clean_kernel::ConstantKind::Axiom)
            })
            .map(ToString::to_string)
            .collect();
        if !own_axioms.is_empty() {
            eprintln!(
                "warning: module {module} declares {} axiom(s), which every module citing \
                 them will refuse to credit: {}",
                own_axioms.len(),
                own_axioms.join(", ")
            );
        }
        Ok(())
    }

    /// Elaborate and kernel-check every declaration of `module` into `env`
    /// through the SAME pipeline `clean check` and `clean project check` use
    /// (`preprocess_decl_with_context` + `elaborate_decl_and_register_with_context_and_warning`
    /// over one `FileContext`), and refuse the module on any failure.
    ///
    /// Returns the cited roots of the module's `example`s, which are checked
    /// and then discarded (never registered), so the closure gate can only
    /// reach them through their terms.
    ///
    /// # What this replaced (round-22 verification of `317f48b45`)
    ///
    /// The builder ran its own loop: a fresh `ElabCtx` per top-level
    /// declaration, then a hand-written `commit_elab_result` that registered
    /// single results and answered `Ok(())` for `Multiple` and `Failed`. A
    /// `section` that recovered from an inner failure returned that failure
    /// as a `Failed` leaf inside `Multiple`, so `section S theorem bad : 1 = 2
    /// := rfl end S` printed `Build OK`, exited 0 and wrote the `.olean`
    /// (likewise a `codef … := sorry` inside a section). The same arm silently
    /// dropped every GOOD declaration of a multi-declaration `namespace` or
    /// `section` from the environment, so a sibling citing an earlier sibling
    /// failed with `Unknown identifier` and the artifact never held them.
    fn elaborate_module(
        module: &str,
        surface: &[clean_parser::SurfaceDecl],
        header: &clean_parser::FileHeader,
        env: &mut clean_kernel::Environment,
        options: &[clean_elab::command_line_options::CommandLineOption],
    ) -> LakeResult<(std::collections::BTreeSet<Name>, Vec<Name>)> {
        let fail = |reason: String| LakeError::BuildFailed {
            module: module.to_string(),
            reason,
        };
        let kernel_before = clean_elab::register::kernel_check_failures_on_this_thread();
        let mut file_ctx = clean_elab::FileContext::new();
        file_ctx.set_file_header(header);
        // Exactly a leading `set_option` per override, as `lean -D` applies it.
        clean_elab::command_line_options::apply_command_line_options(env, &mut file_ctx, options);
        // Dependencies were loaded from the workspace's own artifacts above;
        // an `import` must not reach past them to an external `.olean`.
        file_ctx.disable_external_import_search();
        // Lean's main module is the Lake module name, so a `private`
        // declaration is written into the artifact as Lean writes it,
        // `_private.<module>.0.<name>` (G21), the name `clean check` gives it.
        file_ctx.set_main_module(Name::from_string(module));
        let imports: Vec<Name> = surface
            .iter()
            .filter_map(|decl| match decl {
                clean_parser::SurfaceDecl::Import { paths, .. } => Some(paths),
                _ => None,
            })
            .flatten()
            .map(|path| path.name().clone())
            .collect();
        for import in &imports {
            file_ctx.record_compiler_import(import);
        }
        clean_kernel::env::csimp::begin_source_module(env, Name::from_string(module), imports);

        let mut example_roots = std::collections::BTreeSet::new();
        let mut failures: Vec<String> = Vec::new();
        for decl in surface {
            if matches!(decl, clean_parser::SurfaceDecl::Import { .. }) {
                continue;
            }
            let processed = clean_elab::preprocess_decl_with_context(decl, &mut file_ctx);
            match clean_elab::elaborate_decl_and_register_with_context_and_warning(
                env,
                &processed,
                &mut file_ctx,
            ) {
                Ok(registered) => {
                    let mut leaves: Vec<&ElabResult> = Vec::new();
                    registered.result.leaf_decls(&mut leaves);
                    for leaf in leaves {
                        match leaf {
                            ElabResult::Diagnosed { .. } => {
                                if let Some(message) = leaf.source_error_message() {
                                    failures.push(message);
                                }
                            }
                            ElabResult::Failed { name, error, .. } => {
                                failures.push(format!("{name}: {error}"));
                            }
                            ElabResult::Example { .. } => {
                                example_roots.extend(leaf.cited_roots(env));
                            }
                            _ => {}
                        }
                    }
                }
                Err(e) => {
                    use clean_parser::SurfaceDecl as D;
                    let name = match decl {
                        D::Def { name, .. }
                        | D::Theorem { name, .. }
                        | D::Axiom { name, .. }
                        | D::Opaque { name, .. }
                        | D::Inductive { name, .. }
                        | D::Structure { name, .. }
                        | D::Class { name, .. }
                        | D::Namespace { name, .. } => format!("{name}: "),
                        _ => String::new(),
                    };
                    failures.push(format!("{name}{e}"));
                }
            }
        }
        if !failures.is_empty() {
            return Err(fail(format!(
                "elaboration error: {} declaration(s) failed: {}",
                failures.len(),
                failures.join("; ")
            )));
        }
        let kernel_delta = clean_elab::register::kernel_check_failures_on_this_thread()
            .saturating_sub(kernel_before);
        if kernel_delta > 0 {
            // No declaration row accounts for it, and a module whose kernel
            // recorded a failed check is not a built module.
            return Err(fail(format!(
                "the kernel recorded {kernel_delta} failed check(s) that no declaration reported"
            )));
        }
        Ok((example_roots, file_ctx.instance_global_readds()))
    }

    /// The `-D` overrides in the `lean` arguments Lake compiles `module` with
    /// ([`Workspace::module_lean_args`]), validated with pinned Lean's `-D`
    /// rules: an option Lean would refuse fails the module, as `lean` would.
    /// An argument that is not a `-D` changes nothing Clean elaborates; it is
    /// named on stderr rather than dropped in silence.
    fn module_lean_options(
        &self,
        module: &str,
    ) -> LakeResult<Vec<clean_elab::command_line_options::CommandLineOption>> {
        let fail = |reason: String| LakeError::BuildFailed {
            module: module.to_string(),
            reason,
        };
        let args = self
            .workspace
            .module_lean_args(module)
            .map_err(|e| fail(e.to_string()))?;
        let parsed =
            clean_elab::command_line_options::options_from_lean_args(&args).map_err(|e| {
                fail(format!(
                    "lakefile leanOptions/moreLeanArgs/weakLeanArgs: {e}"
                ))
            })?;
        for option in parsed.options.iter().filter(|o| !o.is_applied()) {
            eprintln!(
                "warning: {module}: lakefile option `-D{}` is a Lean option Clean does not \
                 implement; it cannot change which declarations are accepted (or is Lean's \
                 default), so it was not applied",
                option.to_arg()
            );
        }
        for arg in &parsed.not_applied {
            eprintln!(
                "warning: {module}: `lean` argument `{arg}` from the lakefile has no meaning \
                 to Clean's elaborator and was not applied"
            );
        }
        Ok(parsed.options)
    }

    /// Run the closure gate over the module's `example`s. They are checked and
    /// discarded, so [`Self::gate_module_closure`] (which walks the
    /// environment's new constants) never sees them: `example : 1 = 2 :=
    /// sorry` must not build.
    fn gate_module_examples(
        module: &str,
        env: &clean_kernel::Environment,
        gate: &mut clean_olean::ImportedConeGate,
        roots: &std::collections::BTreeSet<Name>,
    ) -> LakeResult<()> {
        if roots.is_empty() {
            return Ok(());
        }
        let verdict = gate.check(env, roots);
        if verdict.passed(false) {
            return Ok(());
        }
        Err(LakeError::BuildFailed {
            module: module.to_string(),
            reason: format!(
                "an example's cited closure is not credited: {}",
                verdict.refusal_summary(false)
            ),
        })
    }

    /// clean build artifacts
    pub fn clean(&self) -> LakeResult<()> {
        let build_dir = self.workspace.build_dir();
        if build_dir.exists() {
            std::fs::remove_dir_all(&build_dir)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;

    /// A build context over an EMPTY workspace: it provides no modules, so
    /// [`BuildContext::is_stdlib_import`] reduces to the bare name-prefix test.
    fn empty_ctx(tmp: &TempDir) -> BuildContext {
        BuildContext::new(Workspace::new(tmp.path(), "test"))
    }

    #[test]
    fn invalid_module_output_identity_cannot_be_counted_as_fresh_or_skipped() {
        let tmp = TempDir::new().unwrap();
        for force in [false, true] {
            for module in ["7", ".ctor", "A..B", "«../Outside»"] {
                let context = empty_ctx(&tmp).with_options(BuildOptions::new().with_force(force));
                let (built, skipped, failed) = context.build_modules(&[module.to_owned()]);
                assert!(built.is_empty(), "{module}");
                assert!(skipped.is_empty(), "{module}");
                assert_eq!(failed.len(), 1, "{module}");
                assert_eq!(failed[0].0, module);
                assert!(
                    failed[0].1.contains("invalid configuration"),
                    "{:?}",
                    failed
                );
            }
        }
        std::fs::write(tmp.path().join("A.B.lean"), "").unwrap();
        let ws = Workspace::new(tmp.path(), "test");
        assert!(ws.needs_rebuild("«A.B»").unwrap());
        assert!(
            ws.needs_rebuild("A.B").is_err(),
            "different module is missing"
        );
    }

    #[test]
    fn test_extract_imports() {
        let tmp = TempDir::new().unwrap();
        let content = r"
import MyLib.Core
import MyLib.Utils
-- import Commented

open MyLib

def foo := 1
";
        let imports = empty_ctx(&tmp).extract_imports(content).expect("header");
        assert_eq!(imports, vec!["MyLib.Core", "MyLib.Utils"]);
    }

    #[test]
    fn test_extract_imports_uses_header_grammar() {
        let content = "module\n/- import NotAnImport -/\npublic import PublicDep\nmeta import MetaDep\nimport all PrivateDep\nimport\n  MultilineDep\ndef x := 0\n-- import AlsoNotAnImport\n";
        assert_eq!(
            BuildContext::extract_all_imports(content).expect("header"),
            vec!["PublicDep", "MetaDep", "PrivateDep", "MultilineDep"]
        );
        assert!(BuildContext::extract_all_imports("public import MissingModuleHeader").is_err());
    }

    #[test]
    fn test_extract_imports_filters_stdlib() {
        let tmp = TempDir::new().unwrap();
        let content = r"
import Init.Core
import Std.Data.List
import Lean.Elab
import MyProject.Core
";
        let imports = empty_ctx(&tmp).extract_imports(content).expect("header");
        assert_eq!(imports, vec!["MyProject.Core"]);
    }

    #[test]
    fn test_extract_imports_keeps_workspace_provided_stdlib_names() {
        // A module the workspace itself provides is LOCAL, whatever its name:
        // `Std.Mine` is kept as a build dependency while its unprovided
        // sibling `Std.Data.List` still routes to the toolchain.
        let tmp = TempDir::new().unwrap();
        std::fs::write(
            tmp.path().join("lakefile.toml"),
            "name = \"stdshadow\"\n\n[[lean_lib]]\nname = \"Std\"\n",
        )
        .unwrap();
        std::fs::create_dir_all(tmp.path().join("Std")).unwrap();
        std::fs::write(tmp.path().join("Std/Mine.lean"), "def mineVal : Nat := 4\n").unwrap();

        let ws = Workspace::load(tmp.path()).expect("workspace loads");
        let ctx = BuildContext::new(ws);
        assert!(
            !ctx.is_stdlib_import("Std.Mine"),
            "a workspace-provided module is never a stdlib import"
        );
        assert!(
            ctx.is_stdlib_import("Std.Data.List"),
            "an unprovided module still routes to the toolchain"
        );

        let imports = ctx
            .extract_imports("import Std.Mine\nimport Std.Data.List\n")
            .expect("header");
        assert_eq!(imports, vec!["Std.Mine"]);
    }

    #[test]
    fn test_topological_sort() {
        let tmp = TempDir::new().unwrap();
        let ws = Workspace::new(tmp.path(), "test");
        let mut ctx = BuildContext::new(ws);

        ctx.deps.insert("A".to_string(), vec!["B".to_string()]);
        ctx.deps.insert("B".to_string(), vec!["C".to_string()]);
        ctx.deps.insert("C".to_string(), vec![]);

        let sorted = ctx.topological_sort().unwrap();
        assert_eq!(sorted, vec!["C", "B", "A"]);
    }

    #[test]
    fn test_topological_sort_cycle_detection() {
        let tmp = TempDir::new().unwrap();
        let ws = Workspace::new(tmp.path(), "test");
        let mut ctx = BuildContext::new(ws);

        ctx.deps.insert("A".to_string(), vec!["B".to_string()]);
        ctx.deps.insert("B".to_string(), vec!["A".to_string()]);

        let result = ctx.topological_sort();
        assert!(
            matches!(result, Err(LakeError::CircularDependency(_))),
            "expected CircularDependency, got: {result:?}"
        );
    }

    #[test]
    fn test_build_options_default() {
        let opts = BuildOptions::default();
        assert_eq!(opts.jobs, 0);
        assert!(!opts.verbose);
        assert!(!opts.force);
    }

    #[test]
    fn test_build_result_success() {
        let result = BuildResult {
            built: vec!["A".to_string()],
            skipped: vec!["B".to_string()],
            failed: vec![],
            disclosures: vec![],
            duration: Duration::from_secs(1),
        };
        assert!(result.is_success());
        assert_eq!(result.total(), 2);
    }

    #[test]
    fn test_build_result_failure() {
        let result = BuildResult {
            built: vec!["A".to_string()],
            skipped: vec![],
            failed: vec![("B".to_string(), "error".to_string())],
            disclosures: vec![],
            duration: Duration::from_secs(1),
        };
        assert!(!result.is_success());
    }

    #[test]
    fn test_compute_build_levels() {
        let tmp = TempDir::new().unwrap();
        let ws = Workspace::new(tmp.path(), "test");
        let mut ctx = BuildContext::new(ws);

        // A depends on B, B depends on C, D is independent
        ctx.deps.insert("A".to_string(), vec!["B".to_string()]);
        ctx.deps.insert("B".to_string(), vec!["C".to_string()]);
        ctx.deps.insert("C".to_string(), vec![]);
        ctx.deps.insert("D".to_string(), vec![]);

        let modules = vec![
            "A".to_string(),
            "B".to_string(),
            "C".to_string(),
            "D".to_string(),
        ];
        let levels = ctx.compute_build_levels(&modules);

        // Level 0: C, D (no deps)
        // Level 1: B (depends on C)
        // Level 2: A (depends on B)
        assert_eq!(levels.len(), 3);
        assert!(levels[0].contains(&"C".to_string()));
        assert!(levels[0].contains(&"D".to_string()));
        assert_eq!(levels[1], vec!["B"]);
        assert_eq!(levels[2], vec!["A"]);
    }

    #[test]
    fn test_compute_build_levels_parallel() {
        let tmp = TempDir::new().unwrap();
        let ws = Workspace::new(tmp.path(), "test");
        let mut ctx = BuildContext::new(ws);

        // A, B, C all depend on D - they can all build in parallel after D
        ctx.deps.insert("A".to_string(), vec!["D".to_string()]);
        ctx.deps.insert("B".to_string(), vec!["D".to_string()]);
        ctx.deps.insert("C".to_string(), vec!["D".to_string()]);
        ctx.deps.insert("D".to_string(), vec![]);

        let modules = vec![
            "A".to_string(),
            "B".to_string(),
            "C".to_string(),
            "D".to_string(),
        ];
        let levels = ctx.compute_build_levels(&modules);

        // Level 0: D
        // Level 1: A, B, C (all can build in parallel)
        assert_eq!(levels.len(), 2);
        assert_eq!(levels[0], vec!["D"]);
        assert_eq!(levels[1].len(), 3);
        assert!(levels[1].contains(&"A".to_string()));
        assert!(levels[1].contains(&"B".to_string()));
        assert!(levels[1].contains(&"C".to_string()));
    }

    /// Two-hop transitive closure through module imports: the root proves a
    /// value BY RFL through both hops, which is exactly what the single-olean
    /// dep loading missed (A held B's constants but never C's, so the rfl was
    /// defeq-stuck while the build reported success — the 2026-08-21 Lake
    /// pillar audit's wrong-build repro, mechanized).
    #[test]
    fn test_build_transitive_dep_closure_rfl() {
        use std::fs;
        use std::io::Write;

        let tmp = TempDir::new().unwrap();
        let mut lakefile = fs::File::create(tmp.path().join("lakefile.lean")).unwrap();
        writeln!(
            lakefile,
            r#"
package chain where
  name := "chain"
  version := "0.1.0"

lean_lib Chain where
  roots := #[`Chain]
"#
        )
        .unwrap();

        fs::create_dir_all(tmp.path().join("Chain")).unwrap();
        let mut c = fs::File::create(tmp.path().join("Chain/C.lean")).unwrap();
        writeln!(c, "def cVal : Nat := 5").unwrap();
        let mut b = fs::File::create(tmp.path().join("Chain/B.lean")).unwrap();
        writeln!(
            b,
            "import Chain.C
def bVal : Nat := cVal"
        )
        .unwrap();
        let mut a = fs::File::create(tmp.path().join("Chain/A.lean")).unwrap();
        writeln!(
            a,
            "import Chain.B
def aVal : Nat := bVal
theorem a_eq : aVal = 5 := rfl"
        )
        .unwrap();

        let ws = Workspace::load(tmp.path()).unwrap();
        let mut ctx = BuildContext::new(ws).with_options(BuildOptions {
            verbose: true,
            ..BuildOptions::default()
        });
        let report = ctx.build_all().expect("two-hop chain should build");
        assert!(
            report.failed.is_empty(),
            "the rfl through BOTH hops must kernel-verify (closure loading): {:?}",
            report.failed
        );
        assert_eq!(report.built.len(), 3, "all three chain modules build");
    }

    #[test]
    fn test_build_with_dependencies() {
        use std::fs;
        use std::io::Write;

        let tmp = TempDir::new().unwrap();

        // Create lakefile.lean
        let mut lakefile = fs::File::create(tmp.path().join("lakefile.lean")).unwrap();
        writeln!(
            lakefile,
            r#"
package myproject where
  name := "myproject"
  version := "0.1.0"

lean_lib MyProject where
  roots := #[`MyProject]
"#
        )
        .unwrap();

        // Create source directory
        fs::create_dir_all(tmp.path().join("MyProject")).unwrap();

        // Create Core.lean (no dependencies, minimal valid Lean file)
        let mut core = fs::File::create(tmp.path().join("MyProject/Core.lean")).unwrap();
        writeln!(core, "def baseVal : Type 1 := Type").unwrap();

        // Create Main.lean (depends on Core)
        let mut main = fs::File::create(tmp.path().join("MyProject/Main.lean")).unwrap();
        writeln!(
            main,
            r"import MyProject.Core
def mainVal : Type 1 := baseVal"
        )
        .unwrap();

        // Build the project
        let ws = Workspace::load(tmp.path()).unwrap();
        let mut ctx = BuildContext::new(ws).with_options(BuildOptions {
            verbose: true,
            ..Default::default()
        });

        let result = ctx.build_all();

        // The build should succeed
        assert!(result.is_ok(), "Build should succeed: {:?}", result.err());

        let build_result = result.unwrap();
        println!("Built: {:?}", build_result.built);
        println!("Failed: {:?}", build_result.failed);

        // Both modules should be built successfully
        assert!(
            build_result.built.contains(&"MyProject.Core".to_string()),
            "Core should be built"
        );
        assert!(
            build_result.built.contains(&"MyProject.Main".to_string()),
            "Main should be built"
        );
        assert!(
            build_result.failed.is_empty(),
            "No modules should fail: {:?}",
            build_result.failed
        );

        // Verify .olean files were created
        let lib_dir = tmp.path().join(".lake/build/lib");
        assert!(
            lib_dir.join("MyProject/Core.olean").exists(),
            "Core.olean should exist"
        );
        assert!(
            lib_dir.join("MyProject/Main.olean").exists(),
            "Main.olean should exist"
        );

        // Verify payload-backed .olean files can be loaded with dependencies
        let mut load_env = clean_kernel::Environment::new();
        let load_paths = vec![lib_dir.clone()];
        let summaries =
            clean_olean::load_module_with_deps(&mut load_env, "MyProject.Main", &load_paths)
                .expect("load with deps");
        assert!(
            !summaries.is_empty(),
            "expected load summaries from dependency chain"
        );
        let base = Name::from_string("baseVal");
        let main_const = Name::from_string("mainVal");
        assert!(
            load_env.get_const(&base).is_some(),
            "baseVal should be loaded from payload"
        );
        assert!(
            load_env.get_const(&main_const).is_some(),
            "mainVal should be loaded from payload"
        );
    }

    /// Write a two-module project whose `Main` imports `Core`, and return its
    /// temp dir. Used by the check-only tests below.
    fn write_two_module_project() -> TempDir {
        use std::fs;

        let tmp = TempDir::new().expect("tempdir");
        fs::write(
            tmp.path().join("lakefile.lean"),
            "package myproject\n\nlean_lib MyProject where\n  roots := #[`MyProject]\n",
        )
        .expect("write lakefile");
        fs::create_dir_all(tmp.path().join("MyProject")).expect("create src dir");
        fs::write(
            tmp.path().join("MyProject/Core.lean"),
            "def baseVal : Type 1 := Type\n",
        )
        .expect("write Core");
        fs::write(
            tmp.path().join("MyProject/Main.lean"),
            "import MyProject.Core\ndef mainVal : Type 1 := baseVal\n",
        )
        .expect("write Main");
        tmp
    }

    /// Back-date a file so the freshness check reads it as older than any
    /// artifact built from it.
    fn back_date(path: &std::path::Path) {
        let old = std::time::UNIX_EPOCH + Duration::from_secs(1_000_000);
        let file = std::fs::File::options()
            .write(true)
            .open(path)
            .expect("open for set_times");
        file.set_times(
            std::fs::FileTimes::new()
                .set_accessed(old)
                .set_modified(old),
        )
        .expect("set_times");
    }

    /// A check-only build writes NOTHING into the project — and still
    /// resolves the import chain, because its modules' `.olean` files land in
    /// the scratch directory the same run created.
    #[test]
    fn test_check_only_build_leaves_no_artifacts_but_still_resolves_imports() {
        let tmp = write_two_module_project();
        let ws = Workspace::load(tmp.path()).expect("workspace loads");
        let mut ctx = BuildContext::new(ws).with_options(BuildOptions {
            check_only: true,
            ..Default::default()
        });

        let result = ctx.build_all().expect("check-only build should run");
        assert!(
            result.failed.is_empty(),
            "the import chain must still resolve under check_only: {:?}",
            result.failed
        );
        assert_eq!(
            result.built.len(),
            2,
            "both modules are checked, not skipped: {result:?}"
        );

        assert!(
            !tmp.path().join(".lake/build").exists(),
            "a check-only build must leave the project's build directory alone; found {:?}",
            std::fs::read_dir(tmp.path().join(".lake/build")).map(|d| d
                .filter_map(Result::ok)
                .map(|e| e.path())
                .collect::<Vec<_>>())
        );
        // `Workspace::load` canonicalizes its root, so compare against the
        // workspace's own root rather than the raw temp path.
        assert_eq!(
            ctx.workspace().build_dir(),
            ctx.workspace().root().join(".lake/build"),
            "the workspace's build directory is restored when the check returns"
        );
    }

    /// A check-only build must never inherit a verdict from an artifact.
    ///
    /// Measured 2026-08-27 while `check_only` was inert: `clean lake
    /// check-build` printed "Build check passed." for a project whose source
    /// no longer compiled, because every module was skipped against a newer
    /// `.olean`. The ordinary build below used to be the CONTROL that still
    /// skipped and reported success; since build traces (T7a2, 2026-09-26) it
    /// reuses nothing whose trace does not match, so it reports the break
    /// too.
    #[test]
    fn test_check_only_build_does_not_inherit_a_pass_from_stale_artifacts() {
        let tmp = write_two_module_project();

        // Build once, so both artifacts exist and are newer than the sources.
        let ws = Workspace::load(tmp.path()).expect("workspace loads");
        let mut ctx = BuildContext::new(ws);
        let first = ctx.build_all().expect("initial build");
        assert!(first.failed.is_empty(), "setup build: {:?}", first.failed);

        // Break `Main` at the source level: `baseVal` is gone from `Core`.
        // Back-date both sources so the freshness check sees them as stale.
        let core = tmp.path().join("MyProject/Core.lean");
        std::fs::write(&core, "def renamedVal : Type 1 := Type\n").expect("rewrite Core");
        back_date(&core);
        back_date(&tmp.path().join("MyProject/Main.lean"));

        // The ordinary build no longer credits the back-dated artifacts: the
        // source of `Core` differs from the one its trace records, so `Core`
        // is rebuilt, and `Main` then no longer elaborates.
        let ws = Workspace::load(tmp.path()).expect("workspace loads");
        let mut ctx = BuildContext::new(ws);
        let ordinary = ctx.build_all().expect("ordinary build");
        assert!(
            ordinary.skipped.is_empty()
                && ordinary
                    .failed
                    .iter()
                    .any(|(module, _)| module == "MyProject.Main"),
            "the ordinary build must rebuild and report the break, got {ordinary:?}"
        );

        // The check must fail: `Main` no longer elaborates against `Core`.
        let ws = Workspace::load(tmp.path()).expect("workspace loads");
        let mut ctx = BuildContext::new(ws).with_options(BuildOptions {
            check_only: true,
            ..Default::default()
        });
        let checked = ctx.build_all().expect("check-only build should run");
        assert!(
            checked
                .failed
                .iter()
                .any(|(module, _)| module == "MyProject.Main"),
            "check_only must re-elaborate from source and report the break, got {checked:?}"
        );

        // And it still must not have touched the project's artifacts.
        let core_olean = tmp.path().join(".lake/build/lib/MyProject/Core.olean");
        assert!(
            core_olean.exists(),
            "the pre-existing artifact must survive a check-only build"
        );
    }

    #[test]
    fn test_build_dependency_loading_verbose() {
        use std::fs;
        use std::io::Write;

        let tmp = TempDir::new().unwrap();

        // Create lakefile.lean
        let mut lakefile = fs::File::create(tmp.path().join("lakefile.lean")).unwrap();
        writeln!(
            lakefile,
            r#"
package deptest where
  name := "deptest"
  version := "0.1.0"

lean_lib DepTest where
  roots := #[`DepTest]
"#
        )
        .unwrap();

        // Create source directory
        fs::create_dir_all(tmp.path().join("DepTest")).unwrap();

        // Create Base.lean (minimal valid Lean file)
        let mut base = fs::File::create(tmp.path().join("DepTest/Base.lean")).unwrap();
        writeln!(base, "def baseVal : Type 1 := Type").unwrap();

        // Create Mid.lean (depends on Base)
        let mut mid = fs::File::create(tmp.path().join("DepTest/Mid.lean")).unwrap();
        writeln!(mid, "import DepTest.Base\ndef midVal : Type 1 := baseVal").unwrap();

        // Create Top.lean (depends on Mid)
        let mut top = fs::File::create(tmp.path().join("DepTest/Top.lean")).unwrap();
        writeln!(top, "import DepTest.Mid\ndef topVal : Type 1 := midVal").unwrap();

        // Build with verbose output
        let ws = Workspace::load(tmp.path()).unwrap();
        let mut ctx = BuildContext::new(ws).with_options(BuildOptions {
            verbose: true,
            ..Default::default()
        });

        let result = ctx.build_all().unwrap();

        println!("Built: {:?}", result.built);
        println!("Failed: {:?}", result.failed);

        // All three modules should be built in correct order
        assert!(result.built.contains(&"DepTest.Base".to_string()));
        assert!(result.built.contains(&"DepTest.Mid".to_string()));
        assert!(result.built.contains(&"DepTest.Top".to_string()));
        assert!(result.failed.is_empty());

        // Verify build order: Base must come before Mid, Mid before Top
        let base_idx = result.built.iter().position(|m| m == "DepTest.Base");
        let mid_idx = result.built.iter().position(|m| m == "DepTest.Mid");
        let top_idx = result.built.iter().position(|m| m == "DepTest.Top");

        // Due to parallel build, we can't guarantee exact order, but all should be present
        assert!(
            base_idx.is_some(),
            "DepTest.Base should be in built modules"
        );
        assert!(mid_idx.is_some(), "DepTest.Mid should be in built modules");
        assert!(top_idx.is_some(), "DepTest.Top should be in built modules");

        // Validate that loading Top pulls in dependency constants via payloads
        let mut env = clean_kernel::Environment::new();
        let lib_dir = tmp.path().join(".lake/build/lib");
        let _ = clean_olean::load_module_with_deps(&mut env, "DepTest.Top", &[lib_dir])
            .expect("load top with deps");
        for name in ["baseVal", "midVal", "topVal"] {
            let n = Name::from_string(name);
            assert!(
                env.get_const(&n).is_some(),
                "{name} should be available after loading payload olean"
            );
        }
    }

    /// Fixture: a project whose single module imports a stdlib module that
    /// cannot exist in any toolchain's search paths.
    fn stdlib_import_project() -> TempDir {
        use std::fs;
        use std::io::Write;

        let tmp = TempDir::new().unwrap();

        let mut lakefile = fs::File::create(tmp.path().join("lakefile.lean")).unwrap();
        writeln!(
            lakefile,
            r#"
package stdfail where
  name := "stdfail"
  version := "0.1.0"

lean_lib StdFail where
  roots := #[`StdFail]
"#
        )
        .unwrap();

        fs::create_dir_all(tmp.path().join("StdFail")).unwrap();
        fs::write(
            tmp.path().join("StdFail/Uses.lean"),
            "import Init.NoSuchCleanLakeModule\ndef usesVal : Type 1 := Type\n",
        )
        .unwrap();

        tmp
    }

    #[test]
    fn test_build_missing_stdlib_import_fails_closed_by_default() {
        let tmp = stdlib_import_project();
        let ws = Workspace::load(tmp.path()).unwrap();
        let mut ctx = BuildContext::new(ws);

        let result = ctx.build_all().expect("build_all should return a result");

        assert!(
            result.built.is_empty(),
            "no module may 'build' against a silently incomplete environment: {:?}",
            result.built
        );
        assert_eq!(
            result.failed.len(),
            1,
            "expected exactly one failed module: {:?}",
            result.failed
        );
        let (module, reason) = &result.failed[0];
        assert_eq!(module, "StdFail.Uses");
        assert!(
            reason.contains("Init.NoSuchCleanLakeModule"),
            "failure must name the missing import: {reason}"
        );
        assert!(
            reason.contains("--permissive-imports"),
            "failure must name the opt-out flag: {reason}"
        );
    }

    #[test]
    fn test_build_missing_stdlib_import_permissive_warns_and_continues() {
        let tmp = stdlib_import_project();
        let ws = Workspace::load(tmp.path()).unwrap();
        let mut ctx = BuildContext::new(ws).with_options(BuildOptions {
            permissive_imports: true,
            ..Default::default()
        });

        let result = ctx.build_all().expect("build_all should return a result");

        assert!(
            result.failed.is_empty(),
            "permissive mode must warn and continue: {:?}",
            result.failed
        );
        assert!(
            result.built.contains(&"StdFail.Uses".to_string()),
            "module should still build under --permissive-imports: {:?}",
            result.built
        );
    }

    /// Fixture: two-module project where Top imports Base but does not use its
    /// constants, built once so both .olean artifacts exist, then Base.olean is
    /// corrupted and Top.olean removed so only Top rebuilds against the corrupt
    /// dependency artifact.
    fn corrupt_dep_project() -> TempDir {
        use std::fs;
        use std::io::Write;

        let tmp = TempDir::new().unwrap();

        let mut lakefile = fs::File::create(tmp.path().join("lakefile.lean")).unwrap();
        writeln!(
            lakefile,
            r#"
package depfail where
  name := "depfail"
  version := "0.1.0"

lean_lib DepFail where
  roots := #[`DepFail]
"#
        )
        .unwrap();

        fs::create_dir_all(tmp.path().join("DepFail")).unwrap();
        fs::write(
            tmp.path().join("DepFail/Base.lean"),
            "def baseVal : Type 1 := Type\n",
        )
        .unwrap();
        fs::write(
            tmp.path().join("DepFail/Top.lean"),
            "import DepFail.Base\ndef topVal : Type 1 := Type\n",
        )
        .unwrap();

        let ws = Workspace::load(tmp.path()).unwrap();
        let mut ctx = BuildContext::new(ws);
        let first = ctx.build_all().expect("initial build should run");
        assert!(
            first.failed.is_empty(),
            "initial build should succeed: {:?}",
            first.failed
        );

        // Corrupt the dependency artifact and drop Top's artifact so only Top
        // rebuilds.
        let lib_dir = tmp.path().join(".lake/build/lib");
        fs::write(lib_dir.join("DepFail/Base.olean"), b"not an olean").unwrap();
        fs::remove_file(lib_dir.join("DepFail/Top.olean")).unwrap();
        // This fixture exercises the LOADER's fail-closed path for a
        // dependency artifact the build reuses but cannot load. Since build
        // traces, a rewritten artifact is rebuilt from source instead of
        // reused, so the only state that still reaches the loader is a trace
        // naming the corrupt bytes themselves (a trace is a cache key, not a
        // certificate): re-stamp Base's trace over them.
        let base_olean = lib_dir.join("DepFail/Base.olean");
        let trace = build_trace::trace_path(&base_olean);
        let mut recorded: serde_json::Value =
            serde_json::from_slice(&fs::read(&trace).unwrap()).unwrap();
        recorded["outputs"] = build_trace::digest_artifact_parts(&[
            base_olean.clone(),
            base_olean.with_extension("olean.server"),
            base_olean.with_extension("olean.private"),
        ])
        .unwrap()
        .into();
        fs::write(&trace, serde_json::to_vec(&recorded).unwrap()).unwrap();

        tmp
    }

    #[test]
    fn test_build_corrupt_dependency_olean_fails_closed_by_default() {
        let tmp = corrupt_dep_project();
        let ws = Workspace::load(tmp.path()).unwrap();
        let mut ctx = BuildContext::new(ws);

        let result = ctx.build_all().expect("build_all should return a result");

        assert_eq!(
            result.failed.len(),
            1,
            "expected exactly one failed module: {:?}",
            result.failed
        );
        let (module, reason) = &result.failed[0];
        assert_eq!(module, "DepFail.Top");
        assert!(
            reason.contains("DepFail.Base"),
            "failure must name the unloadable dependency: {reason}"
        );
        assert!(
            reason.contains("--permissive-imports"),
            "failure must name the opt-out flag: {reason}"
        );
    }

    #[test]
    fn test_build_corrupt_dependency_olean_permissive_continues() {
        let tmp = corrupt_dep_project();
        let ws = Workspace::load(tmp.path()).unwrap();
        let mut ctx = BuildContext::new(ws).with_options(BuildOptions {
            permissive_imports: true,
            ..Default::default()
        });

        let result = ctx.build_all().expect("build_all should return a result");

        assert!(
            result.failed.is_empty(),
            "permissive mode must warn and continue past the corrupt dep: {:?}",
            result.failed
        );
        assert!(
            result.built.contains(&"DepFail.Top".to_string()),
            "Top should still build under --permissive-imports: {:?}",
            result.built
        );
    }
}

#[cfg(test)]
#[path = "build_admission_tests.rs"]
mod admission_tests;

#[cfg(test)]
#[path = "build_block_tests.rs"]
mod block_tests;

#[cfg(test)]
#[path = "build_options_tests.rs"]
mod options_tests;

/// The environment's class, instance, alias and namespace tables before a
/// module is elaborated, to read off what the module EXPORTS of them (the
/// payload's version-3 fields). Lean exports a module's entries of
/// `classExtension`, `instanceExtension` (global and scoped entries; never a
/// local one or an erasure), `aliasExtension` and `namespacesExt`.
struct ModuleExportBaseline {
    classes: HashSet<Name>,
    /// Instances with a global entry.
    global_instances: HashSet<Name>,
    scoped_entries: usize,
    export_aliases: HashSet<(Name, Name)>,
    namespaces: HashSet<Name>,
}

/// What a module exports of those tables.
struct ModuleExports {
    classes: Vec<clean_kernel::env::KernelClassInfo>,
    global_instances: Vec<clean_kernel::env::KernelInstanceInfo>,
    scoped_instances: Vec<(Name, clean_kernel::env::KernelInstanceInfo)>,
    export_aliases: Vec<(Name, Name)>,
    namespaces: Vec<Name>,
}

impl ModuleExportBaseline {
    fn take(env: &clean_kernel::Environment) -> Self {
        Self {
            classes: env.classes().map(|c| c.name.clone()).collect(),
            global_instances: env
                .instances()
                .filter(|info| clean_olean::has_global_instance_entry(env, &info.name))
                .map(|info| info.name.clone())
                .collect(),
            scoped_entries: env
                .get_ext_state::<clean_olean::ScopedInstanceState>(
                    clean_olean::scoped_instance_idx(),
                )
                .map_or(0, |state| state.entries.len()),
            export_aliases: env
                .export_alias_pairs()
                .map(|(alias, target)| (alias.clone(), target.clone()))
                .collect(),
            namespaces: env.registered_namespaces().cloned().collect(),
        }
    }

    /// The module's exports: `env` after it, `global_readds` the instances it
    /// gave a global entry that already had one
    /// (`FileContext::instance_global_readds`).
    ///
    /// The global instance entries are exported by their effect on an
    /// importer's replay, which inserts each entry IN PLACE when it holds the
    /// instance and PUSHES it otherwise (`DiscrTree.insertVal`): every
    /// instance that gained its first global entry here, in the order it
    /// gained it (its position in the environment's index), then every
    /// instance re-inserted here, each at its final priority.
    fn exports(&self, env: &clean_kernel::Environment, global_readds: &[Name]) -> ModuleExports {
        let mut classes: Vec<clean_kernel::env::KernelClassInfo> = env
            .classes()
            .filter(|class| !self.classes.contains(&class.name))
            .cloned()
            .collect();
        classes.sort_by_key(|class| class.name.to_string());

        let mut pushed: Vec<(u64, clean_kernel::env::KernelInstanceInfo)> = env
            .instances()
            .filter(|info| {
                !self.global_instances.contains(&info.name)
                    && clean_olean::has_global_instance_entry(env, &info.name)
            })
            .map(|info| (env.instance_seq(&info.name).unwrap_or(0), info.clone()))
            .collect();
        pushed.sort_by_key(|(seq, _)| *seq);
        let mut global_instances: Vec<clean_kernel::env::KernelInstanceInfo> =
            pushed.into_iter().map(|(_, info)| info).collect();
        let mut readded: HashSet<&Name> = HashSet::new();
        for name in global_readds {
            if !readded.insert(name) || !self.global_instances.contains(name) {
                continue;
            }
            if let Some(info) = env.instances().find(|info| &info.name == name) {
                global_instances.push(info.clone());
            }
        }

        let scoped_instances = env
            .get_ext_state::<clean_olean::ScopedInstanceState>(clean_olean::scoped_instance_idx())
            .map(|state| {
                state
                    .entries
                    .iter()
                    .skip(self.scoped_entries)
                    .filter_map(|(ns, name, priority)| {
                        let mut info = env.instances().find(|info| &info.name == name)?.clone();
                        info.priority = *priority;
                        Some((ns.clone(), info))
                    })
                    .collect()
            })
            .unwrap_or_default();

        let mut export_aliases: Vec<(Name, Name)> = env
            .export_alias_pairs()
            .map(|(alias, target)| (alias.clone(), target.clone()))
            .filter(|pair| !self.export_aliases.contains(pair))
            .collect();
        export_aliases.sort_by_key(|(alias, target)| (alias.to_string(), target.to_string()));

        let mut namespaces: Vec<Name> = env
            .registered_namespaces()
            .filter(|ns| !self.namespaces.contains(*ns))
            .cloned()
            .collect();
        namespaces.sort_by_key(ToString::to_string);

        ModuleExports {
            classes,
            global_instances,
            scoped_instances,
            export_aliases,
            namespaces,
        }
    }
}

#[cfg(test)]
mod import_resource_tests {
    use super::BuildContext;
    use clean_olean::ImportError;

    #[test]
    fn stopped_imports_cannot_continue_in_permissive_mode() {
        let absent = ImportError::ModuleNotFound {
            module: "Missing".to_owned(),
            searched: vec![],
        };
        assert!(BuildContext::import_allows_fallback(&absent));
        assert!(BuildContext::import_failure_hint(&absent).contains("--permissive-imports"));
        for error in [
            ImportError::Interrupted,
            ImportError::ResourceLimit {
                operation: "structure-field validation".to_owned(),
                reason: "declaration budget exhausted".to_owned(),
            },
        ] {
            assert!(!BuildContext::import_allows_fallback(&error));
            assert!(!BuildContext::import_failure_hint(&error).contains("--permissive-imports"));
        }
    }
}
