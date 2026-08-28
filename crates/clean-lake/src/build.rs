// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lake build system
//!
//! Provides incremental compilation and parallel builds.

use crate::error::{LakeError, LakeResult};
use crate::workspace::Workspace;
use clean_elab::ElabResult;
use clean_kernel::env::{ConstantInfo, Declaration};
use clean_kernel::inductive::{
    Constructor, ConstructorVal, InductiveDecl, InductiveType, InductiveVal, RecursorVal,
};
use clean_kernel::name::Name;
use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

/// Result of building modules: (built, skipped, failed)
/// - built: List of successfully built module names
/// - skipped: List of modules skipped (already up to date)
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

/// Build context for a workspace
pub struct BuildContext {
    /// The workspace being built
    workspace: Workspace,
    /// Module dependency graph
    deps: HashMap<String, Vec<String>>,
    /// Build options
    options: BuildOptions,
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
    /// Modules that were skipped (up to date)
    pub skipped: Vec<String>,
    /// Modules that failed
    pub failed: Vec<(String, String)>,
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
            self.workspace.lib_modules(&lib.name)
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
            duration: start.elapsed(),
        })
    }

    /// Discover all module dependencies
    fn discover_dependencies(&mut self) -> LakeResult<()> {
        self.deps.clear();

        for module in self.workspace.all_modules() {
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
        let imports = self.extract_imports(&content);

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
    fn extract_imports(&self, content: &str) -> Vec<String> {
        Self::extract_all_imports(content)
            .into_iter()
            .filter(|m| !self.is_stdlib_import(m))
            .collect()
    }

    /// Extract ALL import statements from Lean source (including stdlib)
    fn extract_all_imports(content: &str) -> Vec<String> {
        let mut imports = vec![];

        for line in content.lines() {
            let line = line.trim();

            // Skip comments
            if line.starts_with("--") {
                continue;
            }

            // Handle import statements
            if let Some(rest) = line.strip_prefix("import ") {
                let module = rest.trim().to_string();
                imports.push(module);
            }

            // Stop at first non-import declaration
            if !line.is_empty()
                && !line.starts_with("import ")
                && !line.starts_with("--")
                && !line.starts_with("open ")
                && !line.starts_with("set_option ")
            {
                // Continue - imports can be interspersed with other lines in modern Lean
            }
        }

        imports
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

                    // Check if module needs rebuild
                    if !self.options.force && !self.workspace.needs_rebuild(module) {
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

        // Parse
        let surface = clean_parser::parse_file(&content).map_err(|e| LakeError::BuildFailed {
            module: module.to_string(),
            reason: format!("parse error: {e}"),
        })?;

        // Create environment with imported modules
        let mut env = clean_kernel::Environment::with_prelude();
        env.init_io_ops().map_err(|e| LakeError::BuildFailed {
            module: module.to_string(),
            reason: format!("IO operation initialization failed: {e}"),
        })?;

        // Extract ALL imports (including stdlib) from this file
        let all_imports = Self::extract_all_imports(&content);

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
                        // legacy warn-and-continue behavior.
                        if !self.options.permissive_imports {
                            return Err(LakeError::BuildFailed {
                                module: module.to_string(),
                                reason: format!(
                                    "failed to load stdlib import '{imp}': {e} \
                                     (pass --permissive-imports to warn and continue)"
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
            let olean_path = self.workspace.olean_path(dep);
            if olean_path.exists() {
                match clean_olean::load_module_with_deps(&mut env, dep, &dep_search_paths) {
                    Ok(summaries) => {
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
                        if !self.options.permissive_imports {
                            return Err(LakeError::BuildFailed {
                                module: module.to_string(),
                                reason: format!(
                                    "failed to load dependency '{dep}' from {}: {e} \
                                     (pass --permissive-imports to warn and continue)",
                                    olean_path.display()
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

        // Snapshot environment before elaboration so we can capture only new declarations
        let baseline_consts: HashSet<Name> = env.constants().map(|c| c.name.clone()).collect();
        let baseline_inds: HashSet<Name> = env.inductives().map(|i| i.name.clone()).collect();
        let baseline_ctors: HashSet<Name> = env.constructors().map(|c| c.name.clone()).collect();
        let baseline_recs: HashSet<Name> = env.recursors().map(|r| r.name.clone()).collect();

        // Elaborate
        for decl in &surface {
            let (result, aesop_attrs) = {
                let mut elab = clean_elab::ElabCtx::new(&env);
                let result = elab.elab_decl(decl).map_err(|e| LakeError::BuildFailed {
                    module: module.to_string(),
                    reason: format!("elaboration error: {e}"),
                })?;
                let aesop_attrs = elab.take_aesop_attrs();
                (result, aesop_attrs)
            };

            Self::commit_elab_result(&mut env, result).map_err(|reason| {
                LakeError::BuildFailed {
                    module: module.to_string(),
                    reason,
                }
            })?;

            // Register aesop rules collected during elaboration
            for (name, attr) in aesop_attrs {
                clean_elab::register_aesop_rule(&mut env, name, &attr);
            }
        }

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
        let olean_path = self.workspace.olean_path(module);
        if let Some(parent) = olean_path.parent() {
            std::fs::create_dir_all(parent)?;
        }

        // Generate .olean file using the exporter
        let imports: Vec<(&str, bool)> = import_names.iter().map(|s| (s.as_str(), false)).collect();
        let const_refs: Vec<&str> = export_const_names.iter().map(String::as_str).collect();

        let payload = clean_olean::CleanPayload {
            constants: new_constants,
            inductives: new_inductives,
            constructors: new_constructors,
            recursors: new_recursors,
            structure_fields,
        };

        // Use a fixed git hash for clean-generated .olean files (40 hex chars)
        const CLEAN_GIT_HASH: &str = "1ea5000000000000000000000000000000000000";

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
        let server_path = self.workspace.olean_server_path(module);
        let empty_payload = clean_olean::CleanPayload {
            constants: vec![],
            inductives: vec![],
            constructors: vec![],
            recursors: vec![],
            structure_fields: vec![],
        };
        let server_bytes = clean_olean::OleanExporter::export_with_payload(
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
        let private_path = self.workspace.olean_private_path(module);
        let private_bytes = clean_olean::OleanExporter::export_with_payload(
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

        Ok(())
    }

    /// Commit an elaboration result into the kernel environment.
    fn commit_elab_result(
        env: &mut clean_kernel::Environment,
        result: ElabResult,
    ) -> Result<(), String> {
        match result {
            ElabResult::Definition {
                name,
                universe_params,
                ty,
                val,
                modifiers: _,
            } => env
                .add_decl(Declaration::Definition {
                    name,
                    level_params: universe_params,
                    type_: ty,
                    value: val,
                    is_reducible: false,
                })
                .map_err(|e| e.to_string()),
            ElabResult::Theorem {
                name,
                universe_params,
                ty,
                proof,
                modifiers: _,
            } => env
                .add_decl(Declaration::Theorem {
                    name,
                    level_params: universe_params,
                    type_: ty,
                    value: proof,
                })
                .map_err(|e| e.to_string()),
            ElabResult::Axiom {
                name,
                universe_params,
                ty,
                modifiers: _,
            } => env
                .add_decl(Declaration::Axiom {
                    name,
                    level_params: universe_params,
                    type_: ty,
                })
                .map_err(|e| e.to_string()),
            ElabResult::Opaque {
                name,
                universe_params,
                ty,
                val,
                modifiers: _,
            } => {
                if let Some(value) = val {
                    env.add_decl(Declaration::Opaque {
                        name,
                        level_params: universe_params,
                        type_: ty,
                        value,
                    })
                    .map_err(|e| e.to_string())
                } else {
                    env.add_decl(Declaration::Axiom {
                        name,
                        level_params: universe_params,
                        type_: ty,
                    })
                    .map_err(|e| e.to_string())
                }
            }
            ElabResult::Inductive {
                name,
                universe_params,
                num_params,
                ty,
                constructors,
                derived_instances,
                ..
            } => {
                let decl = InductiveDecl {
                    level_params: universe_params,
                    num_params,
                    types: vec![InductiveType {
                        name: name.clone(),
                        type_: ty,
                        constructors: constructors
                            .into_iter()
                            .map(|(ctor_name, ctor_ty)| Constructor {
                                name: ctor_name,
                                type_: ctor_ty,
                            })
                            .collect(),
                    }],
                };
                env.add_inductive(decl).map_err(|e| e.to_string())?;

                for inst in derived_instances {
                    env.add_decl(Declaration::Definition {
                        name: inst.name,
                        level_params: Vec::new(),
                        type_: inst.ty,
                        value: inst.val,
                        is_reducible: false,
                    })
                    .map_err(|e| e.to_string())?;
                }
                Ok(())
            }
            // A mutual inductive family registers in a single `add_inductive`
            // call so cross-references resolve and the kernel builds the mutual
            // recursors.
            ElabResult::MutualInductive {
                decl,
                derived_instances,
                ..
            } => {
                env.add_inductive(decl).map_err(|e| e.to_string())?;
                for inst in derived_instances {
                    env.add_decl(Declaration::Definition {
                        name: inst.name,
                        level_params: inst.level_params,
                        type_: inst.ty,
                        value: inst.val,
                        is_reducible: false,
                    })
                    .map_err(|e| e.to_string())?;
                }
                Ok(())
            }
            ElabResult::Structure {
                name,
                universe_params,
                num_params,
                ty,
                ctor_name,
                ctor_ty,
                field_names,
                projections,
                derived_instances,
                class_info,
                ..
            } => {
                let decl = InductiveDecl {
                    level_params: universe_params,
                    num_params,
                    types: vec![InductiveType {
                        name: name.clone(),
                        type_: ty,
                        constructors: vec![Constructor {
                            name: ctor_name,
                            type_: ctor_ty,
                        }],
                    }],
                };
                env.add_inductive(decl).map_err(|e| e.to_string())?;
                env.register_structure_fields(name.clone(), field_names)
                    .map_err(|e| e.to_string())?;

                for (proj_name, proj_ty, proj_val) in projections {
                    env.add_decl(Declaration::Definition {
                        name: proj_name,
                        level_params: Vec::new(),
                        type_: proj_ty,
                        value: proj_val,
                        is_reducible: true,
                    })
                    .map_err(|e| e.to_string())?;
                }

                for inst in derived_instances {
                    env.add_decl(Declaration::Definition {
                        name: inst.name.clone(),
                        level_params: Vec::new(),
                        type_: inst.ty,
                        value: inst.val,
                        is_reducible: false,
                    })
                    .map_err(|e| e.to_string())?;

                    // Register instance metadata
                    env.register_instance(clean_kernel::KernelInstanceInfo {
                        name: inst.name,
                        class_name: inst.class_name,
                        priority: inst.priority,
                        type_: None,
                        value: None,
                    });
                }

                // If this is a class declaration, register the class
                if let Some(info) = class_info {
                    env.register_class(clean_kernel::KernelClassInfo {
                        name: name.clone(),
                        num_params: info.num_params,
                        out_params: info.out_params,
                        semi_out_params: info.semi_out_params,
                    });
                }
                Ok(())
            }
            ElabResult::Instance {
                name,
                universe_params,
                ty,
                val,
                ..
            } => env
                .add_decl(Declaration::Definition {
                    name,
                    level_params: universe_params,
                    type_: ty,
                    value: val,
                    is_reducible: false,
                })
                .map_err(|e| e.to_string()),
            // `Failed` is an inner decl that already failed elaboration/kernel
            // checking; it is never committed to the environment (committing it
            // would register a rejected declaration).
            // `Example` is checked-then-discarded (B02; lean4
            // `src/Lean/Elab/Declaration.lean`, `elabExample`) — never committed.
            ElabResult::Multiple(_)
            | ElabResult::Command(_)
            | ElabResult::Skipped
            | ElabResult::Example { .. }
            | ElabResult::Failed { .. } => Ok(()),
        }
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
    fn test_extract_imports() {
        let tmp = TempDir::new().unwrap();
        let content = r"
import MyLib.Core
import MyLib.Utils
-- import Commented

open MyLib

def foo := 1
";
        let imports = empty_ctx(&tmp).extract_imports(content);
        assert_eq!(imports, vec!["MyLib.Core", "MyLib.Utils"]);
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
        let imports = empty_ctx(&tmp).extract_imports(content);
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

        let imports = ctx.extract_imports("import Std.Mine\nimport Std.Data.List\n");
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
    /// `.olean`. The ordinary build below is the CONTROL — it still skips and
    /// still reports success, which is exactly why the check must not.
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

        // CONTROL: the ordinary build reports success without reading either
        // source — this is the state the check has to see through.
        let ws = Workspace::load(tmp.path()).expect("workspace loads");
        let mut ctx = BuildContext::new(ws);
        let control = ctx.build_all().expect("control build");
        assert!(
            control.failed.is_empty() && control.built.is_empty(),
            "control: the ordinary build must skip everything here, got {control:?}"
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

        // Corrupt the dependency artifact (its fresh mtime keeps Base skipped)
        // and drop Top's artifact so only Top rebuilds.
        let lib_dir = tmp.path().join(".lake/build/lib");
        fs::write(lib_dir.join("DepFail/Base.olean"), b"not an olean").unwrap();
        fs::remove_file(lib_dir.join("DepFail/Top.olean")).unwrap();

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
