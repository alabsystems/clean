// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A file's import context: search paths, Lean world, resolution policy,
//! source refusals and compiler dependencies (gap G72, decision R111).

use super::{FileContext, FixedImportPaths};
use crate::imports::ImportPolicy;
use clean_kernel::name::Name;
use std::collections::HashSet;
use std::path::PathBuf;

impl FileContext {
    /// The grammar and command semantics of the same choice that supplies
    /// this file's imports ([`clean_olean::source_world_of`]). A refused
    /// project world keeps refusing every import of a Lean module; its source
    /// language is the Oracle's, which takes no feature decision of the
    /// refused release (R-WR, R111).
    pub fn lean_world(
        &self,
    ) -> Result<clean_kernel::lean_world::LeanWorld, clean_olean::SourceWorldRefusal> {
        match &self.import_world {
            None => Ok(clean_kernel::lean_world::LeanWorld::ORACLE),
            Some(world) => Ok(clean_olean::source_world_of(world)?),
        }
    }

    /// Source world declared for artifacts loaded by this file.
    ///
    /// # Errors
    /// A declared project world without a corresponding source language.
    pub fn declared_lean_world(
        &self,
    ) -> Result<Option<clean_kernel::LeanWorld>, clean_olean::SourceWorldRefusal> {
        match &self.import_world {
            Some(Ok(world)) if world.declared_world().is_some() => Ok(Some(world.source_world()?)),
            _ => Ok(None),
        }
    }

    /// Bind a decision shared with the parser. Every source import in a run
    /// inherits the entry file's decision, not its own nested toolchain.
    pub fn set_source_world(
        &mut self,
        path: &std::path::Path,
        decision: &clean_olean::SourceWorldDecision,
    ) {
        self.set_import_context(path, decision.import_world());
    }
    /// Bind the selected source world and exact artifact roots. Skip project
    /// discovery and additional default roots.
    pub(crate) fn set_captured_source_world(
        &mut self,
        decision: &clean_olean::SourceWorldDecision,
        paths: Vec<PathBuf>,
    ) {
        self.set_fixed_source_world(decision, FixedImportPaths::Captured(paths));
    }

    /// Require actual artifacts on the given roots for the raw Lean front door.
    pub(crate) fn set_artifact_source_world(
        &mut self,
        decision: &clean_olean::SourceWorldDecision,
        paths: Vec<PathBuf>,
    ) {
        self.set_fixed_source_world(decision, FixedImportPaths::ArtifactsOnly(paths));
    }

    fn set_fixed_source_world(
        &mut self,
        decision: &clean_olean::SourceWorldDecision,
        paths: FixedImportPaths,
    ) {
        self.import_world = Some(decision.import_world());
        self.import_search_paths.clear();
        self.fixed_import_paths = Some(paths);
    }

    pub(crate) fn imports_require_artifacts(&self) -> bool {
        matches!(
            &self.fixed_import_paths,
            Some(FixedImportPaths::ArtifactsOnly(_))
        )
    }

    /// Replace the file-level import search paths used for `.olean` loading.
    pub fn set_import_search_paths(&mut self, paths: Vec<PathBuf>) {
        self.import_search_paths = paths;
    }

    /// Get the file-level import search paths used for `.olean` loading.
    #[must_use]
    pub fn import_search_paths(&self) -> &[PathBuf] {
        &self.import_search_paths
    }

    /// Bind this file's imports to `path`'s project (gap G72): its Lake
    /// roots ([`crate::lake_import_search_paths_for_file`]) and the Lean world
    /// its `lean-toolchain` names ([`clean_olean::import_world_for_file`]).
    /// For a caller that elaborates this one file into its environment; a
    /// caller that elaborates several selects the world once and passes it to
    /// [`Self::set_import_context`].
    pub fn set_import_context_for_file(&mut self, path: &std::path::Path) {
        self.set_import_context(path, clean_olean::import_world_for_file(path));
    }

    /// Bind this file's imports to its Lake roots and to `world`, the Lean
    /// world of the run that elaborates it: the world supplies the stdlib
    /// root; a Historical or Frontend-only world is declared on the
    /// environment before any part loads (the checkout's is not, R81); and a
    /// refused world refuses every import of a Lean module, one the run
    /// elaborated from the project's own source staying resolved (R111).
    pub fn set_import_context(
        &mut self,
        path: &std::path::Path,
        world: Result<clean_olean::ImportWorld, clean_olean::ImportWorldRefusal>,
    ) {
        self.import_search_paths = crate::lake_import_search_paths_for_file(path);
        self.fixed_import_paths = None;
        self.import_world = Some(world);
    }

    /// The Lean world this file's imports resolve in, when one was set.
    #[must_use]
    pub(crate) fn import_world(
        &self,
    ) -> Option<&Result<clean_olean::ImportWorld, clean_olean::ImportWorldRefusal>> {
        self.import_world.as_ref()
    }

    /// Every root this file's `.olean` imports resolve on. An exact list is
    /// used as supplied. Project contexts use their own search paths followed
    /// by their world's defaults ([`clean_olean::search_paths_in_world`]).
    ///
    /// # Errors
    ///
    /// The refusal of this file's world: none of its imports may resolve.
    pub fn effective_import_search_paths(
        &self,
    ) -> Result<Vec<PathBuf>, clean_olean::ImportWorldRefusal> {
        if let Some(FixedImportPaths::Captured(paths) | FixedImportPaths::ArtifactsOnly(paths)) =
            &self.fixed_import_paths
        {
            if let Some(Err(refusal)) = &self.import_world {
                return Err(refusal.clone());
            }
            return Ok(paths.clone());
        }
        let defaults = match &self.import_world {
            None => clean_olean::default_search_paths(),
            Some(Ok(world)) => clean_olean::search_paths_in_world(world),
            Some(Err(refusal)) => return Err(refusal.clone()),
        };
        let mut paths = self.import_search_paths.clone();
        for path in defaults {
            if !paths.contains(&path) {
                paths.push(path);
            }
        }
        Ok(paths)
    }

    /// Apply the header from the same parse report as this file's declarations.
    pub fn set_file_header(&mut self, header: &clean_parser::FileHeader) {
        self.module_system = header.is_module;
    }

    pub(crate) fn is_module_system(&self) -> bool {
        self.module_system
    }

    /// Get a mutable reference to the persistent set of modules already loaded
    /// by this file's earlier `import` declarations.
    ///
    /// Threaded into [`clean_olean::load_module_with_deps_bounded_shared`] so a
    /// file's overlapping `.olean` closures are read once across all its
    /// imports rather than re-read per top-level import.
    pub fn import_visited_mut(&mut self) -> &mut hashbrown::HashSet<String> {
        &mut self.import_visited
    }

    /// The modules this file's `import` declarations have loaded from
    /// `.olean` artifacts so far (their whole closures), by name.
    #[must_use]
    pub fn import_visited(&self) -> &hashbrown::HashSet<String> {
        &self.import_visited
    }

    /// Disable external `.olean` import search for this file context.
    ///
    /// When set, `Import` declarations only initialize Clean's built-in
    /// module preludes; they do not consult Lean / Lake / Mathlib `.olean`
    /// artifacts as semantic authority.
    pub fn disable_external_import_search(&mut self) {
        self.disable_external_import_search = true;
    }

    /// Read the sealed flag for the public crate-root policy query.
    #[must_use]
    pub(crate) fn external_import_search_enabled_impl(&self) -> bool {
        !self.disable_external_import_search
    }

    /// Set what this file's `import` statements do when a module resolves to
    /// nothing real. Defaults to [`ImportPolicy::FailClosed`].
    pub fn set_import_policy(&mut self, policy: ImportPolicy) {
        self.import_policy = policy;
    }

    /// The unresolved-import policy in force for this file.
    #[must_use]
    pub fn import_policy(&self) -> ImportPolicy {
        self.import_policy
    }

    /// Record that `module`'s declarations are already in the environment
    /// because this run elaborated its intra-project `.lean` source.
    ///
    /// Without this, a perfectly ordinary multi-file project with no compiled
    /// artifacts would fail closed on its own internal imports: `clean check`
    /// elaborates `Foo.lean` in its first pass, and the second pass then finds
    /// no `Foo.olean` anywhere. The import IS resolved; the missing artifact is
    /// expected.
    pub fn mark_import_satisfied_from_source(&mut self, module: &Name) {
        if self.imports_refused_from_source.contains_key(module) {
            return;
        }
        // Loader availability is shared across the import walk. Only the
        // file's actual Import declarations authorize compiler visibility.
        self.imports_satisfied_from_source.insert(module.clone());
        self.imports_satisfied_without_search.insert(module.clone());
    }

    /// Only the maintained source-module initializer supplies this immutable
    /// memo alongside the environment it actually loaded. It is name-resolution
    /// DATA, not proof credit; external import search and policy are unchanged.
    pub(crate) fn set_preloaded_artifact_imports(
        &mut self,
        imports: clean_olean::CompletedModuleImports,
    ) {
        self.preloaded_artifact_imports = Some(imports);
    }

    pub(crate) fn preloaded_artifact_imports(
        &self,
    ) -> Option<&clean_olean::CompletedModuleImports> {
        self.preloaded_artifact_imports.as_ref()
    }

    /// Record the module keys of an original-reference checked fixed context.
    /// This resolution record installs no declarations and grants no theorem or
    /// source authority; the caller must use this context's paired environment.
    /// Only its replayed declaration cone is citable; any missing library
    /// declaration still refuses, with no artifact search or prelude fallback.
    pub fn install_checked_source_context(
        &mut self,
        context: &clean_olean::fixed_cohort::CheckedSourceContext,
    ) -> Result<(), String> {
        if self
            .checked_source_context_identity
            .as_deref()
            .is_some_and(|identity| identity != context.identity())
        {
            return Err(
                "file context already belongs to a different checked source context".into(),
            );
        }
        self.checked_source_context_identity = Some(context.identity().into());
        for module in context.modules() {
            let module = Name::from_string(module);
            if !self.imports_refused_from_source.contains_key(&module) {
                self.imports_satisfied_from_checked_context
                    .insert(module.clone());
                self.imports_satisfied_without_search.insert(module);
            }
        }
        Ok(())
    }

    #[must_use]
    pub fn import_satisfied_from_checked_context(&self, module: &Name) -> bool {
        self.imports_satisfied_from_checked_context.contains(module)
    }

    /// Record a source import's refusal, retaining its first diagnostic.
    /// This takes precedence over satisfied records, artifacts and permissive
    /// builtin fallback: the partial environment is not the imported module.
    pub fn mark_import_refused_from_source(&mut self, module: &Name, reason: String) {
        self.imports_satisfied_from_source.remove(module);
        self.imports_satisfied_from_checked_context.remove(module);
        self.imports_satisfied_without_search.remove(module);
        self.compiler_imports.remove(module);
        self.imports_refused_from_source
            .entry(module.clone())
            .or_insert(reason);
    }

    /// The first reason this run could not elaborate this source import.
    #[must_use]
    pub fn import_source_refusal(&self, module: &Name) -> Option<&str> {
        self.imports_refused_from_source
            .get(module)
            .map(String::as_str)
    }

    /// Record a resolved import for the source file's compiler dependency view.
    /// This does not satisfy the elaborator's separate import-resolution policy.
    pub fn record_compiler_import(&mut self, module: &Name) {
        self.compiler_imports.insert(module.clone());
    }

    pub(crate) fn refresh_compiler_module(&self, env: &mut clean_kernel::Environment) {
        if let Some(module) = self.main_module() {
            clean_kernel::env::csimp::begin_source_module(
                env,
                module.clone(),
                self.compiler_imports.iter().cloned().collect(),
            );
        }
    }

    /// Whether `module` was recorded by [`Self::mark_import_satisfied_from_source`].
    #[must_use]
    pub fn import_satisfied_from_source(&self, module: &Name) -> bool {
        self.imports_satisfied_from_source.contains(module)
    }

    /// Modules supplied by successfully elaborated source or the checked source
    /// context. Each provenance remains available from its own record.
    #[must_use]
    pub(crate) fn imports_satisfied_without_search(&self) -> &HashSet<Name> {
        &self.imports_satisfied_without_search
    }

    /// The two per-file loader records the import path needs together: the
    /// `visited` memo it mutates, and the read-only set of modules already
    /// supplied by source or its checked context. Returned together so callers need not
    /// clone either to satisfy the borrow checker.
    pub(crate) fn import_loader_state_mut(
        &mut self,
    ) -> (&mut hashbrown::HashSet<String>, &HashSet<Name>) {
        (
            &mut self.import_visited,
            &self.imports_satisfied_without_search,
        )
    }
}
