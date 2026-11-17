// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0
//! Captured source-module orchestration, shared with the file frontends.
//!
//! These are frontend computations and producer data, not proof authority.
//! Declaration checking stays in the existing module driver and kernel. A
//! consumer crediting imported proofs must still perform its original fence.

mod captured;
mod isolation;

pub use captured::{
    captured_file_context, CapturedSourceGraph, CapturedSourceModule, SourceDeclarationOutput,
    SourceGraphError, SourceGraphOutput, SourceImport, SourceImportResolver, SourceModuleOutput,
};
pub use isolation::{elab_outcome_difference, ElabOutcome, ModuleElaboration};

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::rc::Rc;

use clean_kernel::Environment;

/// The existing bound on retained faithful contexts. More contexts change
/// only replay cost, never which source import closure is checked.
const FAITHFUL_ENVIRONMENT_LIMIT: usize = 128;

/// Common import-walk bookkeeping. Its fields are untrusted frontend state;
/// nothing represented here is an admission or an accepted proof.
#[derive(Default)]
pub struct ImportGraph {
    pub completed: HashSet<PathBuf>,
    pub in_flight: HashSet<PathBuf>,
    pub import_frames: Vec<Vec<PathBuf>>,
    pub closures: HashMap<PathBuf, HashSet<PathBuf>>,
    pub direct_imports: HashMap<PathBuf, Vec<PathBuf>>,
    pub faithful: HashMap<PathBuf, Option<Rc<(Environment, ModuleElaboration)>>>,
}

impl ImportGraph {
    /// Enter a source in authored import order, deduplicating diamonds and
    /// detecting an active backedge before any declaration is checked.
    /// `None` means this source already completed in the current environment.
    pub fn enter(
        &mut self,
        path: &Path,
        depth_limit: usize,
    ) -> Result<Option<HashSet<PathBuf>>, String> {
        if self.in_flight.len() >= depth_limit {
            return Err(format!(
                "import depth limit ({depth_limit}) exceeded while checking {}",
                path.display()
            ));
        }
        if let Some(frame) = self.import_frames.last_mut() {
            if !frame.iter().any(|previous| previous == path) {
                frame.push(path.to_path_buf());
            }
        }
        if self.completed.contains(path) {
            return Ok(None);
        }
        if !self.in_flight.insert(path.to_path_buf()) {
            return Err(format!(
                "import cycle detected at {}: file is already being elaborated",
                path.display()
            ));
        }
        let completed_at_start = self.completed.clone();
        self.import_frames.push(Vec::new());
        Ok(Some(completed_at_start))
    }

    /// Leave a visit even when its body failed. A failure is never completed.
    pub fn leave(&mut self, path: &Path) -> Vec<PathBuf> {
        let imports = self.import_frames.pop().unwrap_or_default();
        self.in_flight.remove(path);
        imports
    }

    /// Record the ordered direct and transitive closure, returning whether
    /// this body ran beside a module outside that closure.
    pub fn record_imports(
        &mut self,
        path: &Path,
        direct_imports: Vec<PathBuf>,
        completed_at_start: &HashSet<PathBuf>,
    ) -> bool {
        let mut closure = HashSet::new();
        for import in &direct_imports {
            closure.insert(import.clone());
            if let Some(inner) = self.closures.get(import) {
                closure.extend(inner.iter().cloned());
            }
        }
        let saw_strangers = completed_at_start
            .iter()
            .any(|done| !closure.contains(done));
        self.closures.insert(path.to_path_buf(), closure);
        self.direct_imports
            .insert(path.to_path_buf(), direct_imports);
        saw_strangers
    }

    /// Retain only a context checked without strangers and without an earlier
    /// divergence. Return the record when the caller must retain it elsewhere.
    pub fn retain_faithful(
        &mut self,
        path: &Path,
        own: Option<ModuleElaboration>,
        environment: &Environment,
        saw_strangers: bool,
        no_divergences: bool,
    ) -> Option<ModuleElaboration> {
        let keep = !saw_strangers
            && no_divergences
            && !self.faithful.contains_key(path)
            && self
                .faithful
                .values()
                .filter(|entry| entry.is_some())
                .count()
                < FAITHFUL_ENVIRONMENT_LIMIT;
        match own {
            Some(own) if keep => {
                self.faithful.insert(
                    path.to_path_buf(),
                    Some(Rc::new((environment.clone(), own))),
                );
                None
            }
            other => other,
        }
    }
}

#[cfg(test)]
mod tests;
