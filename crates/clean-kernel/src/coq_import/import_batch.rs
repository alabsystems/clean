// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Batch-oriented Coq import scaffolding.

use super::parser::parse_declarations;
use super::translate::{translate_global_decl, TranslatedGlobalDecl, TranslationContext};
use super::CoqImportResult;
use std::path::{Path, PathBuf};

/// Aggregate counts for one batch import run.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct ImportStats {
    pub successes: usize,
    pub failures: usize,
    pub skipped: usize,
}

/// One Coq source unit supplied to the batch importer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BatchImportSource {
    pub path: PathBuf,
    pub contents: String,
}

impl BatchImportSource {
    #[must_use]
    pub fn new(path: impl Into<PathBuf>, contents: impl Into<String>) -> Self {
        Self {
            path: path.into(),
            contents: contents.into(),
        }
    }
}

impl<P, S> From<(P, S)> for BatchImportSource
where
    P: Into<PathBuf>,
    S: Into<String>,
{
    fn from((path, contents): (P, S)) -> Self {
        Self::new(path, contents)
    }
}

/// Batch importer for Coq `.v` sources.
///
/// Filesystem loading is intentionally left to the caller for now; this layer
/// accepts preloaded source text so batching and stats remain testable while the
/// real I/O pipeline is stubbed out.
#[derive(Debug, Clone)]
pub struct CoqBatchImporter {
    context: TranslationContext,
    stats: ImportStats,
    /// Collected translated declarations (previously discarded).
    /// Populated when `import_sources_collecting` is used instead of `import_sources`.
    declarations: Vec<TranslatedGlobalDecl>,
}

impl Default for CoqBatchImporter {
    fn default() -> Self {
        Self::new()
    }
}

impl CoqBatchImporter {
    #[must_use]
    pub fn new() -> Self {
        Self {
            context: TranslationContext::empty(),
            stats: ImportStats::default(),
            declarations: Vec::new(),
        }
    }

    #[must_use]
    pub fn with_context(context: TranslationContext) -> Self {
        Self {
            context,
            stats: ImportStats::default(),
            declarations: Vec::new(),
        }
    }

    #[must_use]
    pub fn context(&self) -> &TranslationContext {
        &self.context
    }

    pub fn context_mut(&mut self) -> &mut TranslationContext {
        &mut self.context
    }

    #[must_use]
    pub fn stats(&self) -> ImportStats {
        self.stats
    }

    pub fn import_stdlib_types(&mut self) {
        self.context.import_stdlib_type_mappings();
    }

    pub fn import_stdlib_propositions(&mut self) {
        self.context.import_stdlib_propositions();
    }

    pub fn import_sources<I, T>(&mut self, sources: I) -> ImportStats
    where
        I: IntoIterator<Item = T>,
        T: Into<BatchImportSource>,
    {
        for source in sources {
            let source = source.into();
            self.import_one_source(&source.path, &source.contents);
        }
        self.stats
    }

    pub fn translate_source(&self, source: &str) -> CoqImportResult<Vec<TranslatedGlobalDecl>> {
        parse_declarations(source)?
            .iter()
            .map(|decl| translate_global_decl(decl, &self.context))
            .collect()
    }

    /// Import sources and collect the translated declarations.
    ///
    /// Unlike `import_sources` which discards declarations, this method
    /// accumulates them in `self.declarations` for later use by the kernel
    /// type-checker or mathverse shard writer.
    pub fn import_sources_collecting<I, T>(&mut self, sources: I) -> ImportStats
    where
        I: IntoIterator<Item = T>,
        T: Into<BatchImportSource>,
    {
        for source in sources {
            let source = source.into();
            self.import_one_source_collecting(&source.path, &source.contents);
        }
        self.stats
    }

    /// Get collected declarations (from `import_sources_collecting`).
    #[must_use]
    pub fn declarations(&self) -> &[TranslatedGlobalDecl] {
        &self.declarations
    }

    /// Take collected declarations, leaving the internal buffer empty.
    pub fn take_declarations(&mut self) -> Vec<TranslatedGlobalDecl> {
        std::mem::take(&mut self.declarations)
    }

    fn import_one_source(&mut self, path: &Path, source: &str) {
        if !is_coq_source(path) {
            self.stats.skipped += 1;
            return;
        }

        match self.translate_source(source) {
            Ok(_) => self.stats.successes += 1,
            Err(_) => self.stats.failures += 1,
        }
    }

    fn import_one_source_collecting(&mut self, path: &Path, source: &str) {
        if !is_coq_source(path) {
            self.stats.skipped += 1;
            return;
        }

        match self.translate_source(source) {
            Ok(decls) => {
                self.stats.successes += 1;
                self.declarations.extend(decls);
            }
            Err(_) => self.stats.failures += 1,
        }
    }
}

fn is_coq_source(path: &Path) -> bool {
    path.extension()
        .and_then(|ext| ext.to_str())
        .is_some_and(|ext| ext.eq_ignore_ascii_case("v"))
}
