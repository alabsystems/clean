// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end Coq declaration collection and environment wiring.
//!
//! This module ties together [`CoqBatchImporter`] (which parses and translates
//! Coq S-expression declarations) with [`verify_declarations_into`] (which
//! feeds `TranslatedGlobalDecl` values to [`Environment::add_decl`] /
//! [`Environment::add_inductive`]).
//!
//! Before this module, translated declarations were discarded — only
//! success/failure counts survived. Now the full pipeline is:
//!
//! 1. Parse Coq S-expressions → `GlobalDecl`
//! 2. Translate → `TranslatedGlobalDecl` (kernel `Declaration` / `InductiveDecl`)
//! 3. Collect (not discard)
//! 4. Feed to `Environment::add_decl` / `add_inductive`
//! 5. Report per-declaration success/failure

use crate::env::Environment;

use super::import_batch::{BatchImportSource, CoqBatchImporter, ImportStats};
use super::translate::TranslatedGlobalDecl;
use super::verify::{verify_declarations_into, VerifyResult, VerifyStats};

/// Collected declarations from one or more Coq source files, ready to be
/// fed to an [`Environment`].
#[derive(Debug, Clone)]
pub struct CollectedDeclarations {
    /// The translated kernel declarations.
    pub declarations: Vec<TranslatedGlobalDecl>,
    /// Import statistics (parse/translate counts).
    pub import_stats: ImportStats,
}

impl CollectedDeclarations {
    /// Number of collected declarations.
    #[must_use]
    pub fn len(&self) -> usize {
        self.declarations.len()
    }

    /// Whether the collection is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.declarations.is_empty()
    }
}

/// Result of the full collect-and-add pipeline.
#[derive(Debug)]
pub struct AddResult {
    /// Import statistics from the translation phase.
    pub import_stats: ImportStats,
    /// Verification statistics from the environment-add phase.
    pub verify_stats: VerifyStats,
    /// The environment with all successfully added declarations.
    pub env: Environment,
    /// Names of declarations that failed verification, paired with error text.
    pub errors: Vec<(String, String)>,
}

/// Collect translated declarations from Coq sources without discarding them.
///
/// Runs the full parse + translate pipeline via [`CoqBatchImporter`] and
/// returns the collected kernel declarations. Stdlib type and proposition
/// mappings are pre-loaded.
pub fn collect_declarations<I, T>(sources: I) -> CollectedDeclarations
where
    I: IntoIterator<Item = T>,
    T: Into<BatchImportSource>,
{
    let mut importer = CoqBatchImporter::new();
    importer.import_stdlib_types();
    importer.import_stdlib_propositions();
    let import_stats = importer.import_sources_collecting(sources);
    let declarations = importer.take_declarations();
    CollectedDeclarations {
        declarations,
        import_stats,
    }
}

/// Collect declarations using an existing [`CoqBatchImporter`].
///
/// Useful when the caller has already configured stdlib mappings or
/// custom translation context.
pub fn collect_declarations_with(
    importer: &mut CoqBatchImporter,
    sources: impl IntoIterator<Item = impl Into<BatchImportSource>>,
) -> CollectedDeclarations {
    let import_stats = importer.import_sources_collecting(sources);
    let declarations = importer.take_declarations();
    CollectedDeclarations {
        declarations,
        import_stats,
    }
}

/// Feed collected declarations into a fresh [`Environment`], returning
/// the populated environment and per-declaration success/failure stats.
pub fn add_to_environment(collected: CollectedDeclarations) -> AddResult {
    let mut env = Environment::new();
    add_to_environment_into(&mut env, collected)
}

/// Feed collected declarations into an existing [`Environment`].
///
/// Useful when the environment has been pre-configured (e.g., with
/// [`Environment::with_prelude()`] or declarations from other sources).
pub fn add_to_environment_into(
    env: &mut Environment,
    collected: CollectedDeclarations,
) -> AddResult {
    let VerifyResult {
        env: final_env,
        stats: verify_stats,
        errors,
    } = verify_declarations_into(env, collected.declarations);

    AddResult {
        import_stats: collected.import_stats,
        verify_stats,
        env: final_env,
        errors,
    }
}

/// One-shot: parse, translate, collect, and add Coq declarations to a fresh
/// environment.
///
/// Combines [`collect_declarations`] and [`add_to_environment`] for the
/// common case where the caller wants end-to-end processing.
pub fn import_and_verify<I, T>(sources: I) -> AddResult
where
    I: IntoIterator<Item = T>,
    T: Into<BatchImportSource>,
{
    let collected = collect_declarations(sources);
    add_to_environment(collected)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::coq_import::BatchImportSource;

    /// Helper: an axiom declaration in Coq S-expression format.
    fn axiom_source(name: &str) -> BatchImportSource {
        BatchImportSource::new(
            format!("{name}.v"),
            format!(r#"(axiom (name "Coq.Test.{name}") (type (sort prop)))"#),
        )
    }

    #[test]
    fn test_collect_declarations_not_empty() {
        let collected = collect_declarations(vec![axiom_source("alpha")]);
        assert_eq!(collected.len(), 1);
        assert!(!collected.is_empty());
        assert_eq!(collected.import_stats.successes, 1);
        assert_eq!(collected.import_stats.failures, 0);
    }

    #[test]
    fn test_collect_declarations_empty_input() {
        let collected = collect_declarations(Vec::<BatchImportSource>::new());
        assert!(collected.is_empty());
    }

    #[test]
    fn test_collect_declarations_skips_non_v_files() {
        let collected = collect_declarations(vec![BatchImportSource::new(
            "notes.txt",
            r#"(axiom (name "Coq.Test.skip") (type (sort prop)))"#,
        )]);
        assert!(collected.is_empty());
        assert_eq!(collected.import_stats.skipped, 1);
    }

    #[test]
    fn test_add_to_environment_axiom() {
        let collected = collect_declarations(vec![axiom_source("beta")]);
        let result = add_to_environment(collected);
        assert_eq!(result.verify_stats.verified, 1);
        assert_eq!(result.verify_stats.failed, 0);
        assert!(result.errors.is_empty());
    }

    #[test]
    fn test_add_to_environment_bad_source_fails_gracefully() {
        let sources = vec![
            axiom_source("good"),
            BatchImportSource::new("bad.v", "not-valid-sexp"),
        ];
        let collected = collect_declarations(sources);
        // "good" translates, "bad" fails at parse time (not in collected).
        assert_eq!(collected.import_stats.successes, 1);
        assert_eq!(collected.import_stats.failures, 1);
        assert_eq!(collected.len(), 1);

        let result = add_to_environment(collected);
        assert_eq!(result.verify_stats.verified, 1);
    }

    #[test]
    fn test_import_and_verify_end_to_end() {
        let result = import_and_verify(vec![axiom_source("e2e_one"), axiom_source("e2e_two")]);
        assert_eq!(result.import_stats.successes, 2);
        assert_eq!(result.verify_stats.verified, 2);
        assert!(result.errors.is_empty());
    }

    #[test]
    fn test_add_to_environment_into_preserves_existing() {
        let mut env = Environment::new();
        env.add_decl(crate::Declaration::Axiom {
            name: crate::Name::from_string("preexisting"),
            level_params: vec![],
            type_: crate::Expr::prop(),
        })
        .expect("pre-existing decl should add");

        let collected = collect_declarations(vec![axiom_source("fromcoq")]);
        let result = add_to_environment_into(&mut env, collected);
        assert_eq!(result.verify_stats.verified, 1);
        assert!(result
            .env
            .get_const(&crate::Name::from_string("preexisting"))
            .is_some());
    }

    #[test]
    fn test_collect_declarations_with_custom_importer() {
        let mut importer = CoqBatchImporter::new();
        importer.import_stdlib_types();

        let collected = collect_declarations_with(&mut importer, vec![axiom_source("custom")]);
        assert_eq!(collected.len(), 1);
    }
}
