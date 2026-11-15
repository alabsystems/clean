// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Document elaboration: the module driver `clean check` runs, observed as LSP
//! diagnostics, hole goals and declaration info.
//!
//! The editor used to elaborate each declaration with the context-free
//! `elaborate_decl_and_register_with_warning`, so a standalone `open`, a
//! `variable` or a section's state did not reach the next declaration, and a
//! failing member of a `namespace` block produced no diagnostic at all. It now
//! runs `clean_elab::module_driver::elaborate_decls` with the same
//! `FileContext` threading, block flattening and read-only re-validation as
//! `clean check`, which runs the same function.

use super::warnings::{
    collect_deprecated_names, detect_deprecated_usage, detect_duplicate_binders,
    detect_sorry_warnings, detect_unused_variables, merge_registration_sorry_warning,
};
use super::{byte_offset_to_position, CleanBackend};
use crate::document::{
    ElaboratedDecl, ElaboratedDocument, IncrementalState, IncrementalStats, TypeError,
};
use crate::file_progress::LeanFileProgressProcessingInfo;
use clean_elab::module_driver::{
    elaborate_decls, module_elaboration_lock, module_file_context, BudgetReading, DriverOptions,
    FailureIsolation, ImportHandling, LeafOutcome, ModuleObserver,
};
use clean_elab::{ElabError, FileContext, RegisteredElabResult};
use clean_kernel::Environment;
use clean_parser::SurfaceDecl;
use std::collections::{HashMap, HashSet};
use tower_lsp::lsp_types::{Position, Range};

/// What one document's elaboration collects, fed by the module driver.
struct DocumentObserver<'a> {
    text: &'a str,
    end_of_file: Position,
    progress: &'a tokio::sync::mpsc::UnboundedSender<Vec<LeanFileProgressProcessingInfo>>,
    deprecated_names: &'a HashSet<clean_kernel::Name>,
    errors: Vec<TypeError>,
    warnings: Vec<crate::document::Warning>,
    declarations: Vec<ElaboratedDecl>,
    declaration_terms: Vec<(clean_parser::Span, clean_elab::term_info::TermContext)>,
    holes: Vec<crate::document::HoleContext>,
    widget_modules: Vec<crate::document::WidgetModule>,
    /// The current declaration's warnings, flushed when it is done.
    pending_warnings: Vec<crate::document::Warning>,
}

impl ModuleObserver for DocumentObserver<'_> {
    fn before_decl(&mut self, _env: &Environment, index: usize, decl: &SurfaceDecl) {
        let (_kind, _name, span) = CleanBackend::classify_decl(decl);
        // fileProgress shrink: everything before this declaration is done;
        // the remainder of the file (this declaration onward) is still
        // being processed. The first declaration needs no extra event —
        // the parse phase already announced the whole file as processing.
        // Progress is advisory: a send failure only means the async
        // caller stopped listening, so the error is dropped.
        if index > 0 {
            let processing_start = byte_offset_to_position(self.text, span.0);
            let _ = self
                .progress
                .send(vec![LeanFileProgressProcessingInfo::processing(
                    Range::new(processing_start, self.end_of_file),
                )]);
        }

        // Surface-level warnings (unused vars, literal sorry, deprecation)
        self.pending_warnings.extend(detect_unused_variables(decl));
        self.pending_warnings.extend(detect_duplicate_binders(decl));
        self.pending_warnings.extend(detect_sorry_warnings(decl));
        self.pending_warnings
            .extend(detect_deprecated_usage(decl, self.deprecated_names));
    }

    fn decl_registered(&mut self, decl: &SurfaceDecl, registered: &RegisteredElabResult) {
        self.declaration_terms
            .extend(super::declaration_term_info::observe(
                self.text,
                decl,
                &registered.result,
            ));
        // Record hole-local expected types for every user-written `_` hole
        // the elaborator tagged with a source span. This covers nested /
        // sub-term holes (e.g. `Nat.succ (_ : Nat)`) with the precise type the
        // elaborator demanded at that hole, instantiated as far as it is
        // solved.
        CleanBackend::push_hole_contexts(&mut self.holes, &registered.hole_contexts);

        if let Some(info) = CleanBackend::extract_elab_info(&registered.result, decl) {
            // A declaration type cannot supply goals under its binders.
            // Its name observation above uses only its exact source tokens;
            // ordinary term observations are collected separately below.
            // Record a user-defined widget module when the declaration
            // carries the `@[widget_module]` attribute.
            if CleanBackend::is_widget_module_decl(decl) {
                self.widget_modules.push(crate::document::WidgetModule {
                    name: info.name.clone(),
                    start: info.start,
                    end: info.end,
                });
            }
            self.declarations.push(info);
        }

        // Merge surface warnings with the registration report.
        let (_kind, name, span) = CleanBackend::classify_decl(decl);
        let decl_name = name.as_deref().unwrap_or("<anonymous>");
        let surface = std::mem::take(&mut self.pending_warnings);
        self.pending_warnings =
            merge_registration_sorry_warning(surface, registered.warning.as_ref(), decl_name, span);
    }

    fn decl_failed(&mut self, env: &Environment, decl: &SurfaceDecl, error: &ElabError) {
        let (start, end) = CleanBackend::get_decl_span(decl);
        self.errors.push(TypeError {
            start,
            end,
            message: format!("{error}"),
            related: Vec::new(),
        });
        // Even when registration fails (commonly because the declaration
        // contains an unfilled `_` hole whose unsolved metavariable is a free
        // variable the kernel rejects), recover the hole contexts by
        // re-elaborating without registration against the environment the
        // declaration saw — the driver restored it (`FailureIsolation::
        // Rollback`; a failed `deriving` class never lands here — its type
        // registered and passed, and the class is a failed leaf of its own,
        // as Lean logs it). This is exactly the case an IDE needs: the user
        // is hovering a hole they have not yet filled in.
        let (recovered, recovered_holes) = clean_elab::elaborate_decl_capturing_holes(env, decl);
        // This already-required recovery can retain a real declaration type
        // even when an unfinished body prevents kernel registration.
        if let Ok(result) = recovered {
            self.declaration_terms
                .extend(super::declaration_term_info::observe(
                    self.text, decl, &result,
                ));
        }
        CleanBackend::push_hole_contexts(&mut self.holes, &recovered_holes);
    }

    fn leaf_checked(&mut self, _env: &Environment, decl: &SurfaceDecl, outcome: &LeafOutcome<'_>) {
        if let LeafOutcome::Checked {
            source_diagnostics, ..
        } = outcome
        {
            for diagnostic in *source_diagnostics {
                let (start, end) = diagnostic.span.map_or_else(
                    || CleanBackend::get_decl_span(decl),
                    |span| (span.start, span.end),
                );
                self.errors.push(TypeError {
                    start,
                    end,
                    message: diagnostic.error.to_string(),
                    related: Vec::new(),
                });
            }
        }
        // A member of a block that failed, a leaf the read-only re-validation
        // rejected, or one whose elaboration raised a kernel failure is an
        // error — the verdict `clean check` reports for it.
        let ((start, end), message) = match outcome {
            LeafOutcome::Failed {
                decl: inner, error, ..
            } => (CleanBackend::get_decl_span(inner), format!("{error}")),
            LeafOutcome::ValidationFailed { name, message } => (
                CleanBackend::get_decl_span(decl),
                format!("{name}: {message}"),
            ),
            LeafOutcome::Checked {
                name,
                warning: None,
                kernel_failures_delta,
                ..
            } if *kernel_failures_delta > 0 => (
                CleanBackend::get_decl_span(decl),
                format!("{name}: kernel check failures: {kernel_failures_delta}"),
            ),
            _ => return,
        };
        self.errors.push(TypeError {
            start,
            end,
            message,
            related: Vec::new(),
        });
    }

    fn after_decl(
        &mut self,
        _file_ctx: &FileContext,
        _decl: &SurfaceDecl,
        _budget: &BudgetReading,
    ) {
        let pending = std::mem::take(&mut self.pending_warnings);
        self.warnings.extend(pending);
    }
}

impl CleanBackend {
    /// Elaborate text into an ElaboratedDocument through the module driver.
    ///
    /// Runs `clean_elab::module_driver::elaborate_decls` — the loop
    /// `clean check` runs — on a per-document scratch
    /// environment clone so that:
    /// 1. later declarations in the same file see earlier registrations AND
    ///    the file's namespace / `open` / `variable` / section state
    /// 2. registration-derived sorry warnings reach LSP diagnostics
    /// 3. a failed declaration leaks no partial state
    ///    (`FailureIsolation::Rollback`); a type whose `deriving` class
    ///    failed stays declared, as in Lean and `clean check`, and the class
    ///    is an error leaf of its own
    /// 4. a failing member of a block is an error at its own span
    ///
    /// The incremental cache is intentionally bypassed in this path because the
    /// cache cannot replay registration side effects. A later issue can add
    /// replayable caching if profiling shows this path is hot.
    ///
    /// When the file has an `import` header, the header is resolved as a unit
    /// through the process-wide import-closure cache (see
    /// [`super::imports::shared_import_closure`]) and the returned
    /// `Option<Arc<Environment>>` carries the loaded base environment so the
    /// caller can reuse it (e.g. for tactic snapshots); the driver then skips
    /// the `import` declarations (`ImportHandling::Preloaded`). `file_path` is
    /// the document's on-disk location, used to derive project-local `.olean`
    /// search paths; `None` for non-`file:` documents.
    ///
    /// Runs synchronously on the blocking pool ([`Self::elaborate_document`]
    /// wraps it in `spawn_blocking`): the `.olean` import-closure load is
    /// synchronous and must not pin an executor thread, so nothing here may
    /// touch the async runtime. Per-declaration `$/lean/fileProgress` shrink
    /// events — before each declaration after the first, the still-processing
    /// range is reduced to start at that declaration — are pushed through
    /// `progress` for the async caller to forward (the leading whole-file
    /// notification comes from [`CleanBackend::check_document_parse_phase`]).
    /// `fallback_env` is the base environment for the rare case where the
    /// shared prelude closure fails to initialize.
    pub(super) fn elaborate_text_blocking(
        text: &str,
        _prev_state: IncrementalState,
        file_path: Option<&std::path::Path>,
        tactic_patterns: &clean_parser::TacticPatterns,
        fallback_env: Environment,
        progress: &tokio::sync::mpsc::UnboundedSender<Vec<LeanFileProgressProcessingInfo>>,
    ) -> (
        ElaboratedDocument,
        IncrementalState,
        Option<std::sync::Arc<Environment>>,
        Vec<clean_elab::tactic::TacticGoalObservation>,
    ) {
        let Ok(parsed) = clean_parser::parse_file_with_tactics_diagnostics(text, tactic_patterns)
        else {
            return (
                ElaboratedDocument {
                    errors: vec![],
                    warnings: vec![],
                    declarations: vec![],
                    term_infos: Vec::new(),
                    holes: vec![],
                    widget_modules: vec![],
                },
                IncrementalState::default(),
                None,
                Vec::new(),
            );
        };

        let header = parsed.header;
        let decls = parsed.decls;
        let mut errors = Vec::new();
        let new_cache = HashMap::new();
        let stats = IncrementalStats {
            total_commands: decls.len(),
            elaborated_count: decls.len(),
            // Intentionally 0: cache is bypassed during scratch registration
            // because the cache cannot replay registration side effects (#2643).
            cached_count: 0,
        };
        let deprecated_names = collect_deprecated_names(&decls);

        // Resolve the file's import header ONCE through the process-wide
        // closure cache (prelude base + shared `.olean` loader) so every
        // document sharing a header shares one loaded environment and a
        // keystroke never re-reads the `.olean` graph. On load failure a
        // single "imports unavailable" diagnostic replaces the flood of
        // per-declaration unknown-constant errors that elaborating against a
        // bare environment would produce.
        let import_paths = super::imports::import_paths_of_decls(&decls);
        let mut import_env: Option<std::sync::Arc<Environment>> = None;
        if !import_paths.is_empty() {
            match super::imports::shared_import_closure(&import_paths, file_path) {
                Ok(env) => import_env = Some(env),
                Err(reason) => {
                    let (start, end) = decls
                        .iter()
                        .find(|decl| matches!(decl, SurfaceDecl::Import { .. }))
                        .map(Self::get_decl_span)
                        .unwrap_or((0, 0));
                    errors.push(TypeError {
                        start,
                        end,
                        message: format!("imports unavailable: {reason}"),
                        related: Vec::new(),
                    });
                }
            }
        } else {
            // Import-free documents still get the PRELUDE floor (an empty
            // import set through the same process-wide cache), matching how a
            // real Lean editor session always sees the prelude — `def f : Nat
            // → Nat` in a scratch file must resolve `Nat`. Init-and-beyond
            // names correctly stay unknown until imported. If prelude
            // initialization itself fails we fall back to the bare server
            // env rather than erroring the document.
            if let Ok(env) = super::imports::shared_import_closure(&[], None) {
                import_env = Some(env);
            }
        }

        // Clone the base environment into a per-document scratch copy so we
        // can mutate it for registration without affecting the global server
        // state (or the shared import closure).
        let mut scratch_env = match &import_env {
            Some(env) => (**env).clone(),
            None => fallback_env,
        };

        let mut observer = DocumentObserver {
            text,
            end_of_file: byte_offset_to_position(text, text.len()),
            progress,
            deprecated_names: &deprecated_names,
            errors,
            warnings: Vec::new(),
            declarations: Vec::new(),
            declaration_terms: Vec::new(),
            holes: Vec::new(),
            widget_modules: Vec::new(),
            pending_warnings: Vec::new(),
        };
        // The `FileContext` `clean check` starts a file from. Its import
        // settings are inert here: the header was loaded above and the driver
        // skips `import` declarations.
        let mut file_ctx = file_path.map_or_else(FileContext::new, module_file_context);
        file_ctx.set_file_header(&header);
        for import in &import_paths {
            file_ctx.record_compiler_import(import.name());
        }
        let tactic_goals = clean_elab::tactic::TacticGoalCapture::default();
        let term_info = clean_elab::term_info::TermInfoCapture::default();
        file_ctx.set_tactic_goal_capture(Some(tactic_goals.clone()));
        file_ctx.set_term_info_capture(Some(term_info.clone()));
        let (tactic_observations, term_infos) = {
            let _lock = module_elaboration_lock();
            elaborate_decls(
                &mut scratch_env,
                &decls,
                text,
                &mut file_ctx,
                DriverOptions {
                    imports: ImportHandling::Preloaded,
                    isolation: FailureIsolation::Rollback,
                    lean_front_door: true,
                },
                &mut observer,
            );
            // The read-only work observes captured clones after registration.
            // Keep the driver's lock while checking them: kernel attribution
            // counters are shared with other document elaborations.
            let tactic_observations = match tactic_goals.take() {
                Ok(observations) => observations,
                Err(error) => {
                    tracing::warn!(%error, "tactic goal observations unavailable");
                    Vec::new()
                }
            };
            let term_infos = match term_info.take() {
                Ok(mut contexts) => {
                    super::declaration_term_info::append(
                        &mut contexts,
                        std::mem::take(&mut observer.declaration_terms),
                    );
                    contexts
                        .into_iter()
                        .map(|info| crate::document::SourceInfo {
                            id: info.id,
                            parent_id: info.parent_id,
                            start: info.span.start,
                            end: info.span.end,
                            application_head: info
                                .application_head
                                .map(|span| (span.start, span.end)),
                            is_variable: info.is_variable,
                            is_partial: info.is_partial,
                            goal: info.term.map(|term| term.render_goal(&scratch_env)),
                        })
                        .collect()
                }
                Err(error) => {
                    tracing::warn!(%error, "term goal observations unavailable");
                    Vec::new()
                }
            };
            (tactic_observations, term_infos)
        };

        let new_state = IncrementalState {
            cache: new_cache,
            stats,
        };

        (
            ElaboratedDocument {
                errors: observer.errors,
                warnings: observer.warnings,
                declarations: observer.declarations,
                term_infos,
                holes: observer.holes,
                widget_modules: observer.widget_modules,
            },
            new_state,
            import_env,
            tactic_observations,
        )
    }

    /// Append document-level hole contexts for the elaborator-reported holes,
    /// skipping any with a dummy `(0, 0)` span.
    ///
    /// A dummy span means the elaborator could not recover the `_` source
    /// position (e.g. a hole synthesized through a macro roundtrip that did not
    /// preserve it). Surfacing such a hole would attach a spurious goal at
    /// document offset 0, so it is dropped rather than mislocated.
    fn push_hole_contexts(
        holes: &mut Vec<crate::document::HoleContext>,
        elaborated: &[clean_elab::HoleContext],
    ) {
        for hole in elaborated {
            if hole.span.start == 0 && hole.span.end == 0 {
                continue;
            }
            let (expected_type, local_bindings) = hole.render();
            holes.push(crate::document::HoleContext {
                start: hole.span.start,
                end: hole.span.end,
                expected_type,
                local_bindings,
            });
        }
    }

    /// Whether `decl` carries the `@[widget_module]` attribute that marks a
    /// declaration as a user-defined infoview panel widget in Lean 4.
    ///
    /// `@[widget_module]` is not a builtin attribute the parser models, so it
    /// arrives as `Attribute::Unknown("widget_module")` on the declaration's
    /// attribute list. Only the declaration forms that carry an `attrs` list
    /// (`def`, `theorem`, `axiom`, `opaque`) can bear the attribute; the
    /// canonical Lean form is `@[widget_module] def myWidget : Widget.Module`.
    pub(crate) fn is_widget_module_decl(decl: &SurfaceDecl) -> bool {
        use clean_parser::{Attribute, SurfaceDecl};
        let attrs = match decl {
            SurfaceDecl::Def { attrs, .. }
            | SurfaceDecl::Alias { attrs, .. }
            | SurfaceDecl::Theorem { attrs, .. }
            | SurfaceDecl::Axiom { attrs, .. }
            | SurfaceDecl::Opaque { attrs, .. } => attrs,
            _ => return false,
        };
        attrs
            .iter()
            .any(|attr| matches!(attr, Attribute::Unknown(name) if name == "widget_module"))
    }

    /// Extract elaboration info from an ElabResult.
    ///
    /// `type_str` is rendered with the kernel pretty-printer (`Display for
    /// Expr`), the same form used for captured hole goals. Hover, completion
    /// detail, signature help and code lenses show Lean syntax (`Nat -> Nat`),
    /// never Rust `Debug`
    /// structure (`Pi(.., Const(..), ..)`). Signature help extracts parameter
    /// domains from this form via `signature_arrow_parameter_domains`; the
    /// `Pi(`-shaped Debug parser remains only as a fallback.
    fn extract_elab_info(
        result: &clean_elab::ElabResult,
        decl: &SurfaceDecl,
    ) -> Option<ElaboratedDecl> {
        use clean_elab::ElabResult;

        let (start, end) = Self::get_decl_span(decl);

        // The declaration itself — also when it lifted `where` / `let rec`
        // helpers, or has failed `deriving` classes beside it
        // (`ElabResult::primary_leaf`).
        match result.primary_leaf()? {
            ElabResult::Definition { name, ty, .. }
            | ElabResult::Theorem { name, ty, .. }
            | ElabResult::Axiom { name, ty, .. }
            | ElabResult::Opaque { name, ty, .. }
            | ElabResult::Inductive { name, ty, .. }
            | ElabResult::Structure { name, ty, .. }
            | ElabResult::Instance { name, ty, .. } => {
                // A private declaration of a named module is registered as
                // `_private.<module>.0.<name>` (G21); the editor shows and
                // looks it up by the name the source writes, as Lean's hover
                // does (`pp.privateNames false`), and so does its type.
                let user = clean_elab::private_names::user_facing_name(name);
                Some(ElaboratedDecl {
                    name: clean_parser::SurfaceName::from_name(user.clone())
                        .source_spelling()
                        .unwrap_or_else(|| format!("{user:?}")),
                    identity: user,
                    type_str: clean_elab::private_names::user_facing_expr(ty).to_string(),
                    start,
                    end,
                })
            }
            _ => None,
        }
    }
}

#[cfg(test)]
#[path = "document_elab_tests.rs"]
mod tests;
