// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Document lifecycle operations: parsing, elaboration, diagnostics generation,
//! and shared declaration-classification / content-hash helpers.

use super::warnings::{
    collect_deprecated_names, detect_deprecated_usage, detect_duplicate_binders,
    detect_sorry_warnings, detect_unused_variables, merge_registration_sorry_warning,
};
use super::{
    byte_offset_to_position, CleanBackend, DefinitionInfo, TacticGoalSnapshot,
    TacticSnapshotBridgeGap,
};
use crate::document::{
    CommandKind, ElaboratedDecl, ElaboratedDocument, IncrementalState, IncrementalStats,
    ParseError, ParsedCommand, ParsedDocument, TypeError,
};
use crate::file_progress::{
    LeanFileProgress, LeanFileProgressParams, LeanFileProgressProcessingInfo,
};
use clean_parser::{SurfaceBinder, SurfaceDecl, SurfaceExpr, SurfaceTactic};
use std::collections::HashMap;
use tower_lsp::lsp_types::*;

impl CleanBackend {
    /// Parse a document and update its state
    pub(crate) async fn parse_document(&self, uri: &Url) {
        if let Some(mut doc) = self.documents.get_mut(uri) {
            let text = doc.text();
            let parsed = self.parse_text(&text);

            // Update definition index
            self.update_definitions(uri, &text, &parsed);

            doc.parsed = Some(parsed);
        }
    }

    /// Update the definition index with definitions from a document
    fn update_definitions(&self, uri: &Url, text: &str, parsed: &ParsedDocument) {
        // First, remove all definitions from this URI
        let to_remove: Vec<String> = self
            .definitions
            .iter()
            .filter(|entry| &entry.value().uri == uri)
            .map(|entry| entry.key().clone())
            .collect();

        for name in to_remove {
            self.definitions.remove(&name);
        }

        // Add new definitions
        for cmd in &parsed.commands {
            if let Some(name) = &cmd.name {
                // Only index definition-like commands
                match cmd.kind {
                    CommandKind::Definition
                    | CommandKind::Theorem
                    | CommandKind::Lemma
                    | CommandKind::Inductive
                    | CommandKind::Structure
                    | CommandKind::Class
                    | CommandKind::Instance
                    | CommandKind::Axiom => {
                        let (name_start, name_end) = Self::definition_name_span(text, cmd, name)
                            .unwrap_or((cmd.start, cmd.start));
                        self.definitions.insert(
                            name.clone(),
                            DefinitionInfo {
                                uri: uri.clone(),
                                start: cmd.start,
                                end: cmd.end,
                                name_start,
                                name_end,
                            },
                        );
                    }
                    _ => {}
                }
            }
        }
    }

    fn definition_name_span(text: &str, cmd: &ParsedCommand, name: &str) -> Option<(usize, usize)> {
        if let Some(command_text) = text.get(cmd.start..cmd.end) {
            if let Some(span) =
                Self::identifier_name_span_in_text(text, command_text, cmd.start, name)
            {
                return Some(span);
            }
        }

        Self::identifier_name_span_in_text(text, text, 0, name)
    }

    pub(crate) fn identifier_name_span_in_text(
        full_text: &str,
        search_text: &str,
        base_offset: usize,
        name: &str,
    ) -> Option<(usize, usize)> {
        let mut search_pos = 0;
        while let Some(found_pos) = search_text.get(search_pos..)?.find(name) {
            let abs_pos = base_offset + search_pos + found_pos;
            let end_pos = abs_pos + name.len();
            let is_start_boundary = abs_pos == 0
                || full_text
                    .get(..abs_pos)
                    .and_then(|prefix| prefix.chars().next_back())
                    .is_none_or(|ch| !Self::is_identifier_continue(ch));
            let is_end_boundary = end_pos >= full_text.len()
                || full_text
                    .get(end_pos..)
                    .and_then(|suffix| suffix.chars().next())
                    .is_none_or(|ch| !Self::is_identifier_continue(ch));

            if is_start_boundary && is_end_boundary {
                return Some((abs_pos, end_pos));
            }

            let next_char = search_text.get(search_pos + found_pos..)?.chars().next()?;
            search_pos += found_pos + next_char.len_utf8();
        }

        None
    }

    /// Parse text into a ParsedDocument
    pub(crate) fn parse_text(&self, text: &str) -> ParsedDocument {
        match clean_parser::parse_file_with_tactics_diagnostics(text, &self.tactic_patterns) {
            Ok(report) => {
                let mut commands = Vec::new();

                for decl in &report.decls {
                    let (kind, name, span) = Self::classify_decl(decl);
                    let content_hash = Self::compute_content_hash(text, span.0, span.1);
                    commands.push(ParsedCommand {
                        kind,
                        start: span.0,
                        end: span.1,
                        name,
                        content_hash,
                    });
                }

                let errors = report
                    .diagnostics
                    .into_iter()
                    .map(|diag| ParseError {
                        start: diag.recovery_start.byte,
                        end: diag.recovered_at.byte.max(diag.recovery_start.byte + 1),
                        message: diag.message,
                        related: Vec::new(),
                    })
                    .collect();

                ParsedDocument { errors, commands }
            }
            Err(e) => {
                let message = format!("{e}");
                ParsedDocument {
                    errors: vec![ParseError {
                        start: 0,
                        end: 1,
                        message,
                        related: Vec::new(),
                    }],
                    commands: vec![],
                }
            }
        }
    }

    /// Compute a hash of the source text for a span
    pub(crate) fn compute_content_hash(text: &str, start: usize, end: usize) -> u64 {
        use std::hash::{Hash, Hasher};
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        if start < text.len() && end <= text.len() && start <= end {
            text[start..end].hash(&mut hasher);
        }
        hasher.finish()
    }

    /// Classify a parsed declaration
    pub(crate) fn classify_decl(
        decl: &SurfaceDecl,
    ) -> (CommandKind, Option<String>, (usize, usize)) {
        use clean_parser::SurfaceDecl;

        match decl {
            SurfaceDecl::Def { span, name, .. } => (
                CommandKind::Definition,
                Some(name.clone()),
                (span.start, span.end),
            ),
            SurfaceDecl::Theorem { span, name, .. } => (
                CommandKind::Theorem,
                Some(name.clone()),
                (span.start, span.end),
            ),
            SurfaceDecl::Example { span, .. } => {
                (CommandKind::Example, None, (span.start, span.end))
            }
            SurfaceDecl::Inductive { span, name, .. } => (
                CommandKind::Inductive,
                Some(name.clone()),
                (span.start, span.end),
            ),
            SurfaceDecl::Coinductive { span, name, .. } => (
                CommandKind::Coinductive,
                Some(name.clone()),
                (span.start, span.end),
            ),
            SurfaceDecl::Codata { span, name, .. } => (
                CommandKind::Coinductive,
                Some(name.clone()),
                (span.start, span.end),
            ),
            SurfaceDecl::Codef { span, name, .. } => (
                CommandKind::Definition,
                Some(name.clone()),
                (span.start, span.end),
            ),
            SurfaceDecl::Structure { span, name, .. } => (
                CommandKind::Structure,
                Some(name.clone()),
                (span.start, span.end),
            ),
            SurfaceDecl::Class { span, name, .. } => (
                CommandKind::Class,
                Some(name.clone()),
                (span.start, span.end),
            ),
            SurfaceDecl::Instance { span, name, .. } => {
                (CommandKind::Instance, name.clone(), (span.start, span.end))
            }
            SurfaceDecl::Axiom { span, name, .. } => (
                CommandKind::Axiom,
                Some(name.clone()),
                (span.start, span.end),
            ),
            SurfaceDecl::Opaque { span, name, .. } => (
                CommandKind::Other("opaque".to_string()),
                Some(name.clone()),
                (span.start, span.end),
            ),
            SurfaceDecl::Variable { span, binders, .. } => {
                let name = binders.first().map(|b| b.name.clone());
                (CommandKind::Variable, name, (span.start, span.end))
            }
            // `include x` / `omit x` steer which section `variable`s the
            // following declarations receive, so the editor reports them as
            // the variable-scope commands they are.
            SurfaceDecl::IncludeVars { span, names } => (
                CommandKind::Other("include".to_string()),
                names.first().cloned(),
                (span.start, span.end),
            ),
            SurfaceDecl::OmitVars { span, names } => (
                CommandKind::Other("omit".to_string()),
                names.first().cloned(),
                (span.start, span.end),
            ),
            SurfaceDecl::UniverseDecl { span, names, .. } => (
                CommandKind::Universe,
                names.first().cloned(),
                (span.start, span.end),
            ),
            SurfaceDecl::Import { span, .. } => (CommandKind::Import, None, (span.start, span.end)),
            SurfaceDecl::Open { span, .. } => (CommandKind::Open, None, (span.start, span.end)),
            SurfaceDecl::Export { span, .. } => (
                CommandKind::Other("export".to_string()),
                None,
                (span.start, span.end),
            ),
            SurfaceDecl::DerivingInstance { span, .. } => (
                CommandKind::Other("deriving instance".to_string()),
                None,
                (span.start, span.end),
            ),
            SurfaceDecl::Namespace { span, name, .. } => (
                CommandKind::Namespace,
                Some(name.clone()),
                (span.start, span.end),
            ),
            SurfaceDecl::Section { span, name, .. } => {
                (CommandKind::Section, name.clone(), (span.start, span.end))
            }
            SurfaceDecl::Check { span, .. } => (
                CommandKind::Other("check".to_string()),
                None,
                (span.start, span.end),
            ),
            SurfaceDecl::Eval { span, .. } => (
                CommandKind::Other("eval".to_string()),
                None,
                (span.start, span.end),
            ),
            SurfaceDecl::Print { span, .. } => (
                CommandKind::Other("print".to_string()),
                None,
                (span.start, span.end),
            ),
            SurfaceDecl::Mutual { span, .. } => (
                CommandKind::Other("mutual".to_string()),
                None,
                (span.start, span.end),
            ),
            SurfaceDecl::Syntax { span, .. } => (
                CommandKind::Other("syntax".to_string()),
                None,
                (span.start, span.end),
            ),
            SurfaceDecl::DeclareSyntaxCat { span, .. } => (
                CommandKind::Other("declare_syntax_cat".to_string()),
                None,
                (span.start, span.end),
            ),
            SurfaceDecl::Macro { span, .. } => (
                CommandKind::Other("macro".to_string()),
                None,
                (span.start, span.end),
            ),
            SurfaceDecl::MacroRules { span, .. } => (
                CommandKind::Other("macro_rules".to_string()),
                None,
                (span.start, span.end),
            ),
            SurfaceDecl::Notation { span, .. } => (
                CommandKind::Other("notation".to_string()),
                None,
                (span.start, span.end),
            ),
            SurfaceDecl::Attribute { span, .. } => (
                CommandKind::Other("attribute".to_string()),
                None,
                (span.start, span.end),
            ),
            SurfaceDecl::Elab { span, .. } => (
                CommandKind::Other("elab".to_string()),
                None,
                (span.start, span.end),
            ),
            SurfaceDecl::RawDecl { span, .. } => (
                CommandKind::Other("raw".to_string()),
                None,
                (span.start, span.end),
            ),
            SurfaceDecl::SetOption { span, .. } => (
                CommandKind::Other("set_option".to_string()),
                None,
                (span.start, span.end),
            ),
            SurfaceDecl::DeclareAesopRuleSets { span, .. } => (
                CommandKind::Other("declare_aesop_rule_sets".to_string()),
                None,
                (span.start, span.end),
            ),
            SurfaceDecl::LibraryNote { span, .. } => (
                CommandKind::Other("library_note".to_string()),
                None,
                (span.start, span.end),
            ),
        }
    }

    /// Get the span of a declaration
    pub(crate) fn get_decl_span(decl: &SurfaceDecl) -> (usize, usize) {
        Self::classify_decl(decl).2
    }

    /// Elaborate a document and update its state (with incremental checking).
    ///
    /// Structured as read / compute / commit so the `documents` map guard is
    /// never held across elaboration: holding `get_mut` across that await
    /// serialized every other document behind the DashMap shard lock for the
    /// whole run (measured 96.1 s on an import-heavy file). The compute phase
    /// runs on the blocking pool because the `.olean` import-closure load
    /// inside it is synchronous and must not pin an executor thread.
    pub(crate) async fn elaborate_document(&self, uri: &Url) {
        // Read: capture elaboration inputs under a short-lived guard.
        let (text, version, prev_state) = {
            let Some(mut doc) = self.documents.get_mut(uri) else {
                return;
            };
            if let Some(parsed) = &doc.parsed {
                if !parsed.errors.is_empty() {
                    doc.elaborated = Some(ElaboratedDocument {
                        errors: vec![],
                        warnings: vec![],
                        declarations: vec![],
                        holes: vec![],
                        widget_modules: vec![],
                    });
                    self.tactic_goal_snapshots.remove(uri);
                    return;
                }
            }
            let text = doc.text();
            let prev_state = std::mem::take(&mut doc.incremental_state);
            (text, doc.version, prev_state)
        };

        // Compute: no document guard held. `spawn_blocking` needs owned
        // (`'static`) inputs, so the closure gets its own copies; fileProgress
        // shrink events come back over a channel because the notification
        // client must stay on the async side.
        let file_path = uri.to_file_path().ok();
        let tactic_patterns = self.tactic_patterns.clone();
        // Base for the rare case where the shared prelude closure fails to
        // initialize; cloned ahead because the blocking closure cannot await
        // the RwLock.
        let fallback_env = self.env.read().await.clone();
        let (progress_tx, mut progress_rx) = tokio::sync::mpsc::unbounded_channel();
        let task_text = text.clone();
        let mut compute = tokio::task::spawn_blocking(move || {
            Self::elaborate_text_blocking(
                &task_text,
                prev_state,
                file_path.as_deref(),
                &tactic_patterns,
                fallback_env,
                &progress_tx,
            )
        });
        let outcome = loop {
            tokio::select! {
                joined = &mut compute => break joined,
                event = progress_rx.recv() => match event {
                    Some(processing) => {
                        self.send_file_progress(uri, version, processing).await;
                    }
                    // Sender dropped: the compute task is finishing; take its
                    // result.
                    None => break (&mut compute).await,
                },
            }
        };
        // Shrink events still queued when the task finished must precede the
        // terminal notification the elaboration phase sends after this returns.
        while let Ok(processing) = progress_rx.try_recv() {
            self.send_file_progress(uri, version, processing).await;
        }
        // A panicked/aborted compute task has no result to commit; the
        // document keeps its pre-elaboration state.
        let Ok((elaborated, new_state, import_env)) = outcome else {
            return;
        };

        // Tactic snapshots run against the same base the declarations
        // elaborated against: the shared import closure when the file has
        // an import header, the (near-empty) server environment otherwise.
        let shared_env;
        let env: &clean_kernel::Environment = match &import_env {
            Some(imported) => imported,
            None => {
                shared_env = self.env.read().await.clone();
                &shared_env
            }
        };
        self.commit_elaboration(
            uri,
            version,
            &text,
            elaborated,
            new_state,
            env,
            import_env.clone(),
        );
    }

    /// Commit an elaboration result computed off-guard, unless the document
    /// moved on while it was being computed. Returns whether the result was
    /// stored: a version mismatch (or a closed document) discards it as stale
    /// — the `didChange` that bumped the version owns the state and its own
    /// document check supersedes this one.
    ///
    /// `imports_env` is the shared import closure the result elaborated
    /// against; it is stored on the document so synchronous request handlers
    /// (hover) can resolve imported constants without running the blocking
    /// closure loader themselves. `None` when the document elaborated against
    /// the bare server environment.
    pub(crate) fn commit_elaboration(
        &self,
        uri: &Url,
        elaborated_version: i32,
        text: &str,
        elaborated: ElaboratedDocument,
        new_state: IncrementalState,
        env: &clean_kernel::Environment,
        imports_env: Option<std::sync::Arc<clean_kernel::Environment>>,
    ) -> bool {
        let Some(mut doc) = self.documents.get_mut(uri) else {
            return false;
        };
        if doc.version != elaborated_version {
            return false;
        }
        let snapshots = Self::tactic_goal_snapshots_from_text(&doc, text, env);
        doc.elaborated = Some(elaborated);
        doc.incremental_state = new_state;
        doc.imports_env = imports_env;

        if snapshots.is_empty() {
            self.tactic_goal_snapshots.remove(uri);
        } else {
            self.tactic_goal_snapshots.insert(uri.clone(), snapshots);
        }
        true
    }

    fn tactic_goal_snapshots_from_text(
        doc: &crate::document::Document,
        text: &str,
        env: &clean_kernel::Environment,
    ) -> Vec<TacticGoalSnapshot> {
        let Ok(decls) =
            clean_parser::parse_file_with_tactics(text, &Self::builtin_tactic_patterns())
        else {
            return Vec::new();
        };

        decls
            .iter()
            .filter_map(|decl| Self::tactic_goal_snapshot_from_decl(doc, text, env, decl))
            .collect()
    }

    pub(crate) fn builtin_tactic_patterns() -> clean_parser::TacticPatterns {
        clean_elab::tactic::builtins::builtin_tactic_patterns()
    }

    fn tactic_goal_snapshot_from_decl(
        doc: &crate::document::Document,
        text: &str,
        env: &clean_kernel::Environment,
        decl: &SurfaceDecl,
    ) -> Option<TacticGoalSnapshot> {
        match decl {
            SurfaceDecl::Theorem {
                binders, ty, proof, ..
            } => Self::tactic_goal_snapshot_from_theorem(doc, text, env, binders, ty, proof),
            SurfaceDecl::Example {
                ty: Some(ty), val, ..
            } => Self::tactic_goal_snapshot_from_type_and_proof(doc, text, env, ty, val),
            _ => None,
        }
    }

    /// Tactic snapshot for a theorem declaration. Binder-free theorems use the
    /// shared type-and-proof path (typed post-tactic snapshot when the target
    /// elaborates, source-rendered initial goal otherwise). Bound theorems get
    /// the source-rendered initial goal only: `proof_state_for_tactic_target`
    /// still elaborates the bare target with no binder telescope, so the
    /// recorded bridge gap keeps the typed post-tactic path fail-closed.
    pub(crate) fn tactic_goal_snapshot_from_theorem(
        doc: &crate::document::Document,
        text: &str,
        env: &clean_kernel::Environment,
        binders: &[SurfaceBinder],
        ty: &SurfaceExpr,
        proof: &SurfaceExpr,
    ) -> Option<TacticGoalSnapshot> {
        if binders.is_empty() {
            return Self::tactic_goal_snapshot_from_type_and_proof(doc, text, env, ty, proof);
        }
        Self::post_tactic_snapshot_bridge_gap_from_theorem(doc, text, binders, ty, proof)?;
        Self::initial_goal_snapshot_from_bound_theorem(doc, text, binders, ty, proof)
    }

    /// Initial (pre-tactic) goal for a bound theorem: one `name : ty`
    /// hypothesis line per binder above `⊢ target`, all rendered from source
    /// spans — no typed-ProofState claim is made.
    ///
    /// Fail-closed: a binder without a source-renderable type annotation
    /// suppresses the snapshot rather than showing a wrong local context.
    fn initial_goal_snapshot_from_bound_theorem(
        doc: &crate::document::Document,
        text: &str,
        binders: &[SurfaceBinder],
        ty: &SurfaceExpr,
        proof: &SurfaceExpr,
    ) -> Option<TacticGoalSnapshot> {
        let proof_span = match proof {
            SurfaceExpr::ByTactic(span, tactics) if !tactics.is_empty() => *span,
            _ => return None,
        };
        let ty_span = ty.span();
        let target = text.get(ty_span.start..ty_span.end)?.trim();
        if target.is_empty() {
            return None;
        }

        // A surface expression's own span can stop at its HEAD — an instance
        // binder `[Decidable p]` parses as an App whose span covers only
        // `Decidable`, so slicing by `.span()` rendered `inst : Decidable`
        // and dropped the argument. Take the maximum end across the
        // expression's sub-spans instead.
        fn span_extent(e: &SurfaceExpr) -> usize {
            match e {
                SurfaceExpr::App(span, f, args) => args
                    .iter()
                    .map(|a| span_extent(&a.expr))
                    .chain([span.end, span_extent(f)])
                    .max()
                    .unwrap_or(span.end),
                SurfaceExpr::Arrow(span, dom, cod) => {
                    span.end.max(span_extent(dom)).max(span_extent(cod))
                }
                SurfaceExpr::Paren(span, inner) => span.end.max(span_extent(inner)),
                other => other.span().end,
            }
        }

        let mut lines = Vec::with_capacity(binders.len() + 1);
        for binder in binders {
            let binder_ty = binder.ty.as_deref()?;
            let start = binder_ty.span().start;
            let end = span_extent(binder_ty);
            let rendered_ty = text.get(start..end)?.trim();
            if binder.name.is_empty() || rendered_ty.is_empty() {
                return None;
            }
            lines.push(format!("{} : {rendered_ty}", binder.name));
        }
        lines.push(format!("⊢ {target}"));

        Some(TacticGoalSnapshot {
            range: Range::new(
                doc.offset_to_position(proof_span.start),
                doc.offset_to_position(proof_span.end),
            ),
            goals: vec![lines.join("\n")],
        })
    }

    fn tactic_goal_snapshot_from_type_and_proof(
        doc: &crate::document::Document,
        text: &str,
        env: &clean_kernel::Environment,
        ty: &SurfaceExpr,
        proof: &SurfaceExpr,
    ) -> Option<TacticGoalSnapshot> {
        if let Some(snapshot) =
            Self::post_tactic_goal_snapshot_from_type_and_proof(doc, text, env, ty, proof)
        {
            return Some(snapshot);
        }

        let proof_span = match proof {
            SurfaceExpr::ByTactic(span, tactics) if !tactics.is_empty() => *span,
            _ => return None,
        };
        let ty_span = ty.span();
        let target = text.get(ty_span.start..ty_span.end)?.trim();
        if target.is_empty() {
            return None;
        }

        Some(TacticGoalSnapshot {
            range: Range::new(
                doc.offset_to_position(proof_span.start),
                doc.offset_to_position(proof_span.end),
            ),
            goals: vec![format!("⊢ {target}")],
        })
    }

    fn post_tactic_goal_snapshot_from_type_and_proof(
        doc: &crate::document::Document,
        text: &str,
        env: &clean_kernel::Environment,
        ty: &SurfaceExpr,
        proof: &SurfaceExpr,
    ) -> Option<TacticGoalSnapshot> {
        let bridge =
            Self::post_tactic_snapshot_bridge_gap_from_type_and_proof(doc, text, ty, proof)?;
        let byte_range = Self::post_tactic_snapshot_byte_range_from_type_and_proof(proof)?;
        let mut proof_state = clean_elab::tactic::proof_state_for_tactic_target(env, ty).ok()?;
        let snapshot_run = clean_elab::tactic::run_tactic_script_with_snapshots(
            &bridge.tactic_script,
            clean_elab::tactic::TacticPostSnapshotRange {
                start: byte_range.0,
                end: byte_range.1,
            },
            &mut proof_state,
            env,
        )
        .ok()?;
        // A run that admitted goals via `sorry` has no authoritative
        // post-tactic state: rendering its "no goals" at the tactic span
        // would display an admitted proof as solved. Return None so the
        // caller falls back to the pre-tactic target snapshot — Lean's
        // infoview shows the admitted goal at a `sorry`, not "No goals".
        if proof_state.trust_ledger().sorry_count > 0 {
            return None;
        }
        Some(TacticGoalSnapshot {
            range: bridge.post_tactic_range,
            goals: snapshot_run.snapshot.rendered_targets,
        })
    }

    fn post_tactic_snapshot_byte_range_from_type_and_proof(
        proof: &SurfaceExpr,
    ) -> Option<(usize, usize)> {
        let tactics = match proof {
            SurfaceExpr::ByTactic(_, tactics) if !tactics.is_empty() => tactics,
            _ => return None,
        };
        let post_tactic_span = tactics.last().map(SurfaceTactic::span)?;
        Some((post_tactic_span.start, post_tactic_span.end))
    }

    pub(crate) fn post_tactic_snapshot_bridge_gap_from_type_and_proof(
        doc: &crate::document::Document,
        text: &str,
        ty: &SurfaceExpr,
        proof: &SurfaceExpr,
    ) -> Option<TacticSnapshotBridgeGap> {
        let tactics = match proof {
            SurfaceExpr::ByTactic(_, tactics) if !tactics.is_empty() => tactics,
            _ => return None,
        };
        let post_tactic_span = tactics.last().map(SurfaceTactic::span)?;
        let ty_span = ty.span();
        let target_text = text.get(ty_span.start..ty_span.end)?.trim().to_string();
        let tactic_script = text
            .get(post_tactic_span.start..post_tactic_span.end)?
            .trim()
            .to_string();
        if target_text.is_empty() || tactic_script.is_empty() {
            return None;
        }

        Some(TacticSnapshotBridgeGap {
            post_tactic_range: Range::new(
                doc.offset_to_position(post_tactic_span.start),
                doc.offset_to_position(post_tactic_span.end),
            ),
            tactic_script,
            target_text,
            missing_input:
                "typed ProofState for clean_elab::tactic::run_tactic_script_with_snapshots",
        })
    }

    pub(crate) fn post_tactic_snapshot_bridge_gap_from_theorem(
        doc: &crate::document::Document,
        text: &str,
        binders: &[SurfaceBinder],
        ty: &SurfaceExpr,
        proof: &SurfaceExpr,
    ) -> Option<TacticSnapshotBridgeGap> {
        let mut gap =
            Self::post_tactic_snapshot_bridge_gap_from_type_and_proof(doc, text, ty, proof)?;
        if !binders.is_empty() {
            gap.missing_input = "theorem-local binder context for proof_state_for_tactic_target";
        }
        Some(gap)
    }

    /// Elaborate text into an ElaboratedDocument using scratch registration.
    ///
    /// Uses `elaborate_decl_and_register_with_warning` on a per-document scratch
    /// environment clone so that:
    /// 1. later declarations in the same file see earlier registrations
    /// 2. registration-derived sorry warnings reach LSP diagnostics
    /// 3. failed per-declaration registration does not leak partial state
    ///
    /// The incremental cache is intentionally bypassed in this path because the
    /// cache cannot replay registration side effects. A later issue can add
    /// replayable caching if profiling shows this path is hot.
    ///
    /// When the file has an `import` header, the header is resolved as a unit
    /// through the process-wide import-closure cache (see
    /// [`super::imports::shared_import_closure`]) and the returned
    /// `Option<Arc<Environment>>` carries the loaded base environment so the
    /// caller can reuse it (e.g. for tactic snapshots). `file_path` is the
    /// document's on-disk location, used to derive project-local `.olean`
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
    fn elaborate_text_blocking(
        text: &str,
        _prev_state: IncrementalState,
        file_path: Option<&std::path::Path>,
        tactic_patterns: &clean_parser::TacticPatterns,
        fallback_env: clean_kernel::Environment,
        progress: &tokio::sync::mpsc::UnboundedSender<Vec<LeanFileProgressProcessingInfo>>,
    ) -> (
        ElaboratedDocument,
        IncrementalState,
        Option<std::sync::Arc<clean_kernel::Environment>>,
    ) {
        let Ok(decls) = clean_parser::parse_file_with_tactics(text, tactic_patterns) else {
            return (
                ElaboratedDocument {
                    errors: vec![],
                    warnings: vec![],
                    declarations: vec![],
                    holes: vec![],
                    widget_modules: vec![],
                },
                IncrementalState::default(),
                None,
            );
        };

        let mut errors = Vec::new();
        let mut warnings = Vec::new();
        let mut declarations = Vec::new();
        let mut holes = Vec::new();
        let mut widget_modules = Vec::new();
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
        let mut import_env: Option<std::sync::Arc<clean_kernel::Environment>> = None;
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

        let end_of_file = byte_offset_to_position(text, text.len());

        for (decl_index, decl) in decls.iter().enumerate() {
            // Import declarations were handled above as one header unit (or
            // reported once as unavailable); skip them here so the
            // per-declaration path neither re-loads the closure on every
            // keystroke nor duplicates failure noise.
            if matches!(decl, SurfaceDecl::Import { .. }) {
                continue;
            }
            let (_kind, name, span) = Self::classify_decl(decl);
            let decl_name = name.as_deref().unwrap_or("<anonymous>");

            // fileProgress shrink: everything before this declaration is done;
            // the remainder of the file (this declaration onward) is still
            // being processed. The first declaration needs no extra event —
            // the parse phase already announced the whole file as processing.
            // Progress is advisory: a send failure only means the async
            // caller stopped listening, so the error is dropped.
            if decl_index > 0 {
                let processing_start = byte_offset_to_position(text, span.0);
                let _ = progress.send(vec![LeanFileProgressProcessingInfo::processing(
                    Range::new(processing_start, end_of_file),
                )]);
            }

            // Surface-level warnings (unused vars, literal sorry, deprecation)
            let mut cmd_warnings = Vec::new();
            cmd_warnings.extend(detect_unused_variables(decl));
            cmd_warnings.extend(detect_duplicate_binders(decl));
            cmd_warnings.extend(detect_sorry_warnings(decl));
            cmd_warnings.extend(detect_deprecated_usage(decl, &deprecated_names));

            // Use a tentative per-declaration clone so failed registration does
            // not leak partial state into later declarations.
            let mut decl_env = scratch_env.clone();

            match clean_elab::elaborate_decl_and_register_with_warning(&mut decl_env, decl) {
                Ok(registered) => {
                    // Record hole-local expected types for every user-written
                    // `_` hole the elaborator tagged with a source span. This
                    // covers nested / sub-term holes (e.g. `Nat.succ (_ : Nat)`)
                    // with the precise type the elaborator demanded at that hole,
                    // instantiated as far as it is solved.
                    Self::push_hole_contexts(&mut holes, &registered.hole_contexts);

                    if let Some(info) = Self::extract_elab_info(&registered.result, decl) {
                        // Record a hole-local expected type when the body is a
                        // bare `sorry`: the elaborator demands the declaration's
                        // own type there, so the hole-local goal is the
                        // declaration type at the hole's narrower span. Body `_`
                        // holes are already covered by `registered.hole_contexts`
                        // above, so this fallback handles only `sorry`, which the
                        // elaborator does not span-tag.
                        if let Some(hole_span) = Self::body_sorry_span(decl) {
                            holes.push(crate::document::HoleContext {
                                start: hole_span.start,
                                end: hole_span.end,
                                expected_type: info.type_str.clone(),
                                local_bindings: Vec::new(),
                            });
                        }
                        // Record a user-defined widget module when the
                        // declaration carries the `@[widget_module]` attribute.
                        if Self::is_widget_module_decl(decl) {
                            widget_modules.push(crate::document::WidgetModule {
                                name: info.name.clone(),
                                start: info.start,
                                end: info.end,
                            });
                        }
                        declarations.push(info);
                    }

                    // Merge surface warnings with the registration report
                    cmd_warnings = merge_registration_sorry_warning(
                        cmd_warnings,
                        registered.warning.as_ref(),
                        decl_name,
                        span,
                    );

                    // Commit the tentative environment on success
                    scratch_env = decl_env;
                }
                Err(e) => {
                    let (start, end) = Self::get_decl_span(decl);
                    errors.push(TypeError {
                        start,
                        end,
                        message: format!("{e}"),
                        related: Vec::new(),
                    });
                    // Even when registration fails (commonly because the
                    // declaration contains an unfilled `_` hole whose unsolved
                    // metavariable is a free variable the kernel rejects),
                    // recover the hole contexts by re-elaborating without
                    // registration. This is exactly the case an IDE needs: the
                    // user is hovering a hole they have not yet filled in.
                    let (_recovered, recovered_holes) =
                        clean_elab::elaborate_decl_capturing_holes(&scratch_env, decl);
                    Self::push_hole_contexts(&mut holes, &recovered_holes);
                    // decl_env is dropped — scratch_env stays unchanged
                }
            }

            warnings.extend(cmd_warnings);
        }

        let new_state = IncrementalState {
            cache: new_cache,
            stats,
        };

        (
            ElaboratedDocument {
                errors,
                warnings,
                declarations,
                holes,
                widget_modules,
            },
            new_state,
            import_env,
        )
    }

    /// Render a hole's elaborator-provided expected type to the same
    /// pretty-printed form used for declaration types (`extract_elab_info`),
    /// keeping `plainTermGoal` output consistent across hole-local and
    /// whole-declaration goals.
    fn render_hole_type(hole: &clean_elab::HoleContext) -> String {
        let ty = &hole.expected_type;
        format!("{ty}")
    }

    /// Render a hole's captured local hypotheses to pretty-printed
    /// `(name, type)` pairs, using the same renderer as the expected type so
    /// the local context displays consistently with the goal.
    fn render_hole_bindings(hole: &clean_elab::HoleContext) -> Vec<(String, String)> {
        hole.local_bindings
            .iter()
            .map(|(name, ty)| (name.clone(), format!("{ty}")))
            .collect()
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
            holes.push(crate::document::HoleContext {
                start: hole.span.start,
                end: hole.span.end,
                expected_type: Self::render_hole_type(hole),
                local_bindings: Self::render_hole_bindings(hole),
            });
        }
    }

    /// If the declaration's body is a bare `sorry`, return its source span.
    ///
    /// Body `_` holes are reported by the elaborator directly (via
    /// `RegisteredElabResult::hole_contexts`), so only `sorry` — which the
    /// elaborator does not span-tag — is handled here. The hole-local expected
    /// type for a body `sorry` is the declaration's own elaborated type.
    fn body_sorry_span(decl: &SurfaceDecl) -> Option<clean_parser::Span> {
        use clean_parser::SurfaceDecl;
        let body = match decl {
            SurfaceDecl::Def { val, .. } | SurfaceDecl::Example { val, .. } => val.as_ref(),
            SurfaceDecl::Theorem { proof, .. } => proof.as_ref(),
            SurfaceDecl::Opaque { val: Some(val), .. } => val.as_ref(),
            _ => return None,
        };
        Self::expr_sorry_span(body)
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
            | SurfaceDecl::Theorem { attrs, .. }
            | SurfaceDecl::Axiom { attrs, .. }
            | SurfaceDecl::Opaque { attrs, .. } => attrs,
            _ => return false,
        };
        attrs
            .iter()
            .any(|attr| matches!(attr, Attribute::Unknown(name) if name == "widget_module"))
    }

    /// The source span of `expr` when it is a literal `sorry`
    /// (`SurfaceExpr::Ident(_, "sorry")`). A parenthesized `sorry` unwraps to
    /// the inner expression. Synthetic, parser-generated sorry is excluded: it
    /// has no user-visible source token to navigate to. Explicit `_` holes are
    /// handled by the elaborator and intentionally not matched here.
    fn expr_sorry_span(expr: &SurfaceExpr) -> Option<clean_parser::Span> {
        use clean_parser::SurfaceExpr;
        match expr {
            SurfaceExpr::Ident(span, name) if name == "sorry" => Some(*span),
            SurfaceExpr::Paren(_, inner) => Self::expr_sorry_span(inner),
            _ => None,
        }
    }

    /// Extract elaboration info from an ElabResult.
    ///
    /// `type_str` is rendered with the kernel pretty-printer (`Display for
    /// Expr`), the same form used for hole goals, so every editor surface fed
    /// from it (hover, completion detail, signature help, code lenses,
    /// `plainTermGoal`) shows Lean syntax (`Nat -> Nat`), never Rust `Debug`
    /// structure (`Pi(.., Const(..), ..)`). Signature help extracts parameter
    /// domains from this form via `signature_arrow_parameter_domains`; the
    /// `Pi(`-shaped Debug parser remains only as a fallback.
    fn extract_elab_info(
        result: &clean_elab::ElabResult,
        decl: &SurfaceDecl,
    ) -> Option<ElaboratedDecl> {
        use clean_elab::ElabResult;

        let (start, end) = Self::get_decl_span(decl);

        match result {
            ElabResult::Definition { name, ty, .. }
            | ElabResult::Theorem { name, ty, .. }
            | ElabResult::Axiom { name, ty, .. }
            | ElabResult::Opaque { name, ty, .. }
            | ElabResult::Inductive { name, ty, .. }
            | ElabResult::Structure { name, ty, .. }
            | ElabResult::Instance { name, ty, .. } => Some(ElaboratedDecl {
                name: name.to_string(),
                type_str: format!("{ty}"),
                start,
                end,
            }),
            _ => None,
        }
    }

    /// Generate LSP diagnostics from a document.
    ///
    /// Delegates to the shared `diagnostics::generate_all_diagnostics` so that
    /// parse errors, type errors, **and** warnings are all published to the
    /// editor. Prior to #2643 this inline helper dropped warnings.
    pub(crate) fn generate_diagnostics(&self, doc: &crate::document::Document) -> Vec<Diagnostic> {
        crate::diagnostics::generate_all_diagnostics(doc)
    }

    /// Publish diagnostics for a document
    pub(crate) async fn publish_diagnostics(&self, uri: &Url) {
        if let Some(doc) = self.documents.get(uri) {
            let diagnostics = self.generate_diagnostics(&doc);
            self.client
                .publish_diagnostics(uri.clone(), diagnostics, Some(doc.version))
                .await;
        }
    }

    /// Send a `$/lean/fileProgress` notification for `uri` at `version`.
    ///
    /// A non-empty `processing` vector announces ranges still being
    /// elaborated; an empty vector is the terminal "file fully processed"
    /// notification. Mirrors Lean's `LeanFileProgressParams` wire shape.
    pub(crate) async fn send_file_progress(
        &self,
        uri: &Url,
        version: i32,
        processing: Vec<LeanFileProgressProcessingInfo>,
    ) {
        self.client
            .send_notification::<LeanFileProgress>(LeanFileProgressParams {
                text_document: VersionedTextDocumentIdentifier {
                    uri: uri.clone(),
                    version,
                },
                processing,
            })
            .await;
    }

    /// Parse phase of a document check: parse, publish parse-only diagnostics,
    /// and announce the whole file as processing.
    ///
    /// Together with [`Self::check_document_elaboration_phase`] this emits the
    /// Lean4-compatible `$/lean/fileProgress` sequence: a leading notification
    /// whose processing range covers the not-yet-elaborated file,
    /// per-declaration shrink notifications from `elaborate_text_blocking`, and
    /// a terminal notification with empty ranges once processing is done — the
    /// signal the Lean 4 VS Code extension uses to drive its progress bar and
    /// refresh the infoview. Parse diagnostics are published immediately, ahead
    /// of elaboration, whose cold import-closure load can take minutes; the
    /// full set (parse + type + warnings) published after the terminal
    /// notification replaces them.
    ///
    /// This is the part that must complete before a `didOpen`/`didChange`
    /// notification handler returns (parse-first): syntax feedback must not
    /// wait on elaboration. Returns the document version announced in the
    /// leading `$/lean/fileProgress` notification (`None` when the document
    /// is not open), which the elaboration phase echoes in the terminal
    /// notification.
    pub(crate) async fn check_document_parse_phase(&self, uri: &Url) -> Option<i32> {
        self.parse_document(uri).await;

        // Parse-phase feedback, ahead of elaboration. The map guard is
        // dropped before publishing: `publish_diagnostics` awaits the client.
        let parse_feedback = self.documents.get(uri).and_then(|doc| {
            let parsed = doc.parsed.as_ref()?;
            Some((
                doc.version,
                crate::diagnostics::generate_parse_diagnostics(&doc, parsed),
            ))
        });
        if let Some((version, diagnostics)) = parse_feedback {
            self.client
                .publish_diagnostics(uri.clone(), diagnostics, Some(version))
                .await;
        }

        let progress_target = self.documents.get(uri).map(|doc| {
            let text_len = doc.text().len();
            (
                doc.version,
                Range::new(Position::new(0, 0), doc.offset_to_position(text_len)),
            )
        });

        if let Some((version, full_range)) = progress_target {
            self.send_file_progress(
                uri,
                version,
                vec![LeanFileProgressProcessingInfo::processing(full_range)],
            )
            .await;
            Some(version)
        } else {
            None
        }
    }

    /// Elaboration phase of a document check: elaborate + commit,
    /// then send the terminal `$/lean/fileProgress` and publish the full
    /// diagnostics set (parse + type + warnings), replacing the parse-only
    /// publish from the parse phase.
    ///
    /// `generation` is the elaboration generation this run was scheduled
    /// under ([`Self::bump_elaboration_generation`]). When a newer check has
    /// bumped it — or the document was closed — the terminal notification
    /// and the diagnostics publish are skipped: the newer run owns them, and
    /// an empty terminal notification here would end the client's progress
    /// bar while that run is still elaborating. (`commit_elaboration`'s
    /// version check independently discards a stale *result*; this gate
    /// covers the *publishes*.)
    pub(crate) async fn check_document_elaboration_phase(
        &self,
        uri: &Url,
        generation: u64,
        announced_version: Option<i32>,
    ) {
        self.elaborate_document(uri).await;

        if !self.elaboration_generation_is_current(uri, generation) {
            return;
        }

        if let Some(version) = announced_version {
            self.send_file_progress(uri, version, Vec::new()).await;
        }

        self.publish_diagnostics(uri).await;
        self.finish_elaboration_task(uri, generation);
    }
}
