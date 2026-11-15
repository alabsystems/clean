// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Document lifecycle operations: parsing, elaboration, diagnostics generation,
//! and shared declaration-classification / content-hash helpers.

#[cfg(test)]
use super::TacticSnapshotBridgeGap;
use super::{CleanBackend, DefinitionInfo, TacticGoalSnapshot};
use crate::document::{
    CommandKind, ElaboratedDocument, IncrementalState, ParseError, ParsedCommand, ParsedDocument,
};
use crate::file_progress::{
    LeanFileProgress, LeanFileProgressParams, LeanFileProgressProcessingInfo,
};
use clean_parser::SurfaceDecl;
#[cfg(test)]
use clean_parser::{SurfaceBinder, SurfaceExpr, SurfaceTactic};
use std::cmp::Reverse;
use std::collections::{BTreeMap, HashMap};
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
                name.source_spelling(),
                (span.start, span.end),
            ),
            SurfaceDecl::Alias { span, names, .. } => (
                if names.iter().any(|(_, direction)| direction.is_some()) {
                    CommandKind::Theorem
                } else {
                    CommandKind::Definition
                },
                names.first().and_then(|(name, _)| name.source_spelling()),
                (span.start, span.end),
            ),
            SurfaceDecl::Theorem { span, name, .. } => (
                CommandKind::Theorem,
                name.source_spelling(),
                (span.start, span.end),
            ),
            SurfaceDecl::Example { span, .. } => {
                (CommandKind::Example, None, (span.start, span.end))
            }
            SurfaceDecl::Inductive { span, name, .. } => (
                CommandKind::Inductive,
                name.source_spelling(),
                (span.start, span.end),
            ),
            SurfaceDecl::Coinductive { span, name, .. } => (
                CommandKind::Coinductive,
                name.source_spelling(),
                (span.start, span.end),
            ),
            SurfaceDecl::Codata { span, name, .. } => (
                CommandKind::Coinductive,
                name.source_spelling(),
                (span.start, span.end),
            ),
            SurfaceDecl::Codef { span, name, .. } => (
                CommandKind::Definition,
                name.source_spelling(),
                (span.start, span.end),
            ),
            SurfaceDecl::Structure { span, name, .. } => (
                CommandKind::Structure,
                name.source_spelling(),
                (span.start, span.end),
            ),
            SurfaceDecl::Class { span, name, .. } => (
                CommandKind::Class,
                name.source_spelling(),
                (span.start, span.end),
            ),
            SurfaceDecl::Instance { span, name, .. } => (
                CommandKind::Instance,
                name.as_ref().and_then(|n| n.source_spelling()),
                (span.start, span.end),
            ),
            SurfaceDecl::Axiom { span, name, .. } => (
                CommandKind::Axiom,
                name.source_spelling(),
                (span.start, span.end),
            ),
            SurfaceDecl::Opaque { span, name, .. } => (
                CommandKind::Other("opaque".to_string()),
                name.source_spelling(),
                (span.start, span.end),
            ),
            SurfaceDecl::Variable { span, binders, .. } => {
                let name = binders.first().and_then(|b| b.name.source_spelling());
                (CommandKind::Variable, name, (span.start, span.end))
            }
            // `include x` / `omit x` steer which section `variable`s the
            // following declarations receive, so the editor reports them as
            // the variable-scope commands they are.
            SurfaceDecl::IncludeVars { span, names } => (
                CommandKind::Other("include".to_string()),
                names.first().and_then(|n| n.source_spelling()),
                (span.start, span.end),
            ),
            SurfaceDecl::OmitVars { span, names } => (
                CommandKind::Other("omit".to_string()),
                names.first().and_then(|n| n.source_spelling()),
                (span.start, span.end),
            ),
            SurfaceDecl::UniverseDecl { span, names, .. } => (
                CommandKind::Universe,
                names.first().and_then(|n| n.source_spelling()),
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
                name.source_spelling(),
                (span.start, span.end),
            ),
            SurfaceDecl::Section { span, name, .. } => (
                CommandKind::Section,
                name.as_ref().and_then(|n| n.source_spelling()),
                (span.start, span.end),
            ),
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
            SurfaceDecl::Reduce { span, .. } => (
                CommandKind::Other("reduce".to_string()),
                None,
                (span.start, span.end),
            ),
            SurfaceDecl::Print { span, .. } => (
                CommandKind::Other("print".to_string()),
                None,
                (span.start, span.end),
            ),
            SurfaceDecl::PrintAxioms { span, .. } => (
                CommandKind::Other("print axioms".to_string()),
                None,
                (span.start, span.end),
            ),
            SurfaceDecl::Guard { span, .. } => (
                CommandKind::Other("guard".to_string()),
                None,
                (span.start, span.end),
            ),
            SurfaceDecl::GuardMsgs { span, .. } => (
                CommandKind::Other("guard_msgs".to_string()),
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
            SurfaceDecl::Prelude { span } => (
                CommandKind::Other("prelude".to_owned()),
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
                        term_infos: Vec::new(),
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
        let Ok((elaborated, new_state, import_env, tactic_observations)) = outcome else {
            return;
        };

        self.commit_elaboration(
            uri,
            version,
            &text,
            elaborated,
            new_state,
            tactic_observations,
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
        tactic_observations: Vec<clean_elab::tactic::TacticGoalObservation>,
        imports_env: Option<std::sync::Arc<clean_kernel::Environment>>,
    ) -> bool {
        let Some(mut doc) = self.documents.get_mut(uri) else {
            return false;
        };
        if doc.version != elaborated_version {
            return false;
        }
        let snapshots =
            Self::tactic_goal_snapshots_from_observations(&doc, text, tactic_observations);
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

    #[cfg(test)]
    pub(crate) fn builtin_tactic_patterns() -> clean_parser::TacticPatterns {
        clean_elab::tactic::builtins::builtin_tactic_patterns()
    }

    /// Select views of actual normal elaboration states. Source text is used
    /// only for cursor coverage; it never supplies local types or identities.
    fn tactic_goal_snapshots_from_observations(
        doc: &crate::document::Document,
        text: &str,
        mut observations: Vec<clean_elab::tactic::TacticGoalObservation>,
    ) -> Vec<TacticGoalSnapshot> {
        use clean_elab::tactic::TacticGoalObservationKind;
        super::goal_spans::complete_observation_spans(text, &mut observations);
        let after_starts = Self::tactic_after_cursor_starts(text, &observations);
        let mut snapshots = Vec::new();
        for observation in observations {
            let span = observation.tactic_range;
            if span.start >= span.end || text.get(span.start..span.end).is_none() {
                continue;
            }
            let before = observation.before.ok().map(|goals| goals.rendered_targets);
            if observation.kind == TacticGoalObservationKind::ByPrefix {
                if let Some(goals) = before {
                    snapshots.push(TacticGoalSnapshot {
                        range: Range::new(
                            doc.offset_to_position(span.start),
                            doc.offset_to_position(span.end),
                        ),
                        goals,
                    });
                }
                continue;
            }
            let after_start = after_starts
                .get(&(observation.block_id, span.start, span.end))
                .copied()
                .unwrap_or(span.end);
            let after = observation
                .after
                .and_then(Result::ok)
                .map(|goals| goals.rendered_targets)
                .or_else(|| before.clone());
            let line_start = text[..span.start].rfind('\n').map_or(0, |i| i + 1);
            let start = if text[line_start..span.start]
                .chars()
                .all(char::is_whitespace)
            {
                line_start
            } else {
                span.start
            };
            if let Some(goals) = before {
                snapshots.push(TacticGoalSnapshot {
                    range: Range::new(
                        doc.offset_to_position(start),
                        doc.offset_to_position(after_start),
                    ),
                    goals,
                });
            }
            if let Some(goals) = after {
                let whitespace = text[span.end..]
                    .chars()
                    .take_while(|c| c.is_whitespace())
                    .map(char::len_utf8)
                    .sum::<usize>();
                let end = span.end + whitespace;
                // A tactic with no trailing whitespace remains visible at
                // its tail (e.g. just before `)`). EOF also includes its final
                // point. A following declaration's start stays excluded.
                if whitespace == 0 || end == text.len() {
                    let point = doc.offset_to_position(end);
                    snapshots.push(TacticGoalSnapshot {
                        range: Range::new(point, point),
                        goals: goals.clone(),
                    });
                }
                snapshots.push(TacticGoalSnapshot {
                    range: Range::new(
                        doc.offset_to_position(after_start),
                        doc.offset_to_position(end),
                    ),
                    goals,
                });
            }
        }
        snapshots
    }

    /// Lean's flat-tactic rule uses the after state strictly after its start,
    /// including inside the keyword. Future nested tactic info delays that
    /// transition; term-nested `by` proofs belong to a different actual block.
    /// Group equal expansion spans and visit ordered intervals once per block.
    fn tactic_after_cursor_starts(
        text: &str,
        observations: &[clean_elab::tactic::TacticGoalObservation],
    ) -> HashMap<(clean_elab::tactic::TacticGoalBlockId, usize, usize), usize> {
        use clean_elab::tactic::TacticGoalObservationKind;
        let mut blocks: HashMap<_, BTreeMap<_, bool>> = HashMap::new();
        for observation in observations {
            let span = observation.tactic_range;
            if observation.kind == TacticGoalObservationKind::Tactic
                && span.start < span.end
                && text.get(span.start..span.end).is_some()
            {
                blocks
                    .entry(observation.block_id)
                    .or_default()
                    .entry((span.start, Reverse(span.end)))
                    .and_modify(|tail| *tail |= observation.after_at_tail)
                    .or_insert(observation.after_at_tail);
            }
        }
        let mut after_starts = HashMap::new();
        for (block, ranges) in blocks {
            let mut parents: Vec<(usize, usize)> = Vec::new();
            for ((start, Reverse(end)), after_at_tail) in ranges {
                let Some(first) = text[start..end].chars().next() else {
                    continue;
                };
                after_starts.insert(
                    (block, start, end),
                    if after_at_tail {
                        end
                    } else {
                        start + first.len_utf8()
                    },
                );
                while parents.last().is_some_and(|&(parent_start, parent_end)| {
                    start < parent_start || end > parent_end || start >= parent_end
                }) {
                    parents.pop();
                }
                if let Some(&(parent_start, parent_end)) = parents.last() {
                    if let Some(after) = after_starts.get_mut(&(block, parent_start, parent_end)) {
                        *after = (*after).max(end);
                    }
                }
                parents.push((start, end));
            }
        }
        after_starts
    }

    // Historical parser-only bridge guards retained for the dated pending
    // evidence slice. Live snapshots above come from the normal producer.
    #[cfg(test)]
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

    #[cfg(test)]
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
