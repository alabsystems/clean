// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Document lifecycle operations: parsing, elaboration, diagnostics generation,
//! and shared declaration-classification / content-hash helpers.

use super::warnings::{
    collect_deprecated_names, detect_deprecated_usage, detect_duplicate_binders,
    detect_sorry_warnings, detect_unused_variables, merge_registration_sorry_warning,
};
use super::{CleanBackend, DefinitionInfo, TacticGoalSnapshot, TacticSnapshotBridgeGap};
use crate::document::{
    CommandKind, ElaboratedDecl, ElaboratedDocument, IncrementalState, IncrementalStats,
    ParseError, ParsedCommand, ParsedDocument, TypeError,
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
        decl: &clean_parser::SurfaceDecl,
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
    pub(crate) fn get_decl_span(decl: &clean_parser::SurfaceDecl) -> (usize, usize) {
        Self::classify_decl(decl).2
    }

    /// Elaborate a document and update its state (with incremental checking)
    pub(crate) async fn elaborate_document(&self, uri: &Url) {
        if let Some(mut doc) = self.documents.get_mut(uri) {
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

            let (elaborated, new_state) = self.elaborate_text_incremental(&text, prev_state).await;

            let env = self.env.read().await.clone();
            let snapshots = Self::tactic_goal_snapshots_from_text(&doc, &text, &env);
            doc.elaborated = Some(elaborated);
            doc.incremental_state = new_state;

            if snapshots.is_empty() {
                self.tactic_goal_snapshots.remove(uri);
            } else {
                self.tactic_goal_snapshots.insert(uri.clone(), snapshots);
            }
        }
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

    fn tactic_goal_snapshot_from_theorem(
        doc: &crate::document::Document,
        text: &str,
        env: &clean_kernel::Environment,
        binders: &[SurfaceBinder],
        ty: &SurfaceExpr,
        proof: &SurfaceExpr,
    ) -> Option<TacticGoalSnapshot> {
        if !binders.is_empty() {
            Self::post_tactic_snapshot_bridge_gap_from_theorem(doc, text, binders, ty, proof)?;
            return None;
        }
        Self::tactic_goal_snapshot_from_type_and_proof(doc, text, env, ty, proof)
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
    async fn elaborate_text_incremental(
        &self,
        text: &str,
        _prev_state: IncrementalState,
    ) -> (ElaboratedDocument, IncrementalState) {
        let Ok(decls) = clean_parser::parse_file_with_tactics(text, &self.tactic_patterns) else {
            return (
                ElaboratedDocument {
                    errors: vec![],
                    warnings: vec![],
                    declarations: vec![],
                    holes: vec![],
                    widget_modules: vec![],
                },
                IncrementalState::default(),
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

        // Clone the shared environment into a per-document scratch copy so we
        // can mutate it for registration without affecting the global server
        // state.
        let mut scratch_env = self.env.read().await.clone();

        for decl in &decls {
            let (_kind, name, span) = Self::classify_decl(decl);
            let decl_name = name.as_deref().unwrap_or("<anonymous>");

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
        )
    }

    /// Render a hole's elaborator-provided expected type to the same
    /// pretty-printed form used for declaration types (`extract_elab_info`),
    /// keeping `plainTermGoal` output consistent across hole-local and
    /// whole-declaration goals.
    fn render_hole_type(hole: &clean_elab::HoleContext) -> String {
        let ty = &hole.expected_type;
        format!("{ty:?}")
    }

    /// Render a hole's captured local hypotheses to pretty-printed
    /// `(name, type)` pairs, using the same renderer as the expected type so
    /// the local context displays consistently with the goal.
    fn render_hole_bindings(hole: &clean_elab::HoleContext) -> Vec<(String, String)> {
        hole.local_bindings
            .iter()
            .map(|(name, ty)| (name.clone(), format!("{ty:?}")))
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
    fn body_sorry_span(decl: &clean_parser::SurfaceDecl) -> Option<clean_parser::Span> {
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
    pub(crate) fn is_widget_module_decl(decl: &clean_parser::SurfaceDecl) -> bool {
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
    fn expr_sorry_span(expr: &clean_parser::SurfaceExpr) -> Option<clean_parser::Span> {
        use clean_parser::SurfaceExpr;
        match expr {
            SurfaceExpr::Ident(span, name) if name == "sorry" => Some(*span),
            SurfaceExpr::Paren(_, inner) => Self::expr_sorry_span(inner),
            _ => None,
        }
    }

    /// Extract elaboration info from an ElabResult
    fn extract_elab_info(
        result: &clean_elab::ElabResult,
        decl: &clean_parser::SurfaceDecl,
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
                type_str: format!("{ty:?}"),
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

    /// Check a document (parse + elaborate + publish diagnostics)
    pub(crate) async fn check_document(&self, uri: &Url) {
        self.parse_document(uri).await;
        self.elaborate_document(uri).await;
        self.publish_diagnostics(uri).await;
    }
}
