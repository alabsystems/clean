// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! LSP backend implementation
//!
//! Implements the `tower_lsp::LanguageServer` trait for clean.

pub(crate) mod analysis;
pub(crate) mod background;
#[cfg(test)]
mod bound_goal_tests;
mod code_actions;
mod declaration_term_info;
mod document_elab;
mod document_ops;
mod goal_spans;
mod helpers;
mod hover;
#[cfg(test)]
mod import_loading_tests;
mod imports;
mod language_server;
mod links;
mod navigation;
#[cfg(test)]
mod plain_term_goal_tests;
#[cfg(test)]
mod registration_warning_tests;
mod selection_range;
pub(crate) mod semantic_tokens;
mod source_mask;
mod term_goal_selection;
#[cfg(test)]
mod tests;
mod type_hierarchy;
pub(crate) mod warnings;

use crate::document::Document;
use crate::rpc::{
    PanelWidgetInstance, PositionedInteractiveGoals, PositionedTermGoal, Range as RpcRange,
    RpcSessionManager, WidgetSource,
};
use clean_elab::interactive_goals::{
    interactive_goal_from_rendered, InteractiveGoals, InteractiveHypothesisBundle,
    InteractiveTermGoal,
};
use dashmap::DashMap;
use std::sync::Arc;
use tower_lsp::lsp_types::*;
use tower_lsp::Client;

const DECLARATION_PANEL_WIDGET_ID: &str = "clean.DeclarationPanel";
const DECLARATION_PANEL_WIDGET_HASH: u64 = 0x1EAF_5000_3709_0001;
const DECLARATION_PANEL_WIDGET_SOURCE: &str = r#"export default function DeclarationPanel(props) {
  return {
    tag: "div",
    props: {},
    children: props.declarations.map((decl) => `${decl.name} : ${decl.type}`)
  };
}"#;
const TYPE_PANEL_WIDGET_ID: &str = "clean.TypeAtPositionPanel";
const TYPE_PANEL_WIDGET_HASH: u64 = 0x1EAF_5000_3709_0002;
const TYPE_PANEL_WIDGET_SOURCE: &str = r#"export default function TypeAtPositionPanel(props) {
  return {
    tag: "pre",
    props: {},
    children: [`${props.name} : ${props.type}`]
  };
}"#;
/// Panel widget rendered for each user-defined `@[widget_module]` declaration
/// discovered during elaboration. A single JS source serves every user widget;
/// each instance carries the module name in its props so the infoview can label
/// the panel after the declaration that registered it.
const USER_WIDGET_PANEL_ID: &str = "clean.UserWidgetModule";
const USER_WIDGET_PANEL_HASH: u64 = 0x1EAF_5000_3709_0003;
const USER_WIDGET_PANEL_SOURCE: &str = r#"export default function UserWidgetModule(props) {
  return {
    tag: "div",
    props: {},
    children: [`widget module: ${props.module}`]
  };
}"#;

// Re-export byte_offset_to_position so language_server.rs keeps compiling
// via `use super::{byte_offset_to_position, ...}`.
pub(crate) use helpers::byte_offset_to_position;
pub(crate) use helpers::compute_folding_ranges;

/// Semantic token types used by clean LSP
/// The order must match the legend provided in server capabilities
pub(crate) const SEMANTIC_TOKEN_TYPES: &[SemanticTokenType] = &[
    SemanticTokenType::KEYWORD,
    SemanticTokenType::TYPE,
    SemanticTokenType::FUNCTION,
    SemanticTokenType::VARIABLE,
    SemanticTokenType::NUMBER,
    SemanticTokenType::STRING,
    SemanticTokenType::COMMENT,
    SemanticTokenType::OPERATOR,
    SemanticTokenType::NAMESPACE,
    SemanticTokenType::CLASS,
    SemanticTokenType::PROPERTY,
];

/// Semantic token modifiers used by clean LSP
/// The order must match the legend provided in server capabilities
/// Modifiers are represented as bit flags in the token_modifiers_bitset field
pub(crate) const SEMANTIC_TOKEN_MODIFIERS: &[SemanticTokenModifier] = &[
    SemanticTokenModifier::DECLARATION,     // 0: bit 0 (1 << 0 = 1)
    SemanticTokenModifier::DEFINITION,      // 1: bit 1 (1 << 1 = 2)
    SemanticTokenModifier::READONLY,        // 2: bit 2 (1 << 2 = 4)
    SemanticTokenModifier::DEPRECATED,      // 3: bit 3 (1 << 3 = 8)
    SemanticTokenModifier::DEFAULT_LIBRARY, // 4: bit 4 (1 << 4 = 16)
];

/// Modifier bits for semantic tokens (indices match SEMANTIC_TOKEN_MODIFIERS array)
pub(crate) mod modifier_bits {
    pub(crate) const DECLARATION: u32 = 1 << 0;
    pub(crate) const DEFINITION: u32 = 1 << 1;
    pub(crate) const READONLY: u32 = 1 << 2;
    #[cfg(test)]
    pub(crate) const DEPRECATED: u32 = 1 << 3;
    pub(crate) const DEFAULT_LIBRARY: u32 = 1 << 4;
}

/// Information about a definition location
#[derive(Debug, Clone)]
pub(crate) struct DefinitionInfo {
    /// The URI of the document containing the definition
    pub(crate) uri: Url,
    /// Start byte offset of the definition
    pub(crate) start: usize,
    /// End byte offset of the definition
    pub(crate) end: usize,
    /// Start byte offset of the declared identifier
    pub(crate) name_start: usize,
    /// End byte offset of the declared identifier
    pub(crate) name_end: usize,
}

#[derive(Debug, Clone)]
pub(crate) struct TacticGoalSnapshot {
    pub(crate) range: Range,
    pub(crate) goals: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg(test)]
pub(crate) struct TacticSnapshotBridgeGap {
    pub(crate) post_tactic_range: Range,
    pub(crate) tactic_script: String,
    pub(crate) target_text: String,
    pub(crate) missing_input: &'static str,
}

/// Live, client-tunable server configuration.
///
/// Populated from `workspace/didChangeConfiguration` notifications so editors
/// can flip settings without restarting the server. Only fields with a real
/// consumer live here; unrecognized `clean.*` keys are ignored.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct CleanConfig {
    /// Whether `textDocument/inlayHint` returns hints. Mirrors the
    /// `clean.inlayHints.enable` setting (default: enabled). Consumed by
    /// [`CleanBackend::get_inlay_hints`].
    pub(crate) inlay_hints_enabled: bool,
}

impl Default for CleanConfig {
    fn default() -> Self {
        Self {
            inlay_hints_enabled: true,
        }
    }
}

impl CleanConfig {
    /// Merge recognized `clean.*` settings from a client-supplied JSON blob.
    ///
    /// Accepts both the nested form sent by VS Code-style clients
    /// (`{ "clean": { "inlayHints": { "enable": false } } }`) and the
    /// already-scoped form (`{ "inlayHints": { "enable": false } }`).
    /// Unknown keys and malformed shapes are ignored, leaving the current
    /// value untouched, so a partial or junk payload never panics or clobbers
    /// unrelated settings.
    pub(crate) fn apply_json(&mut self, settings: &serde_json::Value) {
        // Prefer the `clean` sub-object when present, otherwise treat the blob
        // as already scoped to the clean namespace.
        let scope = settings.get("clean").unwrap_or(settings);

        if let Some(enabled) = scope
            .get("inlayHints")
            .and_then(|hints| hints.get("enable"))
            .and_then(serde_json::Value::as_bool)
        {
            self.inlay_hints_enabled = enabled;
        }
    }
}

/// clean LSP backend
///
/// Every stateful field is `Arc`-shared (or, for `Client`, internally
/// reference-counted) so `background::CleanBackend::background_handle` can
/// build a second `CleanBackend` *view* over the same state for a per-URI
/// background elaboration task (`tokio::spawn` needs an owned `'static`
/// value). A handle is never a copy: state written through one view is
/// visible through the other.
pub struct CleanBackend {
    /// LSP client for sending notifications
    pub(crate) client: Client,
    /// Open documents
    pub(crate) documents: Arc<DashMap<Url, Document>>,
    /// clean environment (shared across documents)
    pub(crate) env: Arc<tokio::sync::RwLock<clean_kernel::Environment>>,
    /// Definition index: maps name to definition location
    pub(crate) definitions: Arc<DashMap<String, DefinitionInfo>>,
    /// RPC session manager for Lean4-compatible infoview endpoints
    pub(crate) rpc_sessions: Arc<RpcSessionManager>,
    /// Live tactic goals captured by URI and source range for plainGoal/goal widgets.
    pub(crate) tactic_goal_snapshots: Arc<DashMap<Url, Vec<TacticGoalSnapshot>>>,
    /// Cached tactic argument patterns for parser-level dispatch.
    ///
    /// Immutable after construction, so plain `Clone` (not `Arc`) still gives
    /// background handles an identical view.
    pub(crate) tactic_patterns: clean_parser::TacticPatterns,
    /// Client-tunable settings, updated live via `workspace/didChangeConfiguration`.
    pub(crate) config: Arc<tokio::sync::RwLock<CleanConfig>>,
    /// Per-URI background elaboration bookkeeping (unfreeze plan deferred
    /// item C): the latest scheduled generation plus the in-flight task
    /// handle, so a newer `didChange` supersedes and aborts an older run.
    /// Protocol documented in `background.rs`.
    pub(crate) elaboration_tasks: Arc<DashMap<Url, background::ElaborationSlot>>,
}

impl CleanBackend {
    /// Create a new backend
    #[must_use]
    pub fn new(client: Client) -> Self {
        Self {
            client,
            documents: Arc::new(DashMap::new()),
            env: Arc::new(tokio::sync::RwLock::new(clean_kernel::Environment::new())),
            definitions: Arc::new(DashMap::new()),
            rpc_sessions: Arc::new(RpcSessionManager::new()),
            tactic_goal_snapshots: Arc::new(DashMap::new()),
            tactic_patterns: clean_elab::tactic::builtins::builtin_tactic_patterns(),
            config: Arc::new(tokio::sync::RwLock::new(CleanConfig::default())),
            elaboration_tasks: Arc::new(DashMap::new()),
        }
    }
}

// --- Lean4 RPC endpoints ($/lean/rpc/*) and goal helpers ---

impl CleanBackend {
    /// Handle $/lean/rpc/connect
    /// Starts an RPC session tied to a document
    pub(crate) fn rpc_connect(
        &self,
        params: crate::rpc::RpcConnectParams,
    ) -> tower_lsp::jsonrpc::Result<crate::rpc::RpcConnected> {
        self.refresh_infoview_widgets(&params.uri);
        self.refresh_infoview_goals(&params.uri);
        self.rpc_sessions
            .connect(params)
            .map_err(|e| tower_lsp::jsonrpc::Error {
                code: tower_lsp::jsonrpc::ErrorCode::ServerError(i64::from(e.code)),
                message: std::borrow::Cow::Owned(e.message),
                data: None,
            })
    }

    /// Handle $/lean/rpc/call
    /// Invokes a registered RPC procedure
    pub(crate) fn rpc_call(
        &self,
        params: crate::rpc::RpcCallParams,
    ) -> tower_lsp::jsonrpc::Result<serde_json::Value> {
        self.refresh_infoview_widgets(&params.text_document.uri);
        self.refresh_infoview_goals(&params.text_document.uri);
        self.rpc_sessions
            .call(params)
            .map_err(|e| tower_lsp::jsonrpc::Error {
                code: tower_lsp::jsonrpc::ErrorCode::ServerError(i64::from(e.code)),
                message: std::borrow::Cow::Owned(e.message),
                data: None,
            })
    }

    /// Handle $/lean/rpc/release (notification)
    /// Releases RPC object references
    pub(crate) fn rpc_release(&self, params: crate::rpc::RpcReleaseParams) {
        self.rpc_sessions.release(params);
    }

    /// Handle $/lean/rpc/keepAlive (notification)
    /// Keeps session alive (client should send every 10s)
    pub(crate) fn rpc_keep_alive(&self, params: crate::rpc::RpcKeepAliveParams) {
        self.rpc_sessions.keep_alive(params);
    }

    fn has_live_tactic_goal_state(&self) -> bool {
        self.tactic_goal_snapshots
            .iter()
            .any(|entry| !entry.value().is_empty())
    }

    fn has_live_user_widget_modules(&self) -> bool {
        self.documents.iter().any(|entry| {
            entry
                .value()
                .elaborated
                .as_ref()
                .is_some_and(|elab| !elab.widget_modules.is_empty())
        })
    }

    #[cfg(test)]
    fn has_live_hole_expected_type_state(&self) -> bool {
        self.documents.iter().any(|entry| {
            entry
                .value()
                .elaborated
                .as_ref()
                .is_some_and(|elab| !elab.holes.is_empty())
        })
    }

    /// Find a recorded hole context at `position`, preferring the narrowest
    /// overlapping span. Invalid byte spans cannot become clamped LSP ranges.
    fn hole_context_at_position<'a>(
        &self,
        doc: &'a Document,
        position: Position,
    ) -> Option<&'a crate::document::HoleContext> {
        let elab = doc.elaborated.as_ref()?;
        elab.holes
            .iter()
            .filter(|hole| recorded_span_contains(doc, hole.start, hole.end, position))
            .min_by_key(|hole| hole.end.saturating_sub(hole.start))
    }

    #[allow(deprecated)] // Lean4-compatible panel widget shape still carries optional name.
    fn refresh_infoview_widgets(&self, uri: &Url) {
        self.rpc_sessions.register_widget_source(
            DECLARATION_PANEL_WIDGET_HASH,
            WidgetSource {
                sourcetext: DECLARATION_PANEL_WIDGET_SOURCE.to_string(),
            },
        );
        self.rpc_sessions.register_widget_source(
            TYPE_PANEL_WIDGET_HASH,
            WidgetSource {
                sourcetext: TYPE_PANEL_WIDGET_SOURCE.to_string(),
            },
        );
        // Register the shared user-widget JS source only when elaboration has
        // discovered at least one `@[widget_module]` declaration, so the
        // registry stays empty in the common no-user-widget case.
        if self.has_live_user_widget_modules() {
            self.rpc_sessions.register_widget_source(
                USER_WIDGET_PANEL_HASH,
                WidgetSource {
                    sourcetext: USER_WIDGET_PANEL_SOURCE.to_string(),
                },
            );
        }

        let widgets = self
            .documents
            .get(uri)
            .and_then(|doc| {
                let elaborated = doc.elaborated.as_ref()?;
                let mut widgets = Vec::new();
                let declarations: Vec<_> = elaborated
                    .declarations
                    .iter()
                    .map(|decl| {
                        let start = doc.offset_to_position(decl.start);
                        let end = doc.offset_to_position(decl.end);
                        widgets.push(PanelWidgetInstance {
                            id: TYPE_PANEL_WIDGET_ID.to_string(),
                            javascript_hash: TYPE_PANEL_WIDGET_HASH,
                            props: serde_json::json!({
                                "name": &decl.name,
                                "type": &decl.type_str
                            }),
                            range: Some(RpcRange { start, end }),
                            name: None,
                        });
                        serde_json::json!({
                            "name": &decl.name,
                            "type": &decl.type_str,
                            "range": {
                                "start": start,
                                "end": end
                            }
                        })
                    })
                    .collect();

                if !declarations.is_empty() {
                    let start = elaborated
                        .declarations
                        .iter()
                        .map(|decl| decl.start)
                        .min()
                        .unwrap_or(0);
                    let end = elaborated
                        .declarations
                        .iter()
                        .map(|decl| decl.end)
                        .max()
                        .unwrap_or(start);

                    widgets.push(PanelWidgetInstance {
                        id: DECLARATION_PANEL_WIDGET_ID.to_string(),
                        javascript_hash: DECLARATION_PANEL_WIDGET_HASH,
                        props: serde_json::json!({
                            "documentVersion": doc.version,
                            "declarations": declarations
                        }),
                        range: Some(RpcRange {
                            start: doc.offset_to_position(start),
                            end: doc.offset_to_position(end),
                        }),
                        name: None,
                    });
                }

                // Append one panel per user-defined widget module discovered
                // during elaboration (decls carrying `@[widget_module]`), so the
                // infoview surfaces user widgets alongside the built-in panels.
                for module in &elaborated.widget_modules {
                    widgets.push(PanelWidgetInstance {
                        id: USER_WIDGET_PANEL_ID.to_string(),
                        javascript_hash: USER_WIDGET_PANEL_HASH,
                        props: serde_json::json!({ "module": &module.name }),
                        range: Some(RpcRange {
                            start: doc.offset_to_position(module.start),
                            end: doc.offset_to_position(module.end),
                        }),
                        name: None,
                    });
                }

                if widgets.is_empty() {
                    return None;
                }
                Some(widgets)
            })
            .unwrap_or_default();

        self.rpc_sessions
            .replace_panel_widgets(uri.clone(), widgets);
    }

    /// Refresh the structured goal state for `uri` in the RPC goal registry.
    ///
    /// Sources range-local tactic snapshots and recorded hole contexts.
    /// The RPC term-goal registry also retains its existing declaration-type
    /// fallback; that fallback is separate from `$/lean/plainTermGoal`, whose
    /// ranged responses require a captured hole. Term entries are pushed
    /// narrowest-first because the registry lookup is first-match.
    fn refresh_infoview_goals(&self, uri: &Url) {
        let doc_is_elaborated = self
            .documents
            .get(uri)
            .is_some_and(|doc| doc.elaborated.is_some());

        let goal_entries = if doc_is_elaborated && self.has_live_tactic_goal_state() {
            self.tactic_goal_snapshots
                .get(uri)
                .map(|snapshots| {
                    snapshots
                        .value()
                        .iter()
                        .map(|snapshot| PositionedInteractiveGoals {
                            range: RpcRange {
                                start: snapshot.range.start,
                                end: snapshot.range.end,
                            },
                            goals: InteractiveGoals {
                                goals: snapshot
                                    .goals
                                    .iter()
                                    .map(|goal| interactive_goal_from_rendered(goal))
                                    .collect(),
                            },
                        })
                        .collect()
                })
                .unwrap_or_default()
        } else {
            Vec::new()
        };

        let term_entries = self
            .documents
            .get(uri)
            .and_then(|doc| {
                let elab = doc.elaborated.as_ref()?;
                let mut holes: Vec<&crate::document::HoleContext> = elab.holes.iter().collect();
                // Innermost (narrowest) hole first, matching the
                // `plainTermGoal` innermost-hole preference.
                holes.sort_by_key(|hole| hole.end.saturating_sub(hole.start));
                let mut entries: Vec<PositionedTermGoal> = holes
                    .into_iter()
                    .map(|hole| PositionedTermGoal {
                        range: RpcRange {
                            start: doc.offset_to_position(hole.start),
                            end: doc.offset_to_position(hole.end),
                        },
                        goal: InteractiveTermGoal {
                            hyps: hole
                                .local_bindings
                                .iter()
                                .map(|(name, ty)| InteractiveHypothesisBundle {
                                    names: vec![name.clone()],
                                    type_: ty.clone(),
                                    is_instance: false,
                                    is_inserted: false,
                                })
                                .collect(),
                            type_: hole.expected_type.clone(),
                        },
                    })
                    .collect();
                entries.extend(elab.declarations.iter().map(|decl| PositionedTermGoal {
                    range: RpcRange {
                        start: doc.offset_to_position(decl.start),
                        end: doc.offset_to_position(decl.end),
                    },
                    goal: InteractiveTermGoal {
                        hyps: Vec::new(),
                        type_: decl.type_str.clone(),
                    },
                }));
                Some(entries)
            })
            .unwrap_or_default();

        self.rpc_sessions
            .replace_interactive_goals(uri.clone(), goal_entries);
        self.rpc_sessions
            .replace_term_goals(uri.clone(), term_entries);
    }

    /// Handle $/lean/plainGoal
    ///
    /// Returns tactic goals at a position as plain text.
    /// Returns None when live elaboration has not produced a range-local tactic snapshot.
    pub(crate) fn plain_goal(
        &self,
        params: crate::rpc::PlainGoalParams,
    ) -> Option<crate::rpc::PlainGoalResponse> {
        let has_elaborated_doc = self
            .documents
            .get(&params.text_document.uri)
            .is_some_and(|doc| doc.elaborated.is_some());
        if has_elaborated_doc && self.has_live_tactic_goal_state() {
            if let Some(snapshots) = self.tactic_goal_snapshots.get(&params.text_document.uri) {
                if let Some(snapshot) = snapshots
                    .value()
                    .iter()
                    .rev()
                    .filter(|snapshot| {
                        position_after_or_equal(params.position, snapshot.range.start)
                            && (position_before(params.position, snapshot.range.end)
                                || (snapshot.range.start == snapshot.range.end
                                    && params.position == snapshot.range.start))
                    })
                    .min_by_key(|snapshot| {
                        (
                            snapshot
                                .range
                                .end
                                .line
                                .saturating_sub(snapshot.range.start.line),
                            snapshot
                                .range
                                .end
                                .character
                                .saturating_sub(snapshot.range.start.character),
                        )
                    })
                {
                    let goals = snapshot.goals.clone();
                    let rendered = if goals.is_empty() {
                        "no goals".to_string()
                    } else {
                        goals
                            .iter()
                            .map(|goal| format!("```lean\n{goal}\n```"))
                            .collect::<Vec<_>>()
                            .join("\n---\n")
                    };
                    return Some(crate::rpc::PlainGoalResponse { rendered, goals });
                }
            }
        }

        None
    }

    /// Handle $/lean/plainTermGoal, retaining the document guard while reading
    /// its captured state so closing a file cannot race a second lookup.
    pub(crate) fn plain_term_goal_request(
        &self,
        params: crate::rpc::PlainTermGoalParams,
    ) -> tower_lsp::jsonrpc::Result<Option<crate::rpc::PlainTermGoalResponse>> {
        let doc = self
            .documents
            .get(&params.text_document.uri)
            .ok_or_else(|| tower_lsp::jsonrpc::Error {
                code: tower_lsp::jsonrpc::ErrorCode::ContentModified,
                message: format!(
                    "Cannot process request to closed file '{}'",
                    params.text_document.uri
                )
                .into(),
                data: None,
            })?;
        Ok(self.plain_term_goal_from_document(&doc, params.position))
    }

    /// Test helper for the optional captured state, independent of wire errors.
    #[cfg(test)]
    pub(crate) fn plain_term_goal(
        &self,
        params: crate::rpc::PlainTermGoalParams,
    ) -> Option<crate::rpc::PlainTermGoalResponse> {
        let doc = self.documents.get(&params.text_document.uri)?;
        self.plain_term_goal_from_document(&doc, params.position)
    }

    /// Read a captured term goal from an open document.
    ///
    /// Returns JSON null without a captured term goal at this position.
    /// A declaration's public type and range are not term-local expected-type
    /// observations. Hole metadata remains available when a generic term
    /// observation could not be finalized (for example, an unsolved term).
    fn plain_term_goal_from_document(
        &self,
        doc: &Document,
        position: Position,
    ) -> Option<crate::rpc::PlainTermGoalResponse> {
        let info = term_goal_selection::at_position(doc, position);
        let hole = self.hole_context_at_position(doc, position);
        if let Some(info) = info {
            let captured_hole_is_inner = hole.is_some_and(|hole| {
                info.start <= hole.start
                    && hole.end <= info.end
                    && hole.end - hole.start < info.end - info.start
            });
            let partial_hole_has_type = info.is_partial
                && info.goal.is_none()
                && hole.is_some_and(|hole| hole.start == info.start && hole.end == info.end);
            if !captured_hole_is_inner && !partial_hole_has_type {
                return info
                    .goal
                    .as_ref()
                    .map(|goal| crate::rpc::PlainTermGoalResponse {
                        goal: goal.clone(),
                        range: RpcRange {
                            start: doc.offset_to_position(info.start),
                            end: doc.offset_to_position(info.end),
                        },
                    });
            }
        }
        let hole = hole?;
        Some(crate::rpc::PlainTermGoalResponse {
            goal: format_hole_goal(hole),
            range: RpcRange {
                start: doc.offset_to_position(hole.start),
                end: doc.offset_to_position(hole.end),
            },
        })
    }
}

/// Format a hole's goal for `plainTermGoal`, Lean infoview style.
///
/// When the hole has local hypotheses in scope, the goal is rendered as a
/// local-context block above the turnstile:
///
/// ```text
/// n : Nat
/// h : P
/// ⊢ Q
/// ```
///
/// Lean's `InteractiveTermGoal.pretty` retains the turnstile even when the
/// local context is empty.
fn format_hole_goal(hole: &crate::document::HoleContext) -> String {
    let mut out = String::new();
    for (name, ty) in &hole.local_bindings {
        out.push_str(name);
        out.push_str(" : ");
        out.push_str(ty);
        out.push('\n');
    }
    out.push_str("⊢ ");
    out.push_str(&hole.expected_type);
    out
}

fn position_after_or_equal(position: Position, boundary: Position) -> bool {
    position.line > boundary.line
        || (position.line == boundary.line && position.character >= boundary.character)
}

/// Validate source byte boundaries before comparing UTF-16 request positions.
fn recorded_span_contains(doc: &Document, start: usize, end: usize, position: Position) -> bool {
    if start >= end || end > doc.content.len_bytes() {
        return false;
    }
    if doc.content.char_to_byte(doc.content.byte_to_char(start)) != start
        || doc.content.char_to_byte(doc.content.byte_to_char(end)) != end
    {
        return false;
    }
    position_after_or_equal(position, doc.offset_to_position(start))
        && position_after_or_equal(doc.offset_to_position(end), position)
}

fn position_before(position: Position, boundary: Position) -> bool {
    position.line < boundary.line
        || (position.line == boundary.line && position.character < boundary.character)
}
