// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! LSP backend implementation
//!
//! Implements the `tower_lsp::LanguageServer` trait for clean.

pub(crate) mod analysis;
mod code_actions;
mod document_ops;
mod helpers;
mod language_server;
mod links;
mod navigation;
#[cfg(test)]
mod registration_warning_tests;
mod selection_range;
pub(crate) mod semantic_tokens;
#[cfg(test)]
mod tests;
mod type_hierarchy;
pub(crate) mod warnings;

use crate::document::{Document, ElaboratedDecl};
use crate::rpc::{PanelWidgetInstance, Range as RpcRange, RpcSessionManager, WidgetSource};
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
pub struct CleanBackend {
    /// LSP client for sending notifications
    pub(crate) client: Client,
    /// Open documents
    pub(crate) documents: DashMap<Url, Document>,
    /// clean environment (shared across documents)
    pub(crate) env: Arc<tokio::sync::RwLock<clean_kernel::Environment>>,
    /// Definition index: maps name to definition location
    pub(crate) definitions: DashMap<String, DefinitionInfo>,
    /// RPC session manager for Lean4-compatible infoview endpoints
    pub(crate) rpc_sessions: RpcSessionManager,
    /// Live tactic goals captured by URI and source range for plainGoal/goal widgets.
    pub(crate) tactic_goal_snapshots: DashMap<Url, Vec<TacticGoalSnapshot>>,
    /// Cached tactic argument patterns for parser-level dispatch.
    pub(crate) tactic_patterns: clean_parser::TacticPatterns,
    /// Client-tunable settings, updated live via `workspace/didChangeConfiguration`.
    pub(crate) config: Arc<tokio::sync::RwLock<CleanConfig>>,
}

impl CleanBackend {
    /// Create a new backend
    #[must_use]
    pub fn new(client: Client) -> Self {
        Self {
            client,
            documents: DashMap::new(),
            env: Arc::new(tokio::sync::RwLock::new(clean_kernel::Environment::new())),
            definitions: DashMap::new(),
            rpc_sessions: RpcSessionManager::new(),
            tactic_goal_snapshots: DashMap::new(),
            tactic_patterns: clean_elab::tactic::builtins::builtin_tactic_patterns(),
            config: Arc::new(tokio::sync::RwLock::new(CleanConfig::default())),
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

    fn has_live_hole_expected_type_state(&self) -> bool {
        self.documents.iter().any(|entry| {
            entry
                .value()
                .elaborated
                .as_ref()
                .is_some_and(|elab| !elab.holes.is_empty())
        })
    }

    /// Find the hole context at `position` in `doc`, preferring the
    /// innermost (narrowest) hole when several overlap. Returns the recorded
    /// hole-local expected type the elaborator demanded at that hole.
    fn hole_expected_type_at_position(&self, doc: &Document, position: Position) -> Option<String> {
        let elab = doc.elaborated.as_ref()?;
        elab.holes
            .iter()
            .filter(|hole| {
                let start = doc.offset_to_position(hole.start);
                let end = doc.offset_to_position(hole.end);
                position_after_or_equal(position, start) && position_before(position, end)
            })
            // Prefer the smallest matching hole span so a nested hole wins over
            // an enclosing one.
            .min_by_key(|hole| hole.end.saturating_sub(hole.start))
            .map(format_hole_goal)
    }

    fn elaborated_decl_at_position<'a>(
        &self,
        doc: &'a Document,
        position: Position,
    ) -> Option<&'a ElaboratedDecl> {
        let elab = doc.elaborated.as_ref()?;
        elab.declarations.iter().find(|decl| {
            let start = doc.offset_to_position(decl.start);
            let end = doc.offset_to_position(decl.end);
            position_after_or_equal(position, start) && position_before(position, end)
        })
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

    /// Handle $/lean/plainGoal
    ///
    /// Returns tactic goals at a position as plain text.
    /// Returns None when live elaboration has not produced a range-local tactic snapshot.
    pub(crate) fn plain_goal(
        &self,
        params: crate::rpc::PlainGoalParams,
    ) -> crate::rpc::PlainGoalResponse {
        let has_elaborated_doc = self
            .documents
            .get(&params.text_document.uri)
            .is_some_and(|doc| doc.elaborated.is_some());
        if has_elaborated_doc && self.has_live_tactic_goal_state() {
            if let Some(snapshots) = self.tactic_goal_snapshots.get(&params.text_document.uri) {
                if let Some(snapshot) = snapshots.value().iter().find(|snapshot| {
                    position_after_or_equal(params.position, snapshot.range.start)
                        && position_before(params.position, snapshot.range.end)
                }) {
                    return crate::rpc::PlainGoalResponse {
                        goals: Some(snapshot.goals.clone()),
                    };
                }
            }
        }

        crate::rpc::PlainGoalResponse { goals: None }
    }

    /// Handle $/lean/plainTermGoal
    ///
    /// Returns the expected type at a position as plain text. A hole-local
    /// expected type (recorded during elaboration for `_`/`sorry` holes that
    /// constitute a declaration's body) takes precedence over the enclosing
    /// declaration's type, so a cursor on the hole reports the goal the
    /// elaborator demanded there rather than the whole-declaration type.
    pub(crate) fn plain_term_goal(
        &self,
        params: crate::rpc::PlainTermGoalParams,
    ) -> crate::rpc::PlainTermGoalResponse {
        if let Some(doc) = self.documents.get(&params.text_document.uri) {
            if doc.elaborated.is_some() && self.has_live_hole_expected_type_state() {
                if let Some(goal) = self.hole_expected_type_at_position(&doc, params.position) {
                    return crate::rpc::PlainTermGoalResponse { goal: Some(goal) };
                }
            }
            if let Some(decl) = self.elaborated_decl_at_position(&doc, params.position) {
                return crate::rpc::PlainTermGoalResponse {
                    goal: Some(decl.type_str.clone()),
                };
            }
        }

        crate::rpc::PlainTermGoalResponse { goal: None }
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
/// When no hypotheses are in scope, only the expected type is returned
/// (unchanged from the pre-local-context behaviour), so body-level and
/// no-binder holes report a bare expected type.
fn format_hole_goal(hole: &crate::document::HoleContext) -> String {
    if hole.local_bindings.is_empty() {
        return hole.expected_type.clone();
    }
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

fn position_before(position: Position, boundary: Position) -> bool {
    position.line < boundary.line
        || (position.line == boundary.line && position.character < boundary.character)
}
