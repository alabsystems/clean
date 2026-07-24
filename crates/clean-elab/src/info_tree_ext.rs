// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended info tree for IDE integration.
//!
//! Extends [`crate::info_tree`] with higher-level, serializable types consumed
//! by the LSP server: hover info, go-to-definition, completion candidates,
//! diagnostics, semantic tokens, folding ranges, document symbols, reference
//! tracking, and statistics. Each extraction function walks the base
//! [`InfoTree`] once, and [`build_extended_info_tree`] composes them all.

use std::collections::HashMap;

use serde::{Deserialize, Serialize};

use crate::info_tree::{InfoData, InfoKind, InfoTree};

// ---------------------------------------------------------------------------
// IDE types
// ---------------------------------------------------------------------------

/// Hover information at a cursor position.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct HoverInfo {
    /// Byte range in the source (not serialized -- spans are positional).
    #[serde(skip)]
    pub(crate) span_start: usize,
    #[serde(skip)]
    pub(crate) span_end: usize,
    /// Pretty-printed expression text.
    pub(crate) expr_text: String,
    /// Pretty-printed type text.
    pub(crate) type_text: String,
}

/// Go-to-definition result.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct GoToDefinitionInfo {
    pub(crate) name: String,
    /// `(file_path, start, end)` -- `None` when the source location is unknown.
    pub(crate) target_span: Option<(String, usize, usize)>,
    pub(crate) type_text: String,
}

/// A single auto-completion candidate.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct CompletionCandidate {
    pub(crate) label: String,
    pub(crate) type_signature: String,
    pub(crate) detail: Option<String>,
    /// Lexicographic sort key for ordering candidates.
    pub(crate) sort_text: String,
}

/// Diagnostic severity levels (mirrors LSP).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum DiagnosticSeverity {
    Error,
    Warning,
    Info,
    Hint,
}

/// A diagnostic (error/warning) attached to a span.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct DiagnosticInfo {
    #[serde(skip)]
    pub(crate) span_start: usize,
    #[serde(skip)]
    pub(crate) span_end: usize,
    pub(crate) severity: DiagnosticSeverity,
    pub(crate) message: String,
    pub(crate) code: Option<String>,
}

/// Semantic token classification for syntax highlighting.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub(crate) enum SemanticTokenKind {
    Keyword,
    Identifier,
    Type,
    Literal,
    Operator,
    Comment,
    Namespace,
    Function,
    Variable,
    Property,
}

/// A classified semantic token with its span.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct SemanticToken {
    #[serde(skip)]
    pub(crate) span_start: usize,
    #[serde(skip)]
    pub(crate) span_end: usize,
    pub(crate) kind: SemanticTokenKind,
}

/// Kind of collapsible region.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum FoldingRangeKind {
    Comment,
    Imports,
    Region,
    Declaration,
}

/// A collapsible region for the editor.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct FoldingRange {
    pub(crate) start_line: u32,
    pub(crate) end_line: u32,
    pub(crate) kind: FoldingRangeKind,
}

/// Kind of document symbol (for the outline view).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum DocumentSymbolKind {
    Definition,
    Theorem,
    Inductive,
    Structure,
    Namespace,
    Tactic,
    Instance,
    Class,
}

/// A symbol in the document outline.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct DocumentSymbol {
    pub(crate) name: String,
    pub(crate) kind: DocumentSymbolKind,
    #[serde(skip)]
    pub(crate) span_start: usize,
    #[serde(skip)]
    pub(crate) span_end: usize,
    pub(crate) detail: Option<String>,
    pub(crate) children: Vec<DocumentSymbol>,
}

/// Collected references for a single definition name.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct ReferenceInfo {
    pub(crate) definition_name: String,
    /// `(start, end)` byte-offset pairs for each usage site.
    pub(crate) usage_spans: Vec<(usize, usize)>,
}

/// Aggregate statistics over an info tree.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub(crate) struct InfoTreeStats {
    pub(crate) total_nodes: usize,
    pub(crate) total_leaves: usize,
    pub(crate) term_info_count: usize,
    pub(crate) tactic_info_count: usize,
    pub(crate) field_info_count: usize,
    pub(crate) command_info_count: usize,
    pub(crate) macro_expansion_count: usize,
}

/// The full extended info tree -- one per elaborated file / command.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct ExtendedInfoTree {
    pub(crate) hover_info: Vec<HoverInfo>,
    pub(crate) goto_definitions: Vec<GoToDefinitionInfo>,
    pub(crate) completions: Vec<CompletionCandidate>,
    pub(crate) diagnostics: Vec<DiagnosticInfo>,
    pub(crate) semantic_tokens: Vec<SemanticToken>,
    pub(crate) folding_ranges: Vec<FoldingRange>,
    pub(crate) document_symbols: Vec<DocumentSymbol>,
    pub(crate) references: Vec<ReferenceInfo>,
    pub(crate) stats: InfoTreeStats,
}

// ---------------------------------------------------------------------------
// Tree walker
// ---------------------------------------------------------------------------

/// Entry visited during a depth-first walk of the info tree.
enum InfoVisit<'a> {
    Node(&'a crate::info_tree::InfoNode),
    Leaf(&'a InfoData),
}

/// Walk the info tree depth-first, calling `visitor` for every node and leaf.
fn visit_tree(tree: &InfoTree, visitor: &mut dyn FnMut(InfoVisit<'_>)) {
    match tree {
        InfoTree::Node { node, children } => {
            visitor(InfoVisit::Node(node));
            for child in children {
                visit_tree(child, visitor);
            }
        }
        InfoTree::Leaf(data) => visitor(InfoVisit::Leaf(data)),
    }
}

// ---------------------------------------------------------------------------
// Extraction functions
// ---------------------------------------------------------------------------

/// Extract hover info from all `TermInfo` nodes.
#[must_use]
pub(crate) fn extract_hover_info(tree: &InfoTree) -> Vec<HoverInfo> {
    let mut out = Vec::new();
    visit_tree(tree, &mut |v| {
        if let InfoVisit::Node(node) = v {
            if let InfoKind::TermInfo {
                elaborated, type_, ..
            } = &node.kind
            {
                out.push(HoverInfo {
                    span_start: node.span.start,
                    span_end: node.span.end,
                    expr_text: format!("{elaborated}"),
                    type_text: format!("{type_}"),
                });
            }
        }
    });
    out
}

/// Extract go-to-definition entries from `FieldInfo` nodes and
/// `DefinitionHover` leaves.
#[must_use]
pub(crate) fn extract_goto_definitions(tree: &InfoTree) -> Vec<GoToDefinitionInfo> {
    let mut out = Vec::new();
    visit_tree(tree, &mut |v| match v {
        InfoVisit::Node(node) => {
            if let InfoKind::FieldInfo {
                struct_name,
                field_name,
            } = &node.kind
            {
                out.push(GoToDefinitionInfo {
                    name: format!("{struct_name}.{field_name}"),
                    target_span: None,
                    type_text: String::new(),
                });
            }
        }
        InfoVisit::Leaf(data) => {
            if let InfoData::DefinitionHover(name, ty) = data {
                out.push(GoToDefinitionInfo {
                    name: format!("{name}"),
                    target_span: None,
                    type_text: format!("{ty}"),
                });
            }
        }
    });
    out
}

/// Extract completion candidates from `CompletionContext` leaves.
#[must_use]
pub(crate) fn extract_completions(tree: &InfoTree) -> Vec<CompletionCandidate> {
    let mut out = Vec::new();
    visit_tree(tree, &mut |v| {
        if let InfoVisit::Leaf(InfoData::CompletionContext(_prefix, candidates)) = v {
            for (i, name) in candidates.iter().enumerate() {
                let label = format!("{name}");
                out.push(CompletionCandidate {
                    sort_text: format!("{i:05}"),
                    label,
                    type_signature: String::new(),
                    detail: None,
                });
            }
        }
    });
    out
}

/// Classify nodes into semantic tokens for syntax highlighting.
#[must_use]
pub(crate) fn collect_semantic_tokens(tree: &InfoTree) -> Vec<SemanticToken> {
    let mut out = Vec::new();
    visit_tree(tree, &mut |v| {
        if let InfoVisit::Node(node) = v {
            let kind = match &node.kind {
                InfoKind::CommandInfo { .. } => SemanticTokenKind::Keyword,
                InfoKind::TermInfo { .. } => SemanticTokenKind::Variable,
                InfoKind::FieldInfo { .. } => SemanticTokenKind::Property,
                InfoKind::TacticInfo { .. } => SemanticTokenKind::Function,
                InfoKind::MacroExpansion { .. } => SemanticTokenKind::Function,
            };
            out.push(SemanticToken {
                span_start: node.span.start,
                span_end: node.span.end,
                kind,
            });
        }
    });
    out
}

/// Extract document symbols from `CommandInfo` nodes.
#[must_use]
pub(crate) fn collect_document_symbols(tree: &InfoTree) -> Vec<DocumentSymbol> {
    let mut out = Vec::new();
    visit_tree(tree, &mut |v| {
        if let InfoVisit::Node(node) = v {
            if let InfoKind::CommandInfo { command_name } = &node.kind {
                if command_name.is_empty() {
                    return;
                }
                let kind = match command_name.as_str() {
                    "theorem" => DocumentSymbolKind::Theorem,
                    "inductive" => DocumentSymbolKind::Inductive,
                    "structure" => DocumentSymbolKind::Structure,
                    "instance" => DocumentSymbolKind::Instance,
                    "class" => DocumentSymbolKind::Class,
                    "namespace" => DocumentSymbolKind::Namespace,
                    "tactic" => DocumentSymbolKind::Tactic,
                    _ => DocumentSymbolKind::Definition,
                };
                out.push(DocumentSymbol {
                    name: command_name.clone(),
                    kind,
                    span_start: node.span.start,
                    span_end: node.span.end,
                    detail: None,
                    children: Vec::new(),
                });
            }
        }
    });
    out
}

/// Collect references grouped by definition name from `FieldInfo` nodes.
#[must_use]
pub(crate) fn collect_references(tree: &InfoTree) -> Vec<ReferenceInfo> {
    let mut map: HashMap<String, Vec<(usize, usize)>> = HashMap::new();
    visit_tree(tree, &mut |v| {
        if let InfoVisit::Node(node) = v {
            if let InfoKind::FieldInfo { field_name, .. } = &node.kind {
                let key = format!("{field_name}");
                map.entry(key)
                    .or_default()
                    .push((node.span.start, node.span.end));
            }
        }
    });
    map.into_iter()
        .map(|(definition_name, usage_spans)| ReferenceInfo {
            definition_name,
            usage_spans,
        })
        .collect()
}

/// Compute aggregate statistics over the info tree.
#[must_use]
pub(crate) fn compute_stats(tree: &InfoTree) -> InfoTreeStats {
    let mut stats = InfoTreeStats::default();
    visit_tree(tree, &mut |v| match v {
        InfoVisit::Node(node) => {
            stats.total_nodes += 1;
            match &node.kind {
                InfoKind::TermInfo { .. } => stats.term_info_count += 1,
                InfoKind::TacticInfo { .. } => stats.tactic_info_count += 1,
                InfoKind::FieldInfo { .. } => stats.field_info_count += 1,
                InfoKind::CommandInfo { .. } => stats.command_info_count += 1,
                InfoKind::MacroExpansion { .. } => stats.macro_expansion_count += 1,
            }
        }
        InfoVisit::Leaf(_) => {
            stats.total_leaves += 1;
        }
    });
    stats
}

/// Build the full extended info tree from a base [`InfoTree`].
#[must_use]
pub(crate) fn build_extended_info_tree(tree: &InfoTree) -> ExtendedInfoTree {
    ExtendedInfoTree {
        hover_info: extract_hover_info(tree),
        goto_definitions: extract_goto_definitions(tree),
        completions: extract_completions(tree),
        diagnostics: Vec::new(), // populated externally via diagnostics API
        semantic_tokens: collect_semantic_tokens(tree),
        folding_ranges: Vec::new(), // populated externally via line mapping
        document_symbols: collect_document_symbols(tree),
        references: collect_references(tree),
        stats: compute_stats(tree),
    }
}

/// Serialize an [`ExtendedInfoTree`] to pretty-printed JSON.
pub(crate) fn serialize_info_tree(ext: &ExtendedInfoTree) -> Result<String, serde_json::Error> {
    serde_json::to_string_pretty(ext)
}
