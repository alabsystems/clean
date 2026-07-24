// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Navigation and code intelligence: hover, definition, references, rename, completion, symbols.

use super::{CleanBackend, DefinitionInfo};
use crate::document::{CommandKind, ElaboratedDecl, ElaboratedDocument};
use clean_parser::lexer::{Lexer, TokenKind};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use tower_lsp::lsp_types::*;

/// Opaque payload attached to an [`InlayHint`] so that `inlayHint/resolve` can
/// recover the declaration the hint was produced for and lazily compute its
/// resolvable fields (tooltip / label detail) without re-running elaboration
/// for the whole document.
///
/// The LSP spec treats `InlayHint::data` as an opaque value owned by the
/// server: the client round-trips it verbatim between `textDocument/inlayHint`
/// and `inlayHint/resolve`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct InlayHintData {
    /// Document the hint belongs to (so resolve can find the live document
    /// even though resolve requests do not carry a `textDocument`).
    pub(crate) uri: String,
    /// Name of the declaration whose inferred type the hint surfaces.
    pub(crate) name: String,
}

impl InlayHintData {
    /// Encode into the `serde_json::Value` shape the `InlayHint::data` field
    /// expects. Returns `None` if serialization fails, which degrades the hint
    /// to a non-resolvable (but still valid) hint rather than dropping it.
    pub(crate) fn to_value(&self) -> Option<serde_json::Value> {
        serde_json::to_value(self).ok()
    }

    /// Decode from an `InlayHint::data` value, returning `None` when the value
    /// is absent or does not match our payload shape (e.g. a hint produced by a
    /// different code path or protocol version).
    pub(crate) fn from_value(value: &serde_json::Value) -> Option<Self> {
        serde_json::from_value(value.clone()).ok()
    }
}

/// Opaque payload attached to a [`CompletionItem`] so that
/// `completionItem/resolve` can recover the declaration the item refers to and
/// lazily compute its expensive fields (detail signature / documentation)
/// without re-listing every completion for the document.
///
/// As with inlay hints, the LSP spec treats `CompletionItem::data` as an opaque
/// value owned by the server: the client round-trips it verbatim between
/// `textDocument/completion` and `completionItem/resolve`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct CompletionItemData {
    /// Document the completed declaration belongs to (so resolve can find the
    /// live document even though resolve requests carry no `textDocument`).
    pub(crate) uri: String,
    /// Name of the declaration the completion item inserts.
    pub(crate) name: String,
}

impl CompletionItemData {
    /// Encode into the `serde_json::Value` shape the `CompletionItem::data`
    /// field expects. Returns `None` if serialization fails, which degrades the
    /// item to a non-resolvable (but still valid) item rather than dropping it.
    pub(crate) fn to_value(&self) -> Option<serde_json::Value> {
        serde_json::to_value(self).ok()
    }

    /// Decode from a `CompletionItem::data` value, returning `None` when the
    /// value is absent or does not match our payload shape (e.g. an item
    /// produced by a different code path, such as the keyword completions).
    pub(crate) fn from_value(value: &serde_json::Value) -> Option<Self> {
        serde_json::from_value(value.clone()).ok()
    }
}

impl CleanBackend {
    /// Get hover information at a position
    pub(crate) fn get_hover_at(&self, uri: &Url, position: Position) -> Option<Hover> {
        let doc = self.documents.get(uri)?;

        if let Some(elab) = &doc.elaborated {
            for decl in &elab.declarations {
                let start_pos = doc.offset_to_position(decl.start);
                let end_pos = doc.offset_to_position(decl.end);

                if start_pos <= position && position < end_pos {
                    return Some(Hover {
                        contents: HoverContents::Markup(MarkupContent {
                            kind: MarkupKind::Markdown,
                            value: format!("```lean\n{} : {}\n```", decl.name, decl.type_str),
                        }),
                        range: Some(Range {
                            start: start_pos,
                            end: end_pos,
                        }),
                    });
                }
            }
        }

        None
    }

    /// Get the identifier at a position in a document
    pub(crate) fn get_identifier_at(&self, uri: &Url, position: Position) -> Option<String> {
        let doc = self.documents.get(uri)?;
        let text = doc.text();
        let offset = doc.position_to_offset(position);
        let (start, end) = Self::identifier_span_at(&text, offset)?;
        Some(text[start..end].to_string())
    }

    /// Compute inlay hints for the visible range.
    ///
    /// The current slice only surfaces inferred result types for `def`
    /// declarations that omit an explicit `: ty`. Returns no hints when the
    /// caller signals that inlay hints are disabled via configuration (the
    /// `clean.inlayHints.enable` setting; see `CleanConfig`).
    pub(crate) fn get_inlay_hints(&self, uri: &Url, range: Range, enabled: bool) -> Vec<InlayHint> {
        if !enabled {
            return vec![];
        }
        let Some(doc) = self.documents.get(uri) else {
            return vec![];
        };
        let Some(elab) = &doc.elaborated else {
            return vec![];
        };

        let text = doc.text();
        let Ok(decls) = clean_parser::parse_file_with_tactics(&text, &self.tactic_patterns) else {
            return vec![];
        };
        decls
            .into_iter()
            .filter_map(|decl| match decl {
                clean_parser::SurfaceDecl::Def {
                    name,
                    span,
                    ty: None,
                    val,
                    ..
                } => {
                    let type_str = Self::find_elaborated_decl(elab, &name, span.start, span.end)?
                        .type_str
                        .as_str();
                    let hint_offset =
                        Self::find_result_type_hint_offset(&text, span.start, val.span().start);
                    let position = doc.offset_to_position(hint_offset);

                    Self::range_contains_position(range, position).then(|| InlayHint {
                        position,
                        label: InlayHintLabel::String(format!(": {type_str}")),
                        kind: Some(InlayHintKind::TYPE),
                        text_edits: None,
                        tooltip: Some(InlayHintTooltip::String("Inferred result type".to_string())),
                        padding_left: Some(true),
                        padding_right: Some(true),
                        // Carry the source declaration so `inlayHint/resolve`
                        // can lazily upgrade the tooltip to a full signature.
                        data: InlayHintData {
                            uri: uri.to_string(),
                            name: name.clone(),
                        }
                        .to_value(),
                    })
                }
                _ => None,
            })
            .collect()
    }

    /// Resolve the lazily-computable fields of an [`InlayHint`] for an
    /// `inlayHint/resolve` request.
    ///
    /// The hint is enriched in place: if it carries an [`InlayHintData`]
    /// payload pointing at a declaration whose elaborated type we still know,
    /// the tooltip is upgraded to the declaration's full `name : type`
    /// signature (rendered as Lean-fenced markdown, matching hover). Any hint
    /// without a resolvable payload — or one whose document/declaration is no
    /// longer available — is returned unchanged (a clean pass-through), which
    /// is the behaviour the LSP spec requires for hints the server cannot
    /// further resolve.
    pub(crate) fn resolve_inlay_hint(&self, mut hint: InlayHint) -> InlayHint {
        let Some(data) = hint.data.as_ref().and_then(InlayHintData::from_value) else {
            return hint;
        };
        let Ok(uri) = Url::parse(&data.uri) else {
            return hint;
        };
        let Some(doc) = self.documents.get(&uri) else {
            return hint;
        };
        let Some(elab) = &doc.elaborated else {
            return hint;
        };
        let Some(decl) = elab.declarations.iter().find(|decl| decl.name == data.name) else {
            return hint;
        };

        hint.tooltip = Some(InlayHintTooltip::MarkupContent(MarkupContent {
            kind: MarkupKind::Markdown,
            value: format!("```lean\n{} : {}\n```", decl.name, decl.type_str),
        }));
        hint
    }

    /// Resolve the lazily-computable fields of a [`CompletionItem`] for a
    /// `completionItem/resolve` request.
    ///
    /// The item is enriched in place: if it carries a [`CompletionItemData`]
    /// payload pointing at a declaration whose elaborated type we still know,
    /// the item's `detail` is set to the declaration's type signature and its
    /// `documentation` to the same `name : type` rendered as Lean-fenced
    /// markdown (matching hover). Any item without a resolvable payload — e.g.
    /// a keyword completion, or one whose document/declaration is no longer
    /// available — is returned unchanged (a clean pass-through), which is the
    /// behaviour the LSP spec requires for items the server cannot further
    /// resolve.
    pub(crate) fn resolve_completion_item(&self, mut item: CompletionItem) -> CompletionItem {
        let Some(data) = item.data.as_ref().and_then(CompletionItemData::from_value) else {
            return item;
        };
        let Ok(uri) = Url::parse(&data.uri) else {
            return item;
        };
        let Some(doc) = self.documents.get(&uri) else {
            return item;
        };
        let Some(elab) = &doc.elaborated else {
            return item;
        };
        let Some(decl) = elab.declarations.iter().find(|decl| decl.name == data.name) else {
            return item;
        };

        item.detail = Some(decl.type_str.clone());
        item.documentation = Some(Documentation::MarkupContent(MarkupContent {
            kind: MarkupKind::Markdown,
            value: format!("```lean\n{} : {}\n```", decl.name, decl.type_str),
        }));
        item
    }

    fn find_elaborated_decl<'a>(
        elab: &'a ElaboratedDocument,
        name: &str,
        start: usize,
        end: usize,
    ) -> Option<&'a ElaboratedDecl> {
        elab.declarations.iter().find(|decl| {
            decl.name == name && Self::ranges_overlap_offsets(start, end, decl.start, decl.end)
        })
    }

    /// Check if a character can start a Lean identifier.
    pub(crate) fn is_identifier_start(c: char) -> bool {
        c.is_alphabetic() || c == '_' || (c.is_numeric() && !c.is_ascii_digit())
    }

    /// Check if a character can continue a Lean identifier.
    pub(crate) fn is_identifier_continue(c: char) -> bool {
        c.is_alphanumeric() || matches!(c, '_' | '\'' | '?' | '!')
    }

    /// Validate a Lean identifier using the parser's start/continue rules.
    pub(crate) fn is_valid_identifier(name: &str) -> bool {
        let mut chars = name.chars();
        let Some(first) = chars.next() else {
            return false;
        };

        Self::is_identifier_start(first) && chars.all(Self::is_identifier_continue)
    }

    /// Return the byte span of the identifier at or immediately before `offset`.
    pub(crate) fn identifier_span_at(text: &str, offset: usize) -> Option<(usize, usize)> {
        let anchor = Self::identifier_anchor(text, offset)?;
        let mut start = anchor;
        while let Some((prev_idx, ch)) = text[..start].char_indices().next_back() {
            if !Self::is_identifier_continue(ch) {
                break;
            }
            start = prev_idx;
        }

        let mut end = anchor;
        while let Some(ch) = text[end..].chars().next() {
            if !Self::is_identifier_continue(ch) {
                break;
            }
            end += ch.len_utf8();
        }

        Some((start, end))
    }

    fn identifier_anchor(text: &str, offset: usize) -> Option<usize> {
        let mut offset = offset.min(text.len());
        while offset > 0 && !text.is_char_boundary(offset) {
            offset -= 1;
        }

        if let Some(ch) = text.get(offset..)?.chars().next() {
            if Self::is_identifier_continue(ch) {
                return Some(offset);
            }
        }

        let (prev_idx, prev_ch) = text.get(..offset)?.char_indices().next_back()?;
        if Self::is_identifier_continue(prev_ch) {
            Some(prev_idx)
        } else {
            None
        }
    }

    fn has_identifier_char_before(text: &str, offset: usize) -> bool {
        text.get(..offset)
            .and_then(|prefix| prefix.chars().next_back())
            .is_some_and(Self::is_identifier_continue)
    }

    fn has_identifier_char_after(text: &str, offset: usize) -> bool {
        text.get(offset..)
            .and_then(|suffix| suffix.chars().next())
            .is_some_and(Self::is_identifier_continue)
    }

    fn find_result_type_hint_offset(text: &str, decl_start: usize, body_start: usize) -> usize {
        let body_start = body_start.min(text.len());
        let decl_start = decl_start.min(body_start);
        let prefix = &text[decl_start..body_start];

        prefix
            .rfind(":=")
            .map_or(body_start, |idx| decl_start + idx)
    }

    fn range_contains_position(range: Range, position: Position) -> bool {
        range.start <= position && position < range.end
    }

    fn ranges_overlap_offsets(a_start: usize, a_end: usize, b_start: usize, b_end: usize) -> bool {
        a_start < b_end && b_start < a_end
    }

    /// Find the definition location for a name
    pub(crate) fn find_definition(&self, name: &str) -> Option<(Url, Range)> {
        if let Some(def_info) = self.definitions.get(name) {
            if let Some(doc) = self.documents.get(&def_info.uri) {
                let start = doc.offset_to_position(def_info.start);
                let end = doc.offset_to_position(def_info.end);
                return Some((def_info.uri.clone(), Range { start, end }));
            }
        }
        None
    }

    /// Find all references to a name across all documents
    pub(crate) fn find_references(&self, name: &str, include_definition: bool) -> Vec<Location> {
        let mut references = Vec::new();

        for doc_entry in &self.documents {
            let uri = doc_entry.key();
            let doc = doc_entry.value();
            let text = doc.text();

            // Simple text search for the identifier
            let mut search_pos = 0;
            while let Some(found_pos) = text[search_pos..].find(name) {
                let abs_pos = search_pos + found_pos;

                // Check if this is a whole identifier match
                let is_start_boundary =
                    abs_pos == 0 || !Self::has_identifier_char_before(&text, abs_pos);
                let end_pos = abs_pos + name.len();
                let is_end_boundary =
                    end_pos >= text.len() || !Self::has_identifier_char_after(&text, end_pos);

                if is_start_boundary && is_end_boundary {
                    let start = doc.offset_to_position(abs_pos);
                    let end = doc.offset_to_position(end_pos);

                    // Skip definition if not including it
                    if !include_definition {
                        if let Some(def_info) = self.definitions.get(name) {
                            if &def_info.uri == uri && def_info.name_start == abs_pos {
                                search_pos = end_pos;
                                continue;
                            }
                        }
                    }

                    references.push(Location {
                        uri: uri.clone(),
                        range: Range { start, end },
                    });
                }

                let Some(next_char) = text[abs_pos..].chars().next() else {
                    break;
                };
                search_pos = abs_pos + next_char.len_utf8();
            }
        }

        references
    }

    /// Compute document highlights for the identifier under the cursor.
    ///
    /// Reuses the same whole-identifier occurrence scan as `find_references`
    /// (including the declaration site) but restricts results to `uri`, since
    /// `textDocument/documentHighlight` is document-local by contract. Each
    /// occurrence is returned with `DocumentHighlightKind::TEXT`; clean does not
    /// yet distinguish read vs. write access for Lean identifiers, and `TEXT`
    /// is the protocol-specified default.
    pub(crate) fn document_highlights_at(
        &self,
        uri: &Url,
        position: Position,
    ) -> Option<Vec<DocumentHighlight>> {
        let name = self.get_identifier_at(uri, position)?;

        let highlights: Vec<DocumentHighlight> = self
            .find_references(&name, true)
            .into_iter()
            .filter(|loc| &loc.uri == uri)
            .map(|loc| DocumentHighlight {
                range: loc.range,
                kind: Some(DocumentHighlightKind::TEXT),
            })
            .collect();

        (!highlights.is_empty()).then_some(highlights)
    }

    /// Resolve the type-definition location for the identifier under the cursor.
    ///
    /// Go-to-type-definition differs from go-to-definition: instead of jumping
    /// to where the symbol is declared, it jumps to where the *type* of that
    /// symbol is declared. The flow is:
    ///   1. resolve the identifier to its own [`DefinitionInfo`];
    ///   2. read the elaborated type of that declaration (`type_str`);
    ///   3. extract the type's named head constants and return the location of
    ///      the first one that is itself an indexed definition in the workspace.
    ///
    /// When the type is a primitive/builtin with no in-workspace declaration
    /// (e.g. `Nat` from the prelude) there is nothing to navigate to, so this
    /// returns `None` rather than guessing.
    pub(crate) fn find_type_definition_at(
        &self,
        uri: &Url,
        position: Position,
    ) -> Option<(Url, Range)> {
        let name = self.get_identifier_at(uri, position)?;
        let type_str = self.declared_type_str(&name)?;

        Self::type_name_candidates(&type_str)
            .into_iter()
            // Skip self-references: a constant whose type mentions its own name
            // (e.g. a recursor) should not resolve back onto itself.
            .filter(|candidate| candidate != &name)
            .find_map(|candidate| self.find_definition(&candidate))
    }

    /// The elaborated, pretty-printed type string of an indexed declaration, if
    /// the owning document is still open and has been elaborated.
    fn declared_type_str(&self, name: &str) -> Option<String> {
        let def_info = self.definitions.get(name)?;
        let doc = self.documents.get(&def_info.uri)?;
        let elab = doc.elaborated.as_ref()?;
        Self::find_elaborated_decl(elab, name, def_info.start, def_info.end)
            .map(|decl| decl.type_str.clone())
    }

    /// Extract candidate type-constant names from a declaration's type string,
    /// preserving first-appearance order.
    ///
    /// The elaborated `type_str` may be either a clean pretty-printed name
    /// (`"Bar"`, `"List Nat"`) or a structural debug rendering whose name
    /// components surface as identifier tokens. In both cases the named head
    /// constants appear as ordinary Lean identifier substrings, so a single
    /// identifier scan recovers the candidates; resolution against the
    /// definition index then filters out non-declarations (debug field labels,
    /// builtins, etc.).
    pub(crate) fn type_name_candidates(type_str: &str) -> Vec<String> {
        let mut candidates = Vec::new();
        let mut index = 0usize;
        while index < type_str.len() {
            let Some(ch) = type_str[index..].chars().next() else {
                break;
            };
            if Self::is_identifier_start(ch) {
                let start = index;
                let mut end = index + ch.len_utf8();
                while let Some(next) = type_str[end..].chars().next() {
                    if !Self::is_identifier_continue(next) {
                        break;
                    }
                    end += next.len_utf8();
                }
                let token = &type_str[start..end];
                if !candidates.iter().any(|existing| existing == token) {
                    candidates.push(token.to_string());
                }
                index = end;
            } else {
                // `ch` is the full char at `index`, so advancing by its UTF-8
                // length always lands on the next char boundary.
                index += ch.len_utf8();
            }
        }
        candidates
    }

    /// Prepare rename operation - validate the position contains a renameable identifier
    pub(crate) fn prepare_rename_at(
        &self,
        uri: &Url,
        position: Position,
    ) -> Option<(String, Range)> {
        let name = self.get_identifier_at(uri, position)?;

        // Find the exact range of the identifier at this position
        let doc = self.documents.get(uri)?;
        let text = doc.text();
        let offset = doc.position_to_offset(position);
        let (start, end) = Self::identifier_span_at(&text, offset)?;

        let start_pos = doc.offset_to_position(start);
        let end_pos = doc.offset_to_position(end);

        Some((
            name,
            Range {
                start: start_pos,
                end: end_pos,
            },
        ))
    }

    /// Create workspace edits to rename a symbol
    pub(crate) fn create_rename_edits(&self, old_name: &str, new_name: &str) -> WorkspaceEdit {
        use std::collections::HashMap;

        let references = self.find_references(old_name, true);
        let mut changes: HashMap<Url, Vec<TextEdit>> = HashMap::new();

        for location in references {
            changes.entry(location.uri).or_default().push(TextEdit {
                range: location.range,
                new_text: new_name.to_string(),
            });
        }

        WorkspaceEdit {
            changes: Some(changes),
            document_changes: None,
            change_annotations: None,
        }
    }

    /// Get the completion prefix and replacement range at a position.
    pub(crate) fn get_completion_prefix_span(
        &self,
        uri: &Url,
        position: Position,
    ) -> (String, Option<Range>) {
        if let Some(doc) = self.documents.get(uri) {
            let text = doc.text();
            let offset = doc.position_to_offset(position);
            if let Some((start, _)) = Self::identifier_span_at(&text, offset) {
                if start < offset {
                    return (
                        text[start..offset].to_string(),
                        Some(Range {
                            start: doc.offset_to_position(start),
                            end: doc.offset_to_position(offset),
                        }),
                    );
                }
            }
        }

        (String::new(), None)
    }

    /// Get the completion kind for a definition
    pub(crate) fn get_definition_kind(&self, name: &str) -> CompletionItemKind {
        // Look up the parsed document to find the command kind
        if let Some(def_info) = self.definitions.get(name) {
            if let Some(doc) = self.documents.get(&def_info.uri) {
                if let Some(parsed) = &doc.parsed {
                    for cmd in &parsed.commands {
                        if cmd.name.as_ref() == Some(&name.to_string()) {
                            return match cmd.kind {
                                CommandKind::Definition => CompletionItemKind::FUNCTION,
                                CommandKind::Theorem | CommandKind::Lemma => {
                                    CompletionItemKind::FUNCTION
                                }
                                CommandKind::Inductive | CommandKind::Structure => {
                                    CompletionItemKind::CLASS
                                }
                                CommandKind::Class => CompletionItemKind::INTERFACE,
                                CommandKind::Instance => CompletionItemKind::REFERENCE,
                                CommandKind::Axiom => CompletionItemKind::CONSTANT,
                                _ => CompletionItemKind::TEXT,
                            };
                        }
                    }
                }
            }
        }
        CompletionItemKind::TEXT
    }

    /// Short human-readable category label for a defined name, used as the
    /// description on richer completion items (e.g. shown alongside the type
    /// signature in the editor's completion popup).
    pub(crate) fn get_definition_category_label(&self, name: &str) -> Option<&'static str> {
        let def_info = self.definitions.get(name)?;
        let doc = self.documents.get(&def_info.uri)?;
        let parsed = doc.parsed.as_ref()?;
        for cmd in &parsed.commands {
            if cmd.name.as_ref() == Some(&name.to_string()) {
                return Some(match cmd.kind {
                    CommandKind::Definition => "def",
                    CommandKind::Theorem => "theorem",
                    CommandKind::Lemma => "lemma",
                    CommandKind::Inductive => "inductive",
                    CommandKind::Structure => "structure",
                    CommandKind::Class => "class",
                    CommandKind::Instance => "instance",
                    CommandKind::Axiom => "axiom",
                    CommandKind::Variable => "variable",
                    CommandKind::Namespace => "namespace",
                    _ => return None,
                });
            }
        }
        None
    }

    /// Get live checked type information for a completion item.
    pub(crate) fn get_completion_detail(&self, name: &str) -> Option<String> {
        let def_info = self.definitions.get(name)?;
        let doc = self.documents.get(&def_info.uri)?;
        let elab = doc.elaborated.as_ref()?;

        elab.declarations
            .iter()
            .find(|decl| {
                decl.name == name
                    && Self::ranges_overlap_offsets(
                        def_info.start,
                        def_info.end,
                        decl.start,
                        decl.end,
                    )
            })
            .map(|decl| decl.type_str.clone())
    }

    /// Get checked declaration signature help for the identifier before a position.
    pub(crate) fn get_signature_help_at(
        &self,
        uri: &Url,
        position: Position,
    ) -> Option<SignatureHelp> {
        let doc = self.documents.get(uri)?;
        let text = doc.text();
        let offset = doc.position_to_offset(position);
        let (name, argument_count) = self.signature_call_context(&text, offset)?;
        let detail = self.get_completion_detail(name)?;
        let display_detail = self
            .get_signature_display_detail(uri, name)
            .filter(|source_detail| Self::signature_parameter_domains(source_detail).is_some())
            .unwrap_or_else(|| detail.clone());
        let label = format!("{name} : {display_detail}");
        let parameters = Self::signature_parameters(&label, name, &display_detail)
            .or_else(|| Self::signature_parameters(&label, name, &detail));
        let active_parameter = parameters
            .as_ref()
            .filter(|parameters| !parameters.is_empty())
            .map(|parameters| argument_count.min(parameters.len().saturating_sub(1)) as u32);

        Some(SignatureHelp {
            signatures: vec![SignatureInformation {
                label,
                documentation: None,
                parameters,
                active_parameter,
            }],
            active_signature: Some(0),
            active_parameter,
        })
    }

    fn get_signature_display_detail(&self, uri: &Url, name: &str) -> Option<String> {
        let doc = self.documents.get(uri)?;
        let text = doc.text();
        let decls = clean_parser::parse_file_with_tactics(&text, &self.tactic_patterns).ok()?;

        decls.iter().find_map(|decl| {
            let (decl_name, ty) = match decl {
                clean_parser::SurfaceDecl::Def {
                    name, ty: Some(ty), ..
                }
                | clean_parser::SurfaceDecl::Theorem { name, ty, .. }
                | clean_parser::SurfaceDecl::Axiom { name, ty, .. }
                | clean_parser::SurfaceDecl::Opaque { name, ty, .. } => {
                    (name.as_str(), ty.as_ref())
                }
                _ => return None,
            };
            if decl_name != name {
                return None;
            }

            let span = ty.span();
            text.get(span.start..span.end)
                .map(str::trim)
                .filter(|ty| !ty.is_empty())
                .map(str::to_string)
        })
    }

    fn signature_call_context<'a>(&self, text: &'a str, offset: usize) -> Option<(&'a str, usize)> {
        let prefix = text.get(..offset)?.trim_end_matches(char::is_whitespace);
        let line_start = prefix.rfind('\n').map_or(0, |index| index + 1);
        let mut search_offset = line_start;

        while search_offset < prefix.len() {
            let Some((relative_start, ch)) = prefix[search_offset..]
                .char_indices()
                .find(|(_, ch)| Self::is_identifier_start(*ch))
            else {
                break;
            };
            let start = search_offset + relative_start;
            let mut end = start + ch.len_utf8();
            while let Some(ch) = prefix[end..].chars().next() {
                if !Self::is_identifier_continue(ch) {
                    break;
                }
                end += ch.len_utf8();
            }

            let name = prefix.get(start..end)?;
            if self.get_completion_detail(name).is_some() {
                let argument_count = Self::signature_argument_count(prefix.get(end..)?);
                return Some((name, argument_count));
            }
            search_offset = end;
        }

        None
    }

    fn signature_argument_count(text_after_name: &str) -> usize {
        text_after_name.split_whitespace().count()
    }

    fn signature_parameters(
        label: &str,
        name: &str,
        detail: &str,
    ) -> Option<Vec<ParameterInformation>> {
        let domains = Self::signature_parameter_domains(detail)?;

        let mut search_start = name.len() + " : ".len();
        let mut parameters = Vec::with_capacity(domains.len());
        for domain in domains {
            let relative_start = label.get(search_start..)?.find(domain)?;
            let start = search_start + relative_start;
            let end = start + domain.len();
            parameters.push(ParameterInformation {
                label: ParameterLabel::LabelOffsets([start as u32, end as u32]),
                documentation: None,
            });
            search_start = end;
        }

        Some(parameters)
    }

    fn signature_parameter_domains(detail: &str) -> Option<Vec<&str>> {
        if let Some(domains) = Self::signature_arrow_parameter_domains(detail) {
            return Some(domains);
        }
        Self::signature_pi_parameter_domains(detail)
    }

    fn signature_arrow_parameter_domains(detail: &str) -> Option<Vec<&str>> {
        let mut domains = Vec::new();
        let mut start = 0;

        while let Some((arrow_start, arrow_len)) = Self::find_signature_arrow(detail, start) {
            domains.push(detail.get(start..arrow_start)?.trim());
            start = arrow_start + arrow_len;
        }

        (!domains.is_empty()).then_some(domains)
    }

    fn signature_pi_parameter_domains(mut detail: &str) -> Option<Vec<&str>> {
        let mut domains = Vec::new();

        while detail.starts_with("Pi(") {
            let first_comma = Self::find_top_level_comma(detail, "Pi(".len())?;
            let domain_start = first_comma + 1;
            let second_comma = Self::find_top_level_comma(detail, domain_start)?;
            let domain = detail.get(domain_start..second_comma)?.trim();
            if domain.is_empty() {
                break;
            }
            if !domain.starts_with("Sort(") {
                domains.push(domain);
            }

            let body_start = second_comma + 1;
            let body_end = Self::find_matching_delimiter(detail, 2, '(', ')')?;
            detail = detail.get(body_start..body_end)?.trim();
        }

        (!domains.is_empty()).then_some(domains)
    }

    fn find_top_level_comma(text: &str, start: usize) -> Option<usize> {
        let mut depth = 0usize;
        for (index, ch) in text.get(start..)?.char_indices() {
            let absolute = start + index;
            match ch {
                '(' | '[' | '{' => depth += 1,
                ')' | ']' | '}' => depth = depth.saturating_sub(1),
                ',' if depth == 0 => return Some(absolute),
                _ => {}
            }
        }
        None
    }

    fn find_matching_delimiter(
        text: &str,
        open_index: usize,
        open: char,
        close: char,
    ) -> Option<usize> {
        let mut depth = 0usize;
        for (relative, ch) in text.get(open_index..)?.char_indices() {
            let index = open_index + relative;
            if ch == open {
                depth += 1;
            } else if ch == close {
                depth = depth.checked_sub(1)?;
                if depth == 0 {
                    return Some(index);
                }
            }
        }
        None
    }

    fn find_signature_arrow(detail: &str, start: usize) -> Option<(usize, usize)> {
        let ascii = detail
            .get(start..)?
            .find("->")
            .map(|index| (start + index, "->".len()));
        let unicode = detail
            .get(start..)?
            .find('→')
            .map(|index| (start + index, '→'.len_utf8()));

        match (ascii, unicode) {
            (Some(ascii), Some(unicode)) => Some(ascii.min(unicode)),
            (Some(ascii), None) => Some(ascii),
            (None, Some(unicode)) => Some(unicode),
            (None, None) => None,
        }
    }

    /// Get document symbols.
    ///
    /// Builds a hierarchical [`DocumentSymbol`] tree from the parsed surface
    /// declarations. Two LSP-conformance refinements over a naive flat dump:
    ///
    /// 1. `selection_range` points at the declaration's *name* span (the
    ///    identifier the editor highlights when the symbol is selected), not
    ///    the whole declaration. It falls back to the full `range` when no name
    ///    span can be located, and always stays contained within `range`.
    /// 2. `children` nests members under their enclosing scope: declarations
    ///    inside `namespace`/`section` blocks become children of that scope
    ///    (recursively), and `structure`/`class` fields become children of the
    ///    type. This mirrors Lean's outline view.
    pub(crate) fn get_document_symbols(&self, uri: &Url) -> Option<Vec<DocumentSymbol>> {
        let doc = self.documents.get(uri)?;
        let text = doc.text();

        // Re-parse to recover the nested `SurfaceDecl` tree: `ParsedDocument`
        // flattens scopes, losing the namespace/section/field nesting needed
        // for a hierarchical outline.
        let report =
            clean_parser::parse_file_with_tactics_diagnostics(&text, &self.tactic_patterns).ok()?;

        let symbols = report
            .decls
            .iter()
            .filter_map(|decl| Self::surface_decl_to_symbol(&doc, &text, decl))
            .collect();

        Some(symbols)
    }

    /// Map the [`CommandKind`] of a declaration to an LSP [`SymbolKind`].
    fn symbol_kind_for_command(kind: &CommandKind) -> SymbolKind {
        match kind {
            CommandKind::Definition | CommandKind::Theorem | CommandKind::Lemma => {
                SymbolKind::FUNCTION
            }
            CommandKind::Inductive | CommandKind::Coinductive | CommandKind::Structure => {
                SymbolKind::CLASS
            }
            CommandKind::Class => SymbolKind::INTERFACE,
            CommandKind::Instance => SymbolKind::OBJECT,
            CommandKind::Axiom => SymbolKind::CONSTANT,
            CommandKind::Variable => SymbolKind::VARIABLE,
            CommandKind::Universe => SymbolKind::TYPE_PARAMETER,
            CommandKind::Namespace => SymbolKind::NAMESPACE,
            CommandKind::Section => SymbolKind::MODULE,
            _ => SymbolKind::NULL,
        }
    }

    /// Build a [`DocumentSymbol`] (recursively, for scopes) from a surface decl.
    ///
    /// Returns `None` for unnamed/structural decls that should not appear in the
    /// outline (imports, `open`, anonymous `example`, bare `end`, ...).
    fn surface_decl_to_symbol(
        doc: &crate::document::Document,
        text: &str,
        decl: &clean_parser::SurfaceDecl,
    ) -> Option<DocumentSymbol> {
        use clean_parser::SurfaceDecl;

        let (kind, name, (start, decl_end)) = Self::classify_decl(decl);
        let name = name?;

        // The parser records a keyword-only span for several decl kinds (e.g.
        // `def`/`theorem`), so the name may sit just past `decl_end`. Locate the
        // name span and widen the symbol range to cover it, preserving the LSP
        // invariant `selection_range` contained-in `range`.
        let name_span = Self::name_span_offsets(text, start, &name);
        let end = name_span.map_or(decl_end, |(_, name_end)| decl_end.max(name_end));

        let range = Range {
            start: doc.offset_to_position(start),
            end: doc.offset_to_position(end),
        };
        let selection_range = match name_span {
            Some((name_start, name_end)) => Range {
                start: doc.offset_to_position(name_start),
                end: doc.offset_to_position(name_end),
            },
            None => range,
        };
        let symbol_kind = Self::symbol_kind_for_command(&kind);

        // Recurse into scopes / fields to build the children subtree.
        let children = match decl {
            SurfaceDecl::Namespace { decls, .. } | SurfaceDecl::Section { decls, .. } => {
                let nested: Vec<DocumentSymbol> = decls
                    .iter()
                    .filter_map(|inner| Self::surface_decl_to_symbol(doc, text, inner))
                    .collect();
                (!nested.is_empty()).then_some(nested)
            }
            SurfaceDecl::Structure { fields, .. } | SurfaceDecl::Class { fields, .. } => {
                let nested: Vec<DocumentSymbol> = fields
                    .iter()
                    .map(|field| Self::structure_field_to_symbol(doc, text, field))
                    .collect();
                (!nested.is_empty()).then_some(nested)
            }
            _ => None,
        };

        #[allow(deprecated)]
        Some(DocumentSymbol {
            name,
            detail: None,
            kind: symbol_kind,
            tags: None,
            deprecated: None,
            range,
            selection_range,
            children,
        })
    }

    /// Build a child [`DocumentSymbol`] for a single structure/class field.
    fn structure_field_to_symbol(
        doc: &crate::document::Document,
        text: &str,
        field: &clean_parser::SurfaceField,
    ) -> DocumentSymbol {
        let start = field.span.start;
        let name_span = Self::name_span_offsets(text, start, &field.name);
        let end = name_span.map_or(field.span.end, |(_, name_end)| field.span.end.max(name_end));
        let range = Range {
            start: doc.offset_to_position(start),
            end: doc.offset_to_position(end),
        };
        let selection_range = match name_span {
            Some((name_start, name_end)) => Range {
                start: doc.offset_to_position(name_start),
                end: doc.offset_to_position(name_end),
            },
            None => range,
        };

        #[allow(deprecated)]
        DocumentSymbol {
            name: field.name.clone(),
            detail: None,
            kind: SymbolKind::FIELD,
            tags: None,
            deprecated: None,
            range,
            selection_range,
            children: None,
        }
    }

    /// Locate the byte span of a declaration's `name` identifier.
    ///
    /// The parser records a declaration's span as the *keyword* span for many
    /// decl kinds (e.g. `def`/`theorem`), so the name typically appears just
    /// past it. We therefore search forward from the declaration `start` and
    /// take the first identifier-boundary occurrence of `name`, which is the
    /// declaration's own name. Returns `None` if it cannot be located.
    fn name_span_offsets(text: &str, start: usize, name: &str) -> Option<(usize, usize)> {
        let search_text = text.get(start..)?;
        Self::identifier_name_span_in_text(text, search_text, start, name)
    }

    /// Get workspace symbols matching a query
    pub(crate) fn get_workspace_symbols(&self, query: &str) -> Vec<SymbolInformation> {
        let mut symbols = Vec::new();
        let query_lower = query.to_lowercase();

        for entry in &self.definitions {
            let name = entry.key();
            let def_info = entry.value();

            // Match if query is empty or name contains query (case-insensitive)
            if query.is_empty() || name.to_lowercase().contains(&query_lower) {
                // Look up the command kind from the parsed document
                let kind = self.get_symbol_kind_for_definition(name);

                // Get the location
                if let Some(doc) = self.documents.get(&def_info.uri) {
                    let start = doc.offset_to_position(def_info.start);
                    let end = doc.offset_to_position(def_info.end);

                    #[allow(deprecated)]
                    symbols.push(SymbolInformation {
                        name: name.clone(),
                        kind,
                        tags: None,
                        deprecated: None,
                        location: Location {
                            uri: def_info.uri.clone(),
                            range: Range { start, end },
                        },
                        container_name: None,
                    });
                }
            }
        }

        // Sort by name for consistent results
        symbols.sort_by(|a, b| a.name.cmp(&b.name));
        symbols
    }

    /// Build a `CallHierarchyItem` from a definition record. Returns `None` if
    /// the owning document is no longer open.
    pub(crate) fn make_call_hierarchy_item(
        &self,
        name: &str,
        info: &DefinitionInfo,
    ) -> Option<CallHierarchyItem> {
        let doc = self.documents.get(&info.uri)?;
        let kind = self.get_symbol_kind_for_definition(name);
        let range = Range {
            start: doc.offset_to_position(info.start),
            end: doc.offset_to_position(info.end),
        };
        let selection_range = Range {
            start: doc.offset_to_position(info.name_start),
            end: doc.offset_to_position(info.name_end),
        };
        Some(CallHierarchyItem {
            name: name.to_string(),
            kind,
            tags: None,
            detail: None,
            uri: info.uri.clone(),
            range,
            selection_range,
            data: None,
        })
    }

    /// Find the top-level definition whose *body extent* encloses `offset` in
    /// `uri`. Because the parser's tracked `cmd.end` only covers the leading
    /// keyword, the effective body extent is taken as `[def.start, next.start)`
    /// for the definition with the largest `start` that does not exceed
    /// `offset` (with `text.len()` for the last definition in the file).
    pub(crate) fn enclosing_definition(
        &self,
        uri: &Url,
        offset: usize,
    ) -> Option<(String, DefinitionInfo)> {
        let mut sorted: Vec<(String, DefinitionInfo)> = self
            .definitions
            .iter()
            .filter(|entry| &entry.value().uri == uri)
            .map(|entry| (entry.key().clone(), entry.value().clone()))
            .collect();
        sorted.sort_by_key(|(_, info)| info.start);

        let doc = self.documents.get(uri)?;
        let text_len = doc.text().len();
        drop(doc);

        let mut current: Option<(String, DefinitionInfo)> = None;
        for (name, info) in sorted {
            if info.start > offset {
                let body_end = info.start;
                if let Some((cur_name, cur_info)) = current.as_ref() {
                    if offset < body_end {
                        return Some((cur_name.clone(), cur_info.clone()));
                    }
                }
                return None;
            }
            current = Some((name, info));
        }
        if let Some((cur_name, cur_info)) = current.as_ref() {
            if offset < text_len {
                return Some((cur_name.clone(), cur_info.clone()));
            }
        }
        None
    }

    /// Identify the call-hierarchy callees within a definition's *body extent*:
    /// every identifier token between this definition's start and the next
    /// definition's start (or end-of-file) whose name is itself a known
    /// definition (and not the caller's own name). Returns one entry per
    /// callee name with the ranges of its use-sites in the caller.
    pub(crate) fn outgoing_call_ranges(
        &self,
        caller_name: &str,
        info: &DefinitionInfo,
    ) -> HashMap<String, Vec<Range>> {
        let mut targets: HashMap<String, Vec<Range>> = HashMap::new();
        let Some(doc) = self.documents.get(&info.uri) else {
            return targets;
        };
        let text = doc.text();
        let body_end = self
            .next_definition_start(&info.uri, info.start)
            .unwrap_or(text.len());
        if info.start > text.len() || body_end > text.len() {
            return targets;
        }

        for token in Lexer::tokenize(&text) {
            if token.span.start < info.start || token.span.end > body_end {
                continue;
            }
            // Skip the caller's own declaration site.
            if token.span.start == info.name_start && token.span.end == info.name_end {
                continue;
            }
            let TokenKind::Ident(ref name) = token.kind else {
                continue;
            };
            if name == caller_name {
                continue;
            }
            if !self.definitions.contains_key(name) {
                continue;
            }
            let range = Range {
                start: doc.offset_to_position(token.span.start),
                end: doc.offset_to_position(token.span.end),
            };
            targets.entry(name.clone()).or_default().push(range);
        }
        targets
    }

    /// Smallest definition start in `uri` strictly greater than `after`.
    pub(crate) fn next_definition_start(&self, uri: &Url, after: usize) -> Option<usize> {
        self.definitions
            .iter()
            .filter(|entry| &entry.value().uri == uri && entry.value().start > after)
            .map(|entry| entry.value().start)
            .min()
    }

    /// Get the SymbolKind for a definition by name
    pub(crate) fn get_symbol_kind_for_definition(&self, name: &str) -> SymbolKind {
        if let Some(def_info) = self.definitions.get(name) {
            if let Some(doc) = self.documents.get(&def_info.uri) {
                if let Some(parsed) = &doc.parsed {
                    for cmd in &parsed.commands {
                        if cmd.name.as_ref() == Some(&name.to_string()) {
                            return match cmd.kind {
                                CommandKind::Definition
                                | CommandKind::Theorem
                                | CommandKind::Lemma => SymbolKind::FUNCTION,
                                CommandKind::Inductive | CommandKind::Structure => {
                                    SymbolKind::CLASS
                                }
                                CommandKind::Class => SymbolKind::INTERFACE,
                                CommandKind::Instance => SymbolKind::OBJECT,
                                CommandKind::Axiom => SymbolKind::CONSTANT,
                                CommandKind::Variable => SymbolKind::VARIABLE,
                                CommandKind::Namespace => SymbolKind::NAMESPACE,
                                _ => SymbolKind::NULL,
                            };
                        }
                    }
                }
            }
        }
        SymbolKind::NULL
    }
}
