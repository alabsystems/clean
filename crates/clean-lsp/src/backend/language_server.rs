// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `tower_lsp::LanguageServer` trait implementation for `CleanBackend`.

use super::navigation::CompletionItemData;
use super::semantic_tokens::{
    classify_identifier_with_modifiers, find_definition_name_span, token_kind_to_semantic_type,
};
use super::{
    byte_offset_to_position, compute_folding_ranges, CleanBackend, SEMANTIC_TOKEN_MODIFIERS,
    SEMANTIC_TOKEN_TYPES,
};
use crate::document::Document;
use clean_parser::lexer::{Lexer, TokenKind};
use std::collections::{HashMap, HashSet};
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::request;
use tower_lsp::lsp_types::*;
use tower_lsp::LanguageServer;

#[tower_lsp::async_trait]
impl LanguageServer for CleanBackend {
    async fn initialize(&self, _: InitializeParams) -> Result<InitializeResult> {
        Ok(InitializeResult {
            capabilities: ServerCapabilities {
                text_document_sync: Some(TextDocumentSyncCapability::Kind(
                    TextDocumentSyncKind::INCREMENTAL,
                )),
                hover_provider: Some(HoverProviderCapability::Simple(true)),
                document_symbol_provider: Some(OneOf::Left(true)),
                completion_provider: Some(CompletionOptions {
                    trigger_characters: Some(vec![".".to_string(), "#".to_string()]),
                    // We support `completionItem/resolve`: each definition item
                    // carries a `data` payload identifying its source
                    // declaration, and the resolve request lazily attaches the
                    // full detail signature / documentation. See
                    // `CleanBackend::resolve_completion_item`.
                    resolve_provider: Some(true),
                    ..Default::default()
                }),
                signature_help_provider: Some(SignatureHelpOptions {
                    trigger_characters: Some(vec![" ".to_string(), "(".to_string()]),
                    retrigger_characters: Some(vec![",".to_string()]),
                    work_done_progress_options: WorkDoneProgressOptions::default(),
                }),
                definition_provider: Some(OneOf::Left(true)),
                // Go-to-declaration. For Lean declarations the declaration site
                // and the definition site coincide (a `def`/`theorem`/`axiom`
                // is its own declaration), so `goto_declaration` reuses the
                // definition resolution path.
                declaration_provider: Some(DeclarationCapability::Simple(true)),
                type_definition_provider: Some(TypeDefinitionProviderCapability::Simple(true)),
                document_highlight_provider: Some(OneOf::Left(true)),
                references_provider: Some(OneOf::Left(true)),
                workspace_symbol_provider: Some(OneOf::Left(true)),
                code_action_provider: Some(CodeActionProviderCapability::Options(
                    CodeActionOptions {
                        code_action_kinds: Some(vec![
                            CodeActionKind::QUICKFIX,
                            CodeActionKind::REFACTOR_EXTRACT,
                        ]),
                        work_done_progress_options: WorkDoneProgressOptions::default(),
                        resolve_provider: None,
                    },
                )),
                rename_provider: Some(OneOf::Right(RenameOptions {
                    prepare_provider: Some(true),
                    work_done_progress_options: WorkDoneProgressOptions::default(),
                })),
                semantic_tokens_provider: Some(
                    SemanticTokensServerCapabilities::SemanticTokensOptions(
                        SemanticTokensOptions {
                            legend: SemanticTokensLegend {
                                token_types: SEMANTIC_TOKEN_TYPES.to_vec(),
                                token_modifiers: SEMANTIC_TOKEN_MODIFIERS.to_vec(),
                            },
                            full: Some(SemanticTokensFullOptions::Bool(true)),
                            range: Some(true),
                            work_done_progress_options: WorkDoneProgressOptions::default(),
                        },
                    ),
                ),
                inlay_hint_provider: Some(OneOf::Right(InlayHintServerCapabilities::Options(
                    InlayHintOptions {
                        work_done_progress_options: WorkDoneProgressOptions::default(),
                        // We support `inlayHint/resolve`: a hint carries a
                        // `data` payload identifying its source declaration, and
                        // the resolve request lazily attaches a full-signature
                        // tooltip. See `CleanBackend::resolve_inlay_hint`.
                        resolve_provider: Some(true),
                    },
                ))),
                document_formatting_provider: Some(OneOf::Left(true)),
                document_on_type_formatting_provider: Some(DocumentOnTypeFormattingOptions {
                    first_trigger_character: "\n".to_string(),
                    more_trigger_character: None,
                }),
                document_range_formatting_provider: Some(OneOf::Left(true)),
                folding_range_provider: Some(FoldingRangeProviderCapability::Simple(true)),
                selection_range_provider: Some(SelectionRangeProviderCapability::Simple(true)),
                linked_editing_range_provider: Some(LinkedEditingRangeServerCapabilities::Simple(
                    true,
                )),
                call_hierarchy_provider: Some(CallHierarchyServerCapability::Simple(true)),
                document_link_provider: Some(DocumentLinkOptions {
                    // Links are produced cheaply (range + opaque data + a
                    // best-effort target) and their target is verified and
                    // their tooltip enriched lazily by `documentLink/resolve`.
                    // See `CleanBackend::resolve_document_link`.
                    resolve_provider: Some(true),
                    work_done_progress_options: WorkDoneProgressOptions::default(),
                }),
                code_lens_provider: Some(CodeLensOptions {
                    // Lenses are produced unresolved (range + opaque data) and
                    // their command/title is filled in lazily by
                    // `codeLens/resolve`. See `CleanBackend::resolve_code_lens`.
                    resolve_provider: Some(true),
                }),
                // `lsp-types` 0.94 has no typed `type_hierarchy_provider` slot
                // on `ServerCapabilities`, so the prepare/super/subtypes support
                // is advertised through the `experimental` map. Clients that key
                // off `experimental.typeHierarchyProvider` (and `tower-lsp`,
                // which always routes the registered methods) then issue the
                // `textDocument/prepareTypeHierarchy`, `typeHierarchy/supertypes`
                // and `typeHierarchy/subtypes` requests handled below.
                experimental: Some(serde_json::json!({
                    "typeHierarchyProvider": true
                })),
                ..Default::default()
            },
            server_info: Some(ServerInfo {
                name: "clean-lsp".to_string(),
                version: Some(env!("CARGO_PKG_VERSION").to_string()),
            }),
        })
    }

    async fn initialized(&self, _: InitializedParams) {
        self.client
            .log_message(MessageType::INFO, "clean LSP server initialized")
            .await;

        // Dynamically register interest in configuration changes so clients
        // route `workspace/didChangeConfiguration` to us. lsp-types has no
        // static `ServerCapabilities` slot for this notification, so dynamic
        // registration is the supported advertisement path. A client that
        // does not support dynamic registration simply sends the notification
        // unconditionally, which we also handle.
        let registration = Registration {
            id: "clean-did-change-configuration".to_string(),
            method: "workspace/didChangeConfiguration".to_string(),
            register_options: None,
        };
        if let Err(err) = self.client.register_capability(vec![registration]).await {
            self.client
                .log_message(
                    MessageType::WARNING,
                    format!("clean LSP: configuration-change registration failed: {err}"),
                )
                .await;
        }
    }

    async fn shutdown(&self) -> Result<()> {
        Ok(())
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        let uri = params.text_document.uri;
        let version = params.text_document.version;
        let text = params.text_document.text;
        let language_id = params.text_document.language_id;

        self.documents.insert(
            uri.clone(),
            Document::new(uri.clone(), version, text, language_id),
        );

        self.check_document(&uri).await;
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        let uri = params.text_document.uri;
        let version = params.text_document.version;

        if let Some(mut doc) = self.documents.get_mut(&uri) {
            doc.version = version;

            for change in params.content_changes {
                doc.apply_change(change.range, &change.text);
            }
        }

        self.check_document(&uri).await;
    }

    async fn did_close(&self, params: DidCloseTextDocumentParams) {
        let uri = params.text_document.uri;

        // Remove definitions from this document
        let to_remove: Vec<String> = self
            .definitions
            .iter()
            .filter(|entry| entry.value().uri == uri)
            .map(|entry| entry.key().clone())
            .collect();
        for name in to_remove {
            self.definitions.remove(&name);
        }

        self.documents.remove(&uri);
        self.client.publish_diagnostics(uri, vec![], None).await;
    }

    async fn did_save(&self, params: DidSaveTextDocumentParams) {
        self.check_document(&params.text_document.uri).await;
    }

    async fn did_change_configuration(&self, params: DidChangeConfigurationParams) {
        // Merge recognized `clean.*` settings into live state. Unknown keys and
        // malformed shapes are ignored by `apply_json`, so subsequent feature
        // requests (e.g. inlay hints) immediately observe the new values
        // without a server restart.
        self.config.write().await.apply_json(&params.settings);
    }

    async fn hover(&self, params: HoverParams) -> Result<Option<Hover>> {
        let uri = &params.text_document_position_params.text_document.uri;
        let position = params.text_document_position_params.position;
        Ok(self.get_hover_at(uri, position))
    }

    async fn document_symbol(
        &self,
        params: DocumentSymbolParams,
    ) -> Result<Option<DocumentSymbolResponse>> {
        let uri = &params.text_document.uri;
        Ok(self
            .get_document_symbols(uri)
            .map(DocumentSymbolResponse::Nested))
    }

    async fn completion(&self, params: CompletionParams) -> Result<Option<CompletionResponse>> {
        let uri = &params.text_document_position.text_document.uri;
        let position = params.text_document_position.position;

        // Get the prefix being typed (partial identifier)
        let (prefix, replacement_range) = self.get_completion_prefix_span(uri, position);

        let mut items = Vec::new();

        // Add completions from definitions
        for entry in &self.definitions {
            let name = entry.key();
            if prefix.is_empty() || name.starts_with(&prefix) {
                // Determine completion kind based on where the definition came from
                let kind = self.get_definition_kind(name);
                let type_str = self.get_completion_detail(name);
                let category = self.get_definition_category_label(name);

                // Carry the source declaration so `completionItem/resolve` can
                // lazily re-attach the full detail signature / documentation
                // for the item the client ultimately selects.
                let resolve_data = CompletionItemData {
                    uri: entry.value().uri.to_string(),
                    name: name.clone(),
                }
                .to_value();

                let text_edit = replacement_range.map(|range| {
                    CompletionTextEdit::Edit(TextEdit {
                        range,
                        new_text: name.clone(),
                    })
                });

                let label_details = match (&type_str, category) {
                    (Some(ty), Some(cat)) => Some(CompletionItemLabelDetails {
                        detail: Some(format!(" : {ty}")),
                        description: Some(cat.to_string()),
                    }),
                    (Some(ty), None) => Some(CompletionItemLabelDetails {
                        detail: Some(format!(" : {ty}")),
                        description: None,
                    }),
                    (None, Some(cat)) => Some(CompletionItemLabelDetails {
                        detail: None,
                        description: Some(cat.to_string()),
                    }),
                    (None, None) => None,
                };

                let documentation = type_str.as_deref().map(|ty| {
                    Documentation::MarkupContent(MarkupContent {
                        kind: MarkupKind::Markdown,
                        value: format!("```lean\n{name} : {ty}\n```"),
                    })
                });

                items.push(CompletionItem {
                    label: name.clone(),
                    kind: Some(kind),
                    detail: type_str,
                    documentation,
                    deprecated: None,
                    preselect: None,
                    // Sort definitions before keywords for prefix-empty results.
                    sort_text: Some(format!("a_{name}")),
                    filter_text: None,
                    insert_text: Some(name.clone()),
                    insert_text_format: Some(InsertTextFormat::PLAIN_TEXT),
                    insert_text_mode: None,
                    text_edit,
                    additional_text_edits: None,
                    command: None,
                    commit_characters: None,
                    data: resolve_data,
                    tags: None,
                    label_details,
                });
            }
        }

        // Add keyword completions
        for keyword in &[
            "def",
            "theorem",
            "lemma",
            "example",
            "inductive",
            "structure",
            "class",
            "instance",
            "axiom",
            "variable",
            "import",
            "open",
            "namespace",
            "section",
            "end",
            "where",
            "if",
            "then",
            "else",
            "match",
            "with",
            "fun",
            "let",
            "in",
            "do",
            "return",
            "have",
            "show",
            "by",
            "rfl",
            "simp",
            "exact",
            "apply",
            "intro",
            "cases",
            "induction",
            "constructor",
            "rw",
            "rewrite",
            "calc",
            "sorry",
        ] {
            if prefix.is_empty() || keyword.starts_with(&prefix) {
                items.push(CompletionItem {
                    label: (*keyword).to_string(),
                    kind: Some(CompletionItemKind::KEYWORD),
                    insert_text: Some((*keyword).to_string()),
                    insert_text_format: Some(InsertTextFormat::PLAIN_TEXT),
                    // Sort keywords after definitions so user-defined names come first.
                    sort_text: Some(format!("z_{keyword}")),
                    ..Default::default()
                });
            }
        }

        if items.is_empty() {
            Ok(None)
        } else {
            Ok(Some(CompletionResponse::Array(items)))
        }
    }

    async fn completion_resolve(&self, item: CompletionItem) -> Result<CompletionItem> {
        Ok(self.resolve_completion_item(item))
    }

    async fn signature_help(&self, params: SignatureHelpParams) -> Result<Option<SignatureHelp>> {
        let uri = &params.text_document_position_params.text_document.uri;
        let position = params.text_document_position_params.position;
        Ok(self.get_signature_help_at(uri, position))
    }

    async fn goto_definition(
        &self,
        params: GotoDefinitionParams,
    ) -> Result<Option<GotoDefinitionResponse>> {
        let uri = &params.text_document_position_params.text_document.uri;
        let position = params.text_document_position_params.position;

        // Find the identifier at the cursor position
        let Some(name) = self.get_identifier_at(uri, position) else {
            return Ok(None);
        };

        // Look up the definition
        if let Some((def_uri, range)) = self.find_definition(&name) {
            Ok(Some(GotoDefinitionResponse::Scalar(Location {
                uri: def_uri,
                range,
            })))
        } else {
            Ok(None)
        }
    }

    async fn goto_declaration(
        &self,
        params: request::GotoDeclarationParams,
    ) -> Result<Option<request::GotoDeclarationResponse>> {
        let uri = &params.text_document_position_params.text_document.uri;
        let position = params.text_document_position_params.position;

        // For Lean declarations the declaration and definition sites coincide,
        // so go-to-declaration reuses the same identifier resolution and
        // definition index lookup as `goto_definition`.
        let Some(name) = self.get_identifier_at(uri, position) else {
            return Ok(None);
        };

        if let Some((def_uri, range)) = self.find_definition(&name) {
            Ok(Some(GotoDefinitionResponse::Scalar(Location {
                uri: def_uri,
                range,
            })))
        } else {
            Ok(None)
        }
    }

    async fn goto_type_definition(
        &self,
        params: request::GotoTypeDefinitionParams,
    ) -> Result<Option<request::GotoTypeDefinitionResponse>> {
        let uri = &params.text_document_position_params.text_document.uri;
        let position = params.text_document_position_params.position;

        if let Some((def_uri, range)) = self.find_type_definition_at(uri, position) {
            Ok(Some(GotoDefinitionResponse::Scalar(Location {
                uri: def_uri,
                range,
            })))
        } else {
            Ok(None)
        }
    }

    async fn document_highlight(
        &self,
        params: DocumentHighlightParams,
    ) -> Result<Option<Vec<DocumentHighlight>>> {
        let uri = &params.text_document_position_params.text_document.uri;
        let position = params.text_document_position_params.position;
        Ok(self.document_highlights_at(uri, position))
    }

    async fn references(&self, params: ReferenceParams) -> Result<Option<Vec<Location>>> {
        let uri = &params.text_document_position.text_document.uri;
        let position = params.text_document_position.position;
        let include_declaration = params.context.include_declaration;

        // Find the identifier at the cursor position
        let Some(name) = self.get_identifier_at(uri, position) else {
            return Ok(None);
        };

        let references = self.find_references(&name, include_declaration);

        if references.is_empty() {
            Ok(None)
        } else {
            Ok(Some(references))
        }
    }

    async fn code_action(&self, params: CodeActionParams) -> Result<Option<CodeActionResponse>> {
        let uri = &params.text_document.uri;
        let range = params.range;
        let diagnostics = &params.context.diagnostics;

        let mut actions = self.get_code_actions(uri, range, diagnostics);
        actions.retain(|action| code_action_matches_only(action, params.context.only.as_deref()));

        if actions.is_empty() {
            Ok(None)
        } else {
            Ok(Some(actions))
        }
    }

    async fn symbol(
        &self,
        params: WorkspaceSymbolParams,
    ) -> Result<Option<Vec<SymbolInformation>>> {
        let symbols = self.get_workspace_symbols(&params.query);

        if symbols.is_empty() {
            Ok(None)
        } else {
            Ok(Some(symbols))
        }
    }

    async fn prepare_rename(
        &self,
        params: TextDocumentPositionParams,
    ) -> Result<Option<PrepareRenameResponse>> {
        let uri = &params.text_document.uri;
        let position = params.position;

        match self.prepare_rename_at(uri, position) {
            Some((name, range)) => {
                // Return the range and placeholder text
                Ok(Some(PrepareRenameResponse::RangeWithPlaceholder {
                    range,
                    placeholder: name,
                }))
            }
            None => Ok(None),
        }
    }

    async fn rename(&self, params: RenameParams) -> Result<Option<WorkspaceEdit>> {
        let uri = &params.text_document_position.text_document.uri;
        let position = params.text_document_position.position;
        let new_name = &params.new_name;

        // Find the identifier at the cursor position
        let Some(old_name) = self.get_identifier_at(uri, position) else {
            return Ok(None);
        };

        // Keep rename validation aligned with the parser's identifier rules.
        if !Self::is_valid_identifier(new_name) {
            return Ok(None);
        }

        let edits = self.create_rename_edits(&old_name, new_name);

        if edits.changes.as_ref().is_none_or(HashMap::is_empty) {
            Ok(None)
        } else {
            Ok(Some(edits))
        }
    }

    async fn semantic_tokens_full(
        &self,
        params: SemanticTokensParams,
    ) -> Result<Option<SemanticTokensResult>> {
        let uri = &params.text_document.uri;

        let Some(absolute) = self.collect_absolute_semantic_tokens(uri) else {
            return Ok(None);
        };

        Ok(Some(SemanticTokensResult::Tokens(SemanticTokens {
            result_id: None,
            data: delta_encode_semantic_tokens(absolute.iter().copied()),
        })))
    }

    async fn semantic_tokens_range(
        &self,
        params: SemanticTokensRangeParams,
    ) -> Result<Option<SemanticTokensRangeResult>> {
        let uri = &params.text_document.uri;
        let range = params.range;

        let Some(absolute) = self.collect_absolute_semantic_tokens(uri) else {
            return Ok(None);
        };

        // Keep only tokens whose start position falls inside the requested
        // range, then delta-encode over the filtered subset so the first
        // in-range token carries absolute coordinates. Re-encoding (rather
        // than slicing the full delta stream) is required: deltas are relative
        // to the previous *emitted* token, so dropping a prefix would corrupt
        // every following token's position.
        let filtered = absolute
            .iter()
            .copied()
            .filter(|token| position_in_range(token.position(), range));

        Ok(Some(SemanticTokensRangeResult::Tokens(SemanticTokens {
            result_id: None,
            data: delta_encode_semantic_tokens(filtered),
        })))
    }

    async fn inlay_hint(&self, params: InlayHintParams) -> Result<Option<Vec<InlayHint>>> {
        let uri = &params.text_document.uri;
        let enabled = self.config.read().await.inlay_hints_enabled;
        Ok(Some(self.get_inlay_hints(uri, params.range, enabled)))
    }

    async fn inlay_hint_resolve(&self, hint: InlayHint) -> Result<InlayHint> {
        Ok(self.resolve_inlay_hint(hint))
    }

    async fn formatting(&self, params: DocumentFormattingParams) -> Result<Option<Vec<TextEdit>>> {
        let uri = &params.text_document.uri;
        let _options = &params.options;

        let Some(doc) = self.documents.get(uri) else {
            return Ok(None);
        };

        let text = doc.text();

        // Document-level formatting: normalize whitespace per line, cap blank
        // runs at 2, and guarantee exactly one trailing newline.
        let mut formatted = normalize_whitespace_lines(&text);
        formatted.push('\n');

        if formatted == text {
            return Ok(Some(vec![]));
        }

        let line_count = text.lines().count();
        let last_line_len = text.lines().last().map_or(0, str::len);

        Ok(Some(vec![TextEdit {
            range: Range {
                start: Position::new(0, 0),
                end: Position::new(line_count as u32, last_line_len as u32),
            },
            new_text: formatted,
        }]))
    }

    async fn range_formatting(
        &self,
        params: DocumentRangeFormattingParams,
    ) -> Result<Option<Vec<TextEdit>>> {
        let uri = &params.text_document.uri;
        let range = params.range;

        let Some(doc) = self.documents.get(uri) else {
            return Ok(None);
        };
        let text = doc.text();

        let start_off = doc.position_to_offset(range.start);
        let end_off = doc.position_to_offset(range.end);
        if start_off >= end_off || end_off > text.len() {
            return Ok(Some(vec![]));
        }

        // Slice on UTF-8 boundaries; the LSP position math should already land
        // on char boundaries, but be defensive against malformed input.
        if !text.is_char_boundary(start_off) || !text.is_char_boundary(end_off) {
            return Ok(Some(vec![]));
        }
        let slice = &text[start_off..end_off];

        let formatted = normalize_whitespace_lines(slice);
        if formatted == slice {
            return Ok(Some(vec![]));
        }

        Ok(Some(vec![TextEdit {
            range,
            new_text: formatted,
        }]))
    }

    async fn on_type_formatting(
        &self,
        params: DocumentOnTypeFormattingParams,
    ) -> Result<Option<Vec<TextEdit>>> {
        // Trigger is `\n` — the user just hit Return. Trim any trailing
        // whitespace from the line that was just terminated (the line
        // *above* the cursor). Conservative scope: only that one line,
        // no auto-indent (Lean's whitespace-sensitive blocks make a
        // generic indenter more harmful than helpful, and a no-op
        // handler is worse than absence for editors that expect a
        // response).
        let uri = &params.text_document_position.text_document.uri;
        let position = params.text_document_position.position;
        if position.line == 0 {
            return Ok(Some(vec![]));
        }

        let Some(doc) = self.documents.get(uri) else {
            return Ok(None);
        };
        let text = doc.text();

        let target_line = position.line - 1;
        let line_text: String = text
            .lines()
            .nth(target_line as usize)
            .unwrap_or("")
            .to_string();
        let trimmed = line_text.trim_end();
        if trimmed.len() == line_text.len() {
            return Ok(Some(vec![]));
        }

        let trim_start_col = u32::try_from(trimmed.chars().count()).unwrap_or(u32::MAX);
        let original_end_col = u32::try_from(line_text.chars().count()).unwrap_or(u32::MAX);

        Ok(Some(vec![TextEdit {
            range: Range {
                start: Position::new(target_line, trim_start_col),
                end: Position::new(target_line, original_end_col),
            },
            new_text: String::new(),
        }]))
    }

    async fn linked_editing_range(
        &self,
        params: LinkedEditingRangeParams,
    ) -> Result<Option<LinkedEditingRanges>> {
        let uri = &params.text_document_position_params.text_document.uri;
        let position = params.text_document_position_params.position;

        let Some(name) = self.get_identifier_at(uri, position) else {
            return Ok(None);
        };

        // All in-document occurrences of the identifier, including its
        // declaration, so the editor can sync edits across them.
        let ranges: Vec<Range> = self
            .find_references(&name, true)
            .into_iter()
            .filter(|loc| &loc.uri == uri)
            .map(|loc| loc.range)
            .collect();

        if ranges.is_empty() {
            Ok(None)
        } else {
            Ok(Some(LinkedEditingRanges {
                ranges,
                word_pattern: None,
            }))
        }
    }

    async fn prepare_call_hierarchy(
        &self,
        params: CallHierarchyPrepareParams,
    ) -> Result<Option<Vec<CallHierarchyItem>>> {
        let uri = &params.text_document_position_params.text_document.uri;
        let position = params.text_document_position_params.position;

        let Some(name) = self.get_identifier_at(uri, position) else {
            return Ok(None);
        };
        let Some(info) = self.definitions.get(&name) else {
            return Ok(None);
        };
        let Some(item) = self.make_call_hierarchy_item(&name, info.value()) else {
            return Ok(None);
        };
        Ok(Some(vec![item]))
    }

    async fn incoming_calls(
        &self,
        params: CallHierarchyIncomingCallsParams,
    ) -> Result<Option<Vec<CallHierarchyIncomingCall>>> {
        let item = params.item;

        // Group caller-side reference ranges by the enclosing definition they
        // appear in. References outside any known definition are dropped — the
        // call hierarchy panel only renders attributable callers.
        let mut by_caller: HashMap<String, (CallHierarchyItem, Vec<Range>)> = HashMap::new();
        for location in self.find_references(&item.name, false) {
            let caller_doc = self.documents.get(&location.uri);
            let Some(caller_doc) = caller_doc else {
                continue;
            };
            let ref_offset = caller_doc.position_to_offset(location.range.start);
            drop(caller_doc);

            let Some((caller_name, caller_info)) =
                self.enclosing_definition(&location.uri, ref_offset)
            else {
                continue;
            };
            if caller_name == item.name {
                // Self-reference inside the definition itself isn't an incoming call.
                continue;
            }
            let entry = by_caller.entry(caller_name.clone()).or_insert_with(|| {
                let caller_item = self
                    .make_call_hierarchy_item(&caller_name, &caller_info)
                    .unwrap_or_else(|| CallHierarchyItem {
                        name: caller_name.clone(),
                        kind: SymbolKind::FUNCTION,
                        tags: None,
                        detail: None,
                        uri: location.uri.clone(),
                        range: location.range,
                        selection_range: location.range,
                        data: None,
                    });
                (caller_item, Vec::new())
            });
            entry.1.push(location.range);
        }

        let calls: Vec<CallHierarchyIncomingCall> = by_caller
            .into_values()
            .map(|(from, from_ranges)| CallHierarchyIncomingCall { from, from_ranges })
            .collect();

        Ok(Some(calls))
    }

    async fn outgoing_calls(
        &self,
        params: CallHierarchyOutgoingCallsParams,
    ) -> Result<Option<Vec<CallHierarchyOutgoingCall>>> {
        let item = params.item;
        let Some(info) = self.definitions.get(&item.name) else {
            return Ok(Some(vec![]));
        };

        let targets = self.outgoing_call_ranges(&item.name, info.value());

        let mut calls: Vec<CallHierarchyOutgoingCall> = Vec::with_capacity(targets.len());
        for (callee_name, from_ranges) in targets {
            let Some(callee_info) = self.definitions.get(&callee_name) else {
                continue;
            };
            let Some(to) = self.make_call_hierarchy_item(&callee_name, callee_info.value()) else {
                continue;
            };
            calls.push(CallHierarchyOutgoingCall { to, from_ranges });
        }

        Ok(Some(calls))
    }

    async fn prepare_type_hierarchy(
        &self,
        params: TypeHierarchyPrepareParams,
    ) -> Result<Option<Vec<TypeHierarchyItem>>> {
        let uri = &params.text_document_position_params.text_document.uri;
        let position = params.text_document_position_params.position;

        // Only structures, classes, inductives and instances participate in the
        // type hierarchy. Resolve the identifier under the cursor to its
        // definition and reject anything that is not a type-relationship node.
        let Some(name) = self.get_identifier_at(uri, position) else {
            return Ok(None);
        };
        let Some(info) = self.definitions.get(&name) else {
            return Ok(None);
        };
        if !self.is_type_hierarchy_node(&name) {
            return Ok(None);
        }
        let Some(item) = self.make_type_hierarchy_item(&name, info.value()) else {
            return Ok(None);
        };
        Ok(Some(vec![item]))
    }

    async fn supertypes(
        &self,
        params: TypeHierarchySupertypesParams,
    ) -> Result<Option<Vec<TypeHierarchyItem>>> {
        let item = params.item;
        let supertypes = self
            .type_supertypes(&item.name)
            .into_iter()
            .filter_map(|name| {
                let info = self.definitions.get(&name)?;
                self.make_type_hierarchy_item(&name, info.value())
            })
            .collect();
        Ok(Some(supertypes))
    }

    async fn subtypes(
        &self,
        params: TypeHierarchySubtypesParams,
    ) -> Result<Option<Vec<TypeHierarchyItem>>> {
        let item = params.item;
        let subtypes = self
            .type_subtypes(&item.name)
            .into_iter()
            .filter_map(|name| {
                let info = self.definitions.get(&name)?;
                self.make_type_hierarchy_item(&name, info.value())
            })
            .collect();
        Ok(Some(subtypes))
    }

    async fn folding_range(&self, params: FoldingRangeParams) -> Result<Option<Vec<FoldingRange>>> {
        let uri = &params.text_document.uri;

        let Some(doc) = self.documents.get(uri) else {
            return Ok(None);
        };

        let text = doc.text();
        let ranges = compute_folding_ranges(&text);

        if ranges.is_empty() {
            Ok(None)
        } else {
            Ok(Some(ranges))
        }
    }

    async fn selection_range(
        &self,
        params: SelectionRangeParams,
    ) -> Result<Option<Vec<SelectionRange>>> {
        let uri = &params.text_document.uri;

        // The protocol returns one range hierarchy per requested position, in
        // the same order. An unknown document yields `None`; an open document
        // always yields a hierarchy (at minimum the whole-document range) for
        // each position so the client can keep expanding the selection.
        if !self.documents.contains_key(uri) {
            return Ok(None);
        }

        let ranges: Vec<SelectionRange> = params
            .positions
            .into_iter()
            .filter_map(|position| self.selection_range_at(uri, position))
            .collect();

        Ok(Some(ranges))
    }

    async fn document_link(&self, params: DocumentLinkParams) -> Result<Option<Vec<DocumentLink>>> {
        let links = self.get_document_links(&params.text_document.uri);
        if links.is_empty() {
            Ok(None)
        } else {
            Ok(Some(links))
        }
    }

    async fn document_link_resolve(&self, link: DocumentLink) -> Result<DocumentLink> {
        Ok(self.resolve_document_link(link))
    }

    async fn code_lens(&self, params: CodeLensParams) -> Result<Option<Vec<CodeLens>>> {
        let lenses = self.get_code_lenses(&params.text_document.uri);
        if lenses.is_empty() {
            Ok(None)
        } else {
            Ok(Some(lenses))
        }
    }

    async fn code_lens_resolve(&self, lens: CodeLens) -> Result<CodeLens> {
        Ok(self.resolve_code_lens(lens))
    }
}

/// A semantic token with absolute (un-delta-encoded) coordinates. The
/// `semantic_tokens_full` and `semantic_tokens_range` handlers both build this
/// intermediate form and then delta-encode it (the range variant first filters
/// to the requested viewport).
#[derive(Debug, Clone, Copy)]
struct AbsoluteSemanticToken {
    line: u32,
    character: u32,
    length: u32,
    token_type: u32,
    modifiers: u32,
}

impl AbsoluteSemanticToken {
    fn position(self) -> Position {
        Position::new(self.line, self.character)
    }
}

impl CleanBackend {
    /// Compute every semantic token for the document at `uri` in absolute
    /// coordinates, in document order. Returns `None` when the document is not
    /// open. Shared by the full and range semantic-token handlers so both apply
    /// identical classification.
    fn collect_absolute_semantic_tokens(&self, uri: &Url) -> Option<Vec<AbsoluteSemanticToken>> {
        let (text, definition_kinds, definition_spans) = {
            let doc = self.documents.get(uri)?;
            let text = doc.text();
            // Build a map of defined names to their kinds for better classification
            let mut kinds = HashMap::new();
            // Build a set of definition name spans (start, end) to mark DECLARATION modifier
            let mut def_spans = HashSet::new();
            if let Some(parsed) = &doc.parsed {
                for cmd in &parsed.commands {
                    if let Some(name) = &cmd.name {
                        kinds.insert(name.clone(), cmd.kind.clone());
                        // Find the name position within the command span
                        // The name typically follows the keyword (def, theorem, etc.)
                        if let Some(name_pos) =
                            find_definition_name_span(&text, cmd.start, cmd.end, name)
                        {
                            def_spans.insert(name_pos);
                        }
                    }
                }
            }
            for entry in &self.definitions {
                if &entry.value().uri == uri {
                    def_spans.insert((entry.value().name_start, entry.value().name_end));
                }
            }
            (text, kinds, def_spans)
        };

        // Tokenize the document
        let tokens = Lexer::tokenize(&text);

        let mut absolute: Vec<AbsoluteSemanticToken> = Vec::new();
        for token in &tokens {
            // Get token type and modifiers, with enhanced classification for identifiers
            let (token_type, modifiers) = match &token.kind {
                TokenKind::Ident(name) => {
                    // Check if this is a definition site
                    let is_def_site =
                        definition_spans.contains(&(token.span.start, token.span.end));
                    // Look up identifier in known definitions
                    classify_identifier_with_modifiers(name, &definition_kinds, is_def_site)
                }
                other => (token_kind_to_semantic_type(other), 0),
            };

            let Some(token_type) = token_type else {
                continue;
            };

            // Calculate position from byte offset
            let start_pos = byte_offset_to_position(&text, token.span.start);
            let end_pos = byte_offset_to_position(&text, token.span.end);

            // Calculate token length (in characters, not bytes)
            let length = if start_pos.line == end_pos.line {
                end_pos.character - start_pos.character
            } else {
                // Multi-line token - use the first line's length
                // This is rare for most tokens
                (text.len() - token.span.start).min(100) as u32
            };

            absolute.push(AbsoluteSemanticToken {
                line: start_pos.line,
                character: start_pos.character,
                length,
                token_type,
                modifiers,
            });
        }

        Some(absolute)
    }
}

/// Delta-encode absolute semantic tokens into the wire format. Each
/// `SemanticToken` is encoded relative to the previously emitted token:
/// `[deltaLine, deltaStart, length, tokenType, tokenModifiers]`. The first
/// token's deltas are therefore its absolute coordinates, which makes the
/// output valid for any contiguous-or-filtered subset of the document.
fn delta_encode_semantic_tokens(
    tokens: impl IntoIterator<Item = AbsoluteSemanticToken>,
) -> Vec<SemanticToken> {
    let mut data: Vec<SemanticToken> = Vec::new();
    let mut prev_line = 0u32;
    let mut prev_start = 0u32;

    for token in tokens {
        let delta_line = token.line - prev_line;
        let delta_start = if delta_line == 0 {
            token.character - prev_start
        } else {
            token.character
        };

        data.push(SemanticToken {
            delta_line,
            delta_start,
            length: token.length,
            token_type: token.token_type,
            token_modifiers_bitset: token.modifiers,
        });

        prev_line = token.line;
        prev_start = token.character;
    }

    data
}

/// Whether `position` lies within `range`, treating the range as half-open on
/// the end (`[start, end)`). A token that begins exactly at `range.end` is
/// considered outside, matching the LSP convention that a range's end is
/// exclusive; a token beginning exactly at `range.start` is included.
fn position_in_range(position: Position, range: Range) -> bool {
    let at_or_after_start =
        (position.line, position.character) >= (range.start.line, range.start.character);
    let before_end = (position.line, position.character) < (range.end.line, range.end.character);
    at_or_after_start && before_end
}

fn code_action_matches_only(action: &CodeActionOrCommand, only: Option<&[CodeActionKind]>) -> bool {
    let Some(only) = only else {
        return true;
    };

    let CodeActionOrCommand::CodeAction(action) = action else {
        return false;
    };
    let Some(kind) = &action.kind else {
        return false;
    };

    only.iter()
        .any(|requested| code_action_kind_includes(requested, kind))
}

fn code_action_kind_includes(requested: &CodeActionKind, actual: &CodeActionKind) -> bool {
    actual == requested
        || actual
            .as_str()
            .strip_prefix(requested.as_str())
            .is_some_and(|suffix| suffix.starts_with('.'))
}

/// Normalize whitespace across the supplied text: trim trailing whitespace
/// from every line and collapse runs of blank lines to at most two. Returns
/// the normalized lines joined by `\n`, with no leading or trailing newline.
///
/// Shared by [`LanguageServer::formatting`] (document-wide) and
/// [`LanguageServer::range_formatting`] (selection-scoped). The trailing-
/// newline guarantee is applied by `formatting` only — appending one to a
/// partial range would inject spurious blank lines into the document.
fn normalize_whitespace_lines(text: &str) -> String {
    let mut formatted: Vec<String> = Vec::new();
    let mut blank_count = 0usize;

    for line in text.lines() {
        let trimmed = line.trim_end();
        if trimmed.is_empty() {
            blank_count += 1;
            if blank_count <= 2 {
                formatted.push(String::new());
            }
        } else {
            blank_count = 0;
            formatted.push(trimmed.to_string());
        }
    }

    formatted.join("\n")
}
