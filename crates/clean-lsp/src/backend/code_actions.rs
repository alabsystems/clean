// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Code actions and quick fixes for the Lean 5 LSP backend.
//!
//! Provides code action generation including:
//! - Quick fixes for `sorry` occurrences (replace with various tactics)
//! - Diagnostic-based quick fixes (import suggestions, type annotations)
//! - Refactoring actions (extract definition)

use super::helpers::{
    extract_identifier_from_error, ranges_overlap, suggest_imports_for_identifier,
};
use super::CleanBackend;
use crate::document::Document;
use std::collections::HashMap;
use tower_lsp::lsp_types::*;

impl CleanBackend {
    /// Get code actions for a range
    pub(crate) fn get_code_actions(
        &self,
        uri: &Url,
        range: Range,
        diagnostics: &[Diagnostic],
    ) -> Vec<CodeActionOrCommand> {
        let mut actions = Vec::new();

        // Get the document
        let Some(doc) = self.documents.get(uri) else {
            return actions;
        };

        let text = doc.text();

        // 1. Quick fix: Replace `sorry` with placeholder
        self.add_sorry_quick_fixes(&text, uri, range, &mut actions);

        // 2. Quick fix based on diagnostics
        for diagnostic in diagnostics {
            self.add_diagnostic_quick_fixes(&text, uri, diagnostic, &mut actions);
        }

        // 3. Refactoring: Extract definition (if selecting an expression)
        self.add_extract_definition_action(&text, &doc, uri, range, &mut actions);

        actions
    }

    /// Add quick fixes for `sorry` occurrences
    pub(crate) fn add_sorry_quick_fixes(
        &self,
        text: &str,
        uri: &Url,
        range: Range,
        actions: &mut Vec<CodeActionOrCommand>,
    ) {
        // Find all `sorry` occurrences in the text
        let mut pos = 0;
        while let Some(found) = text[pos..].find("sorry") {
            let start_offset = pos + found;
            let end_offset = start_offset + 5; // "sorry".len()

            // Get the position in the document
            let start = self.offset_to_position_in_text(text, start_offset);
            let end = self.offset_to_position_in_text(text, end_offset);

            // Check if this sorry is in or overlaps with the requested range
            let sorry_range = Range { start, end };
            if ranges_overlap(sorry_range, range) {
                // Create a code action to replace sorry with a tactic placeholder
                let edit = TextEdit {
                    range: sorry_range,
                    new_text: "by decide".to_string(),
                };

                let mut changes = HashMap::new();
                changes.insert(uri.clone(), vec![edit.clone()]);

                actions.push(CodeActionOrCommand::CodeAction(CodeAction {
                    title: "Replace 'sorry' with 'by decide'".to_string(),
                    kind: Some(CodeActionKind::QUICKFIX),
                    diagnostics: None,
                    edit: Some(WorkspaceEdit {
                        changes: Some(changes),
                        document_changes: None,
                        change_annotations: None,
                    }),
                    command: None,
                    is_preferred: Some(false),
                    disabled: None,
                    data: None,
                }));

                // Also offer to replace with other tactics
                let other_replacements = [
                    ("trivial", "Replace 'sorry' with 'trivial'"),
                    ("rfl", "Replace 'sorry' with 'rfl'"),
                    ("simp", "Replace 'sorry' with 'simp'"),
                    ("by assumption", "Replace 'sorry' with 'by assumption'"),
                ];

                for (replacement, title) in other_replacements {
                    let edit = TextEdit {
                        range: sorry_range,
                        new_text: replacement.to_string(),
                    };

                    let mut changes = HashMap::new();
                    changes.insert(uri.clone(), vec![edit]);

                    actions.push(CodeActionOrCommand::CodeAction(CodeAction {
                        title: title.to_string(),
                        kind: Some(CodeActionKind::QUICKFIX),
                        diagnostics: None,
                        edit: Some(WorkspaceEdit {
                            changes: Some(changes),
                            document_changes: None,
                            change_annotations: None,
                        }),
                        command: None,
                        is_preferred: Some(false),
                        disabled: None,
                        data: None,
                    }));
                }
            }

            pos = end_offset;
        }
    }

    /// Add quick fixes based on diagnostic messages
    pub(crate) fn add_diagnostic_quick_fixes(
        &self,
        text: &str,
        uri: &Url,
        diagnostic: &Diagnostic,
        actions: &mut Vec<CodeActionOrCommand>,
    ) {
        let message = &diagnostic.message;

        // Check for unknown identifier errors (potential import suggestion)
        if message.contains("unknown identifier") || message.contains("not found") {
            // Extract the identifier name from the error message
            if let Some(ident) = extract_identifier_from_error(message) {
                // Suggest common imports based on the identifier
                let suggested_imports = suggest_imports_for_identifier(&ident);

                for import in suggested_imports {
                    if Self::has_import(text, import) {
                        continue;
                    }

                    let import_text = format!("import {import}\n");

                    // Insert import at the start of the file
                    let edit = TextEdit {
                        range: Range {
                            start: Position {
                                line: 0,
                                character: 0,
                            },
                            end: Position {
                                line: 0,
                                character: 0,
                            },
                        },
                        new_text: import_text,
                    };

                    let mut changes = HashMap::new();
                    changes.insert(uri.clone(), vec![edit]);

                    actions.push(CodeActionOrCommand::CodeAction(CodeAction {
                        title: format!("Add import '{import}'"),
                        kind: Some(CodeActionKind::QUICKFIX),
                        diagnostics: Some(vec![diagnostic.clone()]),
                        edit: Some(WorkspaceEdit {
                            changes: Some(changes),
                            document_changes: None,
                            change_annotations: None,
                        }),
                        command: None,
                        is_preferred: Some(false),
                        disabled: None,
                        data: None,
                    }));
                }
            }
        }

        // Check for type mismatch errors
        if message.contains("type mismatch") {
            // Suggest adding a type annotation
            actions.push(CodeActionOrCommand::CodeAction(CodeAction {
                title: "Add explicit type annotation".to_string(),
                kind: Some(CodeActionKind::QUICKFIX),
                diagnostics: Some(vec![diagnostic.clone()]),
                edit: None, // Would need more context to provide actual edit
                command: None,
                is_preferred: Some(false),
                disabled: Some(CodeActionDisabled {
                    reason: "Requires manual type specification".to_string(),
                }),
                data: None,
            }));
        }
    }

    fn has_import(text: &str, import: &str) -> bool {
        let import_line = format!("import {import}");
        text.lines().any(|line| line.trim() == import_line)
    }

    /// Add refactoring action to extract a definition
    pub(crate) fn add_extract_definition_action(
        &self,
        text: &str,
        doc: &Document,
        uri: &Url,
        range: Range,
        actions: &mut Vec<CodeActionOrCommand>,
    ) {
        // Only offer if a non-empty range is selected
        if range.start == range.end {
            return;
        }

        let start_offset = doc.position_to_offset(range.start);
        let end_offset = doc.position_to_offset(range.end);

        if start_offset >= end_offset || end_offset > text.len() {
            return;
        }

        let selected_text = &text[start_offset..end_offset];

        // Only offer for reasonable selections (not too long, no newlines at edges)
        if selected_text.is_empty() || selected_text.len() > 200 {
            return;
        }

        let trimmed = selected_text.trim();
        if trimmed.is_empty() {
            return;
        }

        // Create the extract definition action
        let new_def = format!("def extracted := {trimmed}\n\n");

        // Find the start of the current declaration to insert before it
        let insert_pos = self.find_declaration_start(text, start_offset);
        let insert_position = self.offset_to_position_in_text(text, insert_pos);

        let mut edits = vec![
            // Insert new definition
            TextEdit {
                range: Range {
                    start: insert_position,
                    end: insert_position,
                },
                new_text: new_def,
            },
            // Replace selected text with reference
            TextEdit {
                range,
                new_text: "extracted".to_string(),
            },
        ];

        // Sort edits by position (from end to start) to avoid offset issues
        edits.sort_by(|a, b| {
            b.range
                .start
                .line
                .cmp(&a.range.start.line)
                .then_with(|| b.range.start.character.cmp(&a.range.start.character))
        });

        let mut changes = HashMap::new();
        changes.insert(uri.clone(), edits);

        actions.push(CodeActionOrCommand::CodeAction(CodeAction {
            title: "Extract to definition".to_string(),
            kind: Some(CodeActionKind::REFACTOR_EXTRACT),
            diagnostics: None,
            edit: Some(WorkspaceEdit {
                changes: Some(changes),
                document_changes: None,
                change_annotations: None,
            }),
            command: None,
            is_preferred: Some(false),
            disabled: None,
            data: None,
        }));
    }

    /// Find the start of the declaration containing the given offset
    pub(crate) fn find_declaration_start(&self, text: &str, offset: usize) -> usize {
        // Look backwards for declaration keywords
        let keywords = [
            "def ",
            "theorem ",
            "lemma ",
            "example ",
            "inductive ",
            "structure ",
            "class ",
            "instance ",
            "axiom ",
        ];

        let search_start = offset.saturating_sub(500);
        let search_text = &text[search_start..offset];

        let mut best_pos = search_start;
        for keyword in keywords {
            if let Some(pos) = search_text.rfind(keyword) {
                let abs_pos = search_start + pos;
                if abs_pos > best_pos {
                    best_pos = abs_pos;
                }
            }
        }

        // If we found a keyword, return the start of that line
        if best_pos > search_start {
            // Go back to the start of the line
            let line_start = text[..best_pos].rfind('\n').map_or(0, |p| p + 1);
            return line_start;
        }

        // Default to start of file
        0
    }

    /// Convert byte offset to LSP position (helper for text without Document)
    pub(crate) fn offset_to_position_in_text(&self, text: &str, offset: usize) -> Position {
        let offset = offset.min(text.len());
        let mut line = 0u32;
        let mut line_start = 0;

        for (i, ch) in text.char_indices() {
            if i >= offset {
                break;
            }
            if ch == '\n' {
                line += 1;
                line_start = i + 1;
            }
        }

        let col_bytes = offset.saturating_sub(line_start);
        let line_text = &text[line_start..];

        // Convert byte offset to UTF-16 code units
        let mut utf16_col = 0u32;
        let mut byte_count = 0;

        for ch in line_text.chars() {
            if byte_count >= col_bytes {
                break;
            }
            byte_count += ch.len_utf8();
            utf16_col += ch.len_utf16() as u32;
        }

        Position {
            line,
            character: utf16_col,
        }
    }
}
