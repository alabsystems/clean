// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the clean LSP backend.

#[path = "tests/typed_name_tests.rs"]
mod typed_name_tests;

#[path = "tests/formatting_withdrawn_tests.rs"]
mod formatting_withdrawn_tests;

use super::analysis::parse_lean_text;
use super::helpers::{
    compute_folding_ranges, extract_identifier_from_error, ranges_overlap,
    suggest_imports_for_identifier,
};
use super::semantic_tokens::{
    classify_identifier_with_modifiers, command_kind_to_semantic_type, find_definition_name_span,
    is_builtin_type, is_likely_type_name, token_kind_to_semantic_type,
};
use super::warnings::{
    collect_deprecated_names, detect_deprecated_usage, detect_duplicate_binders,
    detect_sorry_warnings, detect_unused_variables,
};
use super::*;
use crate::document::{
    CommandKind, Document, ElaboratedDecl, ElaboratedDocument, IncrementalState, ParseError,
    ParsedDocument, WarningCode,
};
use clean_parser::lexer::TokenKind;
use tower_lsp::lsp_types::*;
use tower_lsp::{LanguageServer, LspService};

#[test]
fn test_parse_simple_def() {
    let text = "def x := 1";
    let parsed = parse_lean_text(text);

    assert!(parsed.errors.is_empty());
    assert_eq!(parsed.commands.len(), 1);
    assert_eq!(parsed.commands[0].kind, CommandKind::Definition);
    assert_eq!(parsed.commands[0].name, Some("x".to_string()));
}

#[test]
fn test_parse_multiple_defs() {
    let text = "def x := 1\ndef y := 2\ntheorem t : True := trivial";
    let parsed = parse_lean_text(text);

    assert!(parsed.errors.is_empty());
    assert_eq!(parsed.commands.len(), 3);
    assert_eq!(parsed.commands[0].kind, CommandKind::Definition);
    assert_eq!(parsed.commands[1].kind, CommandKind::Definition);
    assert_eq!(parsed.commands[2].kind, CommandKind::Theorem);
}

#[test]
fn test_parse_with_error() {
    let text = "def x :=";
    let parsed = parse_lean_text(text);
    assert!(!parsed.errors.is_empty());
}

#[test]
fn test_parse_inductive() {
    let text = "inductive Nat : Type\n| zero : Nat\n| succ : Nat -> Nat";
    let parsed = parse_lean_text(text);

    assert!(parsed.errors.is_empty());
    assert_eq!(parsed.commands.len(), 1);
    assert_eq!(parsed.commands[0].kind, CommandKind::Inductive);
    assert_eq!(parsed.commands[0].name, Some("Nat".to_string()));
}

#[test]
fn test_parse_structure() {
    let text = "structure Point where\n  x : Nat\n  y : Nat";
    let parsed = parse_lean_text(text);

    assert!(parsed.errors.is_empty());
    assert_eq!(parsed.commands.len(), 1);
    assert_eq!(parsed.commands[0].kind, CommandKind::Structure);
    assert_eq!(parsed.commands[0].name, Some("Point".to_string()));
}

#[test]
fn test_document_creation() {
    let uri = Url::parse("file:///test.lean").unwrap();
    let doc = Document::new(uri, 1, "def x := 1\n".to_string(), "lean".to_string());

    assert_eq!(doc.version, 1);
    assert_eq!(doc.text(), "def x := 1\n");
}

#[test]
fn test_is_identifier_continue() {
    // ASCII alphanumeric
    assert!(CleanBackend::is_identifier_continue('a'));
    assert!(CleanBackend::is_identifier_continue('Z'));
    assert!(CleanBackend::is_identifier_continue('5'));

    // Lean suffix markers
    assert!(CleanBackend::is_identifier_continue('_'));
    assert!(CleanBackend::is_identifier_continue('\''));
    assert!(CleanBackend::is_identifier_continue('?'));
    assert!(CleanBackend::is_identifier_continue('!'));

    // Unicode identifiers
    assert!(CleanBackend::is_identifier_continue('α'));
    assert!(CleanBackend::is_identifier_continue('ℕ'));

    // Non-identifier chars
    assert!(!CleanBackend::is_identifier_continue(' '));
    assert!(!CleanBackend::is_identifier_continue(':'));
    assert!(!CleanBackend::is_identifier_continue('.'));
    assert!(!CleanBackend::is_identifier_continue('\n'));
}

#[test]
fn test_definition_info_clone() {
    let uri = Url::parse("file:///test.lean").unwrap();
    let info = DefinitionInfo {
        uri: uri.clone(),
        start: 0,
        end: 10,
        name_start: 4,
        name_end: 8,
    };
    let cloned = info.clone();
    assert_eq!(cloned.uri, uri);
    assert_eq!(cloned.start, 0);
    assert_eq!(cloned.end, 10);
    assert_eq!(cloned.name_start, 4);
    assert_eq!(cloned.name_end, 8);
}

#[test]
fn test_ranges_overlap() {
    let r1 = Range {
        start: Position {
            line: 0,
            character: 0,
        },
        end: Position {
            line: 0,
            character: 10,
        },
    };
    let r2 = Range {
        start: Position {
            line: 0,
            character: 5,
        },
        end: Position {
            line: 0,
            character: 15,
        },
    };
    let r3 = Range {
        start: Position {
            line: 0,
            character: 20,
        },
        end: Position {
            line: 0,
            character: 30,
        },
    };

    // Overlapping ranges
    assert!(ranges_overlap(r1, r2));
    assert!(ranges_overlap(r2, r1));

    // Non-overlapping ranges
    assert!(!ranges_overlap(r1, r3));
    assert!(!ranges_overlap(r3, r1));
}

#[test]
fn test_extract_identifier_from_error() {
    // Backtick quoted
    let msg1 = "unknown identifier `foo`";
    assert_eq!(extract_identifier_from_error(msg1), Some("foo".to_string()));

    // Pattern-based
    let msg2 = "unknown identifier bar in context";
    assert_eq!(extract_identifier_from_error(msg2), Some("bar".to_string()));

    // Not found pattern
    let msg3 = "not found: HashMap";
    assert_eq!(
        extract_identifier_from_error(msg3),
        Some("HashMap".to_string())
    );

    // No identifier
    let msg4 = "some other error";
    assert_eq!(extract_identifier_from_error(msg4), None);
}

#[test]
fn test_suggest_imports_for_identifier() {
    // Basic types
    assert!(!suggest_imports_for_identifier("Nat").is_empty());
    assert!(!suggest_imports_for_identifier("List").is_empty());

    // Std types
    assert!(!suggest_imports_for_identifier("HashMap").is_empty());

    // Mathlib types
    assert!(!suggest_imports_for_identifier("Real").is_empty());
    assert!(!suggest_imports_for_identifier("Group").is_empty());

    // Unknown identifier
    assert!(suggest_imports_for_identifier("UnknownThing123").is_empty());
}

#[test]
fn test_get_symbol_kind_for_definition() {
    // This test validates the symbol kind mapping logic
    // The actual backend methods require async context, so we test the mapping directly
    let mappings = [
        (CommandKind::Definition, SymbolKind::FUNCTION),
        (CommandKind::Theorem, SymbolKind::FUNCTION),
        (CommandKind::Lemma, SymbolKind::FUNCTION),
        (CommandKind::Inductive, SymbolKind::CLASS),
        (CommandKind::Structure, SymbolKind::CLASS),
        (CommandKind::Class, SymbolKind::INTERFACE),
        (CommandKind::Instance, SymbolKind::OBJECT),
        (CommandKind::Axiom, SymbolKind::CONSTANT),
        (CommandKind::Variable, SymbolKind::VARIABLE),
        (CommandKind::Namespace, SymbolKind::NAMESPACE),
    ];

    for (cmd_kind, expected_symbol_kind) in mappings {
        let symbol_kind = match cmd_kind {
            CommandKind::Definition | CommandKind::Theorem | CommandKind::Lemma => {
                SymbolKind::FUNCTION
            }
            CommandKind::Inductive | CommandKind::Structure => SymbolKind::CLASS,
            CommandKind::Class => SymbolKind::INTERFACE,
            CommandKind::Instance => SymbolKind::OBJECT,
            CommandKind::Axiom => SymbolKind::CONSTANT,
            CommandKind::Variable => SymbolKind::VARIABLE,
            CommandKind::Namespace => SymbolKind::NAMESPACE,
            _ => SymbolKind::NULL,
        };
        assert_eq!(
            symbol_kind, expected_symbol_kind,
            "Mismatch for {cmd_kind:?}"
        );
    }
}

#[test]
fn test_workspace_symbol_query_matching() {
    // Test case-insensitive matching logic
    let test_cases = [
        ("", "anything", true),     // Empty query matches everything
        ("nat", "Nat", true),       // Case-insensitive match
        ("NAT", "natural", true),   // Case-insensitive substring
        ("foo", "bar", false),      // No match
        ("add", "Nat.add", true),   // Substring match
        ("Point", "MyPoint", true), // Substring match
        ("xyz", "Point", false),    // No match
    ];

    for (query, name, should_match) in test_cases {
        let query_lower = query.to_lowercase();
        let matches = query.is_empty() || name.to_lowercase().contains(&query_lower);
        assert_eq!(
            matches, should_match,
            "Query '{query}' vs name '{name}': expected {should_match}, got {matches}"
        );
    }
}

#[test]
fn test_unused_variable_detection() {
    // Test that unused variables are detected
    let text = "def f (x : Nat) (y : Nat) := x";
    let decls = clean_parser::parse_file(text).unwrap();
    assert_eq!(decls.len(), 1);

    let warnings = detect_unused_variables(&decls[0]);
    assert_eq!(warnings.len(), 1);
    assert!(warnings[0].message.contains("unused variable `y`"));
    assert_eq!(warnings[0].code, WarningCode::UnusedVariable);
}

#[test]
fn test_no_warning_for_used_variables() {
    // Test that used variables don't generate warnings
    let text = "def add (x : Nat) (y : Nat) := Nat.add x y";
    let decls = clean_parser::parse_file(text).unwrap();
    assert_eq!(decls.len(), 1);

    let warnings = detect_unused_variables(&decls[0]);
    assert!(
        warnings.is_empty(),
        "Expected no warnings, got: {warnings:?}"
    );
}

#[test]
fn test_underscore_variables_not_warned() {
    // Test that underscore-prefixed variables don't generate warnings
    let text = "def f (_unused : Nat) := 42";
    let decls = clean_parser::parse_file(text).unwrap();
    assert_eq!(decls.len(), 1);

    let warnings = detect_unused_variables(&decls[0]);
    assert!(
        warnings.is_empty(),
        "Underscore-prefixed variables should not generate warnings"
    );
}

#[test]
fn test_theorem_unused_variable() {
    // Test unused variable detection in theorems
    let text = "theorem t (h : True) (unused : False) : True := h";
    let decls = clean_parser::parse_file(text).unwrap();
    assert_eq!(decls.len(), 1);

    let warnings = detect_unused_variables(&decls[0]);
    assert_eq!(warnings.len(), 1);
    assert!(warnings[0].message.contains("unused variable `unused`"));
}

#[test]
fn test_duplicate_binder_detection_points_at_first_binder() {
    // The second `x` reuses a name already bound; the warning's related
    // location must point at the first binder (a genuine, model-tracked span).
    let text = "def f (x : Nat) (x : Nat) := x";
    let decls = clean_parser::parse_file(text).unwrap();
    assert_eq!(decls.len(), 1);

    let warnings = detect_duplicate_binders(&decls[0]);
    assert_eq!(warnings.len(), 1, "exactly one duplicate binder");
    assert!(warnings[0].message.contains("duplicate binder `x`"));

    // The warning span is the second binder; the related span is the first.
    let first_x = text.find("(x").expect("first binder") + 1;
    let second_x = text.rfind("(x").expect("second binder") + 1;
    assert_eq!(warnings[0].start, second_x, "warning at second binder");

    assert_eq!(warnings[0].related.len(), 1, "one related location");
    assert_eq!(
        warnings[0].related[0].start, first_x,
        "related points at first binder"
    );
    assert!(warnings[0].related[0]
        .message
        .contains("first binding of `x`"));
}

#[test]
fn test_no_duplicate_binder_for_distinct_names() {
    let text = "def f (x : Nat) (y : Nat) := x";
    let decls = clean_parser::parse_file(text).unwrap();
    let warnings = detect_duplicate_binders(&decls[0]);
    assert!(
        warnings.is_empty(),
        "distinct binder names produce no duplicate warnings"
    );
}

#[test]
fn test_duplicate_binder_ignores_anonymous() {
    // Repeated `_` binders are intentional and must not be flagged.
    let text = "def f (_ : Nat) (_ : Nat) := 0";
    let decls = clean_parser::parse_file(text).unwrap();
    let warnings = detect_duplicate_binders(&decls[0]);
    assert!(
        warnings.is_empty(),
        "anonymous `_` binders are repeatable and not flagged"
    );
}

#[test]
fn test_sorry_detection() {
    // Test that sorry usage is detected
    let text = "theorem t : True := sorry";
    let decls = clean_parser::parse_file(text).unwrap();
    assert_eq!(decls.len(), 1);

    let warnings = detect_sorry_warnings(&decls[0]);
    assert_eq!(warnings.len(), 1);
    assert!(warnings[0].message.contains("sorry"));
    assert_eq!(warnings[0].code, WarningCode::IncompleteProof);
}

#[test]
fn test_admit_detection() {
    // Test that admit usage is detected
    let text = "def f : Nat := admit";
    let decls = clean_parser::parse_file(text).unwrap();
    assert_eq!(decls.len(), 1);

    let warnings = detect_sorry_warnings(&decls[0]);
    assert_eq!(warnings.len(), 1);
    assert!(warnings[0].message.contains("admit"));
    assert_eq!(warnings[0].code, WarningCode::IncompleteProof);
}

#[test]
fn test_no_sorry_warning_for_complete_proof() {
    // Test that complete proofs don't generate sorry warnings
    let text = "theorem t : True := True.intro";
    let decls = clean_parser::parse_file(text).unwrap();
    assert_eq!(decls.len(), 1);

    let warnings = detect_sorry_warnings(&decls[0]);
    assert!(
        warnings.is_empty(),
        "Complete proofs should not generate sorry warnings"
    );
}

#[test]
fn test_deprecated_usage_detection() {
    let text = r"
def old : Nat := 1
attribute [deprecated] old
def use_old : Nat := old
";

    let decls = clean_parser::parse_file(text).unwrap();
    let deprecated = collect_deprecated_names(&decls);
    assert!(deprecated.contains(&clean_kernel::Name::anon().str("old")));

    let warnings: Vec<_> = decls
        .iter()
        .flat_map(|d| detect_deprecated_usage(d, &deprecated))
        .collect();

    let deprecated_warnings: Vec<_> = warnings
        .iter()
        .filter(|w| w.code == WarningCode::DeprecatedFeature)
        .collect();

    assert_eq!(
        deprecated_warnings.len(),
        1,
        "Expected one deprecated usage warning, got: {deprecated_warnings:?}"
    );
    assert!(
        deprecated_warnings[0].message.contains("deprecated"),
        "Warning message should mention deprecation"
    );
}

#[test]
fn test_prepare_rename_valid_identifier() {
    // Test that valid identifiers can be prepared for rename
    let text = "def myFunction := 1";
    let parsed = parse_lean_text(text);
    assert!(parsed.errors.is_empty());
    assert_eq!(parsed.commands.len(), 1);
    assert_eq!(parsed.commands[0].name, Some("myFunction".to_string()));
}

#[test]
fn test_create_rename_edits_helper() {
    // Test the workspace edit structure
    use std::collections::HashMap;

    // Create a mock workspace edit
    let mut changes: HashMap<Url, Vec<TextEdit>> = HashMap::new();
    let uri = Url::parse("file:///test.lean").unwrap();
    changes.insert(
        uri.clone(),
        vec![TextEdit {
            range: Range {
                start: Position {
                    line: 0,
                    character: 4,
                },
                end: Position {
                    line: 0,
                    character: 5,
                },
            },
            new_text: "y".to_string(),
        }],
    );

    let edit = WorkspaceEdit {
        changes: Some(changes),
        document_changes: None,
        change_annotations: None,
    };

    let changes = edit.changes.expect("WorkspaceEdit should have changes");
    assert_eq!(changes.len(), 1);
    assert!(changes.contains_key(&uri));
}

#[test]
fn test_identifier_validation_for_rename() {
    // Test valid/invalid identifier detection for renaming
    let valid_names = [
        "x", "myVar", "my_var", "x1", "Nat", "_x", "x'", "done?", "map!", "α", "ℕ",
    ];
    let invalid_names = ["", "1x", "my-var", "a b", "'x"];

    for name in valid_names {
        assert!(
            CleanBackend::is_valid_identifier(name),
            "Expected '{name}' to be valid"
        );
    }

    for name in invalid_names {
        assert!(
            !CleanBackend::is_valid_identifier(name),
            "Expected '{name}' to be invalid"
        );
    }
}

#[test]
fn test_identifier_span_at_unicode() {
    let text = "def αβ' := αβ'";
    let offset = text.find("β").expect("identifier should contain beta");
    let (start, end) =
        CleanBackend::identifier_span_at(text, offset).expect("unicode identifier should be found");
    assert_eq!(&text[start..end], "αβ'");
}

#[test]
fn test_rename_accepts_apostrophe_and_unicode_identifiers() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///rename.lean").unwrap();
    let text = "def αβ := αβ".to_string();
    let offset = text.find('β').expect("identifier should contain beta");
    let doc = Document::new(uri.clone(), 1, text, "lean".to_string());
    let position = doc.offset_to_position(offset);

    backend.documents.insert(uri.clone(), doc);

    let result = tokio::runtime::Runtime::new()
        .expect("tokio runtime should initialize")
        .block_on(LanguageServer::rename(
            backend,
            RenameParams {
                text_document_position: TextDocumentPositionParams {
                    text_document: TextDocumentIdentifier { uri: uri.clone() },
                    position,
                },
                new_name: "γ'".to_string(),
                work_done_progress_params: WorkDoneProgressParams::default(),
            },
        ))
        .expect("rename request should not fail")
        .expect("rename should accept Lean identifiers with apostrophes");

    let changes = result.changes.expect("rename should produce edits");
    let edits = changes
        .get(&uri)
        .expect("rename should target the source file");
    assert_eq!(edits.len(), 2, "both occurrences of αβ should be renamed");
    assert!(edits.iter().all(|edit| edit.new_text == "γ'"));

    let renamed_text = "def γ' := γ'";
    let renamed_span = CleanBackend::identifier_span_at(renamed_text, offset)
        .expect("apostrophe identifier should remain detectable");
    assert_eq!(&renamed_text[renamed_span.0..renamed_span.1], "γ'");
}

#[tokio::test]
async fn test_rename_edits_open_documents_without_touching_longer_identifier() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let decl_uri = Url::parse("file:///rename-decl.lean").unwrap();
    let use_uri = Url::parse("file:///rename-use.lean").unwrap();
    let decl_text = "axiom rename_decl : Nat\n".to_string();
    let use_text = "#check rename_decl\n#check rename_decl_extra\n".to_string();

    backend.documents.insert(
        decl_uri.clone(),
        Document::new(decl_uri.clone(), 1, decl_text.clone(), "lean".to_string()),
    );
    backend.documents.insert(
        use_uri.clone(),
        Document::new(use_uri.clone(), 1, use_text.clone(), "lean".to_string()),
    );
    backend.parse_document(&decl_uri).await;
    backend.elaborate_document(&decl_uri).await;
    backend.parse_document(&use_uri).await;
    backend.elaborate_document(&use_uri).await;

    let rename_position = {
        let doc = backend
            .documents
            .get(&decl_uri)
            .expect("declaration document should remain open");
        let offset = decl_text
            .find("rename_decl")
            .expect("declaration text should contain the renamed identifier");
        doc.offset_to_position(offset)
    };

    let result = LanguageServer::rename(
        backend,
        RenameParams {
            text_document_position: TextDocumentPositionParams {
                text_document: TextDocumentIdentifier {
                    uri: decl_uri.clone(),
                },
                position: rename_position,
            },
            new_name: "renamed_decl".to_string(),
            work_done_progress_params: WorkDoneProgressParams::default(),
        },
    )
    .await
    .expect("rename request should not fail")
    .expect("open-document rename should produce edits");

    let changes = result.changes.expect("rename should use workspace changes");
    let decl_edits = changes
        .get(&decl_uri)
        .expect("rename should edit the declaration document");
    let use_edits = changes
        .get(&use_uri)
        .expect("rename should edit the open use document");
    assert_eq!(
        decl_edits.len(),
        1,
        "rename should edit the declaration identifier once"
    );
    assert_eq!(
        use_edits.len(),
        1,
        "rename should edit only the standalone use, not rename_decl_extra"
    );
    assert_eq!(decl_edits[0].new_text, "renamed_decl");
    assert_eq!(use_edits[0].new_text, "renamed_decl");
}

#[tokio::test]
async fn test_code_action_offers_sorry_quickfix_for_checked_document_range() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///code-action-sorry.lean").unwrap();
    let text = "theorem trivial_goal : True := by\n  sorry\n".to_string();

    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text.clone(), "lean".to_string()),
    );
    backend.parse_document(&uri).await;
    backend.elaborate_document(&uri).await;

    let sorry_range = {
        let doc = backend
            .documents
            .get(&uri)
            .expect("code-action test document should remain open");
        let start = text
            .find("sorry")
            .expect("test text should contain a sorry placeholder");
        Range {
            start: doc.offset_to_position(start),
            end: doc.offset_to_position(start + "sorry".len()),
        }
    };

    let response = LanguageServer::code_action(
        backend,
        CodeActionParams {
            text_document: TextDocumentIdentifier { uri: uri.clone() },
            range: sorry_range,
            context: CodeActionContext {
                diagnostics: vec![],
                only: Some(vec![CodeActionKind::QUICKFIX]),
                trigger_kind: Some(CodeActionTriggerKind::INVOKED),
            },
            work_done_progress_params: WorkDoneProgressParams::default(),
            partial_result_params: PartialResultParams::default(),
        },
    )
    .await
    .expect("code action request should not fail")
    .expect("sorry range should produce code actions");

    let quickfix = response
        .iter()
        .find_map(|action| match action {
            CodeActionOrCommand::CodeAction(action)
                if action.title == "Replace 'sorry' with 'by decide'" =>
            {
                Some(action)
            }
            _ => None,
        })
        .expect("code actions should include the sorry by-decide quickfix");
    assert_eq!(
        quickfix.kind,
        Some(CodeActionKind::QUICKFIX),
        "sorry replacement should be surfaced as a quickfix"
    );
    let changes = quickfix
        .edit
        .as_ref()
        .and_then(|edit| edit.changes.as_ref())
        .expect("sorry quickfix should carry workspace changes");
    let edits = changes
        .get(&uri)
        .expect("sorry quickfix should edit the requested document");
    assert_eq!(edits.len(), 1, "sorry quickfix should use one text edit");
    assert_eq!(
        edits[0].range, sorry_range,
        "sorry quickfix should replace exactly the requested sorry token"
    );
    assert_eq!(edits[0].new_text, "by decide");
}

#[tokio::test]
async fn test_code_action_import_quickfix_from_unknown_identifier_diagnostic() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///code-action-import.lean").unwrap();
    let text = "def table : HashMap String Nat := sorry\n".to_string();

    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text.clone(), "lean".to_string()),
    );
    backend.parse_document(&uri).await;

    let hash_map_range = {
        let doc = backend
            .documents
            .get(&uri)
            .expect("code-action import test document should remain open");
        let start = text
            .find("HashMap")
            .expect("test text should contain the unknown identifier");
        Range {
            start: doc.offset_to_position(start),
            end: doc.offset_to_position(start + "HashMap".len()),
        }
    };
    let diagnostic = Diagnostic {
        range: hash_map_range,
        severity: Some(DiagnosticSeverity::ERROR),
        code: None,
        code_description: None,
        source: Some("clean".to_string()),
        message: "unknown identifier `HashMap`".to_string(),
        related_information: None,
        tags: None,
        data: None,
    };

    let response = LanguageServer::code_action(
        backend,
        CodeActionParams {
            text_document: TextDocumentIdentifier { uri: uri.clone() },
            range: hash_map_range,
            context: CodeActionContext {
                diagnostics: vec![diagnostic.clone()],
                only: Some(vec![CodeActionKind::QUICKFIX]),
                trigger_kind: Some(CodeActionTriggerKind::INVOKED),
            },
            work_done_progress_params: WorkDoneProgressParams::default(),
            partial_result_params: PartialResultParams::default(),
        },
    )
    .await
    .expect("code action request should not fail")
    .expect("unknown identifier diagnostic should produce code actions");

    let quickfix = response
        .iter()
        .find_map(|action| match action {
            CodeActionOrCommand::CodeAction(action)
                if action.title == "Add import 'Std.Data.HashMap'" =>
            {
                Some(action)
            }
            _ => None,
        })
        .expect("code actions should include the HashMap import quickfix");
    assert_eq!(
        quickfix.kind,
        Some(CodeActionKind::QUICKFIX),
        "diagnostic import suggestion should be surfaced as a quickfix"
    );
    assert_eq!(
        quickfix.diagnostics.as_deref(),
        Some(std::slice::from_ref(&diagnostic)),
        "diagnostic quickfix should carry the triggering diagnostic"
    );
    let changes = quickfix
        .edit
        .as_ref()
        .and_then(|edit| edit.changes.as_ref())
        .expect("import quickfix should carry workspace changes");
    let edits = changes
        .get(&uri)
        .expect("import quickfix should edit the requested document");
    assert_eq!(edits.len(), 1, "import quickfix should use one text edit");
    assert_eq!(
        edits[0].range,
        Range::new(Position::new(0, 0), Position::new(0, 0)),
        "import quickfix should insert at the start of the document"
    );
    assert_eq!(edits[0].new_text, "import Std.Data.HashMap\n");
}

#[tokio::test]
async fn test_code_action_import_quickfix_from_qualified_unknown_identifier_diagnostic() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///code-action-qualified-import.lean").unwrap();
    let text = "def table : Std.HashMap String Nat := sorry\n".to_string();

    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text.clone(), "lean".to_string()),
    );
    backend.parse_document(&uri).await;

    let identifier_range = {
        let doc = backend
            .documents
            .get(&uri)
            .expect("qualified import test document should remain open");
        let start = text
            .find("Std.HashMap")
            .expect("test text should contain the qualified unknown identifier");
        Range {
            start: doc.offset_to_position(start),
            end: doc.offset_to_position(start + "Std.HashMap".len()),
        }
    };
    let diagnostic = Diagnostic {
        range: identifier_range,
        severity: Some(DiagnosticSeverity::ERROR),
        code: None,
        code_description: None,
        source: Some("clean".to_string()),
        message: "unknown identifier `Std.HashMap`".to_string(),
        related_information: None,
        tags: None,
        data: None,
    };

    let response = LanguageServer::code_action(
        backend,
        CodeActionParams {
            text_document: TextDocumentIdentifier { uri: uri.clone() },
            range: identifier_range,
            context: CodeActionContext {
                diagnostics: vec![diagnostic.clone()],
                only: Some(vec![CodeActionKind::QUICKFIX]),
                trigger_kind: Some(CodeActionTriggerKind::INVOKED),
            },
            work_done_progress_params: WorkDoneProgressParams::default(),
            partial_result_params: PartialResultParams::default(),
        },
    )
    .await
    .expect("qualified import code action request should not fail")
    .expect("qualified unknown identifier diagnostic should produce code actions");

    let quickfix = response
        .iter()
        .find_map(|action| match action {
            CodeActionOrCommand::CodeAction(action) if action.title == "Add import 'Std'" => {
                Some(action)
            }
            _ => None,
        })
        .expect("code actions should include the qualified Std import quickfix");
    assert_eq!(
        quickfix.kind,
        Some(CodeActionKind::QUICKFIX),
        "qualified import suggestion should be surfaced as a quickfix"
    );
    assert_eq!(
        quickfix.diagnostics.as_deref(),
        Some(std::slice::from_ref(&diagnostic)),
        "qualified import quickfix should carry the triggering diagnostic"
    );
    assert_eq!(
        quickfix.command, None,
        "qualified import quickfix should be edit-only"
    );
    assert_eq!(
        quickfix.disabled, None,
        "qualified import quickfix should be immediately applicable"
    );
    let changes = quickfix
        .edit
        .as_ref()
        .and_then(|edit| edit.changes.as_ref())
        .expect("qualified import quickfix should carry workspace changes");
    let edits = changes
        .get(&uri)
        .expect("qualified import quickfix should edit the requested document");
    assert_eq!(
        edits,
        &[TextEdit {
            range: Range::new(Position::new(0, 0), Position::new(0, 0)),
            new_text: "import Std\n".to_string(),
        }],
        "qualified import quickfix should insert the module import at the start"
    );
}

#[tokio::test]
async fn test_code_action_import_quickfix_skips_existing_import() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///code-action-duplicate-import.lean").unwrap();
    let text = "import Std.Data.HashMap\n\ndef table : HashMap String Nat := sorry\n".to_string();

    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text.clone(), "lean".to_string()),
    );
    backend.parse_document(&uri).await;

    let hash_map_range = {
        let doc = backend
            .documents
            .get(&uri)
            .expect("duplicate import test document should remain open");
        let start = text
            .find("HashMap String")
            .expect("test text should contain the unknown identifier");
        Range {
            start: doc.offset_to_position(start),
            end: doc.offset_to_position(start + "HashMap".len()),
        }
    };
    let diagnostic = Diagnostic {
        range: hash_map_range,
        severity: Some(DiagnosticSeverity::ERROR),
        code: None,
        code_description: None,
        source: Some("clean".to_string()),
        message: "unknown identifier `HashMap`".to_string(),
        related_information: None,
        tags: None,
        data: None,
    };

    let response = LanguageServer::code_action(
        backend,
        CodeActionParams {
            text_document: TextDocumentIdentifier { uri },
            range: hash_map_range,
            context: CodeActionContext {
                diagnostics: vec![diagnostic],
                only: Some(vec![CodeActionKind::QUICKFIX]),
                trigger_kind: Some(CodeActionTriggerKind::INVOKED),
            },
            work_done_progress_params: WorkDoneProgressParams::default(),
            partial_result_params: PartialResultParams::default(),
        },
    )
    .await
    .expect("duplicate import code action request should not fail")
    .expect("unknown identifier diagnostic should still produce alternate code actions");

    assert!(
        response.iter().all(|action| {
            !matches!(
                action,
                CodeActionOrCommand::CodeAction(action)
                    if action.title == "Add import 'Std.Data.HashMap'"
            )
        }),
        "code actions should not offer an import already present in the document"
    );
    assert!(
        response.iter().any(|action| {
            matches!(
                action,
                CodeActionOrCommand::CodeAction(action)
                    if action.title == "Add import 'Std.Data.HashSet'"
            )
        }),
        "duplicate filtering should preserve other suggested import quickfixes"
    );
}

#[tokio::test]
async fn test_code_action_only_quickfix_excludes_extract_refactor_for_identifier_range() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///code-action-only-quickfix.lean").unwrap();
    let text = "def table : HashMap String Nat := sorry\n".to_string();

    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text.clone(), "lean".to_string()),
    );
    backend.parse_document(&uri).await;

    let hash_map_range = {
        let doc = backend
            .documents
            .get(&uri)
            .expect("code-action only test document should remain open");
        let start = text
            .find("HashMap")
            .expect("test text should contain the unknown identifier");
        Range {
            start: doc.offset_to_position(start),
            end: doc.offset_to_position(start + "HashMap".len()),
        }
    };
    let diagnostic = Diagnostic {
        range: hash_map_range,
        severity: Some(DiagnosticSeverity::ERROR),
        code: None,
        code_description: None,
        source: Some("clean".to_string()),
        message: "unknown identifier `HashMap`".to_string(),
        related_information: None,
        tags: None,
        data: None,
    };

    let response = LanguageServer::code_action(
        backend,
        CodeActionParams {
            text_document: TextDocumentIdentifier { uri },
            range: hash_map_range,
            context: CodeActionContext {
                diagnostics: vec![diagnostic],
                only: Some(vec![CodeActionKind::QUICKFIX]),
                trigger_kind: Some(CodeActionTriggerKind::INVOKED),
            },
            work_done_progress_params: WorkDoneProgressParams::default(),
            partial_result_params: PartialResultParams::default(),
        },
    )
    .await
    .expect("quickfix-only code action request should not fail")
    .expect("unknown identifier diagnostic should produce quickfix actions");

    assert!(
        response.iter().any(|action| {
            matches!(
                action,
                CodeActionOrCommand::CodeAction(action)
                    if action.title == "Add import 'Std.Data.HashMap'"
            )
        }),
        "quickfix-only request should keep diagnostic import quickfixes"
    );
    assert!(
        response.iter().all(|action| {
            !matches!(
                action,
                CodeActionOrCommand::CodeAction(action)
                    if action.title == "Extract to definition"
                        || action.kind == Some(CodeActionKind::REFACTOR_EXTRACT)
            )
        }),
        "quickfix-only request should not leak extract-definition refactors"
    );
}

#[tokio::test]
async fn test_code_action_extract_definition_has_edit_only_refactor_shape() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///code-action-extract.lean").unwrap();
    let text = "def double : Nat := 21 + 21\n".to_string();

    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text.clone(), "lean".to_string()),
    );
    backend.parse_document(&uri).await;

    let selection_range = {
        let doc = backend
            .documents
            .get(&uri)
            .expect("extract-definition test document should remain open");
        let start = text
            .find("21 + 21")
            .expect("test text should contain the selected expression");
        Range {
            start: doc.offset_to_position(start),
            end: doc.offset_to_position(start + "21 + 21".len()),
        }
    };

    let response = LanguageServer::code_action(
        backend,
        CodeActionParams {
            text_document: TextDocumentIdentifier { uri: uri.clone() },
            range: selection_range,
            context: CodeActionContext {
                diagnostics: vec![],
                only: Some(vec![CodeActionKind::REFACTOR_EXTRACT]),
                trigger_kind: Some(CodeActionTriggerKind::INVOKED),
            },
            work_done_progress_params: WorkDoneProgressParams::default(),
            partial_result_params: PartialResultParams::default(),
        },
    )
    .await
    .expect("extract-definition code action request should not fail")
    .expect("non-empty expression selection should produce code actions");

    let extract = response
        .iter()
        .find_map(|action| match action {
            CodeActionOrCommand::CodeAction(action) if action.title == "Extract to definition" => {
                Some(action)
            }
            _ => None,
        })
        .expect("code actions should include the extract-definition refactor");
    assert_eq!(
        extract.kind,
        Some(CodeActionKind::REFACTOR_EXTRACT),
        "extract-definition action should be surfaced as a refactor.extract"
    );
    assert_eq!(
        extract.diagnostics, None,
        "extract-definition refactor should not be tied to diagnostics"
    );
    assert_eq!(
        extract.command, None,
        "extract-definition refactor should be edit-only"
    );
    assert_eq!(
        extract.disabled, None,
        "extract-definition refactor should be immediately applicable"
    );
    let changes = extract
        .edit
        .as_ref()
        .and_then(|edit| edit.changes.as_ref())
        .expect("extract-definition refactor should carry workspace changes");
    let edits = changes
        .get(&uri)
        .expect("extract-definition refactor should edit the requested document");
    assert_eq!(
        edits,
        &[
            TextEdit {
                range: selection_range,
                new_text: "extracted".to_string(),
            },
            TextEdit {
                range: Range::new(Position::new(0, 0), Position::new(0, 0)),
                new_text: "def extracted := 21 + 21\n\n".to_string(),
            },
        ],
        "extract-definition refactor should replace the selected range and insert the new declaration"
    );
}

#[test]
fn test_content_hash_computation() {
    // Test that content hashes are computed correctly
    let text = "def x := 1\ndef y := 2";
    let hash1 = CleanBackend::compute_content_hash(text, 0, 10);
    let hash2 = CleanBackend::compute_content_hash(text, 11, 21);
    let hash1_again = CleanBackend::compute_content_hash(text, 0, 10);

    // Same content should produce same hash
    assert_eq!(hash1, hash1_again);
    // Different content should produce different hash
    assert_ne!(hash1, hash2);
}

#[test]
fn test_content_hash_detects_changes() {
    // Test that changing content changes the hash
    let text1 = "def x := 1";
    let text2 = "def x := 2";

    let hash1 = CleanBackend::compute_content_hash(text1, 0, text1.len());
    let hash2 = CleanBackend::compute_content_hash(text2, 0, text2.len());

    assert_ne!(hash1, hash2, "Hash should change when content changes");
}

#[test]
fn test_incremental_state_default() {
    // Test that default incremental state is empty
    let state = IncrementalState::default();
    assert!(state.cache.is_empty());
    assert_eq!(state.stats.total_commands, 0);
    assert_eq!(state.stats.elaborated_count, 0);
    assert_eq!(state.stats.cached_count, 0);
}

#[test]
fn test_parsed_command_has_content_hash() {
    // Test that parsed commands include content hashes
    let text = "def foo := 42";
    let parsed = parse_lean_text(text);

    assert!(parsed.errors.is_empty());
    assert_eq!(parsed.commands.len(), 1);
    // Content hash should be non-zero for non-empty content
    assert_ne!(parsed.commands[0].content_hash, 0);
}

#[test]
fn test_cache_key_generation() {
    // Test cache key generation for named and anonymous declarations
    let text = "def named := 1\nexample : True := trivial";
    let parsed = parse_lean_text(text);

    assert_eq!(parsed.commands.len(), 2);
    // Named declaration should use its name
    assert_eq!(parsed.commands[0].name, Some("named".to_string()));
    // Anonymous declaration (example) should have no name
    assert_eq!(parsed.commands[1].name, None);
}

#[test]
fn test_semantic_token_type_mapping_keywords() {
    // Keywords should map to token type 0
    assert_eq!(token_kind_to_semantic_type(&TokenKind::Def), Some(0));
    assert_eq!(token_kind_to_semantic_type(&TokenKind::Theorem), Some(0));
    assert_eq!(token_kind_to_semantic_type(&TokenKind::Lemma), Some(0));
    assert_eq!(token_kind_to_semantic_type(&TokenKind::Let), Some(0));
    assert_eq!(token_kind_to_semantic_type(&TokenKind::If), Some(0));
    assert_eq!(token_kind_to_semantic_type(&TokenKind::Match), Some(0));
    assert_eq!(token_kind_to_semantic_type(&TokenKind::Structure), Some(0));
    assert_eq!(token_kind_to_semantic_type(&TokenKind::Class), Some(0));
}

#[test]
fn test_semantic_token_type_mapping_types() {
    // Type keywords should map to token type 1
    assert_eq!(token_kind_to_semantic_type(&TokenKind::Type), Some(1));
    assert_eq!(token_kind_to_semantic_type(&TokenKind::Prop), Some(1));
    assert_eq!(token_kind_to_semantic_type(&TokenKind::Sort), Some(1));
}

#[test]
fn test_semantic_token_type_mapping_literals() {
    // Numbers should map to token type 4
    assert_eq!(
        token_kind_to_semantic_type(&TokenKind::nat_lit(42)),
        Some(4)
    );
    // Strings should map to token type 5
    assert_eq!(
        token_kind_to_semantic_type(&TokenKind::StringLit("hello".to_string())),
        Some(5)
    );
}

#[test]
fn test_semantic_token_type_mapping_operators() {
    // Operators should map to token type 7
    assert_eq!(token_kind_to_semantic_type(&TokenKind::Arrow), Some(7));
    assert_eq!(token_kind_to_semantic_type(&TokenKind::FatArrow), Some(7));
    assert_eq!(token_kind_to_semantic_type(&TokenKind::Plus), Some(7));
    assert_eq!(token_kind_to_semantic_type(&TokenKind::Minus), Some(7));
    assert_eq!(token_kind_to_semantic_type(&TokenKind::Star), Some(7));
    assert_eq!(token_kind_to_semantic_type(&TokenKind::Eq), Some(7));
}

#[test]
fn test_semantic_token_type_mapping_identifiers() {
    // Identifiers should map to token type 3 (VARIABLE)
    assert_eq!(
        token_kind_to_semantic_type(&TokenKind::Ident("foo".to_string())),
        Some(3)
    );
}

#[test]
fn test_semantic_token_type_mapping_delimiters() {
    // Delimiters should return None (not highlighted)
    assert_eq!(token_kind_to_semantic_type(&TokenKind::LParen), None);
    assert_eq!(token_kind_to_semantic_type(&TokenKind::RParen), None);
    assert_eq!(token_kind_to_semantic_type(&TokenKind::LBrace), None);
    assert_eq!(token_kind_to_semantic_type(&TokenKind::RBrace), None);
    assert_eq!(token_kind_to_semantic_type(&TokenKind::Comma), None);
    assert_eq!(token_kind_to_semantic_type(&TokenKind::Colon), None);
}

#[test]
fn test_byte_offset_to_position_basic() {
    let text = "def x := 1";
    // Position at start
    let pos = byte_offset_to_position(text, 0);
    assert_eq!(pos.line, 0);
    assert_eq!(pos.character, 0);

    // Position at 'd' of 'def'
    let pos = byte_offset_to_position(text, 0);
    assert_eq!(pos.line, 0);
    assert_eq!(pos.character, 0);

    // Position at 'x'
    let pos = byte_offset_to_position(text, 4);
    assert_eq!(pos.line, 0);
    assert_eq!(pos.character, 4);
}

#[test]
fn test_byte_offset_to_position_multiline() {
    let text = "def x := 1\ndef y := 2";
    // Position on second line
    let pos = byte_offset_to_position(text, 11); // 'd' of second 'def'
    assert_eq!(pos.line, 1);
    assert_eq!(pos.character, 0);

    // Position at 'y'
    let pos = byte_offset_to_position(text, 15);
    assert_eq!(pos.line, 1);
    assert_eq!(pos.character, 4);
}

#[test]
fn test_byte_offset_to_position_counts_utf16_code_units() {
    let text = "def 😀x := 1";
    let x_offset = text.find('x').expect("x should be present");
    let pos = byte_offset_to_position(text, x_offset);
    assert_eq!(pos.line, 0);
    assert_eq!(pos.character, 6);
}

#[test]
fn test_semantic_token_types_constant() {
    // Verify the constant has expected number of types
    assert!(SEMANTIC_TOKEN_TYPES.len() >= 8);
    // Verify key types are present
    assert!(SEMANTIC_TOKEN_TYPES
        .iter()
        .any(|t| t == &SemanticTokenType::KEYWORD));
    assert!(SEMANTIC_TOKEN_TYPES
        .iter()
        .any(|t| t == &SemanticTokenType::TYPE));
    assert!(SEMANTIC_TOKEN_TYPES
        .iter()
        .any(|t| t == &SemanticTokenType::VARIABLE));
    assert!(SEMANTIC_TOKEN_TYPES
        .iter()
        .any(|t| t == &SemanticTokenType::NUMBER));
    assert!(SEMANTIC_TOKEN_TYPES
        .iter()
        .any(|t| t == &SemanticTokenType::STRING));
}

#[test]
fn test_command_kind_to_semantic_type() {
    // Definitions, theorems, lemmas -> FUNCTION (2)
    assert_eq!(command_kind_to_semantic_type(&CommandKind::Definition), 2);
    assert_eq!(command_kind_to_semantic_type(&CommandKind::Theorem), 2);
    assert_eq!(command_kind_to_semantic_type(&CommandKind::Lemma), 2);
    assert_eq!(command_kind_to_semantic_type(&CommandKind::Axiom), 2);

    // Inductive, Structure -> TYPE (1)
    assert_eq!(command_kind_to_semantic_type(&CommandKind::Inductive), 1);
    assert_eq!(command_kind_to_semantic_type(&CommandKind::Structure), 1);

    // Class -> CLASS (9)
    assert_eq!(command_kind_to_semantic_type(&CommandKind::Class), 9);

    // Instance -> PROPERTY (10)
    assert_eq!(command_kind_to_semantic_type(&CommandKind::Instance), 10);

    // Namespace -> NAMESPACE (8)
    assert_eq!(command_kind_to_semantic_type(&CommandKind::Namespace), 8);

    // Variable -> VARIABLE (3)
    assert_eq!(command_kind_to_semantic_type(&CommandKind::Variable), 3);
}

#[test]
fn test_is_likely_type_name_builtins() {
    // Built-in types should be recognized
    assert!(is_likely_type_name("Nat"));
    assert!(is_likely_type_name("Int"));
    assert!(is_likely_type_name("Bool"));
    assert!(is_likely_type_name("String"));
    assert!(is_likely_type_name("List"));
    assert!(is_likely_type_name("Option"));
    assert!(is_likely_type_name("Array"));
    assert!(is_likely_type_name("IO"));
}

#[test]
fn test_is_likely_type_name_capitalized() {
    // Capitalized identifiers are likely types
    assert!(is_likely_type_name("MyType"));
    assert!(is_likely_type_name("Foo"));
    assert!(is_likely_type_name("Point"));

    // Lowercase identifiers are not types
    assert!(!is_likely_type_name("foo"));
    assert!(!is_likely_type_name("myvar"));
    assert!(!is_likely_type_name("x"));
}

#[test]
fn test_classify_identifier_with_definitions() {
    use std::collections::HashMap;

    let mut defs = HashMap::new();
    defs.insert("myFunc".to_string(), CommandKind::Definition);
    defs.insert("MyStruct".to_string(), CommandKind::Structure);
    defs.insert("MyClass".to_string(), CommandKind::Class);
    defs.insert("myInstance".to_string(), CommandKind::Instance);

    // Known definitions should be classified correctly (not at def site)
    let (ty, mods) = classify_identifier_with_modifiers("myFunc", &defs, false);
    assert_eq!(ty, Some(2)); // FUNCTION
    assert_eq!(mods, 0); // No modifiers for usage site

    let (ty, mods) = classify_identifier_with_modifiers("MyStruct", &defs, false);
    assert_eq!(ty, Some(1)); // TYPE
    assert_eq!(mods, 0);

    let (ty, mods) = classify_identifier_with_modifiers("MyClass", &defs, false);
    assert_eq!(ty, Some(9)); // CLASS
    assert_eq!(mods, 0);

    let (ty, mods) = classify_identifier_with_modifiers("myInstance", &defs, false);
    assert_eq!(ty, Some(10)); // PROPERTY
    assert_eq!(mods, 0);

    // Unknown but capitalized -> TYPE heuristic
    let (ty, mods) = classify_identifier_with_modifiers("SomeType", &defs, false);
    assert_eq!(ty, Some(1)); // TYPE
    assert_eq!(mods, 0); // Non-builtin capitalized type

    // Unknown lowercase -> VARIABLE with READONLY
    let (ty, mods) = classify_identifier_with_modifiers("x", &defs, false);
    assert_eq!(ty, Some(3)); // VARIABLE
    assert_eq!(mods, modifier_bits::READONLY); // Variables are readonly
}

#[test]
fn test_semantic_token_modifiers_constant() {
    // Verify the constant has expected number of modifiers
    assert_eq!(SEMANTIC_TOKEN_MODIFIERS.len(), 5);
    // Verify key modifiers are present
    assert!(SEMANTIC_TOKEN_MODIFIERS
        .iter()
        .any(|m| m == &SemanticTokenModifier::DECLARATION));
    assert!(SEMANTIC_TOKEN_MODIFIERS
        .iter()
        .any(|m| m == &SemanticTokenModifier::DEFINITION));
    assert!(SEMANTIC_TOKEN_MODIFIERS
        .iter()
        .any(|m| m == &SemanticTokenModifier::READONLY));
    assert!(SEMANTIC_TOKEN_MODIFIERS
        .iter()
        .any(|m| m == &SemanticTokenModifier::DEPRECATED));
    assert!(SEMANTIC_TOKEN_MODIFIERS
        .iter()
        .any(|m| m == &SemanticTokenModifier::DEFAULT_LIBRARY));
}

#[test]
fn test_modifier_bits_values() {
    // Verify modifier bits are powers of 2 and match indices
    assert_eq!(modifier_bits::DECLARATION, 1 << 0);
    assert_eq!(modifier_bits::DEFINITION, 1 << 1);
    assert_eq!(modifier_bits::READONLY, 1 << 2);
    assert_eq!(modifier_bits::DEPRECATED, 1 << 3);
    assert_eq!(modifier_bits::DEFAULT_LIBRARY, 1 << 4);
}

#[test]
fn test_classify_identifier_definition_site() {
    use std::collections::HashMap;

    let mut defs = HashMap::new();
    defs.insert("myFunc".to_string(), CommandKind::Definition);

    // At definition site, should have DECLARATION and DEFINITION modifiers
    let (ty, mods) = classify_identifier_with_modifiers("myFunc", &defs, true);
    assert_eq!(ty, Some(2)); // FUNCTION
    assert!(mods & modifier_bits::DECLARATION != 0);
    assert!(mods & modifier_bits::DEFINITION != 0);
}

#[tokio::test]
async fn test_semantic_tokens_full_marks_declaration_and_usage_modifiers() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///semantic-token-declaration.lean").unwrap();
    let text = "axiom sem_decl : Nat\n#check sem_decl\n".to_string();

    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text.clone(), "lean".to_string()),
    );
    backend.parse_document(&uri).await;

    let result = LanguageServer::semantic_tokens_full(
        backend,
        SemanticTokensParams {
            text_document: TextDocumentIdentifier { uri: uri.clone() },
            work_done_progress_params: WorkDoneProgressParams::default(),
            partial_result_params: PartialResultParams::default(),
        },
    )
    .await
    .expect("semantic token request should not fail")
    .expect("checked document should produce semantic tokens");

    let SemanticTokensResult::Tokens(tokens) = result else {
        panic!("semantic token request should return a full token set");
    };

    let doc = backend
        .documents
        .get(&uri)
        .expect("semantic token document should remain open");
    let decl_start = text
        .find("sem_decl")
        .expect("test text should contain declaration name");
    let use_start = text
        .rfind("sem_decl")
        .expect("test text should contain declaration use");
    let decl_position = doc.offset_to_position(decl_start);
    let use_position = doc.offset_to_position(use_start);
    drop(doc);

    let decoded = decode_semantic_tokens(&tokens.data);
    let decl_token = decoded
        .iter()
        .find(|token| {
            token.line == decl_position.line && token.character == decl_position.character
        })
        .expect("semantic tokens should include the declaration name");
    assert_eq!(
        decl_token.token_type, 2,
        "declaration name should be classified as a function"
    );
    assert_eq!(
        decl_token.modifiers & (modifier_bits::DECLARATION | modifier_bits::DEFINITION),
        modifier_bits::DECLARATION | modifier_bits::DEFINITION,
        "declaration name should carry declaration and definition modifiers"
    );

    let use_token = decoded
        .iter()
        .find(|token| token.line == use_position.line && token.character == use_position.character)
        .expect("semantic tokens should include the declaration use");
    assert_eq!(
        use_token.token_type, 2,
        "known declaration use should be classified as a function"
    );
    assert_eq!(
        use_token.modifiers & (modifier_bits::DECLARATION | modifier_bits::DEFINITION),
        0,
        "use site should not carry declaration or definition modifiers"
    );
}

#[derive(Debug)]
struct DecodedSemanticToken {
    line: u32,
    character: u32,
    token_type: u32,
    modifiers: u32,
}

fn decode_semantic_tokens(tokens: &[SemanticToken]) -> Vec<DecodedSemanticToken> {
    let mut decoded = Vec::new();
    let mut line = 0;
    let mut character = 0;

    for token in tokens {
        line += token.delta_line;
        if token.delta_line == 0 {
            character += token.delta_start;
        } else {
            character = token.delta_start;
        }
        decoded.push(DecodedSemanticToken {
            line,
            character,
            token_type: token.token_type,
            modifiers: token.token_modifiers_bitset,
        });
    }

    decoded
}

/// Build an `LspService` with a single open, parsed Lean document and return
/// the service plus the document URI. The caller keeps the service alive and
/// reaches the backend via `service.inner()` (the backend itself is not
/// `Clone`, so it cannot be returned independently of its owning service).
async fn semantic_tokens_fixture(text: &str) -> (LspService<CleanBackend>, Url) {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///semantic-token-range.lean").unwrap();
    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text.to_string(), "lean".to_string()),
    );
    backend.parse_document(&uri).await;
    (service, uri)
}

#[tokio::test]
async fn test_semantic_tokens_range_unknown_document_returns_none() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///never-opened.lean").unwrap();

    let result = LanguageServer::semantic_tokens_range(
        backend,
        SemanticTokensRangeParams {
            work_done_progress_params: WorkDoneProgressParams::default(),
            partial_result_params: PartialResultParams::default(),
            text_document: TextDocumentIdentifier { uri },
            range: Range::new(Position::new(0, 0), Position::new(10, 0)),
        },
    )
    .await
    .expect("range request should not error");

    assert!(
        result.is_none(),
        "unknown document should yield no token result"
    );
}

#[tokio::test]
async fn test_semantic_tokens_range_full_span_matches_full_request() {
    let text = "def alpha := 1\ndef beta := alpha\n";
    let (service, uri) = semantic_tokens_fixture(text).await;
    let backend = service.inner();

    let full = LanguageServer::semantic_tokens_full(
        backend,
        SemanticTokensParams {
            work_done_progress_params: WorkDoneProgressParams::default(),
            partial_result_params: PartialResultParams::default(),
            text_document: TextDocumentIdentifier { uri: uri.clone() },
        },
    )
    .await
    .expect("full request should not error")
    .expect("open document should produce full tokens");
    let SemanticTokensResult::Tokens(full_tokens) = full else {
        panic!("full request should return a token set");
    };

    // A range that spans the entire document must reproduce the full result
    // byte-for-byte, including identical delta encoding.
    let range = LanguageServer::semantic_tokens_range(
        backend,
        SemanticTokensRangeParams {
            work_done_progress_params: WorkDoneProgressParams::default(),
            partial_result_params: PartialResultParams::default(),
            text_document: TextDocumentIdentifier { uri },
            range: Range::new(Position::new(0, 0), Position::new(2, 0)),
        },
    )
    .await
    .expect("range request should not error")
    .expect("open document should produce range tokens");
    let SemanticTokensRangeResult::Tokens(range_tokens) = range else {
        panic!("range request should return a token set");
    };

    assert_eq!(
        range_tokens.data, full_tokens.data,
        "whole-document range should match the full token set exactly"
    );
}

#[tokio::test]
async fn test_semantic_tokens_range_subrange_returns_only_in_range_tokens_rebased() {
    let text = "def alpha := 1\ndef beta := 2\ndef gamma := 3\n";
    let (service, uri) = semantic_tokens_fixture(text).await;
    let backend = service.inner();

    // Restrict to the second line only: [line 1, col 0) .. [line 2, col 0).
    let range = LanguageServer::semantic_tokens_range(
        backend,
        SemanticTokensRangeParams {
            work_done_progress_params: WorkDoneProgressParams::default(),
            partial_result_params: PartialResultParams::default(),
            text_document: TextDocumentIdentifier { uri },
            range: Range::new(Position::new(1, 0), Position::new(2, 0)),
        },
    )
    .await
    .expect("range request should not error")
    .expect("open document should produce range tokens");
    let SemanticTokensRangeResult::Tokens(tokens) = range else {
        panic!("range request should return a token set");
    };

    let decoded = decode_semantic_tokens(&tokens.data);
    assert!(
        !decoded.is_empty(),
        "the second line carries at least the `def` keyword and `beta` name"
    );
    assert!(
        decoded.iter().all(|token| token.line == 1),
        "no token outside line 1 should survive the filter, got {decoded:?}"
    );

    // The first surviving token must be re-based: its decoded absolute line is
    // 1 (the raw `delta_line` is the absolute line because nothing precedes it).
    let first = &decoded[0];
    assert_eq!(
        first.line, 1,
        "first in-range token should decode to its true absolute line"
    );
    assert_eq!(
        tokens.data[0].delta_line, 1,
        "first in-range token's raw delta_line should be its absolute line, not 0"
    );
}

#[tokio::test]
async fn test_semantic_tokens_range_empty_range_yields_no_tokens() {
    let text = "def alpha := 1\ndef beta := 2\n";
    let (service, uri) = semantic_tokens_fixture(text).await;
    let backend = service.inner();

    // A zero-width range (start == end) contains no positions under the
    // half-open `[start, end)` rule, so it selects nothing.
    let range = LanguageServer::semantic_tokens_range(
        backend,
        SemanticTokensRangeParams {
            work_done_progress_params: WorkDoneProgressParams::default(),
            partial_result_params: PartialResultParams::default(),
            text_document: TextDocumentIdentifier { uri },
            range: Range::new(Position::new(0, 4), Position::new(0, 4)),
        },
    )
    .await
    .expect("range request should not error")
    .expect("open document should still produce a (possibly empty) token set");
    let SemanticTokensRangeResult::Tokens(tokens) = range else {
        panic!("range request should return a token set");
    };

    assert!(
        tokens.data.is_empty(),
        "an empty range should select no tokens, got {:?}",
        tokens.data
    );
}

#[tokio::test]
async fn test_semantic_tokens_range_boundary_end_exclusive_start_inclusive() {
    let text = "def alpha := 1\ndef beta := 2\n";
    let (service, uri) = semantic_tokens_fixture(text).await;
    let backend = service.inner();

    // Establish the absolute token positions from the full set.
    let full = LanguageServer::semantic_tokens_full(
        backend,
        SemanticTokensParams {
            work_done_progress_params: WorkDoneProgressParams::default(),
            partial_result_params: PartialResultParams::default(),
            text_document: TextDocumentIdentifier { uri: uri.clone() },
        },
    )
    .await
    .expect("full request should not error")
    .expect("open document should produce full tokens");
    let SemanticTokensResult::Tokens(full_tokens) = full else {
        panic!("full request should return a token set");
    };
    let full_decoded = decode_semantic_tokens(&full_tokens.data);

    // `beta` starts at line 1, column 4 (after `def `). A range whose start is
    // exactly that position must include the `beta` token (start inclusive),
    // and a range whose end is exactly that position must exclude it (end
    // exclusive).
    let beta_pos = Position::new(1, 4);
    assert!(
        full_decoded
            .iter()
            .any(|t| t.line == beta_pos.line && t.character == beta_pos.character),
        "fixture should place a token at the `beta` start position"
    );

    let start_inclusive = LanguageServer::semantic_tokens_range(
        backend,
        SemanticTokensRangeParams {
            work_done_progress_params: WorkDoneProgressParams::default(),
            partial_result_params: PartialResultParams::default(),
            text_document: TextDocumentIdentifier { uri: uri.clone() },
            range: Range::new(beta_pos, Position::new(1, 100)),
        },
    )
    .await
    .expect("range request should not error")
    .expect("open document should produce range tokens");
    let SemanticTokensRangeResult::Tokens(start_tokens) = start_inclusive else {
        panic!("range request should return a token set");
    };
    let start_decoded = decode_semantic_tokens(&start_tokens.data);
    assert!(
        start_decoded
            .iter()
            .any(|t| t.line == beta_pos.line && t.character == beta_pos.character),
        "token on the range start edge should be included"
    );

    let end_exclusive = LanguageServer::semantic_tokens_range(
        backend,
        SemanticTokensRangeParams {
            work_done_progress_params: WorkDoneProgressParams::default(),
            partial_result_params: PartialResultParams::default(),
            text_document: TextDocumentIdentifier { uri },
            range: Range::new(Position::new(1, 0), beta_pos),
        },
    )
    .await
    .expect("range request should not error")
    .expect("open document should produce range tokens");
    let SemanticTokensRangeResult::Tokens(end_tokens) = end_exclusive else {
        panic!("range request should return a token set");
    };
    let end_decoded = decode_semantic_tokens(&end_tokens.data);
    assert!(
        end_decoded
            .iter()
            .all(|t| !(t.line == beta_pos.line && t.character == beta_pos.character)),
        "token on the range end edge should be excluded"
    );
}

#[test]
fn test_classify_identifier_builtin_types() {
    use std::collections::HashMap;
    let empty_defs = HashMap::new();

    // Built-in types should get DEFAULT_LIBRARY modifier
    let (ty, mods) = classify_identifier_with_modifiers("Nat", &empty_defs, false);
    assert_eq!(ty, Some(1)); // TYPE
    assert!(mods & modifier_bits::DEFAULT_LIBRARY != 0);

    let (ty, mods) = classify_identifier_with_modifiers("Bool", &empty_defs, false);
    assert_eq!(ty, Some(1)); // TYPE
    assert!(mods & modifier_bits::DEFAULT_LIBRARY != 0);

    let (ty, mods) = classify_identifier_with_modifiers("IO", &empty_defs, false);
    assert_eq!(ty, Some(1)); // TYPE
    assert!(mods & modifier_bits::DEFAULT_LIBRARY != 0);

    // Monad should also be recognized as builtin
    let (ty, mods) = classify_identifier_with_modifiers("Monad", &empty_defs, false);
    assert_eq!(ty, Some(1)); // TYPE
    assert!(mods & modifier_bits::DEFAULT_LIBRARY != 0);
}

#[test]
fn test_is_builtin_type() {
    // Core types
    assert!(is_builtin_type("Nat"));
    assert!(is_builtin_type("Int"));
    assert!(is_builtin_type("Bool"));
    assert!(is_builtin_type("String"));
    assert!(is_builtin_type("Prop"));
    assert!(is_builtin_type("Type"));

    // Collections
    assert!(is_builtin_type("List"));
    assert!(is_builtin_type("Array"));
    assert!(is_builtin_type("Option"));

    // Monads
    assert!(is_builtin_type("IO"));
    assert!(is_builtin_type("StateT"));
    assert!(is_builtin_type("Monad"));

    // Not builtin
    assert!(!is_builtin_type("MyType"));
    assert!(!is_builtin_type("foo"));
    assert!(!is_builtin_type("CustomMonad"));
}

#[test]
fn test_find_definition_name_span() {
    let text = "def myFunc (x : Nat) : Nat := x";
    // The name "myFunc" starts at position 4 (after "def ")
    let span = find_definition_name_span(text, 0, text.len(), "myFunc");
    let (start, end) = span.expect("should find 'myFunc' span in def");
    assert_eq!(&text[start..end], "myFunc");

    // Test with theorem
    let text2 = "theorem add_comm : ∀ x y : Nat, x + y = y + x := by sorry";
    let span2 = find_definition_name_span(text2, 0, text2.len(), "add_comm");
    let (start, end) = span2.expect("should find 'add_comm' span in theorem");
    assert_eq!(&text2[start..end], "add_comm");
}

#[test]
fn test_initialize_advertises_inlay_hint_provider() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();

    let result = tokio::runtime::Runtime::new()
        .expect("tokio runtime should initialize")
        .block_on(LanguageServer::initialize(
            backend,
            InitializeParams::default(),
        ))
        .expect("initialize should succeed");

    assert!(
        result.capabilities.inlay_hint_provider.is_some(),
        "initialize should advertise textDocument/inlayHint"
    );
}

#[test]
fn test_inlay_hints_include_inferred_def_result_type() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///inlay.lean").unwrap();
    let text = "def inferred := 1\ndef explicit : Nat := 2\n".to_string();
    let mut doc = Document::new(uri.clone(), 1, text.clone(), "lean".to_string());

    let inferred_start = text.find("def inferred").expect("definition should exist");
    let inferred_end = inferred_start + "def inferred := 1".len();
    let explicit_start = text
        .find("def explicit")
        .expect("explicit definition should exist");
    let explicit_end = explicit_start + "def explicit : Nat := 2".len();
    doc.elaborated = Some(ElaboratedDocument {
        errors: vec![],
        warnings: vec![],
        declarations: vec![
            ElaboratedDecl {
                identity: clean_kernel::Name::anon().str("inferred"),
                name: "inferred".to_string(),
                type_str: "Nat".to_string(),
                start: inferred_start,
                end: inferred_end,
            },
            ElaboratedDecl {
                identity: clean_kernel::Name::anon().str("explicit"),
                name: "explicit".to_string(),
                type_str: "Nat".to_string(),
                start: explicit_start,
                end: explicit_end,
            },
        ],
        term_infos: Vec::new(),
        holes: vec![],
        widget_modules: vec![],
    });
    let full_range = Range {
        start: Position::new(0, 0),
        end: Position::new(2, 0),
    };

    backend.documents.insert(uri.clone(), doc);

    let hints = backend.get_inlay_hints(&uri, full_range, true);
    assert_eq!(
        hints.len(),
        1,
        "only the inferred definition should get a hint"
    );
    assert_eq!(hints[0].kind, Some(InlayHintKind::TYPE));
    assert_eq!(hints[0].position, Position::new(0, 13));
    match &hints[0].label {
        InlayHintLabel::String(label) => assert_eq!(label, ": Nat"),
        InlayHintLabel::LabelParts(_) => panic!("expected a string inlay-hint label"),
    }
}

#[test]
fn test_inlay_hints_respect_requested_range() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///range.lean").unwrap();
    let text = "def inferred := 1\n".to_string();
    let mut doc = Document::new(uri.clone(), 1, text, "lean".to_string());
    doc.elaborated = Some(ElaboratedDocument {
        errors: vec![],
        warnings: vec![],
        declarations: vec![ElaboratedDecl {
            identity: clean_kernel::Name::anon().str("inferred"),
            name: "inferred".to_string(),
            type_str: "Nat".to_string(),
            start: 0,
            end: "def inferred := 1".len(),
        }],
        term_infos: Vec::new(),
        holes: vec![],
        widget_modules: vec![],
    });

    backend.documents.insert(uri.clone(), doc);

    let off_range = Range {
        start: Position::new(0, 0),
        end: Position::new(0, 12),
    };

    assert!(
        backend.get_inlay_hints(&uri, off_range, true).is_empty(),
        "hints outside the requested range should be filtered out"
    );
}

#[tokio::test]
async fn test_live_inlay_hint_uses_checked_document_result_type() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///live-inlay-hint.lean").unwrap();
    let text = "axiom live_source : Nat\ndef live_inferred := live_source\n".to_string();

    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text.clone(), "lean".to_string()),
    );
    backend.parse_document(&uri).await;
    backend.elaborate_document(&uri).await;

    let expected_type = {
        let doc = backend
            .documents
            .get(&uri)
            .expect("live checked document should remain open");
        doc.elaborated
            .as_ref()
            .and_then(|elaborated| {
                elaborated
                    .declarations
                    .iter()
                    .find(|decl| decl.name == "live_inferred")
            })
            .expect("live check should elaborate the inferred declaration")
            .type_str
            .clone()
    };

    let hints = LanguageServer::inlay_hint(
        backend,
        InlayHintParams {
            text_document: TextDocumentIdentifier { uri },
            range: Range::new(Position::new(0, 0), Position::new(2, 0)),
            work_done_progress_params: WorkDoneProgressParams::default(),
        },
    )
    .await
    .expect("inlay hint request should not fail")
    .expect("checked document should produce inlay hints");

    assert_eq!(
        hints.len(),
        1,
        "live checked document should produce one inferred result-type hint"
    );
    assert_eq!(hints[0].kind, Some(InlayHintKind::TYPE));
    assert_eq!(hints[0].position, Position::new(1, 18));
    match &hints[0].label {
        InlayHintLabel::String(label) => assert_eq!(label, &format!(": {expected_type}")),
        InlayHintLabel::LabelParts(_) => panic!("expected a string inlay-hint label"),
    }
}

#[test]
fn test_initialize_advertises_inlay_hint_resolve_provider() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();

    let result = tokio::runtime::Runtime::new()
        .expect("tokio runtime should initialize")
        .block_on(LanguageServer::initialize(
            backend,
            InitializeParams::default(),
        ))
        .expect("initialize should succeed");

    let inlay = result
        .capabilities
        .inlay_hint_provider
        .expect("initialize should advertise textDocument/inlayHint");
    match inlay {
        OneOf::Right(InlayHintServerCapabilities::Options(options)) => assert_eq!(
            options.resolve_provider,
            Some(true),
            "inlay-hint options should advertise inlayHint/resolve support"
        ),
        other => panic!("expected inlay-hint options with resolve support, got {other:?}"),
    }
}

#[test]
fn test_get_inlay_hints_carry_resolvable_data_payload() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///inlay-data.lean").unwrap();
    let text = "def inferred := 1\n".to_string();
    let mut doc = Document::new(uri.clone(), 1, text.clone(), "lean".to_string());
    doc.elaborated = Some(ElaboratedDocument {
        errors: vec![],
        warnings: vec![],
        declarations: vec![ElaboratedDecl {
            identity: clean_kernel::Name::anon().str("inferred"),
            name: "inferred".to_string(),
            type_str: "Nat".to_string(),
            start: 0,
            end: "def inferred := 1".len(),
        }],
        term_infos: Vec::new(),
        holes: vec![],
        widget_modules: vec![],
    });
    backend.documents.insert(uri.clone(), doc);

    let full_range = Range {
        start: Position::new(0, 0),
        end: Position::new(1, 0),
    };
    let hints = backend.get_inlay_hints(&uri, full_range, true);
    assert_eq!(hints.len(), 1, "the inferred def should get a hint");

    let data = hints[0]
        .data
        .as_ref()
        .and_then(navigation::InlayHintData::from_value)
        .expect("hint should carry a resolvable data payload");
    assert_eq!(data.uri, uri.to_string());
    assert_eq!(data.name, "inferred");
}

#[test]
fn test_resolve_inlay_hint_attaches_full_signature_tooltip() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///inlay-resolve.lean").unwrap();
    let text = "def inferred := 1\n".to_string();
    let mut doc = Document::new(uri.clone(), 1, text, "lean".to_string());
    doc.elaborated = Some(ElaboratedDocument {
        errors: vec![],
        warnings: vec![],
        declarations: vec![ElaboratedDecl {
            identity: clean_kernel::Name::anon().str("inferred"),
            name: "inferred".to_string(),
            type_str: "Nat".to_string(),
            start: 0,
            end: "def inferred := 1".len(),
        }],
        term_infos: Vec::new(),
        holes: vec![],
        widget_modules: vec![],
    });
    backend.documents.insert(uri.clone(), doc);

    let full_range = Range {
        start: Position::new(0, 0),
        end: Position::new(1, 0),
    };
    let hint = backend
        .get_inlay_hints(&uri, full_range, true)
        .pop()
        .expect("inferred def should produce a hint");

    let resolved = tokio::runtime::Runtime::new()
        .expect("tokio runtime should initialize")
        .block_on(LanguageServer::inlay_hint_resolve(backend, hint))
        .expect("inlayHint/resolve should succeed");

    match resolved.tooltip {
        Some(InlayHintTooltip::MarkupContent(markup)) => {
            assert_eq!(markup.kind, MarkupKind::Markdown);
            assert_eq!(markup.value, "```lean\ninferred : Nat\n```");
        }
        other => panic!("expected a markdown signature tooltip, got {other:?}"),
    }
}

#[test]
fn test_resolve_inlay_hint_without_data_is_clean_passthrough() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();

    let bare = InlayHint {
        position: Position::new(3, 7),
        label: InlayHintLabel::String(": Nat".to_string()),
        kind: Some(InlayHintKind::TYPE),
        text_edits: None,
        tooltip: None,
        padding_left: Some(true),
        padding_right: Some(true),
        data: None,
    };

    let resolved = tokio::runtime::Runtime::new()
        .expect("tokio runtime should initialize")
        .block_on(LanguageServer::inlay_hint_resolve(backend, bare.clone()))
        .expect("inlayHint/resolve should succeed for a data-less hint");

    // `InlayHint` does not implement `PartialEq`; compare the serialized form,
    // which captures every field including `tooltip` staying `None`.
    assert_eq!(
        serde_json::to_value(&resolved).expect("resolved hint should serialize"),
        serde_json::to_value(&bare).expect("bare hint should serialize"),
        "a hint with no data should pass through unchanged"
    );
}

#[test]
fn test_resolve_inlay_hint_unknown_document_is_passthrough() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();

    // A well-formed data payload that points at a document the server has
    // never seen (e.g. it was closed between the hint and resolve requests).
    let data = navigation::InlayHintData {
        uri: "file:///never-opened.lean".to_string(),
        name: "ghost".to_string(),
    };
    let hint = InlayHint {
        position: Position::new(0, 0),
        label: InlayHintLabel::String(": ?".to_string()),
        kind: Some(InlayHintKind::TYPE),
        text_edits: None,
        tooltip: None,
        padding_left: None,
        padding_right: None,
        data: data.to_value(),
    };

    let resolved = backend.resolve_inlay_hint(hint.clone());
    assert_eq!(
        serde_json::to_value(&resolved).expect("resolved hint should serialize"),
        serde_json::to_value(&hint).expect("hint should serialize"),
        "resolving against an unknown document should leave the hint unchanged"
    );
}

#[test]
fn test_initialize_advertises_completion_item_resolve_provider() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();

    let result = tokio::runtime::Runtime::new()
        .expect("tokio runtime should initialize")
        .block_on(LanguageServer::initialize(
            backend,
            InitializeParams::default(),
        ))
        .expect("initialize should succeed");

    let completion = result
        .capabilities
        .completion_provider
        .expect("initialize should advertise textDocument/completion");
    assert_eq!(
        completion.resolve_provider,
        Some(true),
        "completion options should advertise completionItem/resolve support"
    );
}

#[test]
fn test_completion_items_carry_resolvable_data_payload() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///completion-data.lean").unwrap();
    let text = "axiom completion_payload : Nat\n#check completion_payload\n".to_string();

    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text, "lean".to_string()),
    );
    tokio::runtime::Runtime::new()
        .expect("tokio runtime should initialize")
        .block_on(async {
            backend.parse_document(&uri).await;
            backend.elaborate_document(&uri).await;
        });

    let position = backend
        .documents
        .get(&uri)
        .map(|doc| {
            let offset = doc
                .text()
                .find("#check completion_payload")
                .expect("test text should contain completion prefix")
                + "#check completion_payload".len();
            doc.offset_to_position(offset)
        })
        .expect("checked document should remain open");

    let response = tokio::runtime::Runtime::new()
        .expect("tokio runtime should initialize")
        .block_on(LanguageServer::completion(
            backend,
            CompletionParams {
                text_document_position: TextDocumentPositionParams {
                    text_document: TextDocumentIdentifier { uri: uri.clone() },
                    position,
                },
                work_done_progress_params: WorkDoneProgressParams::default(),
                partial_result_params: PartialResultParams::default(),
                context: None,
            },
        ))
        .expect("completion request should succeed")
        .expect("completion request should return items");

    let CompletionResponse::Array(items) = response else {
        panic!("expected completion item array");
    };
    let item = items
        .iter()
        .find(|item| item.label == "completion_payload")
        .expect("completion should include the live checked declaration");
    let data = item
        .data
        .as_ref()
        .and_then(navigation::CompletionItemData::from_value)
        .expect("definition completion should carry a resolvable data payload");
    assert_eq!(data.uri, uri.to_string());
    assert_eq!(data.name, "completion_payload");
}

#[test]
fn test_resolve_completion_item_enriches_detail_and_documentation() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///completion-resolve.lean").unwrap();
    let text = "def resolved := 1\n".to_string();
    let mut doc = Document::new(uri.clone(), 1, text, "lean".to_string());
    doc.elaborated = Some(ElaboratedDocument {
        errors: vec![],
        warnings: vec![],
        declarations: vec![ElaboratedDecl {
            identity: clean_kernel::Name::anon().str("resolved"),
            name: "resolved".to_string(),
            type_str: "Nat".to_string(),
            start: 0,
            end: "def resolved := 1".len(),
        }],
        term_infos: Vec::new(),
        holes: vec![],
        widget_modules: vec![],
    });
    backend.documents.insert(uri.clone(), doc);

    // A lazily-returned item: it carries the resolve payload but no detail or
    // documentation yet, exactly as `textDocument/completion` would return it
    // before the client requests `completionItem/resolve`.
    let item = CompletionItem {
        label: "resolved".to_string(),
        kind: Some(CompletionItemKind::FUNCTION),
        data: navigation::CompletionItemData {
            uri: uri.to_string(),
            name: "resolved".to_string(),
        }
        .to_value(),
        ..Default::default()
    };

    let resolved = tokio::runtime::Runtime::new()
        .expect("tokio runtime should initialize")
        .block_on(LanguageServer::completion_resolve(backend, item))
        .expect("completionItem/resolve should succeed");

    assert_eq!(
        resolved.detail.as_deref(),
        Some("Nat"),
        "resolve should attach the elaborated type as detail"
    );
    match resolved.documentation {
        Some(Documentation::MarkupContent(markup)) => {
            assert_eq!(markup.kind, MarkupKind::Markdown);
            assert_eq!(markup.value, "```lean\nresolved : Nat\n```");
        }
        other => panic!("expected markdown signature documentation, got {other:?}"),
    }
}

#[test]
fn test_resolve_completion_item_without_data_is_clean_passthrough() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();

    // A keyword completion: no `data`, so resolve cannot enrich it.
    let bare = CompletionItem {
        label: "theorem".to_string(),
        kind: Some(CompletionItemKind::KEYWORD),
        insert_text: Some("theorem".to_string()),
        data: None,
        ..Default::default()
    };

    let resolved = tokio::runtime::Runtime::new()
        .expect("tokio runtime should initialize")
        .block_on(LanguageServer::completion_resolve(backend, bare.clone()))
        .expect("completionItem/resolve should succeed for a data-less item");

    assert_eq!(
        serde_json::to_value(&resolved).expect("resolved item should serialize"),
        serde_json::to_value(&bare).expect("bare item should serialize"),
        "an item with no data should pass through unchanged"
    );
}

#[test]
fn test_resolve_completion_item_unknown_document_is_passthrough() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();

    // A well-formed payload pointing at a document the server never saw (e.g.
    // closed between the completion and resolve requests).
    let item = CompletionItem {
        label: "ghost".to_string(),
        kind: Some(CompletionItemKind::FUNCTION),
        data: navigation::CompletionItemData {
            uri: "file:///never-opened.lean".to_string(),
            name: "ghost".to_string(),
        }
        .to_value(),
        ..Default::default()
    };

    let resolved = backend.resolve_completion_item(item.clone());
    assert_eq!(
        serde_json::to_value(&resolved).expect("resolved item should serialize"),
        serde_json::to_value(&item).expect("item should serialize"),
        "resolving against an unknown document should leave the item unchanged"
    );
}

#[test]
fn test_plain_goal_returns_none_until_tactic_state_is_tracked() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///plain-goal.lean").unwrap();
    let text = "theorem demo : True := by\n  trivial\n".to_string();
    let mut doc = Document::new(uri.clone(), 1, text, "lean".to_string());
    doc.elaborated = Some(ElaboratedDocument {
        errors: vec![],
        warnings: vec![],
        declarations: vec![ElaboratedDecl {
            identity: clean_kernel::Name::anon().str("demo"),
            name: "demo".to_string(),
            type_str: "True".to_string(),
            start: 0,
            end: "theorem demo : True := by\n  trivial".len(),
        }],
        term_infos: Vec::new(),
        holes: vec![],
        widget_modules: vec![],
    });

    backend.documents.insert(uri.clone(), doc);

    let response = backend.plain_goal(crate::rpc::PlainGoalParams {
        text_document: crate::rpc::TextDocumentIdentifier { uri },
        position: Position::new(1, 2),
    });

    assert!(
        response.is_none(),
        "plainGoal is currently a non-parity baseline: tactic goal state is not tracked yet"
    );
    assert_eq!(
        serde_json::to_value(response).expect("plainGoal reply should serialize"),
        serde_json::Value::Null,
        "a missing snapshot is a null result, not an empty response object"
    );
}

#[test]
fn test_plain_goal_returns_live_tactic_snapshot_when_elaboration_tracks_goals() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///plain-goal-live-snapshot.lean").unwrap();
    let text = "theorem demo : True := by\n  trivial\n".to_string();
    let mut doc = Document::new(uri.clone(), 1, text, "lean".to_string());
    doc.elaborated = Some(ElaboratedDocument {
        errors: vec![],
        warnings: vec![],
        declarations: vec![ElaboratedDecl {
            identity: clean_kernel::Name::anon().str("demo"),
            name: "demo".to_string(),
            type_str: "True".to_string(),
            start: 0,
            end: "theorem demo : True := by\n  trivial".len(),
        }],
        term_infos: Vec::new(),
        holes: vec![],
        widget_modules: vec![],
    });

    backend.documents.insert(uri.clone(), doc);
    backend.tactic_goal_snapshots.insert(
        uri.clone(),
        vec![TacticGoalSnapshot {
            range: Range::new(Position::new(1, 2), Position::new(1, 9)),
            goals: vec!["⊢ True".to_string()],
        }],
    );

    let response = backend.plain_goal(crate::rpc::PlainGoalParams {
        text_document: crate::rpc::TextDocumentIdentifier { uri: uri.clone() },
        position: Position::new(1, 4),
    });

    assert_eq!(
        response.as_ref().map(|response| response.goals.clone()),
        Some(vec!["⊢ True".to_string()]),
        "plainGoal should return the live tactic snapshot covering the requested position"
    );
    assert_eq!(
        serde_json::to_value(&response).expect("plainGoal reply should serialize"),
        serde_json::json!({"goals": ["⊢ True"], "rendered": "```lean\n⊢ True\n```"}),
        "a live snapshot must carry Lean's plain and Markdown forms"
    );

    let outside_snapshot = backend.plain_goal(crate::rpc::PlainGoalParams {
        text_document: crate::rpc::TextDocumentIdentifier { uri: uri.clone() },
        position: Position::new(0, 0),
    });
    assert!(
        outside_snapshot.is_none(),
        "plainGoal should keep range-local tactic snapshots fail-closed"
    );
    assert_eq!(
        serde_json::to_value(outside_snapshot).expect("missing snapshot should serialize"),
        serde_json::Value::Null
    );

    for (goals, rendered) in [
        (vec![], "no goals"),
        (
            vec!["h : Nat\n⊢ h = h".to_string(), "⊢ True".to_string()],
            "```lean\nh : Nat\n⊢ h = h\n```\n---\n```lean\n⊢ True\n```",
        ),
    ] {
        backend.tactic_goal_snapshots.insert(
            uri.clone(),
            vec![TacticGoalSnapshot {
                range: Range::new(Position::new(1, 2), Position::new(1, 9)),
                goals: goals.clone(),
            }],
        );
        let response = backend.plain_goal(crate::rpc::PlainGoalParams {
            text_document: crate::rpc::TextDocumentIdentifier { uri: uri.clone() },
            position: Position::new(1, 4),
        });
        assert_eq!(
            serde_json::to_value(response).expect("snapshot reply should serialize"),
            serde_json::json!({"goals": goals, "rendered": rendered}),
            "an empty snapshot is solved, and multiple goals retain Markdown separators"
        );
    }
}

#[tokio::test]
async fn test_plain_goal_live_elaboration_populates_tactic_snapshot() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///plain-goal-live-elaboration.lean").unwrap();
    let text = "theorem live_goal : True := by\n  sorry\n".to_string();

    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text, "lean".to_string()),
    );
    backend.parse_document(&uri).await;
    backend.elaborate_document(&uri).await;

    let response = backend.plain_goal(crate::rpc::PlainGoalParams {
        text_document: crate::rpc::TextDocumentIdentifier { uri: uri.clone() },
        position: Position::new(1, 2),
    });

    assert_eq!(
        response.map(|response| response.goals),
        Some(vec!["⊢ True".to_string()]),
        "plainGoal should expose the tactic snapshot produced during live document elaboration"
    );

    let outside_snapshot = backend.plain_goal(crate::rpc::PlainGoalParams {
        text_document: crate::rpc::TextDocumentIdentifier { uri },
        position: Position::new(0, 0),
    });
    assert!(
        outside_snapshot.is_none(),
        "live elaboration tactic snapshots should stay range-local"
    );
}

#[tokio::test]
async fn test_plain_goal_live_elaboration_uses_typed_post_tactic_snapshot_when_target_elaborates() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///plain-goal-post-tactic-elaboration.lean").unwrap();
    let text = "theorem prop_goal : Prop := by\n  skip\n".to_string();

    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text, "lean".to_string()),
    );
    backend.parse_document(&uri).await;
    backend.elaborate_document(&uri).await;

    let response = backend.plain_goal(crate::rpc::PlainGoalParams {
        text_document: crate::rpc::TextDocumentIdentifier { uri: uri.clone() },
        position: Position::new(1, 3),
    });

    let goals = response
        .expect("plainGoal should expose the typed post-tactic snapshot at the tactic span")
        .goals;
    assert_eq!(goals.len(), 1);
    assert!(
        goals[0].contains("Sort") || goals[0].contains("Prop"),
        "post-tactic snapshot should render the elaborated Prop target, got {goals:?}"
    );

    let outside_snapshot = backend.plain_goal(crate::rpc::PlainGoalParams {
        text_document: crate::rpc::TextDocumentIdentifier { uri },
        position: Position::new(0, 0),
    });
    assert!(
        outside_snapshot.is_none(),
        "typed post-tactic snapshots should stay tied to the tactic span"
    );
}

#[test]
fn test_post_tactic_snapshot_bridge_names_missing_typed_proof_state() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///post-tactic-snapshot-bridge.lean").unwrap();
    let text = "theorem bridge_goal : True := by\n  skip\n".to_string();
    let doc = Document::new(uri, 1, text.clone(), "lean".to_string());
    let decls =
        clean_parser::parse_file_with_tactics(&text, &CleanBackend::builtin_tactic_patterns())
            .expect("test theorem should parse with tactic syntax");
    let clean_parser::SurfaceDecl::Theorem { ty, proof, .. } = &decls[0] else {
        panic!("expected theorem declaration");
    };

    let gap =
        CleanBackend::post_tactic_snapshot_bridge_gap_from_type_and_proof(&doc, &text, ty, proof)
            .expect("bridge should recover post-tactic range and script text");

    assert_eq!(
        gap.post_tactic_range,
        Range::new(Position::new(1, 2), Position::new(1, 6))
    );
    assert_eq!(gap.tactic_script, "skip");
    assert_eq!(gap.target_text, "True");
    assert_eq!(
        gap.missing_input,
        "typed ProofState for clean_elab::tactic::run_tactic_script_with_snapshots"
    );
    assert!(
        backend.tactic_goal_snapshots.is_empty(),
        "the bridge must not populate plainGoal snapshots without a typed ProofState"
    );
}

#[tokio::test]
async fn test_plain_goal_bound_theorem_requires_theorem_local_context_for_post_tactic_snapshot() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///plain-goal-bound-theorem-context.lean").unwrap();
    let text = "theorem bound_goal (p : Prop) : Prop := by\n  skip\n".to_string();
    let doc = Document::new(uri.clone(), 1, text.clone(), "lean".to_string());
    let decls =
        clean_parser::parse_file_with_tactics(&text, &CleanBackend::builtin_tactic_patterns())
            .expect("bound theorem should parse with tactic syntax");
    let clean_parser::SurfaceDecl::Theorem {
        binders, ty, proof, ..
    } = &decls[0]
    else {
        panic!("expected theorem declaration");
    };

    let gap =
        CleanBackend::post_tactic_snapshot_bridge_gap_from_theorem(&doc, &text, binders, ty, proof)
            .expect("bridge should still recover the source tactic span");

    assert_eq!(
        gap.post_tactic_range,
        Range::new(Position::new(1, 2), Position::new(1, 6))
    );
    assert_eq!(gap.tactic_script, "skip");
    assert_eq!(gap.target_text, "Prop");
    assert_eq!(
        gap.missing_input,
        "theorem-local binder context for proof_state_for_tactic_target"
    );

    backend.documents.insert(uri.clone(), doc);
    backend.parse_document(&uri).await;
    backend.elaborate_document(&uri).await;

    let response = backend.plain_goal(crate::rpc::PlainGoalParams {
        text_document: crate::rpc::TextDocumentIdentifier { uri },
        position: Position::new(1, 3),
    });

    assert_eq!(
        response.map(|response| response.goals),
        Some(vec!["p : Prop\n⊢ Prop".to_string()]),
        "a bound theorem must show the actual typed local context at skip"
    );
}

#[tokio::test]
async fn test_plain_goal_bound_theorem_initial_goal_renders_binders_as_hypotheses() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///plain-goal-binder-hypotheses.lean").unwrap();
    let text = "theorem bound_live (n : Nat) (h : n = n) : n = n := by\n  sorry\n".to_string();

    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text, "lean".to_string()),
    );
    backend.parse_document(&uri).await;
    backend.elaborate_document(&uri).await;

    let response = backend.plain_goal(crate::rpc::PlainGoalParams {
        text_document: crate::rpc::TextDocumentIdentifier { uri: uri.clone() },
        position: Position::new(1, 2),
    });

    assert_eq!(
        response.map(|response| response.goals),
        Some(vec!["n : Nat\nh : n = n\n⊢ n = n".to_string()]),
        "each theorem binder should appear as a hypothesis line above the initial target"
    );

    let outside_snapshot = backend.plain_goal(crate::rpc::PlainGoalParams {
        text_document: crate::rpc::TextDocumentIdentifier { uri },
        position: Position::new(0, 0),
    });
    assert!(
        outside_snapshot.is_none(),
        "binder-aware initial snapshots stay range-local"
    );
}

#[tokio::test]
async fn test_bound_theorem_initial_goal_renders_implicit_and_instance_binders() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///binder-initial-goal-kinds.lean").unwrap();
    let text = "theorem bound_hyp {p : Prop} (hp : p) [inst : Decidable p] : p := by\n  skip\n"
        .to_string();
    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text, "lean".to_string()),
    );
    backend.parse_document(&uri).await;
    backend.elaborate_document(&uri).await;
    let response = backend
        .plain_goal(crate::rpc::PlainGoalParams {
            text_document: crate::rpc::TextDocumentIdentifier { uri },
            position: Position::new(1, 3),
        })
        .expect("the real producer must preserve all binder kinds");
    assert_eq!(
        response.goals,
        vec!["p : Prop\nhp : p\ninst : Decidable p\n⊢ p".to_string()],
        "implicit, explicit and instance locals come from the actual typed context"
    );
}

#[test]
fn test_generate_diagnostics_preserves_parse_error_range() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///parse-diagnostic-range.lean").unwrap();
    let text = "def ok := 1\n#check bad\n".to_string();
    let error_start = text.find("bad").expect("test text should contain bad");
    let error_end = error_start + "bad".len();
    let mut doc = Document::new(uri, 1, text, "lean".to_string());
    doc.parsed = Some(ParsedDocument {
        errors: vec![ParseError {
            start: error_start,
            end: error_end,
            message: "unknown identifier 'bad'".to_string(),
            related: Vec::new(),
        }],
        commands: vec![],
    });

    let expected_range = Range {
        start: doc.offset_to_position(error_start),
        end: doc.offset_to_position(error_end),
    };
    let diagnostics = backend.generate_diagnostics(&doc);
    let diagnostic = diagnostics
        .iter()
        .find(|diagnostic| {
            diagnostic.code == Some(NumberOrString::String("parse-error".to_string()))
        })
        .expect("stored parser error should be exposed as an LSP parse diagnostic");

    assert_eq!(
        diagnostic.range, expected_range,
        "parse diagnostic range should match parser byte span converted to LSP positions"
    );
    assert_eq!(
        diagnostic.severity,
        Some(DiagnosticSeverity::ERROR),
        "parse diagnostic should remain an LSP error"
    );
}

#[tokio::test]
async fn test_live_hover_uses_checked_declaration_range() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///live-hover-range.lean").unwrap();
    let text = "axiom hover_decl : Nat\n".to_string();

    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text, "lean".to_string()),
    );
    backend.parse_document(&uri).await;
    backend.elaborate_document(&uri).await;

    let doc = backend
        .documents
        .get(&uri)
        .expect("live checked document should remain open");
    let decl = doc
        .elaborated
        .as_ref()
        .and_then(|elaborated| elaborated.declarations.first())
        .expect("live check should produce an elaborated declaration")
        .clone();
    // The declaration's EXTENT — keyword through the last byte it occupies —
    // not the keyword-only span the parser records as `decl.start..decl.end`.
    // Those two coincided until the hover repair, which is why hover answered
    // only inside `axiom`.
    let expected_range = Range {
        start: doc.offset_to_position(decl.start),
        end: doc.offset_to_position("axiom hover_decl : Nat".len()),
    };
    assert_eq!(
        decl.end,
        "axiom".len(),
        "the parser still records the keyword-only span; if this changes, the \
         hover extent is no longer the thing under test"
    );
    let query_position = expected_range.start;
    // A position PAST the keyword and outside any identifier (the `:`): the
    // regression this test exists for — it answered `null` before the repair.
    let colon_position = doc.offset_to_position("axiom hover_decl ".len());
    drop(doc);

    for (label, position) in [
        ("keyword", query_position),
        ("type ascription", colon_position),
    ] {
        let hover = backend
            .get_hover_at(&uri, position)
            .unwrap_or_else(|| panic!("hover at the {label} should answer from live state"));
        assert_eq!(
            hover.range,
            Some(expected_range),
            "hover at the {label} should span the whole declaration"
        );
        match hover.contents {
            HoverContents::Markup(markup) => {
                assert!(
                    markup.value.contains("hover_decl"),
                    "hover markdown should include the declaration name"
                );
                assert!(
                    markup.value.contains(&decl.type_str),
                    "hover markdown should include the live checked declaration type"
                );
            }
            other => panic!("expected markdown hover contents, got {other:?}"),
        }
    }
}

#[tokio::test]
async fn test_live_hover_excludes_checked_declaration_end_boundary() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///live-hover-end-boundary.lean").unwrap();
    let text = "axiom hover_end_decl : Nat\n\n#check True\n".to_string();

    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text, "lean".to_string()),
    );
    backend.parse_document(&uri).await;
    backend.elaborate_document(&uri).await;

    let doc = backend
        .documents
        .get(&uri)
        .expect("live checked document should remain open");
    doc.elaborated
        .as_ref()
        .and_then(|elaborated| elaborated.declarations.first())
        .expect("live check should produce an elaborated declaration");
    // The blank line between the axiom and `#check`: inside no declaration's
    // extent, so hover must answer nothing there.
    let gap_position = doc.offset_to_position("axiom hover_end_decl : Nat\n".len());
    // `#check True` parses as a command but elaborates to no declaration, so
    // its own extent has no type to report either.
    let command_position = doc.offset_to_position("axiom hover_end_decl : Nat\n\n#ch".len());
    drop(doc);

    assert!(
        backend.get_hover_at(&uri, gap_position).is_none(),
        "hover should treat declaration extents as half-open: the gap between \
         two commands belongs to neither"
    );
    assert!(
        backend.get_hover_at(&uri, command_position).is_none(),
        "a command that elaborates to no declaration has no type to hover"
    );
}

/// A name from the document's import closure — here the prelude floor an
/// import-free document elaborates against — hovers with its own type, not
/// with the enclosing declaration's.
#[tokio::test]
async fn test_hover_resolves_a_constant_from_the_document_import_closure() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///hover-imported-constant.lean").unwrap();
    let text = "def hover_imported : Nat := 0\n".to_string();

    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text, "lean".to_string()),
    );
    backend.parse_document(&uri).await;
    backend.elaborate_document(&uri).await;

    let nat_position = backend
        .documents
        .get(&uri)
        .map(|doc| doc.offset_to_position("def hover_imported : N".len()))
        .expect("document should remain open");

    let hover = backend
        .get_hover_at(&uri, nat_position)
        .expect("hover on `Nat` should resolve through the import closure");
    let value = hover_markup_value(&hover);
    assert!(
        value.contains("Nat : "),
        "hover should report `Nat`'s own type, got {value:?}"
    );
    assert!(
        !value.contains("hover_imported"),
        "hover on `Nat` must not fall back to the enclosing declaration, got {value:?}"
    );
    assert_eq!(
        hover.range,
        Some(Range {
            start: Position {
                line: 0,
                character: 21
            },
            end: Position {
                line: 0,
                character: 24
            },
        }),
        "hover on an identifier should range over the identifier"
    );
}

/// A declaration's extent spans every line it occupies, so a cursor on a
/// structure field — many lines below the `structure` keyword the parser
/// records as the declaration's whole span — still hovers the structure.
#[tokio::test]
async fn test_hover_extent_spans_a_multiline_declaration() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///hover-multiline-extent.lean").unwrap();
    let text = "structure HoverPoint where\n  px : Nat\n  py : Nat\n".to_string();

    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text, "lean".to_string()),
    );
    backend.parse_document(&uri).await;
    backend.elaborate_document(&uri).await;

    // Column 2 of the second field line: `py`, which is neither a document
    // declaration nor a constant, so hover falls back to the enclosing
    // declaration — three lines below its recorded span.
    let field_position = Position {
        line: 2,
        character: 3,
    };

    let hover = backend
        .get_hover_at(&uri, field_position)
        .expect("a structure field line lies inside the structure's extent");
    let value = hover_markup_value(&hover);
    assert!(
        value.contains("HoverPoint : "),
        "hover on a field line should report the enclosing structure, got {value:?}"
    );
    assert_eq!(
        hover.range.map(|range| range.end),
        Some(Position {
            line: 2,
            character: 10
        }),
        "the extent should end at the structure's last byte, not at its keyword"
    );
}

#[tokio::test]
async fn test_live_hover_renders_lean_syntax_type_not_debug() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///live-hover-pretty-type.lean").unwrap();
    let text = "def f : Nat → Nat := fun n => n\n".to_string();

    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text, "lean".to_string()),
    );
    backend.parse_document(&uri).await;
    backend.elaborate_document(&uri).await;

    let (query_position, type_str) = backend
        .documents
        .get(&uri)
        .and_then(|doc| {
            let decl = doc.elaborated.as_ref()?.declarations.first()?;
            Some((doc.offset_to_position(decl.start), decl.type_str.clone()))
        })
        .expect("live check should elaborate the function declaration");
    assert_eq!(
        type_str, "Nat -> Nat",
        "elaborated declaration type must be the pretty-printed Lean form"
    );

    let hover = backend
        .get_hover_at(&uri, query_position)
        .expect("hover should surface the elaborated declaration");
    let HoverContents::Markup(markup) = hover.contents else {
        panic!("expected markdown hover contents");
    };
    assert!(
        markup.value.contains("f : Nat -> Nat"),
        "hover should render the declaration type in Lean syntax, got: {}",
        markup.value
    );
    for token in ["Const(", "Sort(", "Pi(", "Name {"] {
        assert!(
            !markup.value.contains(token),
            "hover must not leak Rust Debug formatting ({token}), got: {}",
            markup.value
        );
    }
}

#[tokio::test]
async fn test_plain_term_goal_captured_hole_renders_lean_syntax_type_not_debug() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///sorry-hole-pretty-type.lean").unwrap();
    // Require an actual span-tagged expected type from elaboration.
    let text = "def g : Nat → Nat := _\n".to_string();

    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text.clone(), "lean".to_string()),
    );
    backend.parse_document(&uri).await;
    backend.elaborate_document(&uri).await;

    let hole_offset = text.find('_').expect("text contains the hole token");
    let hole_position = backend
        .documents
        .get(&uri)
        .map(|doc| doc.offset_to_position(hole_offset))
        .expect("live checked document should remain open");

    let response = backend.plain_term_goal(crate::rpc::PlainTermGoalParams {
        text_document: crate::rpc::TextDocumentIdentifier { uri },
        position: hole_position,
    });
    let response =
        response.expect("plainTermGoal on a captured body hole should report the recorded goal");
    assert_eq!(response.range.start, hole_position);
    assert_eq!(
        response.range.end,
        Position::new(hole_position.line, hole_position.character + 1)
    );
    let goal = response.goal;
    assert_eq!(
        goal, "⊢ Nat → Nat",
        "plainTermGoal must expose the pretty-printed Lean type, not Rust Debug structure"
    );
}

#[tokio::test]
async fn test_live_goto_definition_uses_checked_document_declaration_range() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///live-goto-definition-range.lean").unwrap();
    let text = "axiom goto_decl : Nat\n#check goto_decl\n".to_string();

    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text, "lean".to_string()),
    );
    backend.parse_document(&uri).await;
    backend.elaborate_document(&uri).await;

    let doc = backend
        .documents
        .get(&uri)
        .expect("live checked document should remain open");
    let parsed_cmd = doc
        .parsed
        .as_ref()
        .and_then(|parsed| {
            parsed
                .commands
                .iter()
                .find(|cmd| cmd.name.as_deref() == Some("goto_decl"))
        })
        .expect("live parse should index the goto_decl declaration");
    let expected_range = Range {
        start: doc.offset_to_position(parsed_cmd.start),
        end: doc.offset_to_position(parsed_cmd.end),
    };
    drop(doc);

    let (definition_uri, definition_range) = backend
        .find_definition("goto_decl")
        .expect("definition index should resolve the live checked declaration");
    assert_eq!(definition_uri, uri);
    assert_eq!(
        definition_range, expected_range,
        "goto definition range should match the live parsed declaration range"
    );
}

#[tokio::test]
async fn test_live_completion_uses_checked_document_definition_item_and_replacement_range() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///live-completion-item.lean").unwrap();
    let text = "axiom completion_decl : Nat\n#check completion\n".to_string();

    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text, "lean".to_string()),
    );
    backend.parse_document(&uri).await;
    backend.elaborate_document(&uri).await;

    let (completion_position, expected_replacement_range) = backend
        .documents
        .get(&uri)
        .map(|doc| {
            let offset = doc
                .text()
                .find("#check completion")
                .expect("test text should contain completion prefix")
                + "#check completion".len();
            let replacement_start = offset - "completion".len();
            (
                doc.offset_to_position(offset),
                Range {
                    start: doc.offset_to_position(replacement_start),
                    end: doc.offset_to_position(offset),
                },
            )
        })
        .expect("live checked document should remain open");

    let response = backend
        .completion(CompletionParams {
            text_document_position: TextDocumentPositionParams {
                text_document: TextDocumentIdentifier { uri },
                position: completion_position,
            },
            work_done_progress_params: WorkDoneProgressParams::default(),
            partial_result_params: PartialResultParams::default(),
            context: None,
        })
        .await
        .expect("completion request should succeed")
        .expect("completion request should return items");

    let CompletionResponse::Array(items) = response else {
        panic!("expected completion item array");
    };
    let item = items
        .iter()
        .find(|item| item.label == "completion_decl")
        .expect("completion should include the live checked declaration");
    assert_eq!(
        item.kind,
        Some(CompletionItemKind::CONSTANT),
        "axiom completion should use constant completion kind"
    );
    assert_eq!(
        item.insert_text.as_deref(),
        Some("completion_decl"),
        "completion should insert the checked declaration name as plain text"
    );
    let Some(CompletionTextEdit::Edit(text_edit)) = &item.text_edit else {
        panic!("completion should replace the typed prefix with a text edit");
    };
    assert_eq!(
        text_edit.range, expected_replacement_range,
        "completion text_edit should replace only the typed identifier prefix"
    );
    assert_eq!(
        text_edit.new_text, "completion_decl",
        "completion text_edit should insert the checked declaration name"
    );
}

#[tokio::test]
async fn test_live_completion_uses_checked_document_declaration_type_detail() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///live-completion-detail.lean").unwrap();
    let text = "axiom completion_detail_decl : Nat\n#check completion_detail\n".to_string();

    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text, "lean".to_string()),
    );
    backend.parse_document(&uri).await;
    backend.elaborate_document(&uri).await;

    let (completion_position, expected_detail) = backend
        .documents
        .get(&uri)
        .map(|doc| {
            let offset = doc
                .text()
                .find("#check completion_detail")
                .expect("test text should contain completion prefix")
                + "#check completion_detail".len();
            let detail = doc
                .elaborated
                .as_ref()
                .and_then(|elaborated| {
                    elaborated
                        .declarations
                        .iter()
                        .find(|decl| decl.name == "completion_detail_decl")
                })
                .expect("live check should elaborate the completion detail declaration")
                .type_str
                .clone();
            (doc.offset_to_position(offset), detail)
        })
        .expect("live checked document should remain open");

    let response = backend
        .completion(CompletionParams {
            text_document_position: TextDocumentPositionParams {
                text_document: TextDocumentIdentifier { uri },
                position: completion_position,
            },
            work_done_progress_params: WorkDoneProgressParams::default(),
            partial_result_params: PartialResultParams::default(),
            context: None,
        })
        .await
        .expect("completion request should succeed")
        .expect("completion request should return items");

    let CompletionResponse::Array(items) = response else {
        panic!("expected completion item array");
    };
    let item = items
        .iter()
        .find(|item| item.label == "completion_detail_decl")
        .expect("completion should include the live checked declaration");
    assert_eq!(
        item.detail.as_deref(),
        Some(expected_detail.as_str()),
        "completion detail should use the live checked declaration type"
    );
}

#[tokio::test]
async fn test_live_completion_keeps_keyword_matches_when_checked_definitions_match_prefix() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///live-completion-keyword-filter.lean").unwrap();
    let text = "axiom theoremish_decl : Nat\n#check the\n".to_string();

    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text, "lean".to_string()),
    );
    backend.parse_document(&uri).await;
    backend.elaborate_document(&uri).await;

    let completion_position = backend
        .documents
        .get(&uri)
        .map(|doc| {
            let offset = doc
                .text()
                .find("#check the")
                .expect("test text should contain completion prefix")
                + "#check the".len();
            doc.offset_to_position(offset)
        })
        .expect("live checked document should remain open");

    let response = backend
        .completion(CompletionParams {
            text_document_position: TextDocumentPositionParams {
                text_document: TextDocumentIdentifier { uri },
                position: completion_position,
            },
            work_done_progress_params: WorkDoneProgressParams::default(),
            partial_result_params: PartialResultParams::default(),
            context: None,
        })
        .await
        .expect("completion request should succeed")
        .expect("completion request should return items");

    let CompletionResponse::Array(items) = response else {
        panic!("expected completion item array");
    };
    assert!(
        items.iter().any(|item| item.label == "theoremish_decl"
            && item.kind == Some(CompletionItemKind::CONSTANT)),
        "completion should include the live checked declaration matching the prefix"
    );
    assert!(
        items
            .iter()
            .any(|item| item.label == "theorem" && item.kind == Some(CompletionItemKind::KEYWORD)),
        "completion should keep matching keyword items even when checked declarations also match"
    );
}

#[tokio::test]
async fn test_live_signature_help_uses_checked_declaration_type_label() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///live-signature-help.lean").unwrap();
    let text = "axiom sig_help_decl : Nat\n#check sig_help_decl \n".to_string();

    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text, "lean".to_string()),
    );
    backend.parse_document(&uri).await;
    backend.elaborate_document(&uri).await;

    let (signature_position, expected_type) = backend
        .documents
        .get(&uri)
        .map(|doc| {
            let offset = doc
                .text()
                .find("#check sig_help_decl ")
                .expect("test text should contain signature-help call")
                + "#check sig_help_decl ".len();
            let expected_type = doc
                .elaborated
                .as_ref()
                .and_then(|elaborated| {
                    elaborated
                        .declarations
                        .iter()
                        .find(|decl| decl.name == "sig_help_decl")
                })
                .expect("live check should elaborate the signature-help declaration")
                .type_str
                .clone();
            (doc.offset_to_position(offset), expected_type)
        })
        .expect("live checked document should remain open");

    let response = LanguageServer::signature_help(
        backend,
        SignatureHelpParams {
            text_document_position_params: TextDocumentPositionParams {
                text_document: TextDocumentIdentifier { uri },
                position: signature_position,
            },
            work_done_progress_params: WorkDoneProgressParams::default(),
            context: Some(SignatureHelpContext {
                trigger_kind: SignatureHelpTriggerKind::TRIGGER_CHARACTER,
                trigger_character: Some(" ".to_string()),
                is_retrigger: false,
                active_signature_help: None,
            }),
        },
    )
    .await
    .expect("signature-help request should succeed")
    .expect("checked declaration should produce signature help");

    assert_eq!(response.signatures.len(), 1);
    assert_eq!(response.active_signature, Some(0));
    assert_eq!(response.active_parameter, None);
    assert_eq!(
        response.signatures[0].label,
        format!("sig_help_decl : {expected_type}"),
        "signature help should use the live checked declaration type"
    );
    assert_eq!(
        response.signatures[0].parameters, None,
        "initial signature-help slice should not claim parameter parsing"
    );
}

#[tokio::test]
async fn test_live_signature_help_marks_arrow_parameters_and_active_argument() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///live-signature-help-parameters.lean").unwrap();
    let text = "axiom sig_binary : Nat → Nat → Nat\n#check sig_binary 1 \n".to_string();

    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text, "lean".to_string()),
    );
    backend.parse_document(&uri).await;
    backend.elaborate_document(&uri).await;

    let signature_position = backend
        .documents
        .get(&uri)
        .map(|doc| {
            let offset = doc
                .text()
                .find("#check sig_binary 1 ")
                .expect("test text should contain signature-help application")
                + "#check sig_binary 1 ".len();
            assert!(
                doc.elaborated
                    .as_ref()
                    .and_then(|elaborated| {
                        elaborated
                            .declarations
                            .iter()
                            .find(|decl| decl.name == "sig_binary")
                    })
                    .is_some(),
                "live check should elaborate the signature-help declaration"
            );
            doc.offset_to_position(offset)
        })
        .expect("live checked document should remain open");

    let response = LanguageServer::signature_help(
        backend,
        SignatureHelpParams {
            text_document_position_params: TextDocumentPositionParams {
                text_document: TextDocumentIdentifier { uri },
                position: signature_position,
            },
            work_done_progress_params: WorkDoneProgressParams::default(),
            context: Some(SignatureHelpContext {
                trigger_kind: SignatureHelpTriggerKind::TRIGGER_CHARACTER,
                trigger_character: Some(" ".to_string()),
                is_retrigger: false,
                active_signature_help: None,
            }),
        },
    )
    .await
    .expect("signature-help request should succeed")
    .expect("checked declaration application should produce signature help");

    assert_eq!(response.signatures.len(), 1);
    assert_eq!(
        response.signatures[0].label, "sig_binary : Nat → Nat → Nat",
        "signature help should prefer source Lean type text for display while remaining checked-gated"
    );
    assert_eq!(
        response.active_parameter,
        Some(1),
        "one supplied argument should make the second arrow parameter active"
    );
    assert_eq!(
        response.signatures[0].active_parameter,
        Some(1),
        "signature-local active parameter should match the response"
    );

    let parameters = response.signatures[0]
        .parameters
        .as_deref()
        .expect("function signature should expose parameter labels");
    assert!(
        parameters.len() >= 2,
        "function signature should expose at least the two visible Nat parameters"
    );
    for (parameter, expected_label) in parameters.iter().take(2).zip(["Nat", "Nat"]) {
        let ParameterLabel::LabelOffsets([start, end]) = parameter.label else {
            panic!("signature parameter should use offsets into the signature label");
        };
        let parameter_label = response.signatures[0]
            .label
            .get(start as usize..end as usize)
            .expect("parameter offsets should slice the signature label");
        assert_eq!(
            parameter_label, expected_label,
            "parameter label should use the Lean source type instead of checked debug names"
        );
    }
}

#[tokio::test]
async fn test_workspace_symbol_query_returns_matching_declarations() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///workspace-symbol-match.lean").unwrap();
    let text =
        "def alphaHelper := 1\ndef betaHelper := 2\ntheorem alphaTheorem : True := trivial\n"
            .to_string();

    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text, "lean".to_string()),
    );
    backend.parse_document(&uri).await;

    // Case-insensitive substring query: "alpha" matches both `alphaHelper`
    // and `alphaTheorem`, but not `betaHelper`.
    let response = LanguageServer::symbol(
        backend,
        WorkspaceSymbolParams {
            query: "ALPHA".to_string(),
            ..Default::default()
        },
    )
    .await
    .expect("workspace/symbol request should succeed")
    .expect("matching query should produce workspace symbols");

    let names: Vec<&str> = response.iter().map(|sym| sym.name.as_str()).collect();
    assert!(
        names.contains(&"alphaHelper"),
        "case-insensitive query should match `alphaHelper`, got {names:?}"
    );
    assert!(
        names.contains(&"alphaTheorem"),
        "case-insensitive query should match `alphaTheorem`, got {names:?}"
    );
    assert!(
        !names.contains(&"betaHelper"),
        "query `alpha` should not match `betaHelper`, got {names:?}"
    );

    // Each returned symbol must point back into the indexed document.
    for sym in &response {
        assert_eq!(
            sym.location.uri, uri,
            "workspace symbol should locate the declaration in its source document"
        );
    }

    // Results are sorted by name for stable client rendering.
    let mut sorted = names.clone();
    sorted.sort_unstable();
    assert_eq!(names, sorted, "workspace symbols should be name-sorted");
}

#[tokio::test]
async fn test_workspace_symbol_no_match_query_returns_none() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///workspace-symbol-no-match.lean").unwrap();
    let text = "def onlyDecl := 1\n".to_string();

    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text, "lean".to_string()),
    );
    backend.parse_document(&uri).await;

    let response = LanguageServer::symbol(
        backend,
        WorkspaceSymbolParams {
            query: "no_such_symbol_anywhere".to_string(),
            ..Default::default()
        },
    )
    .await
    .expect("workspace/symbol request should succeed");

    assert!(
        response.is_none(),
        "a query with no substring match should yield no workspace symbols"
    );
}

#[tokio::test]
async fn test_workspace_symbol_empty_query_returns_all_indexed_declarations() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///workspace-symbol-empty-query.lean").unwrap();
    let text = "def first := 1\ndef second := 2\n".to_string();

    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text, "lean".to_string()),
    );
    backend.parse_document(&uri).await;

    let response = LanguageServer::symbol(
        backend,
        WorkspaceSymbolParams {
            query: String::new(),
            ..Default::default()
        },
    )
    .await
    .expect("workspace/symbol request should succeed")
    .expect("empty query should return every indexed declaration");

    let names: Vec<&str> = response.iter().map(|sym| sym.name.as_str()).collect();
    assert!(
        names.contains(&"first") && names.contains(&"second"),
        "empty query should surface all indexed declarations, got {names:?}"
    );
}

#[tokio::test]
async fn test_workspace_symbol_garbage_query_does_not_panic() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///workspace-symbol-garbage.lean").unwrap();
    // Document body is itself unparseable garbage; the index should simply be
    // empty rather than producing spurious symbols or panicking.
    let text = "@@@ ??? \u{1f600} ::: not lean at all\n".to_string();

    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text, "lean".to_string()),
    );
    backend.parse_document(&uri).await;

    // Query is also garbage including a non-ASCII / control-ish payload. The
    // case-insensitive substring search must tolerate any UTF-8 input.
    let response = LanguageServer::symbol(
        backend,
        WorkspaceSymbolParams {
            query: "@@@\u{1f600}\u{0}\\(*&^%".to_string(),
            ..Default::default()
        },
    )
    .await
    .expect("workspace/symbol request should not error on garbage input");

    assert!(
        response.is_none(),
        "garbage query against a garbage document should yield no symbols"
    );
}

#[tokio::test]
async fn test_workspace_symbol_no_open_documents_returns_none() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();

    let response = LanguageServer::symbol(
        backend,
        WorkspaceSymbolParams {
            query: "anything".to_string(),
            ..Default::default()
        },
    )
    .await
    .expect("workspace/symbol request should succeed with no documents");

    assert!(
        response.is_none(),
        "no open documents means no workspace symbols"
    );
}

#[tokio::test]
async fn test_signature_help_outside_call_site_returns_none() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///signature-help-no-call.lean").unwrap();
    // Cursor sits on the declaration keyword line, not after a known callable
    // identifier, so there is no signature context to resolve.
    let text = "axiom lone_decl : Nat\n".to_string();

    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text, "lean".to_string()),
    );
    backend.parse_document(&uri).await;
    backend.elaborate_document(&uri).await;

    let response = LanguageServer::signature_help(
        backend,
        SignatureHelpParams {
            text_document_position_params: TextDocumentPositionParams {
                text_document: TextDocumentIdentifier { uri },
                position: Position::new(0, 0),
            },
            work_done_progress_params: WorkDoneProgressParams::default(),
            context: Some(SignatureHelpContext {
                trigger_kind: SignatureHelpTriggerKind::INVOKED,
                trigger_character: None,
                is_retrigger: false,
                active_signature_help: None,
            }),
        },
    )
    .await
    .expect("signature-help request should succeed");

    assert!(
        response.is_none(),
        "cursor at the start of a declaration is not a call site and should produce no signature help"
    );
}

#[tokio::test]
async fn test_signature_help_garbage_document_does_not_panic() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///signature-help-garbage.lean").unwrap();
    let text = "%%% \u{1f4a9} not a real call ((( \n".to_string();

    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text.clone(), "lean".to_string()),
    );
    backend.parse_document(&uri).await;
    backend.elaborate_document(&uri).await;

    // Position the cursor at the far end of the garbage line; the call-context
    // scanner should find no known callable and return None without panicking.
    let position = backend
        .documents
        .get(&uri)
        .map(|doc| doc.offset_to_position(text.len()))
        .expect("garbage document should remain open");

    let response = LanguageServer::signature_help(
        backend,
        SignatureHelpParams {
            text_document_position_params: TextDocumentPositionParams {
                text_document: TextDocumentIdentifier { uri },
                position,
            },
            work_done_progress_params: WorkDoneProgressParams::default(),
            context: Some(SignatureHelpContext {
                trigger_kind: SignatureHelpTriggerKind::TRIGGER_CHARACTER,
                trigger_character: Some(" ".to_string()),
                is_retrigger: false,
                active_signature_help: None,
            }),
        },
    )
    .await
    .expect("signature-help request should not error on garbage input");

    assert!(
        response.is_none(),
        "garbage document with no known callables should yield no signature help"
    );
}

#[tokio::test]
async fn test_signature_help_unknown_document_returns_none() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    // No document was ever opened under this URI.
    let uri = Url::parse("file:///signature-help-missing.lean").unwrap();

    let response = LanguageServer::signature_help(
        backend,
        SignatureHelpParams {
            text_document_position_params: TextDocumentPositionParams {
                text_document: TextDocumentIdentifier { uri },
                position: Position::new(3, 7),
            },
            work_done_progress_params: WorkDoneProgressParams::default(),
            context: Some(SignatureHelpContext {
                trigger_kind: SignatureHelpTriggerKind::INVOKED,
                trigger_character: None,
                is_retrigger: false,
                active_signature_help: None,
            }),
        },
    )
    .await
    .expect("signature-help request should succeed for an unknown document");

    assert!(
        response.is_none(),
        "an unopened document should produce no signature help"
    );
}

#[tokio::test]
async fn test_live_references_exclude_checked_declaration_when_requested() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///live-reference-ranges.lean").unwrap();
    let text = "axiom ref_decl : Nat\n#check ref_decl\n#check ref_decl\n".to_string();

    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text.clone(), "lean".to_string()),
    );
    backend.parse_document(&uri).await;
    backend.elaborate_document(&uri).await;

    let doc = backend
        .documents
        .get(&uri)
        .expect("live checked document should remain open");
    let decl_name_start = text
        .find("ref_decl")
        .expect("test text should contain the declaration name");
    let first_use = text
        .find("#check ref_decl")
        .expect("test text should contain first reference")
        + "#check ".len();
    let second_use = text
        .rfind("#check ref_decl")
        .expect("test text should contain second reference")
        + "#check ".len();
    let expected_use_ranges = [
        Range {
            start: doc.offset_to_position(first_use),
            end: doc.offset_to_position(first_use + "ref_decl".len()),
        },
        Range {
            start: doc.offset_to_position(second_use),
            end: doc.offset_to_position(second_use + "ref_decl".len()),
        },
    ];
    drop(doc);

    let def_info = backend
        .definitions
        .get("ref_decl")
        .expect("parse_document should index the declaration");
    assert_eq!(
        def_info.name_start, decl_name_start,
        "definition index should record the identifier span, not just the command span"
    );
    assert_eq!(def_info.name_end, decl_name_start + "ref_decl".len());
    drop(def_info);

    let references = backend.find_references("ref_decl", false);
    assert_eq!(
        references.len(),
        2,
        "references without declaration should return only checked-document uses"
    );
    for (reference, expected_range) in references.iter().zip(expected_use_ranges) {
        assert_eq!(reference.uri, uri);
        assert_eq!(
            reference.range, expected_range,
            "reference range should match the checked-document identifier use"
        );
    }

    let references_with_definition = backend.find_references("ref_decl", true);
    assert_eq!(
        references_with_definition.len(),
        3,
        "references with declaration should include the declaration plus both uses"
    );
}

/// RENAME MUST NOT EDIT COMMENTS OR STRING LITERALS.
///
/// `find_references` was a raw `text.find` scan with identifier-boundary
/// checks and nothing else, and `create_rename_edits` turns every occurrence it
/// returns into a `TextEdit`. So `rename` rewrote the name inside
/// `-- ren_decl is the interesting one` and inside `"ren_decl"` — a silent edit
/// to text the user never meant to touch, and the one failure mode of rename
/// that a user cannot undo by reading the diff, because it looks correct.
///
/// This pins all four positions at once: code (must rename), line comment,
/// block comment and string literal (must not). It is written against
/// `create_rename_edits` rather than only `find_references` because the edit
/// list is what actually reaches the user's file.
#[tokio::test]
async fn test_rename_does_not_edit_comments_or_string_literals() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///rename-masking.lean").unwrap();
    let text = concat!(
        "axiom ren_decl : Nat\n",
        "-- ren_decl is the interesting one\n",
        "/- ren_decl again, /- nested -/ still commented ren_decl -/\n",
        "def s : String := \"ren_decl\"\n",
        "#check ren_decl\n",
    )
    .to_string();

    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text.clone(), "lean".to_string()),
    );
    backend.parse_document(&uri).await;
    backend.elaborate_document(&uri).await;

    // Six occurrences in the text; exactly two are code — the declaration and
    // the `#check`. If this ever reads 6, the mask is not being consulted.
    assert_eq!(
        text.matches("ren_decl").count(),
        6,
        "the fixture must carry four non-code occurrences, or it tests nothing"
    );

    let references = backend.find_references("ren_decl", true);
    assert_eq!(
        references.len(),
        2,
        "find_references returned a comment or string occurrence: {references:#?}"
    );

    let edit = backend.create_rename_edits("ren_decl", "renamed");
    let changes = edit.changes.expect("rename must produce changes");
    let edits = changes.get(&uri).expect("edits for the open document");
    assert_eq!(
        edits.len(),
        2,
        "rename would have rewritten a comment or a string literal: {edits:#?}"
    );

    // And it really does rename the two it should: apply the edits by offset,
    // highest first, and check the result.
    let doc = backend.documents.get(&uri).expect("document stays open");
    let mut offsets: Vec<usize> = edits
        .iter()
        .map(|e| doc.position_to_offset(e.range.start))
        .collect();
    drop(doc);
    offsets.sort_unstable();
    let mut renamed = text.clone();
    for at in offsets.into_iter().rev() {
        renamed.replace_range(at..at + "ren_decl".len(), "renamed");
    }
    assert!(
        renamed.starts_with("axiom renamed : Nat"),
        "the declaration was not renamed: {renamed}"
    );
    assert!(
        renamed.contains("#check renamed"),
        "the use was not renamed: {renamed}"
    );
    assert!(
        renamed.contains("-- ren_decl is the interesting one"),
        "the line comment was edited: {renamed}"
    );
    assert!(
        renamed.contains("still commented ren_decl -/"),
        "the nested block comment was edited: {renamed}"
    );
    assert!(
        renamed.contains("\"ren_decl\""),
        "the string literal was edited: {renamed}"
    );
}

/// `prepareRename` must refuse a position inside a comment or a string.
///
/// The three surfaces have to agree. Once `create_rename_edits` stops
/// producing an edit for a commented occurrence, a `prepareRename` that still
/// said "yes" would offer a rename that then does nothing at the position the
/// user was pointing at — which reads as a broken editor, not as a refusal.
#[tokio::test]
async fn test_prepare_rename_refuses_inside_a_comment_or_string() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///prepare-rename-masking.lean").unwrap();
    let text = concat!(
        "axiom ren_decl : Nat\n",
        "-- ren_decl in a comment\n",
        "def s : String := \"ren_decl\"\n",
    )
    .to_string();

    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text.clone(), "lean".to_string()),
    );
    backend.parse_document(&uri).await;

    let doc = backend.documents.get(&uri).expect("document stays open");
    let at = |needle: &str, skip: usize| -> Position {
        let mut from = 0usize;
        for _ in 0..skip {
            from = text[from..].find(needle).expect("occurrence") + from + 1;
        }
        let off = text[from..].find(needle).expect("occurrence") + from;
        doc.offset_to_position(off + 1)
    };
    let in_code = at("ren_decl", 0);
    let in_comment = at("ren_decl", 1);
    let in_string = at("ren_decl", 2);
    drop(doc);

    assert!(
        backend.prepare_rename_at(&uri, in_code).is_some(),
        "the declaration itself must still be renameable"
    );
    assert!(
        backend.prepare_rename_at(&uri, in_comment).is_none(),
        "prepareRename offered a rename anchored in a line comment"
    );
    assert!(
        backend.prepare_rename_at(&uri, in_string).is_none(),
        "prepareRename offered a rename anchored in a string literal"
    );
}

/// `documentHighlight` is document-local, and stays that way after the scan was
/// split out of `find_references`.
///
/// It used to reach this result by scanning EVERY open document and filtering
/// the answers down to one URI — wasteful before the code mask and worse after
/// it, since each document now also gets a mask built and thrown away. The scan
/// is now per-document; this pins the behaviour that refactor must not change,
/// with a second open document carrying the same identifier so a regression to
/// the workspace-wide scan is visible rather than silent.
#[tokio::test]
async fn test_document_highlights_do_not_leak_across_documents() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();

    let here = Url::parse("file:///highlight-here.lean").unwrap();
    let there = Url::parse("file:///highlight-there.lean").unwrap();
    let text_here = "axiom hl_decl : Nat\n#check hl_decl\n".to_string();
    let text_there = "#check hl_decl\n#check hl_decl\n".to_string();

    backend.documents.insert(
        here.clone(),
        Document::new(here.clone(), 1, text_here.clone(), "lean".to_string()),
    );
    backend.documents.insert(
        there.clone(),
        Document::new(there.clone(), 1, text_there, "lean".to_string()),
    );
    backend.parse_document(&here).await;
    backend.parse_document(&there).await;

    let doc = backend.documents.get(&here).expect("document stays open");
    let at = doc.offset_to_position(text_here.find("hl_decl").expect("the declaration") + 1);
    drop(doc);

    let highlights = backend
        .document_highlights_at(&here, at)
        .expect("the identifier under the cursor has occurrences");
    assert_eq!(
        highlights.len(),
        2,
        "documentHighlight returned occurrences from another document: {highlights:#?}"
    );

    // And the cross-document view is still the one that sees all four.
    assert_eq!(
        backend.find_references("hl_decl", true).len(),
        4,
        "find_references must still be workspace-wide"
    );
}

#[tokio::test]
async fn test_live_references_find_open_document_use_across_files() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let decl_uri = Url::parse("file:///live-reference-decl.lean").unwrap();
    let use_uri = Url::parse("file:///live-reference-use.lean").unwrap();
    let decl_text = "axiom cross_decl : Nat\n".to_string();
    let use_text = "#check cross_decl\n".to_string();

    backend.documents.insert(
        decl_uri.clone(),
        Document::new(decl_uri.clone(), 1, decl_text, "lean".to_string()),
    );
    backend.documents.insert(
        use_uri.clone(),
        Document::new(use_uri.clone(), 1, use_text.clone(), "lean".to_string()),
    );
    backend.parse_document(&decl_uri).await;
    backend.elaborate_document(&decl_uri).await;
    backend.parse_document(&use_uri).await;
    backend.elaborate_document(&use_uri).await;

    let expected_use_range = {
        let doc = backend
            .documents
            .get(&use_uri)
            .expect("live checked use document should remain open");
        let use_offset = use_text
            .find("cross_decl")
            .expect("test text should contain cross-file use");
        Range {
            start: doc.offset_to_position(use_offset),
            end: doc.offset_to_position(use_offset + "cross_decl".len()),
        }
    };

    let references = backend.find_references("cross_decl", false);
    assert_eq!(
        references,
        vec![Location {
            uri: use_uri.clone(),
            range: expected_use_range,
        }],
        "cross-file references without declaration should return the open-document use"
    );

    let mut references_with_definition = backend.find_references("cross_decl", true);
    references_with_definition.sort_by(|left, right| {
        left.uri
            .as_str()
            .cmp(right.uri.as_str())
            .then(left.range.start.line.cmp(&right.range.start.line))
            .then(left.range.start.character.cmp(&right.range.start.character))
    });
    assert_eq!(
        references_with_definition.len(),
        2,
        "cross-file references with declaration should include declaration and use"
    );
    assert_eq!(references_with_definition[0].uri, decl_uri);
    assert_eq!(references_with_definition[1].uri, use_uri);
}

#[test]
fn test_plain_term_goal_does_not_substitute_decl_type_for_missing_term_capture() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///plain-term-goal.lean").unwrap();
    let text = "def answer : Nat := 42\n\n#check answer\n".to_string();
    let mut doc = Document::new(uri.clone(), 1, text, "lean".to_string());
    doc.elaborated = Some(ElaboratedDocument {
        errors: vec![],
        warnings: vec![],
        declarations: vec![ElaboratedDecl {
            identity: clean_kernel::Name::anon().str("answer"),
            name: "answer".to_string(),
            type_str: "Nat".to_string(),
            start: 0,
            end: "def answer : Nat := 42".len(),
        }],
        term_infos: Vec::new(),
        holes: vec![],
        widget_modules: vec![],
    });

    backend.documents.insert(uri.clone(), doc);

    let inside_decl = backend.plain_term_goal(crate::rpc::PlainTermGoalParams {
        text_document: crate::rpc::TextDocumentIdentifier { uri: uri.clone() },
        position: Position::new(0, 4),
    });
    assert!(
        inside_decl.is_none(),
        "a declaration type is not a captured term-local expected type"
    );
    assert_eq!(
        backend
            .documents
            .get(&uri)
            .unwrap()
            .elaborated
            .as_ref()
            .unwrap()
            .declarations[0]
            .type_str,
        "Nat",
        "declaration metadata remains available to its existing consumers"
    );

    let outside_decl = backend.plain_term_goal(crate::rpc::PlainTermGoalParams {
        text_document: crate::rpc::TextDocumentIdentifier { uri },
        position: Position::new(2, 0),
    });
    assert!(
        outside_decl.is_none(),
        "a position without captured term-goal metadata returns null"
    );

    let end_boundary = backend.plain_term_goal(crate::rpc::PlainTermGoalParams {
        text_document: crate::rpc::TextDocumentIdentifier {
            uri: Url::parse("file:///plain-term-goal.lean").unwrap(),
        },
        position: Position::new(0, "def answer : Nat := 42".len() as u32),
    });
    assert!(
        end_boundary.is_none(),
        "a declaration end does not supply term-goal metadata"
    );
}

#[tokio::test]
async fn test_plain_term_goal_live_checked_decl_without_term_capture_returns_none() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///live-plain-term-goal.lean").unwrap();
    let text = "axiom live_answer : Nat\n".to_string();

    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text, "lean".to_string()),
    );
    backend.parse_document(&uri).await;
    backend.elaborate_document(&uri).await;

    let elaborated = backend
        .documents
        .get(&uri)
        .and_then(|doc| doc.elaborated.clone())
        .expect("live check should store elaboration state");
    assert!(
        elaborated.errors.is_empty(),
        "live check should not produce type errors, got {:?}",
        elaborated.errors
    );
    assert!(
        !elaborated.declarations.is_empty(),
        "live check should produce elaborated declarations"
    );
    let expected_type = elaborated.declarations[0].type_str.clone();

    let response = backend.plain_term_goal(crate::rpc::PlainTermGoalParams {
        text_document: crate::rpc::TextDocumentIdentifier { uri },
        position: Position::new(0, 4),
    });

    assert!(
        !expected_type.is_empty(),
        "checked declaration metadata is retained"
    );
    assert!(
        response.is_none(),
        "a checked declaration type alone does not supply term-goal metadata"
    );
}

#[tokio::test]
async fn test_plain_term_goal_live_checked_document_stays_declaration_range_only() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///live-plain-term-goal-boundary.lean").unwrap();
    let text = "axiom live_answer : Nat\n\n".to_string();

    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text, "lean".to_string()),
    );
    backend.parse_document(&uri).await;
    backend.elaborate_document(&uri).await;

    let elaborated = backend
        .documents
        .get(&uri)
        .and_then(|doc| doc.elaborated.clone())
        .expect("live check should store elaboration state");
    assert!(
        elaborated.errors.is_empty(),
        "live check should not produce type errors, got {:?}",
        elaborated.errors
    );
    assert!(
        !elaborated.declarations.is_empty(),
        "live check should produce elaborated declarations"
    );

    let response = backend.plain_term_goal(crate::rpc::PlainTermGoalParams {
        text_document: crate::rpc::TextDocumentIdentifier { uri },
        position: Position::new(1, 0),
    });

    assert!(
        response.is_none(),
        "plainTermGoal should not reuse live declaration type evidence outside declaration ranges"
    );
}

#[test]
fn test_has_live_hole_expected_type_state_false_without_holes() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();

    // No open documents: nothing has recorded a hole context.
    assert!(
        !backend.has_live_hole_expected_type_state(),
        "hole-state predicate must be false when no document has recorded holes"
    );

    // A document with elaboration but no holes also reports false.
    let uri = Url::parse("file:///no-holes.lean").unwrap();
    let mut doc = Document::new(
        uri.clone(),
        1,
        "def x : Nat := 1\n".to_string(),
        "lean".to_string(),
    );
    doc.elaborated = Some(ElaboratedDocument {
        errors: vec![],
        warnings: vec![],
        declarations: vec![ElaboratedDecl {
            identity: clean_kernel::Name::anon().str("x"),
            name: "x".to_string(),
            type_str: "Nat".to_string(),
            start: 0,
            end: "def x : Nat := 1".len(),
        }],
        term_infos: Vec::new(),
        holes: vec![],
        widget_modules: vec![],
    });
    backend.documents.insert(uri, doc);
    assert!(
        !backend.has_live_hole_expected_type_state(),
        "hole-state predicate must stay false when elaboration recorded an empty holes list"
    );
}

#[tokio::test]
async fn test_goto_declaration_resolves_identifier_to_declaration_location() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///goto-declaration.lean").unwrap();
    // Reference `goto_decl` on the `#check` line; declaration sits on line 0.
    let text = "axiom goto_decl : Nat\n#check goto_decl\n".to_string();

    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text, "lean".to_string()),
    );
    backend.parse_document(&uri).await;
    backend.elaborate_document(&uri).await;

    // Declaration ≈ definition for Lean decls, so go-to-declaration must
    // resolve to the same location the definition index records.
    let (def_uri, def_range) = backend
        .find_definition("goto_decl")
        .expect("definition index should resolve the declaration");

    // Cursor on the `goto_decl` reference at line 1, column 7 (`#check `).
    let params = GotoDefinitionParams {
        text_document_position_params: TextDocumentPositionParams {
            text_document: TextDocumentIdentifier { uri: uri.clone() },
            position: Position::new(1, 7),
        },
        work_done_progress_params: WorkDoneProgressParams::default(),
        partial_result_params: PartialResultParams::default(),
    };

    let response = backend
        .goto_declaration(params)
        .await
        .expect("goto_declaration must not error");

    match response {
        Some(GotoDefinitionResponse::Scalar(location)) => {
            assert_eq!(
                location.uri, def_uri,
                "declaration should point at the decl's document"
            );
            assert_eq!(
                location.range, def_range,
                "declaration location should match the definition index range"
            );
        }
        other => panic!("expected a scalar declaration location, got {other:?}"),
    }
}

#[tokio::test]
async fn test_goto_declaration_unknown_identifier_returns_none() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///goto-declaration-none.lean").unwrap();
    // Position 0,0 is whitespace-only: no identifier under the cursor.
    let text = " \n".to_string();

    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text, "lean".to_string()),
    );

    let params = GotoDefinitionParams {
        text_document_position_params: TextDocumentPositionParams {
            text_document: TextDocumentIdentifier { uri },
            position: Position::new(0, 0),
        },
        work_done_progress_params: WorkDoneProgressParams::default(),
        partial_result_params: PartialResultParams::default(),
    };

    let response = backend
        .goto_declaration(params)
        .await
        .expect("goto_declaration must not error");
    assert!(
        response.is_none(),
        "go-to-declaration on a non-identifier position should resolve to nothing"
    );
}

#[tokio::test]
async fn test_plain_term_goal_reports_hole_local_expected_type_for_body_hole() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///hole-term-goal.lean").unwrap();
    // The body underscore records a genuine elaborator context.
    let text = "def answer : Nat := _\n".to_string();

    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text.clone(), "lean".to_string()),
    );
    backend.parse_document(&uri).await;
    backend.elaborate_document(&uri).await;

    let elaborated = backend
        .documents
        .get(&uri)
        .and_then(|doc| doc.elaborated.clone())
        .expect("live check should store elaboration state");
    assert_eq!(
        elaborated.holes.len(),
        1,
        "a body underscore should record exactly one hole context, got {:?}",
        elaborated.holes
    );
    let recorded = &elaborated.holes[0];
    let hole_offset = text.find('_').expect("text contains the hole token");
    assert_eq!(
        recorded.start, hole_offset,
        "hole start should be the underscore token offset"
    );

    assert!(
        backend.has_live_hole_expected_type_state(),
        "predicate must flip true once a hole context is recorded"
    );

    // Capture remains available when the unfilled hole prevents registration.
    // Its expected type and token range are independent of declaration metadata.
    assert_eq!(recorded.expected_type, "Nat");
    assert_eq!((recorded.start, recorded.end), (20, 21));
    let on_hole = backend.plain_term_goal(crate::rpc::PlainTermGoalParams {
        text_document: crate::rpc::TextDocumentIdentifier { uri: uri.clone() },
        position: backend
            .documents
            .get(&uri)
            .map(|doc| doc.offset_to_position(hole_offset))
            .expect("document open"),
    });
    let response = on_hole.expect("the captured body hole supplies a goal");
    assert_eq!(response.goal, "⊢ Nat");
    assert_eq!(response.range.start, Position::new(0, 20));
    assert_eq!(response.range.end, Position::new(0, 21));
}

#[tokio::test]
async fn test_plain_term_goal_reports_subterm_hole_expected_type() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///subterm-hole.lean").unwrap();
    // A NESTED / sub-term hole: the `_` is ascribed to `Nat` inside a larger
    // term `(_ : Nat)`. The hole-local goal is the sub-term type `Nat`,
    // recovered from the elaborator even though the unfilled hole makes the
    // declaration fail kernel registration (the LSP re-elaborates without
    // registration to recover it). The recorded hole span is the narrow `_`
    // token, distinct from the whole-declaration range.
    let text = "def answer : Nat := (_ : Nat)\n".to_string();

    // Initialize Nat in the shared environment so the ascription type resolves
    // to a concrete `Nat` constant (rather than a bare-env auto-implicit FVar),
    // making the recovered sub-term goal observably `Nat`.
    backend
        .env
        .write()
        .await
        .init_nat()
        .expect("Nat should initialize");

    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text.clone(), "lean".to_string()),
    );
    backend.parse_document(&uri).await;
    backend.elaborate_document(&uri).await;

    let elaborated = backend
        .documents
        .get(&uri)
        .and_then(|doc| doc.elaborated.clone())
        .expect("live check should store elaboration state");

    // The sub-term hole is recorded with a narrow span at the `_` token, not at
    // the whole declaration.
    assert_eq!(
        elaborated.holes.len(),
        1,
        "the nested `_` hole should record exactly one hole context, got {:?}",
        elaborated.holes
    );
    let hole_offset = text.find('_').expect("text contains the hole token");
    let recorded = &elaborated.holes[0];
    assert_eq!(
        recorded.start, hole_offset,
        "hole start should be the `_` token offset (sub-term, not whole decl)"
    );
    assert!(
        backend.has_live_hole_expected_type_state(),
        "predicate must flip true once a sub-term hole context is recorded"
    );

    // plainTermGoal on the hole reports the sub-term expected type `Nat`.
    let on_hole = backend.plain_term_goal(crate::rpc::PlainTermGoalParams {
        text_document: crate::rpc::TextDocumentIdentifier { uri: uri.clone() },
        position: backend
            .documents
            .get(&uri)
            .map(|doc| doc.offset_to_position(hole_offset))
            .expect("document open"),
    });
    let goal = on_hole
        .expect("plainTermGoal on the sub-term hole should report a goal")
        .goal;
    assert!(
        goal.contains("Nat"),
        "sub-term hole goal should resolve to Nat, got {goal}"
    );
}

#[tokio::test]
async fn test_plain_term_goal_no_hole_decl_records_no_hole_context() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///no-hole-decl.lean").unwrap();
    // A declaration with no user-written `_` hole records no hole contexts.
    let text = "def answer : Nat := 42\n".to_string();

    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text, "lean".to_string()),
    );
    backend.parse_document(&uri).await;
    backend.elaborate_document(&uri).await;

    let elaborated = backend
        .documents
        .get(&uri)
        .and_then(|doc| doc.elaborated.clone())
        .expect("live check should store elaboration state");
    assert!(
        elaborated.holes.is_empty(),
        "a hole-free declaration must record no hole contexts, got {:?}",
        elaborated.holes
    );
    assert!(
        !backend.has_live_hole_expected_type_state(),
        "hole-state predicate must stay false for a hole-free declaration"
    );
}

#[tokio::test]
async fn test_plain_term_goal_body_hole_under_binder_shows_local_context() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///hole-under-binder.lean").unwrap();
    // A body hole under a binder: `n : Nat` is in scope at the hole, so the
    // hole-local goal should surface the hypothesis above the turnstile
    // (Lean infoview local-context style) followed by the expected type.
    let text = "def f (n : Nat) : Nat := _\n".to_string();

    backend
        .env
        .write()
        .await
        .init_nat()
        .expect("Nat should initialize");

    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text.clone(), "lean".to_string()),
    );
    backend.parse_document(&uri).await;
    backend.elaborate_document(&uri).await;

    let elaborated = backend
        .documents
        .get(&uri)
        .and_then(|doc| doc.elaborated.clone())
        .expect("live check should store elaboration state");
    assert_eq!(
        elaborated.holes.len(),
        1,
        "a body hole under a binder records exactly one hole context, got {:?}",
        elaborated.holes
    );
    // The captured local binding `n : Nat` is surfaced on the hole context.
    let recorded = &elaborated.holes[0];
    assert_eq!(
        recorded.local_bindings.len(),
        1,
        "the in-scope binder `n` should be captured as a local binding, got {:?}",
        recorded.local_bindings
    );
    assert_eq!(recorded.local_bindings[0].0, "n", "binding name is `n`");
    assert!(
        recorded.local_bindings[0].1.contains("Nat"),
        "binding type should resolve to Nat, got {}",
        recorded.local_bindings[0].1
    );

    let hole_offset = text.rfind('_').expect("text contains the hole token");
    let on_hole = backend.plain_term_goal(crate::rpc::PlainTermGoalParams {
        text_document: crate::rpc::TextDocumentIdentifier { uri: uri.clone() },
        position: backend
            .documents
            .get(&uri)
            .map(|doc| doc.offset_to_position(hole_offset))
            .expect("document open"),
    });
    let goal = on_hole
        .expect("plainTermGoal on the hole under a binder should report a goal")
        .goal;
    // The goal renders the local hypothesis above the turnstile, then the
    // expected type after it (Lean infoview block).
    assert!(
        goal.contains("n : "),
        "goal should list the hypothesis `n : <type>` in the local context, got {goal}"
    );
    assert!(
        goal.contains('⊢'),
        "goal with a local context should include the turnstile, got {goal}"
    );
    let (ctx, target) = goal
        .split_once('⊢')
        .expect("goal with a local context has a turnstile separator");
    assert!(
        ctx.contains("n : "),
        "the hypothesis must appear above the turnstile, got {goal}"
    );
    assert!(
        target.contains("Nat"),
        "the expected type must appear after the turnstile, got {goal}"
    );
}

#[tokio::test]
async fn test_plain_term_goal_no_binder_hole_omits_local_context_block() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///hole-no-binder.lean").unwrap();
    // Lean's plain term goal keeps the turnstile with no local hypotheses.
    let text = "def answer : Nat := _\n".to_string();

    backend
        .env
        .write()
        .await
        .init_nat()
        .expect("Nat should initialize");

    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text.clone(), "lean".to_string()),
    );
    backend.parse_document(&uri).await;
    backend.elaborate_document(&uri).await;

    let elaborated = backend
        .documents
        .get(&uri)
        .and_then(|doc| doc.elaborated.clone())
        .expect("live check should store elaboration state");
    assert_eq!(
        elaborated.holes.len(),
        1,
        "the body hole records exactly one hole context, got {:?}",
        elaborated.holes
    );
    assert!(
        elaborated.holes[0].local_bindings.is_empty(),
        "a hole with no binders in scope captures no local bindings, got {:?}",
        elaborated.holes[0].local_bindings
    );

    let hole_offset = text.rfind('_').expect("text contains the hole token");
    let on_hole = backend.plain_term_goal(crate::rpc::PlainTermGoalParams {
        text_document: crate::rpc::TextDocumentIdentifier { uri: uri.clone() },
        position: backend
            .documents
            .get(&uri)
            .map(|doc| doc.offset_to_position(hole_offset))
            .expect("document open"),
    });
    let goal = on_hole
        .expect("plainTermGoal on the no-binder hole should report a goal")
        .goal;
    assert_eq!(goal, "⊢ Nat", "the empty context still has a goal prefix");
}

#[test]
fn test_format_hole_goal_with_and_without_local_context() {
    use crate::document::HoleContext;
    // No bindings: Lean still includes the goal prefix.
    let bare = HoleContext {
        start: 0,
        end: 1,
        expected_type: "Nat".to_string(),
        local_bindings: vec![],
    };
    assert_eq!(format_hole_goal(&bare), "⊢ Nat");

    // With bindings: Lean infoview-style block with the turnstile.
    let with_ctx = HoleContext {
        start: 0,
        end: 1,
        expected_type: "Q".to_string(),
        local_bindings: vec![
            ("n".to_string(), "Nat".to_string()),
            ("h".to_string(), "P".to_string()),
        ],
    };
    assert_eq!(
        format_hole_goal(&with_ctx),
        "n : Nat\nh : P\n⊢ Q",
        "the local context must precede the turnstile, one hypothesis per line"
    );
}

#[test]
fn test_hole_expected_type_prefers_narrowest_overlapping_hole() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///nested-holes.lean").unwrap();
    let text = "def f : Nat := _\n".to_string();
    let mut doc = Document::new(uri.clone(), 1, text, "lean".to_string());
    // Two overlapping holes: a wide outer one and a narrow inner one. The
    // narrowest matching span should win at the overlap point.
    doc.elaborated = Some(ElaboratedDocument {
        errors: vec![],
        warnings: vec![],
        declarations: vec![],
        term_infos: Vec::new(),
        holes: vec![
            crate::document::HoleContext {
                start: 10,
                end: 16,
                expected_type: "OUTER".to_string(),
                local_bindings: vec![],
            },
            crate::document::HoleContext {
                start: 14,
                end: 16,
                expected_type: "INNER".to_string(),
                local_bindings: vec![],
            },
        ],
        widget_modules: vec![],
    });
    backend.documents.insert(uri.clone(), doc.clone());

    let doc_ref = backend.documents.get(&uri).expect("document open");
    // Offset 15 lies inside both holes; the inner (narrower) one wins.
    let inner = backend.hole_context_at_position(&doc_ref, doc.offset_to_position(15));
    assert_eq!(inner.map(|hole| hole.expected_type.as_str()), Some("INNER"));
    // Offset 11 lies only inside the outer hole.
    let outer = backend.hole_context_at_position(&doc_ref, doc.offset_to_position(11));
    assert_eq!(outer.map(|hole| hole.expected_type.as_str()), Some("OUTER"));
    // Lean's includeStop also selects the narrowest term at its end.
    let end = backend.hole_context_at_position(&doc_ref, doc.offset_to_position(16));
    assert_eq!(end.map(|hole| hole.expected_type.as_str()), Some("INNER"));
    let none = backend.hole_context_at_position(&doc_ref, doc.offset_to_position(17));
    assert!(
        none.is_none(),
        "a point beyond both recorded terms has no captured goal"
    );
}

#[test]
fn test_rpc_get_widgets_uses_elaborated_declaration_panel() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///declaration-panel.lean").unwrap();
    let text = "def answer : Nat := 42\n".to_string();
    let mut doc = Document::new(uri.clone(), 7, text, "lean".to_string());
    doc.elaborated = Some(ElaboratedDocument {
        errors: vec![],
        warnings: vec![],
        declarations: vec![ElaboratedDecl {
            identity: clean_kernel::Name::anon().str("answer"),
            name: "answer".to_string(),
            type_str: "Nat".to_string(),
            start: 0,
            end: "def answer : Nat := 42".len(),
        }],
        term_infos: Vec::new(),
        holes: vec![],
        widget_modules: vec![],
    });
    backend.documents.insert(uri.clone(), doc);

    let connected = backend
        .rpc_connect(crate::rpc::RpcConnectParams { uri: uri.clone() })
        .unwrap();

    let widgets_value = backend
        .rpc_call(crate::rpc::RpcCallParams {
            text_document: crate::rpc::TextDocumentIdentifier { uri: uri.clone() },
            position: Position::new(0, 4),
            session_id: connected.session_id,
            method: "Lean.Widget.getWidgets".to_string(),
            params: serde_json::Value::Null,
        })
        .unwrap();
    let widgets: crate::rpc::GetWidgetsResponse = serde_json::from_value(widgets_value).unwrap();
    assert_eq!(widgets.widgets.len(), 2);
    let declaration_panel = widgets
        .widgets
        .iter()
        .find(|widget| widget.id == DECLARATION_PANEL_WIDGET_ID)
        .expect("declaration panel should be populated from elaborated declarations");
    assert_eq!(declaration_panel.id, DECLARATION_PANEL_WIDGET_ID);
    assert_eq!(
        declaration_panel.javascript_hash,
        DECLARATION_PANEL_WIDGET_HASH
    );
    assert_eq!(declaration_panel.props["documentVersion"], 7);
    assert_eq!(declaration_panel.props["declarations"][0]["name"], "answer");
    assert_eq!(declaration_panel.props["declarations"][0]["type"], "Nat");
    let type_panel = widgets
        .widgets
        .iter()
        .find(|widget| widget.id == TYPE_PANEL_WIDGET_ID)
        .expect("type panel should be populated from elaborated declarations");
    assert_eq!(type_panel.javascript_hash, TYPE_PANEL_WIDGET_HASH);
    assert_eq!(type_panel.props["name"], "answer");
    assert_eq!(type_panel.props["type"], "Nat");

    let source_value = backend
        .rpc_call(crate::rpc::RpcCallParams {
            text_document: crate::rpc::TextDocumentIdentifier { uri },
            position: Position::new(0, 4),
            session_id: connected.session_id,
            method: "Lean.Widget.getWidgetSource".to_string(),
            params: serde_json::json!({
                "hash": DECLARATION_PANEL_WIDGET_HASH.to_string(),
                "pos": {"line": 0, "character": 4}
            }),
        })
        .unwrap();
    let source: WidgetSource = serde_json::from_value(source_value).unwrap();
    assert!(source.sourcetext.contains("DeclarationPanel"));
}

#[tokio::test]
async fn test_rpc_get_widgets_uses_live_checked_document_declaration_panels() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///live-declaration-panel.lean").unwrap();
    let text = "axiom live_widget_decl : Nat\n".to_string();

    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text, "lean".to_string()),
    );
    backend.parse_document(&uri).await;
    backend.elaborate_document(&uri).await;

    let elaborated = backend
        .documents
        .get(&uri)
        .and_then(|doc| doc.elaborated.clone())
        .expect("live check should store elaboration state");
    assert!(
        elaborated.errors.is_empty(),
        "live check should not produce type errors, got {:?}",
        elaborated.errors
    );
    let decl = elaborated
        .declarations
        .first()
        .expect("live check should produce an elaborated declaration");
    let query_position = backend
        .documents
        .get(&uri)
        .map(|doc| doc.offset_to_position(decl.start))
        .expect("document should remain open");

    let connected = backend
        .rpc_connect(crate::rpc::RpcConnectParams { uri: uri.clone() })
        .unwrap();
    let widgets_value = backend
        .rpc_call(crate::rpc::RpcCallParams {
            text_document: crate::rpc::TextDocumentIdentifier { uri: uri.clone() },
            position: query_position,
            session_id: connected.session_id,
            method: "Lean.Widget.getWidgets".to_string(),
            params: serde_json::Value::Null,
        })
        .unwrap();
    let widgets: crate::rpc::GetWidgetsResponse = serde_json::from_value(widgets_value).unwrap();

    let declaration_panel = widgets
        .widgets
        .iter()
        .find(|widget| widget.id == DECLARATION_PANEL_WIDGET_ID)
        .expect("declaration panel should be populated from live elaboration state");
    assert_eq!(
        declaration_panel.props["declarations"][0]["name"],
        "live_widget_decl"
    );
    assert_eq!(
        declaration_panel.props["declarations"][0]["type"],
        decl.type_str
    );

    let type_panel = widgets
        .widgets
        .iter()
        .find(|widget| widget.id == TYPE_PANEL_WIDGET_ID)
        .expect("type panel should be populated from live elaboration state");
    assert_eq!(type_panel.props["name"], "live_widget_decl");
    assert_eq!(type_panel.props["type"], decl.type_str);

    let source_value = backend
        .rpc_call(crate::rpc::RpcCallParams {
            text_document: crate::rpc::TextDocumentIdentifier { uri },
            position: query_position,
            session_id: connected.session_id,
            method: "Lean.Widget.getWidgetSource".to_string(),
            params: serde_json::json!({
                "hash": TYPE_PANEL_WIDGET_HASH.to_string(),
                "pos": query_position
            }),
        })
        .unwrap();
    let source: WidgetSource = serde_json::from_value(source_value).unwrap();
    assert!(source.sourcetext.contains("TypeAtPositionPanel"));
}

#[tokio::test]
async fn test_rpc_get_widgets_live_checked_document_filters_type_panels_by_decl_range() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///live-declaration-panel-ranges.lean").unwrap();
    let text = "axiom live_first : Nat\naxiom live_second : Nat\n".to_string();

    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text, "lean".to_string()),
    );
    backend.parse_document(&uri).await;
    backend.elaborate_document(&uri).await;

    let doc = backend
        .documents
        .get(&uri)
        .expect("document should remain open after live check");
    let elaborated = doc
        .elaborated
        .clone()
        .expect("live check should store elaboration state");
    assert!(
        elaborated.errors.is_empty(),
        "live check should not produce type errors, got {:?}",
        elaborated.errors
    );
    assert_eq!(
        elaborated.declarations.len(),
        2,
        "live check should produce both declarations"
    );
    let first_pos = doc.offset_to_position(elaborated.declarations[0].start);
    let second_pos = doc.offset_to_position(elaborated.declarations[1].start);
    drop(doc);

    let connected = backend
        .rpc_connect(crate::rpc::RpcConnectParams { uri: uri.clone() })
        .unwrap();

    let first_value = backend
        .rpc_call(crate::rpc::RpcCallParams {
            text_document: crate::rpc::TextDocumentIdentifier { uri: uri.clone() },
            position: first_pos,
            session_id: connected.session_id,
            method: "Lean.Widget.getWidgets".to_string(),
            params: serde_json::Value::Null,
        })
        .unwrap();
    let first_widgets: crate::rpc::GetWidgetsResponse =
        serde_json::from_value(first_value).unwrap();
    let first_type_panels: Vec<_> = first_widgets
        .widgets
        .iter()
        .filter(|widget| widget.id == TYPE_PANEL_WIDGET_ID)
        .collect();
    assert_eq!(
        first_type_panels.len(),
        1,
        "first declaration position should expose exactly one type panel"
    );
    assert_eq!(first_type_panels[0].props["name"], "live_first");
    let declaration_panel = first_widgets
        .widgets
        .iter()
        .find(|widget| widget.id == DECLARATION_PANEL_WIDGET_ID)
        .expect("declaration panel should summarize the live checked document");
    assert_eq!(
        declaration_panel.props["declarations"]
            .as_array()
            .unwrap()
            .len(),
        2,
        "declaration panel should include both live checked declarations"
    );

    let second_value = backend
        .rpc_call(crate::rpc::RpcCallParams {
            text_document: crate::rpc::TextDocumentIdentifier { uri },
            position: second_pos,
            session_id: connected.session_id,
            method: "Lean.Widget.getWidgets".to_string(),
            params: serde_json::Value::Null,
        })
        .unwrap();
    let second_widgets: crate::rpc::GetWidgetsResponse =
        serde_json::from_value(second_value).unwrap();
    let second_type_panels: Vec<_> = second_widgets
        .widgets
        .iter()
        .filter(|widget| widget.id == TYPE_PANEL_WIDGET_ID)
        .collect();
    assert_eq!(
        second_type_panels.len(),
        1,
        "second declaration position should expose exactly one type panel"
    );
    assert_eq!(second_type_panels[0].props["name"], "live_second");
}

#[tokio::test]
async fn test_rpc_get_widgets_live_checked_refresh_replaces_previous_panels() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///live-declaration-panel-refresh.lean").unwrap();

    backend.documents.insert(
        uri.clone(),
        Document::new(
            uri.clone(),
            1,
            "axiom live_old : Nat\n".to_string(),
            "lean".to_string(),
        ),
    );
    backend.parse_document(&uri).await;
    backend.elaborate_document(&uri).await;

    let old_pos = backend
        .documents
        .get(&uri)
        .and_then(|doc| {
            let elaborated = doc.elaborated.as_ref()?;
            Some(doc.offset_to_position(elaborated.declarations.first()?.start))
        })
        .expect("first live check should produce a declaration position");
    let connected = backend
        .rpc_connect(crate::rpc::RpcConnectParams { uri: uri.clone() })
        .unwrap();
    let old_value = backend
        .rpc_call(crate::rpc::RpcCallParams {
            text_document: crate::rpc::TextDocumentIdentifier { uri: uri.clone() },
            position: old_pos,
            session_id: connected.session_id,
            method: "Lean.Widget.getWidgets".to_string(),
            params: serde_json::Value::Null,
        })
        .unwrap();
    let old_widgets: crate::rpc::GetWidgetsResponse = serde_json::from_value(old_value).unwrap();
    assert!(
        old_widgets
            .widgets
            .iter()
            .any(|widget| widget.props["name"] == "live_old"),
        "first live checked widget response should expose live_old"
    );

    backend.documents.insert(
        uri.clone(),
        Document::new(
            uri.clone(),
            2,
            "axiom live_new : Nat\n".to_string(),
            "lean".to_string(),
        ),
    );
    backend.parse_document(&uri).await;
    backend.elaborate_document(&uri).await;
    let new_pos = backend
        .documents
        .get(&uri)
        .and_then(|doc| {
            let elaborated = doc.elaborated.as_ref()?;
            Some(doc.offset_to_position(elaborated.declarations.first()?.start))
        })
        .expect("second live check should produce a declaration position");

    let new_value = backend
        .rpc_call(crate::rpc::RpcCallParams {
            text_document: crate::rpc::TextDocumentIdentifier { uri },
            position: new_pos,
            session_id: connected.session_id,
            method: "Lean.Widget.getWidgets".to_string(),
            params: serde_json::Value::Null,
        })
        .unwrap();
    let new_widgets: crate::rpc::GetWidgetsResponse = serde_json::from_value(new_value).unwrap();
    let declaration_panel = new_widgets
        .widgets
        .iter()
        .find(|widget| widget.id == DECLARATION_PANEL_WIDGET_ID)
        .expect("refreshed response should include a declaration panel");
    assert_eq!(
        declaration_panel.props["documentVersion"], 2,
        "refreshed declaration panel should use the current document version"
    );
    assert_eq!(
        declaration_panel.props["declarations"][0]["name"], "live_new",
        "refreshed declaration panel should use the current live declaration"
    );
    assert!(
        !new_widgets
            .widgets
            .iter()
            .any(|widget| widget.props["name"] == "live_old"),
        "refreshed widget response must not retain stale live_old type panels"
    );
}

#[test]
fn test_rpc_get_widgets_exposes_type_panel_only_inside_declaration_range() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///type-panel.lean").unwrap();
    let text = "def first : Nat := 1\n\n#check first\n".to_string();
    let mut doc = Document::new(uri.clone(), 3, text, "lean".to_string());
    doc.elaborated = Some(ElaboratedDocument {
        errors: vec![],
        warnings: vec![],
        declarations: vec![ElaboratedDecl {
            identity: clean_kernel::Name::anon().str("first"),
            name: "first".to_string(),
            type_str: "Nat".to_string(),
            start: 0,
            end: "def first : Nat := 1".len(),
        }],
        term_infos: Vec::new(),
        holes: vec![],
        widget_modules: vec![],
    });
    backend.documents.insert(uri.clone(), doc);

    let connected = backend
        .rpc_connect(crate::rpc::RpcConnectParams { uri: uri.clone() })
        .unwrap();

    let outside_value = backend
        .rpc_call(crate::rpc::RpcCallParams {
            text_document: crate::rpc::TextDocumentIdentifier { uri: uri.clone() },
            position: Position::new(2, 0),
            session_id: connected.session_id,
            method: "Lean.Widget.getWidgets".to_string(),
            params: serde_json::Value::Null,
        })
        .unwrap();
    let outside: crate::rpc::GetWidgetsResponse = serde_json::from_value(outside_value).unwrap();
    assert!(
        outside.widgets.is_empty(),
        "type panel is declaration-range backed, not hover/type parity outside elaborated spans"
    );

    let source_value = backend
        .rpc_call(crate::rpc::RpcCallParams {
            text_document: crate::rpc::TextDocumentIdentifier { uri },
            position: Position::new(0, 4),
            session_id: connected.session_id,
            method: "Lean.Widget.getWidgetSource".to_string(),
            params: serde_json::json!({
                "hash": TYPE_PANEL_WIDGET_HASH.to_string(),
                "pos": {"line": 0, "character": 4}
            }),
        })
        .unwrap();
    let source: WidgetSource = serde_json::from_value(source_value).unwrap();
    assert!(source.sourcetext.contains("TypeAtPositionPanel"));
}

#[test]
fn test_rpc_get_widgets_refresh_clears_stale_elaboration_widgets() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///stale-widget-refresh.lean").unwrap();
    let text = "def stale : Nat := 1\n".to_string();
    let mut doc = Document::new(uri.clone(), 1, text, "lean".to_string());
    doc.elaborated = Some(ElaboratedDocument {
        errors: vec![],
        warnings: vec![],
        declarations: vec![ElaboratedDecl {
            identity: clean_kernel::Name::anon().str("stale"),
            name: "stale".to_string(),
            type_str: "Nat".to_string(),
            start: 0,
            end: "def stale : Nat := 1".len(),
        }],
        term_infos: Vec::new(),
        holes: vec![],
        widget_modules: vec![],
    });
    backend.documents.insert(uri.clone(), doc);

    let connected = backend
        .rpc_connect(crate::rpc::RpcConnectParams { uri: uri.clone() })
        .unwrap();

    let initial_value = backend
        .rpc_call(crate::rpc::RpcCallParams {
            text_document: crate::rpc::TextDocumentIdentifier { uri: uri.clone() },
            position: Position::new(0, 4),
            session_id: connected.session_id,
            method: "Lean.Widget.getWidgets".to_string(),
            params: serde_json::Value::Null,
        })
        .unwrap();
    let initial: crate::rpc::GetWidgetsResponse = serde_json::from_value(initial_value).unwrap();
    assert_eq!(initial.widgets.len(), 2);

    backend.documents.insert(
        uri.clone(),
        Document::new(
            uri.clone(),
            2,
            "def stale :=".to_string(),
            "lean".to_string(),
        ),
    );

    let refreshed_value = backend
        .rpc_call(crate::rpc::RpcCallParams {
            text_document: crate::rpc::TextDocumentIdentifier { uri },
            position: Position::new(0, 4),
            session_id: connected.session_id,
            method: "Lean.Widget.getWidgets".to_string(),
            params: serde_json::Value::Null,
        })
        .unwrap();
    let refreshed: crate::rpc::GetWidgetsResponse =
        serde_json::from_value(refreshed_value).unwrap();
    assert!(
        refreshed.widgets.is_empty(),
        "widget refresh should clear stale declaration/type panels when elaboration state is absent"
    );
}

#[tokio::test]
async fn test_linked_editing_range_returns_all_in_document_occurrences() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///linked.lean").unwrap();
    let text = "def foo := 1\n#check foo\n#check foo".to_string();
    let doc = Document::new(uri.clone(), 1, text.clone(), "lean".to_string());
    let first_use_off = text
        .find("#check foo")
        .map(|p| p + "#check ".len())
        .expect("text should contain the identifier");
    let position = doc.offset_to_position(first_use_off);
    backend.documents.insert(uri.clone(), doc);
    backend.parse_document(&uri).await;
    backend.elaborate_document(&uri).await;

    let result = LanguageServer::linked_editing_range(
        backend,
        LinkedEditingRangeParams {
            text_document_position_params: TextDocumentPositionParams {
                text_document: TextDocumentIdentifier { uri: uri.clone() },
                position,
            },
            work_done_progress_params: WorkDoneProgressParams::default(),
        },
    )
    .await
    .expect("linked_editing_range should not fail")
    .expect("an identifier under the cursor should yield linked ranges");

    assert!(
        result.ranges.len() >= 2,
        "expected at least 2 occurrences of `foo`, got {}",
        result.ranges.len()
    );
    assert!(
        result.word_pattern.is_none(),
        "default word pattern should defer to the editor"
    );
}

#[tokio::test]
async fn test_prepare_call_hierarchy_returns_item_for_defined_name() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///ch-prep.lean").unwrap();
    let text = "def foo := 1\n".to_string();
    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text.clone(), "lean".to_string()),
    );
    backend.parse_document(&uri).await;
    backend.elaborate_document(&uri).await;

    let foo_off = text.find("foo").expect("identifier should exist");
    let doc = backend.documents.get(&uri).unwrap();
    let position = doc.offset_to_position(foo_off);
    drop(doc);

    let result = LanguageServer::prepare_call_hierarchy(
        backend,
        CallHierarchyPrepareParams {
            text_document_position_params: TextDocumentPositionParams {
                text_document: TextDocumentIdentifier { uri: uri.clone() },
                position,
            },
            work_done_progress_params: WorkDoneProgressParams::default(),
        },
    )
    .await
    .expect("prepare_call_hierarchy should not fail")
    .expect("named definition should produce an item");

    assert_eq!(result.len(), 1);
    assert_eq!(result[0].name, "foo");
    assert_eq!(result[0].uri, uri);
}

#[tokio::test]
async fn test_incoming_and_outgoing_calls_resolve_across_definitions() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///ch-calls.lean").unwrap();
    let text = "def callee := 1\ndef caller := callee\n".to_string();
    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text.clone(), "lean".to_string()),
    );
    backend.parse_document(&uri).await;
    backend.elaborate_document(&uri).await;

    let callee_info = backend
        .definitions
        .get("callee")
        .expect("callee should be indexed");
    let callee_item = backend
        .make_call_hierarchy_item("callee", callee_info.value())
        .expect("callee item should build");
    drop(callee_info);

    let caller_info = backend
        .definitions
        .get("caller")
        .expect("caller should be indexed");
    let caller_item = backend
        .make_call_hierarchy_item("caller", caller_info.value())
        .expect("caller item should build");
    drop(caller_info);

    // Incoming calls into `callee` should report `caller`.
    let incoming = LanguageServer::incoming_calls(
        backend,
        CallHierarchyIncomingCallsParams {
            item: callee_item,
            work_done_progress_params: WorkDoneProgressParams::default(),
            partial_result_params: PartialResultParams::default(),
        },
    )
    .await
    .expect("incoming_calls should not fail")
    .expect("incoming_calls should return Some");

    assert_eq!(incoming.len(), 1, "expected exactly one caller");
    assert_eq!(incoming[0].from.name, "caller");
    assert!(
        !incoming[0].from_ranges.is_empty(),
        "expected at least one call-site range"
    );

    // Outgoing calls from `caller` should report `callee`.
    let outgoing = LanguageServer::outgoing_calls(
        backend,
        CallHierarchyOutgoingCallsParams {
            item: caller_item,
            work_done_progress_params: WorkDoneProgressParams::default(),
            partial_result_params: PartialResultParams::default(),
        },
    )
    .await
    .expect("outgoing_calls should not fail")
    .expect("outgoing_calls should return Some");

    assert_eq!(outgoing.len(), 1, "expected exactly one callee");
    assert_eq!(outgoing[0].to.name, "callee");
    assert!(
        !outgoing[0].from_ranges.is_empty(),
        "expected at least one outgoing call-site range"
    );
}

#[tokio::test]
async fn test_completion_items_carry_label_details_and_sort_definitions_before_keywords() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///rich-completion.lean").unwrap();
    let text = "def foo := 1\n".to_string();
    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text, "lean".to_string()),
    );
    backend.parse_document(&uri).await;

    // Cursor placed where prefix is empty so every keyword + def is offered.
    let response = LanguageServer::completion(
        backend,
        CompletionParams {
            text_document_position: TextDocumentPositionParams {
                text_document: TextDocumentIdentifier { uri: uri.clone() },
                position: Position::new(1, 0),
            },
            work_done_progress_params: WorkDoneProgressParams::default(),
            partial_result_params: PartialResultParams::default(),
            context: None,
        },
    )
    .await
    .expect("completion should not fail")
    .expect("completion should return Some");
    let items = match response {
        CompletionResponse::Array(items) => items,
        CompletionResponse::List(list) => list.items,
    };

    let foo = items
        .iter()
        .find(|i| i.label == "foo")
        .expect("definition `foo` should be offered as a completion");
    assert_eq!(foo.sort_text.as_deref(), Some("a_foo"));
    let details = foo
        .label_details
        .as_ref()
        .expect("completion item for a defined name should expose label_details");
    assert_eq!(
        details.description.as_deref(),
        Some("def"),
        "label_details.description should carry the command kind"
    );
    // Without elaboration, type info is unavailable — documentation is then
    // intentionally None. With elaboration it should be Markdown markup.
    if let Some(Documentation::MarkupContent(content)) = &foo.documentation {
        assert_eq!(content.kind, MarkupKind::Markdown);
        assert!(content.value.contains("foo"));
    }

    let def_kw = items
        .iter()
        .find(|i| i.label == "def" && i.kind == Some(CompletionItemKind::KEYWORD))
        .expect("`def` keyword should still be offered");
    assert_eq!(def_kw.sort_text.as_deref(), Some("z_def"));

    // Sanity: with sort_text in place, the definition sorts before the keyword.
    assert!(foo.sort_text.as_deref() < def_kw.sort_text.as_deref());
}

#[tokio::test]
async fn test_linked_editing_range_returns_none_outside_identifier() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///linked-empty.lean").unwrap();
    let text = "   \n".to_string();
    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text, "lean".to_string()),
    );

    let result = LanguageServer::linked_editing_range(
        backend,
        LinkedEditingRangeParams {
            text_document_position_params: TextDocumentPositionParams {
                text_document: TextDocumentIdentifier { uri: uri.clone() },
                position: Position::new(0, 1),
            },
            work_done_progress_params: WorkDoneProgressParams::default(),
        },
    )
    .await
    .expect("linked_editing_range should not fail");

    assert!(
        result.is_none(),
        "whitespace position should yield no linked ranges"
    );
}

#[test]
fn test_clean_config_default_enables_inlay_hints() {
    let config = CleanConfig::default();
    assert!(
        config.inlay_hints_enabled,
        "inlay hints should default to enabled"
    );
}

#[test]
fn test_clean_config_apply_json_nested_disables_inlay_hints() {
    let mut config = CleanConfig::default();
    config.apply_json(&serde_json::json!({
        "clean": { "inlayHints": { "enable": false } }
    }));
    assert!(
        !config.inlay_hints_enabled,
        "nested clean.inlayHints.enable=false should disable inlay hints"
    );
}

#[test]
fn test_clean_config_apply_json_scoped_form_updates_inlay_hints() {
    let mut config = CleanConfig::default();
    // Already-scoped payload (no top-level `clean` wrapper).
    config.apply_json(&serde_json::json!({ "inlayHints": { "enable": false } }));
    assert!(
        !config.inlay_hints_enabled,
        "scoped inlayHints.enable=false should disable inlay hints"
    );
    config.apply_json(&serde_json::json!({ "inlayHints": { "enable": true } }));
    assert!(
        config.inlay_hints_enabled,
        "scoped inlayHints.enable=true should re-enable inlay hints"
    );
}

#[test]
fn test_clean_config_apply_json_unknown_keys_are_ignored() {
    let mut config = CleanConfig::default();
    // Unknown keys, wrong types, and a null blob must leave state untouched
    // without panicking.
    config.apply_json(&serde_json::json!({
        "clean": { "someUnknownSetting": 42, "inlayHints": { "enable": "not-a-bool" } }
    }));
    config.apply_json(&serde_json::json!(null));
    config.apply_json(&serde_json::json!("garbage"));
    config.apply_json(&serde_json::json!([1, 2, 3]));
    assert!(
        config.inlay_hints_enabled,
        "unknown / malformed settings should not change the default"
    );
}

#[test]
fn test_get_inlay_hints_disabled_returns_empty() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///inlay-disabled.lean").unwrap();
    let text = "def inferred := 1\n".to_string();
    let mut doc = Document::new(uri.clone(), 1, text, "lean".to_string());
    doc.elaborated = Some(ElaboratedDocument {
        errors: vec![],
        warnings: vec![],
        declarations: vec![ElaboratedDecl {
            identity: clean_kernel::Name::anon().str("inferred"),
            name: "inferred".to_string(),
            type_str: "Nat".to_string(),
            start: 0,
            end: "def inferred := 1".len(),
        }],
        term_infos: Vec::new(),
        holes: vec![],
        widget_modules: vec![],
    });
    backend.documents.insert(uri.clone(), doc);

    let full_range = Range {
        start: Position::new(0, 0),
        end: Position::new(1, 0),
    };
    // Enabled path produces the inferred-type hint...
    assert_eq!(
        backend.get_inlay_hints(&uri, full_range, true).len(),
        1,
        "enabled config should surface the inferred-type hint"
    );
    // ...and the disabled path suppresses it entirely.
    assert!(
        backend.get_inlay_hints(&uri, full_range, false).is_empty(),
        "disabled config should suppress all inlay hints"
    );
}

#[tokio::test]
async fn test_did_change_configuration_disables_inlay_hint_request() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///did-change-config.lean").unwrap();
    let text = "def inferred := 1\n".to_string();
    let mut doc = Document::new(uri.clone(), 1, text, "lean".to_string());
    doc.elaborated = Some(ElaboratedDocument {
        errors: vec![],
        warnings: vec![],
        declarations: vec![ElaboratedDecl {
            identity: clean_kernel::Name::anon().str("inferred"),
            name: "inferred".to_string(),
            type_str: "Nat".to_string(),
            start: 0,
            end: "def inferred := 1".len(),
        }],
        term_infos: Vec::new(),
        holes: vec![],
        widget_modules: vec![],
    });
    backend.documents.insert(uri.clone(), doc);

    let params = InlayHintParams {
        text_document: TextDocumentIdentifier { uri: uri.clone() },
        range: Range::new(Position::new(0, 0), Position::new(1, 0)),
        work_done_progress_params: WorkDoneProgressParams::default(),
    };

    // Default config: the live request returns one hint.
    let before = LanguageServer::inlay_hint(backend, params.clone())
        .await
        .expect("inlay hint request should not fail")
        .expect("default config should produce inlay hints");
    assert_eq!(before.len(), 1, "default config should surface one hint");

    // Flip the setting via the configuration notification.
    LanguageServer::did_change_configuration(
        backend,
        DidChangeConfigurationParams {
            settings: serde_json::json!({ "clean": { "inlayHints": { "enable": false } } }),
        },
    )
    .await;

    assert!(
        !backend.config.read().await.inlay_hints_enabled,
        "didChangeConfiguration should update the stored config"
    );

    // The same request now returns no hints — no restart required.
    let after = LanguageServer::inlay_hint(backend, params)
        .await
        .expect("inlay hint request should not fail")
        .expect("handler always returns Some");
    assert!(
        after.is_empty(),
        "after disabling, the live inlay-hint request should be empty"
    );
}

#[tokio::test]
async fn test_did_change_configuration_malformed_params_are_ignored() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();

    // A junk payload must not panic and must not alter the default state.
    LanguageServer::did_change_configuration(
        backend,
        DidChangeConfigurationParams {
            settings: serde_json::json!("totally-not-an-object"),
        },
    )
    .await;
    LanguageServer::did_change_configuration(
        backend,
        DidChangeConfigurationParams {
            settings: serde_json::json!(null),
        },
    )
    .await;

    assert!(
        backend.config.read().await.inlay_hints_enabled,
        "malformed configuration must leave the default untouched"
    );
}

#[tokio::test]
async fn test_document_highlight_returns_all_occurrences_for_used_symbol() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///highlight.lean").unwrap();
    // `hl_decl` appears three times: declaration plus two uses.
    let text = "axiom hl_decl : Nat\n#check hl_decl\n#check hl_decl\n".to_string();

    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text.clone(), "lean".to_string()),
    );
    backend.parse_document(&uri).await;
    backend.elaborate_document(&uri).await;

    // Place the cursor inside the declaration occurrence of `hl_decl`.
    let cursor = {
        let doc = backend
            .documents
            .get(&uri)
            .expect("highlight document should remain open");
        let decl_offset = text
            .find("hl_decl")
            .expect("text should contain the declaration name")
            + 1;
        doc.offset_to_position(decl_offset)
    };

    let highlights = LanguageServer::document_highlight(
        backend,
        DocumentHighlightParams {
            text_document_position_params: TextDocumentPositionParams {
                text_document: TextDocumentIdentifier { uri: uri.clone() },
                position: cursor,
            },
            work_done_progress_params: WorkDoneProgressParams::default(),
            partial_result_params: PartialResultParams::default(),
        },
    )
    .await
    .expect("document highlight request should not fail")
    .expect("symbol used multiple times should yield highlights");

    assert_eq!(
        highlights.len(),
        3,
        "declaration and both uses of hl_decl should be highlighted"
    );
    assert!(
        highlights
            .iter()
            .all(|hl| hl.kind == Some(DocumentHighlightKind::TEXT)),
        "clean reports textual occurrences with the TEXT highlight kind"
    );

    // Every highlighted range must cover exactly the `hl_decl` identifier.
    let doc = backend
        .documents
        .get(&uri)
        .expect("highlight document should remain open");
    for hl in &highlights {
        let start = doc.position_to_offset(hl.range.start);
        let end = doc.position_to_offset(hl.range.end);
        assert_eq!(
            &text[start..end],
            "hl_decl",
            "highlight range should cover the whole identifier"
        );
    }
}

#[tokio::test]
async fn test_document_highlight_is_document_local() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let decl_uri = Url::parse("file:///highlight-decl.lean").unwrap();
    let use_uri = Url::parse("file:///highlight-use.lean").unwrap();
    let decl_text = "axiom shared_decl : Nat\n".to_string();
    let use_text = "#check shared_decl\n#check shared_decl\n".to_string();

    backend.documents.insert(
        decl_uri.clone(),
        Document::new(decl_uri.clone(), 1, decl_text.clone(), "lean".to_string()),
    );
    backend.documents.insert(
        use_uri.clone(),
        Document::new(use_uri.clone(), 1, use_text.clone(), "lean".to_string()),
    );
    backend.parse_document(&decl_uri).await;
    backend.elaborate_document(&decl_uri).await;
    backend.parse_document(&use_uri).await;
    backend.elaborate_document(&use_uri).await;

    let cursor = {
        let doc = backend
            .documents
            .get(&use_uri)
            .expect("use document should remain open");
        let use_offset = use_text
            .find("shared_decl")
            .expect("use text should contain the identifier");
        doc.offset_to_position(use_offset)
    };

    let highlights = LanguageServer::document_highlight(
        backend,
        DocumentHighlightParams {
            text_document_position_params: TextDocumentPositionParams {
                text_document: TextDocumentIdentifier {
                    uri: use_uri.clone(),
                },
                position: cursor,
            },
            work_done_progress_params: WorkDoneProgressParams::default(),
            partial_result_params: PartialResultParams::default(),
        },
    )
    .await
    .expect("document highlight request should not fail")
    .expect("the use document has two occurrences");

    assert_eq!(
        highlights.len(),
        2,
        "only the two uses in the requested document should be highlighted, not the cross-file declaration"
    );
}

#[tokio::test]
async fn test_document_highlight_no_symbol_under_cursor_returns_none() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///highlight-empty.lean").unwrap();
    // Position the cursor on whitespace where no identifier exists.
    let text = "   \n".to_string();
    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text, "lean".to_string()),
    );

    let result = LanguageServer::document_highlight(
        backend,
        DocumentHighlightParams {
            text_document_position_params: TextDocumentPositionParams {
                text_document: TextDocumentIdentifier { uri: uri.clone() },
                position: Position::new(0, 1),
            },
            work_done_progress_params: WorkDoneProgressParams::default(),
            partial_result_params: PartialResultParams::default(),
        },
    )
    .await
    .expect("document highlight request should not fail");

    assert!(
        result.is_none(),
        "no identifier under the cursor should produce no highlights"
    );
}

#[test]
fn test_type_name_candidates_extracts_identifiers_in_order() {
    // A clean pretty-printed application type.
    let candidates = CleanBackend::type_name_candidates("List Nat");
    assert_eq!(candidates, vec!["List".to_string(), "Nat".to_string()]);

    // A structural debug rendering surfaces the same names as identifier tokens.
    let debug_candidates =
        CleanBackend::type_name_candidates("Const(Name { inner: Str(Anon, \"MyType\") }, [])");
    assert!(
        debug_candidates.iter().any(|name| name == "MyType"),
        "the head constant name should be recoverable from a debug rendering"
    );

    // Repeated names are de-duplicated, preserving first appearance.
    let deduped = CleanBackend::type_name_candidates("Pair Foo Foo Bar");
    assert_eq!(
        deduped,
        vec!["Pair".to_string(), "Foo".to_string(), "Bar".to_string()]
    );

    // No identifiers means no candidates (and no panic).
    assert!(CleanBackend::type_name_candidates("-> (, )").is_empty());
}

#[tokio::test]
async fn test_goto_type_definition_resolves_to_type_decl_location() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///type-definition.lean").unwrap();

    // `MyType` is declared as an inductive; `val` has type `MyType`. Jumping to
    // the type definition of `val` should land on `MyType`'s declaration.
    let mytype_decl = "inductive MyType\n".to_string();
    let val_decl = "axiom val : MyType\n";
    let text = format!("{mytype_decl}{val_decl}");

    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text.clone(), "lean".to_string()),
    );
    // Index the declarations from the parsed document.
    backend.parse_document(&uri).await;

    // Inject a controlled elaborated type for `val` so the resolution does not
    // depend on the elaborator's exact pretty-printing of `MyType`.
    {
        let mut doc = backend
            .documents
            .get_mut(&uri)
            .expect("type-definition document should remain open");
        let val_start = text
            .find("axiom val")
            .expect("text should contain the val declaration");
        doc.elaborated = Some(ElaboratedDocument {
            errors: vec![],
            warnings: vec![],
            declarations: vec![ElaboratedDecl {
                identity: clean_kernel::Name::anon().str("val"),
                name: "val".to_string(),
                type_str: "MyType".to_string(),
                start: val_start,
                end: text.len(),
            }],
            term_infos: Vec::new(),
            holes: vec![],
            widget_modules: vec![],
        });
    }

    let cursor = {
        let doc = backend
            .documents
            .get(&uri)
            .expect("type-definition document should remain open");
        let val_use = text
            .find("val :")
            .expect("text should contain the val identifier");
        doc.offset_to_position(val_use)
    };

    let response = LanguageServer::goto_type_definition(
        backend,
        GotoDefinitionParams {
            text_document_position_params: TextDocumentPositionParams {
                text_document: TextDocumentIdentifier { uri: uri.clone() },
                position: cursor,
            },
            work_done_progress_params: WorkDoneProgressParams::default(),
            partial_result_params: PartialResultParams::default(),
        },
    )
    .await
    .expect("type definition request should not fail")
    .expect("val's type MyType is declared in this document");

    let GotoDefinitionResponse::Scalar(location) = response else {
        panic!("expected a scalar type-definition location");
    };
    assert_eq!(location.uri, uri);
    let doc = backend
        .documents
        .get(&uri)
        .expect("type-definition document should remain open");
    // `find_definition` (shared with goto-definition) returns the declaration
    // command range. The parser tracks the command span as the leading keyword,
    // so the target lands at the start of the `inductive MyType` command — i.e.
    // the MyType declaration site, ahead of the `val` declaration.
    let start_offset = doc.position_to_offset(location.range.start);
    let mytype_command_start = text
        .find("inductive MyType")
        .expect("MyType declaration present");
    let val_command_start = text.find("axiom val").expect("val declaration present");
    assert_eq!(
        start_offset, mytype_command_start,
        "type definition should resolve to the MyType declaration site"
    );
    assert!(
        start_offset < val_command_start,
        "type definition target should sit at the MyType declaration, before the val declaration"
    );
}

#[tokio::test]
async fn test_goto_type_definition_builtin_type_returns_none() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///type-definition-builtin.lean").unwrap();
    let text = "axiom plain : Nat\n".to_string();

    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text.clone(), "lean".to_string()),
    );
    backend.parse_document(&uri).await;
    {
        let mut doc = backend
            .documents
            .get_mut(&uri)
            .expect("builtin type-definition document should remain open");
        let plain_start = text
            .find("axiom plain")
            .expect("text should contain the plain declaration");
        doc.elaborated = Some(ElaboratedDocument {
            errors: vec![],
            warnings: vec![],
            declarations: vec![ElaboratedDecl {
                identity: clean_kernel::Name::anon().str("plain"),
                name: "plain".to_string(),
                // `Nat` is a prelude type with no in-workspace declaration.
                type_str: "Nat".to_string(),
                start: plain_start,
                end: text.len(),
            }],
            term_infos: Vec::new(),
            holes: vec![],
            widget_modules: vec![],
        });
    }

    let cursor = {
        let doc = backend
            .documents
            .get(&uri)
            .expect("builtin type-definition document should remain open");
        let plain_use = text
            .find("plain :")
            .expect("text should contain the plain identifier");
        doc.offset_to_position(plain_use)
    };

    let response = LanguageServer::goto_type_definition(
        backend,
        GotoDefinitionParams {
            text_document_position_params: TextDocumentPositionParams {
                text_document: TextDocumentIdentifier { uri: uri.clone() },
                position: cursor,
            },
            work_done_progress_params: WorkDoneProgressParams::default(),
            partial_result_params: PartialResultParams::default(),
        },
    )
    .await
    .expect("type definition request should not fail");

    assert!(
        response.is_none(),
        "a type with no in-workspace declaration should yield no type-definition target"
    );
}

#[tokio::test]
async fn test_goto_type_definition_no_symbol_under_cursor_returns_none() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///type-definition-empty.lean").unwrap();
    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, "   \n".to_string(), "lean".to_string()),
    );

    let response = LanguageServer::goto_type_definition(
        backend,
        GotoDefinitionParams {
            text_document_position_params: TextDocumentPositionParams {
                text_document: TextDocumentIdentifier { uri: uri.clone() },
                position: Position::new(0, 1),
            },
            work_done_progress_params: WorkDoneProgressParams::default(),
            partial_result_params: PartialResultParams::default(),
        },
    )
    .await
    .expect("type definition request should not fail");

    assert!(
        response.is_none(),
        "no identifier under the cursor should produce no type-definition target"
    );
}

#[tokio::test]
async fn test_initialize_advertises_highlight_and_type_definition_providers() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();

    let result = LanguageServer::initialize(backend, InitializeParams::default())
        .await
        .expect("initialize should succeed");

    assert!(
        matches!(
            result.capabilities.document_highlight_provider,
            Some(OneOf::Left(true))
        ),
        "documentHighlight capability should be advertised"
    );
    assert!(
        matches!(
            result.capabilities.type_definition_provider,
            Some(TypeDefinitionProviderCapability::Simple(true))
        ),
        "typeDefinition capability should be advertised"
    );
}

// --- textDocument/documentLink and textDocument/codeLens ---

/// Build a document and run it through the parse pipeline so link/lens
/// providers see populated `parsed` state. Returns the `LspService` (which
/// owns the backend) — callers reach the backend via `service.inner()` and
/// must keep the service in scope.
fn link_lens_service(uri: &Url, text: &str) -> LspService<CleanBackend> {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text.to_string(), "lean".to_string()),
    );
    // parse_document populates `doc.parsed`, which code lenses read from.
    tokio::runtime::Runtime::new()
        .expect("tokio runtime should initialize")
        .block_on(backend.parse_document(uri));
    service
}

#[test]
fn test_document_link_single_import_covers_module_path_with_target() {
    let uri = Url::parse("file:///proj/Main.lean").expect("uri should parse");
    let text = "import Foo.Bar\n";
    let service = link_lens_service(&uri, text);
    let backend = service.inner();

    let links = backend.get_document_links(&uri);
    assert_eq!(links.len(), 1, "one import should yield one link");

    let link = &links[0];
    // "import " is 7 bytes; "Foo.Bar" spans columns 7..14 on line 0.
    assert_eq!(link.range.start, Position::new(0, 7));
    assert_eq!(link.range.end, Position::new(0, 14));
    assert_eq!(
        link.tooltip.as_deref(),
        Some("import Foo.Bar"),
        "tooltip should describe the imported module"
    );
    let target = link.target.as_ref().expect("file: import should resolve");
    assert!(
        target.as_str().ends_with("/proj/Foo/Bar.lean"),
        "dotted module should map to a relative .lean path: {target}"
    );
}

#[test]
fn test_document_link_comma_and_whitespace_separated_imports_each_linked() {
    let uri = Url::parse("file:///proj/Main.lean").expect("uri should parse");
    // First line: comma-separated. Second line: whitespace-separated.
    let text = "import Alpha.Beta, Gamma\nimport One Two\n";
    let service = link_lens_service(&uri, text);
    let backend = service.inner();

    let links = backend.get_document_links(&uri);
    let modules: Vec<String> = links
        .iter()
        .map(|link| {
            link.tooltip
                .as_deref()
                .unwrap_or("")
                .trim_start_matches("import ")
                .to_string()
        })
        .collect();
    assert_eq!(
        modules,
        vec![
            "Alpha.Beta".to_string(),
            "Gamma".to_string(),
            "One".to_string(),
            "Two".to_string(),
        ],
        "every comma/space-separated module should produce its own link"
    );

    // The two modules on line 1 keep distinct, non-overlapping ranges.
    assert_eq!(
        links[0].range.start,
        Position::new(0, 7),
        "Alpha.Beta start"
    );
    assert_eq!(links[0].range.end, Position::new(0, 17), "Alpha.Beta end");
    assert_eq!(links[1].range.start, Position::new(0, 19), "Gamma start");
    assert_eq!(links[1].range.end, Position::new(0, 24), "Gamma end");
}

#[test]
fn test_document_link_non_file_uri_keeps_link_without_target() {
    let uri = Url::parse("untitled:Untitled-1").expect("uri should parse");
    let text = "import Foo.Bar\n";
    let service = link_lens_service(&uri, text);
    let backend = service.inner();

    let links = backend.get_document_links(&uri);
    assert_eq!(links.len(), 1, "import still surfaces a link");
    assert!(
        links[0].target.is_none(),
        "non-file URI cannot derive a filesystem target"
    );
    assert_eq!(links[0].tooltip.as_deref(), Some("import Foo.Bar"));
}

#[test]
fn test_document_link_empty_and_garbage_input_returns_no_links() {
    let uri = Url::parse("file:///proj/Main.lean").expect("uri should parse");

    let empty_service = link_lens_service(&uri, "");
    assert!(
        empty_service.inner().get_document_links(&uri).is_empty(),
        "empty document has no imports"
    );

    let garbage_service = link_lens_service(&uri, "@@@ )(*& import import , . .. \n }{][");
    // Must not panic; an `import` with no following identifier yields nothing.
    assert!(
        garbage_service.inner().get_document_links(&uri).is_empty(),
        "malformed input should yield no links without panicking"
    );
}

#[test]
fn test_document_link_unknown_document_returns_no_links() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///never-opened.lean").expect("uri should parse");
    assert!(
        backend.get_document_links(&uri).is_empty(),
        "an un-opened document has no links"
    );
}

#[test]
fn test_document_link_carries_resolvable_data_payload() {
    let uri = Url::parse("file:///proj/Main.lean").expect("uri should parse");
    let text = "import Foo.Bar\n";
    let service = link_lens_service(&uri, text);
    let backend = service.inner();

    let links = backend.get_document_links(&uri);
    assert_eq!(links.len(), 1, "one import should yield one link");

    // The cheap pass attaches an opaque payload identifying the module so that
    // documentLink/resolve can recover it.
    let value = links[0]
        .data
        .as_ref()
        .expect("link should carry a resolve payload");
    let data = links::DocumentLinkData::from_value(value).expect("payload should round-trip");
    assert_eq!(data.module, "Foo.Bar");
}

#[test]
fn test_document_link_resolve_existing_file_keeps_target_and_enriches_tooltip() {
    let dir = tempfile::tempdir().expect("tempdir should be created");
    // Layout: <dir>/Main.lean importing Foo.Bar, with <dir>/Foo/Bar.lean present.
    let foo_dir = dir.path().join("Foo");
    std::fs::create_dir_all(&foo_dir).expect("Foo dir should be created");
    let bar_path = foo_dir.join("Bar.lean");
    std::fs::write(&bar_path, "-- target module\n").expect("target file should be written");

    let main_path = dir.path().join("Main.lean");
    let uri = Url::from_file_path(&main_path).expect("main uri should build");
    let service = link_lens_service(&uri, "import Foo.Bar\n");
    let backend = service.inner();

    let links = backend.get_document_links(&uri);
    assert_eq!(links.len(), 1);

    let resolved = backend.resolve_document_link(links[0].clone());
    let target = resolved
        .target
        .as_ref()
        .expect("an existing module file keeps its target");
    assert!(
        target.as_str().ends_with("/Foo/Bar.lean"),
        "target should point at the real module file: {target}"
    );
    let tooltip = resolved.tooltip.as_deref().unwrap_or("");
    assert!(
        tooltip.starts_with("import Foo.Bar -> "),
        "resolve should enrich the tooltip with the located file: {tooltip}"
    );
    assert!(
        tooltip.contains("Bar.lean"),
        "enriched tooltip should name the resolved file: {tooltip}"
    );
}

#[test]
fn test_document_link_resolve_missing_file_drops_target() {
    // A real directory with no Foo/Bar.lean inside it: the best-effort target
    // does not exist, so resolve must not hand back a target pointing nowhere.
    let dir = tempfile::tempdir().expect("tempdir should be created");
    let main_path = dir.path().join("Main.lean");
    let uri = Url::from_file_path(&main_path).expect("main uri should build");
    let service = link_lens_service(&uri, "import Missing.Module\n");
    let backend = service.inner();

    let links = backend.get_document_links(&uri);
    assert_eq!(links.len(), 1);
    // The cheap pass derives a (string-mapped) best-effort target.
    assert!(
        links[0].target.is_some(),
        "cheap pass derives a best-effort target without checking the disk"
    );

    let resolved = backend.resolve_document_link(links[0].clone());
    assert!(
        resolved.target.is_none(),
        "resolve must drop a target that points at a non-existent file"
    );
    assert_eq!(
        resolved.tooltip.as_deref(),
        Some("import Missing.Module (module file not found)"),
        "tooltip should explain the module could not be located"
    );
}

#[test]
fn test_document_link_resolve_non_file_link_passes_through_unchanged() {
    // A non-file URI never produced a target; resolve must return it verbatim
    // (no panic, no fabricated target).
    let uri = Url::parse("untitled:Untitled-1").expect("uri should parse");
    let service = link_lens_service(&uri, "import Foo.Bar\n");
    let backend = service.inner();

    let links = backend.get_document_links(&uri);
    assert_eq!(links.len(), 1);
    assert!(links[0].target.is_none(), "non-file URI has no target");

    let resolved = backend.resolve_document_link(links[0].clone());
    assert_eq!(
        resolved, links[0],
        "a targetless link passes through documentLink/resolve unchanged"
    );
}

#[test]
fn test_document_link_resolve_without_payload_passes_through() {
    // A link carrying no `data` (e.g. produced by a different protocol version)
    // is returned unchanged rather than failing the request.
    let bare = DocumentLink {
        range: Range::new(Position::new(0, 0), Position::new(0, 1)),
        target: None,
        tooltip: None,
        data: None,
    };
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    assert_eq!(
        backend.resolve_document_link(bare.clone()),
        bare,
        "a payload-less link is passed through unchanged"
    );
}

#[tokio::test]
async fn test_document_link_resolve_request_routes_to_provider() {
    let dir = tempfile::tempdir().expect("tempdir should be created");
    let foo_dir = dir.path().join("Foo");
    std::fs::create_dir_all(&foo_dir).expect("Foo dir should be created");
    std::fs::write(foo_dir.join("Bar.lean"), "-- target\n").expect("target file should be written");

    let main_path = dir.path().join("Main.lean");
    let uri = Url::from_file_path(&main_path).expect("main uri should build");
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    backend.documents.insert(
        uri.clone(),
        Document::new(
            uri.clone(),
            1,
            "import Foo.Bar\n".to_string(),
            "lean".to_string(),
        ),
    );
    backend.parse_document(&uri).await;

    let links = LanguageServer::document_link(
        backend,
        DocumentLinkParams {
            text_document: TextDocumentIdentifier { uri: uri.clone() },
            work_done_progress_params: WorkDoneProgressParams::default(),
            partial_result_params: PartialResultParams::default(),
        },
    )
    .await
    .expect("documentLink request should not fail")
    .expect("import should produce at least one link");
    assert_eq!(links.len(), 1);

    let resolved = LanguageServer::document_link_resolve(backend, links[0].clone())
        .await
        .expect("documentLink/resolve request should not fail");
    assert!(
        resolved.target.is_some(),
        "routed resolve should keep the verified target"
    );
    assert!(
        resolved
            .tooltip
            .as_deref()
            .unwrap_or("")
            .starts_with("import Foo.Bar -> "),
        "routed resolve should enrich the tooltip"
    );
}

#[test]
fn test_code_lens_one_lens_per_named_declaration() {
    let uri = Url::parse("file:///proj/Decls.lean").expect("uri should parse");
    let text = "def foo := 1\ntheorem bar : True := trivial\naxiom baz : Nat\n";
    let service = link_lens_service(&uri, text);
    let backend = service.inner();

    let lenses = backend.get_code_lenses(&uri);
    // The cheap codeLens pass produces unresolved lenses: no command yet, with
    // the kind+name recorded in the opaque `data` payload.
    assert!(
        lenses.iter().all(|lens| lens.command.is_none()),
        "the cheap codeLens pass should leave the command unresolved"
    );
    let payloads: Vec<(String, String)> = lenses
        .iter()
        .filter_map(|lens| {
            let data = links::CodeLensData::from_value(lens.data.as_ref()?)?;
            Some((data.kind, data.name))
        })
        .collect();
    assert_eq!(
        payloads,
        vec![
            ("def".to_string(), "foo".to_string()),
            ("theorem".to_string(), "bar".to_string()),
            ("axiom".to_string(), "baz".to_string()),
        ],
        "each named top-level decl should get a kind+name lens payload"
    );

    // The first lens anchors at the start of its declaration. Resolving it
    // fills in the title and the routing command with the document URI and
    // decl name as arguments.
    assert_eq!(lenses[0].range.start, Position::new(0, 0));
    let resolved = backend.resolve_code_lens(lenses[0].clone());
    let command = resolved
        .command
        .as_ref()
        .expect("resolved lens carries a command");
    assert_eq!(command.title, "def foo");
    assert_eq!(command.command, "clean.showDecl");
    let args = command.arguments.as_ref().expect("command carries args");
    assert_eq!(args.len(), 2);
    assert_eq!(args[0], serde_json::Value::String(uri.to_string()));
    assert_eq!(args[1], serde_json::Value::String("foo".to_string()));
}

#[test]
fn test_code_lens_skips_imports_and_anonymous_commands() {
    let uri = Url::parse("file:///proj/Mixed.lean").expect("uri should parse");
    // `import` and `#check`/example carry no navigable name; only `def real`
    // should produce a lens.
    let text = "import Foo\nexample : True := trivial\ndef real := 0\n";
    let service = link_lens_service(&uri, text);
    let backend = service.inner();

    let lenses = backend.get_code_lenses(&uri);
    // Resolve each lens so we can read its computed title.
    let titles: Vec<String> = lenses
        .iter()
        .filter_map(|lens| {
            backend
                .resolve_code_lens(lens.clone())
                .command
                .map(|cmd| cmd.title)
        })
        .collect();
    assert_eq!(
        titles,
        vec!["def real".to_string()],
        "imports and anonymous commands carry no code lens"
    );
}

#[test]
fn test_code_lens_empty_and_garbage_input_returns_no_lenses() {
    let uri = Url::parse("file:///proj/Empty.lean").expect("uri should parse");

    let empty_service = link_lens_service(&uri, "");
    assert!(
        empty_service.inner().get_code_lenses(&uri).is_empty(),
        "empty document has no declarations to lens"
    );

    let garbage_service = link_lens_service(&uri, ")(*&^%$ def def := := \n @@@");
    // Must not panic regardless of how the parser recovers.
    let _ = garbage_service.inner().get_code_lenses(&uri);
}

#[test]
fn test_code_lens_unknown_document_returns_no_lenses() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///never-opened.lean").expect("uri should parse");
    assert!(
        backend.get_code_lenses(&uri).is_empty(),
        "an un-opened document has no code lenses"
    );
}

#[test]
fn test_resolve_code_lens_enriches_title_with_elaborated_type() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///lens-resolve.lean").expect("uri should parse");
    let text = "def foo := 1\n".to_string();
    let mut doc = Document::new(uri.clone(), 1, text, "lean".to_string());
    doc.elaborated = Some(ElaboratedDocument {
        errors: vec![],
        warnings: vec![],
        declarations: vec![ElaboratedDecl {
            identity: clean_kernel::Name::anon().str("foo"),
            name: "foo".to_string(),
            type_str: "Nat".to_string(),
            start: 0,
            end: "def foo := 1".len(),
        }],
        term_infos: Vec::new(),
        holes: vec![],
        widget_modules: vec![],
    });
    backend.documents.insert(uri.clone(), doc);

    let data = links::CodeLensData {
        uri: uri.to_string(),
        name: "foo".to_string(),
        kind: "def".to_string(),
    };
    let lens = CodeLens {
        range: Range {
            start: Position::new(0, 0),
            end: Position::new(0, 0),
        },
        command: None,
        data: data.to_value(),
    };

    let resolved = backend.resolve_code_lens(lens);
    let command = resolved
        .command
        .as_ref()
        .expect("resolve should attach a command");
    assert_eq!(
        command.title, "def foo : Nat",
        "resolve should fold the elaborated type into the title"
    );
    assert_eq!(command.command, "clean.showDecl");
    let args = command.arguments.as_ref().expect("command carries args");
    assert_eq!(args[0], serde_json::Value::String(uri.to_string()));
    assert_eq!(args[1], serde_json::Value::String("foo".to_string()));
}

#[test]
fn test_resolve_code_lens_without_data_is_passthrough() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();

    let bare = CodeLens {
        range: Range {
            start: Position::new(2, 4),
            end: Position::new(2, 4),
        },
        command: None,
        data: None,
    };

    let resolved = backend.resolve_code_lens(bare.clone());
    // `CodeLens` has no `PartialEq`; compare the serialized form so we catch
    // any field (notably `command` staying `None`) drifting on passthrough.
    assert_eq!(
        serde_json::to_value(&resolved).expect("resolved lens should serialize"),
        serde_json::to_value(&bare).expect("bare lens should serialize"),
        "a lens with no data should pass through unchanged"
    );
}

#[test]
fn test_resolve_code_lens_unelaborated_document_falls_back_to_kind_name() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();

    // A well-formed payload pointing at a document the server has never seen
    // (e.g. closed between codeLens and resolve). With no elaborated type
    // available the title falls back to kind + name rather than fabricating
    // a type the document does not have.
    let data = links::CodeLensData {
        uri: "file:///never-opened.lean".to_string(),
        name: "ghost".to_string(),
        kind: "theorem".to_string(),
    };
    let lens = CodeLens {
        range: Range {
            start: Position::new(0, 0),
            end: Position::new(0, 0),
        },
        command: None,
        data: data.to_value(),
    };

    let resolved = backend.resolve_code_lens(lens);
    let command = resolved
        .command
        .as_ref()
        .expect("resolve should still attach a command");
    assert_eq!(
        command.title, "theorem ghost",
        "without an elaborated type the title is just kind + name"
    );
}

#[tokio::test]
async fn test_document_link_request_routes_to_provider() {
    let uri = Url::parse("file:///proj/Main.lean").expect("uri should parse");
    let text = "import Foo.Bar\n";
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text.to_string(), "lean".to_string()),
    );
    backend.parse_document(&uri).await;

    let links = LanguageServer::document_link(
        backend,
        DocumentLinkParams {
            text_document: TextDocumentIdentifier { uri: uri.clone() },
            work_done_progress_params: WorkDoneProgressParams::default(),
            partial_result_params: PartialResultParams::default(),
        },
    )
    .await
    .expect("documentLink request should not fail")
    .expect("import should produce at least one link");
    assert_eq!(links.len(), 1);
    assert_eq!(links[0].range.start, Position::new(0, 7));
}

#[tokio::test]
async fn test_code_lens_request_routes_to_provider() {
    let uri = Url::parse("file:///proj/Decls.lean").expect("uri should parse");
    let text = "def foo := 1\n";
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text.to_string(), "lean".to_string()),
    );
    backend.parse_document(&uri).await;

    let lenses = LanguageServer::code_lens(
        backend,
        CodeLensParams {
            text_document: TextDocumentIdentifier { uri: uri.clone() },
            work_done_progress_params: WorkDoneProgressParams::default(),
            partial_result_params: PartialResultParams::default(),
        },
    )
    .await
    .expect("codeLens request should not fail")
    .expect("a def should produce a lens");
    assert_eq!(lenses.len(), 1);
    // The routed request returns an unresolved lens (no command yet).
    assert!(
        lenses[0].command.is_none(),
        "routed codeLens should be unresolved"
    );

    // Routing the lens through codeLens/resolve fills in its command/title.
    let resolved = LanguageServer::code_lens_resolve(backend, lenses[0].clone())
        .await
        .expect("codeLens/resolve request should not fail");
    assert_eq!(
        resolved.command.as_ref().map(|cmd| cmd.title.as_str()),
        Some("def foo")
    );
}

#[tokio::test]
async fn test_initialize_advertises_document_link_and_code_lens_providers() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();

    let result = LanguageServer::initialize(backend, InitializeParams::default())
        .await
        .expect("initialize should succeed");

    let link_provider = result
        .capabilities
        .document_link_provider
        .expect("documentLink capability should be advertised");
    assert_eq!(
        link_provider.resolve_provider,
        Some(true),
        "documentLink uses the lazy resolve path"
    );

    let lens_provider = result
        .capabilities
        .code_lens_provider
        .expect("codeLens capability should be advertised");
    assert_eq!(
        lens_provider.resolve_provider,
        Some(true),
        "codeLens uses the lazy resolve path"
    );
}

/// `did_save` is implemented, so the sync capability must actually ASK for save
/// notifications. The scalar `TextDocumentSyncCapability::Kind` form carries no
/// `save` field, which tells a spec-conforming client not to send
/// `textDocument/didSave` at all — the handler existed but could never fire.
#[tokio::test]
async fn test_initialize_advertises_save_notifications() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();

    let result = LanguageServer::initialize(backend, InitializeParams::default())
        .await
        .expect("initialize should succeed");

    let sync = result
        .capabilities
        .text_document_sync
        .expect("textDocumentSync capability should be advertised");
    let options = match sync {
        TextDocumentSyncCapability::Options(options) => options,
        TextDocumentSyncCapability::Kind(kind) => panic!(
            "the scalar Kind({kind:?}) form cannot request save notifications; \
             did_save would never fire"
        ),
    };
    assert_eq!(
        options.change,
        Some(TextDocumentSyncKind::INCREMENTAL),
        "incremental sync must be preserved"
    );
    assert_eq!(options.open_close, Some(true));
    assert!(
        matches!(
            options.save,
            Some(TextDocumentSyncSaveOptions::Supported(true))
                | Some(TextDocumentSyncSaveOptions::SaveOptions(_))
        ),
        "save notifications must be requested: {:?}",
        options.save
    );
}

#[tokio::test]
async fn test_initialize_advertises_signature_help_and_workspace_symbol_providers() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();

    let result = LanguageServer::initialize(backend, InitializeParams::default())
        .await
        .expect("initialize should succeed");

    let signature_help = result
        .capabilities
        .signature_help_provider
        .expect("signatureHelp capability should be advertised");
    assert!(
        signature_help
            .trigger_characters
            .as_deref()
            .is_some_and(|chars| chars.iter().any(|c| c == "(")),
        "signatureHelp should retrigger on the opening parenthesis"
    );

    let workspace_symbol = result
        .capabilities
        .workspace_symbol_provider
        .expect("workspace/symbol capability should be advertised");
    assert!(
        matches!(workspace_symbol, OneOf::Left(true)),
        "workspace/symbol should be advertised as a simple boolean provider"
    );
}

// --- foldingRange ---------------------------------------------------------

/// Build the folding ranges for `text` through the pure helper used by the
/// live `textDocument/foldingRange` handler.
fn folding_ranges_for(text: &str) -> Vec<FoldingRange> {
    compute_folding_ranges(text)
}

fn has_region(ranges: &[FoldingRange], start: u32, end: u32) -> bool {
    ranges.iter().any(|r| {
        r.start_line == start && r.end_line == end && r.kind == Some(FoldingRangeKind::Region)
    })
}

fn has_comment(ranges: &[FoldingRange], start: u32, end: u32) -> bool {
    ranges.iter().any(|r| {
        r.start_line == start && r.end_line == end && r.kind == Some(FoldingRangeKind::Comment)
    })
}

#[test]
fn test_folding_multiline_definition_yields_region() {
    let text = "def foo : Nat :=\n  let x := 1\n  x + 1\n";
    let ranges = folding_ranges_for(text);
    assert!(
        has_region(&ranges, 0, 2),
        "multi-line def should fold lines 0..2, got {ranges:?}"
    );
}

#[test]
fn test_folding_single_line_definition_no_region() {
    let text = "def foo := 1\n";
    let ranges = folding_ranges_for(text);
    assert!(
        !ranges
            .iter()
            .any(|r| r.kind == Some(FoldingRangeKind::Region)),
        "single-line def must not produce a region fold, got {ranges:?}"
    );
}

#[test]
fn test_folding_namespace_block_yields_region() {
    let text = "namespace Foo\ndef a := 1\ndef b := 2\nend Foo\n";
    let ranges = folding_ranges_for(text);
    assert!(
        has_region(&ranges, 0, 3),
        "namespace block should fold from `namespace` to `end`, got {ranges:?}"
    );
}

#[test]
fn test_folding_block_comment_preserves_start_column() {
    // The `/-` opener is indented by four spaces; the fold must record that.
    let text = "def x := 1\n    /- a block\n       comment -/\ndef y := 2\n";
    let ranges = folding_ranges_for(text);
    let block = ranges
        .iter()
        .find(|r| r.kind == Some(FoldingRangeKind::Comment) && r.start_line == 1)
        .expect("a block-comment fold starting on line 1 should exist");
    assert_eq!(block.end_line, 2, "block comment should end on line 2");
    assert_eq!(
        block.start_character,
        Some(4),
        "fold should record the real opener column, not 0"
    );
}

#[test]
fn test_folding_single_line_block_comment_no_fold() {
    let text = "/- one liner -/\ndef y := 2\n";
    let ranges = folding_ranges_for(text);
    assert!(
        !ranges.iter().any(|r| {
            r.kind == Some(FoldingRangeKind::Comment) && r.start_line == 0 && r.end_line == 0
        }),
        "a single-line block comment must not fold, got {ranges:?}"
    );
}

#[test]
fn test_folding_consecutive_line_comments_fold() {
    let text = "-- line one\n-- line two\n-- line three\ndef y := 2\n";
    let ranges = folding_ranges_for(text);
    assert!(
        has_comment(&ranges, 0, 2),
        "three consecutive `--` lines should fold 0..2, got {ranges:?}"
    );
}

#[test]
fn test_folding_single_line_comment_no_fold() {
    let text = "-- lonely comment\ndef y := 2\n";
    let ranges = folding_ranges_for(text);
    assert!(
        !ranges
            .iter()
            .any(|r| r.kind == Some(FoldingRangeKind::Comment)),
        "a single `--` line must not fold, got {ranges:?}"
    );
}

#[test]
fn test_folding_trailing_line_comment_run_at_eof_folds() {
    // Run that extends to the end of the document with no closing line.
    let text = "def y := 2\n-- a\n-- b\n-- c";
    let ranges = folding_ranges_for(text);
    assert!(
        has_comment(&ranges, 1, 3),
        "EOF comment run should fold 1..3, got {ranges:?}"
    );
}

#[test]
fn test_folding_by_block_indentation_region() {
    let text = "theorem t : True := by\n  trivial\n  done\n";
    let ranges = folding_ranges_for(text);
    assert!(
        ranges.iter().any(|r| {
            r.kind == Some(FoldingRangeKind::Region) && r.start_line == 0 && r.end_line == 2
        }),
        "`by` tactic block should fold its indented body 0..2, got {ranges:?}"
    );
}

#[test]
fn test_folding_do_block_indentation_region() {
    let text = "def main : IO Unit := do\n  let x := 1\n  pure ()\nend\n";
    let ranges = folding_ranges_for(text);
    assert!(
        ranges
            .iter()
            .any(|r| r.kind == Some(FoldingRangeKind::Region)
                && r.start_line == 0
                && r.end_line == 2),
        "`do` block should fold its indented body 0..2, got {ranges:?}"
    );
}

#[test]
fn test_folding_match_with_block_indentation_region() {
    let text = "def f (n : Nat) := match n with\n  | 0 => 1\n  | _ => 2\n";
    let ranges = folding_ranges_for(text);
    assert!(
        ranges.iter().any(|r| {
            r.kind == Some(FoldingRangeKind::Region) && r.start_line == 0 && r.end_line == 2
        }),
        "`match … with` should fold its arms 0..2, got {ranges:?}"
    );
}

#[test]
fn test_folding_block_opener_keyword_in_identifier_does_not_fold() {
    // The header `#eval window` ends in the identifier `window` (letters
    // `dow`), not the standalone keyword `do`, and `#eval` is not a
    // declaration keyword, so no block must open here.
    let ranges = folding_ranges_for("#eval window\n  body\n  more\n");
    assert!(
        ranges.is_empty(),
        "identifier ending in `dow` must not open a `do` block, got {ranges:?}"
    );
}

#[test]
fn test_folding_real_do_keyword_header_opens_block() {
    // Control case for the previous test: a header ending in the real `do`
    // keyword must open an indentation block.
    let ranges = folding_ranges_for("#eval show IO Unit from do\n  pure ()\n  pure ()\n");
    assert!(
        ranges.iter().any(|r| {
            r.kind == Some(FoldingRangeKind::Region) && r.start_line == 0 && r.end_line == 2
        }),
        "a real `do` header should open a block 0..2, got {ranges:?}"
    );
}

#[test]
fn test_folding_empty_document_no_panic_and_empty() {
    let ranges = folding_ranges_for("");
    assert!(ranges.is_empty(), "empty document yields no folds");
}

#[test]
fn test_folding_garbage_document_no_panic() {
    // Non-Lean junk with mixed unicode must not panic and must not fold spuriously.
    let text = "}{ @@@ \u{1f600} ))) -- x\n???\n";
    let ranges = folding_ranges_for(text);
    // Just assert it returns without panicking; content is unconstrained.
    let _ = ranges;
}

#[tokio::test]
async fn test_folding_range_method_returns_none_for_unknown_document() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///missing.lean").unwrap();

    let result = LanguageServer::folding_range(
        backend,
        FoldingRangeParams {
            text_document: TextDocumentIdentifier { uri },
            work_done_progress_params: WorkDoneProgressParams::default(),
            partial_result_params: PartialResultParams::default(),
        },
    )
    .await
    .expect("folding_range should not fail for a missing document");
    assert!(
        result.is_none(),
        "an untracked document should yield None, not an empty list"
    );
}

#[tokio::test]
async fn test_folding_range_method_returns_regions_for_parsed_document() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///fold.lean").unwrap();
    let text = "namespace Demo\ndef foo : Nat :=\n  1\nend Demo\n".to_string();
    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text, "lean".to_string()),
    );
    backend.parse_document(&uri).await;

    let result = LanguageServer::folding_range(
        backend,
        FoldingRangeParams {
            text_document: TextDocumentIdentifier { uri },
            work_done_progress_params: WorkDoneProgressParams::default(),
            partial_result_params: PartialResultParams::default(),
        },
    )
    .await
    .expect("folding_range should not fail")
    .expect("a parsed multi-line document should yield folds");

    assert!(
        has_region(&result, 0, 3),
        "namespace Demo block should fold 0..3, got {result:?}"
    );
}

#[tokio::test]
async fn test_folding_range_capability_is_advertised() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let result = LanguageServer::initialize(backend, InitializeParams::default())
        .await
        .expect("initialize should not fail");
    assert!(
        matches!(
            result.capabilities.folding_range_provider,
            Some(FoldingRangeProviderCapability::Simple(true))
        ),
        "foldingRange should be advertised as a simple provider"
    );
    assert!(
        result.capabilities.call_hierarchy_provider.is_some(),
        "callHierarchy should be advertised"
    );
}

// --- textDocument/selectionRange ---------------------------------------------

/// Flatten a `SelectionRange` parent chain into a Vec ordered innermost-first.
/// Each successive range must be reachable via `.parent`.
fn flatten_selection_chain(mut node: &SelectionRange) -> Vec<Range> {
    let mut ranges = vec![node.range];
    while let Some(parent) = node.parent.as_deref() {
        ranges.push(parent.range);
        node = parent;
    }
    ranges
}

/// Issue a `selection_range` request for a single position against a freshly
/// parsed document and return the leaf hierarchy.
async fn request_selection_range(text: &str, position: Position) -> Option<SelectionRange> {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///selection.lean").expect("valid uri");
    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text.to_string(), "lean".to_string()),
    );
    backend.parse_document(&uri).await;

    let result = LanguageServer::selection_range(
        backend,
        SelectionRangeParams {
            text_document: TextDocumentIdentifier { uri },
            positions: vec![position],
            work_done_progress_params: WorkDoneProgressParams::default(),
            partial_result_params: PartialResultParams::default(),
        },
    )
    .await
    .expect("selection_range should not fail")
    .expect("a tracked document yields a hierarchy vec");

    result.into_iter().next()
}

#[tokio::test]
async fn test_selection_range_capability_is_advertised() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let result = LanguageServer::initialize(backend, InitializeParams::default())
        .await
        .expect("initialize should not fail");
    assert!(
        matches!(
            result.capabilities.selection_range_provider,
            Some(SelectionRangeProviderCapability::Simple(true))
        ),
        "selectionRange should be advertised as a simple provider"
    );
}

#[tokio::test]
async fn test_selection_range_unknown_document_returns_none() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///missing.lean").expect("valid uri");

    let result = LanguageServer::selection_range(
        backend,
        SelectionRangeParams {
            text_document: TextDocumentIdentifier { uri },
            positions: vec![Position::new(0, 0)],
            work_done_progress_params: WorkDoneProgressParams::default(),
            partial_result_params: PartialResultParams::default(),
        },
    )
    .await
    .expect("selection_range should not fail for a missing document");

    assert!(
        result.is_none(),
        "an untracked document yields None, not an empty list"
    );
}

#[tokio::test]
async fn test_selection_range_identifier_expands_to_command_then_document() {
    // Cursor on `foo` inside the body should expand: identifier -> command -> doc.
    let text = "def foo := bar\n";
    let position = Position::new(0, 12); // on the `bar` body identifier
    let leaf = request_selection_range(text, position)
        .await
        .expect("position yields a hierarchy");
    let chain = flatten_selection_chain(&leaf);

    // Innermost is the `bar` identifier (3 chars on line 0).
    assert_eq!(
        chain[0],
        Range {
            start: Position::new(0, 11),
            end: Position::new(0, 14),
        },
        "innermost range should be the `bar` identifier, got {chain:?}"
    );

    // Each level strictly contains the previous one.
    for window in chain.windows(2) {
        let (inner, outer) = (window[0], window[1]);
        assert!(
            outer.start <= inner.start && inner.end <= outer.end && inner != outer,
            "range {inner:?} must be strictly inside parent {outer:?}"
        );
    }

    // Outermost spans the whole document.
    let last = chain.last().expect("non-empty chain");
    assert_eq!(
        last.start,
        Position::new(0, 0),
        "outermost range starts at document origin, got {chain:?}"
    );
}

#[tokio::test]
async fn test_selection_range_includes_enclosing_bracket_pair() {
    // `def f := (a)` — cursor on `a` should expand to the `(a)` bracket pair
    // before reaching the command level.
    let text = "def f := (a)\n";
    let position = Position::new(0, 10); // on `a`
    let leaf = request_selection_range(text, position)
        .await
        .expect("position yields a hierarchy");
    let chain = flatten_selection_chain(&leaf);

    let bracket_range = Range {
        start: Position::new(0, 9), // '('
        end: Position::new(0, 12),  // one past ')'
    };
    assert!(
        chain.contains(&bracket_range),
        "selection chain should include the `(a)` pair {bracket_range:?}, got {chain:?}"
    );

    // The bracket pair must sit between the identifier and the command/document.
    let ident_idx = chain
        .iter()
        .position(|r| {
            *r == Range {
                start: Position::new(0, 10),
                end: Position::new(0, 11),
            }
        })
        .expect("`a` identifier present in chain");
    let bracket_idx = chain
        .iter()
        .position(|r| *r == bracket_range)
        .expect("bracket pair present in chain");
    assert!(
        bracket_idx > ident_idx,
        "bracket pair must be an ancestor of the identifier, got {chain:?}"
    );
}

#[tokio::test]
async fn test_selection_range_nested_brackets_order_innermost_first() {
    // `[(x)]` — cursor on `x` expands through `(x)` then `[(x)]`.
    let text = "def g := [(x)]\n";
    let position = Position::new(0, 11); // on `x`
    let leaf = request_selection_range(text, position)
        .await
        .expect("position yields a hierarchy");
    let chain = flatten_selection_chain(&leaf);

    let paren = Range {
        start: Position::new(0, 10),
        end: Position::new(0, 13),
    };
    let bracket = Range {
        start: Position::new(0, 9),
        end: Position::new(0, 14),
    };
    let paren_idx = chain.iter().position(|r| *r == paren);
    let bracket_idx = chain.iter().position(|r| *r == bracket);
    assert!(
        paren_idx.is_some() && bracket_idx.is_some(),
        "both `(x)` and `[(x)]` should appear, got {chain:?}"
    );
    assert!(
        paren_idx < bracket_idx,
        "inner `(x)` must precede outer `[(x)]` in the chain, got {chain:?}"
    );
}

#[tokio::test]
async fn test_selection_range_empty_document_yields_document_range() {
    // An empty document still yields a (zero-width) whole-document range so the
    // client receives a usable hierarchy rather than nothing.
    let leaf = request_selection_range("", Position::new(0, 0))
        .await
        .expect("empty document still yields a hierarchy");
    assert!(
        leaf.parent.is_none(),
        "empty document yields a single whole-document range, got {leaf:?}"
    );
    assert_eq!(leaf.range.start, Position::new(0, 0));
}

#[tokio::test]
async fn test_selection_range_garbage_document_no_panic() {
    // Unbalanced brackets and stray unicode must not panic and must still
    // produce a containment-respecting hierarchy.
    let text = "}{ ((( \u{1f600} ]] -- x\n???\n";
    let leaf = request_selection_range(text, Position::new(0, 4))
        .await
        .expect("garbage document still yields a hierarchy");
    let chain = flatten_selection_chain(&leaf);
    for window in chain.windows(2) {
        let (inner, outer) = (window[0], window[1]);
        assert!(
            outer.start <= inner.start && inner.end <= outer.end,
            "even for garbage input each parent must contain its child: {inner:?} in {outer:?}"
        );
    }
}

#[tokio::test]
async fn test_selection_range_multiple_positions_returns_one_chain_each() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///multi.lean").expect("valid uri");
    let text = "def a := 1\ndef b := 2\n";
    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text.to_string(), "lean".to_string()),
    );
    backend.parse_document(&uri).await;

    let result = LanguageServer::selection_range(
        backend,
        SelectionRangeParams {
            text_document: TextDocumentIdentifier { uri },
            positions: vec![Position::new(0, 4), Position::new(1, 4)],
            work_done_progress_params: WorkDoneProgressParams::default(),
            partial_result_params: PartialResultParams::default(),
        },
    )
    .await
    .expect("selection_range should not fail")
    .expect("tracked document yields a hierarchy vec");

    assert_eq!(
        result.len(),
        2,
        "one hierarchy is returned per requested position"
    );
    // First position is on line 0, second on line 1.
    assert_eq!(result[0].range.start.line, 0);
    assert_eq!(result[1].range.start.line, 1);
}

// ---------------------------------------------------------------------------
// textDocument/documentSymbol: name-precise selection_range + nested children
// ---------------------------------------------------------------------------

/// Parse `text` into a fresh backend and return the nested document-symbol tree.
async fn request_document_symbols(text: &str) -> Vec<DocumentSymbol> {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///symbols.lean").expect("valid uri");
    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text.to_string(), "lean".to_string()),
    );
    backend.parse_document(&uri).await;

    backend
        .get_document_symbols(&uri)
        .expect("a tracked document yields a symbol vec")
}

/// Extract the UTF-8 substring of `text` covered by an LSP `Range`, assuming a
/// single-line ASCII span (sufficient for these fixtures).
fn slice_range(text: &str, range: Range) -> String {
    let lines: Vec<&str> = text.split_inclusive('\n').collect();
    let start_line = lines.get(range.start.line as usize).copied().unwrap_or("");
    let s = range.start.character as usize;
    let e = range.end.character as usize;
    start_line.get(s..e).unwrap_or("").to_string()
}

/// A `selection_range` must always be contained within its `range`.
fn assert_selection_within_range(sym: &DocumentSymbol) {
    assert!(
        sym.range.start <= sym.selection_range.start && sym.selection_range.end <= sym.range.end,
        "selection_range {:?} must be contained in range {:?} for `{}`",
        sym.selection_range,
        sym.range,
        sym.name
    );
    if let Some(children) = &sym.children {
        for child in children {
            assert_selection_within_range(child);
        }
    }
}

#[tokio::test]
async fn test_document_symbol_selection_range_points_at_def_name() {
    let text = "def myFunction := 1\n";
    let symbols = request_document_symbols(text).await;

    assert_eq!(symbols.len(), 1, "one top-level def");
    let sym = &symbols[0];
    assert_eq!(sym.name, "myFunction");
    assert_eq!(sym.kind, SymbolKind::FUNCTION);
    assert_eq!(
        slice_range(text, sym.selection_range),
        "myFunction",
        "selection_range should cover exactly the name identifier"
    );
    // The full range is wider than the name.
    assert_ne!(sym.range, sym.selection_range);
    assert_selection_within_range(sym);
}

#[tokio::test]
async fn test_document_symbol_selection_range_points_at_theorem_name() {
    let text = "theorem myThm : True := trivial\n";
    let symbols = request_document_symbols(text).await;

    let sym = &symbols[0];
    assert_eq!(sym.name, "myThm");
    assert_eq!(
        slice_range(text, sym.selection_range),
        "myThm",
        "theorem selection_range should be the name"
    );
    assert_selection_within_range(sym);
}

#[tokio::test]
async fn test_document_symbol_selection_range_points_at_inductive_name() {
    let text = "inductive Color\n| red\n| green\n";
    let symbols = request_document_symbols(text).await;

    let sym = &symbols[0];
    assert_eq!(sym.name, "Color");
    assert_eq!(sym.kind, SymbolKind::CLASS);
    assert_eq!(
        slice_range(text, sym.selection_range),
        "Color",
        "inductive selection_range should be the type name"
    );
    assert_selection_within_range(sym);
}

#[tokio::test]
async fn test_document_symbol_namespace_nests_inner_defs_as_children() {
    let text = "namespace Foo\ndef a := 1\ndef b := 2\nend Foo\n";
    let symbols = request_document_symbols(text).await;

    assert_eq!(symbols.len(), 1, "namespace is a single top-level symbol");
    let ns = &symbols[0];
    assert_eq!(ns.name, "Foo");
    assert_eq!(ns.kind, SymbolKind::NAMESPACE);
    assert_eq!(
        slice_range(text, ns.selection_range),
        "Foo",
        "namespace selection_range should be the name"
    );

    let children = ns.children.as_ref().expect("namespace has children");
    let child_names: Vec<&str> = children.iter().map(|c| c.name.as_str()).collect();
    assert_eq!(child_names, vec!["a", "b"], "inner defs become children");
    for child in children {
        assert_eq!(child.kind, SymbolKind::FUNCTION);
    }
    assert_selection_within_range(ns);
}

#[tokio::test]
async fn test_document_symbol_structure_fields_are_children() {
    let text = "structure Point where\n  x : Nat\n  y : Nat\n";
    let symbols = request_document_symbols(text).await;

    let st = &symbols[0];
    assert_eq!(st.name, "Point");
    assert_eq!(st.kind, SymbolKind::CLASS);

    let fields = st.children.as_ref().expect("structure has field children");
    let field_names: Vec<&str> = fields.iter().map(|f| f.name.as_str()).collect();
    assert_eq!(field_names, vec!["x", "y"], "fields become children");
    for field in fields {
        assert_eq!(field.kind, SymbolKind::FIELD);
    }
    assert_selection_within_range(st);
}

#[tokio::test]
async fn test_document_symbol_recursive_namespace_nesting() {
    let text = "namespace A\nnamespace B\ndef c := 1\nend B\nend A\n";
    let symbols = request_document_symbols(text).await;

    assert_eq!(symbols.len(), 1, "single outer namespace");
    let a = &symbols[0];
    assert_eq!(a.name, "A");

    let a_children = a.children.as_ref().expect("A has children");
    assert_eq!(a_children.len(), 1, "A contains only B");
    let b = &a_children[0];
    assert_eq!(b.name, "B");
    assert_eq!(b.kind, SymbolKind::NAMESPACE);

    let b_children = b.children.as_ref().expect("B has children");
    assert_eq!(b_children.len(), 1);
    assert_eq!(b_children[0].name, "c");
    assert_eq!(b_children[0].kind, SymbolKind::FUNCTION);

    assert_selection_within_range(a);
}

#[tokio::test]
async fn test_document_symbol_flat_file_yields_flat_symbols() {
    let text = "def a := 1\ndef b := 2\ntheorem t : True := trivial\n";
    let symbols = request_document_symbols(text).await;

    assert_eq!(symbols.len(), 3, "three flat top-level symbols");
    let names: Vec<&str> = symbols.iter().map(|s| s.name.as_str()).collect();
    assert_eq!(names, vec!["a", "b", "t"]);
    for sym in &symbols {
        assert!(sym.children.is_none(), "flat declarations have no children");
        assert_selection_within_range(sym);
    }
}

#[tokio::test]
async fn test_document_symbol_empty_file_yields_empty_symbols() {
    let symbols = request_document_symbols("").await;
    assert!(symbols.is_empty(), "empty file has no symbols");
}

// --- textDocument/prepareTypeHierarchy + typeHierarchy/super|subtypes --------

/// Open `text` in a fresh backend under `uri`, parse and elaborate it, and
/// return the owning `LspService` so type-hierarchy requests can be issued
/// against `service.inner()` (which borrows from the returned value).
async fn type_hierarchy_service(uri: &Url, text: &str) -> LspService<CleanBackend> {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text.to_string(), "lean".to_string()),
    );
    backend.parse_document(uri).await;
    backend.elaborate_document(uri).await;
    service
}

#[tokio::test]
async fn test_prepare_type_hierarchy_on_structure_returns_item() {
    let uri = Url::parse("file:///th-struct.lean").unwrap();
    let text = "structure Point where\n  x : Nat\n";
    let service = type_hierarchy_service(&uri, text).await;
    let backend = service.inner();

    let off = text.find("Point").expect("name present");
    let position = {
        let doc = backend.documents.get(&uri).unwrap();
        doc.offset_to_position(off)
    };

    let items = LanguageServer::prepare_type_hierarchy(
        backend,
        TypeHierarchyPrepareParams {
            text_document_position_params: TextDocumentPositionParams {
                text_document: TextDocumentIdentifier { uri: uri.clone() },
                position,
            },
            work_done_progress_params: WorkDoneProgressParams::default(),
        },
    )
    .await
    .expect("prepare_type_hierarchy should not fail")
    .expect("a structure should produce a type hierarchy item");

    assert_eq!(items.len(), 1);
    assert_eq!(items[0].name, "Point");
    assert_eq!(items[0].uri, uri);
    assert_eq!(items[0].kind, SymbolKind::CLASS);
}

#[tokio::test]
async fn test_prepare_type_hierarchy_on_plain_def_returns_none() {
    let uri = Url::parse("file:///th-def.lean").unwrap();
    let text = "def notAType := 1\n";
    let service = type_hierarchy_service(&uri, text).await;
    let backend = service.inner();

    let off = text.find("notAType").expect("name present");
    let position = {
        let doc = backend.documents.get(&uri).unwrap();
        doc.offset_to_position(off)
    };

    let result = LanguageServer::prepare_type_hierarchy(
        backend,
        TypeHierarchyPrepareParams {
            text_document_position_params: TextDocumentPositionParams {
                text_document: TextDocumentIdentifier { uri: uri.clone() },
                position,
            },
            work_done_progress_params: WorkDoneProgressParams::default(),
        },
    )
    .await
    .expect("prepare_type_hierarchy should not fail");

    assert!(
        result.is_none(),
        "a plain `def` is not a type-hierarchy node"
    );
}

#[tokio::test]
async fn test_type_hierarchy_supertypes_reports_structure_extends_parent() {
    let uri = Url::parse("file:///th-extends.lean").unwrap();
    let text = "structure Point where\n  x : Nat\nstructure ColorPoint extends Point where\n  color : Nat\n";
    let service = type_hierarchy_service(&uri, text).await;
    let backend = service.inner();

    let child_info = backend
        .definitions
        .get("ColorPoint")
        .expect("ColorPoint should be indexed");
    let child = backend
        .make_type_hierarchy_item("ColorPoint", child_info.value())
        .expect("child item should build");
    drop(child_info);

    let supertypes = LanguageServer::supertypes(
        backend,
        TypeHierarchySupertypesParams {
            item: child,
            work_done_progress_params: WorkDoneProgressParams::default(),
            partial_result_params: PartialResultParams::default(),
        },
    )
    .await
    .expect("supertypes should not fail")
    .expect("supertypes should return Some");

    let names: Vec<&str> = supertypes.iter().map(|i| i.name.as_str()).collect();
    assert_eq!(names, vec!["Point"], "ColorPoint extends Point");
}

#[tokio::test]
async fn test_type_hierarchy_subtypes_reports_extending_structure() {
    let uri = Url::parse("file:///th-subtypes.lean").unwrap();
    let text = "structure Point where\n  x : Nat\nstructure ColorPoint extends Point where\n  color : Nat\n";
    let service = type_hierarchy_service(&uri, text).await;
    let backend = service.inner();

    let parent_info = backend
        .definitions
        .get("Point")
        .expect("Point should be indexed");
    let parent = backend
        .make_type_hierarchy_item("Point", parent_info.value())
        .expect("parent item should build");
    drop(parent_info);

    let subtypes = LanguageServer::subtypes(
        backend,
        TypeHierarchySubtypesParams {
            item: parent,
            work_done_progress_params: WorkDoneProgressParams::default(),
            partial_result_params: PartialResultParams::default(),
        },
    )
    .await
    .expect("subtypes should not fail")
    .expect("subtypes should return Some");

    let names: Vec<&str> = subtypes.iter().map(|i| i.name.as_str()).collect();
    assert_eq!(
        names,
        vec!["ColorPoint"],
        "ColorPoint is a subtype of Point"
    );
}

#[tokio::test]
async fn test_type_hierarchy_instance_supertype_is_its_class() {
    let uri = Url::parse("file:///th-instance.lean").unwrap();
    // A class plus a named instance of that class. The instance's supertype is
    // the class it implements; the class's subtype is the instance.
    let text = "class Greet where\n  greet : Nat\ninstance instGreet : Greet where\n  greet := 0\n";
    let service = type_hierarchy_service(&uri, text).await;
    let backend = service.inner();

    let inst_info = backend
        .definitions
        .get("instGreet")
        .expect("instGreet should be indexed");
    let inst = backend
        .make_type_hierarchy_item("instGreet", inst_info.value())
        .expect("instance item should build");
    drop(inst_info);

    let supertypes = LanguageServer::supertypes(
        backend,
        TypeHierarchySupertypesParams {
            item: inst,
            work_done_progress_params: WorkDoneProgressParams::default(),
            partial_result_params: PartialResultParams::default(),
        },
    )
    .await
    .expect("supertypes should not fail")
    .expect("supertypes should return Some");
    let super_names: Vec<&str> = supertypes.iter().map(|i| i.name.as_str()).collect();
    assert_eq!(super_names, vec!["Greet"], "instance implements Greet");

    // Reverse edge: the class's subtypes include the instance.
    let class_info = backend
        .definitions
        .get("Greet")
        .expect("Greet should be indexed");
    let class_item = backend
        .make_type_hierarchy_item("Greet", class_info.value())
        .expect("class item should build");
    drop(class_info);

    let subtypes = LanguageServer::subtypes(
        backend,
        TypeHierarchySubtypesParams {
            item: class_item,
            work_done_progress_params: WorkDoneProgressParams::default(),
            partial_result_params: PartialResultParams::default(),
        },
    )
    .await
    .expect("subtypes should not fail")
    .expect("subtypes should return Some");
    let sub_names: Vec<&str> = subtypes.iter().map(|i| i.name.as_str()).collect();
    assert_eq!(
        sub_names,
        vec!["instGreet"],
        "Greet's subtype is its instance"
    );
}

#[tokio::test]
async fn test_type_hierarchy_leaf_structure_has_no_super_or_subtypes() {
    let uri = Url::parse("file:///th-leaf.lean").unwrap();
    let text = "structure Solo where\n  x : Nat\n";
    let service = type_hierarchy_service(&uri, text).await;
    let backend = service.inner();

    let info = backend
        .definitions
        .get("Solo")
        .expect("Solo should be indexed");
    let item = backend
        .make_type_hierarchy_item("Solo", info.value())
        .expect("item should build");
    drop(info);

    let supertypes = LanguageServer::supertypes(
        backend,
        TypeHierarchySupertypesParams {
            item: item.clone(),
            work_done_progress_params: WorkDoneProgressParams::default(),
            partial_result_params: PartialResultParams::default(),
        },
    )
    .await
    .expect("supertypes should not fail")
    .expect("supertypes should return Some");
    assert!(
        supertypes.is_empty(),
        "a structure with no `extends` has no supertypes"
    );

    let subtypes = LanguageServer::subtypes(
        backend,
        TypeHierarchySubtypesParams {
            item,
            work_done_progress_params: WorkDoneProgressParams::default(),
            partial_result_params: PartialResultParams::default(),
        },
    )
    .await
    .expect("subtypes should not fail")
    .expect("subtypes should return Some");
    assert!(
        subtypes.is_empty(),
        "a structure nothing extends has no subtypes"
    );
}

#[tokio::test]
async fn test_initialize_advertises_type_hierarchy_provider() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();

    let result = LanguageServer::initialize(backend, InitializeParams::default())
        .await
        .expect("initialize should succeed");

    let experimental = result
        .capabilities
        .experimental
        .expect("experimental capabilities should be advertised");
    assert_eq!(
        experimental.get("typeHierarchyProvider"),
        Some(&serde_json::Value::Bool(true)),
        "typeHierarchy support is advertised via experimental.typeHierarchyProvider"
    );
}

#[tokio::test]
async fn test_elaboration_records_widget_module_attribute_decl() {
    // A `@[widget_module]`-decorated declaration is recorded as a user widget
    // module during elaboration, flips the live-state probe to true, and is
    // surfaced through the `getWidgets` RPC as a dedicated user-widget panel.
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///user-widget.lean").unwrap();
    // Use an axiom-form widget module so the declaration elaborates cleanly in
    // the fresh server environment (numeric-literal `def` bodies need `Init`'s
    // `OfNat`, which is not loaded here). `@[widget_module]` detection covers
    // axioms as well as defs; the canonical `def` syntax is pinned by the
    // parser-level `test_is_widget_module_decl_detects_attribute` test.
    let text = "@[widget_module] axiom myPanel : Nat\n".to_string();

    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text, "lean".to_string()),
    );
    backend.parse_document(&uri).await;
    backend.elaborate_document(&uri).await;

    let elaborated = backend
        .documents
        .get(&uri)
        .and_then(|doc| doc.elaborated.clone())
        .expect("live check should store elaboration state");
    assert!(
        elaborated.errors.is_empty(),
        "widget-module decl should elaborate cleanly, got {:?}",
        elaborated.errors
    );
    assert_eq!(
        elaborated.widget_modules.len(),
        1,
        "the `@[widget_module]` decl should be recorded once, got {:?}",
        elaborated.widget_modules
    );
    assert_eq!(elaborated.widget_modules[0].name, "myPanel");

    assert!(
        backend.has_live_user_widget_modules(),
        "a recorded widget module flips the live-state probe to true"
    );

    let query_position = backend
        .documents
        .get(&uri)
        .map(|doc| doc.offset_to_position(elaborated.widget_modules[0].start))
        .expect("document should remain open");

    let connected = backend
        .rpc_connect(crate::rpc::RpcConnectParams { uri: uri.clone() })
        .unwrap();
    let widgets_value = backend
        .rpc_call(crate::rpc::RpcCallParams {
            text_document: crate::rpc::TextDocumentIdentifier { uri: uri.clone() },
            position: query_position,
            session_id: connected.session_id,
            method: "Lean.Widget.getWidgets".to_string(),
            params: serde_json::Value::Null,
        })
        .unwrap();
    let widgets: crate::rpc::GetWidgetsResponse = serde_json::from_value(widgets_value).unwrap();

    let user_widget = widgets
        .widgets
        .iter()
        .find(|widget| widget.id == USER_WIDGET_PANEL_ID)
        .expect("getWidgets should include the user-defined widget module panel");
    assert_eq!(user_widget.javascript_hash, USER_WIDGET_PANEL_HASH);
    assert_eq!(user_widget.props["module"], "myPanel");

    // The shared user-widget JS source is registered and retrievable.
    let source_value = backend
        .rpc_call(crate::rpc::RpcCallParams {
            text_document: crate::rpc::TextDocumentIdentifier { uri },
            position: query_position,
            session_id: connected.session_id,
            method: "Lean.Widget.getWidgetSource".to_string(),
            params: serde_json::json!({
                "hash": USER_WIDGET_PANEL_HASH.to_string(),
                "pos": query_position
            }),
        })
        .unwrap();
    let source: WidgetSource = serde_json::from_value(source_value).unwrap();
    assert!(
        source.sourcetext.contains("UserWidgetModule"),
        "user-widget source should be registered, got {:?}",
        source.sourcetext
    );
}

#[tokio::test]
async fn test_elaboration_without_widget_module_reports_no_user_widgets() {
    // Control: a plain declaration records no widget modules, keeps the
    // live-state probe false, and getWidgets carries no user-widget panel.
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///no-user-widget.lean").unwrap();
    let text = "axiom plain : Nat\n".to_string();

    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text, "lean".to_string()),
    );
    backend.parse_document(&uri).await;
    backend.elaborate_document(&uri).await;

    let elaborated = backend
        .documents
        .get(&uri)
        .and_then(|doc| doc.elaborated.clone())
        .expect("live check should store elaboration state");
    assert!(
        elaborated.widget_modules.is_empty(),
        "a plain def records no widget modules, got {:?}",
        elaborated.widget_modules
    );
    assert!(
        !backend.has_live_user_widget_modules(),
        "no widget module keeps the live-state probe false"
    );

    let query_position = backend
        .documents
        .get(&uri)
        .map(|doc| doc.offset_to_position(0))
        .expect("document should remain open");

    let connected = backend
        .rpc_connect(crate::rpc::RpcConnectParams { uri: uri.clone() })
        .unwrap();
    let widgets_value = backend
        .rpc_call(crate::rpc::RpcCallParams {
            text_document: crate::rpc::TextDocumentIdentifier { uri },
            position: query_position,
            session_id: connected.session_id,
            method: "Lean.Widget.getWidgets".to_string(),
            params: serde_json::Value::Null,
        })
        .unwrap();
    let widgets: crate::rpc::GetWidgetsResponse = serde_json::from_value(widgets_value).unwrap();
    assert!(
        widgets
            .widgets
            .iter()
            .all(|widget| widget.id != USER_WIDGET_PANEL_ID),
        "no user-widget panel should be emitted without a `@[widget_module]` decl"
    );
}

#[test]
fn test_is_widget_module_decl_detects_attribute() {
    // Pin the attribute detection at the parser level: `@[widget_module]`
    // arrives as `Attribute::Unknown("widget_module")` and must be recognized,
    // while an undecorated def and an unrelated attribute must not be.
    let patterns = CleanBackend::builtin_tactic_patterns();

    let widget =
        clean_parser::parse_file_with_tactics("@[widget_module] def w : Nat := 0\n", &patterns)
            .expect("widget def should parse");
    assert!(
        CleanBackend::is_widget_module_decl(&widget[0]),
        "a `@[widget_module]` def is a widget module declaration"
    );

    let widget_axiom =
        clean_parser::parse_file_with_tactics("@[widget_module] axiom w : Nat\n", &patterns)
            .expect("widget axiom should parse");
    assert!(
        CleanBackend::is_widget_module_decl(&widget_axiom[0]),
        "a `@[widget_module]` axiom is also recognized (attribute attaches to axiom attrs)"
    );

    let plain = clean_parser::parse_file_with_tactics("def w : Nat := 0\n", &patterns)
        .expect("plain def should parse");
    assert!(
        !CleanBackend::is_widget_module_decl(&plain[0]),
        "an undecorated def is not a widget module declaration"
    );

    let other = clean_parser::parse_file_with_tactics("@[simp] def w : Nat := 0\n", &patterns)
        .expect("simp def should parse");
    assert!(
        !CleanBackend::is_widget_module_decl(&other[0]),
        "an unrelated attribute is not a widget module declaration"
    );
}

// ---------------------------------------------------------------------------
// Interactive goals on the LSP RPC channel
// (Lean.Widget.getInteractiveGoals / getInteractiveTermGoal)
// ---------------------------------------------------------------------------

#[test]
fn test_rpc_call_get_interactive_goals_returns_hypothesis_bundles_for_fixture_theorem() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///interactive-goals-fixture.lean").unwrap();
    let text = "theorem demo : True := by\n  trivial\n".to_string();
    let mut doc = Document::new(uri.clone(), 1, text, "lean".to_string());
    doc.elaborated = Some(ElaboratedDocument {
        errors: vec![],
        warnings: vec![],
        declarations: vec![ElaboratedDecl {
            identity: clean_kernel::Name::anon().str("demo"),
            name: "demo".to_string(),
            type_str: "True".to_string(),
            start: 0,
            end: "theorem demo : True := by\n  trivial".len(),
        }],
        term_infos: Vec::new(),
        holes: vec![],
        widget_modules: vec![],
    });
    backend.documents.insert(uri.clone(), doc);
    backend.tactic_goal_snapshots.insert(
        uri.clone(),
        vec![TacticGoalSnapshot {
            range: Range::new(Position::new(1, 2), Position::new(1, 9)),
            goals: vec!["h : False\n⊢ True".to_string()],
        }],
    );

    // Drive the real LSP RPC surface: connect, then call the method.
    let connected = backend
        .rpc_connect(crate::rpc::RpcConnectParams { uri: uri.clone() })
        .expect("rpc connect should start a session");
    let result = backend.rpc_call(crate::rpc::RpcCallParams {
        text_document: crate::rpc::TextDocumentIdentifier { uri: uri.clone() },
        position: Position::new(1, 4),
        session_id: connected.session_id,
        method: "Lean.Widget.getInteractiveGoals".to_string(),
        params: serde_json::Value::Null,
    });

    let value = match result {
        Ok(value) => value,
        Err(err) => panic!(
            "getInteractiveGoals must be registered on the LSP channel \
             (must not be -32601 Method not found): {err:?}"
        ),
    };
    let goals: InteractiveGoals =
        serde_json::from_value(value).expect("response should be a structured InteractiveGoals");
    assert_eq!(
        goals.goals.len(),
        1,
        "one tactic goal covers the requested position"
    );
    assert_eq!(goals.goals[0].type_, "True");
    assert_eq!(
        goals.goals[0].hyps.len(),
        1,
        "the goal should carry a structured hypothesis bundle, not a plain string"
    );
    assert_eq!(goals.goals[0].hyps[0].names, ["h"]);
    assert_eq!(goals.goals[0].hyps[0].type_, "False");

    // Outside the snapshot range the endpoint stays fail-closed (null).
    let outside = backend
        .rpc_call(crate::rpc::RpcCallParams {
            text_document: crate::rpc::TextDocumentIdentifier { uri },
            position: Position::new(0, 0),
            session_id: connected.session_id,
            method: "Lean.Widget.getInteractiveGoals".to_string(),
            params: serde_json::Value::Null,
        })
        .expect("out-of-range call should still succeed");
    assert!(
        outside.is_null(),
        "positions without live tactic goal state must return null, got {outside}"
    );
}

#[test]
fn test_rpc_call_get_interactive_term_goal_prefers_hole_context_over_declaration() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///interactive-term-goal.lean").unwrap();
    let text = "def foo : Nat := _\n".to_string();
    let hole_start = text.find('_').unwrap();
    let mut doc = Document::new(uri.clone(), 1, text, "lean".to_string());
    doc.elaborated = Some(ElaboratedDocument {
        errors: vec![],
        warnings: vec![],
        declarations: vec![ElaboratedDecl {
            identity: clean_kernel::Name::anon().str("foo"),
            name: "foo".to_string(),
            type_str: "Nat".to_string(),
            start: 0,
            end: hole_start + 1,
        }],
        term_infos: Vec::new(),
        holes: vec![crate::document::HoleContext {
            start: hole_start,
            end: hole_start + 1,
            expected_type: "Nat".to_string(),
            local_bindings: vec![("n".to_string(), "Nat".to_string())],
        }],
        widget_modules: vec![],
    });
    backend.documents.insert(uri.clone(), doc);

    let connected = backend
        .rpc_connect(crate::rpc::RpcConnectParams { uri: uri.clone() })
        .expect("rpc connect should start a session");

    // On the hole: the hole-local expected type with its local context wins.
    let on_hole = backend
        .rpc_call(crate::rpc::RpcCallParams {
            text_document: crate::rpc::TextDocumentIdentifier { uri: uri.clone() },
            position: Position::new(0, u32::try_from(hole_start).unwrap()),
            session_id: connected.session_id,
            method: "Lean.Widget.getInteractiveTermGoal".to_string(),
            params: serde_json::Value::Null,
        })
        .expect("getInteractiveTermGoal must be registered on the LSP channel");
    let hole_goal: InteractiveTermGoal =
        serde_json::from_value(on_hole).expect("response should be a structured term goal");
    assert_eq!(hole_goal.type_, "Nat");
    assert_eq!(
        hole_goal.hyps.len(),
        1,
        "hole-local hypotheses should surface as structured bundles"
    );
    assert_eq!(hole_goal.hyps[0].names, ["n"]);

    // Inside the declaration but off the hole: the declaration type, no hyps.
    let on_decl = backend
        .rpc_call(crate::rpc::RpcCallParams {
            text_document: crate::rpc::TextDocumentIdentifier { uri },
            position: Position::new(0, 4),
            session_id: connected.session_id,
            method: "Lean.Widget.getInteractiveTermGoal".to_string(),
            params: serde_json::Value::Null,
        })
        .expect("declaration-range call should succeed");
    let decl_goal: InteractiveTermGoal =
        serde_json::from_value(on_decl).expect("response should be a structured term goal");
    assert_eq!(decl_goal.type_, "Nat");
    assert!(
        decl_goal.hyps.is_empty(),
        "a declaration-level term goal has no hole-local hypotheses"
    );
}

#[test]
fn test_refresh_infoview_goals_clears_stale_goal_state_when_snapshots_removed() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///interactive-goals-stale.lean").unwrap();
    let text = "theorem demo : True := by\n  trivial\n".to_string();
    let mut doc = Document::new(uri.clone(), 1, text, "lean".to_string());
    doc.elaborated = Some(ElaboratedDocument {
        errors: vec![],
        warnings: vec![],
        declarations: vec![],
        term_infos: Vec::new(),
        holes: vec![],
        widget_modules: vec![],
    });
    backend.documents.insert(uri.clone(), doc);
    backend.tactic_goal_snapshots.insert(
        uri.clone(),
        vec![TacticGoalSnapshot {
            range: Range::new(Position::new(1, 2), Position::new(1, 9)),
            goals: vec!["⊢ True".to_string()],
        }],
    );

    let connected = backend
        .rpc_connect(crate::rpc::RpcConnectParams { uri: uri.clone() })
        .expect("rpc connect should start a session");
    let live = backend
        .rpc_call(crate::rpc::RpcCallParams {
            text_document: crate::rpc::TextDocumentIdentifier { uri: uri.clone() },
            position: Position::new(1, 4),
            session_id: connected.session_id,
            method: "Lean.Widget.getInteractiveGoals".to_string(),
            params: serde_json::Value::Null,
        })
        .expect("live snapshot call should succeed");
    assert!(!live.is_null(), "live snapshot should produce goals");

    // Snapshot state disappears (e.g. re-elaboration removed it): the next
    // call must refresh the registry and fail closed instead of serving
    // stale goals.
    backend.tactic_goal_snapshots.remove(&uri);
    let stale = backend
        .rpc_call(crate::rpc::RpcCallParams {
            text_document: crate::rpc::TextDocumentIdentifier { uri },
            position: Position::new(1, 4),
            session_id: connected.session_id,
            method: "Lean.Widget.getInteractiveGoals".to_string(),
            params: serde_json::Value::Null,
        })
        .expect("call after snapshot removal should still succeed");
    assert!(
        stale.is_null(),
        "removed snapshots must not leave stale interactive goals behind"
    );
}

fn real_tactic_observations_for_commit(
    text: &str,
) -> Vec<clean_elab::tactic::TacticGoalObservation> {
    let (progress, _receiver) = tokio::sync::mpsc::unbounded_channel();
    let (_, _, _, observations) = CleanBackend::elaborate_text_blocking(
        text,
        IncrementalState::default(),
        None,
        &CleanBackend::builtin_tactic_patterns(),
        clean_kernel::Environment::new(),
        &progress,
    );
    assert!(
        !observations.is_empty(),
        "commit control must exercise actual producer data"
    );
    observations
}

#[tokio::test]
async fn test_commit_elaboration_discards_stale_version_result() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///commit-stale.lean").unwrap();
    let text = "theorem demo : True := by\n  trivial\n";
    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 2, text.to_string(), "lean".to_string()),
    );

    // A result computed against version 1 lands while the document is already
    // at version 2: the newer didChange run owns the elaborated state.
    let committed = backend.commit_elaboration(
        &uri,
        1,
        text,
        ElaboratedDocument {
            errors: vec![],
            warnings: vec![],
            declarations: vec![],
            term_infos: Vec::new(),
            holes: vec![],
            widget_modules: vec![],
        },
        IncrementalState::default(),
        real_tactic_observations_for_commit(text),
        None,
    );

    assert!(!committed, "stale-version commit must be refused");
    let doc = backend
        .documents
        .get(&uri)
        .expect("document should remain open");
    assert!(
        doc.elaborated.is_none(),
        "a stale result must not be stored on the document"
    );
    assert!(
        backend.tactic_goal_snapshots.get(&uri).is_none(),
        "a stale result must not install tactic snapshots"
    );
}

#[tokio::test]
async fn test_commit_elaboration_stores_result_at_matching_version() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///commit-current.lean").unwrap();
    let text = "theorem demo : True := by\n  trivial\n";
    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 3, text.to_string(), "lean".to_string()),
    );

    let committed = backend.commit_elaboration(
        &uri,
        3,
        text,
        ElaboratedDocument {
            errors: vec![],
            warnings: vec![],
            declarations: vec![],
            term_infos: Vec::new(),
            holes: vec![],
            widget_modules: vec![],
        },
        IncrementalState::default(),
        real_tactic_observations_for_commit(text),
        None,
    );

    assert!(committed, "matching-version commit must be stored");
    let doc = backend
        .documents
        .get(&uri)
        .expect("document should remain open");
    assert!(
        doc.elaborated.is_some(),
        "the committed result must be stored on the document"
    );
    assert!(
        backend.tactic_goal_snapshots.get(&uri).is_some(),
        "commit should retain the actual by-block tactic observations"
    );
}

// --- Per-URI background elaboration (unfreeze plan deferred item C) ---
//
// The stale-version commit tests above cover mechanism 1 (version check at
// commit); the tests below cover mechanism 2 (per-URI generation counter)
// and mechanism 3 (task-handle tracking / abort), plus the end-to-end
// ordering contract: parse-first inline, elaboration in the background, and
// reads racing the background task served from the last committed snapshot.

/// A guard whose drop sets a flag: the externally observable effect of
/// `JoinHandle::abort` on a task that never completes on its own is that its
/// future (and thus this guard) is dropped.
struct DropFlag(Arc<std::sync::atomic::AtomicBool>);

impl Drop for DropFlag {
    fn drop(&mut self) {
        self.0.store(true, std::sync::atomic::Ordering::SeqCst);
    }
}

/// Spawn a stand-in for an in-flight elaboration task: it never finishes on
/// its own (`pending()`), so only an abort can end it, observed via the
/// returned flag.
fn spawn_pending_task() -> (
    tokio::task::JoinHandle<()>,
    Arc<std::sync::atomic::AtomicBool>,
) {
    let dropped = Arc::new(std::sync::atomic::AtomicBool::new(false));
    let guard = DropFlag(dropped.clone());
    let task = tokio::spawn(async move {
        let _guard = guard;
        std::future::pending::<()>().await;
    });
    (task, dropped)
}

/// Yield until `flag` is set or a generous yield budget runs out: the
/// current-thread test runtime needs scheduler passes to drop an aborted
/// task.
async fn yield_until_set(flag: &std::sync::atomic::AtomicBool) {
    for _ in 0..256 {
        if flag.load(std::sync::atomic::Ordering::SeqCst) {
            return;
        }
        tokio::task::yield_now().await;
    }
}

/// Extract the markdown payload of a hover produced by `get_hover_at`.
fn hover_markup_value(hover: &Hover) -> &str {
    match &hover.contents {
        HoverContents::Markup(markup) => &markup.value,
        other => panic!("hover should carry markup contents, got {other:?}"),
    }
}

#[tokio::test]
async fn test_elaboration_generation_bump_supersedes_older_generation() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///generation-bump.lean").unwrap();

    let first = backend.bump_elaboration_generation(&uri);
    assert!(
        backend.elaboration_generation_is_current(&uri, first),
        "a freshly bumped generation must be current"
    );

    let second = backend.bump_elaboration_generation(&uri);
    assert!(second > first, "generations must increase monotonically");
    assert!(
        !backend.elaboration_generation_is_current(&uri, first),
        "an older generation must read as superseded after a newer bump"
    );
    assert!(
        backend.elaboration_generation_is_current(&uri, second),
        "the newest generation must be current"
    );

    let unseen = Url::parse("file:///generation-unseen.lean").unwrap();
    assert!(
        !backend.elaboration_generation_is_current(&unseen, second),
        "a URI with no scheduled check has no current generation"
    );
}

#[tokio::test]
async fn test_bump_elaboration_generation_aborts_in_flight_task() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///generation-abort.lean").unwrap();

    let generation = backend.bump_elaboration_generation(&uri);
    let (task, dropped) = spawn_pending_task();
    backend.register_elaboration_task(&uri, generation, task);
    assert!(
        backend
            .elaboration_tasks
            .get(&uri)
            .is_some_and(|slot| slot.task.is_some()),
        "a current-generation task must be tracked in the slot"
    );

    let newer = backend.bump_elaboration_generation(&uri);
    yield_until_set(&dropped).await;
    assert!(
        dropped.load(std::sync::atomic::Ordering::SeqCst),
        "the superseding bump must abort the tracked in-flight task"
    );
    assert!(
        backend
            .elaboration_tasks
            .get(&uri)
            .is_some_and(|slot| slot.task.is_none()),
        "the aborted task's handle must be taken out of the slot"
    );
    assert!(
        backend.elaboration_generation_is_current(&uri, newer),
        "the superseding generation must remain current after the abort"
    );
}

#[tokio::test]
async fn test_register_elaboration_task_stale_generation_aborts_task() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///generation-stale-register.lean").unwrap();

    // tower-lsp runs notification handlers concurrently: a newer didChange
    // can bump the generation between an older handler's bump and its task
    // registration. The late registration must abort, not store.
    let first = backend.bump_elaboration_generation(&uri);
    let second = backend.bump_elaboration_generation(&uri);
    let (task, dropped) = spawn_pending_task();
    backend.register_elaboration_task(&uri, first, task);

    assert!(
        backend
            .elaboration_tasks
            .get(&uri)
            .is_some_and(|slot| slot.task.is_none()),
        "a task registered under a superseded generation must not be stored"
    );
    yield_until_set(&dropped).await;
    assert!(
        dropped.load(std::sync::atomic::Ordering::SeqCst),
        "a task registered under a superseded generation must be aborted"
    );
    assert!(
        backend.elaboration_generation_is_current(&uri, second),
        "the stale registration must not disturb the current generation"
    );
}

#[tokio::test]
async fn test_did_close_discards_in_flight_elaboration_task() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///close-discard.lean").unwrap();
    backend.documents.insert(
        uri.clone(),
        Document::new(
            uri.clone(),
            1,
            "def x := 1\n".to_string(),
            "lean".to_string(),
        ),
    );

    let generation = backend.bump_elaboration_generation(&uri);
    let (task, dropped) = spawn_pending_task();
    backend.register_elaboration_task(&uri, generation, task);

    backend
        .did_close(DidCloseTextDocumentParams {
            text_document: TextDocumentIdentifier { uri: uri.clone() },
        })
        .await;

    assert!(
        backend.elaboration_tasks.get(&uri).is_none(),
        "didClose must remove the URI's elaboration slot"
    );
    yield_until_set(&dropped).await;
    assert!(
        dropped.load(std::sync::atomic::Ordering::SeqCst),
        "didClose must abort the in-flight background task"
    );
    assert!(
        !backend.elaboration_generation_is_current(&uri, generation),
        "no generation is current for a closed document, so a still-running task skips its publishes"
    );
}

/// Deferred item C, end-to-end: after `didChange` returns, elaboration is a
/// spawned background task, and a hover in that window answers from the
/// previous version's committed snapshot instead of blocking or going dark.
///
/// Determinism: `#[tokio::test]` runs a current-thread runtime, so the task
/// spawned at the end of `didChange` cannot be polled until this test next
/// awaits — the hover below is therefore provably inside the race window.
#[tokio::test]
async fn test_hover_during_background_elaboration_serves_previous_snapshot() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///background-hover.lean").unwrap();

    backend
        .did_open(DidOpenTextDocumentParams {
            text_document: TextDocumentItem {
                uri: uri.clone(),
                language_id: "lean".to_string(),
                version: 1,
                text: "axiom alpha_marker : Nat\n".to_string(),
            },
        })
        .await;
    backend.wait_for_elaboration(&uri).await;

    // Derive the hover position from the elaborated declaration itself (the
    // hover-precedent idiom) — hardcoded columns silently miss when the
    // declaration's recorded range differs from eyeballed source offsets.
    let query_position = {
        let doc = backend
            .documents
            .get(&uri)
            .expect("document should remain open");
        let decl = doc
            .elaborated
            .as_ref()
            .and_then(|e| e.declarations.first())
            .expect("v1 elaboration should record a declaration")
            .clone();
        doc.offset_to_position(decl.start)
    };
    let before = backend
        .get_hover_at(&uri, query_position)
        .expect("v1 elaboration should produce a hover for alpha_marker");
    assert!(
        hover_markup_value(&before).contains("alpha_marker"),
        "v1 hover should show the elaborated declaration"
    );

    backend
        .did_change(DidChangeTextDocumentParams {
            text_document: VersionedTextDocumentIdentifier {
                uri: uri.clone(),
                version: 2,
            },
            content_changes: vec![TextDocumentContentChangeEvent {
                range: None,
                range_length: None,
                text: "axiom omega_marker : Nat\n".to_string(),
            }],
        })
        .await;

    // Race window: didChange has returned, the v2 elaboration task has not
    // run. The hover must serve the last committed (v1) snapshot.
    let racing = backend
        .get_hover_at(&uri, query_position)
        .expect("a hover racing the background elaboration must serve the last committed snapshot");
    assert!(
        hover_markup_value(&racing).contains("alpha_marker"),
        "the racing hover must answer from the previous committed snapshot"
    );

    backend.wait_for_elaboration(&uri).await;
    let after = backend
        .get_hover_at(&uri, query_position)
        .expect("the background task should commit the v2 elaboration");
    assert!(
        hover_markup_value(&after).contains("omega_marker"),
        "after the background task commits, hover must serve the new snapshot"
    );
}

/// Two rapid `didChange`s: the first spawned elaboration is superseded (and
/// aborted before it can run on the current-thread test runtime); only the
/// newest generation commits, and its result reflects the final text.
#[tokio::test]
async fn test_rapid_did_changes_only_newest_generation_commits() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///background-supersede.lean").unwrap();

    backend
        .did_open(DidOpenTextDocumentParams {
            text_document: TextDocumentItem {
                uri: uri.clone(),
                language_id: "lean".to_string(),
                version: 1,
                text: "axiom first_gen : Nat\n".to_string(),
            },
        })
        .await;
    backend.wait_for_elaboration(&uri).await;

    for (version, text) in [
        (2, "axiom second_gen : Nat\n"),
        (3, "axiom third_gen : Nat\n"),
    ] {
        backend
            .did_change(DidChangeTextDocumentParams {
                text_document: VersionedTextDocumentIdentifier {
                    uri: uri.clone(),
                    version,
                },
                content_changes: vec![TextDocumentContentChangeEvent {
                    range: None,
                    range_length: None,
                    text: text.to_string(),
                }],
            })
            .await;
    }

    // Joins the v3 task (v2's was aborted by v3's bump before it ever ran).
    backend.wait_for_elaboration(&uri).await;

    let doc = backend
        .documents
        .get(&uri)
        .expect("document should remain open");
    let elaborated = doc
        .elaborated
        .as_ref()
        .expect("the newest generation must commit its elaboration");
    assert_eq!(
        elaborated.declarations.len(),
        1,
        "the final text declares exactly one axiom"
    );
    assert_eq!(
        elaborated.declarations[0].name, "third_gen",
        "only the newest generation's result may be committed"
    );
}

#[test]
fn csimp_module_header_attribute_visibility_in_document_elaboration() {
    for (source, accepted) in [
        (
            include_str!(
                "../../../../reports/csimp-2026-11-12/fixtures/header_private_global.lean"
            ),
            false,
        ),
        (
            include_str!(
                "../../../../reports/csimp-2026-11-12/fixtures/header_default_global.lean"
            ),
            false,
        ),
        (
            include_str!(
                "../../../../reports/csimp-2026-11-12/fixtures/header_private_scoped.lean"
            ),
            false,
        ),
        (
            include_str!("../../../../reports/csimp-2026-11-12/fixtures/header_private_local.lean"),
            true,
        ),
        (
            include_str!("../../../../reports/csimp-2026-11-12/fixtures/header_public_axiom.lean"),
            true,
        ),
        (
            include_str!(
                "../../../../reports/csimp-2026-11-12/fixtures/header_public_section.lean"
            ),
            true,
        ),
        (
            include_str!(
                "../../../../reports/csimp-2026-11-12/fixtures/header_section_restore.lean"
            ),
            true,
        ),
        (
            include_str!("../../../../reports/csimp-2026-11-12/fixtures/private.lean"),
            true,
        ),
    ] {
        let (progress, _receiver) = tokio::sync::mpsc::unbounded_channel();
        let (document, _, _, _) = CleanBackend::elaborate_text_blocking(
            source,
            IncrementalState::default(),
            None,
            &CleanBackend::builtin_tactic_patterns(),
            clean_kernel::Environment::with_prelude(),
            &progress,
        );
        if accepted {
            assert!(document.errors.is_empty(), "{:?}", document.errors);
        } else {
            assert!(
                document
                    .errors
                    .iter()
                    .any(|error| error.message.contains("must be public")),
                "{:?}",
                document.errors
            );
        }
    }
}

#[test]
fn module_definition_exposure_in_document_elaboration() {
    let cases = [
        (
            "plain",
            include_str!(
                "../../../../reports/csimp-2026-11-12/fixtures/exposure_plain_public.lean"
            ),
            false,
        ),
        (
            "explicit",
            include_str!(
                "../../../../reports/csimp-2026-11-12/fixtures/exposure_explicit_refl.lean"
            ),
            true,
        ),
        (
            "reflexive",
            include_str!("../../../../reports/csimp-2026-11-12/fixtures/exposure_reflexive.lean"),
            true,
        ),
        (
            "private",
            include_str!("../../../../reports/csimp-2026-11-12/fixtures/exposure_private.lean"),
            true,
        ),
        (
            "exposed",
            include_str!(
                "../../../../reports/csimp-2026-11-12/fixtures/exposure_exposed_defs.lean"
            ),
            true,
        ),
        (
            "abbrev",
            include_str!("../../../../reports/csimp-2026-11-12/fixtures/exposure_abbrev.lean"),
            true,
        ),
        (
            "section",
            include_str!("../../../../reports/csimp-2026-11-12/fixtures/exposure_section.lean"),
            true,
        ),
        (
            "parenthesized",
            include_str!(
                "../../../../reports/csimp-2026-11-12/fixtures/exposure_parenthesized.lean"
            ),
            true,
        ),
        (
            "by_rfl",
            include_str!("../../../../reports/csimp-2026-11-12/fixtures/exposure_by_rfl.lean"),
            true,
        ),
        (
            "parameters",
            include_str!("../../../../reports/csimp-2026-11-12/fixtures/exposure_parameters.lean"),
            true,
        ),
        (
            "explicit_defeq",
            include_str!(
                "../../../../reports/csimp-2026-11-12/fixtures/exposure_explicit_defeq.lean"
            ),
            false,
        ),
        (
            "no_expose",
            include_str!("../../../../reports/csimp-2026-11-12/fixtures/exposure_no_expose.lean"),
            false,
        ),
        (
            "section_override",
            include_str!(
                "../../../../reports/csimp-2026-11-12/fixtures/exposure_section_override.lean"
            ),
            false,
        ),
        (
            "public_helper",
            include_str!(
                "../../../../reports/csimp-2026-11-12/fixtures/exposure_public_helper.lean"
            ),
            false,
        ),
        (
            "example",
            include_str!("../../../../reports/csimp-2026-11-12/fixtures/exposure_example.lean"),
            true,
        ),
    ];
    for (name, source, accepted) in cases {
        let (progress, _receiver) = tokio::sync::mpsc::unbounded_channel();
        let (document, _, _, _) = CleanBackend::elaborate_text_blocking(
            source,
            IncrementalState::default(),
            None,
            &CleanBackend::builtin_tactic_patterns(),
            clean_kernel::Environment::with_prelude(),
            &progress,
        );
        assert_eq!(
            document.errors.is_empty(),
            accepted,
            "{name}: {:?}",
            document.errors
        );
        if !accepted {
            assert!(
                document
                    .errors
                    .iter()
                    .any(|error| error.message.contains("Not a definitional equality")),
                "{name}: {:?}",
                document.errors
            );
        }
    }
}

#[test]
fn alias_commands_retain_editor_identity_and_span() {
    for (source, name, kind) in [
        (
            "alias copied := original",
            "copied",
            CommandKind::Definition,
        ),
        (
            "alias ⟨forward, backward⟩ := equivalence",
            "forward",
            CommandKind::Theorem,
        ),
    ] {
        let parsed = clean_parser::parse_file_with_diagnostics(source).expect("alias syntax");
        assert!(parsed.diagnostics.is_empty());
        let (actual_kind, actual_name, span) = CleanBackend::classify_decl(&parsed.decls[0]);
        assert_eq!(actual_kind, kind);
        assert_eq!(actual_name.as_deref(), Some(name));
        assert_eq!(span, (0, source.len()));
    }
}
