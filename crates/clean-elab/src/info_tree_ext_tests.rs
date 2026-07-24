// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the extended info tree module (`info_tree_ext`).

use clean_kernel::{Expr, Level, Name};
use clean_parser::Span;

use crate::info_tree::{InfoData, InfoKind, InfoTree, InfoTreeBuilder};
use crate::info_tree_ext::{
    build_extended_info_tree, collect_document_symbols, collect_references,
    collect_semantic_tokens, compute_stats, extract_completions, extract_goto_definitions,
    extract_hover_info, serialize_info_tree, CompletionCandidate, DiagnosticInfo,
    DiagnosticSeverity, DocumentSymbol, DocumentSymbolKind, ExtendedInfoTree, FoldingRange,
    FoldingRangeKind, HoverInfo, InfoTreeStats, SemanticToken, SemanticTokenKind,
};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn nat_type() -> Expr {
    Expr::const_(Name::from_string("Nat"), vec![])
}

fn nat_zero() -> Expr {
    Expr::const_(Name::from_string("Nat.zero"), vec![])
}

fn prop_sort() -> Expr {
    Expr::sort(Level::zero())
}

fn bool_type() -> Expr {
    Expr::const_(Name::from_string("Bool"), vec![])
}

fn build_term_tree() -> InfoTree {
    let mut b = InfoTreeBuilder::new();
    b.push_node(
        Span::new(0, 20),
        InfoKind::TermInfo {
            elaborated: nat_zero(),
            type_: nat_type(),
        },
    );
    b.add_leaf(InfoData::TypeAscription(nat_zero(), nat_type()));
    b.pop_node();
    b.build()
}

fn build_command_tree(cmd: &str) -> InfoTree {
    let mut b = InfoTreeBuilder::new();
    b.push_node(
        Span::new(0, 30),
        InfoKind::CommandInfo {
            command_name: cmd.to_owned(),
        },
    );
    b.add_leaf(InfoData::TypeAscription(prop_sort(), prop_sort()));
    b.pop_node();
    b.build()
}

fn build_field_tree() -> InfoTree {
    let mut b = InfoTreeBuilder::new();
    b.push_node(
        Span::new(5, 15),
        InfoKind::FieldInfo {
            struct_name: Name::from_string("Point"),
            field_name: Name::from_string("x"),
        },
    );
    b.add_leaf(InfoData::TypeAscription(nat_zero(), nat_type()));
    b.pop_node();
    b.build()
}

fn build_completion_tree() -> InfoTree {
    let mut b = InfoTreeBuilder::new();
    b.push_node(
        Span::new(0, 10),
        InfoKind::TermInfo {
            elaborated: nat_zero(),
            type_: nat_type(),
        },
    );
    b.add_leaf(InfoData::CompletionContext(
        Name::from_string("Nat"),
        vec![
            Name::from_string("Nat.add"),
            Name::from_string("Nat.sub"),
            Name::from_string("Nat.mul"),
        ],
    ));
    b.pop_node();
    b.build()
}

fn build_mixed_tree() -> InfoTree {
    let mut b = InfoTreeBuilder::new();
    // Outer: command
    b.push_node(
        Span::new(0, 50),
        InfoKind::CommandInfo {
            command_name: "def".to_owned(),
        },
    );
    // Inner: term
    b.push_node(
        Span::new(4, 20),
        InfoKind::TermInfo {
            elaborated: nat_zero(),
            type_: nat_type(),
        },
    );
    b.add_leaf(InfoData::TypeAscription(nat_zero(), nat_type()));
    b.pop_node();
    // Inner: field
    b.push_node(
        Span::new(21, 30),
        InfoKind::FieldInfo {
            struct_name: Name::from_string("Foo"),
            field_name: Name::from_string("bar"),
        },
    );
    b.add_leaf(InfoData::DefinitionHover(
        Name::from_string("Foo.bar"),
        nat_type(),
    ));
    b.pop_node();
    // Inner: tactic
    b.push_node(
        Span::new(31, 45),
        InfoKind::TacticInfo {
            goals_before: vec![prop_sort()],
            goals_after: vec![],
        },
    );
    b.add_leaf(InfoData::TypeAscription(prop_sort(), prop_sort()));
    b.pop_node();
    b.pop_node();
    b.build()
}

// ---------------------------------------------------------------------------
// HoverInfo tests
// ---------------------------------------------------------------------------

#[test]
fn test_extract_hover_info_single_term() {
    let tree = build_term_tree();
    let hovers = extract_hover_info(&tree);
    assert_eq!(hovers.len(), 1);
    assert_eq!(hovers[0].span_start, 0);
    assert_eq!(hovers[0].span_end, 20);
    assert!(!hovers[0].expr_text.is_empty());
    assert!(!hovers[0].type_text.is_empty());
}

#[test]
fn test_extract_hover_info_empty_tree() {
    let tree = InfoTreeBuilder::new().build();
    let hovers = extract_hover_info(&tree);
    assert!(hovers.is_empty());
}

#[test]
fn test_extract_hover_info_command_tree_no_hover() {
    let tree = build_command_tree("def");
    let hovers = extract_hover_info(&tree);
    assert!(
        hovers.is_empty(),
        "CommandInfo nodes should not produce hover"
    );
}

#[test]
fn test_extract_hover_info_mixed_tree() {
    let tree = build_mixed_tree();
    let hovers = extract_hover_info(&tree);
    assert_eq!(hovers.len(), 1, "only the TermInfo node produces hover");
}

// ---------------------------------------------------------------------------
// GoToDefinition tests
// ---------------------------------------------------------------------------

#[test]
fn test_extract_goto_definitions_field() {
    let tree = build_field_tree();
    let defs = extract_goto_definitions(&tree);
    assert_eq!(defs.len(), 1);
    assert_eq!(defs[0].name, "Point.x");
    assert!(defs[0].target_span.is_none());
}

#[test]
fn test_extract_goto_definitions_definition_hover_leaf() {
    let mut b = InfoTreeBuilder::new();
    b.push_node(
        Span::new(0, 10),
        InfoKind::CommandInfo {
            command_name: "def".to_owned(),
        },
    );
    b.add_leaf(InfoData::DefinitionHover(
        Name::from_string("myDef"),
        nat_type(),
    ));
    b.pop_node();
    let tree = b.build();
    let defs = extract_goto_definitions(&tree);
    assert_eq!(defs.len(), 1);
    assert_eq!(defs[0].name, "myDef");
    assert!(!defs[0].type_text.is_empty());
}

#[test]
fn test_extract_goto_definitions_empty() {
    let tree = build_term_tree();
    let defs = extract_goto_definitions(&tree);
    assert!(defs.is_empty());
}

#[test]
fn test_extract_goto_definitions_mixed_yields_both() {
    let tree = build_mixed_tree();
    let defs = extract_goto_definitions(&tree);
    // FieldInfo node + DefinitionHover leaf
    assert_eq!(defs.len(), 2);
}

// ---------------------------------------------------------------------------
// Completion tests
// ---------------------------------------------------------------------------

#[test]
fn test_extract_completions_produces_candidates() {
    let tree = build_completion_tree();
    let completions = extract_completions(&tree);
    assert_eq!(completions.len(), 3);
    assert_eq!(completions[0].label, "Nat.add");
    assert_eq!(completions[1].label, "Nat.sub");
    assert_eq!(completions[2].label, "Nat.mul");
}

#[test]
fn test_extract_completions_empty_tree() {
    let tree = build_term_tree();
    let completions = extract_completions(&tree);
    assert!(completions.is_empty());
}

#[test]
fn test_extract_completions_sort_text_ordering() {
    let tree = build_completion_tree();
    let completions = extract_completions(&tree);
    assert_eq!(completions[0].sort_text, "00000");
    assert_eq!(completions[1].sort_text, "00001");
    assert_eq!(completions[2].sort_text, "00002");
}

// ---------------------------------------------------------------------------
// SemanticToken tests
// ---------------------------------------------------------------------------

#[test]
fn test_collect_semantic_tokens_command_is_keyword() {
    let tree = build_command_tree("def");
    let tokens = collect_semantic_tokens(&tree);
    assert_eq!(tokens.len(), 1);
    assert_eq!(tokens[0].kind, SemanticTokenKind::Keyword);
}

#[test]
fn test_collect_semantic_tokens_term_is_variable() {
    let tree = build_term_tree();
    let tokens = collect_semantic_tokens(&tree);
    assert_eq!(tokens.len(), 1);
    assert_eq!(tokens[0].kind, SemanticTokenKind::Variable);
}

#[test]
fn test_collect_semantic_tokens_field_is_property() {
    let tree = build_field_tree();
    let tokens = collect_semantic_tokens(&tree);
    assert_eq!(tokens.len(), 1);
    assert_eq!(tokens[0].kind, SemanticTokenKind::Property);
}

#[test]
fn test_collect_semantic_tokens_tactic_is_function() {
    let mut b = InfoTreeBuilder::new();
    b.push_node(
        Span::new(0, 10),
        InfoKind::TacticInfo {
            goals_before: vec![prop_sort()],
            goals_after: vec![],
        },
    );
    b.pop_node();
    let tree = b.build();
    let tokens = collect_semantic_tokens(&tree);
    assert_eq!(tokens.len(), 1);
    assert_eq!(tokens[0].kind, SemanticTokenKind::Function);
}

#[test]
fn test_collect_semantic_tokens_mixed_tree_count() {
    let tree = build_mixed_tree();
    let tokens = collect_semantic_tokens(&tree);
    // command + term + field + tactic = 4
    assert_eq!(tokens.len(), 4);
}

#[test]
fn test_collect_semantic_tokens_empty() {
    let tree = InfoTreeBuilder::new().build();
    // Empty tree has a synthetic CommandInfo with empty name — still counted.
    let tokens = collect_semantic_tokens(&tree);
    // The synthetic root has command_name="" which still matches CommandInfo.
    assert_eq!(tokens.len(), 1);
}

// ---------------------------------------------------------------------------
// DocumentSymbol tests
// ---------------------------------------------------------------------------

#[test]
fn test_collect_document_symbols_def() {
    let tree = build_command_tree("def");
    let syms = collect_document_symbols(&tree);
    assert_eq!(syms.len(), 1);
    assert_eq!(syms[0].kind, DocumentSymbolKind::Definition);
    assert_eq!(syms[0].name, "def");
}

#[test]
fn test_collect_document_symbols_theorem() {
    let tree = build_command_tree("theorem");
    let syms = collect_document_symbols(&tree);
    assert_eq!(syms.len(), 1);
    assert_eq!(syms[0].kind, DocumentSymbolKind::Theorem);
}

#[test]
fn test_collect_document_symbols_inductive() {
    let tree = build_command_tree("inductive");
    let syms = collect_document_symbols(&tree);
    assert_eq!(syms[0].kind, DocumentSymbolKind::Inductive);
}

#[test]
fn test_collect_document_symbols_structure() {
    let tree = build_command_tree("structure");
    let syms = collect_document_symbols(&tree);
    assert_eq!(syms[0].kind, DocumentSymbolKind::Structure);
}

#[test]
fn test_collect_document_symbols_instance() {
    let tree = build_command_tree("instance");
    let syms = collect_document_symbols(&tree);
    assert_eq!(syms[0].kind, DocumentSymbolKind::Instance);
}

#[test]
fn test_collect_document_symbols_class() {
    let tree = build_command_tree("class");
    let syms = collect_document_symbols(&tree);
    assert_eq!(syms[0].kind, DocumentSymbolKind::Class);
}

#[test]
fn test_collect_document_symbols_namespace() {
    let tree = build_command_tree("namespace");
    let syms = collect_document_symbols(&tree);
    assert_eq!(syms[0].kind, DocumentSymbolKind::Namespace);
}

#[test]
fn test_collect_document_symbols_unknown_command() {
    let tree = build_command_tree("example");
    let syms = collect_document_symbols(&tree);
    assert_eq!(syms[0].kind, DocumentSymbolKind::Definition);
}

#[test]
fn test_collect_document_symbols_empty_name_skipped() {
    let tree = InfoTreeBuilder::new().build();
    let syms = collect_document_symbols(&tree);
    assert!(syms.is_empty(), "empty command_name should be skipped");
}

#[test]
fn test_collect_document_symbols_non_command_skipped() {
    let tree = build_term_tree();
    let syms = collect_document_symbols(&tree);
    assert!(syms.is_empty());
}

// ---------------------------------------------------------------------------
// Reference tests
// ---------------------------------------------------------------------------

#[test]
fn test_collect_references_single_field() {
    let tree = build_field_tree();
    let refs = collect_references(&tree);
    assert_eq!(refs.len(), 1);
    assert_eq!(refs[0].definition_name, "x");
    assert_eq!(refs[0].usage_spans.len(), 1);
    assert_eq!(refs[0].usage_spans[0], (5, 15));
}

#[test]
fn test_collect_references_empty_tree() {
    let tree = build_term_tree();
    let refs = collect_references(&tree);
    assert!(refs.is_empty());
}

#[test]
fn test_collect_references_groups_by_name() {
    let mut b = InfoTreeBuilder::new();
    b.push_node(
        Span::new(0, 50),
        InfoKind::CommandInfo {
            command_name: "def".to_owned(),
        },
    );
    b.push_node(
        Span::new(1, 10),
        InfoKind::FieldInfo {
            struct_name: Name::from_string("A"),
            field_name: Name::from_string("x"),
        },
    );
    b.pop_node();
    b.push_node(
        Span::new(11, 20),
        InfoKind::FieldInfo {
            struct_name: Name::from_string("B"),
            field_name: Name::from_string("x"),
        },
    );
    b.pop_node();
    b.push_node(
        Span::new(21, 30),
        InfoKind::FieldInfo {
            struct_name: Name::from_string("C"),
            field_name: Name::from_string("y"),
        },
    );
    b.pop_node();
    b.pop_node();
    let tree = b.build();
    let refs = collect_references(&tree);
    assert_eq!(refs.len(), 2, "two distinct field names: x and y");
    let x_ref = refs.iter().find(|r| r.definition_name == "x");
    assert!(x_ref.is_some());
    assert_eq!(x_ref.unwrap().usage_spans.len(), 2);
}

// ---------------------------------------------------------------------------
// Stats tests
// ---------------------------------------------------------------------------

#[test]
fn test_compute_stats_single_term() {
    let tree = build_term_tree();
    let stats = compute_stats(&tree);
    assert_eq!(stats.total_nodes, 1);
    assert_eq!(stats.total_leaves, 1);
    assert_eq!(stats.term_info_count, 1);
}

#[test]
fn test_compute_stats_mixed_tree() {
    let tree = build_mixed_tree();
    let stats = compute_stats(&tree);
    // command + term + field + tactic = 4 nodes
    assert_eq!(stats.total_nodes, 4);
    assert_eq!(stats.command_info_count, 1);
    assert_eq!(stats.term_info_count, 1);
    assert_eq!(stats.field_info_count, 1);
    assert_eq!(stats.tactic_info_count, 1);
    // 3 leaves (TypeAscription, DefinitionHover, TypeAscription)
    assert_eq!(stats.total_leaves, 3);
}

#[test]
fn test_compute_stats_empty_tree() {
    let tree = InfoTreeBuilder::new().build();
    let stats = compute_stats(&tree);
    // Synthetic root node
    assert_eq!(stats.total_nodes, 1);
    assert_eq!(stats.total_leaves, 0);
}

// ---------------------------------------------------------------------------
// build_extended_info_tree tests
// ---------------------------------------------------------------------------

#[test]
fn test_build_extended_info_tree_mixed() {
    let tree = build_mixed_tree();
    let ext = build_extended_info_tree(&tree);
    assert_eq!(ext.hover_info.len(), 1);
    assert_eq!(ext.goto_definitions.len(), 2);
    assert!(ext.completions.is_empty());
    assert!(ext.diagnostics.is_empty());
    assert_eq!(ext.semantic_tokens.len(), 4);
    assert!(ext.folding_ranges.is_empty());
    assert_eq!(ext.document_symbols.len(), 1);
    assert!(!ext.references.is_empty());
    assert_eq!(ext.stats.total_nodes, 4);
}

#[test]
fn test_build_extended_info_tree_empty() {
    let tree = InfoTreeBuilder::new().build();
    let ext = build_extended_info_tree(&tree);
    assert!(ext.hover_info.is_empty());
    assert!(ext.completions.is_empty());
}

// ---------------------------------------------------------------------------
// Serialization tests
// ---------------------------------------------------------------------------

#[test]
fn test_serialize_info_tree_produces_valid_json() {
    let tree = build_mixed_tree();
    let ext = build_extended_info_tree(&tree);
    let json = serialize_info_tree(&ext).expect("serialization should succeed");
    assert!(json.starts_with('{'));
    assert!(json.contains("hover_info"));
    assert!(json.contains("semantic_tokens"));
    assert!(json.contains("stats"));
}

#[test]
fn test_serialize_empty_extended_tree() {
    let tree = InfoTreeBuilder::new().build();
    let ext = build_extended_info_tree(&tree);
    let json = serialize_info_tree(&ext).expect("serialization should succeed");
    let parsed: serde_json::Value = serde_json::from_str(&json).expect("should be valid JSON");
    assert!(parsed.is_object());
}

#[test]
fn test_serialize_roundtrip_stats() {
    let stats = InfoTreeStats {
        total_nodes: 42,
        total_leaves: 10,
        term_info_count: 5,
        tactic_info_count: 3,
        field_info_count: 2,
        command_info_count: 1,
        macro_expansion_count: 0,
    };
    let json = serde_json::to_string(&stats).expect("serialize");
    let back: InfoTreeStats = serde_json::from_str(&json).expect("deserialize");
    assert_eq!(back.total_nodes, 42);
    assert_eq!(back.total_leaves, 10);
}

// ---------------------------------------------------------------------------
// Type construction / API tests
// ---------------------------------------------------------------------------

#[test]
fn test_hover_info_fields() {
    let h = HoverInfo {
        span_start: 10,
        span_end: 20,
        expr_text: "x".to_owned(),
        type_text: "Nat".to_owned(),
    };
    assert_eq!(h.span_start, 10);
    assert_eq!(h.span_end, 20);
    assert_eq!(h.expr_text, "x");
    assert_eq!(h.type_text, "Nat");
}

#[test]
fn test_diagnostic_info_severity_variants() {
    let severities = [
        DiagnosticSeverity::Error,
        DiagnosticSeverity::Warning,
        DiagnosticSeverity::Info,
        DiagnosticSeverity::Hint,
    ];
    for s in &severities {
        let d = DiagnosticInfo {
            span_start: 0,
            span_end: 5,
            severity: *s,
            message: "test".to_owned(),
            code: None,
        };
        assert_eq!(d.severity, *s);
    }
}

#[test]
fn test_completion_candidate_detail() {
    let c = CompletionCandidate {
        label: "foo".to_owned(),
        type_signature: "Nat -> Nat".to_owned(),
        detail: Some("A function".to_owned()),
        sort_text: "00000".to_owned(),
    };
    assert_eq!(c.detail.as_deref(), Some("A function"));
}

#[test]
fn test_folding_range_equality() {
    let a = FoldingRange {
        start_line: 1,
        end_line: 10,
        kind: FoldingRangeKind::Declaration,
    };
    let b = FoldingRange {
        start_line: 1,
        end_line: 10,
        kind: FoldingRangeKind::Declaration,
    };
    assert_eq!(a, b);
}

#[test]
fn test_folding_range_kinds() {
    let kinds = [
        FoldingRangeKind::Comment,
        FoldingRangeKind::Imports,
        FoldingRangeKind::Region,
        FoldingRangeKind::Declaration,
    ];
    for k in &kinds {
        let r = FoldingRange {
            start_line: 0,
            end_line: 1,
            kind: *k,
        };
        assert_eq!(r.kind, *k);
    }
}

#[test]
fn test_document_symbol_children() {
    let child = DocumentSymbol {
        name: "inner".to_owned(),
        kind: DocumentSymbolKind::Definition,
        span_start: 5,
        span_end: 10,
        detail: None,
        children: Vec::new(),
    };
    let parent = DocumentSymbol {
        name: "outer".to_owned(),
        kind: DocumentSymbolKind::Namespace,
        span_start: 0,
        span_end: 20,
        detail: Some("a namespace".to_owned()),
        children: vec![child],
    };
    assert_eq!(parent.children.len(), 1);
    assert_eq!(parent.children[0].name, "inner");
}

#[test]
fn test_semantic_token_kind_hash() {
    use std::collections::HashSet;
    let mut set = HashSet::new();
    set.insert(SemanticTokenKind::Keyword);
    set.insert(SemanticTokenKind::Identifier);
    set.insert(SemanticTokenKind::Type);
    set.insert(SemanticTokenKind::Literal);
    set.insert(SemanticTokenKind::Operator);
    set.insert(SemanticTokenKind::Comment);
    set.insert(SemanticTokenKind::Namespace);
    set.insert(SemanticTokenKind::Function);
    set.insert(SemanticTokenKind::Variable);
    set.insert(SemanticTokenKind::Property);
    assert_eq!(set.len(), 10);
}

#[test]
fn test_extended_info_tree_default_diagnostics_empty() {
    let ext = ExtendedInfoTree {
        hover_info: Vec::new(),
        goto_definitions: Vec::new(),
        completions: Vec::new(),
        diagnostics: Vec::new(),
        semantic_tokens: Vec::new(),
        folding_ranges: Vec::new(),
        document_symbols: Vec::new(),
        references: Vec::new(),
        stats: InfoTreeStats::default(),
    };
    assert!(ext.diagnostics.is_empty());
    assert_eq!(ext.stats.total_nodes, 0);
}

#[test]
fn test_document_symbol_kind_all_variants() {
    let kinds = [
        DocumentSymbolKind::Definition,
        DocumentSymbolKind::Theorem,
        DocumentSymbolKind::Inductive,
        DocumentSymbolKind::Structure,
        DocumentSymbolKind::Namespace,
        DocumentSymbolKind::Tactic,
        DocumentSymbolKind::Instance,
        DocumentSymbolKind::Class,
    ];
    assert_eq!(kinds.len(), 8);
}

#[test]
fn test_semantic_token_span_fields() {
    let t = SemanticToken {
        span_start: 100,
        span_end: 200,
        kind: SemanticTokenKind::Type,
    };
    assert_eq!(t.span_start, 100);
    assert_eq!(t.span_end, 200);
}
