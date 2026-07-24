// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the extended tactic documentation module.

use super::tactic_doc_ext::*;

// -- Registry construction ---------------------------------------------------

#[test]
fn test_registry_new_not_empty() {
    let reg = ExtTacticDocRegistry::new();
    assert!(
        !reg.is_empty(),
        "registry should have entries after construction"
    );
}

#[test]
fn test_registry_len_at_least_30() {
    let reg = ExtTacticDocRegistry::new();
    assert!(reg.len() >= 30, "expected >=30 tactics, got {}", reg.len());
}

#[test]
fn test_all_names_sorted() {
    let reg = ExtTacticDocRegistry::new();
    let names = reg.all_names();
    let mut sorted = names.clone();
    sorted.sort_unstable();
    assert_eq!(
        names, sorted,
        "all_names() must return alphabetically sorted list"
    );
}

// -- Lookup by name ----------------------------------------------------------

#[test]
fn test_get_intro_exists() {
    let reg = ExtTacticDocRegistry::new();
    let doc = reg.get("intro").expect("intro should be documented");
    assert_eq!(doc.name, "intro");
}

#[test]
fn test_get_nonexistent_returns_none() {
    let reg = ExtTacticDocRegistry::new();
    assert!(reg.get("nonexistent_tactic_xyz").is_none());
}

#[test]
fn test_get_exact_category_is_basic() {
    let reg = ExtTacticDocRegistry::new();
    let doc = reg.get("exact").expect("exact should be documented");
    assert_eq!(doc.category, ExtTacticCategory::Basic);
}

#[test]
fn test_get_omega_category_is_arithmetic() {
    let reg = ExtTacticDocRegistry::new();
    let doc = reg.get("omega").expect("omega should be documented");
    assert_eq!(doc.category, ExtTacticCategory::Arithmetic);
}

#[test]
fn test_get_cert_mathverse_category_is_arithmetic() {
    let reg = ExtTacticDocRegistry::new();
    let doc = reg
        .get("cert_mathverse")
        .expect("cert_mathverse should be documented");
    assert_eq!(doc.category, ExtTacticCategory::Arithmetic);
}

#[test]
fn test_get_simp_has_description() {
    let reg = ExtTacticDocRegistry::new();
    let doc = reg.get("simp").expect("simp should be documented");
    assert!(
        !doc.description.is_empty(),
        "description should not be empty"
    );
}

#[test]
fn test_get_blast_category_is_automation() {
    let reg = ExtTacticDocRegistry::new();
    let doc = reg.get("blast").expect("blast should be documented");
    assert_eq!(doc.category, ExtTacticCategory::Automation);
}

// -- Category classification -------------------------------------------------

#[test]
fn test_category_label_basic() {
    assert_eq!(ExtTacticCategory::Basic.label(), "Basic");
}

#[test]
fn test_category_label_automation() {
    assert_eq!(ExtTacticCategory::Automation.label(), "Automation");
}

#[test]
fn test_category_label_custom() {
    assert_eq!(ExtTacticCategory::Custom.label(), "Custom");
}

#[test]
fn test_by_category_basic_nonempty() {
    let reg = ExtTacticDocRegistry::new();
    let basics = reg.by_category(ExtTacticCategory::Basic);
    assert!(!basics.is_empty(), "Basic category should have entries");
}

#[test]
fn test_by_category_arithmetic_contains_omega() {
    let reg = ExtTacticDocRegistry::new();
    let arith = reg.by_category(ExtTacticCategory::Arithmetic);
    assert!(
        arith.iter().any(|d| d.name == "omega"),
        "Arithmetic should include omega"
    );
    assert!(
        arith.iter().any(|d| d.name == "cert_mathverse"),
        "Arithmetic should include cert_mathverse"
    );
    assert!(
        arith.iter().any(|d| d.name == "cert_simp"),
        "Arithmetic should include cert_simp"
    );
}

#[test]
fn test_by_category_automation_contains_blast() {
    let reg = ExtTacticDocRegistry::new();
    let auto = reg.by_category(ExtTacticCategory::Automation);
    assert!(
        auto.iter().any(|d| d.name == "blast"),
        "Automation should include blast"
    );
}

#[test]
fn test_by_category_custom_is_empty() {
    let reg = ExtTacticDocRegistry::new();
    let custom = reg.by_category(ExtTacticCategory::Custom);
    assert!(
        custom.is_empty(),
        "Custom category should be empty by default"
    );
}

// -- Syntax documentation ----------------------------------------------------

#[test]
fn test_syntax_pattern_simp() {
    let reg = ExtTacticDocRegistry::new();
    let doc = reg.get("simp").unwrap();
    assert!(
        doc.syntax.pattern.contains("lemmas"),
        "simp pattern should mention lemmas"
    );
}

#[test]
fn test_syntax_simp_has_only_modifier() {
    let reg = ExtTacticDocRegistry::new();
    let doc = reg.get("simp").unwrap();
    assert!(
        doc.syntax.modifiers.contains(&"only".to_string()),
        "simp should accept 'only'"
    );
}

#[test]
fn test_syntax_cases_accepts_with_clause() {
    let reg = ExtTacticDocRegistry::new();
    let doc = reg.get("cases").unwrap();
    assert!(
        doc.syntax.accepts_with_clause,
        "cases should accept with clause"
    );
}

#[test]
fn test_syntax_rw_accepts_at() {
    let reg = ExtTacticDocRegistry::new();
    let doc = reg.get("rw").unwrap();
    assert!(doc.syntax.accepts_at, "rw should accept at location");
}

#[test]
fn test_syntax_intro_no_at() {
    let reg = ExtTacticDocRegistry::new();
    let doc = reg.get("intro").unwrap();
    assert!(!doc.syntax.accepts_at, "intro should not accept at");
}

// -- Example storage ---------------------------------------------------------

#[test]
fn test_examples_intro_not_empty() {
    let reg = ExtTacticDocRegistry::new();
    let doc = reg.get("intro").unwrap();
    assert!(!doc.examples.is_empty(), "intro should have examples");
}

#[test]
fn test_examples_have_description_and_code() {
    let reg = ExtTacticDocRegistry::new();
    let doc = reg.get("intro").unwrap();
    for ex in &doc.examples {
        assert!(
            !ex.description.is_empty(),
            "example description should not be empty"
        );
        assert!(!ex.code.is_empty(), "example code should not be empty");
    }
}

#[test]
fn test_examples_simp_contains_simp_only() {
    let reg = ExtTacticDocRegistry::new();
    let doc = reg.get("simp").unwrap();
    assert!(
        doc.examples.iter().any(|e| e.code.contains("simp only")),
        "simp examples should include simp only usage"
    );
}

// -- Dependency tracking -----------------------------------------------------

#[test]
fn test_dependencies_intros_depends_on_intro() {
    let reg = ExtTacticDocRegistry::new();
    let deps = reg.dependencies("intros").expect("intros should exist");
    assert!(
        deps.contains(&"intro".to_string()),
        "intros should depend on intro"
    );
}

#[test]
fn test_dependencies_blast_has_multiple() {
    let reg = ExtTacticDocRegistry::new();
    let deps = reg.dependencies("blast").expect("blast should exist");
    assert!(
        deps.len() >= 3,
        "blast should have multiple dependencies, got {}",
        deps.len()
    );
}

#[test]
fn test_dependencies_intro_is_empty() {
    let reg = ExtTacticDocRegistry::new();
    let deps = reg.dependencies("intro").expect("intro should exist");
    assert!(deps.is_empty(), "intro should have no dependencies");
}

#[test]
fn test_reverse_dependencies_intro() {
    let reg = ExtTacticDocRegistry::new();
    let rdeps = reg.reverse_dependencies("intro");
    assert!(
        rdeps.contains(&"intros"),
        "intros should be a reverse dependency of intro"
    );
}

#[test]
fn test_reverse_dependencies_constructor() {
    let reg = ExtTacticDocRegistry::new();
    let rdeps = reg.reverse_dependencies("constructor");
    assert!(
        !rdeps.is_empty(),
        "constructor should have reverse dependencies (split, left, right)"
    );
}

// -- Keyword search ----------------------------------------------------------

#[test]
fn test_search_keyword_exact_name() {
    let reg = ExtTacticDocRegistry::new();
    let results = reg.search_keyword("omega");
    assert!(
        results.iter().any(|d| d.name == "omega"),
        "searching 'omega' should find omega"
    );
}

#[test]
fn test_search_keyword_case_insensitive() {
    let reg = ExtTacticDocRegistry::new();
    let results = reg.search_keyword("OMEGA");
    assert!(
        results.iter().any(|d| d.name == "omega"),
        "search should be case-insensitive"
    );
}

#[test]
fn test_search_keyword_description_match() {
    let reg = ExtTacticDocRegistry::new();
    let results = reg.search_keyword("contradiction");
    // Should find both the tactic named "contradiction" and others mentioning it
    assert!(
        !results.is_empty(),
        "searching 'contradiction' should find results"
    );
}

#[test]
fn test_search_keyword_no_results() {
    let reg = ExtTacticDocRegistry::new();
    let results = reg.search_keyword("zzz_nonexistent_keyword_zzz");
    assert!(results.is_empty(), "nonsense keyword should return empty");
}

#[test]
fn test_search_keyword_in_example_code() {
    let reg = ExtTacticDocRegistry::new();
    let results = reg.search_keyword("Nat.add_zero");
    assert!(
        !results.is_empty(),
        "searching example code content should find results"
    );
}

// -- Goal-pattern search -----------------------------------------------------

#[test]
fn test_suggest_equality_includes_rfl() {
    let reg = ExtTacticDocRegistry::new();
    let suggestions = reg.suggest_for_goal(GoalPattern::Equality);
    assert!(
        suggestions.iter().any(|d| d.name == "rfl"),
        "equality should suggest rfl"
    );
}

#[test]
fn test_suggest_false_includes_contradiction() {
    let reg = ExtTacticDocRegistry::new();
    let suggestions = reg.suggest_for_goal(GoalPattern::False);
    assert!(
        suggestions.iter().any(|d| d.name == "contradiction"),
        "False goal should suggest contradiction"
    );
}

#[test]
fn test_suggest_conjunction_includes_split() {
    let reg = ExtTacticDocRegistry::new();
    let suggestions = reg.suggest_for_goal(GoalPattern::Conjunction);
    assert!(
        suggestions.iter().any(|d| d.name == "split"),
        "conjunction should suggest split"
    );
}

#[test]
fn test_suggest_forall_includes_intro() {
    let reg = ExtTacticDocRegistry::new();
    let suggestions = reg.suggest_for_goal(GoalPattern::Forall);
    assert!(
        suggestions.iter().any(|d| d.name == "intro"),
        "forall should suggest intro"
    );
}

#[test]
fn test_suggest_numeric_includes_omega() {
    let reg = ExtTacticDocRegistry::new();
    let suggestions = reg.suggest_for_goal(GoalPattern::NumericRelation);
    assert!(
        suggestions.iter().any(|d| d.name == "omega"),
        "numeric should suggest omega"
    );
    assert!(
        suggestions.iter().any(|d| d.name == "cert_mathverse"),
        "numeric should suggest cert_mathverse"
    );
}

#[test]
fn test_suggest_negation_includes_by_contra() {
    let reg = ExtTacticDocRegistry::new();
    let suggestions = reg.suggest_for_goal(GoalPattern::Negation);
    assert!(
        suggestions.iter().any(|d| d.name == "by_contra"),
        "negation should suggest by_contra"
    );
}

#[test]
fn test_goal_pattern_label() {
    assert_eq!(GoalPattern::Equality.label(), "Equality");
    assert_eq!(GoalPattern::Other.label(), "Other");
}

// -- Documentation formatting ------------------------------------------------

#[test]
fn test_format_markdown_contains_header() {
    let reg = ExtTacticDocRegistry::new();
    let md = reg
        .format_doc("intro", DocFormat::Markdown)
        .expect("intro should format");
    assert!(md.contains("## intro"), "markdown should contain H2 header");
}

#[test]
fn test_format_markdown_contains_category() {
    let reg = ExtTacticDocRegistry::new();
    let md = reg.format_doc("intro", DocFormat::Markdown).unwrap();
    assert!(
        md.contains("**Category:** Basic"),
        "markdown should contain category"
    );
}

#[test]
fn test_format_markdown_contains_version() {
    let reg = ExtTacticDocRegistry::new();
    let md = reg.format_doc("intro", DocFormat::Markdown).unwrap();
    assert!(
        md.contains("**Since:** v0.1.0"),
        "markdown should contain version"
    );
}

#[test]
fn test_format_plain_text_contains_name() {
    let reg = ExtTacticDocRegistry::new();
    let txt = reg
        .format_doc("simp", DocFormat::PlainText)
        .expect("simp should format");
    assert!(
        txt.starts_with("simp\n"),
        "plain text should start with name"
    );
}

#[test]
fn test_format_structured_is_json_like() {
    let reg = ExtTacticDocRegistry::new();
    let json = reg
        .format_doc("omega", DocFormat::Structured)
        .expect("omega should format");
    assert!(
        json.starts_with('{') && json.ends_with('}'),
        "structured should be JSON-like"
    );
    assert!(
        json.contains("\"name\":\"omega\""),
        "structured should contain name field"
    );
}

#[test]
fn test_format_nonexistent_returns_none() {
    let reg = ExtTacticDocRegistry::new();
    assert!(reg.format_doc("nonexistent", DocFormat::Markdown).is_none());
}

#[test]
fn test_format_markdown_with_modifiers() {
    let reg = ExtTacticDocRegistry::new();
    let md = reg.format_doc("simp", DocFormat::Markdown).unwrap();
    assert!(
        md.contains("**Modifiers:**"),
        "simp markdown should show modifiers"
    );
}

#[test]
fn test_format_markdown_with_dependencies() {
    let reg = ExtTacticDocRegistry::new();
    let md = reg.format_doc("blast", DocFormat::Markdown).unwrap();
    assert!(
        md.contains("**Uses internally:**"),
        "blast markdown should show dependencies"
    );
}

// -- Version tracking --------------------------------------------------------

#[test]
fn test_version_intro_is_010() {
    let reg = ExtTacticDocRegistry::new();
    let doc = reg.get("intro").unwrap();
    assert_eq!(doc.since_version, "0.1.0");
}

#[test]
fn test_version_nlinarith_is_020() {
    let reg = ExtTacticDocRegistry::new();
    let doc = reg.get("nlinarith").unwrap();
    assert_eq!(doc.since_version, "0.2.0");
}

#[test]
fn test_version_blast_is_030() {
    let reg = ExtTacticDocRegistry::new();
    let doc = reg.get("blast").unwrap();
    assert_eq!(doc.since_version, "0.3.0");
}

// -- Statistics --------------------------------------------------------------

#[test]
fn test_stats_total_tactics_matches_len() {
    let reg = ExtTacticDocRegistry::new();
    let stats = reg.stats();
    assert_eq!(stats.total_tactics, reg.len());
}

#[test]
fn test_stats_initial_search_count_zero() {
    let reg = ExtTacticDocRegistry::new();
    let stats = reg.stats();
    assert_eq!(stats.total_searches, 0, "search count should start at 0");
}

#[test]
fn test_stats_search_count_increments() {
    let reg = ExtTacticDocRegistry::new();
    let _ = reg.search_keyword("omega");
    let _ = reg.search_keyword("simp");
    let stats = reg.stats();
    assert_eq!(
        stats.total_searches, 2,
        "search count should be 2 after 2 searches"
    );
}

#[test]
fn test_stats_goal_suggest_increments_search() {
    let reg = ExtTacticDocRegistry::new();
    let _ = reg.suggest_for_goal(GoalPattern::Equality);
    let stats = reg.stats();
    assert_eq!(
        stats.total_searches, 1,
        "goal suggestion should increment search count"
    );
}

#[test]
fn test_stats_category_counts_sum_to_total() {
    let reg = ExtTacticDocRegistry::new();
    let stats = reg.stats();
    let sum: usize = stats.category_counts.values().sum();
    assert_eq!(
        sum, stats.total_tactics,
        "category counts should sum to total"
    );
}

#[test]
fn test_stats_total_examples_positive() {
    let reg = ExtTacticDocRegistry::new();
    let stats = reg.stats();
    assert!(
        stats.total_examples > 0,
        "should have at least some examples"
    );
}

#[test]
fn test_stats_category_counts_has_basic() {
    let reg = ExtTacticDocRegistry::new();
    let stats = reg.stats();
    assert!(stats
        .category_counts
        .contains_key(&ExtTacticCategory::Basic));
}
