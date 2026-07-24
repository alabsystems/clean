// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{TacticCategory, TacticDocRegistry};

#[test]
fn test_registry_has_at_least_30_tactics() {
    let reg = TacticDocRegistry::new();
    assert!(
        reg.len() >= 30,
        "expected at least 30 documented tactics, got {}",
        reg.len()
    );
}

#[test]
fn test_get_known_tactic_returns_some() {
    let reg = TacticDocRegistry::new();
    let doc = reg.get("intro").expect("intro should be documented");
    assert_eq!(doc.name, "intro");
    assert_eq!(doc.category, TacticCategory::Basic);
    assert!(!doc.description.is_empty());
    assert!(!doc.signature.is_empty());
}

#[test]
fn test_get_unknown_tactic_returns_none() {
    let reg = TacticDocRegistry::new();
    assert!(reg.get("nonexistent_tactic_xyz").is_none());
}

#[test]
fn test_all_names_sorted() {
    let reg = TacticDocRegistry::new();
    let names = reg.all_names();
    let mut sorted = names.clone();
    sorted.sort_unstable();
    assert_eq!(names, sorted, "all_names should return sorted names");
}

#[test]
fn test_all_names_contains_core_tactics() {
    let reg = TacticDocRegistry::new();
    let names = reg.all_names();
    for expected in [
        "intro",
        "apply",
        "exact",
        "rfl",
        "simp",
        "omega",
        "cert_mathverse",
        "cert_simp",
        "cases",
        "sorry",
    ] {
        assert!(
            names.contains(&expected),
            "all_names should contain '{expected}'"
        );
    }
}

#[test]
fn test_by_category_basic() {
    let reg = TacticDocRegistry::new();
    let basic = reg.by_category(TacticCategory::Basic);
    assert!(
        basic.len() >= 3,
        "expected at least 3 Basic tactics, got {}",
        basic.len()
    );
    for doc in &basic {
        assert_eq!(doc.category, TacticCategory::Basic);
    }
}

#[test]
fn test_by_category_arithmetic() {
    let reg = TacticDocRegistry::new();
    let arith = reg.by_category(TacticCategory::Arithmetic);
    assert!(
        arith.len() >= 3,
        "expected at least 3 Arithmetic tactics, got {}",
        arith.len()
    );
    let names: Vec<&str> = arith.iter().map(|d| d.name.as_str()).collect();
    assert!(names.contains(&"omega"), "Arithmetic should include omega");
    assert!(
        names.contains(&"cert_mathverse"),
        "Arithmetic should include cert_mathverse"
    );
    assert!(
        names.contains(&"cert_simp"),
        "Arithmetic should include cert_simp"
    );
    assert!(names.contains(&"ring"), "Arithmetic should include ring");
}

#[test]
fn test_by_category_returns_empty_for_unused_categories() {
    // All categories should have at least one entry in our registry,
    // so verify none are accidentally empty.
    let reg = TacticDocRegistry::new();
    for cat in [
        TacticCategory::Basic,
        TacticCategory::Rewriting,
        TacticCategory::Logic,
        TacticCategory::Arithmetic,
        TacticCategory::Search,
        TacticCategory::Combinator,
        TacticCategory::Closing,
        TacticCategory::Advanced,
    ] {
        assert!(
            !reg.by_category(cat).is_empty(),
            "category {:?} should have at least one documented tactic",
            cat
        );
    }
}

#[test]
fn test_search_by_name_substring() {
    let reg = TacticDocRegistry::new();
    let results = reg.search("omega");
    assert!(
        !results.is_empty(),
        "search for 'omega' should return results"
    );
    assert!(results.iter().any(|d| d.name == "omega"));
}

#[test]
fn test_search_by_description_substring() {
    let reg = TacticDocRegistry::new();
    let results = reg.search("contradiction");
    assert!(
        results.len() >= 2,
        "search for 'contradiction' should match multiple tactics (by_contra, contradiction, exfalso)"
    );
}

#[test]
fn test_search_case_insensitive() {
    let reg = TacticDocRegistry::new();
    let upper = reg.search("OMEGA");
    let lower = reg.search("omega");
    assert_eq!(
        upper.len(),
        lower.len(),
        "search should be case-insensitive"
    );
}

#[test]
fn test_search_no_results() {
    let reg = TacticDocRegistry::new();
    let results = reg.search("zzz_no_match_zzz");
    assert!(results.is_empty());
}

#[test]
fn test_format_doc_known_tactic() {
    let reg = TacticDocRegistry::new();
    let formatted = reg.format_doc("simp").expect("simp should be documented");
    assert!(formatted.contains("## simp"));
    assert!(formatted.contains("**Category:**"));
    assert!(formatted.contains("**Signature:**"));
    assert!(formatted.contains("Simplify"));
}

#[test]
fn test_format_doc_unknown_tactic_returns_none() {
    let reg = TacticDocRegistry::new();
    assert!(reg.format_doc("nonexistent_xyz").is_none());
}

#[test]
fn test_format_doc_includes_examples() {
    let reg = TacticDocRegistry::new();
    let formatted = reg.format_doc("intro").expect("intro should be documented");
    assert!(
        formatted.contains("### Examples"),
        "formatted doc should include examples section"
    );
    assert!(
        formatted.contains("```lean"),
        "examples should be in lean code blocks"
    );
}

#[test]
fn test_format_doc_includes_see_also() {
    let reg = TacticDocRegistry::new();
    let formatted = reg.format_doc("intro").expect("intro should be documented");
    assert!(
        formatted.contains("**See also:**"),
        "formatted doc should include see_also section"
    );
    assert!(
        formatted.contains("intros"),
        "intro's see_also should reference intros"
    );
}

#[test]
fn test_every_doc_has_nonempty_fields() {
    let reg = TacticDocRegistry::new();
    for name in reg.all_names() {
        let doc = reg.get(name).unwrap();
        assert!(!doc.name.is_empty(), "{name}: name is empty");
        assert!(!doc.signature.is_empty(), "{name}: signature is empty");
        assert!(!doc.description.is_empty(), "{name}: description is empty");
        assert!(
            !doc.examples.is_empty(),
            "{name}: should have at least one example"
        );
    }
}
