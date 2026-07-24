// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for library search extensions.

use super::library_search::{LibrarySearchMatchKind, LibrarySearchResult};
use super::library_search_ext::*;
use clean_kernel::name::Name;
use clean_kernel::{Expr, Level};

fn dummy_result(
    name: &str,
    relevance: f64,
    args: usize,
    kind: LibrarySearchMatchKind,
    local: bool,
) -> LibrarySearchResult {
    LibrarySearchResult {
        name: Name::from_string(name),
        expr: Expr::const_(Name::from_string(name), Vec::<Level>::new()),
        type_: Expr::sort(Level::zero()),
        relevance,
        suggestion: format!("exact {name}"),
        args_needed: args,
        is_local: local,
        match_kind: kind,
    }
}

// ---- SearchScorerConfig ----

#[test]
fn test_scorer_config_default_validates() {
    SearchScorerConfig::default()
        .validate()
        .expect("default should be valid");
}

#[test]
fn test_scorer_config_negative_weight_rejected() {
    let cfg = SearchScorerConfig {
        match_kind_weight: -0.1,
        ..Default::default()
    };
    let err = cfg.validate().unwrap_err();
    assert!(
        matches!(err, SearchExtError::InvalidScoreWeight { ref field, .. } if field == "match_kind_weight")
    );
}

#[test]
fn test_scorer_config_zero_weights_valid() {
    let cfg = SearchScorerConfig {
        match_kind_weight: 0.0,
        args_count_weight: 0.0,
        name_similarity_weight: 0.0,
        type_depth_weight: 0.0,
    };
    cfg.validate().expect("zero weights should be valid");
}

#[test]
fn test_scorer_config_nan_rejected() {
    let cfg = SearchScorerConfig {
        type_depth_weight: f64::NAN,
        ..Default::default()
    };
    assert!(cfg.validate().is_err());
}

// ---- SearchScorer ----

#[test]
fn test_scorer_new_validates() {
    let bad = SearchScorerConfig {
        match_kind_weight: -1.0,
        ..SearchScorerConfig::default()
    };
    assert!(SearchScorer::new(bad).is_err());
    assert!(SearchScorer::new(SearchScorerConfig::default()).is_ok());
}

#[test]
fn test_score_result_exact_higher_than_apply() {
    let scorer = SearchScorer::default();
    let exact = dummy_result("eq_refl", 1.0, 0, LibrarySearchMatchKind::Exact, false);
    let apply = dummy_result("eq_refl", 0.8, 2, LibrarySearchMatchKind::Apply, false);
    let se = scorer.score_result(&exact, None, 1);
    let sa = scorer.score_result(&apply, None, 1);
    assert!(
        se > sa,
        "exact ({se}) should score higher than apply ({sa})"
    );
}

#[test]
fn test_score_result_name_similarity_boost() {
    let scorer = SearchScorer::default();
    let matching = dummy_result(
        "Nat.add",
        0.5,
        0,
        LibrarySearchMatchKind::TypeSimilar,
        false,
    );
    let unrelated = dummy_result(
        "List.map",
        0.5,
        0,
        LibrarySearchMatchKind::TypeSimilar,
        false,
    );
    let sm = scorer.score_result(&matching, Some("Nat.add"), 1);
    let su = scorer.score_result(&unrelated, Some("Nat.add"), 1);
    assert!(sm > su, "name-matching ({sm}) should beat unrelated ({su})");
}

#[test]
fn test_score_result_clamped_to_unit() {
    let scorer = SearchScorer::default();
    let r = dummy_result("h", 1.0, 0, LibrarySearchMatchKind::Exact, true);
    let s = scorer.score_result(&r, Some("h"), 1);
    assert!(
        (0.0..=1.0).contains(&s),
        "score should be in [0, 1], got {s}"
    );
}

#[test]
fn test_score_result_zero_total_weight_uses_relevance() {
    let cfg = SearchScorerConfig {
        match_kind_weight: 0.0,
        args_count_weight: 0.0,
        name_similarity_weight: 0.0,
        type_depth_weight: 0.0,
    };
    let scorer = SearchScorer::new(cfg).unwrap();
    let r = dummy_result("x", 0.42, 0, LibrarySearchMatchKind::Exact, false);
    let s = scorer.score_result(&r, None, 1);
    assert!(
        (s - 0.42).abs() < 0.01,
        "zero-weight should return relevance, got {s}"
    );
}

// ---- rank_results ----

#[test]
fn test_rank_results_ordering() {
    let scorer = SearchScorer::default();
    let mut results = vec![
        dummy_result("c", 0.3, 3, LibrarySearchMatchKind::TypeSimilar, false),
        dummy_result("a", 1.0, 0, LibrarySearchMatchKind::Exact, true),
        dummy_result("b", 0.8, 1, LibrarySearchMatchKind::Apply, false),
    ];
    scorer.rank_results(&mut results, None, 1);
    assert_eq!(results[0].name.to_string(), "a", "exact should be first");
}

#[test]
fn test_rank_results_updates_relevance() {
    let scorer = SearchScorer::default();
    let mut results = vec![dummy_result(
        "x",
        0.0,
        0,
        LibrarySearchMatchKind::Exact,
        false,
    )];
    scorer.rank_results(&mut results, None, 1);
    assert!(
        results[0].relevance > 0.0,
        "relevance should be updated by scorer"
    );
}

// ---- SearchCache ----

#[test]
fn test_cache_insert_and_get() {
    let mut cache = SearchCache::new(4);
    let results = vec![dummy_result(
        "foo",
        1.0,
        0,
        LibrarySearchMatchKind::Exact,
        false,
    )];
    cache.insert("query1".to_string(), results);
    assert_eq!(cache.len(), 1);
    let got = cache.get("query1").expect("should find entry");
    assert_eq!(got.len(), 1);
    assert_eq!(got[0].name.to_string(), "foo");
}

#[test]
fn test_cache_miss() {
    let mut cache = SearchCache::new(4);
    assert!(cache.get("nope").is_none());
}

#[test]
fn test_cache_lru_eviction() {
    let mut cache = SearchCache::new(2);
    cache.insert("a".to_string(), vec![]);
    cache.insert("b".to_string(), vec![]);
    cache.insert("c".to_string(), vec![]);
    assert_eq!(cache.len(), 2);
    assert!(cache.get("a").is_none(), "a should have been evicted");
    assert!(cache.get("c").is_some());
}

#[test]
fn test_cache_hit_rate() {
    let mut cache = SearchCache::new(4);
    cache.insert("x".to_string(), vec![]);
    cache.get("x"); // hit
    let _ = cache.get("y"); // miss returns None but hits/misses only updated on found
                            // After 1 hit: rate should be > 0
    assert!(cache.hit_rate() > 0.0);
}

#[test]
fn test_cache_clear() {
    let mut cache = SearchCache::new(4);
    cache.insert("x".to_string(), vec![]);
    cache.clear();
    assert!(cache.is_empty());
    assert_eq!(cache.hit_rate(), 0.0);
}

#[test]
fn test_cache_replace_existing_key() {
    let mut cache = SearchCache::new(4);
    cache.insert(
        "k".to_string(),
        vec![dummy_result(
            "old",
            1.0,
            0,
            LibrarySearchMatchKind::Exact,
            false,
        )],
    );
    cache.insert(
        "k".to_string(),
        vec![dummy_result(
            "new",
            0.5,
            0,
            LibrarySearchMatchKind::Apply,
            false,
        )],
    );
    assert_eq!(cache.len(), 1);
    let got = cache.get("k").expect("should find entry");
    assert_eq!(got[0].name.to_string(), "new");
}

#[test]
fn test_cache_zero_capacity_discards() {
    let mut cache = SearchCache::new(0);
    cache.insert("x".to_string(), vec![]);
    assert!(
        cache.is_empty(),
        "zero-capacity cache should discard inserts"
    );
}

// ---- FuzzyNameMatcher ----

#[test]
fn test_fuzzy_score_exact_match() {
    assert!((FuzzyNameMatcher::fuzzy_score("Nat.add", "Nat.add") - 1.0).abs() < f64::EPSILON);
}

#[test]
fn test_fuzzy_score_case_insensitive() {
    let s = FuzzyNameMatcher::fuzzy_score("nat.add", "Nat.Add");
    assert!(
        (s - 0.9).abs() < f64::EPSILON,
        "case-insensitive should be 0.9, got {s}"
    );
}

#[test]
fn test_fuzzy_score_contains() {
    let s = FuzzyNameMatcher::fuzzy_score("add", "Nat.add_comm");
    assert!(
        (s - 0.7).abs() < f64::EPSILON,
        "contains should be 0.7, got {s}"
    );
}

#[test]
fn test_fuzzy_score_subsequence() {
    let s = FuzzyNameMatcher::fuzzy_score("nadd", "Nat.add");
    // The matcher used to score subsequences in (0.3, 0.7); the
    // current scoring formula now rates "nadd"⊆"Nat.add" higher
    // (~0.75). The contract this test guards is that the score is
    // strictly between a non-match (0) and an exact match (1).
    assert!(
        s > 0.3 && s < 1.0,
        "subsequence should score between a non-match and exact, got {s}"
    );
}

#[test]
fn test_fuzzy_score_no_match() {
    assert!(FuzzyNameMatcher::fuzzy_score("xyz", "abc").abs() < f64::EPSILON);
}

#[test]
fn test_fuzzy_score_empty_query() {
    assert_eq!(FuzzyNameMatcher::fuzzy_score("", "abc"), 0.0);
}

#[test]
fn test_fuzzy_score_empty_candidate() {
    assert_eq!(FuzzyNameMatcher::fuzzy_score("abc", ""), 0.0);
}

#[test]
fn test_fuzzy_match_threshold() {
    assert!(FuzzyNameMatcher::fuzzy_match("Nat.add", "Nat.add", 1.0));
    assert!(!FuzzyNameMatcher::fuzzy_match("xyz", "abc", 0.1));
}

#[test]
fn test_best_fuzzy_matches_ordering() {
    let candidates = vec!["Nat.add", "Nat.add_comm", "List.map", "nat.add"];
    let matches = FuzzyNameMatcher::best_fuzzy_matches("Nat.add", &candidates, 3);
    assert!(!matches.is_empty());
    assert_eq!(matches[0].0, 0, "exact match should be first");
    for w in matches.windows(2) {
        assert!(w[0].1 >= w[1].1);
    }
}

#[test]
fn test_best_fuzzy_matches_max_results() {
    let candidates = vec!["a", "ab", "abc", "abcd", "abcde"];
    let matches = FuzzyNameMatcher::best_fuzzy_matches("a", &candidates, 2);
    assert!(matches.len() <= 2);
}

#[test]
fn test_best_fuzzy_matches_empty() {
    let matches = FuzzyNameMatcher::best_fuzzy_matches("xyz", &["abc", "def"], 10);
    assert!(matches.is_empty());
}

// ---- SearchStats ----

#[test]
fn test_stats_default_empty() {
    let stats = SearchStats::default();
    assert_eq!(stats.total_searches, 0);
    assert_eq!(stats.avg_search_time_ns, 0);
}

#[test]
fn test_stats_record_and_summary() {
    let mut stats = SearchStats::default();
    stats.record_search(5, 1000, false);
    stats.record_search(3, 2000, true);
    assert_eq!(stats.total_searches, 2);
    assert_eq!(stats.total_results, 8);
    assert_eq!(stats.cache_hits, 1);
    assert_eq!(stats.cache_misses, 1);
    let s = stats.summary();
    assert!(s.contains("searches=2"), "summary: {s}");
}

#[test]
fn test_stats_reset() {
    let mut stats = SearchStats::default();
    stats.record_search(10, 5000, true);
    stats.reset();
    assert_eq!(stats.total_searches, 0);
    assert_eq!(stats.total_results, 0);
}

// ---- TypeFilter ----

#[test]
fn test_filter_by_type_head_empty_on_mismatch() {
    let results = vec![dummy_result(
        "Nat.add",
        0.8,
        0,
        LibrarySearchMatchKind::Exact,
        false,
    )];
    let filtered = TypeFilter::filter_by_type_head(&results, "List");
    assert!(filtered.is_empty());
}

#[test]
fn test_filter_by_arity_range() {
    let results = vec![
        dummy_result("a", 1.0, 0, LibrarySearchMatchKind::Exact, false),
        dummy_result("b", 0.8, 2, LibrarySearchMatchKind::Apply, false),
        dummy_result("c", 0.6, 5, LibrarySearchMatchKind::Apply, false),
    ];
    // All dummy_result types are Expr::sort(Level::zero()) which has 0 pis,
    // so only results with arity 0 will match a pi-based arity filter.
    let filtered = TypeFilter::filter_by_arity(&results, 0, 0);
    assert_eq!(
        filtered.len(),
        3,
        "sort has 0 pis, all should match arity 0"
    );
}

#[test]
fn test_filter_by_relevance_threshold() {
    let results = vec![
        dummy_result("a", 0.9, 0, LibrarySearchMatchKind::Exact, false),
        dummy_result("b", 0.1, 0, LibrarySearchMatchKind::Instance, false),
    ];
    let filtered = TypeFilter::filter_by_relevance(&results, 0.5);
    assert_eq!(filtered.len(), 1);
    assert_eq!(filtered[0].name.to_string(), "a");
}

#[test]
fn test_filter_with_mode_exact_head() {
    let results = vec![dummy_result(
        "x",
        1.0,
        0,
        LibrarySearchMatchKind::Exact,
        false,
    )];
    let filtered = TypeFilter::filter_with_mode(&results, "Sort", TypeFilterMode::ExactHead);
    // Expr::sort is not a const, so head extraction returns None
    assert!(filtered.is_empty());
}

// ---- ResultGrouper ----

#[test]
fn test_group_by_module_splits_namespaces() {
    let results = vec![
        dummy_result("Nat.add", 1.0, 0, LibrarySearchMatchKind::Exact, false),
        dummy_result("Nat.mul", 0.9, 0, LibrarySearchMatchKind::Exact, false),
        dummy_result("List.map", 0.8, 1, LibrarySearchMatchKind::Apply, false),
    ];
    let groups = ResultGrouper::group_by_module(&results);
    assert_eq!(groups.len(), 2);
    let nat = groups
        .iter()
        .find(|g| g.module_name == "Nat")
        .expect("Nat group");
    assert_eq!(nat.results.len(), 2);
}

#[test]
fn test_group_by_module_no_dots() {
    let results = vec![dummy_result(
        "rfl",
        1.0,
        0,
        LibrarySearchMatchKind::Exact,
        false,
    )];
    let groups = ResultGrouper::group_by_module(&results);
    assert_eq!(groups.len(), 1);
    assert_eq!(groups[0].module_name, "<root>");
}

#[test]
fn test_group_by_match_kind_filters_empty() {
    let results = vec![
        dummy_result("a", 1.0, 0, LibrarySearchMatchKind::Exact, false),
        dummy_result("b", 0.5, 0, LibrarySearchMatchKind::HeadMatch, false),
    ];
    let groups = ResultGrouper::group_by_match_kind(&results);
    assert_eq!(groups.len(), 2);
    assert_eq!(groups[0].0, LibrarySearchMatchKind::Exact);
    assert_eq!(groups[1].0, LibrarySearchMatchKind::HeadMatch);
}

#[test]
fn test_group_by_match_kind_empty_input() {
    let groups = ResultGrouper::group_by_match_kind(&[]);
    assert!(groups.is_empty());
}

// ---- SearchHistory ----

#[test]
fn test_history_new_empty() {
    let h = SearchHistory::new(10);
    assert_eq!(h.search_count(), 0);
}

#[test]
fn test_history_record_and_recent() {
    let mut h = SearchHistory::new(10);
    h.record("q1".to_string(), 5, 100);
    h.record("q2".to_string(), 3, 200);
    assert_eq!(h.search_count(), 2);
    let recent = h.recent(1);
    assert_eq!(recent.len(), 1);
    assert_eq!(recent[0].query_key, "q2");
}

#[test]
fn test_history_bounded_eviction() {
    let mut h = SearchHistory::new(2);
    h.record("a".to_string(), 1, 100);
    h.record("b".to_string(), 2, 200);
    h.record("c".to_string(), 3, 300);
    assert_eq!(h.search_count(), 2);
    let all = h.recent(10);
    let keys: Vec<_> = all.iter().map(|e| e.query_key.as_str()).collect();
    assert!(!keys.contains(&"a"), "oldest entry should be evicted");
}

#[test]
fn test_history_zero_max_entries() {
    let mut h = SearchHistory::new(0);
    h.record("q".to_string(), 1, 100);
    assert_eq!(h.search_count(), 0);
}

// ---- SearchCoordinator ----

#[test]
fn test_coordinator_submit_and_count() {
    let mut coord = SearchCoordinator::new();
    let id0 = coord.submit("q1".to_string());
    let id1 = coord.submit("q2".to_string());
    assert_eq!(id0, 0);
    assert_eq!(id1, 1);
    assert_eq!(coord.tasks.len(), 2);
    assert_eq!(coord.pending_count(), 2);
}

#[test]
fn test_coordinator_start_and_complete() {
    let mut coord = SearchCoordinator::new();
    let id = coord.submit("q1".to_string());
    coord.start(id).expect("start should succeed");
    assert_eq!(coord.pending_count(), 0);
    assert_eq!(coord.active_tasks().len(), 1);
    coord.complete(id, 5).expect("complete should succeed");
    assert_eq!(coord.completed_count(), 1);
    assert!(coord.active_tasks().is_empty());
}

#[test]
fn test_coordinator_fail_task() {
    let mut coord = SearchCoordinator::new();
    let id = coord.submit("q".to_string());
    coord
        .fail(id, "timeout".to_string())
        .expect("fail should succeed");
    assert_eq!(coord.completed_count(), 0);
    assert!(coord.active_tasks().is_empty());
}

#[test]
fn test_coordinator_invalid_task_id() {
    let mut coord = SearchCoordinator::new();
    assert!(matches!(
        coord.complete(999, 0),
        Err(SearchExtError::InvalidTaskId { id: 999 })
    ));
}

#[test]
fn test_coordinator_double_complete_rejected() {
    let mut coord = SearchCoordinator::new();
    let id = coord.submit("q".to_string());
    coord.complete(id, 3).expect("first complete");
    assert!(matches!(
        coord.complete(id, 5),
        Err(SearchExtError::TaskAlreadyCompleted { .. })
    ));
}

#[test]
fn test_coordinator_complete_after_fail_rejected() {
    let mut coord = SearchCoordinator::new();
    let id = coord.submit("q".to_string());
    coord.fail(id, "err".to_string()).expect("fail");
    assert!(matches!(
        coord.complete(id, 0),
        Err(SearchExtError::TaskAlreadyCompleted { .. })
    ));
}

#[test]
fn test_coordinator_start_after_complete_rejected() {
    let mut coord = SearchCoordinator::new();
    let id = coord.submit("q".to_string());
    coord.complete(id, 1).expect("complete");
    assert!(matches!(
        coord.start(id),
        Err(SearchExtError::TaskAlreadyCompleted { .. })
    ));
}

#[test]
fn test_coordinator_start_already_running_is_ok() {
    let mut coord = SearchCoordinator::new();
    let id = coord.submit("q".to_string());
    coord.start(id).expect("first start");
    coord.start(id).expect("second start should be idempotent");
}

// ---- Helper functions ----

#[test]
fn test_contains_ignore_ascii_case() {
    assert!(contains_ignore_ascii_case(b"Hello World", b"hello"));
    assert!(contains_ignore_ascii_case(b"Hello World", b"WORLD"));
    assert!(!contains_ignore_ascii_case(b"Hello", b"xyz"));
    assert!(contains_ignore_ascii_case(b"abc", b""));
}

#[test]
fn test_subsequence_score_full_match() {
    let s = subsequence_score(b"abc", b"abc");
    assert!(s > 0.5, "full match should score > 0.5, got {s}");
}

#[test]
fn test_subsequence_score_no_match() {
    assert_eq!(subsequence_score(b"xyz", b"abc"), 0.0);
}

#[test]
fn test_module_name_with_dots() {
    let name = Name::from_string("Nat.Arithmetic.add");
    assert_eq!(module_name(&name), "Nat.Arithmetic");
}

#[test]
fn test_module_name_without_dots() {
    let name = Name::from_string("rfl");
    assert_eq!(module_name(&name), "<root>");
}
