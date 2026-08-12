// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extensions for `library_search`.

// Staged Lean4-parity scaffold with no caller yet (tests included): kept per the
// keep-and-annotate doctrine — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
use std::collections::{BTreeMap, VecDeque};

use clean_kernel::{name::Name, Expr, ExprKind};
use thiserror::Error;

use super::library_search::{
    calculate_type_similarity, count_pis, expr_depth, extract_head_name, LibrarySearchMatchKind,
    LibrarySearchResult,
};

#[derive(Debug, Clone, Error, PartialEq)]
pub(crate) enum SearchExtError {
    #[error("search cache capacity must be positive")]
    #[allow(dead_code)]
    // 2026-08-04: no caller in either build; staged prototype kept per keep-and-annotate doctrine.
    CacheCapacityExceeded,
    #[error("invalid search task id {id}")]
    InvalidTaskId { id: usize },
    #[error("search task {id} has already finished")]
    TaskAlreadyCompleted { id: usize },
    #[error("invalid score weight {field}={value}")]
    InvalidScoreWeight { field: String, value: f64 },
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) struct SearchScorerConfig {
    pub(crate) match_kind_weight: f64,
    pub(crate) args_count_weight: f64,
    pub(crate) name_similarity_weight: f64,
    pub(crate) type_depth_weight: f64,
}

impl Default for SearchScorerConfig {
    fn default() -> Self {
        Self {
            match_kind_weight: 0.4,
            args_count_weight: 0.15,
            name_similarity_weight: 0.25,
            type_depth_weight: 0.2,
        }
    }
}

impl SearchScorerConfig {
    pub(crate) fn validate(&self) -> Result<(), SearchExtError> {
        [
            ("match_kind_weight", self.match_kind_weight),
            ("args_count_weight", self.args_count_weight),
            ("name_similarity_weight", self.name_similarity_weight),
            ("type_depth_weight", self.type_depth_weight),
        ]
        .into_iter()
        .try_for_each(|(field, value)| {
            (value.is_finite() && value >= 0.0)
                .then_some(())
                .ok_or_else(|| SearchExtError::InvalidScoreWeight {
                    field: field.to_owned(),
                    value,
                })
        })
    }
}

#[derive(Debug, Clone, Copy, Default)]
pub(crate) struct SearchScorer {
    pub(crate) config: SearchScorerConfig,
}

impl SearchScorer {
    pub(crate) fn new(config: SearchScorerConfig) -> Result<Self, SearchExtError> {
        config.validate()?;
        Ok(Self { config })
    }

    pub(crate) fn score_result(
        &self,
        result: &LibrarySearchResult,
        goal_name: Option<&str>,
        goal_depth: usize,
    ) -> f64 {
        let total = self.config.match_kind_weight
            + self.config.args_count_weight
            + self.config.name_similarity_weight
            + self.config.type_depth_weight;
        if total == 0.0 {
            return result.relevance.clamp(0.0, 1.0);
        }
        let name_score = goal_name.map_or(0.5, |goal| {
            let full = result.name.to_string();
            let leaf = full.rsplit('.').next().unwrap_or(full.as_str());
            FuzzyNameMatcher::fuzzy_score(goal, leaf)
                .max(FuzzyNameMatcher::fuzzy_score(goal, &full))
        });
        let kind_score = match result.match_kind {
            LibrarySearchMatchKind::Exact => 1.0,
            LibrarySearchMatchKind::Apply => 0.85,
            LibrarySearchMatchKind::HeadMatch => 0.65,
            LibrarySearchMatchKind::TypeSimilar => 0.55,
            LibrarySearchMatchKind::Instance => 0.4,
        };
        let depth_gap = expr_depth(&result.type_).abs_diff(goal_depth) as f64;
        let depth_score = ((1.0 / (1.0 + depth_gap))
            * (1.0 / (1.0 + count_pis(&result.type_) as f64 * 0.1)))
            .clamp(0.0, 1.0);
        let score = self.config.match_kind_weight * kind_score
            + self.config.args_count_weight * (1.0 / (1.0 + result.args_needed as f64))
            + self.config.name_similarity_weight * name_score
            + self.config.type_depth_weight * depth_score;
        (score / total).clamp(0.0, 1.0)
    }

    pub(crate) fn rank_results(
        &self,
        results: &mut [LibrarySearchResult],
        goal_name: Option<&str>,
        goal_depth: usize,
    ) {
        results
            .iter_mut()
            .for_each(|result| result.relevance = self.score_result(result, goal_name, goal_depth));
        results.sort_by(|left, right| {
            right
                .relevance
                .total_cmp(&left.relevance)
                .then_with(|| left.args_needed.cmp(&right.args_needed))
                .then_with(|| left.name.cmp(&right.name))
        });
    }
}

#[derive(Debug, Clone)]
pub(crate) struct SearchCache {
    pub(crate) capacity: usize,
    pub(crate) entries: VecDeque<(String, Vec<LibrarySearchResult>)>,
    pub(crate) hits: u64,
    pub(crate) misses: u64,
}

impl SearchCache {
    pub(crate) fn new(capacity: usize) -> Self {
        Self {
            capacity,
            entries: VecDeque::new(),
            hits: 0,
            misses: 0,
        }
    }

    #[allow(dead_code)] // 2026-08-04: no caller in either build; staged prototype kept per keep-and-annotate doctrine.
    pub(crate) fn validate(&self) -> Result<(), SearchExtError> {
        (self.capacity > 0)
            .then_some(())
            .ok_or(SearchExtError::CacheCapacityExceeded)
    }

    pub(crate) fn get(&mut self, key: &str) -> Option<&[LibrarySearchResult]> {
        let Some(index) = self
            .entries
            .iter()
            .position(|(entry_key, _)| entry_key == key)
        else {
            self.misses = self.misses.saturating_add(1);
            return None;
        };
        self.hits = self.hits.saturating_add(1);
        if index > 0 {
            if let Some(entry) = self.entries.remove(index) {
                self.entries.push_front(entry);
            }
        }
        self.entries.front().map(|(_, results)| results.as_slice())
    }

    pub(crate) fn insert(&mut self, key: String, results: Vec<LibrarySearchResult>) {
        if self.capacity == 0 {
            return;
        }
        if let Some(index) = self
            .entries
            .iter()
            .position(|(entry_key, _)| entry_key == &key)
        {
            let _ = self.entries.remove(index);
        }
        self.entries.push_front((key, results));
        while self.entries.len() > self.capacity {
            let _ = self.entries.pop_back();
        }
    }

    pub(crate) fn clear(&mut self) {
        self.entries.clear();
        self.hits = 0;
        self.misses = 0;
    }
    pub(crate) fn hit_rate(&self) -> f64 {
        if self.hits + self.misses == 0 {
            0.0
        } else {
            self.hits as f64 / (self.hits + self.misses) as f64
        }
    }
    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }
    pub(crate) fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct FuzzyNameMatcher;

impl FuzzyNameMatcher {
    pub(crate) fn fuzzy_score(query: &str, candidate: &str) -> f64 {
        if query.is_empty() || candidate.is_empty() {
            return 0.0;
        }
        if query == candidate {
            return 1.0;
        }
        if query.eq_ignore_ascii_case(candidate) {
            return 0.9;
        }
        if contains_ignore_ascii_case(candidate.as_bytes(), query.as_bytes()) {
            return 0.7;
        }
        subsequence_score(query.as_bytes(), candidate.as_bytes())
    }

    pub(crate) fn fuzzy_match(query: &str, candidate: &str, threshold: f64) -> bool {
        Self::fuzzy_score(query, candidate) >= threshold.clamp(0.0, 1.0)
    }

    pub(crate) fn best_fuzzy_matches(
        query: &str,
        candidates: &[&str],
        max_results: usize,
    ) -> Vec<(usize, f64)> {
        let mut matches: Vec<_> = candidates
            .iter()
            .enumerate()
            .filter_map(|(index, candidate)| {
                let score = Self::fuzzy_score(query, candidate);
                (score > 0.0).then_some((index, score))
            })
            .collect();
        matches.sort_by(|left, right| {
            right
                .1
                .total_cmp(&left.1)
                .then_with(|| left.0.cmp(&right.0))
        });
        matches.truncate(max_results);
        matches
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct SearchStats {
    pub(crate) total_searches: u64,
    pub(crate) total_results: u64,
    pub(crate) cache_hits: u64,
    pub(crate) cache_misses: u64,
    pub(crate) avg_search_time_ns: u64,
}

impl SearchStats {
    pub(crate) fn record_search(&mut self, result_count: usize, duration_ns: u64, cache_hit: bool) {
        let prev = self.total_searches;
        self.total_searches = self.total_searches.saturating_add(1);
        self.total_results = self
            .total_results
            .saturating_add(u64::try_from(result_count).unwrap_or(u64::MAX));
        if cache_hit {
            self.cache_hits = self.cache_hits.saturating_add(1);
        } else {
            self.cache_misses = self.cache_misses.saturating_add(1);
        }
        let total_time = self.avg_search_time_ns as u128 * prev as u128 + duration_ns as u128;
        self.avg_search_time_ns = (total_time / self.total_searches as u128) as u64;
    }

    pub(crate) fn summary(&self) -> String {
        format!(
            "searches={}, results={}, cache_hits={}, cache_misses={}, avg_search_time_ns={}",
            self.total_searches,
            self.total_results,
            self.cache_hits,
            self.cache_misses,
            self.avg_search_time_ns
        )
    }

    pub(crate) fn reset(&mut self) {
        *self = Self::default();
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum TypeFilterMode {
    ExactHead,
    #[allow(dead_code)]
    // 2026-08-04: no caller in either build; staged prototype kept per keep-and-annotate doctrine.
    Compatible,
    SubExpression,
}

impl TypeFilterMode {
    pub(crate) fn matches(self, expr: &Expr, head: &str) -> bool {
        match self {
            Self::ExactHead => extract_head_name(expr).as_deref() == Some(head),
            Self::Compatible => {
                Self::ExactHead.matches(expr, head)
                    || Self::SubExpression.matches(expr, head)
                    || calculate_type_similarity(
                        expr,
                        &Expr::const_(Name::from_string(head), Vec::new()),
                    ) >= 0.35
            }
            Self::SubExpression => expr_contains_head(expr, head),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct TypeFilter;

impl TypeFilter {
    pub(crate) fn filter_with_mode(
        results: &[LibrarySearchResult],
        head: &str,
        mode: TypeFilterMode,
    ) -> Vec<LibrarySearchResult> {
        results
            .iter()
            .filter(|result| mode.matches(&result.type_, head))
            .cloned()
            .collect()
    }
    pub(crate) fn filter_by_type_head(
        results: &[LibrarySearchResult],
        head: &str,
    ) -> Vec<LibrarySearchResult> {
        Self::filter_with_mode(results, head, TypeFilterMode::ExactHead)
    }
    pub(crate) fn filter_by_arity(
        results: &[LibrarySearchResult],
        min: usize,
        max: usize,
    ) -> Vec<LibrarySearchResult> {
        results
            .iter()
            .filter(|result| (min..=max).contains(&count_pis(&result.type_)))
            .cloned()
            .collect()
    }
    pub(crate) fn filter_by_relevance(
        results: &[LibrarySearchResult],
        min_relevance: f64,
    ) -> Vec<LibrarySearchResult> {
        results
            .iter()
            .filter(|result| result.relevance >= min_relevance)
            .cloned()
            .collect()
    }
}

#[derive(Debug, Clone)]
pub(crate) struct ModuleGroup {
    pub(crate) module_name: String,
    pub(crate) results: Vec<LibrarySearchResult>,
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct ResultGrouper;

impl ResultGrouper {
    pub(crate) fn group_by_module(results: &[LibrarySearchResult]) -> Vec<ModuleGroup> {
        let mut groups: BTreeMap<String, Vec<LibrarySearchResult>> = BTreeMap::new();
        results.iter().cloned().for_each(|result| {
            groups
                .entry(module_name(&result.name))
                .or_default()
                .push(result)
        });
        groups
            .into_iter()
            .map(|(module_name, results)| ModuleGroup {
                module_name,
                results,
            })
            .collect()
    }

    pub(crate) fn group_by_match_kind(
        results: &[LibrarySearchResult],
    ) -> Vec<(LibrarySearchMatchKind, Vec<LibrarySearchResult>)> {
        [
            LibrarySearchMatchKind::Exact,
            LibrarySearchMatchKind::Apply,
            LibrarySearchMatchKind::HeadMatch,
            LibrarySearchMatchKind::TypeSimilar,
            LibrarySearchMatchKind::Instance,
        ]
        .into_iter()
        .filter_map(|kind| {
            let grouped: Vec<_> = results
                .iter()
                .filter(|result| result.match_kind == kind)
                .cloned()
                .collect();
            (!grouped.is_empty()).then_some((kind, grouped))
        })
        .collect()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SearchHistoryEntry {
    pub(crate) query_key: String,
    pub(crate) result_count: usize,
    pub(crate) timestamp_ns: u64,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct SearchHistory {
    pub(crate) max_entries: usize,
    pub(crate) entries: Vec<SearchHistoryEntry>,
}

impl SearchHistory {
    pub(crate) fn new(max_entries: usize) -> Self {
        Self {
            max_entries,
            entries: Vec::new(),
        }
    }
    pub(crate) fn record(&mut self, query_key: String, result_count: usize, timestamp_ns: u64) {
        if self.max_entries == 0 {
            return;
        }
        self.entries.push(SearchHistoryEntry {
            query_key,
            result_count,
            timestamp_ns,
        });
        let overflow = self.entries.len().saturating_sub(self.max_entries);
        if overflow > 0 {
            self.entries.drain(..overflow);
        }
    }
    pub(crate) fn recent(&self, n: usize) -> &[SearchHistoryEntry] {
        &self.entries[self.entries.len().saturating_sub(n)..]
    }
    pub(crate) fn search_count(&self) -> usize {
        self.entries.len()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SearchTaskStatus {
    Pending,
    Running,
    Completed(usize),
    Failed(String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SearchTask {
    pub(crate) id: usize,
    pub(crate) query_key: String,
    pub(crate) status: SearchTaskStatus,
}

#[derive(Debug, Clone, Default)]
pub(crate) struct SearchCoordinator {
    pub(crate) tasks: Vec<SearchTask>,
}

impl SearchCoordinator {
    pub(crate) fn new() -> Self {
        Self { tasks: Vec::new() }
    }
    pub(crate) fn submit(&mut self, query_key: String) -> usize {
        let id = self.tasks.len();
        self.tasks.push(SearchTask {
            id,
            query_key,
            status: SearchTaskStatus::Pending,
        });
        id
    }
    pub(crate) fn start(&mut self, id: usize) -> Result<(), SearchExtError> {
        match self.tasks.get_mut(id) {
            Some(task) => match task.status {
                SearchTaskStatus::Pending | SearchTaskStatus::Running => {
                    task.status = SearchTaskStatus::Running;
                    Ok(())
                }
                _ => Err(SearchExtError::TaskAlreadyCompleted { id }),
            },
            None => Err(SearchExtError::InvalidTaskId { id }),
        }
    }
    pub(crate) fn complete(
        &mut self,
        id: usize,
        result_count: usize,
    ) -> Result<(), SearchExtError> {
        match self.tasks.get_mut(id) {
            Some(task) => match task.status {
                SearchTaskStatus::Pending | SearchTaskStatus::Running => {
                    task.status = SearchTaskStatus::Completed(result_count);
                    Ok(())
                }
                _ => Err(SearchExtError::TaskAlreadyCompleted { id }),
            },
            None => Err(SearchExtError::InvalidTaskId { id }),
        }
    }
    pub(crate) fn fail(&mut self, id: usize, reason: String) -> Result<(), SearchExtError> {
        match self.tasks.get_mut(id) {
            Some(task) => match task.status {
                SearchTaskStatus::Pending | SearchTaskStatus::Running => {
                    task.status = SearchTaskStatus::Failed(reason);
                    Ok(())
                }
                _ => Err(SearchExtError::TaskAlreadyCompleted { id }),
            },
            None => Err(SearchExtError::InvalidTaskId { id }),
        }
    }
    pub(crate) fn pending_count(&self) -> usize {
        self.tasks
            .iter()
            .filter(|task| matches!(&task.status, SearchTaskStatus::Pending))
            .count()
    }
    pub(crate) fn completed_count(&self) -> usize {
        self.tasks
            .iter()
            .filter(|task| matches!(&task.status, SearchTaskStatus::Completed(_)))
            .count()
    }
    pub(crate) fn active_tasks(&self) -> Vec<&SearchTask> {
        self.tasks
            .iter()
            .filter(|task| {
                matches!(
                    &task.status,
                    SearchTaskStatus::Pending | SearchTaskStatus::Running
                )
            })
            .collect()
    }
}

pub(crate) fn contains_ignore_ascii_case(haystack: &[u8], needle: &[u8]) -> bool {
    needle.is_empty()
        || haystack.windows(needle.len()).any(|window| {
            window
                .iter()
                .zip(needle.iter())
                .all(|(a, b)| a.eq_ignore_ascii_case(b))
        })
}

pub(crate) fn subsequence_score(query: &[u8], candidate: &[u8]) -> f64 {
    let (matched, start, end, contiguous, _) = query.iter().fold(
        (0usize, None, None, 0usize, None),
        |(matched, start, end, contiguous, prev), needle| {
            let next = candidate
                .iter()
                .enumerate()
                .skip(prev.map_or(0, |idx| idx + 1))
                .find(|(_, byte)| byte.eq_ignore_ascii_case(needle))
                .map(|(idx, _)| idx);
            match next {
                Some(idx) => (
                    matched + 1,
                    start.or(Some(idx)),
                    Some(idx),
                    contiguous + usize::from(prev.is_some_and(|last| idx == last + 1)),
                    Some(idx),
                ),
                None => (matched, start, end, contiguous, prev),
            }
        },
    );
    if matched != query.len() {
        return 0.0;
    }
    let span = end
        .zip(start)
        .map_or(candidate.len().max(1), |(last, first)| last + 1 - first);
    let coverage = query.len() as f64 / candidate.len().max(1) as f64;
    let compactness = query.len() as f64 / span.max(1) as f64;
    let continuity = contiguous as f64 / query.len().saturating_sub(1).max(1) as f64;
    (0.4 + 0.25 * coverage + 0.25 * compactness + 0.1 * continuity).clamp(0.0, 0.89)
}

pub(crate) fn expr_contains_head(expr: &Expr, head: &str) -> bool {
    if extract_head_name(expr).as_deref() == Some(head) {
        return true;
    }
    match expr.kind() {
        ExprKind::App(fun, arg) => expr_contains_head(fun, head) || expr_contains_head(arg, head),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            expr_contains_head(ty, head) || expr_contains_head(body, head)
        }
        ExprKind::Let(_, ty, value, body, _) => {
            expr_contains_head(ty, head)
                || expr_contains_head(value, head)
                || expr_contains_head(body, head)
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
            expr_contains_head(inner, head)
        }
        ExprKind::CubicalPath { ty, left, right } => {
            expr_contains_head(ty, head)
                || expr_contains_head(left, head)
                || expr_contains_head(right, head)
        }
        ExprKind::CubicalPathLam { body } => expr_contains_head(body, head),
        ExprKind::CubicalPathApp { path, arg } => {
            expr_contains_head(path, head) || expr_contains_head(arg, head)
        }
        ExprKind::CubicalHComp { ty, phi, u, base } => {
            expr_contains_head(ty, head)
                || expr_contains_head(phi, head)
                || expr_contains_head(u, head)
                || expr_contains_head(base, head)
        }
        ExprKind::CubicalTransp { ty, phi, base } => {
            expr_contains_head(ty, head)
                || expr_contains_head(phi, head)
                || expr_contains_head(base, head)
        }
        _ => false,
    }
}

pub(crate) fn module_name(name: &Name) -> String {
    let rendered = name.to_string();
    rendered
        .rsplit_once('.')
        .map_or_else(|| "<root>".to_string(), |(module, _)| module.to_string())
}
