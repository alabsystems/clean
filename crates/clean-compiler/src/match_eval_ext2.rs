// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended match evaluation: caching and symbolic evaluation.
//!
//! Split from `match_eval_ext` for file-size compliance.
//! - Result caching for repeated pattern evaluations
//! - Symbolic evaluation with partially-known inputs
//! - Cached evaluation combining tracing with caching
//!
//! Part of #3084 - Match expression compilation for native execution.

use std::collections::HashMap;

use clean_kernel::Name;

use crate::match_compile::DecisionTree;
use crate::match_eval::{MatchEnv, MatchValue};
use crate::match_eval_ext::{eval_traced, EvalBudget, MatchEvalExtError};

// ---------------------------------------------------------------------------
// Result caching
// ---------------------------------------------------------------------------

/// A cache key combining scrutinee names with their runtime values.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct CacheKey {
    /// Serialized representation of (name, value-tag) pairs.
    pub(crate) entries: Vec<(String, String)>,
}

impl CacheKey {
    /// Build a cache key from an environment's bindings.
    pub(crate) fn from_env(env: &MatchEnv, scrutinee_names: &[Name]) -> Self {
        let entries: Vec<(String, String)> = scrutinee_names
            .iter()
            .map(|name| {
                let tag_str = env
                    .lookup(name)
                    .map(value_tag_string)
                    .unwrap_or_else(|| "?".to_string());
                (name.to_string(), tag_str)
            })
            .collect();
        Self { entries }
    }
}

/// Produce a string representation of a value's tag structure for caching.
fn value_tag_string(val: &MatchValue) -> String {
    match val {
        MatchValue::Constructor(tag, fields) => {
            let field_strs: Vec<String> = fields.iter().map(value_tag_string).collect();
            if field_strs.is_empty() {
                tag.name.to_string()
            } else {
                format!("{}({})", tag.name, field_strs.join(","))
            }
        }
        MatchValue::Leaf => "_".to_string(),
    }
}

/// A simple result cache for match evaluations.
#[derive(Debug, Clone)]
pub(crate) struct EvalCache {
    entries: HashMap<CacheKey, usize>,
    hits: usize,
    misses: usize,
}

impl EvalCache {
    /// Create a new empty cache.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            entries: HashMap::new(),
            hits: 0,
            misses: 0,
        }
    }

    /// Look up a cached result.
    pub(crate) fn get(&mut self, key: &CacheKey) -> Option<usize> {
        match self.entries.get(key) {
            Some(&arm_idx) => {
                self.hits += 1;
                Some(arm_idx)
            }
            None => {
                self.misses += 1;
                None
            }
        }
    }

    /// Insert a result into the cache.
    pub(crate) fn insert(&mut self, key: CacheKey, arm_idx: usize) {
        self.entries.insert(key, arm_idx);
    }

    /// Number of cache hits.
    #[must_use]
    pub(crate) fn hit_count(&self) -> usize {
        self.hits
    }

    /// Number of cache misses.
    #[must_use]
    pub(crate) fn miss_count(&self) -> usize {
        self.misses
    }

    /// Cache hit rate (0.0 to 1.0).
    #[must_use]
    pub(crate) fn hit_rate(&self) -> f64 {
        let total = self.hits + self.misses;
        if total == 0 {
            return 0.0;
        }
        self.hits as f64 / total as f64
    }

    /// Number of cached entries.
    #[must_use]
    pub(crate) fn size(&self) -> usize {
        self.entries.len()
    }

    /// Clear all cached entries but preserve hit/miss statistics.
    pub(crate) fn clear(&mut self) {
        self.entries.clear();
    }
}

// ---------------------------------------------------------------------------
// Symbolic evaluation
// ---------------------------------------------------------------------------

/// A symbolic value that may be concrete or unknown.
// Staged input type for `symbolic_eval`: the pass currently takes the unknown
// set as bare `&[Name]`. Kept for the partial-information evaluator that will
// carry concrete/unknown values per scrutinee — 2026-07-31.
#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub(crate) enum SymbolicValue {
    /// Fully known concrete value.
    Concrete(MatchValue),
    /// Unknown value with an optional type hint (constructor name).
    Unknown(Option<Name>),
}

/// Result of symbolic evaluation.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub(crate) enum SymbolicResult {
    /// Evaluation resolved to a definite arm.
    Definite(usize),
    /// Multiple arms are possible given the partial information.
    Ambiguous(Vec<usize>),
    /// No arm can match (non-exhaustive even symbolically).
    NoMatch,
}

/// Evaluate a decision tree symbolically with partially-known inputs.
///
/// Returns which arms could possibly match given the partial information.
#[must_use]
pub(crate) fn symbolic_eval(
    tree: &DecisionTree,
    env: &MatchEnv,
    unknowns: &[Name],
) -> SymbolicResult {
    let mut possible_arms: Vec<usize> = Vec::new();
    collect_possible_arms(tree, env, unknowns, &mut possible_arms);
    possible_arms.sort_unstable();
    possible_arms.dedup();

    match possible_arms.len() {
        0 => SymbolicResult::NoMatch,
        1 => SymbolicResult::Definite(possible_arms[0]),
        _ => SymbolicResult::Ambiguous(possible_arms),
    }
}

fn collect_possible_arms(
    tree: &DecisionTree,
    env: &MatchEnv,
    unknowns: &[Name],
    arms: &mut Vec<usize>,
) {
    match tree {
        DecisionTree::Leaf(idx) => {
            if *idx != usize::MAX {
                arms.push(*idx);
            }
        }
        DecisionTree::Switch(scrutinee, branches, default) => {
            let is_unknown = unknowns.iter().any(|n| n == &scrutinee.name);

            if is_unknown {
                for (_, subtree) in branches {
                    collect_possible_arms(subtree, env, unknowns, arms);
                }
                if let Some(def) = default {
                    collect_possible_arms(def, env, unknowns, arms);
                }
            } else {
                let val = env.lookup(&scrutinee.name);
                match val {
                    Some(v) => {
                        if let Some(tag) = v.ctor_tag() {
                            let mut matched = false;
                            for (branch_tag, subtree) in branches {
                                if branch_tag.name == tag.name {
                                    collect_possible_arms(subtree, env, unknowns, arms);
                                    matched = true;
                                    break;
                                }
                            }
                            if !matched {
                                if let Some(def) = default {
                                    collect_possible_arms(def, env, unknowns, arms);
                                }
                            }
                        } else if let Some(def) = default {
                            collect_possible_arms(def, env, unknowns, arms);
                        }
                    }
                    None => {
                        for (_, subtree) in branches {
                            collect_possible_arms(subtree, env, unknowns, arms);
                        }
                        if let Some(def) = default {
                            collect_possible_arms(def, env, unknowns, arms);
                        }
                    }
                }
            }
        }
        DecisionTree::Guard(_, success, failure) => {
            collect_possible_arms(success, env, unknowns, arms);
            collect_possible_arms(failure, env, unknowns, arms);
        }
    }
}

// ---------------------------------------------------------------------------
// Cached evaluation
// ---------------------------------------------------------------------------

/// Evaluate with caching. Returns arm index and whether it was a cache hit.
pub(crate) fn eval_cached(
    tree: &DecisionTree,
    env: &MatchEnv,
    scrutinee_names: &[Name],
    cache: &mut EvalCache,
    budget: &EvalBudget,
) -> Result<(usize, bool), MatchEvalExtError> {
    let key = CacheKey::from_env(env, scrutinee_names);

    if let Some(arm_idx) = cache.get(&key) {
        return Ok((arm_idx, true));
    }

    let (arm_idx, _, _) = eval_traced(tree, env, budget)?;
    cache.insert(key, arm_idx);
    Ok((arm_idx, false))
}
