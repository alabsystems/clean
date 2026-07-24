// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for match_eval_ext2: caching and symbolic evaluation.

use clean_kernel::Name;

use crate::match_compile::{ConstructorTag, DecisionTree, Var};
use crate::match_eval::{MatchEnv, MatchValue};
use crate::match_eval_ext::EvalBudget;
use crate::match_eval_ext2::*;
use crate::native_types::NativeType;

// ---------------------------------------------------------------------------
// Test helpers
// ---------------------------------------------------------------------------

fn mk_var(name: &str) -> Var {
    Var {
        name: Name::from_string(name),
        type_: NativeType::UInt64,
    }
}

fn mk_tag(name: &str, arity: usize) -> ConstructorTag {
    ConstructorTag {
        name: Name::from_string(name),
        arity,
    }
}

fn mk_ctor_val(name: &str, fields: Vec<MatchValue>) -> MatchValue {
    MatchValue::Constructor(mk_tag(name, fields.len()), fields)
}

fn mk_env(pairs: &[(&str, MatchValue)]) -> MatchEnv {
    let bindings: Vec<(Name, MatchValue)> = pairs
        .iter()
        .map(|(n, v)| (Name::from_string(n), v.clone()))
        .collect();
    MatchEnv::new(&bindings)
}

fn simple_switch_tree() -> DecisionTree {
    DecisionTree::Switch(
        mk_var("x"),
        vec![
            (mk_tag("A", 0), DecisionTree::Leaf(0)),
            (mk_tag("B", 0), DecisionTree::Leaf(1)),
        ],
        Some(Box::new(DecisionTree::Leaf(2))),
    )
}

fn nested_switch_tree() -> DecisionTree {
    let inner = DecisionTree::Switch(
        mk_var("x_Some_f0"),
        vec![(mk_tag("Just", 0), DecisionTree::Leaf(0))],
        Some(Box::new(DecisionTree::Leaf(2))),
    );
    DecisionTree::Switch(
        mk_var("x"),
        vec![
            (mk_tag("Some", 1), inner),
            (mk_tag("None", 0), DecisionTree::Leaf(1)),
        ],
        None,
    )
}

fn guard_tree() -> DecisionTree {
    DecisionTree::Guard(
        clean_kernel::Expr::sort(clean_kernel::Level::zero()),
        Box::new(DecisionTree::Leaf(0)),
        Box::new(DecisionTree::Leaf(1)),
    )
}

// =========================================================================
// Cache tests
// =========================================================================

#[test]
fn test_cache_empty() {
    let cache = EvalCache::new();
    assert_eq!(cache.size(), 0);
    assert_eq!(cache.hit_count(), 0);
    assert_eq!(cache.miss_count(), 0);
    assert_eq!(cache.hit_rate(), 0.0);
}

#[test]
fn test_cache_insert_and_get() {
    let mut cache = EvalCache::new();
    let key = CacheKey {
        entries: vec![("x".to_string(), "A".to_string())],
    };
    cache.insert(key.clone(), 42);
    assert_eq!(cache.size(), 1);
    assert_eq!(cache.get(&key), Some(42));
    assert_eq!(cache.hit_count(), 1);
}

#[test]
fn test_cache_miss() {
    let mut cache = EvalCache::new();
    let key = CacheKey {
        entries: vec![("x".to_string(), "A".to_string())],
    };
    assert_eq!(cache.get(&key), None);
    assert_eq!(cache.miss_count(), 1);
}

#[test]
fn test_cache_hit_rate() {
    let mut cache = EvalCache::new();
    let key = CacheKey {
        entries: vec![("x".to_string(), "A".to_string())],
    };
    cache.insert(key.clone(), 0);
    let _ = cache.get(&key); // hit
    let _ = cache.get(&key); // hit
    let miss_key = CacheKey {
        entries: vec![("y".to_string(), "B".to_string())],
    };
    let _ = cache.get(&miss_key); // miss
                                  // 2 hits, 1 miss
    assert!((cache.hit_rate() - 2.0 / 3.0).abs() < 1e-9);
}

#[test]
fn test_cache_clear() {
    let mut cache = EvalCache::new();
    let key = CacheKey {
        entries: vec![("x".to_string(), "A".to_string())],
    };
    cache.insert(key.clone(), 0);
    let _ = cache.get(&key);
    cache.clear();
    assert_eq!(cache.size(), 0);
    // Stats preserved after clear
    assert_eq!(cache.hit_count(), 1);
}

#[test]
fn test_eval_cached_miss_then_hit() {
    let tree = simple_switch_tree();
    let env = mk_env(&[("x", mk_ctor_val("A", vec![]))]);
    let names = vec![Name::from_string("x")];
    let mut cache = EvalCache::new();
    let budget = EvalBudget::default();

    let (arm, was_hit) = eval_cached(&tree, &env, &names, &mut cache, &budget).unwrap();
    assert_eq!(arm, 0);
    assert!(!was_hit);

    let (arm2, was_hit2) = eval_cached(&tree, &env, &names, &mut cache, &budget).unwrap();
    assert_eq!(arm2, 0);
    assert!(was_hit2);
}

#[test]
fn test_eval_cached_different_values() {
    let tree = simple_switch_tree();
    let names = vec![Name::from_string("x")];
    let mut cache = EvalCache::new();
    let budget = EvalBudget::default();

    let env_a = mk_env(&[("x", mk_ctor_val("A", vec![]))]);
    let (arm_a, _) = eval_cached(&tree, &env_a, &names, &mut cache, &budget).unwrap();
    assert_eq!(arm_a, 0);

    let env_b = mk_env(&[("x", mk_ctor_val("B", vec![]))]);
    let (arm_b, hit_b) = eval_cached(&tree, &env_b, &names, &mut cache, &budget).unwrap();
    assert_eq!(arm_b, 1);
    assert!(!hit_b); // different key, should miss
}

// =========================================================================
// Symbolic evaluation tests
// =========================================================================

#[test]
fn test_symbolic_definite_known_input() {
    let tree = simple_switch_tree();
    let env = mk_env(&[("x", mk_ctor_val("A", vec![]))]);
    let result = symbolic_eval(&tree, &env, &[]);
    assert_eq!(result, SymbolicResult::Definite(0));
}

#[test]
fn test_symbolic_ambiguous_unknown_input() {
    let tree = simple_switch_tree();
    let env = mk_env(&[]);
    let unknowns = vec![Name::from_string("x")];
    let result = symbolic_eval(&tree, &env, &unknowns);
    assert!(matches!(result, SymbolicResult::Ambiguous(ref arms) if arms.len() == 3));
}

#[test]
fn test_symbolic_no_match() {
    let tree = DecisionTree::Leaf(usize::MAX);
    let env = mk_env(&[]);
    let result = symbolic_eval(&tree, &env, &[]);
    assert_eq!(result, SymbolicResult::NoMatch);
}

#[test]
fn test_symbolic_guard_both_branches() {
    let tree = guard_tree();
    let env = mk_env(&[]);
    let result = symbolic_eval(&tree, &env, &[]);
    assert!(matches!(result, SymbolicResult::Ambiguous(ref arms) if arms == &[0, 1]));
}

#[test]
fn test_symbolic_nested_unknown() {
    let tree = nested_switch_tree();
    let env = mk_env(&[]);
    let unknowns = vec![Name::from_string("x"), Name::from_string("x_Some_f0")];
    let result = symbolic_eval(&tree, &env, &unknowns);
    assert!(matches!(result, SymbolicResult::Ambiguous(ref arms) if arms.len() == 3));
}

#[test]
fn test_symbolic_partial_known() {
    let tree = nested_switch_tree();
    let inner_val = mk_ctor_val("Just", vec![]);
    let env = mk_env(&[("x", mk_ctor_val("Some", vec![inner_val]))]);
    let unknowns = vec![Name::from_string("x_Some_f0")];
    let result = symbolic_eval(&tree, &env, &unknowns);
    assert!(matches!(result, SymbolicResult::Ambiguous(ref arms) if arms.len() == 2));
}
