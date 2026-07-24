// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Contract-oriented tests for `TypeCheckCache`.
//!
//! These are issue #988 "Kani-style" properties: each test targets a documented
//! cache invariant rather than only exercising the surface API.

use crate::cache::{TypeCheckCache, TypeCheckId};
use crate::expr::{BinderInfo, Expr, ExprKind, ExprMeta};
use crate::level::Level;
use crate::name::Name;
use proptest::prelude::*;

fn sample_expr(seed: u8) -> Expr {
    match seed % 8 {
        0 => Expr::prop(),
        1 => Expr::type_(),
        2 => Expr::const_(Name::from_string(&format!("Const{seed}")), vec![]),
        3 => Expr::app(
            Expr::const_(Name::from_string(&format!("f{}", seed % 4)), vec![]),
            Expr::const_(Name::from_string(&format!("x{}", seed % 4)), vec![]),
        ),
        4 => Expr::lam(
            BinderInfo::Default,
            Expr::type_(),
            Expr::from_kind(ExprKind::BVar(0)),
        ),
        5 => Expr::pi(BinderInfo::Default, Expr::type_(), Expr::prop()),
        6 => Expr::const_(Name::from_string("List"), vec![Level::zero()]),
        _ => Expr::const_(Name::from_string("List"), vec![Level::succ(Level::zero())]),
    }
}

fn sample_value(seed: u8) -> Expr {
    match seed % 6 {
        0 => Expr::prop(),
        1 => Expr::type_(),
        2 => Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
        3 => Expr::const_(Name::from_string("Nat"), vec![]),
        4 => Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_()),
        _ => Expr::app(
            Expr::const_(Name::from_string("Result"), vec![]),
            Expr::prop(),
        ),
    }
}

fn fresh_type_for(expr: &Expr, env_hash: u64, mode_hash: u64) -> Expr {
    let seed = (expr.hash_cached() as u64) ^ env_hash.rotate_left(7) ^ mode_hash.rotate_right(3);
    sample_value(seed as u8)
}

proptest! {
    #[test]
    fn prop_type_check_id_tracks_expr_env_and_mode(
        expr_seed in any::<u8>(),
        env_hash in any::<u64>(),
        mode_hash in any::<u64>(),
        other_env_hash in any::<u64>(),
        other_mode_hash in any::<u64>(),
    ) {
        let expr = sample_expr(expr_seed);
        let same_expr = sample_expr(expr_seed);

        prop_assert_eq!(
            TypeCheckId::new(&expr, env_hash, mode_hash),
            TypeCheckId::new(&same_expr, env_hash, mode_hash),
            "equal expressions with equal hashes must produce equal TypeCheckIds",
        );

        if other_env_hash != env_hash {
            prop_assert_ne!(
                TypeCheckId::new(&expr, env_hash, mode_hash),
                TypeCheckId::new(&expr, other_env_hash, mode_hash),
                "env_hash must be part of the cache key",
            );
        }

        if other_mode_hash != mode_hash {
            prop_assert_ne!(
                TypeCheckId::new(&expr, env_hash, mode_hash),
                TypeCheckId::new(&expr, env_hash, other_mode_hash),
                "mode_hash must be part of the cache key",
            );
        }
    }

    #[test]
    fn prop_empty_cache_returns_none_for_all_lookups(
        expr_seed in any::<u8>(),
        env_hash in any::<u64>(),
        mode_hash in any::<u64>(),
    ) {
        let expr = sample_expr(expr_seed);
        let mut cache = TypeCheckCache::with_hashes(env_hash, mode_hash);

        prop_assert!(cache.is_empty());
        prop_assert_eq!(cache.len(), 0);
        prop_assert_eq!(cache.get(&expr), None);
        prop_assert_eq!(cache.stats().hits, 0);
        prop_assert_eq!(cache.stats().misses, 1);
        prop_assert_eq!(cache.stats().entries, 0);
    }

    #[test]
    fn prop_insert_followed_by_get_returns_inserted_value(
        expr_seed in any::<u8>(),
        value_seed in any::<u8>(),
        env_hash in any::<u64>(),
        mode_hash in any::<u64>(),
    ) {
        let expr = sample_expr(expr_seed);
        let inserted = sample_value(value_seed);
        let mut cache = TypeCheckCache::with_hashes(env_hash, mode_hash);

        cache.insert(&expr, inserted.clone());

        prop_assert_eq!(cache.get(&expr).cloned(), Some(inserted));
        prop_assert_eq!(cache.len(), 1);
        prop_assert_eq!(cache.stats().entries, cache.len());
        prop_assert_eq!(cache.stats().hits, 1);
        prop_assert_eq!(cache.stats().misses, 0);
    }

    #[test]
    fn prop_cache_hits_return_same_result_as_fresh_computation(
        expr_seed in any::<u8>(),
        env_hash in any::<u64>(),
        mode_hash in any::<u64>(),
    ) {
        let expr = sample_expr(expr_seed);
        let expected = fresh_type_for(&expr, env_hash, mode_hash);
        let mut cache = TypeCheckCache::with_hashes(env_hash, mode_hash);

        cache.insert(&expr, expected.clone());

        let first_hit = cache.get(&expr).cloned();
        let fresh_again = fresh_type_for(&expr, env_hash, mode_hash);
        let second_hit = cache.get(&expr).cloned();

        prop_assert_eq!(first_hit, Some(expected));
        prop_assert_eq!(second_hit, Some(fresh_again));
        prop_assert_eq!(cache.stats().hits, 2);
        prop_assert_eq!(cache.stats().misses, 0);
    }

    #[test]
    fn prop_same_env_hash_preserves_cached_entries(
        expr_seed in any::<u8>(),
        env_hash in any::<u64>(),
        mode_hash in any::<u64>(),
    ) {
        let expr = sample_expr(expr_seed);
        let expected = fresh_type_for(&expr, env_hash, mode_hash);
        let mut cache = TypeCheckCache::with_hashes(env_hash, mode_hash);

        cache.insert(&expr, expected.clone());
        cache.set_env_hash(env_hash);

        prop_assert_eq!(cache.env_hash(), env_hash);
        prop_assert_eq!(cache.len(), 1);
        prop_assert_eq!(cache.stats().entries, 1);
        prop_assert_eq!(cache.get(&expr).cloned(), Some(expected));
    }

    #[test]
    fn prop_env_hash_change_invalidates_existing_entries(
        expr_seed in any::<u8>(),
        env_hash in any::<u64>(),
        new_env_hash in any::<u64>(),
        mode_hash in any::<u64>(),
    ) {
        prop_assume!(new_env_hash != env_hash);

        let expr = sample_expr(expr_seed);
        let miss_expr = sample_expr(expr_seed.wrapping_add(1));
        let expected = fresh_type_for(&expr, env_hash, mode_hash);
        let mut cache = TypeCheckCache::with_hashes(env_hash, mode_hash);

        let _ = cache.get(&miss_expr);
        cache.insert(&expr, expected);
        let _ = cache.get(&expr);
        let hits_before = cache.stats().hits;
        let misses_before = cache.stats().misses;

        cache.set_env_hash(new_env_hash);

        prop_assert_eq!(cache.env_hash(), new_env_hash);
        prop_assert!(cache.is_empty());
        prop_assert_eq!(cache.len(), 0);
        prop_assert_eq!(cache.stats().entries, 0);
        prop_assert_eq!(cache.stats().hits, hits_before);
        prop_assert_eq!(cache.stats().misses, misses_before);
        prop_assert_eq!(cache.get(&expr), None);
        prop_assert_eq!(cache.stats().misses, misses_before + 1);
    }
}

#[test]
fn contract_mode_hash_change_invalidates_existing_entries() {
    let env_hash = 17;
    let old_mode_hash = 3;
    let new_mode_hash = 9;
    let expr = sample_expr(3);
    let expected = fresh_type_for(&expr, env_hash, old_mode_hash);
    let mut cache = TypeCheckCache::with_hashes(env_hash, old_mode_hash);

    cache.insert(&expr, expected);
    cache.set_mode_hash(new_mode_hash);

    assert_eq!(cache.mode_hash(), new_mode_hash);
    assert!(cache.is_empty());
    assert_eq!(cache.len(), 0);
    assert_eq!(cache.stats().entries, 0);
    assert_eq!(cache.get(&expr), None);
}

#[test]
fn contract_hash_collisions_do_not_cross_contaminate_results() {
    let collision_hash = 0xDEAD_BEEF;
    let env_hash = 11;
    let mode_hash = 7;

    let expr_a = Expr::with_meta(
        ExprKind::BVar(0),
        ExprMeta::pack(collision_hash, 0, 0, false, false, false, false),
    );
    let expr_b = Expr::with_meta(
        ExprKind::BVar(1),
        ExprMeta::pack(collision_hash, 0, 0, false, false, false, false),
    );

    assert_ne!(
        expr_a, expr_b,
        "collision test requires distinct expressions"
    );
    assert_eq!(
        expr_a.hash_cached(),
        expr_b.hash_cached(),
        "collision test requires identical cached hashes",
    );
    assert_ne!(
        TypeCheckId::new(&expr_a, env_hash, mode_hash),
        TypeCheckId::new(&expr_b, env_hash, mode_hash),
        "TypeCheckId must use structural equality to reject hash-only collisions",
    );

    let type_a = Expr::prop();
    let type_b = Expr::type_();
    let mut cache = TypeCheckCache::with_hashes(env_hash, mode_hash);
    cache.insert(&expr_a, type_a.clone());
    cache.insert(&expr_b, type_b.clone());

    assert_eq!(cache.len(), 2);
    assert_eq!(cache.get(&expr_a).cloned(), Some(type_a));
    assert_eq!(cache.get(&expr_b).cloned(), Some(type_b));
}

#[test]
fn contract_clear_removes_all_entries_and_resets_statistics() {
    let env_hash = 41;
    let mode_hash = 13;
    let expr_a = sample_expr(2);
    let expr_b = sample_expr(5);
    let type_a = fresh_type_for(&expr_a, env_hash, mode_hash);
    let type_b = fresh_type_for(&expr_b, env_hash, mode_hash);
    let miss_expr = sample_expr(7);
    let mut cache = TypeCheckCache::with_hashes(env_hash, mode_hash);

    cache.insert(&expr_a, type_a.clone());
    cache.insert(&expr_b, type_b.clone());
    assert_eq!(cache.get(&expr_a).cloned(), Some(type_a));
    assert_eq!(cache.get(&miss_expr), None);

    cache.clear();

    assert!(cache.is_empty());
    assert_eq!(cache.len(), 0);
    assert_eq!(cache.stats().hits, 0);
    assert_eq!(cache.stats().misses, 0);
    assert_eq!(cache.stats().entries, 0);
    assert_eq!(cache.env_hash(), env_hash);
    assert_eq!(cache.mode_hash(), mode_hash);
    assert_eq!(cache.get(&expr_b), None);
}
