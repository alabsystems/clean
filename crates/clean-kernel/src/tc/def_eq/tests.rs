// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! DefEq cache key tests and quick_is_def_eq basic tests.
//!
//! Delta failure cache and lazy delta reduction tests are in `tests_delta.rs`.

use super::*;
use crate::env::Environment;
use crate::expr::{BinderInfo, MDataValue};
use crate::level::Level;
use crate::tc::reduction::string_lit_to_constructor;
use std::collections::hash_map::DefaultHasher;
use std::collections::HashMap;

fn hash_key(key: &DefEqCacheKey) -> u64 {
    let mut hasher = DefaultHasher::new();
    key.hash(&mut hasher);
    hasher.finish()
}

#[test]
fn test_defeq_cache_key_is_order_invariant() {
    let a = Expr::nat_lit(1);
    let b = Expr::nat_lit(2);
    let key_ab = DefEqCacheKey::new(&a, &b, TransparencyMode::Default);
    let key_ba = DefEqCacheKey::new(&b, &a, TransparencyMode::Default);

    assert!(
        key_ab == key_ba,
        "def-eq cache key should treat (a, b) and (b, a) as the same pair"
    );
    assert_eq!(
        hash_key(&key_ab),
        hash_key(&key_ba),
        "unordered pair semantics require commutative hashing"
    );
}

#[test]
fn test_defeq_cache_key_separates_transparency_modes() {
    let a = Expr::prop();
    let b = Expr::type_();
    let key_default = DefEqCacheKey::new(&a, &b, TransparencyMode::Default);
    let key_all = DefEqCacheKey::new(&a, &b, TransparencyMode::All);

    assert!(
        key_default != key_all,
        "transparency mode must participate in cache-key equality"
    );

    let mut cache = HashMap::new();
    cache.insert(key_default, true);
    cache.insert(key_all, false);
    assert_eq!(
        cache.len(),
        2,
        "cache must keep separate entries for different transparency modes"
    );
}

#[test]
fn test_is_bool_true_const_requires_exact_name_and_no_levels() {
    let exact = Expr::const_(Name::from_string("Bool.true"), vec![]);
    let with_levels = Expr::const_(Name::from_string("Bool.true"), vec![Level::zero()]);
    let other = Expr::const_(Name::from_string("Bool.false"), vec![]);

    assert!(is_bool_true_const(&exact));
    assert!(!is_bool_true_const(&with_levels));
    assert!(!is_bool_true_const(&other));
}

#[test]
fn test_quick_is_def_eq_handles_literals_and_mdata_transparently() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    assert_eq!(
        tc.quick_is_def_eq(&Expr::nat_lit(11), &Expr::nat_lit(11)),
        Some(true)
    );
    assert_eq!(
        tc.quick_is_def_eq(&Expr::nat_lit(11), &Expr::nat_lit(12)),
        Some(false)
    );

    let md_left = Expr::mdata(
        vec![(Name::from_string("tag"), MDataValue::Nat(1))],
        Expr::nat_lit(5),
    );
    let md_right = Expr::mdata(vec![], Expr::nat_lit(5));
    let md_other = Expr::mdata(vec![], Expr::nat_lit(6));

    assert_eq!(tc.quick_is_def_eq(&md_left, &md_right), Some(true));
    assert_eq!(tc.quick_is_def_eq(&md_left, &md_other), Some(false));
}

#[test]
fn test_try_string_lit_expansion_core_accepts_string_of_list_form() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let lit = Expr::str_lit("clean");
    let expanded = string_lit_to_constructor("clean");
    assert!(
        tc.try_string_lit_expansion_core(&lit, &expanded),
        "string literal should def-eq String.ofList constructor form"
    );

    let wrong_head = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::nat_lit(0),
    );
    assert!(
        !tc.try_string_lit_expansion_core(&lit, &wrong_head),
        "non-String.ofList applications must be rejected"
    );
}

#[test]
fn test_lazy_delta_reduction_returns_final_pair_when_no_unfolding_possible() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let lhs = Expr::app(Expr::nat_lit(1), Expr::nat_lit(2));
    let rhs = Expr::app(Expr::nat_lit(3), Expr::nat_lit(4));

    assert_eq!(
        tc.lazy_delta_reduction(&lhs, &rhs),
        Err((lhs, rhs)),
        "when neither side is delta-reducible, lazy delta should return final expressions"
    );
}

#[test]
fn test_defeq_cache_reflexive_pairs_have_distinct_hashes() {
    let exprs = [
        Expr::nat_lit(0),
        Expr::nat_lit(1),
        Expr::nat_lit(42),
        Expr::prop(),
        Expr::type_(),
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::succ(Level::zero())))),
    ];

    let mut hashes = std::collections::HashSet::new();
    for e in &exprs {
        let key = DefEqCacheKey::new(e, e, TransparencyMode::Default);
        hashes.insert(hash_key(&key));
    }

    assert!(
        hashes.len() >= 3,
        "reflexive cache keys should have diverse hashes, got {} distinct out of {} keys \
         (XOR bug would give 1)",
        hashes.len(),
        exprs.len()
    );
}

#[test]
fn test_defeq_cache_reflexive_pairs_do_not_collide_in_hashmap() {
    let mut cache: HashMap<DefEqCacheKey, bool> = HashMap::new();
    let entries: Vec<Expr> = (0..20).map(Expr::nat_lit).collect();

    for e in &entries {
        let key = DefEqCacheKey::new(e, e, TransparencyMode::Default);
        cache.insert(key, true);
    }

    assert_eq!(
        cache.len(),
        20,
        "20 distinct reflexive pairs must be stored as 20 separate entries"
    );

    for e in &entries {
        let key = DefEqCacheKey::new(e, e, TransparencyMode::Default);
        assert_eq!(
            cache.get(&key),
            Some(&true),
            "reflexive entry for {:?} must be retrievable",
            e
        );
    }
}

#[test]
fn test_try_infer_type_quick_lambda_closed_body_returns_closed_type() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let lam = Expr::lam(
        BinderInfo::Default,
        Expr::const_(Name::from_string("Nat"), vec![]),
        Expr::nat_lit(42),
    );

    let ty = tc.try_infer_type_quick(&lam);
    assert!(
        ty.is_some(),
        "should infer type for lambda with closed body"
    );
    let ty = ty.unwrap();
    assert!(
        !ty.has_loose_bvars_quick(),
        "inferred type of closed lambda must not have loose BVars, got: {:?}",
        ty
    );
}

#[test]
fn test_try_infer_type_quick_lambda_open_body_returns_none() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let lam = Expr::lam(
        BinderInfo::Default,
        Expr::const_(Name::from_string("Nat"), vec![]),
        Expr::from_kind(ExprKind::BVar(0)),
    );

    let ty = tc.try_infer_type_quick(&lam);
    assert!(
        ty.is_none(),
        "should return None for lambda with body referencing BVar(0)"
    );
}

// === Branch-sharing tests (#3402) ===

/// Verify that is_def_eq_app_spine handles basic App spine comparison.
/// For `f a b` vs `f a b`, the spine comparison should return true.
#[test]
fn test_app_spine_basic_equality() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let f = Expr::const_(Name::from_string("f"), vec![]);
    let a = Expr::nat_lit(1);
    let b = Expr::nat_lit(2);

    // f a b
    let lhs = Expr::app(Expr::app(f.clone(), a.clone()), b.clone());
    // f a b (same)
    let rhs = Expr::app(Expr::app(f, a), b);

    assert!(
        tc.is_def_eq(&lhs, &rhs),
        "identical App spines must be def-eq"
    );
}

/// Verify that App spine comparison detects differences.
/// For `f a b` vs `f a c` where b != c, should return false.
#[test]
fn test_app_spine_detects_difference_in_last_arg() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let f = Expr::const_(Name::from_string("f"), vec![]);
    let a = Expr::nat_lit(1);
    let b = Expr::nat_lit(2);
    let c = Expr::nat_lit(3);

    let lhs = Expr::app(Expr::app(f.clone(), a.clone()), b);
    let rhs = Expr::app(Expr::app(f, a), c);

    assert!(
        !tc.is_def_eq(&lhs, &rhs),
        "spines differing in last arg must not be def-eq"
    );
}

/// Verify that App spine comparison handles mismatched arities by returning false.
/// For `f a` vs `f a b`, should return false from spine comparison.
#[test]
fn test_app_spine_mismatched_arity() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let f = Expr::const_(Name::from_string("f"), vec![]);
    let a = Expr::nat_lit(1);
    let b = Expr::nat_lit(2);

    let lhs = Expr::app(f.clone(), a.clone());
    let rhs = Expr::app(Expr::app(f, a), b);

    assert!(
        !tc.is_def_eq(&lhs, &rhs),
        "spines with different arities must not be def-eq"
    );
}

/// Simulate the branch-sharing scenario: multiple "branches" share a common
/// prefix in their application spines. After checking the first branch,
/// subsequent branches should benefit from cached equiv_manager entries.
///
/// This creates N expressions of the form `f shared_1 shared_2 unique_i`
/// and checks def-eq pairwise. The shared prefix should be cached after
/// the first comparison, making subsequent comparisons faster.
#[test]
fn test_app_spine_branch_sharing_cache_benefit() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let f = Expr::const_(Name::from_string("f"), vec![]);
    let shared1 = Expr::nat_lit(100);
    let shared2 = Expr::nat_lit(200);

    // Build "branches": f shared1 shared2 unique_i for i in 0..10
    let branches: Vec<Expr> = (0..10u64)
        .map(|i| {
            Expr::app(
                Expr::app(Expr::app(f.clone(), shared1.clone()), shared2.clone()),
                Expr::nat_lit(i),
            )
        })
        .collect();

    // Also build corresponding "target branches" with same structure
    // but fresh allocations (different pointers, same structure)
    let targets: Vec<Expr> = (0..10u64)
        .map(|i| {
            Expr::app(
                Expr::app(Expr::app(f.clone(), shared1.clone()), shared2.clone()),
                Expr::nat_lit(i),
            )
        })
        .collect();

    // Check def-eq for each pair — all should be equal
    for (i, (branch, target)) in branches.iter().zip(targets.iter()).enumerate() {
        assert!(
            tc.is_def_eq(branch, target),
            "branch {} should be def-eq to its target",
            i
        );
    }

    // Verify different branches are NOT equal to each other
    assert!(
        !tc.is_def_eq(&branches[0], &branches[1]),
        "branches with different unique suffixes must not be def-eq"
    );
}

/// Verify deep App spines work correctly: f a₁ a₂ ... a₁₀ vs same.
#[test]
fn test_app_spine_deep_chain() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let f = Expr::const_(Name::from_string("f"), vec![]);

    // Build f 1 2 3 4 5 6 7 8 9 10
    let mut lhs = f.clone();
    let mut rhs = f;
    for i in 1..=10u64 {
        lhs = Expr::app(lhs, Expr::nat_lit(i));
        rhs = Expr::app(rhs, Expr::nat_lit(i));
    }

    assert!(
        tc.is_def_eq(&lhs, &rhs),
        "deep App spines with identical args must be def-eq"
    );
}

// === Recursor branch-sharing tests (#3402) ===

/// Verify that try_branch_sharing_def_eq fires for identical Nat.rec applications.
///
/// Builds two structurally identical `Nat.rec motive zero_case succ_case n`
/// applications and confirms they are definitionally equal. The branch-sharing
/// path compares params, motives, minors, indices, and major arguments
/// individually using the BranchSharingCache.
#[test]
fn test_recursor_branch_sharing_identical() {
    use crate::expr::BinderInfo;

    let mut env = Environment::new();
    env.init_nat().unwrap();
    let tc = TypeChecker::new(&env);

    let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
    let nat_rec = Expr::const_(
        Name::from_string("Nat.rec"),
        vec![Level::succ(Level::zero())],
    );
    let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    // motive: fun _ : Nat => Nat
    let motive = Expr::lam(BinderInfo::Default, nat_const.clone(), nat_const.clone());

    // zero case: Nat.zero
    let zero_case = nat_zero.clone();

    // succ case: fun (n : Nat) (_ : Nat) => Nat.succ n
    let succ_case = Expr::lam(
        BinderInfo::Default,
        nat_const.clone(),
        Expr::lam(
            BinderInfo::Default,
            nat_const.clone(),
            Expr::app(
                Expr::const_(Name::from_string("Nat.succ"), vec![]),
                Expr::bvar(1),
            ),
        ),
    );

    // major: Nat.zero
    let major = nat_zero.clone();

    // Build Nat.rec motive zero_case succ_case major (both identical)
    let lhs = Expr::apps(
        nat_rec.clone(),
        [
            motive.clone(),
            zero_case.clone(),
            succ_case.clone(),
            major.clone(),
        ],
    );
    let rhs = Expr::apps(nat_rec, [motive, zero_case, succ_case, major]);

    assert!(
        tc.is_def_eq(&lhs, &rhs),
        "identical Nat.rec applications must be def-eq via branch sharing"
    );
}

/// Verify that try_branch_sharing_def_eq detects differences in minor premises.
///
/// Two Nat.rec applications with the same motive and major but different
/// minor premises (succ cases) must NOT be definitionally equal.
/// Uses `Nat.succ Nat.zero` as the major argument so that the succ case
/// actually fires (with `Nat.zero`, iota-reduction picks the zero case
/// and the succ minor is irrelevant).
#[test]
fn test_recursor_branch_sharing_different_minors() {
    use crate::expr::BinderInfo;

    let mut env = Environment::new();
    env.init_nat().unwrap();
    let tc = TypeChecker::new(&env);

    let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
    let nat_rec = Expr::const_(
        Name::from_string("Nat.rec"),
        vec![Level::succ(Level::zero())],
    );
    let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);

    let motive = Expr::lam(BinderInfo::Default, nat_const.clone(), nat_const.clone());
    let zero_case = nat_zero.clone();

    // succ_case_a: fun (n : Nat) (_ : Nat) => Nat.succ n
    let succ_case_a = Expr::lam(
        BinderInfo::Default,
        nat_const.clone(),
        Expr::lam(
            BinderInfo::Default,
            nat_const.clone(),
            Expr::app(nat_succ.clone(), Expr::bvar(1)),
        ),
    );

    // succ_case_b: fun (_ : Nat) (_ : Nat) => Nat.zero (constant zero)
    let succ_case_b = Expr::lam(
        BinderInfo::Default,
        nat_const.clone(),
        Expr::lam(BinderInfo::Default, nat_const.clone(), nat_zero.clone()),
    );

    // Major: Nat.succ Nat.zero (= 1), so the succ case fires
    let major = Expr::app(nat_succ, nat_zero.clone());

    let lhs = Expr::apps(
        nat_rec.clone(),
        [
            motive.clone(),
            zero_case.clone(),
            succ_case_a,
            major.clone(),
        ],
    );
    let rhs = Expr::apps(nat_rec, [motive, zero_case, succ_case_b, major]);

    // With major=1:
    // lhs reduces to Nat.succ Nat.zero = 1
    // rhs reduces to Nat.zero = 0
    // These are not def-eq.
    assert!(
        !tc.is_def_eq(&lhs, &rhs),
        "Nat.rec apps with different succ cases must not be def-eq when succ case fires"
    );
}

/// Verify branch-sharing works with Eq.rec which uses MajorAfterMinors layout.
///
/// Eq.rec has: num_params=2, num_motives=1, num_minors=1, num_indices=1
/// Layout: [param(alpha), param(a), motive, minor, index(b), major]
/// This tests the MajorAfterMinors RecursorArgOrder path.
#[test]
fn test_recursor_branch_sharing_eq_rec_congruence() {
    use crate::expr::BinderInfo;

    let mut env = Environment::new();
    env.init_eq().unwrap();
    env.init_true_false().unwrap();
    let tc = TypeChecker::new(&env);

    let prop = Expr::prop();
    let true_const = Expr::const_(Name::from_string("True"), vec![]);

    // motive: fun (b : Prop) (_ : Eq Prop True b) => Prop
    let motive = Expr::lam(
        BinderInfo::Default,
        prop.clone(),
        Expr::lam(BinderInfo::Default, Expr::prop(), Expr::prop()),
    );

    // minor: True (the refl case result)
    let minor = true_const.clone();

    // Eq.refl Prop True : Eq Prop True True
    let eq_refl = Expr::const_(
        Name::from_string("Eq.refl"),
        vec![Level::succ(Level::zero())],
    );
    let major = Expr::app(Expr::app(eq_refl, prop.clone()), true_const.clone());

    // Eq.rec {u1, u2} alpha a motive minor index major
    let eq_rec = Expr::const_(
        Name::from_string("Eq.rec"),
        vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
    );

    // Build identical applications with fresh allocations
    let lhs = Expr::apps(
        eq_rec.clone(),
        [
            prop.clone(),
            true_const.clone(),
            motive.clone(),
            minor.clone(),
            true_const.clone(), // index b = True
            major.clone(),
        ],
    );
    let rhs = Expr::apps(
        eq_rec,
        [
            prop.clone(),
            true_const.clone(),
            motive,
            minor,
            true_const, // index b = True
            major,
        ],
    );

    assert!(
        tc.is_def_eq(&lhs, &rhs),
        "identical Eq.rec applications must be def-eq via branch sharing"
    );
}

// === App spine branch-sharing with same-Const head tests (#3402) ===

/// Simulate the monadic bind case-split pattern from the issue: multiple
/// "branches" sharing a common function head and common prefix arguments,
/// differing only in the tail arguments.
///
/// This tests the enhanced `is_def_eq_app_spine` path where same-Const
/// function heads trigger `branch_sharing_compare` for each argument,
/// pre-caching no-delta WHNF results. After the first branch comparison,
/// subsequent branches should find the shared prefix cached.
#[test]
fn test_app_spine_same_const_head_shared_prefix() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Common function head: `semBinOp` (simulated as an opaque constant)
    let sem_bin_op = Expr::const_(Name::from_string("semBinOp"), vec![]);

    // Shared prefix: 4 monadic bind arguments (identical across all branches)
    let shared_bind1 = Expr::const_(Name::from_string("lookupValue.x"), vec![]);
    let shared_bind2 = Expr::const_(Name::from_string("lookupValue.y"), vec![]);
    let shared_bind3 = Expr::const_(Name::from_string("getState"), vec![]);
    let shared_bind4 = Expr::const_(Name::from_string("matchBinOp"), vec![]);

    // Build 10 "branches" with same head + shared prefix + unique suffix
    let branch_count = 10u64;
    let branches_a: Vec<Expr> = (0..branch_count)
        .map(|i| {
            Expr::apps(
                sem_bin_op.clone(),
                [
                    shared_bind1.clone(),
                    shared_bind2.clone(),
                    shared_bind3.clone(),
                    shared_bind4.clone(),
                    Expr::nat_lit(i), // unique divergent suffix
                ],
            )
        })
        .collect();

    // Build matching branches with fresh allocations (different pointers)
    let branches_b: Vec<Expr> = (0..branch_count)
        .map(|i| {
            Expr::apps(
                sem_bin_op.clone(),
                [
                    shared_bind1.clone(),
                    shared_bind2.clone(),
                    shared_bind3.clone(),
                    shared_bind4.clone(),
                    Expr::nat_lit(i),
                ],
            )
        })
        .collect();

    // Each branch pair should be def-eq (shared prefix + same suffix)
    for (i, (a, b)) in branches_a.iter().zip(branches_b.iter()).enumerate() {
        assert!(
            tc.is_def_eq(a, b),
            "branch {} should be def-eq to its counterpart",
            i
        );
    }

    // Different branches should NOT be def-eq (suffix differs)
    assert!(
        !tc.is_def_eq(&branches_a[0], &branches_a[1]),
        "branches with different suffixes must not be def-eq"
    );
}

/// Test that branch-sharing with same-Const head works for deeply nested
/// application spines (simulating complex monadic bind chains).
#[test]
fn test_app_spine_same_const_head_deep_prefix() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let bind = Expr::const_(Name::from_string("Bind.bind"), vec![]);

    // Build a 20-argument application with same head
    let shared_prefix: Vec<Expr> = (0..19u64)
        .map(|i| Expr::const_(Name::from_string(&format!("step{}", i)), vec![]))
        .collect();

    let mut lhs = bind.clone();
    for arg in &shared_prefix {
        lhs = Expr::app(lhs, arg.clone());
    }
    lhs = Expr::app(lhs, Expr::nat_lit(42)); // unique tail

    let mut rhs = bind.clone();
    for arg in &shared_prefix {
        rhs = Expr::app(rhs, arg.clone());
    }
    rhs = Expr::app(rhs, Expr::nat_lit(42)); // same unique tail

    assert!(
        tc.is_def_eq(&lhs, &rhs),
        "deep App spine with same-Const head and 20 shared prefix args must be def-eq"
    );

    // Different tail
    let mut rhs_diff = bind;
    for arg in &shared_prefix {
        rhs_diff = Expr::app(rhs_diff, arg.clone());
    }
    rhs_diff = Expr::app(rhs_diff, Expr::nat_lit(99));

    assert!(
        !tc.is_def_eq(&lhs, &rhs_diff),
        "same prefix but different tail must not be def-eq"
    );
}

/// Test that non-Const function heads (e.g., FVar or App) fall back to
/// regular is_def_eq_impl without using branch-sharing cache.
#[test]
fn test_app_spine_non_const_head_fallback() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // FVar heads: branch-sharing cache should NOT be used (heads_are_same_const
    // returns false), but def-eq should still work correctly.
    let fvar_head = Expr::fvar(crate::expr::FVarId(0));
    let lhs = Expr::app(
        Expr::app(fvar_head.clone(), Expr::nat_lit(1)),
        Expr::nat_lit(2),
    );
    let rhs = Expr::app(Expr::app(fvar_head, Expr::nat_lit(1)), Expr::nat_lit(2));

    assert!(
        tc.is_def_eq(&lhs, &rhs),
        "FVar-headed spines should still be def-eq via regular path"
    );
}

/// Verify that the branch-sharing cache provides cross-call benefit across
/// multiple is_def_eq calls with shared substructure. This simulates the
/// semBinOp pattern: 49 branches sharing 4 monadic binds.
#[test]
fn test_app_spine_cross_call_cache_reuse() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let f = Expr::const_(Name::from_string("semBinOp"), vec![]);

    // Build complex shared prefix using nested lambda/app expressions
    // that require actual WHNF reduction to compare.
    let shared_arg = Expr::lam(
        BinderInfo::Default,
        Expr::sort(Level::zero()),
        Expr::bvar(0),
    );

    // Build 49 branch pairs (simulating 7x7 constructor match)
    let branch_count = 49u64;
    for i in 0..branch_count {
        let lhs = Expr::apps(
            f.clone(),
            [shared_arg.clone(), shared_arg.clone(), Expr::nat_lit(i)],
        );
        let rhs = Expr::apps(
            f.clone(),
            [shared_arg.clone(), shared_arg.clone(), Expr::nat_lit(i)],
        );
        assert!(
            tc.is_def_eq(&lhs, &rhs),
            "branch {} of 49 must be def-eq",
            i
        );
    }

    // Verify cross-branch inequality still holds
    let branch_0 = Expr::apps(
        f.clone(),
        [shared_arg.clone(), shared_arg.clone(), Expr::nat_lit(0)],
    );
    let branch_48 = Expr::apps(f, [shared_arg.clone(), shared_arg, Expr::nat_lit(48)]);
    assert!(
        !tc.is_def_eq(&branch_0, &branch_48),
        "branches 0 and 48 with different suffixes must not be def-eq"
    );
}

// === Prefix-factored lambda branch sharing tests (#3402) ===

/// Test the verified-pair mechanism: once a pair of expressions is confirmed
/// def-eq, subsequent comparisons of the same pair return immediately.
///
/// Constructs two structurally identical complex expressions, compares them
/// once (populating the verified-pair set), then compares again. The second
/// comparison should be essentially free.
#[test]
fn test_branch_sharing_verified_pair_reuse() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let f = Expr::const_(Name::from_string("f"), vec![]);
    let complex_arg = Expr::lam(
        BinderInfo::Default,
        Expr::sort(Level::zero()),
        Expr::app(Expr::const_(Name::from_string("g"), vec![]), Expr::bvar(0)),
    );

    let lhs = Expr::apps(f.clone(), [complex_arg.clone(), Expr::nat_lit(1)]);
    let rhs = Expr::apps(f.clone(), [complex_arg.clone(), Expr::nat_lit(1)]);

    // First call: verifies and records the pair
    assert!(tc.is_def_eq(&lhs, &rhs), "first comparison should succeed");

    // Build fresh allocations of the same expressions
    let lhs2 = Expr::apps(f.clone(), [complex_arg.clone(), Expr::nat_lit(1)]);
    let rhs2 = Expr::apps(f, [complex_arg, Expr::nat_lit(1)]);

    // Second call: should reuse cached verified pairs
    assert!(
        tc.is_def_eq(&lhs2, &rhs2),
        "second comparison should reuse cache"
    );
}

/// Test lambda-bodied minor premise prefix factoring.
///
/// Simulates the semBinOp pattern: minor premises are lambdas whose bodies
/// share a common prefix of monadic binds. Constructs N lambda-bodied
/// branches with identical prefix and different suffixes, and verifies
/// that:
/// 1. Self-comparisons succeed
/// 2. Cross-branch comparisons with different suffixes fail
/// 3. The shared prefix is not re-verified after the first branch
#[test]
fn test_branch_sharing_lambda_body_prefix_factoring() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let bind = Expr::const_(Name::from_string("Bind.bind"), vec![]);
    let step1 = Expr::const_(Name::from_string("lookupValue"), vec![]);
    let step2 = Expr::const_(Name::from_string("getState"), vec![]);
    let step3 = Expr::const_(Name::from_string("matchOp"), vec![]);

    // Build 7 lambda-bodied branches with shared prefix:
    // fun (x : Nat) => Bind.bind step1 step2 step3 <unique_i>
    let branches: Vec<(Expr, Expr)> = (0..7u64)
        .map(|i| {
            let body_a = Expr::apps(
                bind.clone(),
                [
                    step1.clone(),
                    step2.clone(),
                    step3.clone(),
                    Expr::nat_lit(i),
                ],
            );
            let body_b = Expr::apps(
                bind.clone(),
                [
                    step1.clone(),
                    step2.clone(),
                    step3.clone(),
                    Expr::nat_lit(i),
                ],
            );
            let lam_a = Expr::lam(BinderInfo::Default, nat_ty.clone(), body_a);
            let lam_b = Expr::lam(BinderInfo::Default, nat_ty.clone(), body_b);
            (lam_a, lam_b)
        })
        .collect();

    // Each branch pair should be def-eq
    for (i, (a, b)) in branches.iter().enumerate() {
        assert!(
            tc.is_def_eq(a, b),
            "branch {} lambda pair should be def-eq",
            i
        );
    }

    // Different branches should NOT be def-eq
    assert!(
        !tc.is_def_eq(&branches[0].0, &branches[1].0),
        "branches with different suffixes must not be def-eq"
    );
}

/// Test the full 7x7 = 49 branch case-split pattern.
///
/// Mimics `semBinOp` matching on two `Value` arguments with 7 constructors
/// each. Each branch is a lambda with a shared monadic prefix of 4 binds
/// followed by a unique operation.
#[test]
fn test_branch_sharing_7x7_case_split_pattern() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let bind = Expr::const_(Name::from_string("Bind.bind"), vec![]);

    // 4 shared monadic bind steps (common prefix across all 49 branches)
    let prefix_steps: Vec<Expr> = (0..4u64)
        .map(|i| Expr::const_(Name::from_string(&format!("monadicStep{}", i)), vec![]))
        .collect();

    // Build 49 branch pairs (7 x 7)
    let branch_count = 49u64;
    for i in 0..branch_count {
        let mut args_a = prefix_steps.clone();
        args_a.push(Expr::nat_lit(i));
        let body_a = Expr::apps(bind.clone(), args_a);

        let mut args_b = prefix_steps.clone();
        args_b.push(Expr::nat_lit(i));
        let body_b = Expr::apps(bind.clone(), args_b);

        let lam_a = Expr::lam(BinderInfo::Default, nat_ty.clone(), body_a);
        let lam_b = Expr::lam(BinderInfo::Default, nat_ty.clone(), body_b);

        assert!(
            tc.is_def_eq(&lam_a, &lam_b),
            "49-branch case split: branch {} should be def-eq to its counterpart",
            i
        );
    }

    // Cross-branch inequality: branch 0 vs branch 48
    let mut args_0 = prefix_steps.clone();
    args_0.push(Expr::nat_lit(0));
    let branch_0 = Expr::lam(
        BinderInfo::Default,
        nat_ty.clone(),
        Expr::apps(bind.clone(), args_0),
    );

    let mut args_48 = prefix_steps;
    args_48.push(Expr::nat_lit(48));
    let branch_48 = Expr::lam(BinderInfo::Default, nat_ty, Expr::apps(bind, args_48));

    assert!(
        !tc.is_def_eq(&branch_0, &branch_48),
        "branches 0 and 48 with different operations must not be def-eq"
    );
}

/// Test prefix factoring with nested lambda binders.
///
/// Branch lambdas take multiple arguments:
/// fun (x : Nat) (y : Nat) => f prefix1 prefix2 <unique>
/// The prefix should be shared across branches regardless of binder depth.
#[test]
fn test_branch_sharing_nested_lambda_binders() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let f = Expr::const_(Name::from_string("evalBinOp"), vec![]);
    let prefix1 = Expr::const_(Name::from_string("normalize"), vec![]);
    let prefix2 = Expr::const_(Name::from_string("typecheck"), vec![]);

    // Branch: fun (x : Nat) (y : Nat) => f prefix1 prefix2 unique_i
    let make_branch = |unique: u64| {
        Expr::lam(
            BinderInfo::Default,
            nat_ty.clone(),
            Expr::lam(
                BinderInfo::Default,
                nat_ty.clone(),
                Expr::apps(
                    f.clone(),
                    [prefix1.clone(), prefix2.clone(), Expr::nat_lit(unique)],
                ),
            ),
        )
    };

    // 20 branches with shared double-lambda prefix
    for i in 0..20u64 {
        let a = make_branch(i);
        let b = make_branch(i);
        assert!(
            tc.is_def_eq(&a, &b),
            "nested lambda branch {} should be def-eq",
            i
        );
    }

    // Inequality: different unique suffix
    assert!(
        !tc.is_def_eq(&make_branch(0), &make_branch(19)),
        "nested lambda branches with different suffixes must differ"
    );
}

/// Test that prefix factoring handles the case where branches have
/// different binder arities (some take 1 arg, others take 2).
/// The comparison should still work correctly via fallback.
#[test]
fn test_branch_sharing_mixed_binder_arities() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);

    // Branch A: fun (x : Nat) => nat_lit(42)
    let branch_a = Expr::lam(BinderInfo::Default, nat_ty.clone(), Expr::nat_lit(42));

    // Branch B: fun (x : Nat) (y : Nat) => nat_lit(42)
    let branch_b = Expr::lam(
        BinderInfo::Default,
        nat_ty.clone(),
        Expr::lam(BinderInfo::Default, nat_ty, Expr::nat_lit(42)),
    );

    // These should NOT be def-eq (different binder structure)
    assert!(
        !tc.is_def_eq(&branch_a, &branch_b),
        "branches with different binder arities must not be def-eq"
    );
}

/// Test that the branch-sharing optimization preserves correctness when
/// expressions have hash collisions (same cached hash but different structure).
#[test]
fn test_branch_sharing_hash_collision_safety() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let f = Expr::const_(Name::from_string("f"), vec![]);

    // Even if two different expressions happen to have the same 32-bit hash,
    // the full def-eq comparison must still be correct. We can't manufacture
    // hash collisions easily, but we verify that different expressions with
    // similar structure are correctly distinguished.
    let a = Expr::apps(f.clone(), [Expr::nat_lit(0), Expr::nat_lit(1)]);
    let b = Expr::apps(f, [Expr::nat_lit(1), Expr::nat_lit(0)]);

    assert!(
        !tc.is_def_eq(&a, &b),
        "expressions with swapped args must not be def-eq despite same head"
    );
}
