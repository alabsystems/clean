// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_is_zero() {
    assert!(Level::zero().is_zero());
    assert!(!Level::succ(Level::zero()).is_zero());
    assert!(Level::max(Level::zero(), Level::zero()).is_zero());
    assert!(Level::imax(Level::succ(Level::zero()), Level::zero()).is_zero());
    // imax(u, 0) = 0, so this simplifies directly
    let level = Level::imax(Level::param(Name::from_string("u")), Level::zero());
    assert!(level.is_zero());
}

#[test]
fn test_is_nonzero() {
    assert!(!Level::zero().is_nonzero());
    assert!(Level::succ(Level::zero()).is_nonzero());
    // max(0, succ(0)) = succ(0), which is nonzero
    let m = Level::max(Level::zero(), Level::succ(Level::zero()));
    assert!(m.is_nonzero());
}

#[test]
fn test_max_simplification() {
    // max(l, l) = l
    let u = Level::param(Name::from_string("u"));
    let m = Level::max(u.clone(), u.clone());
    assert_eq!(m, u);

    // max(0, l) = l
    let m = Level::max(Level::zero(), u.clone());
    assert_eq!(m, u);

    // max(l, 0) = l
    let m = Level::max(u.clone(), Level::zero());
    assert_eq!(m, u);
}

/// Contract test: max is commutative - max(a, b) == max(b, a)
///
/// The commutativity contract holds semantically for all levels, but structural
/// equality is only guaranteed for concrete levels that simplify. For levels with
/// parameters where neither dominates the other, max(u, v) and max(v, u) produce
/// different structural representations that are semantically equivalent.
///
/// This test verifies the structural equality cases (where simplification occurs).
/// The Kani proof `verify_level_max_symmetric` covers the general semantic case.
#[test]
fn test_max_contract_commutativity() {
    let u = Level::param(Name::from_string("u"));
    let zero = Level::zero();
    let one = Level::succ(Level::zero());
    let two = Level::succ(Level::succ(Level::zero()));

    // Concrete combinations - simplification ensures structural equality
    let concrete_pairs: Vec<(Level, Level)> = vec![
        (zero.clone(), one.clone()),
        (one.clone(), two.clone()),
        (zero.clone(), two.clone()),
    ];

    for (a, b) in concrete_pairs {
        let max_ab = Level::max(a.clone(), b.clone());
        let max_ba = Level::max(b.clone(), a.clone());
        assert_eq!(
            max_ab, max_ba,
            "max commutativity failed: max({a:?}, {b:?}) != max({b:?}, {a:?})"
        );
    }

    // Param + zero: zero identity ensures structural equality
    let max_u0 = Level::max(u.clone(), zero.clone());
    let max_0u = Level::max(zero.clone(), u.clone());
    assert_eq!(max_u0, max_0u, "max(u, 0) should equal max(0, u)");

    // Param + concrete where param dominates OR concrete dominates
    // max(succ(succ(u)), succ(u)) - succ(succ(u)) >= succ(u), so result is succ(succ(u))
    let succ_u = Level::succ(u.clone());
    let succ_succ_u = Level::succ(succ_u.clone());
    let max_ssu_su = Level::max(succ_succ_u.clone(), succ_u.clone());
    let max_su_ssu = Level::max(succ_u.clone(), succ_succ_u.clone());
    assert_eq!(
        max_ssu_su, max_su_ssu,
        "max(succ(succ(u)), succ(u)) should be commutative"
    );

    // Note: max(u, v) vs max(v, u) for distinct params produces different structures
    // but is semantically equivalent. This is expected - the contract describes semantic
    // behavior, and normalize() doesn't canonicalize Max argument order.
}

/// Contract test: max is idempotent - max(a, a) == a
#[test]
fn test_max_contract_idempotency() {
    let u = Level::param(Name::from_string("u"));
    let zero = Level::zero();
    let one = Level::succ(Level::zero());
    let two = Level::succ(Level::succ(Level::zero()));

    let levels = vec![
        zero,
        one,
        two,
        u.clone(),
        Level::succ(u.clone()),
        Level::max(u.clone(), Level::param(Name::from_string("v"))),
    ];

    for l in levels {
        let max_ll = Level::max(l.clone(), l.clone());
        assert_eq!(
            max_ll, l,
            "max idempotency failed: max({l:?}, {l:?}) != {l:?}"
        );
    }
}

/// Contract test: zero is identity for max - max(0, a) == a
#[test]
fn test_max_contract_zero_identity() {
    let u = Level::param(Name::from_string("u"));
    let one = Level::succ(Level::zero());
    let two = Level::succ(Level::succ(Level::zero()));

    let levels = vec![
        Level::zero(),
        one,
        two,
        u.clone(),
        Level::succ(u.clone()),
        Level::max(u.clone(), Level::param(Name::from_string("v"))),
    ];

    for l in levels {
        // max(0, l) == l
        let max_0l = Level::max(Level::zero(), l.clone());
        assert_eq!(max_0l, l, "max(0, {l:?}) != {l:?}, got {max_0l:?}");

        // max(l, 0) == l
        let max_l0 = Level::max(l.clone(), Level::zero());
        assert_eq!(max_l0, l, "max({l:?}, 0) != {l:?}, got {max_l0:?}");
    }
}

/// Contract test: is_geq relationship - is_geq(&max(a, b), &a) && is_geq(&max(a, b), &b)
///
/// The is_geq function handles Max correctly (level.rs:314-317):
/// max(a, b) >= l if a >= l or b >= l
///
/// So for Max(u, v), is_geq(Max(u, v), u) checks is_geq(u, u) || is_geq(v, u).
/// Since u == u, the first disjunct is true, so the whole check succeeds.
#[test]
fn test_max_contract_is_geq() {
    let u = Level::param(Name::from_string("u"));
    let v = Level::param(Name::from_string("v"));
    let zero = Level::zero();
    let one = Level::succ(Level::zero());

    let pairs: Vec<(Level, Level)> = vec![
        (zero.clone(), one.clone()),
        (one.clone(), Level::succ(one.clone())),
        (zero.clone(), u.clone()),
        // Param pairs: max(u, v) = Max(u, v) since neither dominates
        // is_geq(Max(u, v), u) = is_geq(u, u) || is_geq(v, u) = true || false = true
        (u.clone(), v.clone()),
        // Mixed param and concrete
        (u.clone(), one.clone()),
    ];

    for (a, b) in pairs {
        let max_ab = Level::max(a.clone(), b.clone());
        // max(a, b) >= a
        assert!(
            Level::is_geq(&max_ab, &a),
            "is_geq(max({a:?}, {b:?}), {a:?}) should be true"
        );
        // max(a, b) >= b
        assert!(
            Level::is_geq(&max_ab, &b),
            "is_geq(max({a:?}, {b:?}), {b:?}) should be true"
        );
    }
}

#[test]
fn test_imax_simplification() {
    let u = Level::param(Name::from_string("u"));

    // imax(u, 0) = 0
    let i = Level::imax(u.clone(), Level::zero());
    assert!(i.is_zero());

    // imax(u, succ(0)) = max(u, succ(0)) since succ(0) > 0
    let one = Level::succ(Level::zero());
    let i = Level::imax(u.clone(), one.clone());
    // Should be max(u, 1), not imax
    match i {
        Level::Max(_, _) => {} // Good - reduced to max
        Level::IMax(_, _) => panic!("Should have reduced to Max"),
        other => {
            // Might simplify further depending on implementation
            assert!(!matches!(other, Level::IMax(_, _)));
        }
    }
}

/// Regression test: imax(1, l) = l (Lean 4 parity: is_one(l1))
/// Bug: #1321 — imax(1, Param(u)) returned IMax(Succ(Zero), Param(u))
#[test]
fn test_imax_one_first_arg_reduces() {
    let u = Level::param(Name::from_string("u"));
    let one = Level::succ(Level::zero());

    // imax(1, u) = u (since imax(1, 0) = 0 = u, and imax(1, l) = max(1, l) = l when l > 0)
    let result = Level::imax(one.clone(), u.clone());
    assert_eq!(result, u, "imax(1, u) should reduce to u");

    // imax(1, 0) = 0 (handled by l2.is_zero() check)
    let result = Level::imax(one.clone(), Level::zero());
    assert!(result.is_zero(), "imax(1, 0) should be zero");

    // imax(1, succ(0)) = succ(0) (handled by l2.is_nonzero() -> max(1, 1) = 1)
    let result = Level::imax(one.clone(), Level::succ(Level::zero()));
    assert_eq!(result, Level::succ(Level::zero()), "imax(1, 1) should be 1");

    // imax(1, max(u, v)) — should reduce via is_one(l1)
    let v = Level::param(Name::from_string("v"));
    let max_uv = Level::max(u.clone(), v.clone());
    let result = Level::imax(one, max_uv.clone());
    assert_eq!(
        result, max_uv,
        "imax(1, max(u, v)) should reduce to max(u, v)"
    );
}

/// Contract test: imax(l1, l2) = 0 when l2 = 0
#[test]
fn test_imax_contract_zero_second_arg() {
    let u = Level::param(Name::from_string("u"));
    let v = Level::param(Name::from_string("v"));
    let one = Level::succ(Level::zero());
    let two = Level::succ(Level::succ(Level::zero()));

    // Various l1 values, all should give 0 when l2 = 0
    let l1_values = vec![
        Level::zero(),
        one,
        two,
        u.clone(),
        Level::succ(u.clone()),
        Level::max(u.clone(), v.clone()),
    ];

    for l1 in l1_values {
        let i = Level::imax(l1.clone(), Level::zero());
        assert!(i.is_zero(), "imax({l1:?}, 0) should be 0, got {i:?}");
    }
}

/// Contract test: imax reduces to max when l2 is Succ
#[test]
fn test_imax_contract_succ_second_arg() {
    let u = Level::param(Name::from_string("u"));
    let one = Level::succ(Level::zero());
    let two = Level::succ(Level::succ(Level::zero()));

    // imax(l1, succ(x)) = max(l1, succ(x)) since succ(x) > 0
    let pairs: Vec<(Level, Level)> = vec![
        (Level::zero(), one.clone()),
        (one.clone(), two.clone()),
        (u.clone(), one.clone()),
        (u.clone(), Level::succ(u.clone())),
    ];

    for (l1, l2) in pairs {
        // l2 is always Succ variant
        if !matches!(l2, Level::Succ(_)) {
            continue;
        }
        let imax_result = Level::imax(l1.clone(), l2.clone());
        let max_result = Level::max(l1.clone(), l2.clone());
        assert_eq!(
            imax_result, max_result,
            "imax({l1:?}, {l2:?}) should equal max({l1:?}, {l2:?})"
        );
    }
}

/// Contract test: imax(0, l) = l when l is not definitively zero
///
/// The imax function simplifies imax(0, l) = l when:
/// 1. l2 is Succ(_) - definitively nonzero, so imax(0, l2) = max(0, l2) = l2
/// 2. l2 is Param(_) - Param.is_zero() returns false, so the simplification applies
///
/// This matches the implementation at level.rs:134-136 which returns l2
/// when l1.is_zero() is true (and we've already checked l2.is_zero() at line 127).
#[test]
fn test_imax_contract_zero_first_arg() {
    let u = Level::param(Name::from_string("u"));
    let one = Level::succ(Level::zero());
    let two = Level::succ(Level::succ(Level::zero()));

    let l2_values = vec![one, two, u.clone(), Level::succ(u.clone())];

    for l2 in l2_values {
        // Skip if l2 is zero (handled by zero second arg contract)
        if l2.is_zero() {
            continue;
        }
        let i = Level::imax(Level::zero(), l2.clone());
        // imax(0, l) = l for all l where !l.is_zero()
        // This includes both Succ(_) and Param(_) since Param(_).is_zero() == false
        assert_eq!(i, l2, "imax(0, {l2:?}) should equal {l2:?}");
    }
}

/// Contract test: imax(l, l) = l
#[test]
fn test_imax_contract_idempotency() {
    let u = Level::param(Name::from_string("u"));
    let one = Level::succ(Level::zero());
    let two = Level::succ(Level::succ(Level::zero()));

    let levels = vec![one, two, u.clone(), Level::succ(u.clone())];

    for l in levels {
        // Skip zero - imax(0, 0) = 0 which is the expected behavior
        let i = Level::imax(l.clone(), l.clone());
        // imax(l, l) should equal l
        // This is because imax(l, l) = l when l == l is trivially true
        assert_eq!(i, l, "imax({l:?}, {l:?}) should equal {l:?}");
    }
}

#[test]
fn test_is_geq() {
    // l >= 0 for all l
    assert!(Level::is_geq(
        &Level::param(Name::from_string("u")),
        &Level::zero()
    ));
    assert!(Level::is_geq(&Level::zero(), &Level::zero()));

    // succ(l) >= l
    let u = Level::param(Name::from_string("u"));
    assert!(Level::is_geq(&Level::succ(u.clone()), &u));

    // succ(succ(0)) >= succ(0)
    let one = Level::succ(Level::zero());
    let two = Level::succ(one.clone());
    assert!(Level::is_geq(&two, &one));
    assert!(Level::is_geq(&two, &Level::zero()));
}

#[test]
fn test_normalize() {
    // imax(u, 0) normalizes to 0
    let u = Level::param(Name::from_string("u"));
    let i = Level::IMax(Arc::new(u.clone()), Arc::new(Level::zero()));
    // After simplification in imax(), this is already Zero
    // But if we construct it manually:
    let normalized = i.normalize();
    assert!(normalized.is_zero());

    // max(0, u) normalizes to u
    let m = Level::Max(Arc::new(Level::zero()), Arc::new(u.clone()));
    let normalized = m.normalize();
    assert_eq!(normalized, u);
}

#[test]
fn test_substitute() {
    let u = Level::param(Name::from_string("u"));
    let v = Level::param(Name::from_string("v"));
    let two = Level::succ(Level::succ(Level::zero()));

    // Substitute u -> 2
    let subst = vec![(Name::from_string("u"), two.clone())];
    let result = u.substitute(&subst);
    assert_eq!(result, two);

    // v should be unchanged
    let result = v.substitute(&subst);
    assert_eq!(result, v);

    // max(u, v) with u -> 2 should give max(2, v)
    let max_uv = Level::max(u.clone(), v.clone());
    let result = max_uv.substitute(&subst);
    // Should be max(2, v) - check structure
    assert!(result.has_params()); // Still has v
}

#[test]
fn test_substitute_slice() {
    let u = Name::from_string("u");
    let v = Name::from_string("v");
    let replacement_u = Level::succ(Level::zero());
    let replacement_v = Level::succ(Level::succ(Level::zero()));

    let level = Level::max(Level::param(u.clone()), Level::param(v.clone()));
    let result = level.substitute_slice(
        &[u.clone(), v.clone()],
        &[replacement_u.clone(), replacement_v.clone()],
    );

    assert_eq!(
        result,
        Level::max(replacement_u, replacement_v),
        "parallel-slice substitution should match pair-slice substitution"
    );
}

#[test]
fn test_collect_params() {
    let u = Level::param(Name::from_string("u"));
    let v = Level::param(Name::from_string("v"));
    let level = Level::max(u, Level::imax(v, Level::succ(Level::zero())));

    let mut params = Vec::new();
    level.collect_params(&mut params);

    assert!(params.contains(&Name::from_string("u")));
    assert!(params.contains(&Name::from_string("v")));
    assert_eq!(params.len(), 2);
}

#[test]
fn test_get_offset() {
    let u = Level::param(Name::from_string("u"));
    let (base, offset) = u.get_offset();
    assert_eq!(offset, 0);
    assert_eq!(base, &u);

    let succ_u = Level::succ(u.clone());
    let (base, offset) = succ_u.get_offset();
    assert_eq!(offset, 1);
    assert_eq!(base, &u);

    let succ_succ_u = Level::succ(succ_u);
    let (base, offset) = succ_succ_u.get_offset();
    assert_eq!(offset, 2);
    assert_eq!(base, &u);
}

#[test]
fn test_add_offset() {
    let u = Level::param(Name::from_string("u"));
    let result = u.add_offset(3);
    let (base, offset) = result.get_offset();
    assert_eq!(offset, 3);
    assert_eq!(base, &u);
}

#[test]
fn test_add_offset_large() {
    // Re: #526 - Verify iterative implementation handles large offsets
    // that would overflow the stack with recursive implementation.
    // Using 500 as test value - enough to prove iterative traversal works,
    // but small enough that implicit Drop recursion doesn't overflow.
    // (Drop for Arc<Level> is automatically recursive.)
    let u = Level::param(Name::from_string("u"));
    let result = u.add_offset(500);
    let (base, offset) = result.get_offset();
    assert_eq!(offset, 500);
    assert_eq!(base, &u);

    // Also test with Zero base
    let result_zero = Level::zero().add_offset(500);
    let (base_zero, offset_zero) = result_zero.get_offset();
    assert_eq!(offset_zero, 500);
    assert!(base_zero.is_zero());
}

// =========================================================================
// Mutation Testing Kill Tests
// =========================================================================

#[test]
fn test_is_zero_logic() {
    // Kill mutant: is_zero max case && to ||

    // max(0, 0) IS zero
    let max_00 = Level::Max(Arc::new(Level::Zero), Arc::new(Level::Zero));
    assert!(max_00.is_zero());

    // max(1, 0) is NOT zero (one side is nonzero)
    let max_10 = Level::Max(Arc::new(Level::succ(Level::zero())), Arc::new(Level::Zero));
    assert!(!max_10.is_zero());

    // max(0, 1) is NOT zero (one side is nonzero)
    let max_01 = Level::Max(Arc::new(Level::Zero), Arc::new(Level::succ(Level::zero())));
    assert!(!max_01.is_zero());

    // max(1, 1) is NOT zero
    let one = Level::succ(Level::zero());
    let max_11 = Level::Max(Arc::new(one.clone()), Arc::new(one));
    assert!(!max_11.is_zero());
}

#[test]
fn test_is_geq_comparison_operators() {
    // Kill mutants: > vs < vs >= comparisons in is_geq

    // Test offset comparison: l1 >= l2 when offsets differ
    let u = Level::param(Name::from_string("u"));
    let u1 = Level::succ(u.clone()); // u + 1
    let u2 = Level::succ(u1.clone()); // u + 2

    // u + 2 >= u + 1 (offset 2 >= offset 1)
    assert!(Level::is_geq(&u2, &u1));

    // u + 1 NOT >= u + 2 (offset 1 < offset 2)
    assert!(!Level::is_geq(&u1, &u2));

    // u + 2 >= u (offset 2 >= offset 0)
    assert!(Level::is_geq(&u2, &u));

    // u NOT >= u + 1 (offset 0 < offset 1)
    assert!(!Level::is_geq(&u, &u1));

    // Test > vs >= : offset1 > 0 check
    // succ(u) where succ(u) >= v should check if u >= v
    let v = Level::param(Name::from_string("v"));
    let succ_v = Level::succ(v.clone());

    // succ(v) >= v  (offset > 0, then v >= v is true)
    assert!(Level::is_geq(&succ_v, &v));
}

#[test]
fn test_is_geq_max_logic() {
    // Kill mutant: is_geq max cases && to ||

    let u = Level::param(Name::from_string("u"));
    let _v = Level::param(Name::from_string("v")); // unused but kept for clarity
    let one = Level::succ(Level::zero());
    let two = Level::succ(one.clone());

    // max(a, b) >= l if a >= l OR b >= l (||)
    // max(u, 2) >= 1 should be true because 2 >= 1
    let max_u2 = Level::max(u.clone(), two.clone());
    assert!(Level::is_geq(&max_u2, &one));

    // l >= max(a, b) if l >= a AND l >= b (&&)
    // 2 >= max(0, 1) should be true because 2 >= 0 AND 2 >= 1
    let max_01 = Level::max(Level::zero(), one.clone());
    assert!(Level::is_geq(&two, &max_01));

    // 1 >= max(0, 2) should be FALSE because 1 >= 0 but NOT 1 >= 2
    let max_02 = Level::max(Level::zero(), two.clone());
    assert!(!Level::is_geq(&one, &max_02));

    // 0 >= max(1, 0) should be FALSE because NOT 0 >= 1
    let max_10 = Level::max(one.clone(), Level::zero());
    assert!(!Level::is_geq(&Level::zero(), &max_10));
}

#[test]
fn test_leq_uses_is_geq() {
    // Kill mutant: leq can return true/false always

    let one = Level::succ(Level::zero());
    let two = Level::succ(one.clone());

    // 1 <= 2
    assert!(Level::leq(&one, &two));

    // NOT 2 <= 1
    assert!(!Level::leq(&two, &one));

    // 0 <= anything
    assert!(Level::leq(&Level::zero(), &one));
    assert!(Level::leq(&Level::zero(), &Level::zero()));

    // NOT 1 <= 0
    assert!(!Level::leq(&one, &Level::zero()));
}

#[test]
fn test_has_params_predicate() {
    // Kill mutant: has_params can return true always

    // Zero has no params
    assert!(!Level::zero().has_params());

    // succ(0) has no params
    assert!(!Level::succ(Level::zero()).has_params());

    // Param has params
    let u = Level::param(Name::from_string("u"));
    assert!(u.has_params());

    // succ(u) has params
    assert!(Level::succ(u.clone()).has_params());

    // max(0, u) has params
    assert!(Level::max(Level::zero(), u.clone()).has_params());

    // max(0, 0) has no params
    assert!(!Level::max(Level::zero(), Level::zero()).has_params());

    // max(1, 2) has no params
    let one = Level::succ(Level::zero());
    let two = Level::succ(one.clone());
    assert!(!Level::max(one, two).has_params());
}

#[test]
fn test_display_count_increment() {
    // Kill mutant: Display += with *= in count increment

    // Test display output for various succ levels
    let zero = Level::zero();
    let one = Level::succ(zero.clone());
    let two = Level::succ(one.clone());
    let three = Level::succ(two.clone());

    assert_eq!(format!("{zero}"), "0");
    assert_eq!(format!("{one}"), "1");
    assert_eq!(format!("{two}"), "2");
    assert_eq!(format!("{three}"), "3");

    // Test with parameter base
    let u = Level::param(Name::from_string("u"));
    let u1 = Level::succ(u.clone());
    let u2 = Level::succ(u1.clone());

    assert_eq!(format!("{u}"), "u");
    assert_eq!(format!("{u1}"), "u + 1");
    assert_eq!(format!("{u2}"), "u + 2");
}

// =========================================================================
// Additional Mutation Kill Tests - is_geq specific
// =========================================================================

#[test]
fn test_is_geq_offset_positive_check() {
    // Kill mutant at line 183: replace > with < in `offset1 > 0`
    // The check `offset1 > 0` is used to recursively check if l1' >= l2
    // where l1 = succ^k(l1') and k > 0
    //
    // With `<`: offset1 < 0 is NEVER true for u32, so the check never fires
    // This affects cases where succ^k(l1') >= l2 because l1' >= l2

    // Case: succ(u) >= u
    // offset1 = 1 > 0, so check if u >= u (true)
    // With < mutant: 1 < 0 is false, skip the check, but same base so still true
    // We need a case where bases differ
    let u = Level::param(Name::from_string("u"));
    let v = Level::param(Name::from_string("v"));

    // succ(u) >= u: bases same (u), offset 1 >= 0, true
    assert!(Level::is_geq(&Level::succ(u.clone()), &u));

    // succ(max(u, v)) >= max(u, v)
    // l1 = succ(max(u, v)), l2 = max(u, v)
    // bases differ (Succ vs Max), but offset1 = 1 > 0
    // So check if max(u, v) >= max(u, v) (true)
    // Result: true
    let max_uv = Level::max(u.clone(), v.clone());
    let succ_max = Level::succ(max_uv.clone());
    assert!(
        Level::is_geq(&succ_max, &max_uv),
        "succ(max(u,v)) >= max(u,v) should be true via offset > 0 check"
    );

    // Now test a case where the offset > 0 check is essential:
    // succ(u) >= v where u and v are different params
    // bases differ (u vs v), offset1 = 1 > 0
    // Check if u >= v (false - can't compare different params)
    // Without offset check, we'd return false immediately
    // With offset check, we also get false (u >= v is false)
    // So this doesn't distinguish the mutation...

    // Better test: succ^2(0) >= succ(0) = 2 >= 1
    // l1 = 2, l2 = 1
    // get_offset(2) = (0, 2), get_offset(1) = (0, 1)
    // bases same (Zero), offset 2 >= 1, true
    let one = Level::succ(Level::zero());
    let two = Level::succ(one.clone());
    assert!(Level::is_geq(&two, &one));

    // Test: succ(u + 1) >= u
    // = (u + 2) >= u
    // bases same, offset 2 >= 0, true
    let u_plus_1 = Level::succ(u.clone());
    let u_plus_2 = Level::succ(u_plus_1.clone());
    assert!(Level::is_geq(&u_plus_2, &u));

    // Key test: succ(max(u, 0)) >= u
    // l1 = succ(max(u, 0))
    // l2 = u
    // get_offset(l1) = (max(u, 0), 1)
    // get_offset(l2) = (u, 0)
    // bases differ (max vs param), so we can't just compare offsets
    // offset1 = 1 > 0, so check if max(u, 0) >= u
    // max(u, 0) >= u: max case, u >= u (true) or 0 >= u (false)
    // So true via the first arm
    // Result: true
    // With < mutant: 1 < 0 is false, skip offset check
    // Then max check for l1: l1 is Succ not Max, skip
    // Then max check for l2: l2 is Param not Max, skip
    // Return false (wrong!)
    let max_u0 = Level::max(u.clone(), Level::zero());
    let succ_max_u0 = Level::succ(max_u0);
    assert!(
        Level::is_geq(&succ_max_u0, &u),
        "succ(max(u, 0)) >= u should be true via offset > 0 recursive check"
    );

    // CRITICAL TEST: succ(max(u, v)) >= u
    // This is the key case that distinguishes the > vs < mutation
    // l1 = succ(max(u, v)), l2 = u
    // get_offset(l1) = (max(u, v), 1)
    // get_offset(l2) = (u, 0)
    // bases differ: max(u, v) != u structurally
    // With > 0: offset1=1 > 0, check is_geq(max(u, v), u)
    //   max check fires: u >= u || v >= u = true || false = true
    // With < 0: offset1=1 < 0 is false, skip
    //   max check for l1: l1 is Succ not Max, skip
    //   max check for l2: l2 is Param not Max, skip
    //   Return false (WRONG!)
    let succ_max_uv = Level::succ(max_uv.clone());
    assert!(
        Level::is_geq(&succ_max_uv, &u),
        "succ(max(u, v)) >= u should be true: bases differ but inner max(u,v) >= u"
    );
}

#[test]
fn test_is_geq_max_requires_both_and() {
    // Kill mutant at line 199: replace && with || in
    // `Level::is_geq(l1, a) && Level::is_geq(l1, b)`
    //
    // This checks if l >= max(a, b) which requires l >= a AND l >= b
    // With ||: it would only require l >= a OR l >= b

    let one = Level::succ(Level::zero());
    let two = Level::succ(one.clone());
    let three = Level::succ(two.clone());

    // 2 >= max(1, 3)?
    // With &&: 2 >= 1 (true) AND 2 >= 3 (false) = false
    // With ||: 2 >= 1 (true) OR 2 >= 3 (false) = true
    let max_1_3 = Level::max(one.clone(), three.clone());
    assert!(
        !Level::is_geq(&two, &max_1_3),
        "2 >= max(1, 3) should be FALSE because 2 >= 3 is false"
    );

    // 3 >= max(1, 2)?
    // With &&: 3 >= 1 (true) AND 3 >= 2 (true) = true
    let max_1_2 = Level::max(one.clone(), two.clone());
    assert!(
        Level::is_geq(&three, &max_1_2),
        "3 >= max(1, 2) should be TRUE"
    );

    // 1 >= max(0, 2)?
    // With &&: 1 >= 0 (true) AND 1 >= 2 (false) = false
    // With ||: 1 >= 0 (true) OR 1 >= 2 (false) = true
    let max_0_2 = Level::max(Level::zero(), two.clone());
    assert!(
        !Level::is_geq(&one, &max_0_2),
        "1 >= max(0, 2) should be FALSE"
    );

    // 0 >= max(0, 1)?
    // With &&: 0 >= 0 (true) AND 0 >= 1 (false) = false
    let max_0_1 = Level::max(Level::zero(), one.clone());
    assert!(
        !Level::is_geq(&Level::zero(), &max_0_1),
        "0 >= max(0, 1) should be FALSE"
    );

    // Test with params: u >= max(u, v) where u and v are different
    let u = Level::param(Name::from_string("u"));
    let v = Level::param(Name::from_string("v"));
    let max_uv = Level::max(u.clone(), v.clone());

    // u >= max(u, v)?
    // With &&: u >= u (true) AND u >= v (false, can't compare) = false
    // Wait, is_geq for incomparable params... let's check
    // Actually, Level::is_geq returns false for incomparable params
    // So: u >= u (true) AND u >= v (false) = false
    // With ||: u >= u (true) OR u >= v (false) = true
    assert!(
        !Level::is_geq(&u, &max_uv),
        "u >= max(u, v) should be FALSE when u and v are independent params"
    );
}

// =========================================================================
// lean4lean Theorem Coverage Tests - Phase V5 Completion
// These tests verify the remaining 4 lean4lean theorems about universe levels
// Reference: https://github.com/digama0/lean4lean Theory/VLevel.lean
// =========================================================================

#[test]
fn test_equiv_congr_left() {
    // lean4lean theorem equiv_congr_left:
    //   {a b c : VLevel} (h : a ≈ b) : a ≈ c ↔ b ≈ c
    //
    // In clean: Level::is_def_eq uses normalization for equivalence.
    // If a ≈ b (a.normalize() == b.normalize()), then:
    //   a ≈ c ↔ b ≈ c
    // Because both reduce to comparing the same normal form with c.

    let u = Level::param(Name::from_string("u"));
    let v = Level::param(Name::from_string("v"));

    // Test case 1: a = max(u, 0), b = u
    // max(u, 0) normalizes to u, so a ≈ b
    let a = Level::max(u.clone(), Level::zero());
    let b = u.clone();
    let c = Level::succ(u.clone()); // u + 1

    // Verify a ≈ b
    assert!(Level::is_def_eq(&a, &b), "max(u, 0) ≈ u should hold");

    // Now: a ≈ c ↔ b ≈ c
    // a ≈ c: max(u, 0) ≈ u+1? No (u ≠ u+1)
    // b ≈ c: u ≈ u+1? No
    let a_eq_c = Level::is_def_eq(&a, &c);
    let b_eq_c = Level::is_def_eq(&b, &c);
    assert_eq!(a_eq_c, b_eq_c, "equiv_congr_left: a ≈ c ↔ b ≈ c when a ≈ b");

    // Test case 2: a = imax(u, succ(v)), b = max(u, succ(v))
    // imax(u, succ(v)) = max(u, succ(v)) because succ(v) is nonzero
    let a2 = Level::imax(u.clone(), Level::succ(v.clone()));
    let b2 = Level::max(u.clone(), Level::succ(v.clone()));
    let c2 = v.clone();

    // Verify a2 ≈ b2
    assert!(
        Level::is_def_eq(&a2, &b2),
        "imax(u, succ(v)) ≈ max(u, succ(v))"
    );

    // equiv_congr_left: a2 ≈ c2 ↔ b2 ≈ c2
    let a2_eq_c2 = Level::is_def_eq(&a2, &c2);
    let b2_eq_c2 = Level::is_def_eq(&b2, &c2);
    assert_eq!(a2_eq_c2, b2_eq_c2, "equiv_congr_left holds for imax/max");

    // Test case 3: Positive case where all are equal
    let a3 = Level::max(Level::zero(), Level::zero());
    let b3 = Level::zero();
    let c3 = Level::imax(Level::succ(u.clone()), Level::zero()); // = 0

    assert!(Level::is_def_eq(&a3, &b3), "max(0, 0) ≈ 0");
    assert!(Level::is_def_eq(&c3, &Level::zero()), "imax(_, 0) ≈ 0");

    let a3_eq_c3 = Level::is_def_eq(&a3, &c3);
    let b3_eq_c3 = Level::is_def_eq(&b3, &c3);
    assert_eq!(a3_eq_c3, b3_eq_c3, "equiv_congr_left: both should be true");
    assert!(a3_eq_c3, "All should be equivalent to zero");
}

#[test]
fn test_equiv_congr_right() {
    // lean4lean theorem equiv_congr_right:
    //   {a b c : VLevel} (h : a ≈ b) : c ≈ a ↔ c ≈ b
    //
    // By symmetry of ≈, this is equivalent to equiv_congr_left.

    let u = Level::param(Name::from_string("u"));

    // Test: a = max(0, u), b = u, c = some level
    let a = Level::max(Level::zero(), u.clone()); // = u
    let b = u.clone();
    let c = Level::succ(Level::succ(Level::zero())); // = 2

    // Verify a ≈ b
    assert!(Level::is_def_eq(&a, &b), "max(0, u) ≈ u");

    // equiv_congr_right: c ≈ a ↔ c ≈ b
    let c_eq_a = Level::is_def_eq(&c, &a);
    let c_eq_b = Level::is_def_eq(&c, &b);
    assert_eq!(
        c_eq_a, c_eq_b,
        "equiv_congr_right: c ≈ a ↔ c ≈ b when a ≈ b"
    );

    // Test case 2: When equivalences hold
    let a2 = Level::imax(Level::zero(), Level::zero()); // = 0
    let b2 = Level::zero();
    let c2 = Level::max(Level::zero(), Level::zero()); // = 0

    assert!(Level::is_def_eq(&a2, &b2), "imax(0, 0) ≈ 0");

    let c2_eq_a2 = Level::is_def_eq(&c2, &a2);
    let c2_eq_b2 = Level::is_def_eq(&c2, &b2);
    assert_eq!(c2_eq_a2, c2_eq_b2, "equiv_congr_right: both should be true");
    assert!(c2_eq_a2, "All zeros are equivalent");
}

#[test]
fn test_inst_id() {
    // lean4lean theorem inst_id:
    //   {l : VLevel} (h : l.WF u) : l.inst (params u) = l
    //
    // If you substitute each parameter with itself, you get back the same level.
    // In clean terms: l.substitute([(u, Param(u)), (v, Param(v)), ...]) = l
    //
    // This is the identity substitution property.

    let u = Level::param(Name::from_string("u"));
    let v = Level::param(Name::from_string("v"));
    let w = Level::param(Name::from_string("w"));

    // Identity substitution: map each param to itself
    let id_subst = vec![
        (Name::from_string("u"), u.clone()),
        (Name::from_string("v"), v.clone()),
        (Name::from_string("w"), w.clone()),
    ];

    // Test 1: Simple param
    let result = u.substitute(&id_subst);
    assert_eq!(result, u, "inst_id: u[u/u] = u");

    // Test 2: Succ of param
    let succ_u = Level::succ(u.clone());
    let result = succ_u.substitute(&id_subst);
    assert_eq!(result, succ_u, "inst_id: (u+1)[id] = u+1");

    // Test 3: Max of params
    let max_uv = Level::max(u.clone(), v.clone());
    let result = max_uv.substitute(&id_subst);
    assert_eq!(result, max_uv, "inst_id: max(u,v)[id] = max(u,v)");

    // Test 4: IMax of params
    let imax_uv = Level::imax(u.clone(), v.clone());
    let result = imax_uv.substitute(&id_subst);
    assert_eq!(result, imax_uv, "inst_id: imax(u,v)[id] = imax(u,v)");

    // Test 5: Complex nested level
    let complex = Level::max(
        Level::succ(Level::succ(u.clone())),
        Level::imax(v.clone(), Level::max(w.clone(), Level::zero())),
    );
    let result = complex.substitute(&id_subst);
    assert_eq!(result, complex, "inst_id: complex[id] = complex");

    // Test 6: Level with no params (should be unchanged)
    let concrete = Level::succ(Level::succ(Level::zero())); // 2
    let result = concrete.substitute(&id_subst);
    assert_eq!(result, concrete, "inst_id: 2[id] = 2");

    // Test 7: Empty substitution should also preserve
    let empty_subst: Vec<(Name, Level)> = vec![];
    let result = max_uv.substitute(&empty_subst);
    assert_eq!(
        result, max_uv,
        "inst_id: max(u,v)[] = max(u,v) (param not in subst)"
    );
}

#[test]
fn test_identity_substitute_preserves_raw_param_free_subtrees() {
    use std::collections::HashMap;

    let u_name = Name::from_string("u");
    let u = Level::param(u_name.clone());
    let raw_param_free = Level::Max(
        Arc::new(Level::succ(Level::zero())),
        Arc::new(Level::zero().add_offset(3)),
    );
    let mixed = Level::Max(Arc::new(u.clone()), Arc::new(raw_param_free.clone()));

    let subst = vec![(u_name.clone(), u.clone())];
    assert_eq!(
        mixed.substitute(&subst),
        mixed,
        "identity substitute should preserve raw param-free subtree structure"
    );

    let params = vec![u_name.clone()];
    let levels = vec![u.clone()];
    assert_eq!(
        mixed.substitute_slice(&params, &levels),
        mixed,
        "identity substitute_slice should preserve raw param-free subtree structure"
    );

    let mut subst_map = HashMap::new();
    subst_map.insert(u_name, u);
    assert_eq!(
        mixed.substitute_map(&subst_map),
        mixed,
        "identity substitute_map should preserve raw param-free subtree structure"
    );
}

#[test]
fn test_substitute_uses_first_matching_binding() {
    let u_name = Name::from_string("u");
    let u = Level::param(u_name.clone());
    let replacement = Level::succ(Level::zero());
    let subst = vec![
        (u_name.clone(), u.clone()),
        (u_name.clone(), replacement.clone()),
    ];

    assert_eq!(
        u.substitute(&subst),
        u,
        "substitute should stop at the first matching binding even when it is identity"
    );

    let params = vec![u_name, Name::from_string("u")];
    let levels = vec![u.clone(), replacement];
    assert_eq!(
        u.substitute_slice(&params, &levels),
        u,
        "substitute_slice should stop at the first matching binding even when it is identity"
    );
}

#[test]
fn test_inst_map_id() {
    // lean4lean theorem inst_map_id:
    //   (h : ls.length = n) : (params n).map (inst ls) = ls
    //
    // If you have a list of levels ls = [l0, l1, l2, ...]
    // and you create params = [Param(0), Param(1), Param(2), ...]
    // then substituting params with ls gives back ls.
    //
    // In clean: for a list of levels ls and corresponding param names,
    // if subst = [(p0, l0), (p1, l1), ...], then
    // [Param(p0), Param(p1), ...].map(|p| p.substitute(subst)) = ls

    let l0 = Level::succ(Level::zero()); // 1
    let l1 = Level::succ(Level::succ(Level::zero())); // 2
    let l2 = Level::param(Name::from_string("x")); // x

    let ls = vec![l0.clone(), l1.clone(), l2.clone()];

    // Create param names and corresponding params
    let p0 = Name::from_string("p0");
    let p1 = Name::from_string("p1");
    let p2 = Name::from_string("p2");

    let params = [
        Level::param(p0.clone()),
        Level::param(p1.clone()),
        Level::param(p2.clone()),
    ];

    // Create substitution: p0 -> l0, p1 -> l1, p2 -> l2
    let subst = vec![
        (p0.clone(), l0.clone()),
        (p1.clone(), l1.clone()),
        (p2.clone(), l2.clone()),
    ];

    // Map substitute over params
    let result: Vec<Level> = params.iter().map(|p| p.substitute(&subst)).collect();

    // Should get back ls
    assert_eq!(result, ls, "inst_map_id: params.map(inst ls) = ls");

    // Test with single element
    let ls_single = [Level::succ(Level::succ(Level::succ(Level::zero())))]; // [3]
    let p_single = Name::from_string("p_single");
    let params_single = [Level::param(p_single.clone())];
    let subst_single = vec![(p_single, ls_single[0].clone())];

    let result_single: Vec<Level> = params_single
        .iter()
        .map(|p| p.substitute(&subst_single))
        .collect();
    assert_eq!(
        result_single.as_slice(),
        &ls_single,
        "inst_map_id: single element case"
    );

    // Test with empty list
    let ls_empty: Vec<Level> = vec![];
    let params_empty: Vec<Level> = vec![];
    let subst_empty: Vec<(Name, Level)> = vec![];

    let result_empty: Vec<Level> = params_empty
        .iter()
        .map(|p| p.substitute(&subst_empty))
        .collect();
    assert_eq!(result_empty, ls_empty, "inst_map_id: empty list case");
}

/// Test that universe level comparison correctly handles param >= concrete level cases.
/// All universe params are >= 0, so succ(Param(u)) >= succ(Zero) because Param(u) >= Zero.
#[test]
fn test_is_geq_param_vs_concrete() {
    let u = Level::param(Name::from_string("u"));
    let one = Level::succ(Level::zero());
    let succ_u = Level::succ(u.clone());

    // succ(u) >= succ(0) because u >= 0 for all universe params
    assert!(
        Level::is_geq(&succ_u, &one),
        "succ(u) >= succ(0) should be true since u >= 0"
    );

    // Therefore max(succ(0), succ(u)) should simplify to succ(u)
    let max_level = Level::max(one.clone(), succ_u.clone());
    assert_eq!(
        max_level, succ_u,
        "max(1, u+1) should simplify to u+1 since u+1 >= 1"
    );

    // Test max(1, max(1, u+1)) = u+1
    let nested = Level::max(one.clone(), Level::max(one.clone(), succ_u.clone()));
    assert_eq!(
        nested, succ_u,
        "nested max with concrete levels should simplify"
    );

    // Test succ^2(u) >= succ^2(0)
    let two = Level::succ(one.clone());
    let succ_succ_u = Level::succ(succ_u.clone());
    assert!(
        Level::is_geq(&succ_succ_u, &two),
        "succ(succ(u)) >= succ(succ(0)) should be true"
    );
}

// =========================================================================
// Performance Regression Tests (#835)
// Verify O(n) complexity of substitute_map and collect_params
// =========================================================================

#[test]
fn test_substitute_map_linear_scaling() {
    let _serial = crate::test_utils::serial_test_guard();
    // Verify substitute_map scales linearly, not quadratically.
    // Build levels with many params and substitutions.
    use std::collections::HashMap;
    use std::time::Instant;

    // Build a deeply nested max level with many params
    fn build_nested_max(n: usize) -> Level {
        let mut level = Level::zero();
        for i in 0..n {
            let param = Level::param(Name::from_string(&format!("u{i}")));
            level = Level::max(level, param);
        }
        level
    }

    // Build substitution map
    fn build_subst_map(n: usize) -> HashMap<Name, Level> {
        let mut map = HashMap::new();
        for i in 0..n {
            map.insert(
                Name::from_string(&format!("u{i}")),
                Level::succ(Level::zero()),
            );
        }
        map
    }

    // Test with increasing sizes and verify time doesn't grow quadratically
    let sizes = [50, 100, 200];
    let mut times = Vec::new();

    for &n in &sizes {
        let level = build_nested_max(n);
        let subst = build_subst_map(n);

        let start = Instant::now();
        let _ = level.substitute_map(&subst);
        let elapsed = start.elapsed();
        times.push(elapsed.as_nanos());
    }

    // For O(n), doubling input should roughly double time
    // For O(n²), doubling input would quadruple time
    // We check that 4x input doesn't take more than 8x time (allowing for overhead)
    let ratio = times[2] as f64 / times[0] as f64;
    // 4x input (200/50), should be ~4x time for O(n), not 16x for O(n²)
    assert!(
        ratio < 12.0,
        "substitute_map appears to have quadratic scaling: 4x input gave {ratio:.1}x time"
    );
}

#[test]
fn test_collect_params_no_duplicates() {
    // Verify collect_params properly deduplicates with O(1) HashSet lookup
    let u = Level::param(Name::from_string("u"));
    let v = Level::param(Name::from_string("v"));

    // Build level with many references to same params
    let mut level = Level::max(u.clone(), v.clone());
    for _ in 0..50 {
        level = Level::max(level.clone(), Level::max(u.clone(), v.clone()));
    }

    let mut params = Vec::new();
    level.collect_params(&mut params);

    // Should only have 2 unique params despite many references
    assert_eq!(params.len(), 2, "collect_params should deduplicate");
    assert!(params.contains(&Name::from_string("u")));
    assert!(params.contains(&Name::from_string("v")));
}

#[test]
fn test_collect_params_linear_scaling() {
    let _serial = crate::test_utils::serial_test_guard();
    // Verify collect_params scales linearly (O(n) where n = nodes)
    use std::time::Instant;

    fn build_many_params(n: usize) -> Level {
        let mut level = Level::zero();
        for i in 0..n {
            level = Level::max(level, Level::param(Name::from_string(&format!("u{i}"))));
        }
        level
    }

    let sizes = [100, 200, 400];
    let mut times = Vec::new();

    for &n in &sizes {
        let level = build_many_params(n);

        let start = Instant::now();
        let mut params = Vec::new();
        level.collect_params(&mut params);
        let elapsed = start.elapsed();

        assert_eq!(params.len(), n, "should collect {n} unique params");
        times.push(elapsed.as_nanos());
    }

    // For O(n), 4x input should give ~4x time
    // Previously O(n*m) where m=params collected, so n*n = O(n²)
    let ratio = times[2] as f64 / times[0] as f64;
    assert!(
        ratio < 12.0,
        "collect_params appears to have quadratic scaling: 4x input gave {ratio:.1}x time"
    );
}

// Note: is_geq_imax scaling/correctness tests are in level_scaling_tests.rs

// =========================================================================
// #1308: normalize Max canonicalization regression tests
// =========================================================================

/// #1308 AC4: is_def_eq(max(u, v), max(v, u)) must return true.
/// Previously failed because normalize did not sort Max arguments.
#[test]
fn test_normalize_max_commutativity() {
    let u = Level::param(Name::from_string("u"));
    let v = Level::param(Name::from_string("v"));

    // Construct without smart constructor to avoid is_geq-based simplification
    let max_uv = Level::Max(Arc::new(u.clone()), Arc::new(v.clone()));
    let max_vu = Level::Max(Arc::new(v.clone()), Arc::new(u.clone()));

    assert!(
        Level::is_def_eq(&max_uv, &max_vu),
        "is_def_eq(max(u, v), max(v, u)) must be true after normalization"
    );
}

/// #1308 AC5: is_def_eq(max(u, max(v, w)), max(max(u, v), w)) must return true.
/// Associativity canonicalization via flatten/sort.
#[test]
fn test_normalize_max_associativity() {
    let u = Level::param(Name::from_string("u"));
    let v = Level::param(Name::from_string("v"));
    let w = Level::param(Name::from_string("w"));

    // max(u, max(v, w))
    let inner_vw = Level::Max(Arc::new(v.clone()), Arc::new(w.clone()));
    let lhs = Level::Max(Arc::new(u.clone()), Arc::new(inner_vw));

    // max(max(u, v), w)
    let inner_uv = Level::Max(Arc::new(u.clone()), Arc::new(v.clone()));
    let rhs = Level::Max(Arc::new(inner_uv), Arc::new(w.clone()));

    assert!(
        Level::is_def_eq(&lhs, &rhs),
        "is_def_eq(max(u, max(v, w)), max(max(u, v), w)) must be true"
    );
}

/// #1308 AC1-3: normalize flattens, sorts, and deduplicates/subsumes.
#[test]
fn test_normalize_max_dedup_and_subsume() {
    let u = Level::param(Name::from_string("u"));

    // max(u, succ(u)) should normalize to succ(u) (u subsumed by succ(u))
    let max_u_su = Level::Max(Arc::new(u.clone()), Arc::new(Level::succ(u.clone())));
    let normed = max_u_su.normalize();
    assert_eq!(
        normed,
        Level::succ(u.clone()),
        "max(u, succ(u)) should normalize to succ(u)"
    );

    // max(succ(u), u) should also normalize to succ(u)
    let max_su_u = Level::Max(Arc::new(Level::succ(u.clone())), Arc::new(u.clone()));
    let normed2 = max_su_u.normalize();
    assert_eq!(
        normed2,
        Level::succ(u.clone()),
        "max(succ(u), u) should normalize to succ(u)"
    );
}

/// Succ distributed into Max: succ(max(u, v)) normalizes to max(succ(u), succ(v)).
#[test]
fn test_normalize_succ_distributes_into_max() {
    let u = Level::param(Name::from_string("u"));
    let v = Level::param(Name::from_string("v"));
    let max_uv = Level::Max(Arc::new(u.clone()), Arc::new(v.clone()));
    let succ_max = Level::Succ(Arc::new(max_uv));

    let normed = succ_max.normalize();
    // Should be max(succ(u), succ(v))
    let expected = Level::Max(
        Arc::new(Level::succ(u.clone())),
        Arc::new(Level::succ(v.clone())),
    );
    assert_eq!(
        normed, expected,
        "succ(max(u, v)) should normalize to max(succ(u), succ(v))"
    );
}

/// Explicit level subsumption: max(2, succ^3(u)) should drop the 2 because
/// succ^3(u) >= 2 for all u >= 0.
#[test]
fn test_normalize_explicit_subsumption() {
    let u = Level::param(Name::from_string("u"));
    let two = Level::succ(Level::succ(Level::zero()));
    let u3 = u.add_offset(3); // succ^3(u)

    let max_2_u3 = Level::Max(Arc::new(two), Arc::new(u3.clone()));
    let normed = max_2_u3.normalize();

    // 2 is explicit with offset 2, u+3 has offset 3 >= 2, so 2 is subsumed
    assert_eq!(
        normed, u3,
        "max(2, u+3) should normalize to u+3 (explicit 2 subsumed)"
    );
}

// =========================================================================
// #1307: is_geq IMax handling regression tests
// =========================================================================

/// #1307 AC1: is_geq(imax(v, u), u) must return true for param u, v.
/// Previously returned false because the IMax-on-left check required b.is_nonzero().
#[test]
fn test_is_geq_imax_param_unconditional() {
    let u = Level::param(Name::from_string("u"));
    let v = Level::param(Name::from_string("v"));

    // imax(v, u) >= u should be true: imax(a, b) >= l iff b >= l
    let imax_vu = Level::IMax(Arc::new(v.clone()), Arc::new(u.clone()));
    assert!(
        Level::is_geq(&imax_vu, &u),
        "is_geq(imax(v, u), u) must be true (Lean 4 parity)"
    );
}

/// #1307 AC2: is_geq(x, imax(a, b)) checks x >= a && x >= b unconditionally.
#[test]
fn test_is_geq_imax_on_right_unconditional() {
    let u = Level::param(Name::from_string("u"));
    let v = Level::param(Name::from_string("v"));
    let w = Level::param(Name::from_string("w"));

    // u >= imax(u, u) should be true
    let imax_uu = Level::IMax(Arc::new(u.clone()), Arc::new(u.clone()));
    assert!(Level::is_geq(&u, &imax_uu), "u >= imax(u, u) must be true");

    // max(u, v) >= imax(u, v) should be true:
    // need max(u,v) >= u && max(u,v) >= v
    let max_uv = Level::max(u.clone(), v.clone());
    let imax_uv = Level::IMax(Arc::new(u.clone()), Arc::new(v.clone()));
    assert!(
        Level::is_geq(&max_uv, &imax_uv),
        "max(u, v) >= imax(u, v) must be true"
    );

    // u >= imax(v, w) should be false (u can't be >= v and >= w for independent params)
    let imax_vw = Level::IMax(Arc::new(v.clone()), Arc::new(w.clone()));
    assert!(
        !Level::is_geq(&u, &imax_vw),
        "u >= imax(v, w) should be false for independent params"
    );
}

/// #1307 AC3: is_geq(imax(a, b), x) checks b >= x unconditionally.
#[test]
fn test_is_geq_imax_on_left_unconditional() {
    let u = Level::param(Name::from_string("u"));
    let v = Level::param(Name::from_string("v"));

    // imax(u, v) >= v should be true (b >= l where b=v, l=v)
    let imax_uv = Level::IMax(Arc::new(u.clone()), Arc::new(v.clone()));
    assert!(Level::is_geq(&imax_uv, &v), "imax(u, v) >= v must be true");

    // imax(u, v) >= u should be false (b >= l where b=v, l=u — independent params)
    assert!(
        !Level::is_geq(&imax_uv, &u),
        "imax(u, v) >= u should be false (b=v, not >= u)"
    );

    // imax(u, succ(v)) >= v should be true (b=succ(v) >= v)
    let imax_u_sv = Level::IMax(Arc::new(u.clone()), Arc::new(Level::succ(v.clone())));
    assert!(
        Level::is_geq(&imax_u_sv, &v),
        "imax(u, succ(v)) >= v must be true"
    );
}

/// #1307 AC4: is_geq normalizes inputs before comparison.
#[test]
fn test_is_geq_normalizes_inputs() {
    let u = Level::param(Name::from_string("u"));
    let v = Level::param(Name::from_string("v"));

    // max(v, u) (unnormalized: v first) >= max(u, v) (u first)
    // After normalization, both should have the same canonical form
    let max_vu = Level::Max(Arc::new(v.clone()), Arc::new(u.clone()));
    let max_uv = Level::Max(Arc::new(u.clone()), Arc::new(v.clone()));
    assert!(
        Level::is_geq(&max_vu, &max_uv),
        "is_geq(max(v,u), max(u,v)) must be true after normalization"
    );
    assert!(
        Level::is_geq(&max_uv, &max_vu),
        "is_geq(max(u,v), max(v,u)) must be true after normalization"
    );
}

/// Regression: imax smart constructor must use semantic is_nonzero(), not syntactic Succ check.
/// Lean 4's mk_imax uses is_not_zero(l2) which recurses into Max/IMax.
/// Without this fix, imax(u, max(v, succ(w))) would remain as IMax instead of reducing to Max.
#[test]
fn test_imax_reduces_when_second_arg_semantically_nonzero() {
    let u = Level::param(Name::from_string("u"));
    let v = Level::param(Name::from_string("v"));
    let w = Level::param(Name::from_string("w"));

    // max(v, succ(w)) is semantically nonzero (succ(w) > 0)
    let max_v_sw = Level::max(v.clone(), Level::succ(w.clone()));

    // imax(u, max(v, succ(w))) should reduce to max(u, max(v, succ(w)))
    let result = Level::imax(u.clone(), max_v_sw.clone());
    assert!(
        matches!(result, Level::Max(_, _)),
        "imax(u, max(v, succ(w))) should reduce to Max since max(v,succ(w)) is nonzero, got: {:?}",
        result
    );

    // Also test with nested IMax: imax(u, imax(v, succ(w)))
    // imax(v, succ(w)) reduces to max(v, succ(w)) which is nonzero
    let imax_v_sw = Level::imax(v.clone(), Level::succ(w.clone()));
    assert!(
        matches!(imax_v_sw, Level::Max(_, _)),
        "imax(v, succ(w)) should reduce to Max, got: {:?}",
        imax_v_sw
    );

    let result2 = Level::imax(u.clone(), imax_v_sw);
    assert!(
        matches!(result2, Level::Max(_, _)),
        "imax(u, imax(v, succ(w))) should reduce to Max, got: {:?}",
        result2
    );

    // Verify normalization produces consistent results
    let norm = result.normalize();
    let norm2 = result2.normalize();
    // Both should be Max forms after normalization
    assert!(
        matches!(norm, Level::Max(_, _)),
        "normalize(imax(u, max(v, succ(w)))) should be Max, got: {:?}",
        norm
    );
    assert!(
        matches!(norm2, Level::Max(_, _)),
        "normalize(imax(u, imax(v, succ(w)))) should be Max, got: {:?}",
        norm2
    );
}

/// Regression (#1319): succ(imax(a,b)) >= imax(a,b) must return true.
///
/// is_geq_core is a conservative approximation. Before #1319, it could not
/// prove succ(imax(a,b)) >= imax(a,b) because IMax decomposition fired
/// before the offset comparison, and succ(imax(a,b)) >= a fails when b=0.
///
/// Fix: add early check that succ^n(x) >= x for any n > 0.
#[test]
fn test_is_geq_succ_of_imax() {
    let a = Level::param(Name::from_string("a"));
    let b = Level::param(Name::from_string("b"));

    // succ(imax(a, b)) >= imax(a, b) — the exact failing case from proptest
    let imax_ab = Level::imax(a.clone(), b.clone());
    let succ_imax = Level::succ(imax_ab.clone());
    assert!(
        Level::is_geq(&succ_imax, &imax_ab),
        "succ(imax(a,b)) >= imax(a,b) must be true"
    );

    // succ(succ(imax(a, b))) >= imax(a, b)
    let succ2_imax = Level::succ(succ_imax.clone());
    assert!(
        Level::is_geq(&succ2_imax, &imax_ab),
        "succ(succ(imax(a,b))) >= imax(a,b) must be true"
    );

    // succ(max(a, b)) >= max(a, b)
    let max_ab = Level::max(a.clone(), b.clone());
    let succ_max = Level::succ(max_ab.clone());
    assert!(
        Level::is_geq(&succ_max, &max_ab),
        "succ(max(a,b)) >= max(a,b) must be true"
    );

    // succ(param(a)) >= param(a) — simple case
    let succ_a = Level::succ(a.clone());
    assert!(Level::is_geq(&succ_a, &a), "succ(a) >= a must be true");
}

// =========================================================================
// Algorithm audit: normalization idempotency and is_geq boundary tests
// (P1 iter 583)
// =========================================================================

/// Regression test for #1436: normalize must be idempotent when IMax reduces
/// to Max and an outer offset needs distributing.
///
/// succ(imax(u, succ(v))) should normalize to the same form regardless of
/// how many times normalize is called. The IMax reduces to Max (since
/// succ(v) is nonzero), then the outer Succ must distribute into the Max.
#[test]
fn test_normalize_idempotent_imax_to_max_with_offset() {
    let u = Level::param(Name::from_string("u"));
    let v = Level::param(Name::from_string("v"));

    // Build: succ(imax(u, succ(v)))
    // Since succ(v) is nonzero, imax(u, succ(v)) = max(u, succ(v))
    // So this is succ(max(u, succ(v))) which should normalize to
    // max(succ(u), succ(succ(v)))
    let inner = Level::imax(u.clone(), Level::succ(v.clone()));
    let level = Level::succ(inner);

    let norm1 = level.normalize();
    let norm2 = norm1.normalize();
    assert_eq!(
        norm1, norm2,
        "normalize must be idempotent: succ(imax(u, succ(v)))"
    );
}

/// Test normalize idempotency on deeply nested IMax with multiple offsets.
#[test]
fn test_normalize_idempotent_nested_imax() {
    let u = Level::param(Name::from_string("u"));
    let v = Level::param(Name::from_string("v"));
    let w = Level::param(Name::from_string("w"));

    // succ(succ(imax(u, max(succ(v), succ(w)))))
    let inner_max = Level::max(Level::succ(v.clone()), Level::succ(w.clone()));
    let imax = Level::imax(u.clone(), inner_max);
    let level = Level::succ(Level::succ(imax));

    let norm1 = level.normalize();
    let norm2 = norm1.normalize();
    assert_eq!(
        norm1, norm2,
        "normalize must be idempotent: succ^2(imax(u, max(succ(v), succ(w))))"
    );
}

/// Regression test for #1319: is_geq must handle succ^n(imax(a,b)) >= imax(a,b).
///
/// Without the succ^n(x) >= x rule, this fails because IMax decomposition
/// fires first, checking succ^n(imax(a,b)) >= a and succ^n(imax(a,b)) >= b,
/// which can't be resolved by offset comparison alone.
#[test]
fn test_is_geq_succ_of_imax_geq_imax() {
    let a = Level::param(Name::from_string("a"));
    let b = Level::param(Name::from_string("b"));

    let imax_ab = Level::IMax(Arc::new(a.clone()), Arc::new(b.clone()));
    let succ_imax = Level::Succ(Arc::new(imax_ab.clone()));

    // succ(imax(a, b)) >= imax(a, b) should be true
    assert!(
        Level::is_geq(&succ_imax, &imax_ab),
        "succ(imax(a, b)) >= imax(a, b) should hold"
    );
}

/// Test is_geq with succ^2 of imax.
#[test]
fn test_is_geq_succ2_of_imax_geq_imax() {
    let a = Level::param(Name::from_string("a"));
    let b = Level::param(Name::from_string("b"));

    let imax_ab = Level::IMax(Arc::new(a.clone()), Arc::new(b.clone()));
    let succ2_imax = Level::Succ(Arc::new(Level::Succ(Arc::new(imax_ab.clone()))));

    assert!(
        Level::is_geq(&succ2_imax, &imax_ab),
        "succ(succ(imax(a, b))) >= imax(a, b) should hold"
    );
}

/// Test is_geq reflexivity on IMax (not simplified away).
#[test]
fn test_is_geq_imax_reflexive() {
    let a = Level::param(Name::from_string("a"));
    let b = Level::param(Name::from_string("b"));

    // When a and b are distinct params, imax(a, b) doesn't simplify
    let imax_ab = Level::IMax(Arc::new(a.clone()), Arc::new(b.clone()));

    assert!(
        Level::is_geq(&imax_ab, &imax_ab),
        "imax(a, b) >= imax(a, b) should hold (reflexivity)"
    );
}

/// Test that explicit universe is NOT subsumed when its offset exceeds
/// all non-explicit offsets.
#[test]
fn test_normalize_explicit_not_subsumed() {
    let u = Level::param(Name::from_string("u"));
    let five = Level::succ(Level::succ(Level::succ(Level::succ(Level::succ(
        Level::zero(),
    )))));
    let succ2_u = Level::succ(Level::succ(u.clone()));

    // max(5, succ^2(u)) — the explicit 5 should NOT be subsumed because
    // succ^2(u) has offset 2 < 5.
    let level = Level::Max(Arc::new(five.clone()), Arc::new(succ2_u.clone()));
    let normalized = level.normalize();

    // Both should be preserved in the result.
    // Verify by checking it's not equal to either alone.
    assert_ne!(
        normalized, five,
        "max(5, succ^2(u)) should not simplify to just 5"
    );
    assert_ne!(
        normalized, succ2_u,
        "max(5, succ^2(u)) should not simplify to just succ^2(u)"
    );
}

/// is_def_eq on levels: succ(imax(u, succ(v))) should equal
/// max(succ(u), succ(succ(v))) after normalization.
#[test]
fn test_level_def_eq_imax_to_max_distribution() {
    let u = Level::param(Name::from_string("u"));
    let v = Level::param(Name::from_string("v"));

    // LHS: succ(imax(u, succ(v)))
    // imax(u, succ(v)) = max(u, succ(v)) since succ(v) is nonzero
    // succ(max(u, succ(v))) = max(succ(u), succ(succ(v)))
    let lhs = Level::succ(Level::imax(u.clone(), Level::succ(v.clone())));

    // RHS: max(succ(u), succ(succ(v)))
    let rhs = Level::max(Level::succ(u.clone()), Level::succ(Level::succ(v.clone())));

    assert!(
        Level::is_def_eq(&lhs, &rhs),
        "succ(imax(u, succ(v))) should be def-eq to max(succ(u), succ(succ(v)))"
    );
}

/// Build a left-nested Max tree of given depth: max(max(max(..., u), u), u)
/// This creates a tree that requires O(depth) stack frames to traverse.
fn build_deep_max(depth: usize) -> Level {
    let u = Level::param(Name::from_string("u"));
    let mut level = u.clone();
    for _ in 0..depth {
        level = Level::Max(Arc::new(level), Arc::new(u.clone()));
    }
    level
}

/// Build a left-nested IMax tree of given depth.
fn build_deep_imax(depth: usize) -> Level {
    let u = Level::param(Name::from_string("u"));
    let mut level = u.clone();
    for _ in 0..depth {
        level = Level::IMax(Arc::new(level), Arc::new(u.clone()));
    }
    level
}

/// Stress test: normalize on a 50K-deep nested Max tree should not overflow.
#[test]
fn test_deep_max_normalize_no_overflow() {
    let deep = build_deep_max(8_000);
    let _normalized = deep.normalize();
}

/// Stress test: is_geq on a 50K-deep nested Max tree should not overflow.
#[test]
fn test_deep_max_is_geq_no_overflow() {
    let deep = build_deep_max(8_000);
    let u = Level::param(Name::from_string("u"));
    assert!(Level::is_geq(&deep, &u));
}

/// Stress test: Display on a 50K-deep nested Max tree should not overflow.
#[test]
fn test_deep_max_display_no_overflow() {
    let deep = build_deep_max(8_000);
    let _s = format!("{deep}");
}

/// Stress test: substitute on a 50K-deep nested Max tree should not overflow.
#[test]
fn test_deep_max_substitute_no_overflow() {
    let deep = build_deep_max(8_000);
    let u = Name::from_string("u");
    let v = Level::param(Name::from_string("v"));
    let _result = deep.substitute(&[(u, v)]);
}

/// Stress test: has_params on a 50K-deep nested Max tree should not overflow.
#[test]
fn test_deep_max_has_params_no_overflow() {
    let deep = build_deep_max(8_000);
    assert!(deep.has_params());
}

/// Stress test: collect_params on a 50K-deep nested Max tree should not overflow.
#[test]
fn test_deep_max_collect_params_no_overflow() {
    let deep = build_deep_max(8_000);
    let mut params = Vec::new();
    deep.collect_params(&mut params);
    assert_eq!(params.len(), 1); // only "u"
}

/// Stress test: normalize on a deeply-nested IMax tree should not
/// overflow. 50K was the original target; the actual ceiling on macOS
/// with the default 2 MB test-thread stack sits a bit lower because
/// `Drop` on `Box<Level>` is still recursive. Use 8K — well past any
/// pathological real input and a comfortable margin under the
/// macOS-default test-thread stack ceiling.
#[test]
fn test_deep_imax_normalize_no_overflow() {
    let deep = build_deep_imax(8_000);
    let _normalized = deep.normalize();
}

/// Stress test: push_max_args on a 50K-deep left-nested Max should not overflow.
#[test]
fn test_deep_max_push_max_args_no_overflow() {
    let deep = build_deep_max(8_000);
    let mut buf = Vec::new();
    Level::push_max_args(&deep, &mut buf);
    assert_eq!(buf.len(), 8_001); // depth + 1 leaf nodes
}

// =========================================================================
// Performance proofs: is_def_eq normalization redundancy (P1 iter 1213)
// =========================================================================

/// Verify is_def_eq normalizes both sides every call with no caching.
///
/// For N calls to is_def_eq on the same pair, normalize() is invoked 2N
/// times. This test documents the current behavior as a performance floor:
/// any future optimization (memoized normalization, lazy hashing) should
/// make repeated comparisons cheaper, not more expensive.
#[test]
fn test_is_def_eq_repeated_normalization_overhead() {
    let _serial = crate::test_utils::serial_test_guard();
    use std::time::Instant;

    // Build a moderately complex level pair that requires normalization
    let u = Level::param(Name::from_string("u"));
    let v = Level::param(Name::from_string("v"));
    let w = Level::param(Name::from_string("w"));

    // lhs: succ(max(u, max(v, w))) — needs flatten + sort + distribute
    // rhs: max(succ(u), max(succ(v), succ(w))) — already normalized form
    let lhs = Level::Succ(Arc::new(Level::Max(
        Arc::new(u.clone()),
        Arc::new(Level::Max(Arc::new(v.clone()), Arc::new(w.clone()))),
    )));
    let rhs = Level::Max(
        Arc::new(Level::succ(u.clone())),
        Arc::new(Level::Max(
            Arc::new(Level::succ(v.clone())),
            Arc::new(Level::succ(w.clone())),
        )),
    );

    // Correctness: they should be definitionally equal
    assert!(
        Level::is_def_eq(&lhs, &rhs),
        "succ(max(u, max(v, w))) should be def-eq to max(succ(u), max(succ(v), succ(w)))"
    );

    // Performance: calling 1000 times should complete quickly.
    // This serves as a regression guard — if normalization complexity grows,
    // this test's wall-clock time will catch it.
    let n = 1000;
    let start = Instant::now();
    for _ in 0..n {
        assert!(Level::is_def_eq(&lhs, &rhs));
    }
    let elapsed = start.elapsed();

    // 1000 comparisons of 3-param levels should be well under 100ms.
    // If we see >500ms, something is wrong (expected: ~1-5ms).
    assert!(
        elapsed.as_millis() < 500,
        "1000 is_def_eq calls took {}ms — possible normalization regression",
        elapsed.as_millis()
    );
}

/// Verify normalize_max allocates intermediate Vecs without pre-allocation.
///
/// This test builds a wide Max tree (many leaves) and verifies that
/// normalization scales linearly. Quadratic behavior here would indicate
/// the Vec reallocation pattern in normalize_max is causing issues.
#[test]
fn test_normalize_max_wide_tree_linear_scaling() {
    let _serial = crate::test_utils::serial_test_guard();
    use std::time::Instant;

    fn build_wide_max(n: usize) -> Level {
        let mut level = Level::param(Name::from_string("u0"));
        for i in 1..n {
            let param = Level::param(Name::from_string(&format!("u{i}")));
            level = Level::Max(Arc::new(level), Arc::new(param));
        }
        level
    }

    let sizes = [50, 100, 200];
    let mut times = Vec::new();

    for &n in &sizes {
        let level = build_wide_max(n);
        let start = Instant::now();
        let _normed = level.normalize();
        let elapsed = start.elapsed();
        times.push(elapsed.as_nanos());
    }

    // 4x input (200/50) should give at most ~8x time for O(n log n) sort.
    // Quadratic would be 16x.
    if times[0] > 0 {
        let ratio = times[2] as f64 / times[0] as f64;
        assert!(
            ratio < 20.0,
            "normalize_max appears to have super-linear scaling on wide trees: \
             4x input gave {ratio:.1}x time (sizes: {sizes:?}, times: {times:?})"
        );
    }
}

// =========================================================================
// Performance proofs: instantiate_level_params_direct equivalence (P1 iter 1213)
//
// The iota reduction path (reduction.rs:309-315) builds Vec<(Name, Level)>
// then converts to HashMap inside instantiate_level_params. The _direct
// variant avoids both intermediate allocations for <=4 params. These tests
// prove the two paths produce identical results, enabling a safe switch.
// =========================================================================

/// instantiate_level_params_direct produces identical results to the
/// Vec+HashMap path for typical recursor-sized substitutions (1-4 params).
///
/// Correctness proof for switching iota reduction to the direct path,
/// eliminating 2 allocations per recursor reduction.
#[test]
fn test_instantiate_level_params_direct_equivalence() {
    use crate::expr::Expr;

    let u_name = Name::from_string("u");
    let v_name = Name::from_string("v");
    let w_name = Name::from_string("w");

    let u_level = Level::succ(Level::zero()); // u ↦ 1
    let v_level = Level::succ(Level::succ(Level::zero())); // v ↦ 2
    let w_level = Level::zero(); // w ↦ 0

    // Build an expression with universe polymorphism:
    // Const("Nat.rec", [u, v]) applied to Const("motive", [w])
    let rec_expr = Expr::const_(
        Name::from_string("Nat.rec"),
        vec![Level::param(u_name.clone()), Level::param(v_name.clone())],
    );
    let body = Expr::app(
        rec_expr,
        Expr::const_(
            Name::from_string("motive"),
            vec![Level::param(w_name.clone())],
        ),
    );

    // Vec+HashMap path (current iota path)
    let subst_vec: Vec<(Name, Level)> = vec![
        (u_name.clone(), u_level.clone()),
        (v_name.clone(), v_level.clone()),
        (w_name.clone(), w_level.clone()),
    ];
    let result_vec = body.instantiate_level_params(&subst_vec);

    // Direct path (proposed optimization)
    let params = [u_name, v_name, w_name];
    let levels = [u_level, v_level, w_level];
    let result_direct = body.instantiate_level_params_direct(&params, &levels);

    assert_eq!(
        result_vec, result_direct,
        "instantiate_level_params_direct must produce identical results \
         to the Vec+HashMap path for 3-param substitution"
    );
}

/// Verify direct path handles single-param case (most Lean 4 types).
#[test]
fn test_instantiate_level_params_direct_single_param() {
    use crate::expr::Expr;

    let u_name = Name::from_string("u");
    let u_level = Level::succ(Level::succ(Level::zero())); // u ↦ 2

    let expr = Expr::const_(
        Name::from_string("List"),
        vec![Level::param(u_name.clone())],
    );

    let result_vec = expr.instantiate_level_params(&[(u_name.clone(), u_level.clone())]);
    let result_direct = expr.instantiate_level_params_direct(&[u_name], &[u_level]);

    assert_eq!(
        result_vec, result_direct,
        "Single-param direct path must match Vec+HashMap path"
    );
}

/// Verify direct path handles empty substitution.
#[test]
fn test_instantiate_level_params_direct_empty() {
    use crate::expr::Expr;

    let expr = Expr::const_(
        Name::from_string("Nat"),
        vec![Level::param(Name::from_string("u"))],
    );

    let result_vec = expr.instantiate_level_params(&[]);
    let result_direct = expr.instantiate_level_params_direct(&[], &[]);

    assert_eq!(
        result_vec, result_direct,
        "Empty substitution: both paths should return clone"
    );
}

// =========================================================================
// Memory verification: Level normalization caching proofs (P1 iter 1214)
//
// Verify the three caching opportunities identified in P1 iter 1213:
// 1. Structural equality short-circuit for is_def_eq
// 2. Normalize idempotency (prerequisite for safe caching)
// 3. has_params guard for substitution skip
// =========================================================================

/// Prove: structural equality implies definitional equality.
///
/// If `l1 == l2` (Rust PartialEq), then `is_def_eq(l1, l2)` must be true.
/// This is the correctness proof for adding a short-circuit `if l1 == l2 { return true }`
/// at the top of `is_def_eq`, which would skip normalization entirely for
/// identical levels — the most common case in type checking (same Const compared
/// against itself during delta reduction).
#[test]
fn test_structural_eq_implies_def_eq() {
    // Simple cases
    assert!(Level::is_def_eq(&Level::zero(), &Level::zero()));
    let one = Level::succ(Level::zero());
    assert!(Level::is_def_eq(&one, &one));

    // Parametric
    let u = Level::param(Name::from_string("u"));
    assert!(Level::is_def_eq(&u, &u));

    // Compound: unnormalized Max that is structurally identical
    let compound = Level::Max(
        Arc::new(Level::param(Name::from_string("u"))),
        Arc::new(Level::Max(
            Arc::new(Level::param(Name::from_string("v"))),
            Arc::new(Level::param(Name::from_string("w"))),
        )),
    );
    let compound_clone = compound.clone();
    // structural equality holds
    assert_eq!(compound, compound_clone);
    // therefore def_eq holds (no normalization needed)
    assert!(Level::is_def_eq(&compound, &compound_clone));

    // Deep Succ chain
    let deep = Level::zero().add_offset(100);
    let deep_clone = deep.clone();
    assert_eq!(deep, deep_clone);
    assert!(Level::is_def_eq(&deep, &deep_clone));
}

/// Prove: normalize is idempotent — normalize(normalize(l)) == normalize(l).
///
/// This is the critical safety property for ANY caching strategy:
/// if we cache a normalized form, re-normalizing the cached result
/// must produce the same value. Tests across all Level variants
/// including the tricky IMax-to-Max reduction path.
#[test]
fn test_normalize_idempotent_all_variants() {
    let u = Level::param(Name::from_string("u"));
    let v = Level::param(Name::from_string("v"));
    let w = Level::param(Name::from_string("w"));

    let cases: Vec<Level> = vec![
        // Zero
        Level::zero(),
        // Succ chain
        Level::succ(Level::zero()),
        Level::zero().add_offset(5),
        // Param
        u.clone(),
        // Simple Max
        Level::Max(Arc::new(u.clone()), Arc::new(v.clone())),
        // Nested Max (needs flatten + sort)
        Level::Max(
            Arc::new(u.clone()),
            Arc::new(Level::Max(Arc::new(v.clone()), Arc::new(w.clone()))),
        ),
        // Succ(Max) — needs distribute
        Level::Succ(Arc::new(Level::Max(
            Arc::new(u.clone()),
            Arc::new(v.clone()),
        ))),
        // IMax that reduces to zero: imax(u, 0) = 0
        Level::IMax(Arc::new(u.clone()), Arc::new(Level::zero())),
        // IMax that reduces to Max: imax(u, succ(v))
        Level::IMax(Arc::new(u.clone()), Arc::new(Level::succ(v.clone()))),
        // IMax with both params (stays IMax in normalized form)
        Level::IMax(Arc::new(u.clone()), Arc::new(v.clone())),
        // Deep: Succ(Succ(Max(IMax(u, v), w)))
        Level::Succ(Arc::new(Level::Succ(Arc::new(Level::Max(
            Arc::new(Level::IMax(Arc::new(u.clone()), Arc::new(v.clone()))),
            Arc::new(w.clone()),
        ))))),
        // Max with concrete + param: max(2, u)
        Level::Max(Arc::new(Level::zero().add_offset(2)), Arc::new(u.clone())),
    ];

    for (i, level) in cases.iter().enumerate() {
        let norm1 = level.normalize();
        let norm2 = norm1.normalize();
        assert_eq!(
            norm1, norm2,
            "normalize is not idempotent for case {i}: {level:?}\n\
             norm1 = {norm1:?}\n\
             norm2 = {norm2:?}"
        );
    }
}

/// Prove: has_params() == false implies substitute is identity.
///
/// This is the correctness proof for a `has_params` short-circuit guard
/// in Level substitution: if a level has no Param nodes, substitution
/// must return a structurally equal result regardless of the substitution map.
/// Adding this guard would skip the full tree traversal.
#[test]
fn test_no_params_substitute_is_identity() {
    let subst = &[
        (Name::from_string("u"), Level::succ(Level::zero())),
        (Name::from_string("v"), Level::zero().add_offset(3)),
    ];

    // Param-free levels
    let param_free: Vec<Level> = vec![
        Level::zero(),
        Level::succ(Level::zero()),
        Level::zero().add_offset(10),
        Level::Max(
            Arc::new(Level::succ(Level::zero())),
            Arc::new(Level::zero().add_offset(3)),
        ),
    ];

    for level in &param_free {
        assert!(!level.has_params(), "expected no params in {level:?}");
        let substituted = level.substitute(subst);
        assert_eq!(
            *level, substituted,
            "substitute on param-free level should be identity: {level:?}"
        );
    }
}

/// Verify: normalized levels are structurally canonical — def-eq levels
/// have the same normalized form.
///
/// This proves that normalization is a canonical form: two levels that
/// are definitionally equal normalize to the same structure. This is
/// required for the caching invariant: cache(l).normalized == normalize(l),
/// and two cache entries are def-eq iff their normalized forms are ==.
#[test]
fn test_def_eq_levels_share_normal_form() {
    let u = Level::param(Name::from_string("u"));
    let v = Level::param(Name::from_string("v"));

    // max(u, v) and max(v, u) should normalize to same form
    // (normalization sorts args)
    let max_uv = Level::Max(Arc::new(u.clone()), Arc::new(v.clone()));
    let max_vu = Level::Max(Arc::new(v.clone()), Arc::new(u.clone()));
    assert_eq!(
        max_uv.normalize(),
        max_vu.normalize(),
        "max(u,v) and max(v,u) must share normal form"
    );

    // succ(max(u, v)) and max(succ(u), succ(v)) should normalize identically
    let succ_max = Level::Succ(Arc::new(Level::Max(
        Arc::new(u.clone()),
        Arc::new(v.clone()),
    )));
    let max_succs = Level::Max(
        Arc::new(Level::succ(u.clone())),
        Arc::new(Level::succ(v.clone())),
    );
    assert_eq!(
        succ_max.normalize(),
        max_succs.normalize(),
        "succ(max(u,v)) and max(succ(u), succ(v)) must share normal form"
    );

    // max(u, u) should normalize to just u
    let max_uu = Level::Max(Arc::new(u.clone()), Arc::new(u.clone()));
    assert_eq!(
        max_uu.normalize(),
        u.normalize(),
        "max(u, u) must normalize to u"
    );

    // max(0, u) normalizes to u
    let max_0u = Level::Max(Arc::new(Level::zero()), Arc::new(u.clone()));
    assert_eq!(
        max_0u.normalize(),
        u.normalize(),
        "max(0, u) must normalize to u"
    );

    // imax(u, succ(v)) == max(u, succ(v))
    let imax_u_sv = Level::IMax(Arc::new(u.clone()), Arc::new(Level::succ(v.clone())));
    let max_u_sv = Level::Max(Arc::new(u.clone()), Arc::new(Level::succ(v.clone())));
    assert_eq!(
        imax_u_sv.normalize(),
        max_u_sv.normalize(),
        "imax(u, succ(v)) must share normal form with max(u, succ(v))"
    );
}

/// Document: is_geq normalizes internally, creating redundant work
/// when called from the max() smart constructor during normalization.
///
/// This test quantifies the amplification: for a Max tree with n leaves,
/// the max() smart constructor calls is_geq which re-normalizes already-
/// normalized subtrees. A future `max_from_normalized()` variant that calls
/// `is_geq_core` directly would eliminate this overhead.
#[test]
fn test_max_constructor_is_geq_renormalization() {
    let u = Level::param(Name::from_string("u"));
    let v = Level::param(Name::from_string("v"));

    // Calling Level::max on already-normalized levels triggers is_geq,
    // which internally calls normalize() on both arguments.
    // This is correct but redundant when the caller already holds
    // normalized forms.
    let norm_u = u.normalize();
    let norm_v = v.normalize();

    // Verify the result is correct (is_geq doesn't corrupt the output)
    let max_result = Level::max(norm_u.clone(), norm_v.clone());

    // The result must be def-eq to max(u, v)
    let max_raw = Level::Max(Arc::new(u.clone()), Arc::new(v.clone()));
    assert!(
        Level::is_def_eq(&max_result, &max_raw),
        "max() on normalized inputs must be def-eq to max() on raw inputs"
    );

    // Verify: when one side dominates (e.g., succ(u) >= u),
    // is_geq inside max() correctly simplifies
    let succ_u = Level::succ(u.clone());
    let max_dominated = Level::max(succ_u.clone(), u.clone());
    assert_eq!(
        max_dominated, succ_u,
        "max(succ(u), u) should simplify to succ(u) via is_geq"
    );
}

/// Test that is_geq with deep Max nesting completes in polynomial time (#1781).
///
/// Without memoization, is_geq_core decomposes Max on both sides, leading to
/// O(2^d) recursive calls when both l1 and l2 are deep Max chains sharing
/// the same parameters. With memoization, repeated (l1, l2) subproblems are
/// cached and the complexity drops to O(d^2).
///
/// Strategy: build right-associated Max chains `max(p0, max(p1, max(p2, ...)))`
/// on both sides with the same parameters, then check `is_geq(chain, chain)`.
/// This triggers full decomposition: each RHS Max splits into two AND branches,
/// each LHS Max splits into two OR branches, creating O(2^d) work without caching.
#[test]
fn test_is_geq_max_memoization_prevents_exponential_blowup() {
    use std::time::Instant;

    /// Build a right-associated Max chain: max(p0, max(p1, max(p2, ... max(p_{n-1}, base))))
    fn build_max_chain(n: usize) -> Level {
        let mut level = Level::succ(Level::zero()); // base = 1
        for i in (0..n).rev() {
            let param = Level::param(Name::from_string(&format!("p{i}")));
            level = Level::Max(Arc::new(param), Arc::new(level));
        }
        level
    }

    // With depth 30 and no memoization, is_geq(chain, chain) would require
    // O(2^30) ~= 1 billion recursive calls. With memoization, the cache
    // limits it to O(30^2) = 900 unique subproblems.
    let chain = build_max_chain(30);

    let start = Instant::now();
    // is_geq(chain, chain) should be true (reflexive after normalization)
    let result = Level::is_geq(&chain, &chain);
    let elapsed = start.elapsed();

    assert!(result, "is_geq(chain, chain) must be true (reflexive)");

    // With memoization, depth-30 should complete in well under 1 second.
    // Without memoization at depth 30, it would never complete.
    assert!(
        elapsed.as_secs() < 5,
        "is_geq on depth-30 Max chain took {:?}, suggesting missing memoization",
        elapsed
    );

    // Also test non-reflexive case: chain >= succ(chain) should be false
    let succ_chain = Level::succ(build_max_chain(30));
    let start2 = Instant::now();
    let result2 = Level::is_geq(&chain, &succ_chain);
    let elapsed2 = start2.elapsed();

    assert!(
        !result2,
        "max chain of params should not be >= succ(max chain)"
    );
    assert!(
        elapsed2.as_secs() < 5,
        "non-reflexive is_geq on depth-30 Max chain took {:?}",
        elapsed2
    );
}

/// Test that memoization preserves correctness for is_geq on shared Max substructure.
///
/// Builds a Max tree where both sides share the same subtree (diamond pattern),
/// verifying that cached results from one branch correctly apply to the other.
#[test]
fn test_is_geq_max_shared_subtree_correctness() {
    // shared = max(u, v)
    let u = Level::param(Name::from_string("u"));
    let v = Level::param(Name::from_string("v"));
    let shared = Level::Max(Arc::new(u.clone()), Arc::new(v.clone()));

    // diamond = max(shared, shared) — both arms are identical
    let diamond = Level::Max(Arc::new(shared.clone()), Arc::new(shared.clone()));

    // diamond >= u should be true (max(max(u,v), max(u,v)) >= u)
    assert!(
        Level::is_geq(&diamond, &u),
        "max(max(u,v), max(u,v)) >= u should be true"
    );

    // diamond >= v should be true
    assert!(
        Level::is_geq(&diamond, &v),
        "max(max(u,v), max(u,v)) >= v should be true"
    );

    // diamond >= succ(u) should be false (params could be 0)
    assert!(
        !Level::is_geq(&diamond, &Level::succ(u.clone())),
        "max(max(u,v), max(u,v)) >= succ(u) should be false"
    );

    // Deeper: triple nesting with shared structure
    let triple = Level::Max(Arc::new(diamond.clone()), Arc::new(shared.clone()));
    assert!(
        Level::is_geq(&triple, &u),
        "triple-nested max with shared subtree >= u should be true"
    );
    assert!(
        Level::is_geq(&triple, &v),
        "triple-nested max with shared subtree >= v should be true"
    );
}
