// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Kani drop workaround for Arc<Name> unwinding in Level
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//
// Level enum contains Param(Name) and MVar(Name) variants. Even though
// harnesses only construct Zero/Succ chains, CBMC generates drop glue
// for ALL variants, triggering recursive Arc<Name> unwinding.
//
// Solution: Leak Level values with std::mem::forget. Sound for functional
// verification: we verify value semantics, not deallocation.

/// Leak a Level to prevent CBMC from unwinding recursive Arc<Name> drops.
fn leak(l: Level) {
    std::mem::forget(l);
}

/// Verify that max is commutative: max(a, b) == max(b, a)
#[kani::proof]
#[kani::unwind(6)]
fn verify_level_max_symmetric() {
    let a_depth: u8 = kani::any();
    let b_depth: u8 = kani::any();

    // Keep depths small to bound recursion
    kani::assume(a_depth < 4);
    kani::assume(b_depth < 4);

    // Create concrete levels
    let a = build_level_from_depth(a_depth);
    let b = build_level_from_depth(b_depth);

    let max_ab = Level::max(a.clone(), b.clone());
    let max_ba = Level::max(b, a);

    // Commutativity
    assert_eq!(max_ab, max_ba);
    leak(max_ab);
    leak(max_ba);
}

/// Verify level comparison is reflexive: l <= l for all l
#[kani::proof]
#[kani::unwind(4)]
fn verify_level_leq_reflexive() {
    let depth: u8 = kani::any();
    kani::assume(depth < 4);

    let level = build_level_from_depth(depth);

    // Every level is less-than-or-equal to itself
    assert!(Level::leq(&level, &level));
    leak(level);
}

/// Verify normalize is idempotent: normalize(normalize(l)) == normalize(l)
#[kani::proof]
#[kani::unwind(6)]
fn verify_level_normalize_idempotent() {
    let depth: u8 = kani::any();
    kani::assume(depth < 3);

    let level = build_level_from_depth(depth);
    let norm1 = level.normalize();
    let norm2 = norm1.normalize();

    assert_eq!(norm1, norm2);
    leak(norm1);
    leak(norm2);
    leak(level);
}

/// Verify is_zero consistency: is_zero implies not is_nonzero
#[kani::proof]
#[kani::unwind(4)]
fn verify_zero_nonzero_exclusive() {
    let depth: u8 = kani::any();
    kani::assume(depth < 4);

    let level = build_level_from_depth(depth);

    // If is_zero, then not is_nonzero
    if level.is_zero() {
        assert!(!level.is_nonzero());
    }
    // If is_nonzero, then not is_zero
    if level.is_nonzero() {
        assert!(!level.is_zero());
    }
    leak(level);
}

/// Helper to build a concrete level from a depth value.
/// Maps depth to succ^depth(Zero).
fn build_level_from_depth(depth: u8) -> Level {
    let mut l = Level::zero();
    for _ in 0..depth {
        l = Level::succ(l);
    }
    l
}
