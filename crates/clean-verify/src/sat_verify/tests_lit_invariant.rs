// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Behavioral regression tests for #3329: `Lit(0)` must not be a valid
//! literal because it is self-negating (`-0 == 0`), violating `l != ~l`.

use super::types::Lit;

#[test]
fn test_lit_negate_invariant_wide_range() {
    // `l != ~l` across a wide sample of valid i32 literals.
    let samples: Vec<i32> = (-128..=128)
        .chain([i32::MIN + 1, -10_000, -1, 1, 10_000, i32::MAX])
        .filter(|&v| v != 0)
        .collect();
    for val in samples {
        let lit = Lit::new(val).expect("nonzero literal should construct");
        assert_eq!(lit.negate().negate(), lit, "negate involutive for {val}");
        assert_ne!(lit.negate(), lit, "l != ~l invariant for {val}");
        assert_eq!(
            lit.var(),
            lit.negate().var(),
            "var() invariant under negate for {val}"
        );
    }
}

#[test]
#[should_panic(expected = "Lit(0) is self-negating")]
fn test_lit_negate_panics_on_zero_even_in_release() {
    // Defense-in-depth: if a bug ever constructs a Lit(0) via the
    // pub(crate) tuple constructor, negate() MUST not silently return
    // Lit(0) (which would make resolution unsound). The assert! (not
    // debug_assert!) ensures this fires in release builds too.
    let rogue = Lit(0);
    let _ = rogue.negate();
}

#[test]
fn test_lit_field_is_pub_crate_only() {
    // Documentation test: Lit's inner field is pub(crate) so external
    // callers cannot write `Lit(0)` directly. This test compiles only
    // because we are in the same crate. Downstream code must use
    // `Lit::new()` (fallible) or `Lit::from_dimacs()` (panics on 0).
    let lit = Lit::new(7).expect("valid");
    assert_eq!(lit.to_dimacs(), 7);
    let _ = Lit(0); // intentionally — crate-local only
}
