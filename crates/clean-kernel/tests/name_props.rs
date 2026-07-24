// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Phase 1c: Proptest equivalents of Kani timeout harnesses for Name (#982)
//! Migrated from designs/2026-03-04-982-proptest-alternative.md
//!
//! Kani harnesses verify_name_hash_consistency and verify_name_no_panic timeout
//! because Name is a recursive linked list via Arc<Name>. CBMC generates 81M
//! clauses for even a 4-byte Name. These proptests exercise real production
//! code with arbitrary-depth names.

use clean_kernel::Name;
use proptest::prelude::*;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

fn compute_hash(name: &Name) -> u64 {
    let mut hasher = DefaultHasher::new();
    name.hash(&mut hasher);
    hasher.finish()
}

/// Strategy for generating Names with string segments.
fn name_str_strategy(max_depth: usize) -> impl Strategy<Value = Name> {
    prop::collection::vec("[a-z]{1,4}", 1..=max_depth).prop_map(|segments| {
        segments
            .iter()
            .fold(Name::anon(), |parent, seg| parent.str(seg))
    })
}

/// Strategy for generating Names with mixed string and numeric segments.
fn name_mixed_strategy(max_depth: usize) -> impl Strategy<Value = Name> {
    prop::collection::vec(
        prop_oneof![
            "[a-z]{1,4}".prop_map(|s| (Some(s), None)),
            (0u64..1000).prop_map(|n| (None, Some(n))),
        ],
        1..=max_depth,
    )
    .prop_map(|segments| {
        segments.iter().fold(Name::anon(), |parent, seg| match seg {
            (Some(s), _) => parent.str(s),
            (_, Some(n)) => parent.num(*n),
            _ => unreachable!(),
        })
    })
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    // ================================================================
    // Name hash consistency (Kani equivalent: verify_name_hash_consistency)
    // Kani generates 81M clauses for this property on a 4-byte Name.
    // ================================================================

    /// Equal names produce equal hashes.
    #[test]
    fn prop_name_hash_eq_implies_hash_eq(
        segments in prop::collection::vec("[a-z]{1,4}", 1..6)
    ) {
        let name1 = segments.iter().fold(Name::anon(), |parent, seg| {
            parent.str(seg)
        });
        let name2 = segments.iter().fold(Name::anon(), |parent, seg| {
            parent.str(seg)
        });
        let hash1 = compute_hash(&name1);
        let hash2 = compute_hash(&name2);
        prop_assert_eq!(hash1, hash2,
            "Equal names should have equal hashes");
        prop_assert_eq!(&name1, &name2,
            "Names built from same segments should be equal");
    }

    // ================================================================
    // Name clone equality (Kani equivalents: verify_name_no_panic,
    // verify_name_roundtrip_alphanumeric, verify_anon_consistent)
    // ================================================================

    /// Clone produces equal name.
    #[test]
    fn prop_name_clone_eq(
        segments in prop::collection::vec("[a-z]{1,4}", 1..8)
    ) {
        let name = segments.iter().fold(Name::anon(), |parent, seg| {
            parent.str(seg)
        });
        let cloned = name.clone();
        prop_assert_eq!(&name, &cloned,
            "Cloned name should equal original");
        prop_assert_eq!(compute_hash(&name), compute_hash(&cloned),
            "Cloned name should have same hash");
    }

    // ================================================================
    // Name with numeric segments
    // ================================================================

    /// Mixed string/numeric names: clone and hash consistency.
    #[test]
    fn prop_name_mixed_clone_hash(name in name_mixed_strategy(6)) {
        let cloned = name.clone();
        prop_assert_eq!(&name, &cloned,
            "Cloned mixed name should equal original");
        prop_assert_eq!(compute_hash(&name), compute_hash(&cloned),
            "Cloned mixed name should have same hash");
    }

    /// Deep names: verify no stack overflow on clone/eq/hash.
    #[test]
    fn prop_name_deep_no_panic(name in name_str_strategy(20)) {
        let cloned = name.clone();
        prop_assert_eq!(&name, &cloned);
        let _ = compute_hash(&name);
    }

    // ================================================================
    // Name equality reflexivity
    // ================================================================

    #[test]
    fn prop_name_eq_reflexive(name in name_mixed_strategy(8)) {
        prop_assert_eq!(&name, &name,
            "Name should be equal to itself");
    }

    // ================================================================
    // Name ordering consistency with equality
    // ================================================================

    #[test]
    fn prop_name_ord_consistent_with_eq(
        n1 in name_str_strategy(5),
        n2 in name_str_strategy(5)
    ) {
        use std::cmp::Ordering;
        let eq = n1 == n2;
        let ord = n1.cmp(&n2);
        if eq {
            prop_assert_eq!(ord, Ordering::Equal,
                "Equal names should have Equal ordering");
        } else {
            prop_assert_ne!(ord, Ordering::Equal,
                "Unequal names should not have Equal ordering");
        }
    }

    // ================================================================
    // Name from_string roundtrip
    // ================================================================

    /// from_string produces expected structure for dotted names.
    #[test]
    fn prop_name_from_string_segments(
        segments in prop::collection::vec("[a-z]{1,4}", 1..5)
    ) {
        let dotted = segments.join(".");
        let from_str = Name::from_string(&dotted);
        let manual = segments.iter().fold(Name::anon(), |parent, seg| {
            parent.str(seg)
        });
        prop_assert_eq!(&from_str, &manual,
            "from_string should match manual construction: {:?}", dotted);
    }
}
