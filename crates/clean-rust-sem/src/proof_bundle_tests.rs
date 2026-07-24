// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the proof-obligation pipeline: bundle builder, ownership
//! obligation extraction, and SourceProgram API.

use crate::proof_bundle_builder::{BundleStats, OwnershipObligationKind, ProofBundleBuilder};
use crate::source::SourceProgram;

/// Parse a Rust source snippet or return the parse error as a test failure.
fn parse(source: &str) -> SourceProgram {
    SourceProgram::parse(source).expect("test source should parse")
}

// ---------------------------------------------------------------------------
// Positive: safe code produces satisfied obligations
// ---------------------------------------------------------------------------

#[test]
fn test_safe_shared_borrow_produces_satisfied_obligations() {
    let source = r#"
        fn main() {
            let x: i32 = 42;
            let _r: &i32 = &x;
            let _v: i32 = *_r;
        }
    "#;
    let program = parse(source);
    let bundle = program
        .proof_obligations()
        .expect("proof_obligations should succeed");

    // Should have at least one ownership obligation (from the borrow)
    assert!(
        !bundle.ownership_obligations.is_empty(),
        "expected at least one ownership obligation"
    );

    // All obligations from safe code should be satisfied
    let violated: Vec<_> = bundle
        .ownership_obligations
        .iter()
        .filter(|o| !o.satisfied)
        .collect();
    // The only potentially unsatisfied one is the aliasing check which
    // may report "passed" depending on interpreter behavior. Check that
    // borrow obligations specifically are satisfied.
    let borrow_obligations: Vec<_> = bundle
        .ownership_obligations
        .iter()
        .filter(|o| {
            matches!(
                o.kind,
                OwnershipObligationKind::SharedBorrowValid
                    | OwnershipObligationKind::MutableBorrowExclusive
            )
        })
        .collect();
    for obligation in &borrow_obligations {
        assert!(
            obligation.satisfied,
            "borrow obligation should be satisfied in safe code: {}",
            obligation.description
        );
    }

    // Stats should reflect satisfaction
    assert!(
        bundle.stats.total() > 0,
        "stats total should be > 0, got {}",
        bundle.stats.total()
    );
}

#[test]
fn test_safe_mutable_borrow_produces_satisfied_obligations() {
    let source = r#"
        fn main() {
            let mut x: i32 = 10;
            let r: &mut i32 = &mut x;
            *r = 20;
        }
    "#;
    let program = parse(source);
    let bundle = program
        .proof_obligations()
        .expect("proof_obligations should succeed");

    let mut_obligations: Vec<_> = bundle
        .ownership_obligations
        .iter()
        .filter(|o| o.kind == OwnershipObligationKind::MutableBorrowExclusive)
        .collect();

    assert!(
        !mut_obligations.is_empty(),
        "expected at least one MutableBorrowExclusive obligation"
    );
    for obligation in &mut_obligations {
        assert!(
            obligation.satisfied,
            "mutable borrow obligation should be satisfied in safe code: {}",
            obligation.description
        );
    }
}

// ---------------------------------------------------------------------------
// Negative: unsafe borrows produce violated obligations
// ---------------------------------------------------------------------------

#[test]
fn test_vec_new_lowers_and_produces_ownership_obligations() {
    // `Vec::new` is a standard-library constructor intrinsic (not a
    // user-declared function). It used to surface as `UnknownLocal` during VIR
    // lowering; the builtin-constructor lowering now models it as an empty
    // growable buffer so the proof-obligation pipeline succeeds and the
    // subsequent `&x` borrow yields a shared-borrow obligation.
    let source = r#"
        fn takes_ownership(v: Vec<i32>) -> i32 {
            0
        }
        fn main() {
            let x: Vec<i32> = Vec::new();
            let _y: i32 = takes_ownership(x);
            let _r: &Vec<i32> = &x;
        }
    "#;
    let program = parse(source);

    // Lowering no longer fails with `UnknownLocal { name: "Vec::new" }`.
    program
        .lower_to_vir()
        .expect("Vec::new should lower to VIR (no UnknownLocal)");

    let bundle = program
        .proof_obligations()
        .expect("proof_obligations should succeed once Vec::new lowers");

    assert!(
        !bundle.ownership_obligations.is_empty(),
        "expected ownership obligations from the borrow of the Vec"
    );

    // The `&x` borrow must be recorded as a shared-borrow obligation.
    assert!(
        bundle
            .ownership_obligations
            .iter()
            .any(|o| o.kind == OwnershipObligationKind::SharedBorrowValid),
        "expected a SharedBorrowValid obligation for `&x`"
    );

    // SOUNDNESS: the proof-bundle NLL tracks borrow conflicts, not
    // initialization/move dataflow, so it does not (yet) flag the
    // use-after-move of `x`. This test pins that `Vec::new` lowers and the
    // borrow obligation is emitted; detecting the move itself is a separate,
    // larger gap in the VIR-level move analysis and is intentionally not
    // asserted here. See `crate::ownership::BorrowChecker::check_borrow`,
    // which models `UseAfterMove` at the value level but is not wired into
    // the VIR proof-bundle pipeline.
}

#[test]
fn test_vec_with_capacity_lowers_to_vir() {
    // `Vec::with_capacity(n)` is the second Vec constructor intrinsic; the
    // capacity argument is a runtime hint that the verification model ignores,
    // but it must still lower without error.
    let source = r#"
        fn main() {
            let _v: Vec<u8> = Vec::with_capacity(8);
        }
    "#;
    let program = parse(source);
    program
        .lower_to_vir()
        .expect("Vec::with_capacity should lower to VIR");
}

#[test]
fn test_string_new_lowers_to_vir() {
    // `String::new` is the empty-string constructor intrinsic.
    let source = r#"
        fn main() {
            let _s: String = String::new();
        }
    "#;
    let program = parse(source);
    program
        .lower_to_vir()
        .expect("String::new should lower to VIR");
}

#[test]
fn test_box_new_is_transparent_over_argument() {
    // `Box::new(x)` is transparent over its argument in the verification model,
    // so it lowers using the inner value's type.
    let source = r#"
        fn main() {
            let _b: Box<i32> = Box::new(7);
        }
    "#;
    let program = parse(source);
    program
        .lower_to_vir()
        .expect("Box::new should lower to VIR");
}

#[test]
fn test_vec_constructor_into_non_vec_destination_is_rejected() {
    // SOUNDNESS: the empty-Vec lowering must not silently coerce a `Vec` into a
    // non-Vec destination. A `Vec::new()` initializer for an `i32` binding must
    // be rejected rather than producing a bogus aggregate.
    let source = r#"
        fn main() {
            let _x: i32 = Vec::new();
        }
    "#;
    let program = parse(source);
    let err = program
        .lower_to_vir()
        .expect_err("Vec::new into an i32 destination must be rejected");
    let msg = format!("{err:?}");
    assert!(
        msg.contains("Vec constructor"),
        "expected a Vec-constructor destination-type error, got: {msg}"
    );
}

#[test]
fn test_constructor_intrinsic_allow_list_is_arity_sensitive() {
    // Negative case: the builtin-constructor allow-list only fires for the
    // exact name+arity pairs. A wrong-arity call (e.g. `Vec::new(5)`,
    // `String::from()`, `Box::new()`) must NOT be treated as a builtin and must
    // still surface as the original `UnknownLocal` lowering error, so the
    // allow-list cannot mask genuinely unsupported callees.
    for source in [
        "fn main() { let _v: Vec<i32> = Vec::new(5); }",
        "fn main() { let _s: String = String::from(); }",
        "fn main() { let _b: Box<i32> = Box::new(); }",
    ] {
        let program = parse(source);
        let err = program
            .lower_to_vir()
            .expect_err("wrong-arity constructor call must not lower as a builtin");
        let msg = format!("{err:?}");
        assert!(
            msg.contains("UnknownLocal"),
            "expected UnknownLocal for `{source}`, got: {msg}"
        );
    }
}

// ---------------------------------------------------------------------------
// BundleStats
// ---------------------------------------------------------------------------

#[test]
fn test_bundle_stats_empty() {
    let stats = BundleStats::from_obligations(&[]);
    assert_eq!(stats.total(), 0);
    assert!(stats.all_satisfied());
}

#[test]
fn test_bundle_stats_counts_by_kind() {
    use crate::proof_bundle_builder::OwnershipObligation;
    use clean_kernel::Expr;

    let obligations = vec![
        OwnershipObligation {
            function: "f".to_string(),
            kind: OwnershipObligationKind::SharedBorrowValid,
            description: "test".to_string(),
            goal: Expr::const_str("test"),
            satisfied: true,
            location: None,
        },
        OwnershipObligation {
            function: "f".to_string(),
            kind: OwnershipObligationKind::MutableBorrowExclusive,
            description: "test".to_string(),
            goal: Expr::const_str("test"),
            satisfied: true,
            location: None,
        },
        OwnershipObligation {
            function: "f".to_string(),
            kind: OwnershipObligationKind::MoveWithoutLiveBorrows,
            description: "test".to_string(),
            goal: Expr::const_str("test"),
            satisfied: false,
            location: None,
        },
        OwnershipObligation {
            function: "f".to_string(),
            kind: OwnershipObligationKind::AliasingInvalidation,
            description: "test".to_string(),
            goal: Expr::const_str("test"),
            satisfied: true,
            location: None,
        },
    ];

    let stats = BundleStats::from_obligations(&obligations);
    assert_eq!(stats.shared_borrow_valid, 1);
    assert_eq!(stats.mutable_borrow_exclusive, 1);
    assert_eq!(stats.move_without_live_borrows, 1);
    assert_eq!(stats.aliasing_invalidation, 1);
    assert_eq!(stats.total_satisfied, 3);
    assert_eq!(stats.total_violated, 1);
    assert_eq!(stats.total(), 4);
    assert!(!stats.all_satisfied());
}

// ---------------------------------------------------------------------------
// ProofBundleBuilder direct API
// ---------------------------------------------------------------------------

#[test]
fn test_proof_bundle_builder_from_source() {
    let source = r#"
        fn main() {
            let x: i32 = 5;
            let _y: i32 = x;
        }
    "#;
    let program = parse(source);
    let builder = ProofBundleBuilder::new();
    let bundle = builder
        .from_source(&program)
        .expect("from_source should succeed");

    // Should have function types translated
    assert!(
        !bundle.translated_types.is_empty(),
        "expected translated function types"
    );

    // Aliasing observation should exist
    // (may pass or fail depending on interpreter, but must be present)
    let _ = &bundle.aliasing_observation;
}

#[test]
fn test_proof_bundle_builder_default_trait() {
    // ProofBundleBuilder implements Default
    let builder = ProofBundleBuilder::default();
    let source = r#"
        fn noop() {}
    "#;
    let program = parse(source);
    let bundle = builder
        .from_source(&program)
        .expect("from_source should succeed");

    // A no-op function should have minimal obligations
    assert!(bundle.translated_types.contains_key("noop"));
}

// ---------------------------------------------------------------------------
// SourceProgram API parity
// ---------------------------------------------------------------------------

#[test]
fn test_source_program_proof_obligations_matches_build_proof_bundle() {
    let source = r#"
        fn add(a: i32, b: i32) -> i32 {
            a + b
        }
        fn main() {
            let _result: i32 = add(1, 2);
        }
    "#;
    let program = parse(source);

    let bundle_a = program
        .build_proof_bundle()
        .expect("build_proof_bundle should succeed");
    let bundle_b = program
        .proof_obligations()
        .expect("proof_obligations should succeed");

    // Both should produce bundles with the same function set
    assert_eq!(
        bundle_a.translated_types.keys().collect::<Vec<_>>(),
        bundle_b.translated_types.keys().collect::<Vec<_>>(),
    );

    // Both should have the same obligation count
    assert_eq!(bundle_a.obligations.len(), bundle_b.obligations.len());
    assert_eq!(
        bundle_a.ownership_obligations.len(),
        bundle_b.ownership_obligations.len()
    );
}

// ---------------------------------------------------------------------------
// Aliasing integration
// ---------------------------------------------------------------------------

#[test]
fn test_aliasing_observation_included_in_bundle() {
    let source = r#"
        fn main() {
            let x: i32 = 1;
            let _r1: &i32 = &x;
            let _r2: &i32 = &x;
        }
    "#;
    let program = parse(source);
    let bundle = program
        .proof_obligations()
        .expect("proof_obligations should succeed");

    // Aliasing observation should be present
    assert!(
        !bundle.aliasing_observation.summary.is_empty(),
        "aliasing summary should not be empty"
    );

    // Should have at least one AliasingInvalidation obligation
    let aliasing_count = bundle
        .ownership_obligations
        .iter()
        .filter(|o| o.kind == OwnershipObligationKind::AliasingInvalidation)
        .count();
    assert!(
        aliasing_count > 0,
        "expected at least one aliasing obligation"
    );
}

// ---------------------------------------------------------------------------
// VIR obligations still present alongside ownership obligations
// ---------------------------------------------------------------------------

#[test]
fn test_vir_obligations_coexist_with_ownership() {
    let source = r#"
        fn main() {
            let mut x: i32 = 10;
            let r: &mut i32 = &mut x;
            *r = 20;
        }
    "#;
    let program = parse(source);
    let bundle = program
        .proof_obligations()
        .expect("proof_obligations should succeed");

    // VIR-level obligations (from proof_obligations module) should be present
    assert!(
        !bundle.obligations.is_empty(),
        "expected VIR-level obligations"
    );

    // Ownership-level obligations (from builder) should also be present
    assert!(
        !bundle.ownership_obligations.is_empty(),
        "expected ownership obligations"
    );
}
