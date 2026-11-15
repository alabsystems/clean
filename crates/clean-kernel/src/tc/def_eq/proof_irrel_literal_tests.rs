// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Actual literal-selection paths and independent result-field observations.
//!
//! These native tests do not attach a source-execution theorem. In particular,
//! observing a warm shared Name does not certify LazyLock initialization, Arc
//! ownership, compiler layouts, or the hash primitives. The expected result is
//! never constructed with Expr::const_: its graph and metadata are inspected.

use crate::cert::ProofCert;
use crate::env::{murmur_hash_64a, Environment};
use crate::expr::{BigNat, Expr, ExprKind, ExprMeta, Literal};
use crate::level::Level;
use crate::name::{Name, NameInner};
use crate::tc::infer::infer_literal_type;
use crate::tc::TypeChecker;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

/// Independently spell the wrapping mixing equation, rather than recomputing
/// metadata through the result's production constructor or compute_meta.
fn observed_mix_hash(h: u64, k: u64) -> u64 {
    const M: u64 = 0xc6a4_a793_5bd1_e995;
    let product = k.wrapping_mul(M);
    (h ^ product ^ (product >> 47) ^ M).wrapping_mul(M)
}

fn literal_result_invariant(result: &Expr, expected: &str) -> bool {
    let ExprKind::Const(name, levels) = result.kind() else {
        return false;
    };
    let NameInner::Str(parent, component) = name.inner() else {
        return false;
    };
    if !matches!(parent.inner(), NameInner::Anon)
        || parent.lean4_hash() != 1723
        || component.as_bytes() != expected.as_bytes()
        || !levels.is_empty()
    {
        return false;
    }
    let expected_name_hash = observed_mix_hash(
        parent.lean4_hash(),
        murmur_hash_64a(component.as_bytes(), 11),
    );
    if name.lean4_hash() != expected_name_hash {
        return false;
    }

    // Name::hash writes its public cached u64. SmallVec::hash writes the slice,
    // so an independently hashed empty slice supplies its empty-level input.
    let mut name_hasher = DefaultHasher::new();
    name.lean4_hash().hash(&mut name_hasher);
    let mut levels_hasher = DefaultHasher::new();
    let empty_levels: &[Level] = &[];
    empty_levels.hash(&mut levels_hasher);
    let expected_hash = observed_mix_hash(
        5,
        observed_mix_hash(name_hasher.finish(), levels_hasher.finish()),
    ) as u32;
    let raw = result.meta().raw();
    raw >> 32 == 0 && raw == u64::from(expected_hash)
}

fn literal(input: &Expr) -> &Literal {
    let ExprKind::Lit(value) = input.kind() else {
        panic!("fixture must remain a literal");
    };
    value
}

fn string_strong_count(value: &Literal) -> Option<usize> {
    match value {
        Literal::String(value) => Some(Arc::strong_count(value)),
        Literal::Nat(_) => None,
    }
}

fn assert_input_preserved(
    input: &Expr,
    original: &Literal,
    raw: u64,
    big_data: Option<*const u64>,
) {
    let current = literal(input);
    assert_eq!(current, original, "literal payload must not change");
    assert_eq!(input.meta().raw(), raw, "input metadata must not change");
    match (current, original) {
        (Literal::String(current), Literal::String(original)) => {
            assert!(
                Arc::ptr_eq(current, original),
                "borrowed string graph changed"
            );
            assert_eq!(current.as_bytes(), original.as_bytes());
        }
        (Literal::Nat(BigNat::Big(current)), Literal::Nat(BigNat::Big(_))) => {
            assert_eq!(
                Some(current.as_ptr()),
                big_data,
                "borrowed limb storage changed"
            );
        }
        (Literal::Nat(BigNat::Small(_)), Literal::Nat(BigNat::Small(_))) => {}
        _ => panic!("literal representation changed"),
    }
}

fn assert_same_name_graph(left: &Expr, right: &Expr) {
    let (ExprKind::Const(left, _), ExprKind::Const(right, _)) = (left.kind(), right.kind()) else {
        panic!("observed results must be constants");
    };
    let (NameInner::Str(lp, ls), NameInner::Str(rp, rs)) = (left.inner(), right.inner()) else {
        panic!("observed builtin names must have a string component");
    };
    assert!(Arc::ptr_eq(lp, rp), "cloned Name parent must be shared");
    assert!(Arc::ptr_eq(ls, rs), "cloned Name bytes must be shared");
}

fn exercise_literal_paths(value: Literal, expected: &str) {
    let input = Expr::from_kind(ExprKind::Lit(value));
    let original = literal(&input).clone();
    let raw = input.meta().raw();
    let big_data = match literal(&input) {
        Literal::Nat(BigNat::Big(limbs)) => Some(limbs.as_ptr()),
        _ => None,
    };
    let env = Environment::for_lean_replay();
    let tc = TypeChecker::new(&env);

    let input_refs = string_strong_count(literal(&input));
    let direct = infer_literal_type(literal(&input));
    assert!(literal_result_invariant(&direct, expected));
    // The current string fixtures allocate fresh payload Arcs. This count
    // equality is not a general borrow frame: a payload may alias the selected
    // builtin Name's component, whose strong count Name::clone changes.
    assert_eq!(string_strong_count(literal(&input)), input_refs);
    assert_input_preserved(&input, &original, raw, big_data);

    // Reach the changed arm without the quick cache, and then exercise both
    // the first cache insertion and a real cache hit through its public entry.
    let inner = tc
        .try_infer_type_quick_inner(&input)
        .expect("literal quick arm");
    assert!(literal_result_invariant(&inner, expected));
    assert_eq!(string_strong_count(literal(&input)), input_refs);
    assert!(tc.quick_infer_cache.borrow().is_empty());
    let quick = tc
        .try_infer_type_quick(&input)
        .expect("quick literal inference");
    assert!(literal_result_invariant(&quick, expected));
    assert_eq!(tc.quick_infer_cache.borrow().len(), 1);
    let cache_before = tc.quick_infer_cache.borrow().stats().clone();
    assert_eq!(cache_before.misses, 1);
    assert_eq!(cache_before.hits_current, 0);
    let quick_again = tc
        .try_infer_type_quick(&input)
        .expect("cached quick literal inference");
    assert!(literal_result_invariant(&quick_again, expected));
    let cache_after = tc.quick_infer_cache.borrow().stats().clone();
    assert_eq!(cache_after.hits_current, cache_before.hits_current + 1);
    assert_eq!(cache_after.misses, cache_before.misses);
    assert_input_preserved(&input, &original, raw, big_data);

    let ordinary = tc.infer_type(&input).expect("ordinary literal inference");
    assert!(literal_result_invariant(&ordinary, expected));
    let (certified, cert) = tc
        .infer_type_with_cert(&input)
        .expect("certificate literal inference");
    assert!(literal_result_invariant(&certified, expected));
    // ProofCert has a custom Drop implementation: observe its owned fields
    // through a borrow, keeping the real certificate and its input owners live.
    let ProofCert::Lit {
        lit: cert_lit,
        type_: cert_type,
    } = &cert
    else {
        panic!("literal inference must retain a literal certificate");
    };
    assert_eq!(cert_lit, &original);
    match (cert_lit, literal(&input)) {
        (Literal::String(retained), Literal::String(borrowed)) => {
            assert!(Arc::ptr_eq(retained, borrowed));
        }
        (Literal::Nat(_), Literal::Nat(_)) => {}
        _ => panic!("literal certificate changed the input kind"),
    }
    assert!(literal_result_invariant(cert_type, expected));
    assert_input_preserved(&input, &original, raw, big_data);

    for result in [
        &inner,
        &quick,
        &quick_again,
        &ordinary,
        &certified,
        cert_type,
    ] {
        assert_same_name_graph(&direct, result);
        assert!(
            tc.type_is_quickly_not_in_prop(result),
            "existing literal prefilter must remain reachable"
        );
    }
    // Caches and certificates may legitimately retain cloned input owners.
    // Payload identity/content above is checked independently of their counts.
}

#[test]
fn literal_type_nat_paths_preserve_representation_and_input() {
    for value in [
        BigNat::Small(0),
        BigNat::Small(u64::MAX),
        BigNat::Big(vec![u64::MAX, 1, 7]),
    ] {
        exercise_literal_paths(Literal::Nat(value), "Nat");
    }
}

#[test]
fn literal_type_string_paths_preserve_representation_and_input() {
    for value in ["", "λ🦀", "a\0b", "Nat"] {
        exercise_literal_paths(Literal::String(Arc::from(value)), "String");
    }
}

fn exercise_literal_alias_counts(
    value: Literal,
    selected_seed: &Expr,
    selected: &str,
    unselected_seed: &Expr,
    unselected: &str,
) {
    let (ExprKind::Const(selected_name, _), ExprKind::Const(unselected_name, _)) =
        (selected_seed.kind(), unselected_seed.kind())
    else {
        panic!("builtin seeds must be constants");
    };
    let (
        NameInner::Str(selected_parent, selected_component),
        NameInner::Str(other_parent, other_component),
    ) = (selected_name.inner(), unselected_name.inner())
    else {
        panic!("builtin seeds must contain parent and string component Arcs");
    };
    let input = Expr::from_kind(ExprKind::Lit(value));
    let original = literal(&input).clone();
    let raw = input.meta().raw();
    let big_data = match literal(&input) {
        Literal::Nat(BigNat::Big(limbs)) => Some(limbs.as_ptr()),
        _ => None,
    };
    // Borrow the two actual Arc<Name> parents and Arc<str> components. The
    // input and its retained payload copy are already included in the baseline.
    let counts = || {
        (
            Arc::strong_count(selected_parent),
            Arc::strong_count(selected_component),
            Arc::strong_count(other_parent),
            Arc::strong_count(other_component),
        )
    };
    let baseline = counts();
    // Different builtin names do not imply distinct parent allocations. An
    // alias of either selected Arc observes its increment, even when reached
    // through the unselected graph; this is not a whole-heap frame claim.
    let other_parent_delta = usize::from(Arc::ptr_eq(selected_parent, other_parent));
    let other_component_delta = usize::from(Arc::ptr_eq(selected_component, other_component));
    let result = infer_literal_type(literal(&input));
    assert!(literal_result_invariant(&result, selected));
    assert_same_name_graph(selected_seed, &result);
    assert_input_preserved(&input, &original, raw, big_data);
    assert_eq!(
        counts(),
        (
            baseline.0 + 1,
            baseline.1 + 1,
            baseline.2 + other_parent_delta,
            baseline.3 + other_component_delta,
        ),
        "{selected}: result must retain both selected Arcs with alias-safe unselected effects"
    );
    assert!(literal_result_invariant(selected_seed, selected));
    assert!(literal_result_invariant(unselected_seed, unselected));
    drop(result);
    assert_eq!(
        counts(),
        baseline,
        "{selected}: dropping result restores all observed counts"
    );
    assert_input_preserved(&input, &original, raw, big_data);
    assert!(literal_result_invariant(selected_seed, selected));
    assert!(literal_result_invariant(unselected_seed, unselected));
}

#[test]
fn literal_type_builtin_aliases_preserve_payload_with_legal_refcount_changes() {
    // Exact counts on the global builtin Arcs need isolation from other tests.
    // Re-run this same test, and only this test, in a fresh libtest process.
    const CHILD_MARKER: &str = "CLEAN_LITERAL_BUILTIN_ALIAS_TEST_CHILD";
    let (_, module) = module_path!()
        .split_once("::")
        .expect("literal tests must be nested inside the kernel crate");
    let test_name = format!(
        "{module}::literal_type_builtin_aliases_preserve_payload_with_legal_refcount_changes"
    );
    if std::env::var(CHILD_MARKER).ok().as_deref() != Some(test_name.as_str()) {
        let output = std::process::Command::new(
            std::env::current_exe().expect("locate current libtest executable"),
        )
        .arg(&test_name)
        .arg("--exact")
        .arg("--test-threads=1")
        .env(CHILD_MARKER, &test_name)
        .output()
        .expect("run isolated builtin Arc alias regression");
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            output.status.success()
                && stdout
                    .matches("test result: ok. 1 passed; 0 failed; 0 ignored;")
                    .count()
                    == 1,
            "isolated alias regression did not run exactly once: {}\nstdout:\n{stdout}\nstderr:\n{stderr}",
            output.status
        );
        return;
    }

    // Warm both real builtin graphs before taking any baseline. These are
    // native ownership observations, not proofs of source execution, lazy
    // initialization, Arc's implementation, or new graph allocation.
    let string_seed = infer_literal_type(&Literal::String(Arc::from("seed")));
    let nat_seed = infer_literal_type(&Literal::nat(0));
    assert!(literal_result_invariant(&string_seed, "String"));
    assert!(literal_result_invariant(&nat_seed, "Nat"));
    let (ExprKind::Const(string_name, _), ExprKind::Const(nat_name, _)) =
        (string_seed.kind(), nat_seed.kind())
    else {
        panic!("builtin seeds must be constants");
    };
    let (NameInner::Str(_, string_component), NameInner::Str(_, nat_component)) =
        (string_name.inner(), nat_name.inner())
    else {
        panic!("builtin seeds must contain the actual string components");
    };

    // The payload can alias either component; its bytes do not select Nat.
    for component in [string_component, nat_component] {
        exercise_literal_alias_counts(
            Literal::String(Arc::clone(component)),
            &string_seed,
            "String",
            &nat_seed,
            "Nat",
        );
    }
    // Nat selects the other graph. Observe both ownership edges in that
    // direction too, without presuming either pair of parent Arcs is distinct.
    for value in [BigNat::Small(0), BigNat::Big(vec![u64::MAX, 1, 7])] {
        exercise_literal_alias_counts(
            Literal::Nat(value),
            &nat_seed,
            "Nat",
            &string_seed,
            "String",
        );
    }
}

#[test]
fn literal_type_observer_rejects_bytes_correct_corrupt_outputs() {
    for (value, expected) in [
        (Literal::nat(0), "Nat"),
        (Literal::String(Arc::from("")), "String"),
    ] {
        let good = infer_literal_type(&value);
        assert!(
            literal_result_invariant(&good, expected),
            "positive observer control"
        );
        let ExprKind::Const(name, _) = good.kind() else {
            panic!("literal result must be a constant");
        };

        let wrong_kind =
            Expr::from_kind(ExprKind::Proj(name.clone(), 0, Arc::new(Expr::nat_lit(0))));
        assert!(!literal_result_invariant(&wrong_kind, expected));
        let wrong_levels = Expr::const_(name.clone(), vec![Level::zero()]);
        assert!(!literal_result_invariant(&wrong_levels, expected));
        let wrong_parent = Expr::const_(Name::anon().str("Prefix").str(expected), vec![]);
        assert!(!literal_result_invariant(&wrong_parent, expected));
        let other = if expected == "Nat" { "String" } else { "Nat" };
        assert!(!literal_result_invariant(&good, other));

        let hash = good.hash_cached();
        let bad_hash = Expr::with_meta(
            good.kind().clone(),
            ExprMeta::pack(hash ^ 1, 0, 0, false, false, false, false),
        );
        assert!(!literal_result_invariant(&bad_hash, expected));
        for (range, depth, fvar, expr_mvar, level_mvar, level_param) in [
            (1, 0, false, false, false, false),
            (0, 1, false, false, false, false),
            (0, 0, true, false, false, false),
            (0, 0, false, true, false, false),
            (0, 0, false, false, true, false),
            (0, 0, false, false, false, true),
        ] {
            let corrupt = Expr::with_meta(
                good.kind().clone(),
                ExprMeta::pack(hash, range, depth, fvar, expr_mvar, level_mvar, level_param),
            );
            assert!(!literal_result_invariant(&corrupt, expected));
        }
    }
}
