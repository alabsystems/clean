// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Two-window controls. Every stored entry comes from actual type inference;
//! the enclosing test frame only exposes the memo before outer-frame cleanup.

use super::*;
use crate::cert::CertVerifier;
use crate::{BinderInfo, Environment, Name, TypeError};

struct MemoFrame<'tc, 'env>(&'tc TypeChecker<'env>);

impl<'tc, 'env> MemoFrame<'tc, 'env> {
    fn new(checker: &'tc TypeChecker<'env>, retain: bool) -> Self {
        assert_eq!(checker.infer_memo_depth.replace(1), 0);
        assert!(!checker.cert_retained.replace(retain));
        assert!(checker.infer_arc_memo.borrow().is_empty());
        Self(checker)
    }
}

impl Drop for MemoFrame<'_, '_> {
    fn drop(&mut self) {
        self.0.infer_memo_depth.set(0);
        self.0.cert_retained.set(false);
        self.0.infer_arc_memo.borrow_mut().clear();
    }
}

fn infer(checker: &TypeChecker<'_>, node: &Arc<Expr>) -> Arc<ProofCert> {
    let (ty, cert) = checker
        .infer_type_with_cert_arc(node)
        .expect("actual inference");
    assert_eq!(ty, Expr::type_());
    cert
}

fn assert_bound(checker: &TypeChecker<'_>, capacity: usize) {
    let memo = checker.infer_arc_memo.borrow();
    assert!(memo.len() <= capacity);
    for window in [&memo.current, &memo.previous] {
        assert!(window.len <= capacity / 2 + capacity % 2);
        assert_eq!(
            window.len,
            window.buckets.values().map(HashMap::len).sum::<usize>()
        );
    }
    for (scope, bucket) in &memo.current.buckets {
        if let Some(previous) = memo.previous.buckets.get(scope) {
            assert!(bucket.keys().all(|key| !previous.contains_key(key)));
        }
    }
}

#[test]
fn aggregate_capacity_zero_one_odd_and_large_admits_later_nodes() {
    let env = Environment::new();
    for capacity in [0, 1, 2, 3, 5, 100_001] {
        let mut checker = TypeChecker::new(&env);
        checker.set_max_cache_entries(capacity);
        let _frame = MemoFrame::new(&checker, true);
        // Cross at least two rotations, including the odd-cap total-size guard.
        for _ in 0..2 * capacity + 3 {
            let node = Arc::new(Expr::prop());
            let cert = infer(&checker, &node);
            let key = checker.infer_arc_memo_key(&node);
            assert_eq!(
                checker.infer_arc_memo.borrow().contains_key(&key),
                capacity != 0
            );
            assert!(checker.infer_arc_memo.borrow().len() <= capacity);
            if capacity == 1 {
                assert_eq!(checker.infer_arc_memo.borrow().previous.len, 0);
            }
            // Replaying each tiny certificate exercises the disabled-cache case
            // too; an eviction never supplies a fabricated typing result.
            assert_eq!(
                CertVerifier::new(&env)
                    .verify(&cert, &node)
                    .expect("replay"),
                Expr::type_()
            );
        }
        assert_bound(&checker, capacity);
    }
}

#[test]
fn largest_capacity_threshold_does_not_overflow() {
    let env = Environment::new();
    let mut checker = TypeChecker::new(&env);
    checker.set_max_cache_entries(usize::MAX);
    let _frame = MemoFrame::new(&checker, true);
    for _ in 0..2 {
        drop(infer(&checker, &Arc::new(Expr::prop())));
    }
    assert_eq!(checker.infer_arc_memo.borrow().len(), 2);
    assert_bound(&checker, usize::MAX);
}

#[test]
fn lowering_capacity_clears_inference_windows_and_readmits_with_new_bound() {
    let env = Environment::new();
    let mut checker = TypeChecker::new(&env);
    checker.set_max_cache_entries(4);
    // Keep a real inference frame without an outstanding immutable guard so
    // the public &mut setter can be exercised between completed child calls.
    checker.infer_memo_depth.set(1);
    checker.cert_retained.set(true);
    let nodes: Vec<_> = (0..4).map(|_| Arc::new(Expr::prop())).collect();
    for node in &nodes {
        drop(infer(&checker, node));
    }
    assert_eq!(checker.infer_arc_memo.borrow().len(), 4);
    checker.set_max_cache_entries(1);
    assert!(checker.infer_arc_memo.borrow().is_empty());
    drop(infer(&checker, &nodes[0]));
    assert_bound(&checker, 1);
    checker.set_max_cache_entries(0);
    assert!(checker.infer_arc_memo.borrow().is_empty());
    drop(infer(&checker, &nodes[0]));
    assert_bound(&checker, 0);
    checker.infer_memo_depth.set(0);
    checker.cert_retained.set(false);
}

#[test]
fn explicit_admission_capacity_reduction_cannot_leave_oversized_windows() {
    let env = Environment::new();
    let mut checker = TypeChecker::new(&env);
    checker.set_max_cache_entries(4);
    let _frame = MemoFrame::new(&checker, true);
    let nodes: Vec<_> = (0..4).map(|_| Arc::new(Expr::prop())).collect();
    for node in &nodes {
        drop(infer(&checker, node));
    }
    let key = checker.infer_arc_memo_key(&nodes[0]);
    let mut memo = checker.infer_arc_memo.borrow_mut();
    let previously_inferred = memo.get(&key).expect("actual previous result").clone();
    memo.insert_if_absent_with(key, 1, || previously_inferred);
    assert_eq!(memo.len(), 1);
    assert!(memo.contains_key(&key));
    memo.insert_if_absent_with(key, 0, || panic!("disabled admission"));
    assert!(memo.is_empty());
}

#[test]
fn explicit_admission_shrink_at_equal_total_cannot_demote_an_oversized_window() {
    let env = Environment::new();
    let mut checker = TypeChecker::new(&env);
    checker.set_max_cache_entries(10);
    let _frame = MemoFrame::new(&checker, true);
    for _ in 0..5 {
        drop(infer(&checker, &Arc::new(Expr::prop())));
    }
    assert_eq!(checker.infer_arc_memo.borrow().current.len, 5);
    // Derive the new entry independently so the explicit admission API, rather
    // than the checker's unchanged cap=10, receives the first reduced cap=5.
    let node = Arc::new(Expr::prop());
    let (ty, cert) = TypeChecker::new(&env)
        .infer_type_with_cert(&node)
        .expect("independently derived new entry");
    let key = checker.infer_arc_memo_key(&node);
    checker
        .infer_arc_memo
        .borrow_mut()
        .insert_if_absent_with(key, 5, || (node.clone(), ty, Some(Arc::new(cert))));
    assert!(checker.infer_arc_memo.borrow().contains_key(&key));
    assert_bound(&checker, 5);
}

#[test]
fn previous_hits_keep_exact_certificate_but_do_not_promote_hot_entries() {
    let env = Environment::new();
    let mut checker = TypeChecker::new(&env);
    checker.set_max_cache_entries(4);
    let _frame = MemoFrame::new(&checker, true);
    let nodes: Vec<_> = (0..5).map(|_| Arc::new(Expr::prop())).collect();
    let first = infer(&checker, &nodes[0]);
    drop(infer(&checker, &nodes[1]));
    drop(infer(&checker, &nodes[2]));
    let key = checker.infer_arc_memo_key(&nodes[0]);
    assert!(checker.infer_arc_memo.borrow().previous.get(&key).is_some());
    for _ in 0..8 {
        assert!(Arc::ptr_eq(&first, &infer(&checker, &nodes[0])));
    }
    drop(infer(&checker, &nodes[3]));
    assert!(Arc::ptr_eq(&first, &infer(&checker, &nodes[0])));
    drop(infer(&checker, &nodes[4]));
    assert!(!checker.infer_arc_memo.borrow().contains_key(&key));
    let recomputed = infer(&checker, &nodes[0]);
    assert!(!Arc::ptr_eq(&first, &recomputed));
    assert!(Arc::ptr_eq(&recomputed, &infer(&checker, &nodes[0])));
    assert_eq!(
        CertVerifier::new(&env)
            .verify(&first, &nodes[0])
            .expect("old owner replay"),
        Expr::type_()
    );
    assert_bound(&checker, 4);
}

#[test]
fn sliding_working_set_reuses_recent_nodes_after_old_window_eviction() {
    let env = Environment::new();
    let mut checker = TypeChecker::new(&env);
    checker.set_max_cache_entries(4);
    let _frame = MemoFrame::new(&checker, true);
    let nodes: Vec<_> = (0..7).map(|_| Arc::new(Expr::prop())).collect();
    let certs: Vec<_> = nodes[..6]
        .iter()
        .map(|node| infer(&checker, node))
        .collect();
    for index in 2..6 {
        assert!(Arc::ptr_eq(&certs[index], &infer(&checker, &nodes[index])));
    }
    drop(infer(&checker, &nodes[6]));
    for index in 4..6 {
        assert!(Arc::ptr_eq(&certs[index], &infer(&checker, &nodes[index])));
    }
    for node in &nodes[..4] {
        assert!(!checker
            .infer_arc_memo
            .borrow()
            .contains_key(&checker.infer_arc_memo_key(node)));
    }
    assert_bound(&checker, 4);
}

#[test]
fn rotation_releases_evicted_input_and_certificate_owners() {
    let env = Environment::new();
    let mut checker = TypeChecker::new(&env);
    checker.set_max_cache_entries(2);
    let _frame = MemoFrame::new(&checker, true);
    let first = Arc::new(Expr::prop());
    let first_cert = infer(&checker, &first);
    let input_weak = Arc::downgrade(&first);
    let cert_weak = Arc::downgrade(&first_cert);
    drop(first);
    drop(first_cert);
    drop(infer(&checker, &Arc::new(Expr::prop())));
    assert!(input_weak.upgrade().is_some());
    assert!(cert_weak.upgrade().is_some());
    let newest = Arc::new(Expr::prop());
    let newest_cert = infer(&checker, &newest);
    assert!(input_weak.upgrade().is_none());
    assert!(cert_weak.upgrade().is_none());
    assert_eq!(
        CertVerifier::new(&env)
            .verify(&newest_cert, &newest)
            .expect("surviving replay"),
        Expr::type_()
    );
    assert_bound(&checker, 2);
}

#[test]
fn full_previous_window_type_only_entry_upgrades_before_eviction() {
    let env = Environment::new();
    let mut checker = TypeChecker::new(&env);
    checker.set_max_cache_entries(3);
    let _frame = MemoFrame::new(&checker, false);
    let nodes: Vec<_> = (0..3).map(|_| Arc::new(Expr::prop())).collect();
    for node in &nodes {
        drop(infer(&checker, node));
    }
    let key = checker.infer_arc_memo_key(&nodes[0]);
    {
        let memo = checker.infer_arc_memo.borrow();
        assert_eq!((memo.current.len, memo.previous.len), (1, 2));
        assert!(memo
            .previous
            .get(&key)
            .expect("previous type-only entry")
            .2
            .is_none());
    }
    checker.cert_retained.set(true);
    let cert = infer(&checker, &nodes[0]);
    {
        let mut memo = checker.infer_arc_memo.borrow_mut();
        assert_eq!((memo.current.len, memo.previous.len), (1, 2));
        let entry = memo.previous.get(&key).expect("upgraded in place");
        assert!(Arc::ptr_eq(&entry.0, &nodes[0]));
        assert!(Arc::ptr_eq(
            entry.2.as_ref().expect("real certificate"),
            &cert
        ));
        // Simulates only admission after a recursive fill, not an inferred
        // value: the closure must never run or downgrade the existing entry.
        memo.insert_if_absent_with(key, 3, || panic!("existing certificate must win"));
        assert_eq!((memo.current.len, memo.previous.len), (1, 2));
    }
    assert!(Arc::ptr_eq(&cert, &infer(&checker, &nodes[0])));
    assert_eq!(
        CertVerifier::new(&env)
            .verify(&cert, &nodes[0])
            .expect("upgraded replay"),
        Expr::type_()
    );
    assert_bound(&checker, 3);
}

#[test]
fn retirement_removes_scope_from_both_windows_without_evicting_live_prefix() {
    let env = Environment::new();
    let mut checker = TypeChecker::new(&env);
    checker.set_max_cache_entries(4);
    let _frame = MemoFrame::new(&checker, true);
    let outer = checker.ctx_push(Name::anon(), Expr::prop(), BinderInfo::Default);
    let outer_node = Arc::new(Expr::prop());
    let outer_cert = infer(&checker, &outer_node);
    let outer_key = checker.infer_arc_memo_key(&outer_node);
    let inner = checker.ctx_push(Name::anon(), Expr::prop(), BinderInfo::Default);
    let mut owners = vec![];
    for _ in 0..3 {
        let node = Arc::new(Expr::prop());
        owners.push(Arc::downgrade(&node));
        drop(infer(&checker, &node));
    }
    {
        let memo = checker.infer_arc_memo.borrow();
        assert!(memo
            .current
            .buckets
            .contains_key(&InferArcMemoScope::Prefix(inner)));
        assert!(memo
            .previous
            .buckets
            .contains_key(&InferArcMemoScope::Prefix(inner)));
    }
    assert!(owners.iter().all(|weak| weak.upgrade().is_some()));
    checker.ctx_pop();
    assert!(owners.iter().all(|weak| weak.upgrade().is_none()));
    assert_eq!(checker.infer_arc_memo.borrow().len(), 1);
    assert!(checker
        .infer_arc_memo
        .borrow()
        .previous
        .get(&outer_key)
        .is_some());
    assert!(Arc::ptr_eq(&outer_cert, &infer(&checker, &outer_node)));
    assert!(
        matches!(checker.infer_type_with_cert_arc(&Arc::new(Expr::fvar(inner))), Err(TypeError::UnknownFVar(id)) if id == inner)
    );
    assert_eq!(checker.infer_arc_memo.borrow().len(), 1);
    checker.ctx_pop();
    assert_eq!(checker.ctx_len(), 0);
    assert_ne!(outer, inner);
    assert!(checker.infer_arc_memo.borrow().is_empty());
}

#[test]
fn clear_releases_both_windows_but_external_certificates_still_replay() {
    let env = Environment::new();
    let mut checker = TypeChecker::new(&env);
    checker.set_max_cache_entries(2);
    let _frame = MemoFrame::new(&checker, true);
    let mut owners = vec![];
    let mut certs = vec![];
    for _ in 0..2 {
        let node = Arc::new(Expr::prop());
        owners.push(Arc::downgrade(&node));
        certs.push(infer(&checker, &node));
    }
    assert_eq!(checker.infer_arc_memo.borrow().current.len, 1);
    assert_eq!(checker.infer_arc_memo.borrow().previous.len, 1);
    assert!(owners.iter().all(|weak| weak.upgrade().is_some()));
    checker.infer_arc_memo.borrow_mut().clear();
    assert!(checker.infer_arc_memo.borrow().is_empty());
    assert!(owners.iter().all(|weak| weak.upgrade().is_none()));
    for cert in certs {
        assert_eq!(
            CertVerifier::new(&env)
                .verify(&cert, &Expr::prop())
                .expect("external replay"),
            Expr::type_()
        );
    }
}

#[test]
fn immediate_inference_error_does_not_rotate_full_windows() {
    let env = Environment::new();
    let mut checker = TypeChecker::new(&env);
    checker.set_max_cache_entries(2);
    let _frame = MemoFrame::new(&checker, true);
    let nodes: Vec<_> = (0..2).map(|_| Arc::new(Expr::prop())).collect();
    let certs: Vec<_> = nodes.iter().map(|node| infer(&checker, node)).collect();
    assert!(matches!(
        checker.infer_type_with_cert_arc(&Arc::new(Expr::bvar(0))),
        Err(TypeError::UnboundVariable(0))
    ));
    assert_eq!(checker.infer_arc_memo.borrow().current.len, 1);
    assert_eq!(checker.infer_arc_memo.borrow().previous.len, 1);
    for (node, cert) in nodes.iter().zip(certs) {
        assert!(Arc::ptr_eq(&cert, &infer(&checker, node)));
    }
}

#[test]
fn previous_infer_only_entry_cannot_satisfy_strict_check() {
    let env = Environment::new();
    let mut checker = TypeChecker::new(&env);
    checker.set_max_cache_entries(16);
    let _frame = MemoFrame::new(&checker, false);
    let bad = Arc::new(Expr::app(
        Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0)),
        Expr::prop(),
    ));
    assert_eq!(
        checker
            .infer_type_with_cert_arc(&bad)
            .expect("infer-only result")
            .0,
        Expr::prop()
    );
    let permissive = checker.infer_arc_memo_key(&bad);
    while checker.infer_arc_memo.borrow().current.len < 8 {
        drop(infer(&checker, &Arc::new(Expr::prop())));
    }
    drop(infer(&checker, &Arc::new(Expr::prop())));
    assert!(checker
        .infer_arc_memo
        .borrow()
        .previous
        .get(&permissive)
        .is_some());
    checker.infer_only.set(false);
    checker.cert_retained.set(true);
    let strict = checker.infer_arc_memo_key(&bad);
    assert_ne!(strict, permissive);
    assert!(matches!(
        checker.infer_type_with_cert_arc(&bad),
        Err(TypeError::TypeMismatch { .. })
    ));
    assert!(!checker.infer_arc_memo.borrow().contains_key(&strict));
    assert_bound(&checker, 16);
}

#[test]
#[cfg(feature = "inference-stats")]
fn actual_window_counters_distinguish_eviction_from_hits_and_clear() {
    use crate::tc::reduction_stats::inference::{inference_stats_reset, inference_stats_snapshot};
    let env = Environment::new();
    let mut checker = TypeChecker::new(&env);
    checker.set_max_cache_entries(4);
    let _frame = MemoFrame::new(&checker, true);
    inference_stats_reset();
    let nodes: Vec<_> = (0..5).map(|_| Arc::new(Expr::prop())).collect();
    for node in &nodes {
        drop(infer(&checker, node));
    }
    let counts = inference_stats_snapshot().expect("enabled counters");
    assert_eq!(counts.arc_rotations, 2);
    assert_eq!(counts.arc_evicted_entries, 2);
    assert_eq!(counts.arc_peak_entries, 4);
    drop(infer(&checker, &nodes[4]));
    checker.infer_arc_memo.borrow_mut().clear();
    let after = inference_stats_snapshot().expect("enabled counters");
    assert_eq!(after.arc_rotations, counts.arc_rotations);
    assert_eq!(after.arc_evicted_entries, counts.arc_evicted_entries);
    inference_stats_reset();
}
