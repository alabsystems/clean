// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Exact-prefix lifetime controls, using only genuinely inferred memo entries.

use super::*;
use crate::cert::CertVerifier;
use crate::{BinderInfo, Environment, Name, TypeError};

struct MemoFrame<'tc, 'env>(&'tc TypeChecker<'env>);

impl<'tc, 'env> MemoFrame<'tc, 'env> {
    fn new(checker: &'tc TypeChecker<'env>) -> Self {
        assert_eq!(checker.infer_memo_depth.replace(1), 0);
        assert!(!checker.cert_retained.replace(true));
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

fn infer(checker: &TypeChecker<'_>, node: &Arc<Expr>) -> (Expr, ProofCert) {
    checker
        .infer_type_with_cert_arc(node)
        .map(|(ty, cert)| (ty, cert.as_ref().clone()))
        .expect("actual retained child inference")
}

#[test]
fn scoped_retirement_releases_unreachable_owners_and_preserves_outer_bucket() {
    let env = Environment::new();
    let checker = TypeChecker::new(&env);
    let _frame = MemoFrame::new(&checker);
    let outer = checker.ctx_push(Name::anon(), Expr::prop(), BinderInfo::Default);
    let outer_node = Arc::new(Expr::prop());
    let outer_weak = Arc::downgrade(&outer_node);
    let outer_key = checker.infer_arc_memo_key(&outer_node);
    drop(infer(&checker, &outer_node));
    drop(outer_node);

    let inner = checker.ctx_push(Name::anon(), Expr::prop(), BinderInfo::Default);
    let input = Arc::new(Expr::app(
        Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0)),
        Expr::prop(),
    ));
    let input_weak = Arc::downgrade(&input);
    let key = checker.infer_arc_memo_key(&input);
    let result = infer(&checker, &input);
    let cert_weak = {
        let memo = checker.infer_arc_memo.borrow();
        let ProofCert::App { fn_cert, .. } = memo[&key].2.as_deref().expect("real certificate")
        else {
            panic!("application certificate");
        };
        Arc::downgrade(fn_cert)
    };
    drop(result);
    drop(input);
    assert!(input_weak.upgrade().is_some());
    assert!(cert_weak.upgrade().is_some());
    assert!(checker
        .infer_arc_memo
        .borrow()
        .current
        .buckets
        .contains_key(&InferArcMemoScope::Prefix(inner)));

    checker.ctx_pop();
    assert!(
        input_weak.upgrade().is_none(),
        "retired input owner released"
    );
    assert!(
        cert_weak.upgrade().is_none(),
        "retired raw certificate released"
    );
    let restored = outer_weak.upgrade().expect("active outer owner retained");
    assert_eq!(checker.infer_arc_memo_key(&restored), outer_key);
    assert!(checker.infer_arc_memo.borrow().contains_key(&outer_key));
    assert_eq!(infer(&checker, &restored).0, Expr::type_());
    assert_eq!(checker.infer_arc_memo.borrow().current.buckets.len(), 1);
    assert!(checker.infer_arc_memo.borrow().previous.buckets.is_empty());
    assert!(checker
        .infer_arc_memo
        .borrow()
        .current
        .buckets
        .contains_key(&InferArcMemoScope::Prefix(outer)));
    drop(restored);
    checker.ctx_pop();
    assert!(outer_weak.upgrade().is_none());
    assert!(checker.infer_arc_memo.borrow().is_empty());
}

#[test]
fn scoped_retirement_recovers_aggregate_capacity_after_window_eviction() {
    for capacity in [0, 2] {
        let env = Environment::new();
        let mut checker = TypeChecker::new(&env);
        checker.set_max_cache_entries(capacity);
        let _frame = MemoFrame::new(&checker);
        let outer = Arc::new(Expr::prop());
        let inner = Arc::new(Expr::prop());
        let later = Arc::new(Expr::prop());
        drop(infer(&checker, &outer));
        checker.ctx_push(Name::anon(), Expr::prop(), BinderInfo::Default);
        drop(infer(&checker, &inner));
        assert_eq!(checker.infer_arc_memo.borrow().len(), capacity);
        let later_inner_key = checker.infer_arc_memo_key(&later);
        assert_eq!(infer(&checker, &later).0, Expr::type_());
        assert_eq!(
            checker
                .infer_arc_memo
                .borrow()
                .contains_key(&later_inner_key),
            capacity != 0,
            "positive capacity admits the later completed node"
        );
        checker.ctx_pop();
        // At cap=2, admitting `later` evicted the old outer window. Both
        // surviving entries then belonged to the now-retired inner scope.
        assert!(checker.infer_arc_memo.borrow().is_empty());
        let (ty, cert) = infer(&checker, &later);
        assert_eq!(ty, Expr::type_());
        assert_eq!(
            checker.infer_arc_memo.borrow().len(),
            usize::from(capacity != 0)
        );
        assert_eq!(
            checker
                .infer_arc_memo
                .borrow()
                .contains_key(&checker.infer_arc_memo_key(&later)),
            capacity != 0
        );
        assert_eq!(
            CertVerifier::new(&env)
                .verify(&cert, &later)
                .expect("real replay"),
            ty
        );
    }
}

#[test]
fn scoped_retirement_truncates_exact_nonmonotonic_ids_and_keeps_empty_prefix() {
    let env = Environment::new();
    let checker = TypeChecker::new(&env);
    let _frame = MemoFrame::new(&checker);
    let shared = Arc::new(Expr::prop());
    drop(infer(&checker, &shared));
    let empty_key = checker.infer_arc_memo_key(&shared);
    // Exact stack order, deliberately unlike numeric ID order. FVar0 must not
    // alias the empty prefix. Explicit IDs use the real no-reuse guard.
    let mut keys = vec![];
    for id in [FVarId(9), FVarId(0), FVarId(4)] {
        checker
            .ctx_mut()
            .push_with_id(id, Name::anon(), Expr::prop(), BinderInfo::Default);
        drop(infer(&checker, &shared));
        keys.push(checker.infer_arc_memo_key(&shared));
    }
    assert_eq!(checker.infer_arc_memo.borrow().len(), 4);
    {
        // A no-op must not even request mutable access to either structure.
        let _ctx = checker.local_context();
        let _memo = checker.infer_arc_memo.borrow();
        checker.ctx_truncate_to(3);
    }
    assert_eq!(
        checker.infer_arc_memo.borrow().len(),
        4,
        "no-op keeps every bucket"
    );
    checker.ctx_truncate_to(1);
    assert_eq!(checker.ctx_len(), 1);
    let memo = checker.infer_arc_memo.borrow();
    assert_eq!(memo.len(), 2);
    assert!(memo.contains_key(&empty_key));
    assert!(memo.contains_key(&keys[0]));
    assert!(!memo.contains_key(&keys[1]));
    assert!(!memo.contains_key(&keys[2]));
    drop(memo);
    checker.reset_local_context();
    checker.ctx_pop();
    assert_eq!(checker.ctx_len(), 0);
    assert_eq!(checker.infer_arc_memo.borrow().len(), 1);
    assert!(checker.infer_arc_memo.borrow().contains_key(&empty_key));
}

#[test]
fn scoped_retirement_context_replacement_clears_every_old_namespace() {
    let env = Environment::new();
    let mut checker = TypeChecker::new(&env);
    checker.infer_memo_depth.set(1);
    checker.cert_retained.set(true);
    let closed = Arc::new(Expr::prop());
    let closed_weak = Arc::downgrade(&closed);
    drop(infer(&checker, &closed));
    drop(closed);
    let id = checker.ctx_push(Name::anon(), Expr::prop(), BinderInfo::Default);
    let shared = Arc::new(Expr::fvar(id));
    assert_eq!(infer(&checker, &shared).0, Expr::prop());
    assert_eq!(checker.infer_arc_memo.borrow().len(), 2);
    {
        let ctx = checker.local_context_mut();
        assert_eq!(ctx.pop().expect("old local").id, id);
        ctx.push_with_id(id, Name::anon(), Expr::type_(), BinderInfo::Default);
    }
    assert!(checker.infer_arc_memo.borrow().is_empty());
    assert!(closed_weak.upgrade().is_none());
    assert_eq!(
        infer(&checker, &shared).0,
        Expr::type_(),
        "new namespace, no stale type"
    );
    checker.ctx_pop();
    assert!(matches!(
        checker.infer_type_with_cert_arc(&shared),
        Err(TypeError::UnknownFVar(missing)) if missing == id
    ));
    assert!(checker.infer_arc_memo.borrow().is_empty());
    checker.infer_memo_depth.set(0);
    checker.cert_retained.set(false);
}

#[test]
fn scoped_retirement_error_cleanup_and_retained_certificate_replay() {
    let env = Environment::new();
    let checker = TypeChecker::new(&env);
    let frame = MemoFrame::new(&checker);
    let outer = checker.ctx_push(Name::anon(), Expr::prop(), BinderInfo::Default);
    let shared = Arc::new(Expr::prop());
    drop(infer(&checker, &shared));
    let outer_key = checker.infer_arc_memo_key(&shared);
    let bad = Expr::lam(
        BinderInfo::Default,
        Expr::prop(),
        Expr::app(Expr::prop(), Expr::prop()),
    );
    assert!(matches!(
        checker.infer_type_with_cert(&bad),
        Err(TypeError::NotAFunction { .. })
    ));
    assert_eq!(checker.ctx_len(), 1);
    assert_eq!(checker.infer_arc_memo.borrow().len(), 1);
    assert!(checker.infer_arc_memo.borrow().contains_key(&outer_key));

    let good = Expr::lam(
        BinderInfo::Default,
        Expr::type_(),
        Expr::lam(
            BinderInfo::Default,
            Expr::bvar(0),
            Expr::let_named(
                Name::anon(),
                Expr::bvar(1),
                Expr::bvar(0),
                Expr::bvar(0),
                false,
            ),
        ),
    );
    let (ty, cert) = checker
        .infer_type_with_cert(&good)
        .expect("dependent Lam/Let");
    let expected = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
    );
    assert_eq!(ty, expected);
    assert_eq!(checker.ctx_len(), 1);
    assert!(checker
        .infer_arc_memo
        .borrow()
        .current
        .buckets
        .keys()
        .all(|key| *key == InferArcMemoScope::Prefix(outer)));
    assert!(checker.infer_arc_memo.borrow().previous.buckets.is_empty());
    checker.ctx_pop();
    drop(frame);
    assert!(checker.infer_arc_memo.borrow().is_empty());
    assert_eq!(
        CertVerifier::new(&env)
            .verify(&cert, &good)
            .expect("returned certificate survives retirement"),
        expected
    );
}
