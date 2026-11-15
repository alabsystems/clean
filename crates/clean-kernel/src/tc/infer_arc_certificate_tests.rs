// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Retained certificate DAGs, through actual inference and independent replay.

use super::*;
use crate::cert::CertVerifier;
use crate::tc::expr_location::ExprPathStep;
use crate::{BinderInfo, Environment, Level, Name, TypeError};
use std::collections::HashSet;

// Keep an enclosing frame only where a test must observe a genuine child entry
// before outer-call cleanup. No certificate or memo entry is fabricated.
struct MemoFrame<'tc, 'env> {
    checker: &'tc TypeChecker<'env>,
    retained: bool,
    infer_only: bool,
}

impl<'tc, 'env> MemoFrame<'tc, 'env> {
    fn new(checker: &'tc TypeChecker<'env>, retained: bool) -> Self {
        assert_eq!(checker.infer_memo_depth.replace(1), 0);
        assert!(checker.infer_arc_memo.borrow().is_empty());
        Self {
            checker,
            retained: checker.cert_retained.replace(retained),
            infer_only: checker.infer_only.get(),
        }
    }
}

impl Drop for MemoFrame<'_, '_> {
    fn drop(&mut self) {
        self.checker.infer_memo_depth.set(0);
        self.checker.cert_retained.set(self.retained);
        self.checker.infer_only.set(self.infer_only);
        self.checker.infer_arc_memo.borrow_mut().clear();
    }
}

fn choose_type() -> Arc<Expr> {
    // (fun (A : Type) (B : Type) => A) : Type -> Type -> Type.
    Arc::new(Expr::lam(
        BinderInfo::Default,
        Expr::type_(),
        Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(1)),
    ))
}

fn diamond(depth: usize) -> Arc<Expr> {
    let choose = choose_type();
    let mut node = Arc::new(Expr::prop());
    for _ in 0..depth {
        node = Arc::new(Expr::app_arc(
            Arc::new(Expr::app_arc(choose.clone(), node.clone())),
            node,
        ));
    }
    node
}

fn repeated_arguments(cert: &ProofCert) -> (&Arc<ProofCert>, &Arc<ProofCert>) {
    let ProofCert::App {
        fn_cert,
        arg_cert: right,
        ..
    } = cert
    else {
        panic!("outer application certificate");
    };
    let ProofCert::App { arg_cert: left, .. } = fn_cert.as_ref() else {
        panic!("partial application certificate");
    };
    (left, right)
}

fn certificate_nodes(root: &ProofCert) -> usize {
    let mut seen = HashSet::new();
    let mut pending = vec![root];
    while let Some(cert) = pending.pop() {
        if !seen.insert(std::ptr::from_ref(cert)) {
            continue;
        }
        match cert {
            ProofCert::App {
                fn_cert, arg_cert, ..
            } => {
                pending.extend([fn_cert.as_ref(), arg_cert.as_ref()]);
            }
            ProofCert::Lam {
                arg_type_cert,
                body_cert,
                ..
            } => {
                pending.extend([arg_type_cert.as_ref(), body_cert.as_ref()]);
            }
            ProofCert::Sort { .. } | ProofCert::BVar { .. } => {}
            _ => panic!("unexpected certificate in this closed lambda/App fixture"),
        }
    }
    seen.len()
}

fn assert_clean(checker: &TypeChecker<'_>) {
    assert_eq!(checker.ctx_len(), 0);
    assert_eq!(checker.infer_memo_depth.get(), 0);
    assert!(!checker.cert_retained.get());
    assert!(checker.infer_arc_memo.borrow().is_empty());
    assert!(checker.expr_loc_snapshot().is_none());
}

#[test]
fn retained_arc_certificate_public_diamond_shares_and_replays_at_zero_capacity() {
    let env = Environment::new();
    let term = diamond(5);
    let mut counts = Vec::new();
    for capacity in [0, 256] {
        let mut checker = TypeChecker::new(&env);
        checker.set_max_cache_entries(capacity);
        let (ty, cert) = checker
            .infer_type_with_cert(&term)
            .expect("public retained inference");
        assert_eq!(ty, Expr::type_());
        assert_clean(&checker);
        assert_eq!(
            CertVerifier::new(&env)
                .verify(&cert, &term)
                .expect("closed replay"),
            Expr::type_()
        );
        let mut level = &cert;
        for _ in 0..5 {
            let (left, right) = repeated_arguments(level);
            assert_eq!(Arc::ptr_eq(left, right), capacity != 0);
            level = left;
        }
        counts.push(certificate_nodes(&cert));
        // Returning the public certificate must not leave a cache alive for a
        // later outer call, even while the first certificate remains retained.
        let (_, again) = checker
            .infer_type_with_cert(&term)
            .expect("second outer call");
        assert!(!Arc::ptr_eq(
            repeated_arguments(&cert).0,
            repeated_arguments(&again).0
        ));
        assert_clean(&checker);
    }
    assert!(
        counts[1] < counts[0],
        "physical certificate sharing, not a timing claim"
    );
}

#[test]
fn retained_arc_certificate_separates_modes_prefixes_and_releases_retired_owner() {
    let env = Environment::new();
    let checker = TypeChecker::new(&env);
    let frame = MemoFrame::new(&checker, true);
    let node = Arc::new(Expr::prop());
    let (_, outer) = checker
        .infer_type_with_cert_arc(&node)
        .expect("empty prefix");
    let (_, hit) = checker
        .infer_type_with_cert_arc(&node)
        .expect("same exact key");
    assert!(Arc::ptr_eq(&outer, &hit));
    drop(hit);
    checker.ctx_push(Name::anon(), Expr::prop(), BinderInfo::Default);
    let (_, inner) = checker
        .infer_type_with_cert_arc(&node)
        .expect("different prefix");
    assert!(!Arc::ptr_eq(&outer, &inner));
    let retired = Arc::downgrade(&inner);
    drop(inner);
    checker.ctx_pop();
    assert!(retired.upgrade().is_none());
    let (_, restored) = checker
        .infer_type_with_cert_arc(&node)
        .expect("restored prefix");
    assert!(Arc::ptr_eq(&outer, &restored));
    checker.infer_only.set(false);
    let (_, full) = checker
        .infer_type_with_cert_arc(&node)
        .expect("different mode");
    assert!(!Arc::ptr_eq(&outer, &full));
    checker.infer_only.set(true);
    let bad = Arc::new(Expr::app(
        Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0)),
        Expr::prop(),
    ));
    assert_eq!(
        checker
            .infer_type_with_cert_arc(&bad)
            .expect("infer-only type")
            .0,
        Expr::prop()
    );
    checker.infer_only.set(false);
    assert!(matches!(
        checker.infer_type_with_cert_arc(&bad),
        Err(TypeError::TypeMismatch { .. })
    ));
    assert!(!checker
        .infer_arc_memo
        .borrow()
        .contains_key(&checker.infer_arc_memo_key(&bad)));
    checker.infer_only.set(true);
    let id = checker.ctx_push(Name::anon(), Expr::prop(), BinderInfo::Default);
    let local = Arc::new(Expr::fvar(id));
    assert_eq!(
        checker
            .infer_type_with_cert_arc(&local)
            .expect("actual local")
            .0,
        Expr::prop()
    );
    checker.ctx_pop();
    assert!(
        matches!(checker.infer_type_with_cert_arc(&local), Err(TypeError::UnknownFVar(missing)) if missing == id)
    );
    drop(frame);
    assert_clean(&checker);
    assert_eq!(
        CertVerifier::new(&env)
            .verify(&outer, &node)
            .expect("external owner survives cleanup"),
        Expr::type_()
    );
}

#[test]
fn retained_arc_certificate_upgrades_genuine_type_only_entry_at_capacity() {
    let env = Environment::new();
    let mut checker = TypeChecker::new(&env);
    checker.set_max_cache_entries(1);
    let frame = MemoFrame::new(&checker, false);
    let shared = Arc::new(Expr::type_());
    let expected = Expr::sort(Level::succ(Level::succ(Level::zero())));
    // Both branches derive the entry. The debug discard path also stores only
    // a type; release additionally exercises the real fast-inference caller.
    #[cfg(debug_assertions)]
    assert_eq!(
        checker
            .infer_type_with_cert_arc(&shared)
            .expect("discard inference")
            .0,
        expected
    );
    #[cfg(not(debug_assertions))]
    assert_eq!(
        checker
            .infer_type_fast_arc(&shared)
            .expect("fast inference"),
        expected
    );
    let key = checker.infer_arc_memo_key(&shared);
    assert_eq!(checker.infer_arc_memo.borrow().len(), 1);
    assert!(checker.infer_arc_memo.borrow()[&key].2.is_none());
    // Upgrade the existing cap=1 entry before any other successful admission
    // can evict it. The subsequent public App independently checks recomputation
    // and retained replay across single-entry window turnover.
    checker.cert_retained.set(true);
    let (_, upgraded) = checker
        .infer_type_with_cert_arc(&shared)
        .expect("actual upgrade before eviction");
    checker.cert_retained.set(false);
    assert!(Arc::ptr_eq(
        checker.infer_arc_memo.borrow()[&key]
            .2
            .as_ref()
            .expect("upgraded entry"),
        &upgraded
    ));
    assert_eq!(checker.infer_arc_memo.borrow().len(), 1);
    let term = Expr::app_arc(
        Arc::new(Expr::lam(
            BinderInfo::Default,
            expected.clone(),
            Expr::bvar(0),
        )),
        shared,
    );
    // This public entry sets cert_retained=true even though infer_only=true.
    let (ty, cert) = checker
        .infer_type_with_cert(&term)
        .expect("retained upgrade at full capacity");
    assert_eq!(ty, expected);
    assert!(
        !checker.cert_retained.get(),
        "public entry restores its caller's mode"
    );
    let ProofCert::App { arg_cert, .. } = &cert else {
        panic!("application");
    };
    {
        let memo = checker.infer_arc_memo.borrow();
        assert_eq!(memo.len(), 1);
        let stored = memo[&key].2.as_ref().expect("real upgraded certificate");
        assert!(Arc::ptr_eq(stored, arg_cert));
        assert!(
            matches!(stored.as_ref(), ProofCert::Sort { level } if *level == Level::succ(Level::zero()))
        );
    }
    drop(frame);
    assert_clean(&checker);
    assert_eq!(
        CertVerifier::new(&env)
            .verify(&cert, &term)
            .expect("replay upgraded entry"),
        expected
    );
}

#[test]
fn retained_arc_certificate_errors_keep_breadcrumbs_budget_and_cleanup() {
    let env = Environment::new();
    for capacity in [0, 256] {
        let mut checker = TypeChecker::new(&env);
        checker.set_max_cache_entries(capacity);
        checker.infer_only.set(false);
        let bad_arg = Expr::lam(
            BinderInfo::Default,
            Expr::prop(),
            Expr::app(
                Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0)),
                Expr::prop(),
            ),
        );
        let TypeError::TypeMismatch { location, .. } = checker
            .infer_type_with_cert(&bad_arg)
            .expect_err("wrong argument type")
        else {
            panic!("type mismatch");
        };
        assert_eq!(
            location.expect("argument breadcrumb").steps,
            vec![ExprPathStep::LamBody, ExprPathStep::AppArg]
        );
        assert_clean(&checker);
        let bad_fn = Expr::lam(
            BinderInfo::Default,
            Expr::type_(),
            Expr::app(Expr::prop(), Expr::prop()),
        );
        let TypeError::NotAFunction { location, .. } = checker
            .infer_type_with_cert(&bad_fn)
            .expect_err("non-function")
        else {
            panic!("not a function");
        };
        assert_eq!(
            location.expect("function breadcrumb").steps,
            vec![ExprPathStep::LamBody, ExprPathStep::AppFn]
        );
        assert_clean(&checker);
    }
    // Own the thread-local ambient budget so assertion failure cannot poison a
    // later libtest case. A spent budget remains a refusal, never cached success.
    std::thread::spawn(|| {
        use crate::tc::decl_budget::{clear_declaration_budget, set_declaration_budget};
        let env = Environment::new();
        let checker = TypeChecker::new(&env);
        set_declaration_budget(1);
        assert!(matches!(
            checker.infer_type_with_cert(&diamond(2)),
            Err(TypeError::DeclarationBudgetExhausted { limit: 1 })
        ));
        assert_clean(&checker);
        clear_declaration_budget();
        let (ty, cert) = checker
            .infer_type_with_cert(&Expr::prop())
            .expect("later fresh inference");
        assert_eq!(ty, Expr::type_());
        assert_eq!(
            CertVerifier::new(&env)
                .verify(&cert, &Expr::prop())
                .expect("later replay"),
            ty
        );
        assert_clean(&checker);
    })
    .join()
    .expect("budget-control thread");
}

#[test]
fn retained_arc_certificate_binder_rebinding_preserves_shared_children_and_replay() {
    let env = Environment::new();
    let checker = TypeChecker::new(&env);
    // Closed children retain their input identity while opening the binder.
    // Their returned certificate must survive the popped scope and rebinding.
    let term = Expr::lam(
        BinderInfo::Default,
        Expr::type_(),
        diamond(3).as_ref().clone(),
    );
    let expected = Expr::arrow(Expr::type_(), Expr::type_());
    let (ty, cert) = checker
        .infer_type_with_cert(&term)
        .expect("closed body under binder");
    assert_eq!(ty, expected);
    assert_clean(&checker);
    let ProofCert::Lam { body_cert, .. } = &cert else {
        panic!("lambda certificate");
    };
    let (left, right) = repeated_arguments(body_cert);
    assert!(Arc::ptr_eq(left, right));
    assert_eq!(
        CertVerifier::new(&env)
            .verify(&cert, &term)
            .expect("retired closed-body replay"),
        expected
    );

    // Separately require real FVar-to-BVar rebinding and its dependent replay.
    // This does not require the upstream expression opener to intern outputs.
    let shared = Arc::new(Expr::bvar(0));
    let term = Expr::lam(
        BinderInfo::Default,
        Expr::type_(),
        Expr::app_arc(
            Arc::new(Expr::app_arc(choose_type(), shared.clone())),
            shared,
        ),
    );
    let (ty, cert) = checker
        .infer_type_with_cert(&term)
        .expect("binder inference and retirement");
    assert_eq!(ty, expected);
    assert_clean(&checker);
    let ProofCert::Lam { body_cert, .. } = &cert else {
        panic!("lambda certificate");
    };
    let (left, right) = repeated_arguments(body_cert);
    assert!(matches!(left.as_ref(), ProofCert::BVar { .. }));
    assert!(matches!(right.as_ref(), ProofCert::BVar { .. }));
    assert_eq!(
        CertVerifier::new(&env)
            .verify(&cert, &term)
            .expect("independent closed binder replay"),
        expected
    );
}
