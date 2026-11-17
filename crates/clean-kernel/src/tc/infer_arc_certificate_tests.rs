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

#[cfg(debug_assertions)]
#[test]
fn discarded_debug_public_inference_does_not_retain_unused_child_certificates() {
    let env = Environment::new();
    let checker = TypeChecker::new(&env);
    let frame = MemoFrame::new(&checker, false);
    let shared = diamond(12);
    let term = Expr::app_arc(
        Arc::new(Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0))),
        shared.clone(),
    );
    assert_eq!(
        checker.infer_type(&term).expect("ordinary inference"),
        Expr::type_()
    );
    let key = checker.infer_arc_memo_key(&shared);
    assert!(
        checker.infer_arc_memo.borrow()[&key].2.is_none(),
        "plain debug infer_type retained an unused child certificate"
    );
    assert!(!checker.cert_retained.get());
    drop(frame);
    assert_clean(&checker);
    let (ty, cert) = checker
        .infer_type_with_cert(&term)
        .expect("actual retained inference");
    assert_eq!(ty, Expr::type_());
    assert_eq!(
        CertVerifier::new(&env)
            .verify(&cert, &term)
            .expect("retained replay"),
        ty
    );
}

#[cfg(debug_assertions)]
#[test]
fn discarded_debug_warm_memo_keeps_strict_children_and_full_mode_refusals() {
    let env = Environment::new();
    for bad in [
        Expr::app(
            Expr::lam(BinderInfo::Default, Expr::prop(), Expr::prop()),
            Expr::bvar(0),
        ),
        Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::prop()),
        Expr::let_named(
            Name::from_string("x"),
            Expr::bvar(0),
            Expr::prop(),
            Expr::prop(),
            false,
        ),
        Expr::let_named(
            Name::from_string("x"),
            Expr::type_(),
            Expr::bvar(0),
            Expr::prop(),
            false,
        ),
    ] {
        let checker = TypeChecker::new(&env);
        let frame = MemoFrame::new(&checker, false);
        assert_eq!(
            checker
                .infer_type(&diamond(3))
                .expect("warm ordinary inference"),
            Expr::type_()
        );
        let result = checker.infer_type(&bad);
        assert!(
            matches!(result, Err(TypeError::UnboundVariable(0))),
            "{result:?}"
        );
        assert!(!checker.cert_retained.get());
        drop(frame);
        assert_clean(&checker);
    }
    // Infer-only still has its documented weaker ascription contract. A real
    // entry derived there must never answer a later full-mode request.
    let checker = TypeChecker::new(&env);
    let frame = MemoFrame::new(&checker, false);
    let bad = Arc::new(Expr::app(
        Expr::lam(BinderInfo::Default, Expr::prop(), Expr::prop()),
        Expr::type_(),
    ));
    let term = Expr::app_arc(
        Arc::new(Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0))),
        bad.clone(),
    );
    assert_eq!(
        checker
            .infer_type(&term)
            .expect("infer-only ascription is not a full check"),
        Expr::type_()
    );
    let key = checker.infer_arc_memo_key(&bad);
    assert!(checker.infer_arc_memo.borrow()[&key].2.is_none());
    assert!(matches!(
        checker.infer_type_full(&term),
        Err(TypeError::TypeMismatch { .. })
    ));
    assert!(matches!(
        checker.infer_type_with_cert_full(&term),
        Err(TypeError::TypeMismatch { .. })
    ));
    assert!(!checker.cert_retained.get());
    drop(frame);
    assert_clean(&checker);
}

#[cfg(debug_assertions)]
#[test]
fn discarded_debug_configured_trace_keeps_real_certificates() {
    use crate::cert::trace::{NullCollector, ThreadedCollector, TraceCollector, TraceEntry};
    let env = Environment::new();
    for enabled in [false, true] {
        let collector: Arc<dyn TraceCollector> = if enabled {
            Arc::new(ThreadedCollector::new())
        } else {
            Arc::new(NullCollector)
        };
        let mut checker = TypeChecker::new(&env);
        checker.set_trace_collector(Some(collector.clone()));
        let frame = MemoFrame::new(&checker, false);
        let shared = diamond(4);
        let term = Expr::app_arc(
            Arc::new(Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0))),
            shared.clone(),
        );
        assert_eq!(
            checker.infer_type(&term).expect("trace inference"),
            Expr::type_()
        );
        let key = checker.infer_arc_memo_key(&shared);
        let cert = checker.infer_arc_memo.borrow()[&key]
            .2
            .clone()
            .expect("configured trace retains real cert");
        assert_eq!(
            CertVerifier::new(&env)
                .verify(&cert, &shared)
                .expect("real trace child"),
            Expr::type_()
        );
        let entries = collector.flush();
        if enabled {
            let root_hash = crate::cert::trace::expr_hash(&term);
            let proof = entries
                .iter()
                .find_map(|entry| match entry {
                    TraceEntry::Infer { expr_hash, cert } if *expr_hash == root_hash => Some(cert),
                    _ => None,
                })
                .expect("actual root trace");
            assert_eq!(
                CertVerifier::new(&env)
                    .verify(proof, &term)
                    .expect("root trace replay"),
                Expr::type_()
            );
        } else {
            assert!(entries.is_empty());
        }
        drop(frame);
        assert_clean(&checker);
    }
}

#[cfg(not(debug_assertions))]
#[test]
fn discarded_release_warm_weaker_memo_never_answers_retained_children() {
    let env = Environment::new();
    // These fixtures deliberately violate scope. Release infer-only can skip
    // these children; retained inference must still visit and reject them.
    for bad in [
        Expr::app(
            Expr::lam(BinderInfo::Default, Expr::prop(), Expr::prop()),
            Expr::bvar(0),
        ),
        Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::prop()),
        Expr::let_named(
            Name::from_string("x"),
            Expr::bvar(0),
            Expr::prop(),
            Expr::prop(),
            false,
        ),
        Expr::let_named(
            Name::from_string("x"),
            Expr::type_(),
            Expr::bvar(0),
            Expr::prop(),
            false,
        ),
    ] {
        let checker = TypeChecker::new(&env);
        let frame = MemoFrame::new(&checker, false);
        let bad = Arc::new(bad);
        let _warm_type = checker
            .infer_type_fast_arc(&bad)
            .expect("actual weaker fast producer");
        let key = checker.infer_arc_memo_key(&bad);
        assert!(checker.infer_arc_memo.borrow()[&key].2.is_none());
        let term = Expr::app_arc(
            Arc::new(Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0))),
            bad,
        );
        assert!(matches!(
            checker.infer_type_with_cert(&term),
            Err(TypeError::UnboundVariable(0))
        ));
        assert!(matches!(
            checker.infer_type_with_cert_full(&term),
            Err(TypeError::UnboundVariable(0))
        ));
        assert!(!checker.cert_retained.get());
        drop(frame);
        assert_clean(&checker);
    }
}

#[cfg(debug_assertions)]
#[test]
fn discarded_debug_nested_retained_and_full_certificate_consumers_keep_real_output() {
    let env = Environment::new();
    for (retained, full) in [(true, false), (false, true)] {
        let checker = TypeChecker::new(&env);
        let frame = MemoFrame::new(&checker, retained);
        let shared = diamond(4);
        let term = Expr::app_arc(
            Arc::new(Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0))),
            shared.clone(),
        );
        let ty = if full {
            checker.infer_type_full(&term)
        } else {
            checker.infer_type(&term)
        }
        .expect("nested/full inference");
        assert_eq!(ty, Expr::type_());
        assert_eq!(checker.cert_retained.get(), retained);
        assert!(checker.infer_only.get());
        let previous = checker.infer_only.replace(!full);
        let key = checker.infer_arc_memo_key(&shared);
        checker.infer_only.set(previous);
        if full {
            assert!(
                checker.infer_arc_memo.borrow()[&key].2.is_none(),
                "Expr-only full checking keeps types, not unused certificates"
            );
            let (full_ty, full_cert) = checker
                .infer_type_with_cert_full(&term)
                .expect("explicit full certificate consumer");
            assert_eq!(
                CertVerifier::new(&env)
                    .verify(&full_cert, &term)
                    .expect("full root replay"),
                full_ty
            );
        }
        let cert = checker.infer_arc_memo.borrow()[&key]
            .2
            .clone()
            .expect("retained/full certificate consumer must retain real output");
        assert_eq!(
            CertVerifier::new(&env)
                .verify(&cert, &shared)
                .expect("nested/full certificate replay"),
            Expr::type_()
        );
        drop(frame);
        assert_clean(&checker);
    }
}

#[cfg(debug_assertions)]
#[test]
fn discarded_debug_full_query_drops_output_and_upgrades_full_consumers() {
    let env = Environment::new();
    let checker = TypeChecker::new(&env);
    let frame = MemoFrame::new(&checker, false);
    let shared = diamond(12);
    let term = Expr::app_arc(
        Arc::new(Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0))),
        shared.clone(),
    );
    assert_eq!(
        checker.infer_type_full(&term).expect("full type query"),
        Expr::type_()
    );
    assert!(!checker.cert_retained.get());
    assert!(checker.infer_only.get());
    let previous = checker.infer_only.replace(false);
    let key = checker.infer_arc_memo_key(&shared);
    checker.infer_only.set(previous);
    assert!(
        checker.infer_arc_memo.borrow()[&key].2.is_none(),
        "full type-only query retained an unused child certificate"
    );

    // The private full-mode consumer has no retained flag to mask a leaked
    // discard scope. It must still upgrade and return a genuine certificate.
    let previous = checker.infer_only.replace(false);
    let (private_ty, private_cert) = checker
        .infer_type_with_cert_arc(&shared)
        .expect("private full certificate consumer after Expr-only query");
    checker.infer_only.set(previous);
    assert_eq!(private_ty, Expr::type_());
    assert_eq!(
        CertVerifier::new(&env)
            .verify(&private_cert, &shared)
            .expect("private full output survives independent verification"),
        private_ty
    );

    // A later explicit full certificate consumer must upgrade the genuinely
    // checked None entry and return a complete certificate for independent replay.
    let (ty, cert) = checker
        .infer_type_with_cert_full(&term)
        .expect("retained full certificate after type-only warmup");
    assert_eq!(ty, Expr::type_());
    assert_eq!(
        CertVerifier::new(&env)
            .verify(&cert, &term)
            .expect("full root certificate replay"),
        ty
    );
    let child = checker.infer_arc_memo.borrow()[&key]
        .2
        .clone()
        .expect("full consumer upgraded actual None entry");
    assert_eq!(
        CertVerifier::new(&env)
            .verify(&child, &shared)
            .expect("upgraded shared child replay"),
        Expr::type_()
    );
    drop(frame);
    assert_clean(&checker);
}

#[cfg(debug_assertions)]
#[test]
fn discarded_debug_full_scope_preserves_refusals_and_restores_after_errors() {
    let env = Environment::new();
    for bad in [
        Expr::app(
            Expr::lam(BinderInfo::Default, Expr::prop(), Expr::prop()),
            Expr::bvar(0),
        ),
        Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::prop()),
        Expr::let_named(
            Name::from_string("x"),
            Expr::bvar(0),
            Expr::prop(),
            Expr::prop(),
            false,
        ),
        Expr::let_named(
            Name::from_string("x"),
            Expr::type_(),
            Expr::bvar(0),
            Expr::prop(),
            false,
        ),
    ] {
        let checker = TypeChecker::new(&env);
        checker
            .infer_type_full(&diamond(3))
            .expect("strict full warmup");
        assert!(matches!(
            checker.infer_type_full(&bad),
            Err(TypeError::UnboundVariable(0))
        ));
        assert!(!checker.cert_output_discarded.get());
        assert!(!checker.cert_retained.get());
        assert!(checker.infer_only.get());
        assert_clean(&checker);
        let term = diamond(3);
        let (ty, cert) = checker
            .infer_type_with_cert_full(&term)
            .expect("retained full inference after an error");
        assert_eq!(
            CertVerifier::new(&env)
                .verify(&cert, &term)
                .expect("real certificate after refused full query"),
            ty
        );
        assert!(!checker.cert_output_discarded.get());
        assert_clean(&checker);
    }
}
