// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Release-path Arc memo regressions. These tests are not compiled in debug
//! builds, where public inference follows the certificate-generating path.

use super::*;
use crate::cert::{CertError, CertVerifier, ProofCert};
use crate::expr::MDataMap;
use crate::tc::infer_arc_memo::InferArcMemoKey;
use std::sync::Arc;

/// Hold a test-only enclosing inference frame so that actual child dispatches
/// can be observed before the production outer-frame cleanup. No memo entries
/// are fabricated: every entry below must come from an inference call.
struct MemoFrame<'tc, 'env>(&'tc TypeChecker<'env>);

impl<'tc, 'env> MemoFrame<'tc, 'env> {
    fn new(tc: &'tc TypeChecker<'env>) -> Self {
        assert_eq!(tc.infer_memo_depth.get(), 0);
        assert!(tc.infer_arc_memo.borrow().is_empty());
        tc.infer_memo_depth.set(1);
        Self(tc)
    }
}

impl Drop for MemoFrame<'_, '_> {
    fn drop(&mut self) {
        self.0.infer_memo_depth.set(0);
        self.0.infer_arc_memo.borrow_mut().clear();
    }
}

fn mdata_arc(inner: Arc<Expr>) -> Expr {
    Expr::from_kind(ExprKind::MData(MDataMap::new(), inner))
}

fn memo_key(arc: &Arc<Expr>, infer_only: bool, last: Option<FVarId>) -> InferArcMemoKey {
    InferArcMemoKey::new(arc, infer_only, last)
}

fn bad_application() -> Arc<Expr> {
    // (fun (p : Prop) => p) Prop has an infer-only result, but its
    // argument has type Type rather than the required Prop.
    Arc::new(Expr::app(
        Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0)),
        Expr::prop(),
    ))
}

#[test]
fn fast_arc_memo_records_each_stable_child_kind() {
    let env = Environment::new();
    let lam_domain = Arc::new(Expr::prop());
    let pi_domain = Arc::new(Expr::prop());
    let let_type = Arc::new(Expr::type_());
    let let_value = Arc::new(Expr::prop());
    let metadata_inner = Arc::new(Expr::prop());
    let cases = [
        (
            Expr::lam_arc(
                BinderInfo::Default,
                lam_domain.clone(),
                Arc::new(Expr::bvar(0)),
            ),
            vec![lam_domain],
            Expr::arrow(Expr::prop(), Expr::prop()),
        ),
        (
            Expr::pi_arc(
                BinderInfo::Default,
                pi_domain.clone(),
                Arc::new(Expr::prop()),
            ),
            vec![pi_domain],
            Expr::type_(),
        ),
        (
            Expr::let_named_arc(
                Name::anon(),
                let_type.clone(),
                let_value.clone(),
                Arc::new(Expr::bvar(0)),
                false,
            ),
            vec![let_type, let_value],
            Expr::type_(),
        ),
        (
            mdata_arc(metadata_inner.clone()),
            vec![metadata_inner],
            Expr::type_(),
        ),
    ];

    for (term, children, expected) in cases {
        let tc = TypeChecker::new(&env);
        let _frame = MemoFrame::new(&tc);
        assert_eq!(
            tc.infer_type_full(&term).expect("full child inference"),
            expected
        );
        assert_eq!(tc.ctx_len(), 0);
        for child in children {
            let memo = tc.infer_arc_memo.borrow();
            let (owner, _, cert) = memo
                .get(&memo_key(&child, false, None))
                .expect("the actual stable child must have a memo entry");
            assert!(Arc::ptr_eq(owner, &child));
            assert!(
                cert.is_none(),
                "fast inference must not fabricate certificates"
            );
        }
    }
}

#[test]
fn fast_arc_memo_separates_inference_only_from_full_checking() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let bad = bad_application();
    let _frame = MemoFrame::new(&tc);
    assert_eq!(
        tc.infer_type(&mdata_arc(bad.clone())).expect("infer-only"),
        Expr::prop()
    );
    assert!(tc
        .infer_arc_memo
        .borrow()
        .contains_key(&memo_key(&bad, true, None)));

    let terms = [
        Expr::lam_arc(BinderInfo::Default, bad.clone(), Arc::new(Expr::bvar(0))),
        Expr::pi_arc(BinderInfo::Default, bad.clone(), Arc::new(Expr::prop())),
        Expr::let_named_arc(
            Name::anon(),
            bad.clone(),
            Arc::new(Expr::prop()),
            Arc::new(Expr::bvar(0)),
            false,
        ),
        Expr::let_named_arc(
            Name::anon(),
            Arc::new(Expr::prop()),
            bad.clone(),
            Arc::new(Expr::bvar(0)),
            false,
        ),
        mdata_arc(bad.clone()),
    ];
    for term in terms {
        assert!(matches!(
            tc.infer_type_full(&term),
            Err(TypeError::TypeMismatch { .. })
        ));
        assert!(
            tc.infer_only.get(),
            "full-check entry must restore infer-only mode"
        );
        assert_eq!(tc.ctx_len(), 0);
        assert!(!tc
            .infer_arc_memo
            .borrow()
            .contains_key(&memo_key(&bad, false, None)));
    }
}

#[test]
fn fast_arc_memo_keys_the_active_binder_context() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let outer = tc.ctx_push(Name::anon(), Expr::prop(), BinderInfo::Default);
    let shared = Arc::new(Expr::fvar(outer));
    let term = mdata_arc(shared.clone());
    let _frame = MemoFrame::new(&tc);

    assert_eq!(
        tc.infer_type_full(&term).expect("outer local"),
        Expr::prop()
    );
    let inner = tc.ctx_push(Name::anon(), Expr::type_(), BinderInfo::Default);
    assert_eq!(
        tc.infer_type_full(&term)
            .expect("same outer local under binder"),
        Expr::prop()
    );
    assert!(tc
        .infer_arc_memo
        .borrow()
        .contains_key(&memo_key(&shared, false, Some(outer))));
    assert!(tc
        .infer_arc_memo
        .borrow()
        .contains_key(&memo_key(&shared, false, Some(inner))));
    tc.ctx_pop();
    assert_eq!(
        tc.infer_type_full(&term).expect("restored outer context"),
        Expr::prop()
    );
    tc.ctx_pop();
    assert_eq!(tc.ctx_len(), 0);
}

#[test]
fn fast_arc_memo_preserves_dependent_binder_and_let_results() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    // fun (A : Type) (x : A) => let y : A := x; y
    let term = Expr::lam(
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
    let expected = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
    );
    assert_eq!(
        tc.infer_type_full(&term).expect("dependent full inference"),
        expected
    );
    assert_eq!(tc.ctx_len(), 0);
    assert_eq!(tc.infer_memo_depth.get(), 0);
    assert!(tc.infer_arc_memo.borrow().is_empty());
}

#[test]
fn fast_arc_memo_zero_fallback_and_single_entry_turnover() {
    let env = Environment::new();
    for capacity in [0, 1] {
        let mut tc = TypeChecker::new(&env);
        tc.set_max_cache_entries(capacity);
        let _frame = MemoFrame::new(&tc);
        let shared_type = Arc::new(Expr::type_());
        let sort_two = Expr::sort(Level::succ(Level::succ(Level::zero())));
        assert_eq!(
            tc.infer_type_fast_arc(&shared_type).expect("fast Type"),
            sort_two
        );
        assert_eq!(tc.infer_arc_memo.borrow().len(), capacity);
        if capacity == 1 {
            assert!(
                tc.infer_arc_memo.borrow()[&memo_key(&shared_type, true, None)]
                    .2
                    .is_none()
            );
        }

        let other = Arc::new(Expr::prop());
        assert_eq!(
            tc.infer_type_fast_arc(&other).expect("later inference"),
            Expr::type_()
        );
        assert_eq!(
            tc.infer_arc_memo
                .borrow()
                .contains_key(&memo_key(&other, true, None)),
            capacity != 0
        );
        assert!(!tc
            .infer_arc_memo
            .borrow()
            .contains_key(&memo_key(&shared_type, true, None)));
        let term = Expr::app_arc(
            Arc::new(Expr::lam(
                BinderInfo::Default,
                sort_two.clone(),
                Expr::bvar(0),
            )),
            shared_type.clone(),
        );
        let (ty, cert) = tc
            .infer_type_with_cert(&term)
            .expect("retained inference at capacity");
        assert_eq!(ty, sort_two);
        assert!(tc.infer_arc_memo.borrow().len() <= capacity);
        if capacity == 1 {
            assert!(matches!(
                tc.infer_arc_memo.borrow()[&memo_key(&shared_type, true, None)].2.as_deref(),
                Some(ProofCert::Sort { level }) if *level == Level::succ(Level::zero())
            ));
        }
        assert_eq!(
            CertVerifier::new(&env)
                .verify(&cert, &term)
                .expect("replay at capacity"),
            sort_two
        );
        assert!(!tc.cert_retained.get());
        assert!(matches!(
            tc.infer_type_full(&mdata_arc(bad_application())),
            Err(TypeError::TypeMismatch { .. })
        ));
        assert_eq!(tc.infer_arc_memo.borrow().len(), capacity);
    }
}

#[test]
fn certificate_check_mode_upgrades_type_only_entries() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    tc.set_max_cache_entries(1);
    tc.infer_only.set(false);
    let _frame = MemoFrame::new(&tc);
    let shared = Arc::new(Expr::type_());
    let expected = Expr::sort(Level::succ(Level::succ(Level::zero())));
    tc.ctx_push(Name::anon(), Expr::prop(), BinderInfo::Default);
    assert_eq!(
        tc.infer_type_fast_arc(&shared).expect("scoped fast type"),
        expected
    );
    assert_eq!(tc.infer_arc_memo.borrow().len(), 1);
    tc.ctx_pop();
    assert_eq!(tc.infer_arc_memo.borrow().len(), 1);
    assert!(
        tc.infer_arc_memo
            .borrow()
            .contains_key(&InferArcMemoKey::independent(&shared, false)),
        "closed type-only ownership survives a nonempty prefix pop"
    );
    assert_eq!(
        tc.infer_type_fast_arc(&shared)
            .expect("full-mode fast inference"),
        expected
    );
    assert!(tc.infer_arc_memo.borrow()[&memo_key(&shared, false, None)]
        .2
        .is_none());
    assert!(!tc.cert_retained.get());
    let (ty, cert) = tc
        .infer_type_with_cert_arc(&shared)
        .expect("check-mode certificate upgrade");
    assert_eq!(ty, expected);
    tc.infer_arc_memo
        .borrow_mut()
        .insert_if_absent_with(memo_key(&shared, false, None), 1, || {
            panic!("an existing real certificate must not be replaced")
        });
    assert_eq!(tc.infer_arc_memo.borrow().len(), 1);
    assert!(tc.infer_arc_memo.borrow()[&memo_key(&shared, false, None)]
        .2
        .is_some());
    assert_eq!(
        CertVerifier::new(&env)
            .verify(&cert, &shared)
            .expect("check-mode replay"),
        expected
    );
}

#[test]
fn fast_arc_windows_admit_and_reuse_nodes_after_initial_capacity() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    tc.set_max_cache_entries(4);
    let _frame = MemoFrame::new(&tc);
    let nodes: Vec<_> = (0..6).map(|_| Arc::new(Expr::prop())).collect();
    for node in &nodes {
        assert_eq!(
            tc.infer_type_fast_arc(node).expect("new fast node"),
            Expr::type_()
        );
        assert!(tc
            .infer_arc_memo
            .borrow()
            .contains_key(&memo_key(node, true, None)));
        assert!(tc.infer_arc_memo.borrow().len() <= 4);
    }
    for node in &nodes[..2] {
        assert!(!tc
            .infer_arc_memo
            .borrow()
            .contains_key(&memo_key(node, true, None)));
    }
    for node in &nodes[2..] {
        assert_eq!(
            tc.infer_type_fast_arc(node).expect("recent fast hit"),
            Expr::type_()
        );
        let memo = tc.infer_arc_memo.borrow();
        let entry = memo.get(&memo_key(node, true, None)).expect("recent entry");
        assert!(Arc::ptr_eq(&entry.0, node));
        assert!(entry.2.is_none());
    }
    assert_eq!(tc.infer_arc_memo.borrow().len(), 4);
}

#[test]
fn fast_arc_memo_pins_owners_only_for_the_active_frame() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let frame = MemoFrame::new(&tc);
    let child = Arc::new(Expr::type_());
    let weak = Arc::downgrade(&child);
    let term = mdata_arc(child.clone());
    assert_eq!(
        tc.infer_type(&term).expect("infer actual metadata child"),
        Expr::sort(Level::succ(Level::succ(Level::zero())))
    );
    drop(term);
    drop(child);
    assert!(
        weak.upgrade().is_some(),
        "the entry must pin its address owner"
    );
    drop(frame);
    assert!(
        weak.upgrade().is_none(),
        "clearing must release the memo's owner"
    );
}

#[test]
fn fast_arc_memo_cleans_up_after_success_error_and_direct_calls() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let shared = Arc::new(Expr::type_());
    let expected = Expr::sort(Level::succ(Level::succ(Level::zero())));
    assert_eq!(
        tc.infer_type_fast_arc(&shared).expect("direct fast call"),
        expected
    );
    assert!(tc.infer_arc_memo.borrow().is_empty());
    let (ty, cert) = tc
        .infer_type_with_cert_arc(&shared)
        .expect("direct certificate call");
    assert_eq!(ty, expected);
    assert_eq!(
        CertVerifier::new(&env)
            .verify(&cert, &shared)
            .expect("direct replay"),
        expected
    );
    assert!(tc.infer_arc_memo.borrow().is_empty());

    let bad_body = Expr::lam_arc(BinderInfo::Default, shared, Arc::new(Expr::bvar(1)));
    assert!(matches!(
        tc.infer_type_full(&bad_body),
        Err(TypeError::UnboundVariable(_))
    ));
    assert_eq!(tc.ctx_len(), 0);
    assert_eq!(tc.infer_memo_depth.get(), 0);
    assert!(tc.infer_arc_memo.borrow().is_empty());
    assert!(tc.infer_only.get());
    assert_eq!(
        tc.infer_type(&Expr::prop()).expect("subsequent inference"),
        Expr::type_()
    );

    let bad = bad_application();
    assert!(matches!(
        tc.infer_type_full(&mdata_arc(bad)),
        Err(TypeError::TypeMismatch { .. })
    ));
    assert_eq!(tc.infer_memo_depth.get(), 0);
    assert!(tc.infer_arc_memo.borrow().is_empty());
}

/// A retained certificate traversal can re-enter fast inference while checking
/// that an `And` projection's field is in Prop. The field below is a Pi, so its
/// domain is visited by fast inference before the outer application's argument
/// is visited by certificate inference. Both edges own the SAME Arc to Type.
/// A type-only memo entry must not supply a placeholder Sort(0) certificate for
/// that Sort(1) argument.
#[test]
fn retained_projection_reentry_keeps_real_sort_certificate() {
    let mut env = Environment::new();
    env.init_true_false().expect("initialize checked True");
    env.init_and().expect("initialize checked And");

    let true_ty = Expr::const_(Name::from_string("True"), vec![]);
    let true_intro = Expr::const_(Name::from_string("True.intro"), vec![]);
    let shared_type = Arc::new(Expr::type_());
    // P := forall (_ : Type), True; P is in Prop.
    let p = Expr::pi_arc(
        BinderInfo::Default,
        shared_type.clone(),
        Arc::new(true_ty.clone()),
    );
    let proof_p = Expr::lam_arc(
        BinderInfo::Default,
        shared_type.clone(),
        Arc::new(true_intro.clone()),
    );
    let pair = Expr::apps(
        Expr::const_(Name::from_string("And.intro"), vec![]),
        [p.clone(), true_ty.clone(), proof_p, true_intro.clone()],
    );
    let projection = Expr::proj(Name::from_string("And"), 0, pair);
    // g := fun (_ : P) (_ : Sort 2) => True.intro.
    let g = Expr::lam(
        BinderInfo::Default,
        p,
        Expr::lam(
            BinderInfo::Default,
            Expr::sort(Level::succ(Level::succ(Level::zero()))),
            true_intro,
        ),
    );
    let term = Expr::app_arc(Arc::new(Expr::app(g, projection)), shared_type.clone());

    // Establish the closed term's ordinary typing independently. A separate
    // checker is essential: warming its projection cache would skip the later
    // certificate traversal's Prop-field validation and hide the re-entry.
    TypeChecker::new(&env)
        .check_type(&term, &true_ty)
        .expect("the closed term has type True under full checking");

    let tc = TypeChecker::new(&env);
    let (ty, cert) = tc
        .infer_type_with_cert(&term)
        .expect("retain a certificate for the closed term");
    assert_eq!(ty, true_ty);
    assert_eq!(tc.infer_memo_depth.get(), 0);
    assert!(tc.infer_arc_memo.borrow().is_empty());
    assert!(!tc.cert_retained.get());

    let ProofCert::App { arg_cert, .. } = &cert else {
        panic!("the outer application must retain an App certificate");
    };
    let actual_argument_level = Level::succ(Level::zero());
    assert!(
        matches!(arg_cert.as_ref(), ProofCert::Sort { level } if *level == actual_argument_level),
        "Type needs its actual Sort(1) certificate, not the fast-path placeholder"
    );
    let mut verifier = CertVerifier::new(&env);
    assert_eq!(
        verifier
            .verify(&cert, &term)
            .expect("independent certificate replay"),
        true_ty
    );

    // This is a certificate-fidelity regression, not a claim that replay
    // accepts an invalid proof: the independent Sort rule rejects the old
    // placeholder for the actual argument.
    assert!(matches!(
        verifier.verify(
            &ProofCert::Sort {
                level: Level::zero()
            },
            &shared_type
        ),
        Err(CertError::LevelMismatch { .. })
    ));
}
