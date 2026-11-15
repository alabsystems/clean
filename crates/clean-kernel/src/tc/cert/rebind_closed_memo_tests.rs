// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structural cache controls plus real inference and independent replay.

use super::super::{convert_fvar_cert_to_bvar, convert_with_closed_memo};
use super::*;
use crate::cert::CertVerifier;
use crate::expr::{BinderInfo, Expr, FVarId};
use crate::level::Level;
use crate::name::Name;
use crate::{Environment, TypeChecker};

fn closed_dag(depth: usize) -> Arc<ProofCert> {
    let mut node = Arc::new(ProofCert::Sort {
        level: Level::zero(),
    });
    for _ in 0..depth {
        node = Arc::new(ProofCert::App {
            fn_cert: node.clone(),
            fn_type: Box::new(Expr::prop()),
            arg_cert: node,
            result_type: Box::new(Expr::prop()),
        });
    }
    node
}

fn wrapper(child: Arc<ProofCert>) -> ProofCert {
    ProofCert::MData {
        metadata: Default::default(),
        inner_cert: child,
        result_type: Box::new(Expr::prop()),
    }
}

fn inner(cert: &ProofCert) -> &Arc<ProofCert> {
    let ProofCert::MData { inner_cert, .. } = cert else {
        panic!("wrapper")
    };
    inner_cert
}

#[test]
fn closed_shared_dag_support_is_reused_across_distinct_targets() {
    // This is a structural traversal fixture, not a valid typing derivation.
    for depth in [8, 24] {
        for binders in [8, 32] {
            let node = closed_dag(depth);
            let mut memo = RebindClosedMemo::default();
            for id in 0..binders {
                let converted = convert_with_closed_memo(
                    wrapper(node.clone()),
                    FVarId(id as u64),
                    0,
                    &mut memo,
                    256,
                );
                assert!(Arc::ptr_eq(inner(&converted), &node));
            }
            assert!(memo.visits <= depth + binders + 1, "{} visits", memo.visits);
            assert!(memo.hits >= binders - 1);
        }
    }
}

#[test]
fn target_specific_absence_never_becomes_fvar_free_support() {
    let first = FVarId(7);
    let second = FVarId(8);
    for child in [
        Arc::new(ProofCert::FVar {
            id: second,
            type_: Box::new(Expr::prop()),
        }),
        Arc::new(ProofCert::Const {
            name: Name::from_string("structural"),
            levels: vec![],
            // Only metadata mentions the future target.
            type_: Box::new(Expr::fvar(second)),
        }),
    ] {
        let mut memo = RebindClosedMemo::default();
        let original = wrapper(child);
        for target in [first, second, first] {
            assert_eq!(
                convert_with_closed_memo(original.clone(), target, 0, &mut memo, 64),
                convert_fvar_cert_to_bvar(original.clone(), target, 0),
            );
        }
        assert_eq!(memo.len(), 0, "FVar-bearing nodes must not enter this memo");
    }
}

#[test]
fn cached_support_still_checks_depth_and_metadata_bvar_shifts() {
    let child = Arc::new(ProofCert::BVar {
        idx: 2,
        expected_type: Box::new(Expr::bvar(0)),
    });
    let original = wrapper(child);
    let mut memo = RebindClosedMemo::default();
    for depth in [3, 0, 1, 3] {
        assert_eq!(
            convert_with_closed_memo(original.clone(), FVarId(19), depth, &mut memo, 64),
            convert_fvar_cert_to_bvar(original.clone(), FVarId(19), depth),
        );
    }
    assert!(memo.hits > 0);
}

#[test]
fn cached_support_preserves_depth_and_index_saturation() {
    // Structural boundary fixture, not a valid typing derivation. Certificate
    // index/depth addition saturates; unlike Expr metadata, it does not panic.
    let body = Arc::new(ProofCert::BVar {
        idx: u32::MAX,
        expected_type: Box::new(Expr::prop()),
    });
    let child = Arc::new(ProofCert::Lam {
        binder_info: BinderInfo::Default,
        arg_type_cert: closed_dag(0),
        body_cert: body.clone(),
        result_type: Box::new(Expr::prop()),
    });
    let original = wrapper(child);
    let mut memo = RebindClosedMemo::default();
    let _ = convert_with_closed_memo(original.clone(), FVarId(1), 0, &mut memo, 64);
    assert!(memo.len() > 0);
    let cached = convert_with_closed_memo(original.clone(), FVarId(2), u32::MAX, &mut memo, 64);
    let uncached = convert_fvar_cert_to_bvar(original.clone(), FVarId(2), u32::MAX);
    assert_eq!(cached, uncached);
    assert_eq!(
        cached, original,
        "saturating arithmetic preserves these values"
    );
    assert!(memo.hits > 0);
    assert!(
        !Arc::ptr_eq(inner(&cached), inner(&original)),
        "cached binder support must not skip depth saturation"
    );
    let ProofCert::Lam { body_cert, .. } = inner(&cached).as_ref() else {
        panic!("Lam")
    };
    assert!(
        !Arc::ptr_eq(body_cert, &body),
        "cached BVar support must not skip index saturation"
    );
}

#[test]
fn weak_memo_does_not_retain_values_or_survive_arc_mutation() {
    let mut child = closed_dag(0);
    let mut memo = RebindClosedMemo::default();
    let converted = convert_with_closed_memo(wrapper(child.clone()), FVarId(1), 0, &mut memo, 64);
    drop(converted);
    assert_eq!(Arc::strong_count(&child), 1);
    let old_owner = Arc::downgrade(&child);
    assert!(memo.get(&child).is_some());
    *Arc::make_mut(&mut child) = ProofCert::BVar {
        idx: 0,
        expected_type: Box::new(Expr::prop()),
    };
    assert!(old_owner.upgrade().is_none());
    assert!(memo.get(&child).is_none());
    let new_owner = Arc::downgrade(&child);
    let converted = convert_with_closed_memo(wrapper(child.clone()), FVarId(2), 1, &mut memo, 64);
    drop(converted);
    drop(child);
    assert!(new_owner.upgrade().is_none());
    assert!(memo
        .entries
        .values()
        .all(|(owner, _)| owner.upgrade().is_none()));
}

#[test]
fn stale_or_wrong_weak_owner_cannot_authorize_a_summary_hit() {
    let mut memo = RebindClosedMemo::default();
    let original = closed_dag(0);
    let converted =
        convert_with_closed_memo(wrapper(original.clone()), FVarId(1), 0, &mut memo, 64);
    drop(converted);
    let summary = memo.get(&original).unwrap();
    let other = closed_dag(0);
    let other_key = Arc::as_ptr(&other) as usize;
    // Live Weak owners prevent actual allocation-address reuse. Inject the
    // mismatched association directly to exercise the identity guard anyway.
    memo.entries
        .insert(other_key, (Arc::downgrade(&original), summary));
    assert!(memo.get(&other).is_none());
    assert!(!memo.entries.contains_key(&other_key));
    let expired = Arc::downgrade(&original);
    drop(original);
    assert!(expired.upgrade().is_none());
    memo.entries.insert(other_key, (expired, summary));
    assert!(memo.get(&other).is_none());
    assert!(!memo.entries.contains_key(&other_key));
}

#[test]
fn outer_cleanup_guard_and_checker_drop_release_weak_entries() {
    let env = Environment::new();
    let checker = TypeChecker::new(&env);
    let child = closed_dag(0);
    let warm = || {
        let converted = convert_with_closed_memo(
            wrapper(child.clone()),
            FVarId(1),
            0,
            &mut checker.rebind_closed_memo.borrow_mut(),
            64,
        );
        drop(converted);
    };
    warm();
    assert_eq!(Arc::strong_count(&child), 1);
    assert_eq!(Arc::weak_count(&child), 1);
    let refused = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _guard = crate::tc::cert::ClearRebindMemo(&checker.rebind_closed_memo);
        panic!("exercise cleanup, not kernel acceptance");
    }));
    assert!(refused.is_err());
    assert_eq!(checker.rebind_closed_memo.borrow().len(), 0);
    assert_eq!(Arc::weak_count(&child), 0);
    warm();
    assert_eq!(Arc::weak_count(&child), 1);
    drop(checker);
    assert_eq!(Arc::weak_count(&child), 0);
}

#[test]
fn zero_and_full_admission_caps_preserve_original_conversion() {
    let original = wrapper(closed_dag(8));
    for cap in [0, 1, 4] {
        let mut memo = RebindClosedMemo::default();
        for target in [FVarId(9), FVarId(10)] {
            assert_eq!(
                convert_with_closed_memo(original.clone(), target, 0, &mut memo, cap),
                convert_fvar_cert_to_bvar(original.clone(), target, 0),
            );
            assert!(memo.len() <= cap);
        }
    }
}

fn nested_closed_lets(count: usize) -> (Expr, Expr) {
    let ty = Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop());
    let value = Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0));
    let mut body = value.clone();
    for _ in 0..count {
        body = Expr::let_named_arc(
            Name::from_string("saved"),
            Arc::new(ty.clone()),
            Arc::new(value.clone()),
            Arc::new(body),
            false,
        );
    }
    (body, ty)
}

#[test]
fn real_nested_let_certificates_replay_and_outer_exits_clear_the_memo() {
    let env = Environment::new();
    for count in [4, 16] {
        let checker = TypeChecker::new(&env);
        let (expr, expected) = nested_closed_lets(count);
        let (ty, cert) = checker
            .infer_type_with_cert(&expr)
            .expect("real closed term");
        assert_eq!(ty, expected);
        assert_eq!(
            CertVerifier::new(&env).verify(&cert, &expr).unwrap(),
            expected
        );
        let memo = checker.rebind_closed_memo.borrow();
        assert_eq!(memo.len(), 0);
        assert!(
            memo.hits > 0,
            "production binder exits must consume the memo"
        );
        assert!(memo.visits <= 64 * count + 64);
        drop(memo);
        // The function child first warms real binder support; the unbound
        // argument then fails before the enclosing inference can succeed.
        let failing = Expr::app(expr.clone(), Expr::bvar(0));
        assert!(checker.infer_type_with_cert(&failing).is_err());
        assert_eq!(checker.rebind_closed_memo.borrow().len(), 0);
        let (_, cert_again) = checker.infer_type_with_cert(&expr).unwrap();
        assert_eq!(
            CertVerifier::new(&env).verify(&cert_again, &expr).unwrap(),
            expected
        );
    }
}

#[test]
fn cached_inference_certificate_corruption_still_refuses_the_same_claim() {
    let env = Environment::new();
    let checker = TypeChecker::new(&env);
    let (expr, expected) = nested_closed_lets(4);
    let (_, good) = checker.infer_type_with_cert(&expr).unwrap();
    let mut verifier = CertVerifier::new(&env);
    for corrupt_type in [false, true] {
        let mut bad = good.clone();
        let ProofCert::Let { value_cert, .. } = &mut bad else {
            panic!("Let")
        };
        let ProofCert::Lam { body_cert, .. } = Arc::make_mut(value_cert) else {
            panic!("Lam")
        };
        let ProofCert::BVar { idx, expected_type } = Arc::make_mut(body_cert) else {
            panic!("BVar")
        };
        if corrupt_type {
            **expected_type = Expr::type_();
        } else {
            *idx = 1;
        }
        assert!(verifier.verify(&bad, &expr).is_err());
        assert_eq!(verifier.verify(&good, &expr).unwrap(), expected);
    }
}
