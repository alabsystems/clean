// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Exact occurrence queries are transformation support, not typing evidence.
//! Structural cases intentionally exercise all constructors without claiming
//! they are well typed. Only the final inference/replay test claims validity.

use super::super::RebindContext;
use super::SupportContext;
use crate::cert::{CertError, CertVerifier, ProofCert, ZFCSetCertKind};
use crate::env::Environment;
use crate::expr::{BinderInfo, Expr, ExprKind, ExprVisitor, FVarId, Literal, ZFCSetExpr};
use crate::level::Level;
use crate::name::Name;
use crate::tc::TypeChecker;
use std::sync::Arc;

const TARGET: FVarId = FVarId(53);
const OTHER: FVarId = FVarId(54);

struct OccurrenceOracle(FVarId);

impl ExprVisitor for OccurrenceOracle {
    type Result = bool;

    fn combine(&self, a: bool, b: bool) -> bool {
        a || b
    }

    fn visit_fvar(&mut self, id: FVarId) -> bool {
        id == self.0
    }
}

// Independently construct every ExprKind, expanding the ZFCSet family to all
// nine alternatives. Never use the production child enumerator as the oracle.
fn expression_cases([a, b, c, d]: [Arc<Expr>; 4]) -> Vec<(ExprKind, usize)> {
    use ExprKind as E;
    use ZFCSetExpr as Z;
    vec![
        (E::BVar(0), 0),
        (E::FVar(OTHER), 0),
        (E::Sort(Level::zero()), 0),
        (
            E::Const(Name::from_string("supportConstant"), Default::default()),
            0,
        ),
        (E::App(a.clone(), b.clone()), 2),
        (E::Lam(BinderInfo::Default.into(), a.clone(), b.clone()), 2),
        (E::Pi(BinderInfo::Default.into(), a.clone(), b.clone()), 2),
        (
            E::Let(
                Name::from_string("v"),
                a.clone(),
                b.clone(),
                c.clone(),
                false,
            ),
            3,
        ),
        (E::Lit(Literal::String(Arc::from("supportLiteral"))), 0),
        (E::Proj(Name::from_string("S"), 0, a.clone()), 1),
        (E::MData(vec![], a.clone()), 1),
        (E::SProp, 0),
        (E::Squash(a.clone()), 1),
        (E::CubicalInterval, 0),
        (E::CubicalI0, 0),
        (E::CubicalI1, 0),
        (
            E::CubicalPath {
                ty: a.clone(),
                left: b.clone(),
                right: c.clone(),
            },
            3,
        ),
        (E::CubicalPathLam { body: a.clone() }, 1),
        (
            E::CubicalPathApp {
                path: a.clone(),
                arg: b.clone(),
            },
            2,
        ),
        (
            E::CubicalHComp {
                ty: a.clone(),
                phi: b.clone(),
                u: c.clone(),
                base: d.clone(),
            },
            4,
        ),
        (
            E::CubicalTransp {
                ty: a.clone(),
                phi: b.clone(),
                base: c.clone(),
            },
            3,
        ),
        (
            E::CubicalCoe {
                ty: a.clone(),
                r: b.clone(),
                s: c.clone(),
                base: d,
            },
            4,
        ),
        (E::ZFCSet(Z::Empty), 0),
        (E::ZFCSet(Z::Infinity), 0),
        (E::ZFCSet(Z::Singleton(a.clone())), 1),
        (E::ZFCSet(Z::Pair(a.clone(), b.clone())), 2),
        (E::ZFCSet(Z::Union(a.clone())), 1),
        (E::ZFCSet(Z::PowerSet(a.clone())), 1),
        (
            E::ZFCSet(Z::Separation {
                set: a.clone(),
                pred: b.clone(),
            }),
            2,
        ),
        (
            E::ZFCSet(Z::Replacement {
                set: a.clone(),
                func: b.clone(),
            }),
            2,
        ),
        (E::ZFCSet(Z::Choice(a.clone())), 1),
        (
            E::ZFCMem {
                element: a.clone(),
                set: b.clone(),
            },
            2,
        ),
        (E::ZFCComprehension { domain: a, pred: b }, 2),
    ]
}

#[test]
fn exact_support_checks_every_expression_constructor_and_child() {
    let unrelated = Arc::new(Expr::fvar(OTHER));
    let baseline = expression_cases(std::array::from_fn(|_| unrelated.clone()));
    assert_eq!(baseline.len(), 33);
    assert_eq!(baseline.iter().map(|(_, arity)| arity).sum::<usize>(), 43);
    for (kind, _) in baseline {
        let expr = Expr::from_kind(kind);
        let mut context = SupportContext::new(TARGET);
        assert!(!context.contains_target(&expr));
        assert!(!OccurrenceOracle(TARGET).visit_expr(&expr));
        let cached = context.expr_memo.len();
        assert!(!context.contains_target(&expr));
        assert_eq!(context.expr_memo.len(), cached);
    }
    let mut edges = 0;
    for position in 0..4 {
        let mut children = std::array::from_fn(|_| unrelated.clone());
        children[position] = Arc::new(Expr::fvar(TARGET));
        for (kind, arity) in expression_cases(children) {
            if position >= arity {
                continue;
            }
            let expr = Expr::from_kind(kind);
            let mut context = SupportContext::new(TARGET);
            assert!(OccurrenceOracle(TARGET).visit_expr(&expr));
            assert!(context.contains_target(&expr));
            let cached = context.expr_memo.len();
            assert!(context.contains_target(&expr));
            assert_eq!(context.expr_memo.len(), cached);
            edges += 1;
        }
    }
    assert_eq!(edges, 43);
    let leaf = Expr::fvar(TARGET);
    assert!(SupportContext::new(TARGET).contains_target(&leaf));
    assert!(!SupportContext::new(OTHER).contains_target(&leaf));
    let closed = Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0));
    let mut context = SupportContext::new(TARGET);
    assert!(!context.contains_target(&closed));
    assert!(
        context.expr_memo.is_empty(),
        "cached closed metadata is the O(1) fast path"
    );
}

#[test]
fn exact_support_memoizes_shared_positive_and_negative_dags_per_target() {
    // A recursive tree walk would expand 2^4096 paths. The production walk
    // uses neither recursion nor structural hashing/equality/serialization.
    const DEPTH: usize = 4096;
    let mut root = Arc::new(Expr::fvar(OTHER));
    for _ in 0..DEPTH {
        root = Arc::new(Expr::app_arc(root.clone(), root));
    }
    for (target, expected) in [(TARGET, false), (OTHER, true)] {
        let mut context = SupportContext::new(target);
        assert_eq!(context.contains_target(&root), expected);
        assert_eq!(context.expr_memo.len(), DEPTH + 1);
        assert!(context
            .expr_memo
            .values()
            .all(|(_, found)| *found == expected));
        for _ in 0..8 {
            assert_eq!(context.contains_target(&root), expected);
        }
        assert_eq!(context.expr_memo.len(), DEPTH + 1);
    }
}

#[test]
fn positive_expression_support_skips_suffix_and_memoizes_only_witness_ancestors() {
    const DEPTH: usize = 4096;
    let target = Arc::new(Expr::fvar(TARGET));
    let mut suffix = Arc::new(Expr::fvar(OTHER));
    for _ in 0..DEPTH {
        suffix = Arc::new(Expr::app_arc(suffix.clone(), suffix));
    }
    let witness = Arc::new(Expr::app_arc(target, suffix.clone()));
    let root = Expr::from_kind(ExprKind::Squash(witness.clone()));
    let mut context = SupportContext::new(TARGET);
    assert!(context.contains_target(&root));
    assert_eq!(context.expr_memo.len(), 3, "leaf and two actual ancestors");
    assert!(context.expr_memo.values().all(|(_, found)| *found));
    assert!(!context.expr_memo.contains_key(&Arc::as_ptr(&suffix)));

    // A warm positive child must propagate through a DIFFERENT root too.
    let second = Expr::app_arc(witness, suffix.clone());
    assert!(context.contains_target(&second));
    assert_eq!(context.expr_memo.len(), 4);
    assert!(!context.expr_memo.contains_key(&Arc::as_ptr(&suffix)));

    // Skipping that sibling was not an absence claim: query it independently.
    assert!(!context.contains_target(&suffix));
    assert_eq!(context.expr_memo.len(), DEPTH + 5);
    assert_eq!(
        context
            .expr_memo
            .values()
            .filter(|(_, found)| !found)
            .count(),
        DEPTH + 1,
        "the negative shared DAG is still completely summarized"
    );
    assert!(context.contains_target(&root));
    assert!(context.contains_target(&second));
    assert_eq!(context.expr_memo.len(), DEPTH + 5);
    let last = Expr::app_arc(suffix.clone(), Arc::new(Expr::fvar(TARGET)));
    assert!(context.contains_target(&last));
    assert_eq!(
        context.expr_memo.len(),
        DEPTH + 7,
        "a warm negative prefix must resume and reach the later witness"
    );
    assert!(SupportContext::new(OTHER).contains_target(&suffix));
}

#[test]
fn positive_expression_support_keeps_every_prefix_and_skips_only_later_children() {
    let mut edges = 0;
    for position in 0..4 {
        // Distinct allocations, including the equal-valued negative leaves.
        let children = std::array::from_fn(|index| {
            Arc::new(Expr::fvar(if index == position { TARGET } else { OTHER }))
        });
        for (kind, arity) in expression_cases(children.clone()) {
            if position >= arity {
                continue;
            }
            let root = Expr::from_kind(kind);
            let mut context = SupportContext::new(TARGET);
            assert!(OccurrenceOracle(TARGET).visit_expr(&root));
            assert!(context.contains_target(&root));
            assert_eq!(context.expr_memo.len(), position + 2);
            for (index, child) in children.iter().enumerate().take(arity) {
                assert_eq!(
                    context
                        .expr_memo
                        .get(&Arc::as_ptr(child))
                        .map(|(_, found)| *found),
                    (index <= position).then_some(index == position),
                    "child {index}, witness {position}"
                );
            }
            edges += 1;
        }
    }
    assert_eq!(edges, 43, "all constructor child positions");
}

#[test]
fn positive_expression_support_preserves_later_conversion_and_metadata_refusal() {
    let make = |index| {
        metadata_cert(Expr::app(
            Expr::fvar(TARGET),
            Expr::app(Expr::fvar(OTHER), Expr::bvar(index)),
        ))
    };
    let root = make(7);
    let mut support = SupportContext::new(TARGET);
    assert!(!support.arc(&root).unchanged_at(0));
    assert_eq!(support.expr_memo.len(), 2, "metadata root and target only");
    let expected = metadata_cert(Expr::app(
        Expr::bvar(0),
        Expr::app(Expr::fvar(OTHER), Expr::bvar(8)),
    ));
    let actual = RebindContext::new(TARGET).convert_arc(&root, 0);
    assert_eq!(
        actual, expected,
        "actual conversion still visits the suffix"
    );

    let invalid_shift = make(Expr::MAX_BVAR_INDEX);
    let failure =
        std::panic::catch_unwind(|| RebindContext::new(TARGET).convert_arc(&invalid_shift, 0))
            .expect_err("the skipped suffix must still reject an out-of-range shift");
    let message = failure
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| failure.downcast_ref::<&str>().copied())
        .expect("string metadata-range panic");
    assert_eq!(
        message,
        "too many bound variables: loose_bvar_range=1048576 exceeds max=1048575"
    );
}

fn metadata_cert(expr: Expr) -> Arc<ProofCert> {
    Arc::new(ProofCert::Const {
        name: Name::from_string("structuralMetadata"),
        levels: vec![],
        type_: Box::new(expr),
    })
}

#[test]
fn exact_support_reuses_unrelated_metadata_but_preserves_loose_bvar_conversion() {
    // The target leaf already makes this certificate affected. Its metadata
    // need not be summarized, but the original converter must still shift it.
    let known_target = ProofCert::FVar {
        id: TARGET,
        type_: Box::new(Expr::app(Expr::fvar(OTHER), Expr::bvar(7))),
    };
    let mut support = SupportContext::new(TARGET);
    let summary = support.cert(&known_target);
    assert!(summary.may_abstract_fvar);
    assert_eq!(
        summary.loose_range, 0,
        "positive support stops before metadata"
    );
    assert!(!summary.unchanged_at(8));
    assert!(support.expr_memo.is_empty());
    assert_eq!(
        RebindContext::new(TARGET).convert_ref(&known_target, 0),
        ProofCert::BVar {
            idx: 0,
            expected_type: Box::new(Expr::app(Expr::fvar(OTHER), Expr::bvar(8))),
        }
    );

    let metadata = Expr::app(Expr::fvar(OTHER), Expr::bvar(0));
    let child = metadata_cert(metadata);
    let input = Arc::new(ProofCert::App {
        fn_cert: child.clone(),
        fn_type: Box::new(Expr::prop()),
        arg_cert: child.clone(),
        result_type: Box::new(Expr::prop()),
    });
    let mut context = RebindContext::new(TARGET);
    for depth in [1, 2, 8, 512, u32::MAX] {
        assert!(Arc::ptr_eq(&context.convert_arc(&input, depth), &input));
    }
    assert!(
        context.memo.is_empty(),
        "no converted nodes for any covered depth"
    );
    let occurrence_nodes = context.support.expr_memo.len();
    assert_eq!(
        occurrence_nodes, 2,
        "metadata root and unrelated FVar; BVar is closed"
    );
    let shifted = context.convert_arc(&input, 0);
    assert!(!Arc::ptr_eq(&shifted, &input));
    let ProofCert::App {
        fn_cert, arg_cert, ..
    } = shifted.as_ref()
    else {
        panic!("App");
    };
    assert!(Arc::ptr_eq(fn_cert, arg_cert));
    assert_eq!(
        fn_cert.as_ref(),
        metadata_cert(Expr::app(Expr::fvar(OTHER), Expr::bvar(1))).as_ref()
    );
    assert!(Arc::ptr_eq(&context.convert_arc(&input, 0), &shifted));
    assert_eq!(context.support.expr_memo.len(), occurrence_nodes);
    assert!(Arc::ptr_eq(&context.convert_arc(&input, 1), &input));

    let changed_target = RebindContext::new(OTHER).convert_arc(&child, 1);
    assert!(!Arc::ptr_eq(&changed_target, &child));
    assert_eq!(
        changed_target.as_ref(),
        metadata_cert(Expr::app(Expr::bvar(1), Expr::bvar(0))).as_ref()
    );
}

#[test]
fn positive_cert_support_skips_siblings_but_negative_support_stays_complete() {
    const DEPTH: usize = 64;
    let sort = Arc::new(ProofCert::Sort {
        level: Level::zero(),
    });
    let mut shared = Arc::new(ProofCert::Lam {
        binder_info: BinderInfo::Default,
        arg_type_cert: sort.clone(),
        body_cert: sort,
        result_type: Box::new(Expr::prop()),
    });
    for _ in 0..DEPTH {
        shared = Arc::new(ProofCert::App {
            fn_cert: shared.clone(),
            fn_type: Box::new(Expr::prop()),
            arg_cert: shared,
            result_type: Box::new(Expr::prop()),
        });
    }
    let root = Arc::new(ProofCert::App {
        fn_cert: Arc::new(ProofCert::FVar {
            id: TARGET,
            type_: Box::new(Expr::app(Expr::fvar(OTHER), Expr::bvar(7))),
        }),
        fn_type: Box::new(Expr::fvar(OTHER)),
        arg_cert: shared.clone(),
        result_type: Box::new(Expr::bvar(7)),
    });
    let mut positive = SupportContext::new(TARGET);
    for _ in 0..8 {
        let summary = positive.arc(&root);
        for depth in [0, 8, u32::MAX] {
            assert!(!summary.unchanged_at(depth));
        }
        assert_eq!(
            positive.memo.len(),
            2,
            "root and the first target leaf only"
        );
        assert!(positive.expr_memo.is_empty(), "no unneeded metadata query");
    }
    let mut absent = SupportContext::new(FVarId(55));
    let summary = absent.arc(&root);
    assert!(!summary.may_abstract_fvar);
    assert_eq!(
        absent.memo.len(),
        DEPTH + 4,
        "every distinct certificate node"
    );
    assert_eq!((summary.loose_range, summary.binder_height), (8, 1));
    assert!(!summary.unchanged_at(7));
    assert!(summary.unchanged_at(8));
    assert!(
        !summary.unchanged_at(u32::MAX),
        "depth saturation still needs conversion"
    );

    let actual = RebindContext::new(TARGET).convert_arc(&root, 0);
    let ProofCert::App {
        fn_cert,
        fn_type,
        arg_cert,
        result_type,
    } = actual.as_ref()
    else {
        panic!("App");
    };
    assert_eq!(
        fn_cert.as_ref(),
        &ProofCert::BVar {
            idx: 0,
            expected_type: Box::new(Expr::app(Expr::fvar(OTHER), Expr::bvar(8))),
        }
    );
    assert_eq!(fn_type.as_ref(), &Expr::fvar(OTHER));
    assert_eq!(result_type.as_ref(), &Expr::bvar(8));
    assert!(
        Arc::ptr_eq(arg_cert, &shared),
        "actual unchanged DAG is still reused"
    );
}

#[test]
fn positive_metadata_support_still_converts_skipped_certificate_edges() {
    // ZFC result metadata is visited before its certificate children by the
    // support query. Its positive result must not skip the actual conversion.
    let root = Arc::new(ProofCert::ZFCSet {
        kind: ZFCSetCertKind::Pair(
            Arc::new(ProofCert::FVar {
                id: OTHER,
                type_: Box::new(Expr::fvar(TARGET)),
            }),
            Arc::new(ProofCert::BVar {
                idx: 2,
                expected_type: Box::new(Expr::bvar(2)),
            }),
        ),
        result_type: Box::new(Expr::fvar(TARGET)),
    });
    let mut support = SupportContext::new(TARGET);
    assert!(!support.arc(&root).unchanged_at(1));
    assert_eq!(support.memo.len(), 1, "no certificate child queried");
    assert_eq!(
        support.expr_memo.len(),
        1,
        "just the positive metadata root"
    );
    let expected = ProofCert::ZFCSet {
        kind: ZFCSetCertKind::Pair(
            Arc::new(ProofCert::FVar {
                id: OTHER,
                type_: Box::new(Expr::bvar(1)),
            }),
            Arc::new(ProofCert::BVar {
                idx: 3,
                expected_type: Box::new(Expr::bvar(3)),
            }),
        ),
        result_type: Box::new(Expr::bvar(1)),
    };
    let actual = RebindContext::new(TARGET).convert_arc(&root, 1);
    assert_eq!(actual.as_ref(), &expected);
    assert_eq!(
        serde_json::to_vec(actual.as_ref()).unwrap(),
        serde_json::to_vec(&expected).unwrap()
    );
}

#[test]
fn positive_cert_support_keeps_late_saturation_and_metadata_failure() {
    let maximal = Arc::new(ProofCert::BVar {
        idx: u32::MAX,
        expected_type: Box::new(Expr::prop()),
    });
    let binder = Arc::new(ProofCert::Lam {
        binder_info: BinderInfo::Default,
        arg_type_cert: Arc::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        body_cert: maximal.clone(),
        result_type: Box::new(Expr::prop()),
    });
    let mut root = ProofCert::App {
        fn_cert: Arc::new(ProofCert::FVar {
            id: TARGET,
            type_: Box::new(Expr::prop()),
        }),
        fn_type: Box::new(Expr::prop()),
        arg_cert: binder.clone(),
        result_type: Box::new(Expr::prop()),
    };
    let mut support = SupportContext::new(TARGET);
    assert!(!support.cert(&root).unchanged_at(u32::MAX));
    assert_eq!(
        support.memo.len(),
        1,
        "only the first target leaf, not the root value"
    );
    let actual = RebindContext::new(TARGET).convert_ref(&root, u32::MAX);
    let ProofCert::App {
        fn_cert, arg_cert, ..
    } = &actual
    else {
        panic!("App");
    };
    assert_eq!(
        fn_cert.as_ref(),
        &ProofCert::BVar {
            idx: u32::MAX,
            expected_type: Box::new(Expr::prop()),
        }
    );
    assert!(
        !Arc::ptr_eq(arg_cert, &binder),
        "late binder depth saturation is not skipped"
    );
    assert_eq!(arg_cert.as_ref(), binder.as_ref());
    let ProofCert::Lam { body_cert, .. } = arg_cert.as_ref() else {
        panic!("Lam");
    };
    assert!(
        !Arc::ptr_eq(body_cert, &maximal),
        "late BVar index saturation is not skipped"
    );
    drop(support);

    let ProofCert::App { arg_cert, .. } = &mut root else {
        panic!("App");
    };
    *arg_cert = metadata_cert(Expr::lam(
        BinderInfo::Default,
        Expr::prop(),
        Expr::fvar(TARGET),
    ));
    let failure =
        std::panic::catch_unwind(|| RebindContext::new(TARGET).convert_ref(&root, u32::MAX))
            .expect_err("positive support must not suppress a later metadata failure");
    let message = failure
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| failure.downcast_ref::<&str>().copied())
        .expect("string metadata-range panic");
    assert!(
        message.contains("too many bound variables: loose_bvar_range="),
        "{message}"
    );
}

#[test]
fn exact_support_preserves_target_metadata_range_failure_and_saturation() {
    let affected = metadata_cert(Expr::lam(
        BinderInfo::Default,
        Expr::prop(),
        Expr::fvar(TARGET),
    ));
    let unrelated = metadata_cert(Expr::lam(
        BinderInfo::Default,
        Expr::prop(),
        Expr::fvar(OTHER),
    ));
    assert!(Arc::ptr_eq(
        &RebindContext::new(TARGET).convert_arc(&unrelated, u32::MAX),
        &unrelated
    ));
    // Certificate depth arithmetic saturates; Expr's narrower metadata range
    // still rejects an actually substituted target, exactly as before.
    let failure =
        std::panic::catch_unwind(|| RebindContext::new(TARGET).convert_arc(&affected, u32::MAX))
            .expect_err("the original affected metadata converter must run");
    let message = failure
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| failure.downcast_ref::<&str>().copied())
        .expect("string metadata-range panic");
    assert!(
        message.contains("too many bound variables: loose_bvar_range="),
        "{message}"
    );

    let maximal = Arc::new(ProofCert::BVar {
        idx: u32::MAX,
        expected_type: Box::new(Expr::fvar(OTHER)),
    });
    let result = RebindContext::new(TARGET).convert_arc(&maximal, u32::MAX);
    assert!(
        !Arc::ptr_eq(&result, &maximal),
        "u64 certificate range guard is retained"
    );
    assert_eq!(result.as_ref(), maximal.as_ref());
}

#[test]
fn exact_support_dependent_inference_replays_and_rejects_same_claim_mutants() {
    // During the inner abstraction, outer A/x FVars remain in types/proofs.
    // They are unrelated to that binder, not evidence to bypass verification.
    let expr = Expr::lam(
        BinderInfo::Default,
        Expr::type_(),
        Expr::lam(
            BinderInfo::Default,
            Expr::bvar(0),
            Expr::lam(BinderInfo::Default, Expr::bvar(1), Expr::bvar(1)),
        ),
    );
    let expected = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(
            BinderInfo::Default,
            Expr::bvar(0),
            Expr::pi(BinderInfo::Default, Expr::bvar(1), Expr::bvar(2)),
        ),
    );
    let env = Environment::new();
    let (actual, good) = TypeChecker::new(&env)
        .infer_type_with_cert(&expr)
        .expect("actual dependent three-binder inference");
    assert_eq!(actual, expected);
    let mut verifier = CertVerifier::new(&env);
    assert_eq!(
        verifier
            .verify(&good, &expr)
            .expect("independent positive replay"),
        expected
    );
    for wrong_type in [false, true] {
        let mut bad = good.clone();
        let mut leaf = &mut bad;
        for _ in 0..3 {
            let ProofCert::Lam { body_cert, .. } = leaf else {
                panic!("Lam");
            };
            leaf = Arc::make_mut(body_cert);
        }
        let ProofCert::BVar { idx, expected_type } = leaf else {
            panic!("returned BVar");
        };
        assert_eq!(*idx, 1);
        if wrong_type {
            **expected_type = Expr::prop();
            assert!(matches!(
                verifier.verify(&bad, &expr),
                Err(CertError::TypeMismatch { .. })
            ));
        } else {
            *idx = 0;
            assert!(matches!(
                verifier.verify(&bad, &expr),
                Err(CertError::InvalidBVar(1))
            ));
        }
        assert_eq!(
            verifier
                .verify(&good, &expr)
                .expect("same positive after refusal"),
            expected
        );
    }
}
