// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Exact substitution ownership controls. Structural cases need not be typed;
//! only the explicit inference/replay test below claims a valid closed term.

use super::*;
use crate::cert::{CertError, CertVerifier, ProofCert};
use crate::env::Environment;
use crate::expr::{BinderData, BinderInfo, Multiplicity, ZFCSetExpr};
use crate::tc::TypeChecker;

const TARGET: FVarId = FVarId(93);
const OTHER: FVarId = FVarId(94);

fn app_children(expr: &Expr) -> (&Arc<Expr>, &Arc<Expr>) {
    let ExprKind::App(left, right) = expr.kind() else {
        panic!("expected App")
    };
    (left, right)
}

fn check_shared_operation(leaf: Expr, expected: Expr, run: impl Fn(&Expr) -> Expr) {
    let unchanged = Arc::new(Expr::const_str("unchanged"));
    let branch = Arc::new(Expr::app_arc(Arc::new(leaf), unchanged.clone()));
    let input = Expr::app_arc(branch.clone(), branch);
    let output = run(&input);
    let (left, right) = app_children(&output);
    assert!(
        Arc::ptr_eq(left, right),
        "changed roots must share, not just descendants"
    );
    assert_eq!(
        left.as_ref(),
        &Expr::app(expected, unchanged.as_ref().clone())
    );
    let (_, retained) = app_children(left);
    assert!(
        Arc::ptr_eq(retained, &unchanged),
        "unchanged sibling keeps its Arc"
    );
}

#[test]
fn all_eight_substitutions_keep_exact_changed_child_arcs_and_values() {
    let x = Expr::const_str("X");
    let y = Expr::const_str("Y");
    check_shared_operation(Expr::bvar(0), x.clone(), |e| e.instantiate(&x));
    check_shared_operation(Expr::bvar(1), y.clone(), |e| {
        e.instantiate_rev(&[x.clone(), y.clone()])
    });
    check_shared_operation(Expr::bvar(0), Expr::bvar(2), |e| e.lift(2));
    check_shared_operation(Expr::bvar(2), Expr::bvar(0), |e| {
        e.lower_loose_bvars(2).expect("supported lowering")
    });
    check_shared_operation(Expr::fvar(TARGET), Expr::bvar(0), |e| {
        e.abstract_fvar(TARGET)
    });
    check_shared_operation(Expr::fvar(TARGET), x.clone(), |e| e.subst_fvar(TARGET, &x));
    let u = Name::from_string("u");
    let mapping = HashMap::from([(u.clone(), Level::zero())]);
    // Both Sort and Const leaf overrides are live in each level folder.
    for (leaf, expected) in [
        (Expr::sort(Level::param(u.clone())), Expr::prop()),
        (
            Expr::const_str_levels("Poly", vec![Level::param(u.clone())]),
            Expr::const_str_levels("Poly", vec![Level::zero()]),
        ),
    ] {
        check_shared_operation(leaf.clone(), expected.clone(), |e| {
            e.instantiate_level_params_map(&mapping)
        });
        check_shared_operation(leaf, expected, |e| {
            e.instantiate_level_params_direct(std::slice::from_ref(&u), &[Level::zero()])
        });
    }
}

fn binders(body: Arc<Expr>) -> Vec<Expr> {
    let ty = Arc::new(Expr::type_());
    vec![
        Expr::lam_arc(
            BinderData::new(BinderInfo::Implicit, Multiplicity::One),
            ty.clone(),
            body.clone(),
        ),
        Expr::pi_arc(
            BinderData::new(BinderInfo::InstImplicit, Multiplicity::Zero),
            ty.clone(),
            body.clone(),
        ),
        ek(ExprKind::Let(
            Name::from_string("kept"),
            ty.clone(),
            ty.clone(),
            body.clone(),
            true,
        )),
        ek(ExprKind::CubicalPathLam { body: body.clone() }),
        ek(ExprKind::ZFCComprehension {
            domain: ty.clone(),
            pred: body.clone(),
        }),
        ek(ExprKind::ZFCSet(ZFCSetExpr::Separation {
            set: ty.clone(),
            pred: body.clone(),
        })),
        ek(ExprKind::ZFCSet(ZFCSetExpr::Replacement {
            set: ty,
            func: body,
        })),
    ]
}

fn binder_body(expr: &Expr) -> &Arc<Expr> {
    match expr.kind() {
        ExprKind::Lam(_, _, body)
        | ExprKind::Pi(_, _, body)
        | ExprKind::Let(_, _, _, body, _)
        | ExprKind::CubicalPathLam { body } => body,
        ExprKind::ZFCComprehension { pred, .. }
        | ExprKind::ZFCSet(ZFCSetExpr::Separation { pred, .. }) => pred,
        ExprKind::ZFCSet(ZFCSetExpr::Replacement { func, .. }) => func,
        _ => panic!("expected binder"),
    }
}

fn check_binder_contexts(
    input: Expr,
    outside: Expr,
    inside: Expr,
    depth_sensitive: bool,
    run: impl Fn(&Expr) -> Expr,
) {
    let shared = Arc::new(input);
    let expected_binders = binders(Arc::new(inside));
    for (wrapped, expected) in binders(shared.clone()).into_iter().zip(expected_binders) {
        let expr = Expr::app_arc(shared.clone(), Arc::new(wrapped));
        let output = run(&expr);
        let (ordinary, wrapped) = app_children(&output);
        assert_eq!(ordinary.as_ref(), &outside);
        assert_eq!(
            wrapped.as_ref(),
            &expected,
            "binder metadata/value/depth changed"
        );
        assert_eq!(
            Arc::ptr_eq(ordinary, binder_body(wrapped)),
            !depth_sensitive
        );
    }
}

#[test]
fn shared_inputs_keep_all_seven_binder_roles_and_depth_keys() {
    let x = Expr::const_str("X");
    let y = Expr::const_str("Y");
    let pair = Expr::app(Expr::bvar(0), Expr::bvar(1));
    check_binder_contexts(
        pair.clone(),
        Expr::app(x.clone(), Expr::bvar(0)),
        Expr::app(Expr::bvar(0), x.clone()),
        true,
        |e| e.instantiate(&x),
    );
    check_binder_contexts(
        pair.clone(),
        Expr::app(x.clone(), y.clone()),
        Expr::app(Expr::bvar(0), x.clone()),
        true,
        |e| e.instantiate_rev(&[x.clone(), y.clone()]),
    );
    check_binder_contexts(
        pair,
        Expr::app(Expr::bvar(2), Expr::bvar(3)),
        Expr::app(Expr::bvar(0), Expr::bvar(3)),
        true,
        |e| e.lift(2),
    );
    // Supported in both contexts. Equal output values still use distinct depth keys.
    check_binder_contexts(Expr::bvar(2), Expr::bvar(1), Expr::bvar(1), true, |e| {
        e.lower_loose_bvars(1)
            .expect("no removed binder referenced")
    });
    check_binder_contexts(
        Expr::app(Expr::fvar(TARGET), Expr::bvar(0)),
        Expr::app(Expr::bvar(0), Expr::bvar(1)),
        Expr::app(Expr::bvar(1), Expr::bvar(0)),
        true,
        |e| e.abstract_fvar(TARGET),
    );
    check_binder_contexts(Expr::fvar(TARGET), x.clone(), x.clone(), false, |e| {
        e.subst_fvar(TARGET, &x)
    });
    let u = Name::from_string("u");
    let mapping = HashMap::from([(u.clone(), Level::zero())]);
    check_binder_contexts(
        Expr::sort(Level::param(u.clone())),
        Expr::prop(),
        Expr::prop(),
        false,
        |e| e.instantiate_level_params_map(&mapping),
    );
    check_binder_contexts(
        Expr::sort(Level::param(u.clone())),
        Expr::prop(),
        Expr::prop(),
        false,
        |e| e.instantiate_level_params_direct(std::slice::from_ref(&u), &[Level::zero()]),
    );
}

fn check_root_and_binder_hooks<F: MemoizedSubst>(
    mut make: impl FnMut() -> F,
    input: Expr,
    root_value: Expr,
    binder_value: Expr,
) {
    let mut root = make();
    assert_eq!(root.fold_expr_opt(&input), Some(root_value));
    assert!(
        root.fold_memo().map.is_empty(),
        "leaf root must not allocate a memo Arc"
    );
    let closed = Expr::const_str("closed");
    assert_eq!(root.fold_expr_opt(&closed), None);
    assert!(root.fold_memo().map.is_empty());
    let closed_arc = Arc::new(closed);
    assert!(root.fold_expr_arc_opt(&closed_arc).is_none());
    assert!(root.fold_binder_body_arc_opt(&closed_arc).is_none());
    assert!(root.fold_memo().map.is_empty());

    let mut legacy = make();
    assert_eq!(
        legacy.fold_binder_body_opt(&input),
        Some(binder_value.clone())
    );
    assert_eq!(legacy.memo_depth(), 0, "legacy binder restores its counter");
    assert!(legacy.fold_memo().map.is_empty());
    let input = Arc::new(input);
    let mut arc = make();
    let first = arc
        .fold_binder_body_arc_opt(&input)
        .expect("changed binder child");
    let second = arc
        .fold_binder_body_arc_opt(&input)
        .expect("same changed child");
    assert_eq!(first.as_ref(), &binder_value);
    assert!(Arc::ptr_eq(&first, &second));
    assert_eq!(arc.memo_depth(), 0, "Arc binder restores its counter");
    assert_eq!(arc.fold_memo().map.len(), 1);
}

#[test]
fn legacy_roots_and_binder_hooks_preserve_uncached_leaf_and_pruning_paths() {
    let x = Expr::const_str("X");
    let vals = [x.clone(), Expr::const_str("Y")];
    check_root_and_binder_hooks(
        || Instantiator {
            val: &x,
            depth: 0,
            memo: FoldMemo::default(),
        },
        Expr::bvar(1),
        Expr::bvar(0),
        x.clone(),
    );
    check_root_and_binder_hooks(
        || MultiInstantiator {
            vals: &vals,
            depth: 0,
            memo: FoldMemo::default(),
        },
        Expr::bvar(1),
        vals[1].clone(),
        x.clone(),
    );
    check_root_and_binder_hooks(
        || Lifter {
            start: 0,
            amount: 2,
            memo: FoldMemo::default(),
        },
        Expr::bvar(1),
        Expr::bvar(3),
        Expr::bvar(3),
    );
    check_root_and_binder_hooks(
        || Lowerer {
            start: 0,
            amount: 1,
            memo: FoldMemo::default(),
        },
        Expr::bvar(2),
        Expr::bvar(1),
        Expr::bvar(1),
    );
    check_root_and_binder_hooks(
        || Abstractor::new(TARGET, 0),
        Expr::fvar(TARGET),
        Expr::bvar(0),
        Expr::bvar(1),
    );
    check_root_and_binder_hooks(
        || FVarSubst {
            id: TARGET,
            replacement: &x,
            memo: FoldMemo::default(),
        },
        Expr::fvar(TARGET),
        x.clone(),
        x.clone(),
    );
    let u = Name::from_string("u");
    let mapping = HashMap::from([(u.clone(), Level::zero())]);
    let params = [u.clone()];
    let levels = [Level::zero()];
    check_root_and_binder_hooks(
        || LevelParamSubst {
            subst: &mapping,
            memo: FoldMemo::default(),
        },
        Expr::sort(Level::param(u.clone())),
        Expr::prop(),
        Expr::prop(),
    );
    check_root_and_binder_hooks(
        || LevelParamSubstSlice {
            params: &params,
            levels: &levels,
            memo: FoldMemo::default(),
        },
        Expr::sort(Level::param(u)),
        Expr::prop(),
        Expr::prop(),
    );
}

#[test]
fn replacements_remain_one_step_and_memos_do_not_cross_calls_or_targets() {
    let input = Expr::lam(
        BinderInfo::Default,
        Expr::type_(),
        Expr::app(Expr::bvar(1), Expr::bvar(0)),
    );
    assert_eq!(
        input.instantiate(&Expr::bvar(0)),
        input,
        "replacement is lifted in its own fresh folder"
    );
    let replacement = Expr::app(Expr::fvar(TARGET), Expr::const_str("X"));
    check_shared_operation(Expr::fvar(TARGET), replacement.clone(), |e| {
        e.subst_fvar(TARGET, &replacement)
    });
    let leaf = Arc::new(Expr::fvar(OTHER));
    let x = Expr::const_str("X");
    let mut absent = FVarSubst {
        id: TARGET,
        replacement: &x,
        memo: FoldMemo::default(),
    };
    assert!(absent.fold_expr_arc_opt(&leaf).is_none());
    assert!(absent.fold_binder_body_arc_opt(&leaf).is_none());
    assert_eq!(absent.memo.map.len(), 1);
    assert!(
        absent.memo.map.values().all(Option::is_none),
        "negative results stay memoized"
    );
    let expr = Expr::app_arc(leaf.clone(), leaf);
    let changed = expr.subst_fvar(OTHER, &x);
    let (left, right) = app_children(&changed);
    assert!(Arc::ptr_eq(left, right));
    assert_eq!(left.as_ref(), &x);
    assert_eq!(
        expr.subst_fvar(TARGET, &x),
        expr,
        "another target has no authority from the previous call"
    );
    let y = Expr::const_str("Y");
    assert_eq!(expr.subst_fvar(OTHER, &y), Expr::app(y.clone(), y));
}

#[test]
fn arc_substitution_keeps_lowering_refusals_and_saturating_guard_boundaries() {
    let removed = Arc::new(Expr::bvar(0));
    assert!(Expr::app_arc(removed.clone(), removed)
        .lower_loose_bvars(1)
        .is_none());
    let bound = Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0));
    assert_eq!(bound.lower_loose_bvars(u32::MAX), Some(bound.clone()));
    assert_eq!(bound.lift(0), bound);
    let leaf = Arc::new(Expr::bvar(Expr::MAX_BVAR_INDEX));
    let mut lift = Lifter {
        start: u32::MAX,
        amount: 1,
        memo: FoldMemo::default(),
    };
    assert!(lift.fold_binder_body_arc_opt(&leaf).is_none());
    assert_eq!(
        lift.start,
        u32::MAX,
        "saturating binder arithmetic is not a new error"
    );
    assert!(lift.memo.map.is_empty(), "guard precedes memo lookup");
    let mut abstractor = Abstractor::new(TARGET, u32::MAX);
    let unrelated = Arc::new(Expr::fvar(OTHER));
    assert!(abstractor.fold_binder_body_arc_opt(&unrelated).is_none());
    assert_eq!(abstractor.depth, u32::MAX);
    assert_eq!(abstractor.memo.map.len(), 1);
    // These remain genuine Expr metadata errors, not saturated accepted terms.
    for shared in [false, true] {
        let input = if shared {
            Expr::app_arc(leaf.clone(), leaf.clone())
        } else {
            leaf.as_ref().clone()
        };
        let error = std::panic::catch_unwind(|| input.lift(1))
            .expect_err("MAX_BVAR_INDEX shift must still panic");
        let message = error
            .downcast_ref::<String>()
            .map(String::as_str)
            .or_else(|| error.downcast_ref::<&str>().copied())
            .expect("panic text");
        // Lifting uses the constructor's metadata check, not deserialization.
        assert_eq!(
            message,
            "too many bound variables: loose_bvar_range=1048576 exceeds max=1048575"
        );
    }
}

fn diamond(depth: usize, leaf: Expr) -> Expr {
    let mut expr = leaf;
    for _ in 0..depth {
        let child = Arc::new(expr);
        expr = Expr::app_arc(child.clone(), child);
    }
    expr
}

#[test]
fn second_substitution_visits_exact_shared_nodes_not_shallow_root_copies() {
    let depth = 12;
    let input = diamond(depth, Expr::bvar(0));
    let first = input.lift(1);
    let mut cursor = &first;
    for _ in 0..depth {
        let (left, right) = app_children(cursor);
        assert!(Arc::ptr_eq(left, right));
        cursor = left;
    }
    assert_eq!(cursor, &Expr::bvar(1));
    // Independently reconstruct the old cached Expr shape, not a second folder:
    // two distinct shallow child allocations, whose descendants remain shared.
    let mut old_shape = Expr::bvar(1);
    for _ in 0..depth {
        old_shape = Expr::app_arc(Arc::new(old_shape.clone()), Arc::new(old_shape));
    }
    assert_eq!(first, old_shape);
    let mut shared_fold = Lifter {
        start: 0,
        amount: 1,
        memo: FoldMemo::default(),
    };
    let mut copied_fold = Lifter {
        start: 0,
        amount: 1,
        memo: FoldMemo::default(),
    };
    let shared_output = first.fold_opt_or_clone(&mut shared_fold);
    let copied_output = old_shape.fold_opt_or_clone(&mut copied_fold);
    assert_eq!(shared_output, copied_output);
    assert_eq!(shared_fold.memo.map.len(), depth);
    assert_eq!(copied_fold.memo.map.len(), 2 * depth);
    // The public root is deliberately not a memo entry in either count.
    assert_eq!(shared_output, diamond(depth, Expr::bvar(2)));
}

#[test]
fn substituted_dependent_term_infers_and_independently_replays_with_mutants() {
    let a = FVarId(101);
    let f = FVarId(102);
    let x = FVarId(103);
    let shared_f = Arc::new(Expr::fvar(f));
    let open = Expr::app_arc(
        shared_f.clone(),
        Arc::new(Expr::app_arc(shared_f, Arc::new(Expr::fvar(x)))),
    );
    let term_x = Expr::lam(BinderInfo::Default, Expr::fvar(a), open.abstract_fvar(x));
    let f_type = Expr::pi(BinderInfo::Default, Expr::fvar(a), Expr::fvar(a));
    let term_f = Expr::lam(BinderInfo::Default, f_type, term_x.abstract_fvar(f));
    let term = Expr::lam(BinderInfo::Default, Expr::type_(), term_f.abstract_fvar(a));
    let expected = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(
            BinderInfo::Default,
            Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
            Expr::pi(BinderInfo::Default, Expr::bvar(1), Expr::bvar(2)),
        ),
    );
    let body = binder_body(binder_body(binder_body(&term)));
    let (first_f, inner) = app_children(body);
    let (second_f, _) = app_children(inner);
    assert!(Arc::ptr_eq(first_f, second_f));
    assert_eq!(first_f.as_ref(), &Expr::bvar(1));
    let env = Environment::new();
    let (actual, good) = TypeChecker::new(&env)
        .infer_type_with_cert(&term)
        .expect("actual closed dependent inference");
    assert_eq!(actual, expected);
    let mut verifier = CertVerifier::new(&env);
    assert_eq!(
        verifier
            .verify(&good, &term)
            .expect("independent certificate replay"),
        expected
    );
    // Combined control: the same f survives expression opening, certificate
    // inference, and all three binder rebindings as one certified child.
    let mut node = &good;
    for _ in 0..3 {
        let ProofCert::Lam { body_cert, .. } = node else {
            panic!("Lam certificate")
        };
        node = body_cert;
    }
    let ProofCert::App {
        fn_cert: first_f,
        arg_cert: inner,
        ..
    } = node
    else {
        panic!("outer App certificate")
    };
    let ProofCert::App {
        fn_cert: second_f, ..
    } = inner.as_ref()
    else {
        panic!("inner App certificate")
    };
    assert!(Arc::ptr_eq(first_f, second_f));
    for wrong_type in [false, true] {
        let mut bad = good.clone();
        let mut node = &mut bad;
        for _ in 0..3 {
            let ProofCert::Lam { body_cert, .. } = node else {
                panic!("Lam certificate")
            };
            node = Arc::make_mut(body_cert);
        }
        let ProofCert::App { fn_cert, .. } = node else {
            panic!("App certificate")
        };
        let ProofCert::BVar { idx, expected_type } = Arc::make_mut(fn_cert) else {
            panic!("function BVar certificate")
        };
        assert_eq!(*idx, 1);
        if wrong_type {
            **expected_type = Expr::prop();
            assert!(matches!(
                verifier.verify(&bad, &term),
                Err(CertError::TypeMismatch { .. })
            ));
        } else {
            *idx = 0;
            assert!(matches!(
                verifier.verify(&bad, &term),
                Err(CertError::InvalidBVar(1))
            ));
        }
        assert_eq!(
            verifier
                .verify(&good, &term)
                .expect("positive after refusal"),
            expected
        );
    }
}

#[test]
fn deep_substitution_retains_stack_safe_dispatch_and_exact_leaf() {
    let depth = 1024;
    let mut expr = Expr::fvar(TARGET);
    for _ in 0..depth {
        expr = ek(ExprKind::Squash(Arc::new(expr)));
    }
    let output = expr.subst_fvar(TARGET, &Expr::fvar(OTHER));
    let mut cursor = &output;
    for _ in 0..depth {
        let ExprKind::Squash(child) = cursor.kind() else {
            panic!("Squash")
        };
        cursor = child;
    }
    assert_eq!(cursor, &Expr::fvar(OTHER));
}
