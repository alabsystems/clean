// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for proof_helpers free functions: mk_eq_refl, abstract_over_expr,
//! abstract_at_rewrite_site, extract_or/implies/iff, mk_negation, lift_bvars.

use super::proof_helpers::*;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, Level};

const CONSTRAINED_STACK: usize = 1024 * 1024;

fn nat() -> Expr {
    Expr::const_(Name::from_string("Nat"), vec![])
}

fn const_expr(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

#[test]
fn test_mk_eq_refl_structure() {
    let u = Level::succ(Level::zero());
    let ty = nat();
    let val = const_expr("a");
    let refl = mk_eq_refl(&u, &ty, &val);

    // Should be App(App(Const("Eq.refl", [u]), ty), val)
    let args = refl.get_app_args();
    assert_eq!(args.len(), 2, "Eq.refl should have 2 args: type and value");
    let head = refl.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, levels) => {
            assert_eq!(name.to_string(), "Eq.refl");
            assert_eq!(levels.len(), 1);
        }
        _ => panic!("expected Const(Eq.refl), got {:?}", head),
    }
}

#[test]
fn test_abstract_over_expr_replaces_target_with_bvar() {
    let a = const_expr("a");
    let result = abstract_over_expr(&a, &a, 0);
    match result.kind() {
        ExprKind::BVar(idx) => assert_eq!(*idx, 0),
        _ => panic!("expected BVar(0), got {:?}", result),
    }
}

#[test]
fn test_abstract_over_expr_leaves_non_target_unchanged() {
    let a = const_expr("a");
    let b = const_expr("b");
    let result = abstract_over_expr(&a, &b, 0);
    assert_eq!(result, a, "non-target should be unchanged");
}

#[test]
fn test_abstract_over_expr_app_replaces_in_both_positions() {
    let a = const_expr("a");
    let f = const_expr("f");
    let fa = Expr::app(f.clone(), a.clone());
    let result = abstract_over_expr(&fa, &a, 0);

    // Should produce App(f, BVar(0))
    match result.kind() {
        ExprKind::App(func, arg) => {
            assert_eq!(**func, f, "function position unchanged");
            match arg.kind() {
                ExprKind::BVar(idx) => assert_eq!(*idx, 0),
                _ => panic!("expected BVar(0) in arg position"),
            }
        }
        _ => panic!("expected App, got {:?}", result),
    }
}

#[test]
fn test_abstract_at_rewrite_site_identical_preserves_target() {
    // When orig == rewritten, even if orig contains target, don't abstract.
    let a = const_expr("a");
    let result = abstract_at_rewrite_site(&a, &a, &a, 0);
    assert_eq!(result, a, "identical orig/rewritten should preserve orig");
}

#[test]
fn test_abstract_at_rewrite_site_rewrites_at_site() {
    let a = const_expr("a");
    let b = const_expr("b");
    // orig = a, rewritten = b, target = a -> BVar(0)
    let result = abstract_at_rewrite_site(&a, &b, &a, 0);
    match result.kind() {
        ExprKind::BVar(idx) => assert_eq!(*idx, 0),
        _ => panic!("expected BVar(0) at rewrite site, got {:?}", result),
    }
}

#[test]
fn test_extract_or_disjuncts_single() {
    let p = const_expr("P");
    let disjuncts = extract_or_disjuncts(&p);
    assert_eq!(disjuncts.len(), 1);
    assert_eq!(disjuncts[0], p);
}

#[test]
fn test_extract_or_disjuncts_binary() {
    let p = const_expr("P");
    let q = const_expr("Q");
    // Build: Or P Q = App(App(Const("Or"), P), Q)
    let or_pq = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), p.clone()),
        q.clone(),
    );
    let disjuncts = extract_or_disjuncts(&or_pq);
    assert_eq!(disjuncts.len(), 2);
    assert_eq!(disjuncts[0], p);
    assert_eq!(disjuncts[1], q);
}

#[test]
fn test_extract_or_disjuncts_nested() {
    let p = const_expr("P");
    let q = const_expr("Q");
    let r = const_expr("R");
    let or = |a: Expr, b: Expr| {
        Expr::app(
            Expr::app(Expr::const_(Name::from_string("Or"), vec![]), a),
            b,
        )
    };
    // Or P (Or Q R)
    let expr = or(p.clone(), or(q.clone(), r.clone()));
    let disjuncts = extract_or_disjuncts(&expr);
    assert_eq!(disjuncts.len(), 3);
    assert_eq!(disjuncts[0], p);
    assert_eq!(disjuncts[1], q);
    assert_eq!(disjuncts[2], r);
}

#[test]
fn test_extract_implies_components_non_dependent_pi() {
    let p = const_expr("P");
    let q = const_expr("Q");
    // Pi(_ : P, Q) where Q doesn't use BVar(0) = P -> Q
    let arrow = Expr::pi(BinderInfo::Default, p.clone(), q.clone());
    let result = extract_implies_components(&arrow);
    let (domain, body) = result.expect("non-dependent Pi should have implies components");
    assert_eq!(domain, p);
    assert_eq!(body, q);
}

#[test]
fn test_extract_implies_components_dependent_pi_returns_none() {
    let p = const_expr("P");
    // Pi(x : P, BVar(0)) -- body references x, so it's a dependent Pi
    let dep = Expr::pi(BinderInfo::Default, p, Expr::bvar(0));
    assert!(
        extract_implies_components(&dep).is_none(),
        "dependent Pi should not have implies components"
    );
}

#[test]
fn test_extract_iff_components() {
    let p = const_expr("P");
    let q = const_expr("Q");
    let iff = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Iff"), vec![]), p.clone()),
        q.clone(),
    );
    let result = extract_iff_components(&iff);
    let (lhs, rhs) = result.expect("Iff app should have extractable components");
    assert_eq!(lhs, p);
    assert_eq!(rhs, q);
}

#[test]
fn test_extract_iff_components_non_iff_returns_none() {
    let p = const_expr("P");
    assert!(
        extract_iff_components(&p).is_none(),
        "non-Iff expression should return None"
    );
}

#[test]
fn test_mk_negation_structure() {
    let p = const_expr("P");
    let neg = mk_negation(&p);
    // Not(P) = Pi(_ : P, False)
    match neg.kind() {
        ExprKind::Pi(_, domain, body) => {
            assert_eq!(**domain, p);
            match body.kind() {
                ExprKind::Const(name, levels) => {
                    assert_eq!(name.to_string(), "False");
                    assert!(levels.is_empty());
                }
                _ => panic!("expected Const(False), got {:?}", body),
            }
        }
        _ => panic!("expected Pi, got {:?}", neg),
    }
}

#[test]
fn test_lift_bvars_lifts_free_variable() {
    // BVar(0) with no binders above = free, should be lifted
    let bv = Expr::bvar(0);
    let lifted = lift_bvars(&bv, 3);
    match lifted.kind() {
        ExprKind::BVar(idx) => assert_eq!(*idx, 3),
        _ => panic!("expected BVar(3), got {:?}", lifted),
    }
}

#[test]
fn test_lift_bvars_preserves_constants() {
    let c = const_expr("c");
    let lifted = lift_bvars(&c, 5);
    assert_eq!(lifted, c, "constants should be unchanged by lifting");
}

#[test]
fn test_lift_bvars_under_binder() {
    // Lambda(_, Nat, BVar(0)) -- BVar(0) is bound, should NOT be lifted
    let body = Expr::lam(BinderInfo::Default, nat(), Expr::bvar(0));
    let lifted = lift_bvars(&body, 1);
    // Under the binder, BVar(0) has cutoff=1 so idx(0) < cutoff(1) -> not lifted
    match lifted.kind() {
        ExprKind::Lam(_, _, inner_body) => match inner_body.kind() {
            ExprKind::BVar(idx) => assert_eq!(*idx, 0, "bound var should not be lifted"),
            _ => panic!("expected BVar(0)"),
        },
        _ => panic!("expected Lam"),
    }
}

/// Memory verification: abstract_over_expr recurses to full Expr depth.
///
/// Runs on a constrained stack using a dedicated small-stack thread so this
/// stays sensitive to `stacker::maybe_grow` regressions instead of only
/// documenting a shallow success case on the default test stack.
///
/// Regression test for memory_verification P1 iter 1320.
#[test]
fn test_abstract_over_expr_deep_recursion() {
    let handle = std::thread::Builder::new()
        // libtest uses the standard thread builder on this toolchain, whose
        // Unix default minimum stack is 2 MiB. Keep this below that so losing
        // `stacker::maybe_grow` makes the regression more likely to fail.
        .stack_size(CONSTRAINED_STACK)
        .spawn(|| {
            let target = const_expr("target");
            let f = const_expr("f");

            // Build: f(f(f(...f(target)...))) at depth `d`
            fn build_deep_app(f: &Expr, leaf: &Expr, depth: usize) -> Expr {
                let mut expr = leaf.clone();
                for _ in 0..depth {
                    expr = Expr::app(f.clone(), expr);
                }
                expr
            }

            // Match the repo's other stack-safe regression tests: deep enough that
            // the constrained 4 MiB thread stack would be brittle without the
            // guard, while still running quickly under the protected path.
            let depth = 10_000;
            let deep = build_deep_app(&f, &target, depth);
            let result = abstract_over_expr(&deep, &target, 0);

            // Verify: innermost position replaced with BVar(0), all f applications preserved
            let mut current = &result;
            for _ in 0..depth {
                match current.kind() {
                    ExprKind::App(func, arg) => {
                        assert_eq!(**func, f, "function position should be preserved");
                        current = arg;
                    }
                    other => panic!("expected App at depth, got {other:?}"),
                }
            }
            match current.kind() {
                ExprKind::BVar(idx) => {
                    assert_eq!(*idx, 0, "innermost target should become BVar(0)")
                }
                other => panic!("expected BVar(0) at leaf, got {other:?}"),
            }

            eprintln!(
                "abstract_over_expr recursion: depth={depth} completed on a {} byte stack with stacker::maybe_grow guard.",
                CONSTRAINED_STACK
            );
        })
        .expect("small-stack thread spawn should succeed");
    handle
        .join()
        .unwrap_or_else(|panic| std::panic::resume_unwind(panic));
}
