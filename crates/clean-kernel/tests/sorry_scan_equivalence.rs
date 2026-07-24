// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_kernel::{env::SorrySummary, expr::ZFCSetExpr, BinderInfo, Expr, ExprKind, Name};
use std::sync::Arc;

fn legacy_explicit_sorry() -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("sorry"), vec![]),
        Expr::prop(),
    )
}

fn sorry_ax(flag: &str) -> Expr {
    Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("sorryAx"), vec![]),
            Expr::prop(),
        ),
        Expr::const_(Name::from_string(flag), vec![]),
    )
}

fn push_zfc_set_children<'a>(stack: &mut Vec<&'a Expr>, set_expr: &'a ZFCSetExpr) {
    match set_expr {
        ZFCSetExpr::Empty | ZFCSetExpr::Infinity => {}
        ZFCSetExpr::Singleton(a)
        | ZFCSetExpr::Union(a)
        | ZFCSetExpr::PowerSet(a)
        | ZFCSetExpr::Choice(a) => stack.push(a),
        ZFCSetExpr::Pair(a, b)
        | ZFCSetExpr::Separation { set: a, pred: b }
        | ZFCSetExpr::Replacement { set: a, func: b } => {
            stack.push(b);
            stack.push(a);
        }
    }
}

fn push_expr_children<'a>(stack: &mut Vec<&'a Expr>, curr: &'a Expr) {
    match curr.kind() {
        ExprKind::Sort(_)
        | ExprKind::Const(_, _)
        | ExprKind::BVar(_)
        | ExprKind::FVar(_)
        | ExprKind::Lit(_)
        | ExprKind::SProp
        | ExprKind::CubicalInterval
        | ExprKind::CubicalI0
        | ExprKind::CubicalI1 => {}
        ExprKind::App(f, a) => {
            stack.push(a);
            stack.push(f);
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            stack.push(body);
            stack.push(ty);
        }
        ExprKind::Let(_, ty, val, body, _) => {
            stack.push(body);
            stack.push(val);
            stack.push(ty);
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
            stack.push(inner);
        }
        ExprKind::CubicalPath { ty, left, right } => {
            stack.push(right);
            stack.push(left);
            stack.push(ty);
        }
        ExprKind::CubicalPathLam { body } => stack.push(body),
        ExprKind::CubicalPathApp { path, arg } => {
            stack.push(arg);
            stack.push(path);
        }
        ExprKind::CubicalHComp { ty, phi, u, base } => {
            stack.push(base);
            stack.push(u);
            stack.push(phi);
            stack.push(ty);
        }
        ExprKind::CubicalTransp { ty, phi, base } => {
            stack.push(base);
            stack.push(phi);
            stack.push(ty);
        }
        ExprKind::CubicalCoe { ty, r, s, base } => {
            stack.push(base);
            stack.push(s);
            stack.push(r);
            stack.push(ty);
        }
        ExprKind::ZFCSet(set_expr) => push_zfc_set_children(stack, set_expr),
        ExprKind::ZFCMem { element, set } => {
            stack.push(set);
            stack.push(element);
        }
        ExprKind::ZFCComprehension { domain, pred } => {
            stack.push(pred);
            stack.push(domain);
        }
    }
}

fn legacy_sorry_scan(expr: &Expr) -> (bool, bool, bool) {
    let mut has_sorry = false;
    let mut has_explicit = false;
    let mut has_synthetic = false;
    let mut stack = vec![expr];

    while let Some(curr) = stack.pop() {
        has_sorry |= curr.is_sorry();
        has_explicit |= curr.is_non_synthetic_sorry();
        has_synthetic |= curr.is_synthetic_sorry();
        push_expr_children(&mut stack, curr);
    }

    (has_sorry, has_explicit, has_synthetic)
}

fn base_cases(
    no_sorry: &Expr,
    legacy_explicit: &Expr,
    explicit_sorry_ax: &Expr,
    synthetic_sorry_ax: &Expr,
) -> Vec<(&'static str, Expr)> {
    vec![
        ("const", no_sorry.clone()),
        ("legacy_explicit", legacy_explicit.clone()),
        ("explicit_sorry_ax", explicit_sorry_ax.clone()),
        ("synthetic_sorry_ax", synthetic_sorry_ax.clone()),
        (
            "app_mixed",
            Expr::app(
                legacy_explicit.clone(),
                Expr::app(explicit_sorry_ax.clone(), synthetic_sorry_ax.clone()),
            ),
        ),
        (
            "lam",
            Expr::lam(
                BinderInfo::Default,
                synthetic_sorry_ax.clone(),
                Expr::app(no_sorry.clone(), legacy_explicit.clone()),
            ),
        ),
        (
            "pi",
            Expr::pi(
                BinderInfo::Implicit,
                explicit_sorry_ax.clone(),
                synthetic_sorry_ax.clone(),
            ),
        ),
        (
            "let",
            Expr::let_named(
                Name::anon(),
                Expr::prop(),
                legacy_explicit.clone(),
                Expr::app(no_sorry.clone(), synthetic_sorry_ax.clone()),
                false,
            ),
        ),
        (
            "proj",
            Expr::proj(
                Name::from_string("Pkg.Struct"),
                0,
                explicit_sorry_ax.clone(),
            ),
        ),
        ("mdata", Expr::mdata(vec![], synthetic_sorry_ax.clone())),
        (
            "squash",
            Expr::from_kind(ExprKind::Squash(Arc::new(legacy_explicit.clone()))),
        ),
    ]
}

fn cubical_cases(
    no_sorry: &Expr,
    legacy_explicit: &Expr,
    explicit_sorry_ax: &Expr,
    synthetic_sorry_ax: &Expr,
) -> Vec<(&'static str, Expr)> {
    vec![
        (
            "cubical_path",
            Expr::from_kind(ExprKind::CubicalPath {
                ty: Arc::new(Expr::prop()),
                left: Arc::new(explicit_sorry_ax.clone()),
                right: Arc::new(synthetic_sorry_ax.clone()),
            }),
        ),
        (
            "cubical_path_lam",
            Expr::from_kind(ExprKind::CubicalPathLam {
                body: Arc::new(legacy_explicit.clone()),
            }),
        ),
        (
            "cubical_path_app",
            Expr::from_kind(ExprKind::CubicalPathApp {
                path: Arc::new(explicit_sorry_ax.clone()),
                arg: Arc::new(Expr::from_kind(ExprKind::CubicalI1)),
            }),
        ),
        (
            "cubical_hcomp",
            Expr::from_kind(ExprKind::CubicalHComp {
                ty: Arc::new(Expr::prop()),
                phi: Arc::new(explicit_sorry_ax.clone()),
                u: Arc::new(synthetic_sorry_ax.clone()),
                base: Arc::new(no_sorry.clone()),
            }),
        ),
        (
            "cubical_transp",
            Expr::from_kind(ExprKind::CubicalTransp {
                ty: Arc::new(Expr::prop()),
                phi: Arc::new(no_sorry.clone()),
                base: Arc::new(legacy_explicit.clone()),
            }),
        ),
    ]
}

fn zfc_cases(
    no_sorry: &Expr,
    legacy_explicit: &Expr,
    explicit_sorry_ax: &Expr,
    synthetic_sorry_ax: &Expr,
) -> Vec<(&'static str, Expr)> {
    vec![
        (
            "zfc_singleton",
            Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Singleton(Arc::new(
                explicit_sorry_ax.clone(),
            )))),
        ),
        (
            "zfc_pair",
            Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Pair(
                Arc::new(synthetic_sorry_ax.clone()),
                Arc::new(no_sorry.clone()),
            ))),
        ),
        (
            "zfc_replacement",
            Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Replacement {
                set: Arc::new(explicit_sorry_ax.clone()),
                func: Arc::new(synthetic_sorry_ax.clone()),
            })),
        ),
        (
            "zfc_mem",
            Expr::from_kind(ExprKind::ZFCMem {
                element: Arc::new(legacy_explicit.clone()),
                set: Arc::new(no_sorry.clone()),
            }),
        ),
        (
            "zfc_comprehension",
            Expr::from_kind(ExprKind::ZFCComprehension {
                domain: Arc::new(no_sorry.clone()),
                pred: Arc::new(synthetic_sorry_ax.clone()),
            }),
        ),
    ]
}

fn test_cases() -> Vec<(&'static str, Expr)> {
    let no_sorry = Expr::const_(Name::from_string("noSorry"), vec![]);
    let legacy_explicit = legacy_explicit_sorry();
    let explicit_sorry_ax = sorry_ax("Bool.false");
    let synthetic_sorry_ax = sorry_ax("Bool.true");

    let mut cases = base_cases(
        &no_sorry,
        &legacy_explicit,
        &explicit_sorry_ax,
        &synthetic_sorry_ax,
    );
    cases.extend(cubical_cases(
        &no_sorry,
        &legacy_explicit,
        &explicit_sorry_ax,
        &synthetic_sorry_ax,
    ));
    cases.extend(zfc_cases(
        &no_sorry,
        &legacy_explicit,
        &explicit_sorry_ax,
        &synthetic_sorry_ax,
    ));
    cases
}

#[test]
fn sorry_scan_matches_legacy_walker_across_expr_shapes() {
    for (label, expr) in test_cases() {
        let expected = legacy_sorry_scan(&expr);
        assert_eq!(
            (
                expr.has_sorry(),
                expr.has_non_synthetic_sorry(),
                expr.has_synthetic_sorry(),
            ),
            expected,
            "legacy predicate API drifted for {label}: {expr:?}"
        );
        assert_eq!(
            expr.sorry_scan(),
            expected,
            "single-pass sorry_scan must match legacy walker for {label}: {expr:?}"
        );

        let summary = SorrySummary::from_expr(&expr);
        assert_eq!(
            (
                summary.has_sorry,
                summary.has_explicit_sorry,
                summary.has_synthetic_sorry,
            ),
            expected,
            "SorrySummary::from_expr must preserve legacy walker results for {label}: {expr:?}"
        );
    }
}
