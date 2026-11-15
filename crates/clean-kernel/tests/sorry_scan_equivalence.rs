// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The kernel's sorry scanners — `Expr::{has_sorry, has_non_synthetic_sorry,
//! has_synthetic_sorry}`, the single-pass `Expr::sorry_scan`, and
//! `SorrySummary::from_expr` (through `Expr::trust_scan`) — checked against
//! walkers written HERE, with their own exhaustive child traversal, across
//! every `ExprKind` arm.
//!
//! Since 2026-09-28 (`01189665c`, "a declaration uses sorry iff sorryAx is in
//! its constant closure") those scanners answer two different questions, and
//! this file checks each against the walker that can answer it:
//!
//! * WHETHER there is a sorry (`has_sorry`, and the synthetic bit). This is
//!   the soundness question. `per_node_scan` asks it of EVERY subterm,
//!   including each partial-application prefix of a sorry spine, which the
//!   kernel's scan deliberately does not visit; so it is the check that
//!   skipping those prefixes never hides a sorry.
//! * WHICH KIND (explicit or synthetic). This is provenance only. A
//!   sorry-headed application spine is ONE occurrence, labelled by its literal
//!   flag; its prefixes `sorryAx α` and `sorryAx` are not further, flag-less
//!   occurrences (`expr/sorry.rs`, `push_sorry_scan_children`).
//!   `occurrence_scan` implements that definition.
//!
//! The per-node walk cannot answer the second question. Since `01189665c` a
//! flag-less `sorryAx α` standing alone IS a (non-synthetic) sorry, and every
//! `sorryAx` spine has flag-less prefixes, so the per-node walk reports
//! "explicit" wherever `sorryAx` occurs at all: it read the literal synthetic
//! `@sorryAx Prop Bool.true` as `(true, true, true)`. Until 2026-10-03 this
//! file used the per-node walk as its oracle for all three bits, and so failed
//! on that atom while the kernel answered `(true, false, true)` — the same
//! answer it gave before `01189665c`.

use clean_kernel::{env::SorrySummary, expr::ZFCSetExpr, BinderInfo, Expr, ExprKind, Name};
use std::sync::Arc;

fn c(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn legacy_explicit_sorry() -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("sorry"), vec![]),
        Expr::prop(),
    )
}

fn sorry_ax_const() -> Expr {
    c("sorryAx")
}

fn sorry_ax(flag: &str) -> Expr {
    Expr::apps(sorry_ax_const(), [Expr::prop(), c(flag)])
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

/// Every subterm, each asked the per-node predicates — spine prefixes and the
/// bare head constant included. Authoritative for `has_sorry` and the
/// synthetic bit; its explicit bit over-reports (see the module docs).
fn per_node_scan(expr: &Expr) -> (bool, bool, bool) {
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

/// The documented occurrence semantics: a node whose application head is
/// `sorry` / `sorryAx` is ONE occurrence, labelled by the per-node predicates;
/// only its arguments are walked further (a sorry can hide in an argument),
/// never its partial-application prefixes. Every other node is walked by this
/// file's own traversal.
fn occurrence_scan(expr: &Expr) -> (bool, bool, bool) {
    let mut has_sorry = false;
    let mut has_explicit = false;
    let mut has_synthetic = false;
    let mut stack = vec![expr];

    while let Some(curr) = stack.pop() {
        if curr.is_sorry() {
            has_sorry = true;
            has_explicit |= curr.is_non_synthetic_sorry();
            has_synthetic |= curr.is_synthetic_sorry();
            stack.extend(curr.get_app_args());
            continue;
        }
        push_expr_children(&mut stack, curr);
    }

    (has_sorry, has_explicit, has_synthetic)
}

/// The leaf shapes, each with the `(has_sorry, has_explicit, has_synthetic)`
/// the kernel must report for it. Pinned literally, so neither walker above can
/// drift away from the definition without a red here.
fn atoms() -> Vec<(&'static str, Expr, (bool, bool, bool))> {
    vec![
        ("const", c("noSorry"), (false, false, false)),
        (
            "legacy_explicit",
            legacy_explicit_sorry(),
            (true, true, false),
        ),
        (
            "explicit_sorry_ax",
            sorry_ax("Bool.false"),
            (true, true, false),
        ),
        (
            "synthetic_sorry_ax",
            sorry_ax("Bool.true"),
            (true, false, true),
        ),
        // The shapes `01189665c` made visible: each was sorry-FREE before it.
        (
            "partial_sorry_ax",
            Expr::app(sorry_ax_const(), Expr::prop()),
            (true, true, false),
        ),
        ("bare_sorry_ax", sorry_ax_const(), (true, true, false)),
        (
            "non_literal_flag",
            Expr::apps(
                sorry_ax_const(),
                [Expr::prop(), Expr::app(c("not"), c("Bool.true"))],
            ),
            (true, true, false),
        ),
        // A literal synthetic spine with an extra argument: still ONE
        // synthetic occurrence.
        (
            "synthetic_extra_arg",
            Expr::apps(
                sorry_ax_const(),
                [Expr::prop(), c("Bool.true"), c("noSorry")],
            ),
            (true, false, true),
        ),
        // Arguments of a sorry spine are scanned: an explicit sorry in the
        // type argument of a synthetic one is found ...
        (
            "explicit_inside_synthetic",
            Expr::apps(sorry_ax_const(), [sorry_ax("Bool.false"), c("Bool.true")]),
            (true, true, true),
        ),
        // ... and two nested synthetic occurrences stay synthetic.
        (
            "synthetic_inside_synthetic",
            Expr::apps(sorry_ax_const(), [sorry_ax("Bool.true"), c("Bool.true")]),
            (true, false, true),
        ),
        // An MData-wrapped head is not a sorry head, so the flag is not read:
        // the bare `sorryAx` under the MData is the occurrence, and it is
        // labelled explicit (an over-report, never an under-report).
        (
            "mdata_head",
            Expr::apps(
                Expr::mdata(vec![], sorry_ax_const()),
                [Expr::prop(), c("Bool.true")],
            ),
            (true, true, false),
        ),
    ]
}

fn base_cases(
    no_sorry: &Expr,
    legacy_explicit: &Expr,
    explicit_sorry_ax: &Expr,
    synthetic_sorry_ax: &Expr,
) -> Vec<(&'static str, Expr)> {
    vec![
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
    let no_sorry = c("noSorry");
    let legacy_explicit = legacy_explicit_sorry();
    let explicit_sorry_ax = sorry_ax("Bool.false");
    let synthetic_sorry_ax = sorry_ax("Bool.true");

    let mut cases: Vec<_> = atoms()
        .into_iter()
        .map(|(label, expr, _)| (label, expr))
        .collect();
    cases.extend(base_cases(
        &no_sorry,
        &legacy_explicit,
        &explicit_sorry_ax,
        &synthetic_sorry_ax,
    ));
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

/// The three kernel answers for `expr`, each checked equal to `expected`.
fn assert_kernel_scans_equal(label: &str, expr: &Expr, expected: (bool, bool, bool)) {
    assert_eq!(
        (
            expr.has_sorry(),
            expr.has_non_synthetic_sorry(),
            expr.has_synthetic_sorry(),
        ),
        expected,
        "predicate API disagrees with the occurrence definition for {label}: {expr:?}"
    );
    assert_eq!(
        expr.sorry_scan(),
        expected,
        "single-pass sorry_scan disagrees with the occurrence definition for {label}: {expr:?}"
    );
    let summary = SorrySummary::from_expr(expr);
    assert_eq!(
        (
            summary.has_sorry,
            summary.has_explicit_sorry,
            summary.has_synthetic_sorry,
        ),
        expected,
        "SorrySummary::from_expr disagrees with the occurrence definition for {label}: {expr:?}"
    );
}

#[test]
fn atom_scans_are_pinned() {
    for (label, expr, pinned) in atoms() {
        assert_eq!(
            occurrence_scan(&expr),
            pinned,
            "occurrence walker drifted from the pinned answer for {label}: {expr:?}"
        );
        assert_kernel_scans_equal(label, &expr, pinned);
    }
}

#[test]
fn sorry_scan_matches_occurrence_walker_across_expr_shapes() {
    for (label, expr) in test_cases() {
        assert_kernel_scans_equal(label, &expr, occurrence_scan(&expr));
    }
}

/// The soundness half: the kernel visits a sorry spine once and skips its
/// prefixes; a walk that visits EVERY subterm must find no sorry the kernel
/// missed, and no synthetic one either. The kernel's explicit bit may be
/// narrower than the per-node one (prefixes are not occurrences) but never
/// wider: each occurrence it labels explicit is a node the per-node walk sees.
#[test]
fn skipping_spine_prefixes_never_hides_a_sorry() {
    for (label, expr) in test_cases() {
        let (has_sorry, per_node_explicit, has_synthetic) = per_node_scan(&expr);
        let summary = SorrySummary::from_expr(&expr);
        for (surface, (kernel_has, kernel_explicit, kernel_synthetic)) in [
            (
                "predicate API",
                (
                    expr.has_sorry(),
                    expr.has_non_synthetic_sorry(),
                    expr.has_synthetic_sorry(),
                ),
            ),
            ("sorry_scan", expr.sorry_scan()),
            (
                "SorrySummary::from_expr",
                (
                    summary.has_sorry,
                    summary.has_explicit_sorry,
                    summary.has_synthetic_sorry,
                ),
            ),
        ] {
            assert_eq!(
                (kernel_has, kernel_synthetic),
                (has_sorry, has_synthetic),
                "{surface} under-/over-reports a sorry against the per-node walk for {label}: {expr:?}"
            );
            assert!(
                !kernel_explicit || per_node_explicit,
                "{surface} invents an explicit sorry the per-node walk never saw for {label}: {expr:?}"
            );
        }
    }
}
