// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structural visitor controls, not kernel-proof or performance claims.

use super::*;
use crate::expr::{BinderData, BinderInfo, MDataValue, Multiplicity};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Hook {
    Ordinary,
    Binder,
}

/// Independent constructor/role table: 43 slots, seven binder bodies.
fn cases([a, b, c, d]: &[Arc<Expr>; 4]) -> Vec<(Expr, &'static [Hook])> {
    use Hook::{Binder as B, Ordinary as O};
    let name = Name::from_string("visitor.payload");
    vec![
        (ek(ExprKind::App(a.clone(), b.clone())), &[O, O]),
        (
            ek(ExprKind::Lam(
                BinderData::new(BinderInfo::Implicit, Multiplicity::One),
                a.clone(),
                b.clone(),
            )),
            &[O, B],
        ),
        (
            ek(ExprKind::Pi(
                BinderData::new(BinderInfo::InstImplicit, Multiplicity::Zero),
                a.clone(),
                b.clone(),
            )),
            &[O, B],
        ),
        (
            ek(ExprKind::Let(
                name.clone(),
                a.clone(),
                b.clone(),
                c.clone(),
                true,
            )),
            &[O, O, B],
        ),
        (ek(ExprKind::Proj(name.clone(), 7, a.clone())), &[O]),
        (
            ek(ExprKind::MData(
                vec![(name, MDataValue::Bool(true))],
                a.clone(),
            )),
            &[O],
        ),
        (ek(ExprKind::Squash(a.clone())), &[O]),
        (
            ek(ExprKind::CubicalPath {
                ty: a.clone(),
                left: b.clone(),
                right: c.clone(),
            }),
            &[O, O, O],
        ),
        (ek(ExprKind::CubicalPathLam { body: a.clone() }), &[B]),
        (
            ek(ExprKind::CubicalPathApp {
                path: a.clone(),
                arg: b.clone(),
            }),
            &[O, O],
        ),
        (
            ek(ExprKind::CubicalHComp {
                ty: a.clone(),
                phi: b.clone(),
                u: c.clone(),
                base: d.clone(),
            }),
            &[O, O, O, O],
        ),
        (
            ek(ExprKind::CubicalTransp {
                ty: a.clone(),
                phi: b.clone(),
                base: c.clone(),
            }),
            &[O, O, O],
        ),
        (
            ek(ExprKind::CubicalCoe {
                ty: a.clone(),
                r: b.clone(),
                s: c.clone(),
                base: d.clone(),
            }),
            &[O, O, O, O],
        ),
        (ek(ExprKind::ZFCSet(ZFCSetExpr::Singleton(a.clone()))), &[O]),
        (
            ek(ExprKind::ZFCSet(ZFCSetExpr::Pair(a.clone(), b.clone()))),
            &[O, O],
        ),
        (ek(ExprKind::ZFCSet(ZFCSetExpr::Union(a.clone()))), &[O]),
        (ek(ExprKind::ZFCSet(ZFCSetExpr::PowerSet(a.clone()))), &[O]),
        (
            ek(ExprKind::ZFCSet(ZFCSetExpr::Separation {
                set: a.clone(),
                pred: b.clone(),
            })),
            &[O, B],
        ),
        (
            ek(ExprKind::ZFCSet(ZFCSetExpr::Replacement {
                set: a.clone(),
                func: b.clone(),
            })),
            &[O, B],
        ),
        (ek(ExprKind::ZFCSet(ZFCSetExpr::Choice(a.clone()))), &[O]),
        (
            ek(ExprKind::ZFCMem {
                element: a.clone(),
                set: b.clone(),
            }),
            &[O, O],
        ),
        (
            ek(ExprKind::ZFCComprehension {
                domain: a.clone(),
                pred: b.clone(),
            }),
            &[O, B],
        ),
    ]
}

fn children(expr: &Expr) -> Vec<&Arc<Expr>> {
    match expr.kind() {
        ExprKind::App(a, b) | ExprKind::Lam(_, a, b) | ExprKind::Pi(_, a, b) => vec![a, b],
        ExprKind::Let(_, a, b, c, _) => vec![a, b, c],
        ExprKind::Proj(_, _, a) | ExprKind::MData(_, a) | ExprKind::Squash(a) => vec![a],
        ExprKind::CubicalPath { ty, left, right } => vec![ty, left, right],
        ExprKind::CubicalPathLam { body } => vec![body],
        ExprKind::CubicalPathApp { path, arg } => vec![path, arg],
        ExprKind::CubicalHComp { ty, phi, u, base } => vec![ty, phi, u, base],
        ExprKind::CubicalTransp { ty, phi, base } => vec![ty, phi, base],
        ExprKind::CubicalCoe { ty, r, s, base } => vec![ty, r, s, base],
        ExprKind::ZFCSet(set) => match set {
            ZFCSetExpr::Empty | ZFCSetExpr::Infinity => vec![],
            ZFCSetExpr::Singleton(a)
            | ZFCSetExpr::Union(a)
            | ZFCSetExpr::PowerSet(a)
            | ZFCSetExpr::Choice(a) => vec![a],
            ZFCSetExpr::Pair(a, b) => vec![a, b],
            ZFCSetExpr::Separation { set, pred } => vec![set, pred],
            ZFCSetExpr::Replacement { set, func } => vec![set, func],
        },
        ExprKind::ZFCMem { element, set } => vec![element, set],
        ExprKind::ZFCComprehension { domain, pred } => vec![domain, pred],
        ExprKind::BVar(_)
        | ExprKind::FVar(_)
        | ExprKind::Sort(_)
        | ExprKind::Const(..)
        | ExprKind::Lit(_)
        | ExprKind::SProp
        | ExprKind::CubicalInterval
        | ExprKind::CubicalI0
        | ExprKind::CubicalI1 => vec![],
    }
}

fn inputs() -> [Arc<Expr>; 4] {
    std::array::from_fn(|i| Arc::new(Expr::bvar(i as u32 + 1)))
}

struct SuppliedArc<'a> {
    target: &'a Arc<Expr>,
    replacement: &'a Arc<Expr>,
    events: Vec<Hook>,
}

impl ExprFolderOpt for SuppliedArc<'_> {
    fn fold_expr_arc_opt(&mut self, expr: &Arc<Expr>) -> Option<Arc<Expr>> {
        self.events.push(Hook::Ordinary);
        Arc::ptr_eq(expr, self.target).then(|| self.replacement.clone())
    }

    fn fold_binder_body_arc_opt(&mut self, expr: &Arc<Expr>) -> Option<Arc<Expr>> {
        self.events.push(Hook::Binder);
        Arc::ptr_eq(expr, self.target).then(|| self.replacement.clone())
    }
}

#[test]
fn changed_arc_is_preserved_in_every_child_slot() {
    let input = inputs();
    let replacement = Arc::new(Expr::app(Expr::fvar(FVarId::new(99)), Expr::bvar(9)));
    let fixtures = cases(&input);
    assert_eq!(fixtures.len(), 22);
    assert_eq!(
        fixtures.iter().map(|(_, roles)| roles.len()).sum::<usize>(),
        43
    );
    assert_eq!(
        fixtures
            .iter()
            .flat_map(|(_, roles)| roles.iter())
            .filter(|role| **role == Hook::Binder)
            .count(),
        7
    );
    for (case, (expr, roles)) in fixtures.iter().enumerate() {
        assert_eq!(children(expr).len(), roles.len());
        for slot in 0..roles.len() {
            let mut folder = SuppliedArc {
                target: &input[slot],
                replacement: &replacement,
                events: vec![],
            };
            let result = folder
                .fold_expr_opt(expr)
                .expect("selected child must change");
            assert_eq!(folder.events.as_slice(), *roles, "case {case}, slot {slot}");
            let mut expected_children = input.clone();
            expected_children[slot] = replacement.clone();
            let expected = &cases(&expected_children)[case].0;
            assert_eq!(&result, expected, "constructor metadata, case {case}");
            assert_eq!(result.loose_bvar_range(), expected.loose_bvar_range());
            assert_eq!(result.has_fvar_quick(), expected.has_fvar_quick());
            for (position, child) in children(&result).iter().enumerate() {
                assert!(
                    Arc::ptr_eq(child, &expected_children[position]),
                    "case {case}, slot {slot}, child {position}"
                );
                assert!(Arc::ptr_eq(children(expr)[position], &input[position]));
            }
        }
    }
}

#[test]
fn unchanged_children_and_root_pruning_keep_original_arcs() {
    let input = inputs();
    let absent = Arc::new(Expr::bvar(90));
    for (expr, roles) in cases(&input) {
        let mut folder = SuppliedArc {
            target: &absent,
            replacement: &absent,
            events: vec![],
        };
        assert!(folder.fold_expr_opt(&expr).is_none());
        assert_eq!(folder.events, roles);
        for (i, child) in children(&expr).iter().enumerate() {
            assert!(Arc::ptr_eq(child, &input[i]));
        }
    }
    struct Pruned;
    impl ExprFolderOpt for Pruned {
        fn should_descend(&self, _: &Expr) -> bool {
            false
        }
        fn fold_expr_arc_opt(&mut self, _: &Arc<Expr>) -> Option<Arc<Expr>> {
            panic!("pruned child visited")
        }
        fn fold_binder_body_arc_opt(&mut self, _: &Arc<Expr>) -> Option<Arc<Expr>> {
            panic!("pruned binder visited")
        }
        fn fold_bvar_opt(&mut self, _: u32) -> Option<Expr> {
            panic!("pruned leaf visited")
        }
    }
    for (expr, _) in cases(&input) {
        assert!(Pruned.fold_expr_opt(&expr).is_none());
    }
    assert!(Pruned.fold_expr_opt(&Expr::bvar(0)).is_none());

    struct LegacyPruned;
    impl ExprFolderOpt for LegacyPruned {
        fn should_descend(&self, _: &Expr) -> bool {
            false
        }
        fn fold_bvar_opt(&mut self, _: u32) -> Option<Expr> {
            panic!("legacy guard was bypassed")
        }
    }
    assert!(LegacyPruned.fold_expr_arc_opt(&input[0]).is_none());
    assert!(LegacyPruned.fold_binder_body_arc_opt(&input[0]).is_none());

    struct Noop;
    impl ExprFolderOpt for Noop {}
    let leaves = [
        Expr::bvar(3),
        Expr::fvar(FVarId::new(5)),
        Expr::sort(Level::zero()),
        Expr::const_(Name::from_string("leaf"), vec![Level::zero()]),
        Expr::nat_lit(7),
        ek(ExprKind::SProp),
        ek(ExprKind::CubicalInterval),
        ek(ExprKind::CubicalI0),
        ek(ExprKind::CubicalI1),
        ek(ExprKind::ZFCSet(ZFCSetExpr::Empty)),
        ek(ExprKind::ZFCSet(ZFCSetExpr::Infinity)),
    ];
    for leaf in leaves {
        assert!(Noop.fold_expr_opt(&leaf).is_none());
    }
}

#[test]
fn arc_defaults_preserve_legacy_dispatch_and_binder_depth() {
    #[derive(Default)]
    struct Legacy {
        depth: u32,
        events: Vec<(Hook, u32)>,
    }
    impl ExprFolderOpt for Legacy {
        fn fold_expr_opt(&mut self, expr: &Expr) -> Option<Expr> {
            if let ExprKind::BVar(idx) = expr.kind() {
                self.events.push((Hook::Ordinary, self.depth));
                return Some(Expr::bvar(idx + 10 + self.depth));
            }
            stack_safe(|| self.fold_expr_opt_inner(expr))
        }
        fn fold_binder_body_opt(&mut self, expr: &Expr) -> Option<Expr> {
            self.events.push((Hook::Binder, self.depth));
            self.depth += 1;
            let result = self.fold_expr_opt(expr);
            self.depth -= 1;
            result
        }
    }
    let input = inputs();
    for (case, (expr, roles)) in cases(&input).into_iter().enumerate() {
        let mut folder = Legacy::default();
        let result = folder
            .fold_expr_opt(&expr)
            .expect("legacy override changes children");
        let mut expected = Vec::new();
        for role in roles {
            if *role == Hook::Binder {
                expected.push((Hook::Binder, 0));
            }
            expected.push((Hook::Ordinary, u32::from(*role == Hook::Binder)));
        }
        assert_eq!(folder.events, expected, "case {case}");
        assert_eq!(folder.depth, 0);
        for (slot, child) in children(&result).iter().enumerate() {
            assert_eq!(
                child.as_ref(),
                &Expr::bvar(slot as u32 + 11 + u32::from(roles[slot] == Hook::Binder))
            );
        }
    }
    struct Leaf;
    impl ExprFolderOpt for Leaf {
        fn fold_bvar_opt(&mut self, index: u32) -> Option<Expr> {
            Some(Expr::bvar(index + 1))
        }
    }
    assert_eq!(
        Leaf.fold_expr_arc_opt(&input[0]).unwrap().as_ref(),
        &Expr::bvar(2)
    );
    assert_eq!(
        Leaf.fold_binder_body_arc_opt(&input[0]).unwrap().as_ref(),
        &Expr::bvar(2)
    );
}

#[test]
fn legacy_extension_hooks_remain_virtual() {
    struct Override {
        level: u8,
        calls: Vec<u8>,
    }
    impl ExprFolderOpt for Override {
        fn fold_expr_opt_inner(&mut self, expr: &Expr) -> Option<Expr> {
            self.calls.push(0);
            if self.level == 0 {
                Some(Expr::bvar(100))
            } else {
                self.fold_expr_opt_inner_full(expr)
            }
        }
        fn fold_expr_opt_extensions(&mut self, expr: &Expr) -> Option<Expr> {
            self.calls.push(1);
            if self.level == 1 {
                Some(Expr::bvar(101))
            } else {
                self.fold_expr_opt_zfc(expr)
            }
        }
        fn fold_expr_opt_zfc(&mut self, expr: &Expr) -> Option<Expr> {
            self.calls.push(2);
            if self.level == 2 {
                Some(Expr::bvar(102))
            } else {
                let ExprKind::ZFCSet(set) = expr.kind() else {
                    panic!("expected set")
                };
                self.fold_zfc_set_expr_opt(set)
                    .map(|set| ek(ExprKind::ZFCSet(set)))
            }
        }
        fn fold_zfc_set_expr_opt(&mut self, _: &ZFCSetExpr) -> Option<ZFCSetExpr> {
            self.calls.push(3);
            Some(ZFCSetExpr::Singleton(Arc::new(Expr::bvar(103))))
        }
    }
    let expr = Arc::new(ek(ExprKind::ZFCSet(ZFCSetExpr::Empty)));
    for level in 0..=3 {
        let mut folder = Override {
            level,
            calls: vec![],
        };
        let result = folder
            .fold_expr_arc_opt(&expr)
            .expect("legacy extension override");
        assert_eq!(folder.calls, (0..=level).collect::<Vec<_>>());
        let expected = if level == 3 {
            ek(ExprKind::ZFCSet(ZFCSetExpr::Singleton(Arc::new(
                Expr::bvar(103),
            ))))
        } else {
            Expr::bvar(100 + u32::from(level))
        };
        assert_eq!(result.as_ref(), &expected);
    }
}

#[test]
fn repeated_changed_child_keeps_one_supplied_allocation() {
    let shared = Arc::new(Expr::bvar(0));
    let replacement = Arc::new(Expr::app(Expr::bvar(7), Expr::bvar(8)));
    let input = ek(ExprKind::App(shared.clone(), shared.clone()));
    let mut folder = SuppliedArc {
        target: &shared,
        replacement: &replacement,
        events: vec![],
    };
    let result = folder.fold_expr_opt(&input).expect("both slots change");
    let ExprKind::App(a, b) = result.kind() else {
        panic!("expected app")
    };
    assert!(Arc::ptr_eq(a, b));
    assert!(Arc::ptr_eq(a, &replacement));
    assert_eq!(folder.events, [Hook::Ordinary, Hook::Ordinary]);
}
