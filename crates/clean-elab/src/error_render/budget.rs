// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bound diagnostic work BEFORE Display or private-name folding can expand a DAG.
//! Count occurrences, not unique pointers: printing repeats shared children.
//! This is rendering policy only; it must never decide equality or proof status.

use clean_kernel::expr::{Literal, MDataValue, ZFCSetExpr};
use clean_kernel::name::{Name, NameInner};
use clean_kernel::{Expr, ExprKind, Level};

const NODES: usize = 1024;
const DEPTH: usize = 64;
const PAYLOAD_BYTES: usize = 8192;

pub(super) fn fits(expr: &Expr) -> bool {
    Budget {
        nodes: NODES,
        bytes: PAYLOAD_BYTES,
    }
    .expr(expr, 0)
    .is_some()
}

struct Budget {
    nodes: usize,
    bytes: usize,
}

impl Budget {
    fn node(&mut self, depth: usize) -> Option<()> {
        if depth > DEPTH {
            return None;
        }
        self.nodes = self.nodes.checked_sub(1)?;
        Some(())
    }

    fn bytes(&mut self, size: usize) -> Option<()> {
        self.bytes = self.bytes.checked_sub(size)?;
        Some(())
    }

    fn name(&mut self, mut name: &Name, mut depth: usize) -> Option<()> {
        loop {
            self.node(depth)?;
            match name.inner() {
                NameInner::Anon => return Some(()),
                NameInner::Str(parent, text) => {
                    self.bytes(text.len())?;
                    name = parent;
                }
                NameInner::Num(parent, _) => name = parent,
            }
            depth += 1;
        }
    }

    fn level(&mut self, level: &Level, depth: usize) -> Option<()> {
        self.node(depth)?;
        match level {
            Level::Zero => Some(()),
            Level::Param(name) => self.name(name, depth + 1),
            Level::Succ(inner) => self.level(inner, depth + 1),
            Level::Max(a, b) | Level::IMax(a, b) => {
                self.level(a, depth + 1)?;
                self.level(b, depth + 1)
            }
        }
    }

    fn expr(&mut self, expr: &Expr, depth: usize) -> Option<()> {
        self.node(depth)?;
        let d = depth + 1;
        match expr.kind() {
            ExprKind::BVar(_)
            | ExprKind::FVar(_)
            | ExprKind::SProp
            | ExprKind::CubicalInterval
            | ExprKind::CubicalI0
            | ExprKind::CubicalI1 => {}
            ExprKind::Sort(level) => self.level(level, d)?,
            ExprKind::Const(name, levels) => {
                self.name(name, d)?;
                // Check length before iterating even when levels are hidden by Display.
                if levels.len() > self.nodes {
                    return None;
                }
                for level in levels {
                    self.level(level, d)?;
                }
            }
            ExprKind::Lit(Literal::String(text)) => self.bytes(text.len())?,
            ExprKind::Lit(Literal::Nat(n)) => {
                self.bytes(n.limbs().len().checked_mul(8)?)?;
            }
            ExprKind::App(a, b)
            | ExprKind::Lam(_, a, b)
            | ExprKind::Pi(_, a, b)
            | ExprKind::CubicalPathApp { path: a, arg: b }
            | ExprKind::ZFCMem { element: a, set: b }
            | ExprKind::ZFCComprehension { domain: a, pred: b } => {
                self.expr(a, d)?;
                self.expr(b, d)?;
            }
            ExprKind::Let(name, ty, val, body, _) => {
                self.name(name, d)?;
                self.expr(ty, d)?;
                self.expr(val, d)?;
                self.expr(body, d)?;
            }
            ExprKind::Proj(name, _, inner) => {
                self.name(name, d)?;
                self.expr(inner, d)?;
            }
            ExprKind::MData(metadata, inner) => {
                // The private-name folder clones metadata; ZFC's Debug also prints it.
                if metadata.len() > self.nodes {
                    return None;
                }
                for (name, value) in metadata {
                    self.node(d)?;
                    self.name(name, d)?;
                    match value {
                        MDataValue::String(text) => self.bytes(text.len())?,
                        MDataValue::Name(name) => self.name(name, d)?,
                        MDataValue::Bool(_) | MDataValue::Nat(_) => {}
                    }
                }
                self.expr(inner, d)?;
            }
            ExprKind::Squash(inner) | ExprKind::CubicalPathLam { body: inner } => {
                self.expr(inner, d)?
            }
            ExprKind::CubicalPath { ty, left, right } => {
                self.expr(ty, d)?;
                self.expr(left, d)?;
                self.expr(right, d)?;
            }
            ExprKind::CubicalHComp { ty, phi, u, base } => {
                self.expr(ty, d)?;
                self.expr(phi, d)?;
                self.expr(u, d)?;
                self.expr(base, d)?;
            }
            ExprKind::CubicalTransp { ty, phi, base } => {
                self.expr(ty, d)?;
                self.expr(phi, d)?;
                self.expr(base, d)?;
            }
            ExprKind::CubicalCoe { ty, r, s, base } => {
                self.expr(ty, d)?;
                self.expr(r, d)?;
                self.expr(s, d)?;
                self.expr(base, d)?;
            }
            ExprKind::ZFCSet(set) => match set {
                ZFCSetExpr::Empty | ZFCSetExpr::Infinity => {}
                ZFCSetExpr::Singleton(e)
                | ZFCSetExpr::Union(e)
                | ZFCSetExpr::PowerSet(e)
                | ZFCSetExpr::Choice(e) => self.expr(e, d)?,
                ZFCSetExpr::Pair(a, b)
                | ZFCSetExpr::Separation { set: a, pred: b }
                | ZFCSetExpr::Replacement { set: a, func: b } => {
                    self.expr(a, d)?;
                    self.expr(b, d)?;
                }
            },
        }
        Some(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::error_render::term;
    use crate::unify::{MetaState, Unifier, UnifyResult};
    use clean_kernel::expr::BigNat;
    use clean_kernel::BinderData;
    use std::sync::Arc;
    use std::time::Instant;

    fn shared(depth: usize) -> Expr {
        let mut e = Arc::new(Expr::const_(Name::from_string("P"), vec![]));
        for _ in 0..depth {
            e = Arc::new(Expr::app_arc(e.clone(), e));
        }
        e.as_ref().clone()
    }

    fn omitted(expr: &Expr) {
        assert_eq!(term(expr), "<term omitted: rendering budget exceeded>");
    }

    #[test]
    fn small_diagnostics_keep_the_existing_display_and_private_names() {
        let p = Expr::const_(Name::from_string("P"), vec![]);
        for e in [
            p.clone(),
            Expr::app(p.clone(), p.clone()),
            Expr::pi(BinderData::default(), p.clone(), p.clone()),
            Expr::lam(BinderData::default(), p, Expr::bvar(0)),
            Expr::from_kind(ExprKind::Lit(Literal::String("a\nλ".into()))),
        ] {
            assert_eq!(term(&e), e.to_string());
        }
        let private = Expr::const_(Name::from_string("_private.Example.0.helper"), vec![]);
        assert_eq!(term(&private), "helper");
    }

    #[test]
    fn shared_terms_exhaust_occurrences_before_any_formatting() {
        // Only 41 allocations, but more than a trillion printed occurrences.
        // The budget must not deduplicate pointers or format before truncating.
        let big = shared(40);
        let mut budget = Budget {
            nodes: NODES,
            bytes: PAYLOAD_BYTES,
        };
        assert!(budget.expr(&big, 0).is_none());
        assert_eq!(budget.nodes, 0);
        omitted(&big);
        // Also exercise the private-name fold's former exponential path.
        let private = Expr::app(
            Expr::const_(Name::from_string("_private.Example.0.f"), vec![]),
            big,
        );
        omitted(&private);
    }

    #[test]
    fn deep_terms_and_large_leaves_are_checked_before_display() {
        let mut deep = Expr::bvar(0);
        for _ in 0..1000 {
            deep = Expr::app(deep, Expr::bvar(0));
        }
        omitted(&deep);
        omitted(&Expr::const_(
            Name::from_string(&"x".repeat(PAYLOAD_BYTES + 1)),
            vec![],
        ));
        omitted(&Expr::from_kind(ExprKind::Lit(Literal::String(
            "x".repeat(PAYLOAD_BYTES + 1).into(),
        ))));
        omitted(&Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Big(
            vec![1; PAYLOAD_BYTES],
        )))));
        let mut level = Level::zero();
        for _ in 0..1000 {
            level = Level::Succ(level.into());
        }
        omitted(&Expr::sort(level));
        let mut level = Level::zero();
        for _ in 0..40 {
            let child = Arc::new(level);
            level = Level::Max(child.clone().into(), child.into());
        }
        // Expr::sort hashes a level before rendering; exercise the preflight
        // directly here so constructing the fixture does not expand this DAG.
        let mut budget = Budget {
            nodes: NODES,
            bytes: PAYLOAD_BYTES,
        };
        assert!(budget.level(&level, 0).is_none());
        assert_eq!(budget.nodes, 0);
    }

    #[test]
    fn payload_boundary_and_hidden_children_cannot_bypass_the_budget() {
        let text = Expr::from_kind(ExprKind::Lit(Literal::String(
            "\0".repeat(PAYLOAD_BYTES).into(),
        )));
        assert!(fits(&text));
        assert_eq!(term(&text), text.to_string());
        let big = Arc::new(shared(40));
        omitted(&Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Pair(
            big.clone(),
            big,
        ))));
        let metadata = vec![(
            Name::from_string("tag"),
            MDataValue::String("x".repeat(PAYLOAD_BYTES + 1).into()),
        )];
        omitted(&Expr::mdata(metadata, Expr::bvar(0)));
        let levels = vec![Level::zero(); NODES + 1];
        omitted(&Expr::const_(Name::from_string("P"), levels));
        let mut name = Name::anon();
        for _ in 0..1000 {
            name = name.str("x");
        }
        omitted(&Expr::const_(name, vec![]));
    }

    #[test]
    fn large_mismatch_still_fails_and_small_mismatch_is_unchanged() {
        let mut metas = MetaState::new();
        let mut unifier = Unifier::new(&mut metas);
        let big = shared(40);
        let prop = Expr::sort(Level::zero());
        assert!(matches!(unifier.unify(&big, &big), UnifyResult::Success));
        let UnifyResult::Failure(message) = unifier.unify(&big, &prop) else {
            panic!("a large application must still fail against a sort");
        };
        assert_eq!(message, "cannot unify an application with a sort: <term omitted: rendering budget exceeded> vs Prop");
        let small = Expr::const_(Name::from_string("P"), vec![]);
        let UnifyResult::Failure(message) = unifier.unify(&small, &prop) else {
            panic!("a constant must still fail against a sort");
        };
        assert_eq!(message, "cannot unify a constant with a sort: P vs Prop");
    }

    #[test]
    fn measure_shared_term_rendering() {
        // A safe baseline with the old renderer, plus a DAG too large to print.
        // Report timings; correctness uses deterministic budgets, not a flaky deadline.
        let moderate = shared(12);
        let start = Instant::now();
        let baseline = std::hint::black_box(moderate.to_string());
        let baseline_time = start.elapsed();
        let big = shared(40);
        let start = Instant::now();
        for _ in 0..1000 {
            std::hint::black_box(term(std::hint::black_box(&big)));
        }
        let bounded_time = start.elapsed();
        omitted(&moderate);
        eprintln!("error-term measurement: old depth=12 bytes={} time={baseline_time:?}; bounded depth=40 iterations=1000 total={bounded_time:?}", baseline.len());
    }
}
