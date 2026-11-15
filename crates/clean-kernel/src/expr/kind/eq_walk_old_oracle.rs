// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Literal pre-worklist comparator: independent ordered/accounting oracle.
//! Production never compiles this test-only helper. Its Arc-child walk and
//! postorder memo body are retained, including the segmented-stack guard.

use super::super::*;
use crate::expr::stack_safe;

#[cfg(not(kani))]
pub(super) struct OldWalk {
    /// Node pairs whose comparison has returned `true` so far in this walk.
    pub(super) proven: Option<hashbrown::HashSet<(usize, usize)>>,
    /// Comparisons completed with `true`; the memo is only allocated once a
    /// walk is big enough to be worth it, so the common small comparison (a
    /// cache key probe, a head check) stays allocation-free.
    pub(super) completed: u32,
    /// Structural node comparisons entered (the work measure the regression
    /// test bounds). Counts every node comparison that got past the metadata
    /// pre-filter and both fast paths.
    #[cfg(test)]
    pub(super) visits: u64,
}

/// Completed comparisons after which a walk starts memoizing proven pairs.
/// Below it, re-walking a repeated subterm costs at most this many visits.
#[cfg(not(kani))]
const EXPR_EQ_MEMO_AFTER: u32 = 64;

#[cfg(not(kani))]
impl OldWalk {
    /// Structural equality of two root expressions, metadata pre-filter
    /// first, in one fresh walk.
    pub(crate) fn exprs(a: &Expr, b: &Expr) -> bool {
        Self::new().root_exprs(a, b)
    }

    /// The derived structural equality of two `ExprKind`s, in one fresh walk.
    pub(crate) fn kinds(a: &ExprKind, b: &ExprKind) -> bool {
        Self::new().kind_pair(a, b)
    }

    /// Private: a walk's memo is only sound while the two roots it was built
    /// for are borrowed, so no caller may hold one across comparisons.
    pub(super) fn new() -> Self {
        OldWalk {
            proven: None,
            completed: 0,
            #[cfg(test)]
            visits: 0,
        }
    }

    #[inline]
    fn arcs(&mut self, a: &Arc<Expr>, b: &Arc<Expr>) -> bool {
        // Only a pair shared on BOTH sides can be reached again later in this
        // walk, so only such a pair is worth remembering (Lean's
        // `is_shared(a) && is_shared(b)` gate): a node held by one reference
        // has one parent, so it is re-reached only through a re-reached
        // ancestor, whose pair is the one remembered. The count only decides
        // WHETHER to remember a proven pair, never a verdict.
        Arc::ptr_eq(a, b) || self.nodes(a, b, Arc::strong_count(a) > 1 && Arc::strong_count(b) > 1)
    }

    pub(super) fn root_exprs(&mut self, a: &Expr, b: &Expr) -> bool {
        self.nodes(a, b, false)
    }

    fn nodes(&mut self, a: &Expr, b: &Expr, memoizable: bool) -> bool {
        // Metadata pre-filter: reject mismatches in O(1) using the full cached
        // metadata word (hash/depth/flags/loose_bvar_range).
        if a.meta != b.meta {
            return false;
        }
        let key = (
            std::ptr::from_ref(a) as usize,
            std::ptr::from_ref(b) as usize,
        );
        if memoizable
            && self
                .proven
                .as_ref()
                .is_some_and(|proven| proven.contains(&key))
        {
            return true;
        }
        #[cfg(test)]
        {
            self.visits += 1;
        }
        // Every child comparison re-enters here, so keep the recursive descent
        // behind the segmented-stack guard used by the other kernel walks.
        let equal = stack_safe(|| self.kind_pair(&a.kind, &b.kind));
        if equal {
            self.completed = self.completed.saturating_add(1);
            if memoizable && self.completed > EXPR_EQ_MEMO_AFTER {
                self.proven.get_or_insert_with(Default::default).insert(key);
            }
        }
        equal
    }

    /// The derived structural equality of two `ExprKind`s, exactly, with every
    /// `Arc<Expr>` child compared through this walk. Non-`Arc` fields compare
    /// with `==`, identical to the derived impl.
    pub(super) fn kind_pair(&mut self, a: &ExprKind, b: &ExprKind) -> bool {
        match (a, b) {
            (ExprKind::BVar(a), ExprKind::BVar(b)) => a == b,
            (ExprKind::FVar(a), ExprKind::FVar(b)) => a == b,
            (ExprKind::Sort(a), ExprKind::Sort(b)) => a == b,
            (ExprKind::Const(n1, l1), ExprKind::Const(n2, l2)) => n1 == n2 && l1 == l2,
            (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => {
                self.arcs(f1, f2) && self.arcs(a1, a2)
            }
            (ExprKind::Lam(b1, t1, bo1), ExprKind::Lam(b2, t2, bo2)) => {
                b1 == b2 && self.arcs(t1, t2) && self.arcs(bo1, bo2)
            }
            (ExprKind::Pi(b1, t1, bo1), ExprKind::Pi(b2, t2, bo2)) => {
                b1 == b2 && self.arcs(t1, t2) && self.arcs(bo1, bo2)
            }
            (ExprKind::Let(n1, t1, v1, bo1, d1), ExprKind::Let(n2, t2, v2, bo2, d2)) => {
                n1 == n2
                    && self.arcs(t1, t2)
                    && self.arcs(v1, v2)
                    && self.arcs(bo1, bo2)
                    && d1 == d2
            }
            (ExprKind::Lit(a), ExprKind::Lit(b)) => a == b,
            (ExprKind::Proj(n1, i1, e1), ExprKind::Proj(n2, i2, e2)) => {
                n1 == n2 && i1 == i2 && self.arcs(e1, e2)
            }
            (ExprKind::MData(m1, e1), ExprKind::MData(m2, e2)) => m1 == m2 && self.arcs(e1, e2),
            (ExprKind::SProp, ExprKind::SProp) => true,
            (ExprKind::Squash(e1), ExprKind::Squash(e2)) => self.arcs(e1, e2),
            (ExprKind::CubicalInterval, ExprKind::CubicalInterval) => true,
            (ExprKind::CubicalI0, ExprKind::CubicalI0) => true,
            (ExprKind::CubicalI1, ExprKind::CubicalI1) => true,
            (
                ExprKind::CubicalPath {
                    ty: t1,
                    left: l1,
                    right: r1,
                },
                ExprKind::CubicalPath {
                    ty: t2,
                    left: l2,
                    right: r2,
                },
            ) => self.arcs(t1, t2) && self.arcs(l1, l2) && self.arcs(r1, r2),
            (ExprKind::CubicalPathLam { body: b1 }, ExprKind::CubicalPathLam { body: b2 }) => {
                self.arcs(b1, b2)
            }
            (
                ExprKind::CubicalPathApp { path: p1, arg: a1 },
                ExprKind::CubicalPathApp { path: p2, arg: a2 },
            ) => self.arcs(p1, p2) && self.arcs(a1, a2),
            (
                ExprKind::CubicalHComp {
                    ty: t1,
                    phi: p1,
                    u: u1,
                    base: ba1,
                },
                ExprKind::CubicalHComp {
                    ty: t2,
                    phi: p2,
                    u: u2,
                    base: ba2,
                },
            ) => self.arcs(t1, t2) && self.arcs(p1, p2) && self.arcs(u1, u2) && self.arcs(ba1, ba2),
            (
                ExprKind::CubicalTransp {
                    ty: t1,
                    phi: p1,
                    base: ba1,
                },
                ExprKind::CubicalTransp {
                    ty: t2,
                    phi: p2,
                    base: ba2,
                },
            ) => self.arcs(t1, t2) && self.arcs(p1, p2) && self.arcs(ba1, ba2),
            (
                ExprKind::CubicalCoe {
                    ty: t1,
                    r: r1,
                    s: s1,
                    base: ba1,
                },
                ExprKind::CubicalCoe {
                    ty: t2,
                    r: r2,
                    s: s2,
                    base: ba2,
                },
            ) => self.arcs(t1, t2) && self.arcs(r1, r2) && self.arcs(s1, s2) && self.arcs(ba1, ba2),
            (ExprKind::ZFCSet(a), ExprKind::ZFCSet(b)) => a == b,
            (
                ExprKind::ZFCMem {
                    element: e1,
                    set: s1,
                },
                ExprKind::ZFCMem {
                    element: e2,
                    set: s2,
                },
            ) => self.arcs(e1, e2) && self.arcs(s1, s2),
            (
                ExprKind::ZFCComprehension {
                    domain: d1,
                    pred: p1,
                },
                ExprKind::ZFCComprehension {
                    domain: d2,
                    pred: p2,
                },
            ) => self.arcs(d1, d2) && self.arcs(p1, p2),
            // Different variants are never equal. Enumerated tuple arms above
            // are exhaustive over same-variant pairs; any (X, Y) with X≠Y falls
            // here, matching the derived impl.
            _ => false,
        }
    }
}
