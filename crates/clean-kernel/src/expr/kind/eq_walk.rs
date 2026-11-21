// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! One ordered structural walk, using borrowed enter/complete continuations.
//!
//! A pair is memoized only after every ordered field has compared equal. The
//! pointer/metadata gates, shared-pair gate and 64-completion threshold retain
//! the former recursive walk's decisions and accounting. Both borrowed roots
//! keep every memoized address live throughout this single comparison.
//! Expressions are immutable after construction: no retained address can
//! change meaning, be freed or be recycled during the borrowed comparison.
//! A false field ends the conjunction, so false pairs need no memo entries.
//!
//! ExprKind's explicit Arc children use this worklist. Level, metadata and
//! ZFCSet delegated equality remain unchanged; this is not a blanket claim
//! that those separately delegated comparisons are recursion-free.

use super::{Expr, ExprKind};
use crate::expr::stack_safe;
use smallvec::SmallVec;
use std::sync::Arc;

#[cfg(test)]
#[path = "eq_walk_tests.rs"]
mod tests;

/// Work is borrowed: queuing a child never clones an Arc or changes its
/// strong count. Eight inline slots keep ordinary small probes heap-free.
enum Task<'a> {
    Enter(&'a Expr, &'a Expr, bool),
    Arcs(&'a Arc<Expr>, &'a Arc<Expr>),
    Kinds(&'a ExprKind, &'a ExprKind),
    Complete((usize, usize), bool),
    Bool(bool, bool),
}

type Tasks<'a> = SmallVec<[Task<'a>; 8]>;

/// A private, single-use walk. Only exprs/kinds are production entry points;
/// release parents cannot create a walk or retain its pointer-pair state.
pub(crate) struct ExprEqWalk {
    proven: Option<hashbrown::HashSet<(usize, usize)>>,
    completed: u32,
    /// Node pairs entered; charged to the kernel work meter when the walk ends.
    visits: u64,
    #[cfg(test)]
    max_pending: usize,
    #[cfg(test)]
    spilled: bool,
}

const EXPR_EQ_MEMO_AFTER: u32 = 64;

impl ExprEqWalk {
    /// Every production comparison pays the work meter for the node pairs it
    /// entered: a cache probe whose hashes agree walks its keys, and that walk
    /// is as long as the key (see `crate::work_meter`). A `false` with equal
    /// root metadata is recorded as a collision of the metadata word.
    pub(crate) fn exprs(a: &Expr, b: &Expr) -> bool {
        let mut walk = Self::new();
        let equal = walk.root_exprs(a, b);
        // The root's metadata gate refuses before entering, so a walk that
        // entered anything had equal root metadata words.
        crate::work_meter::charge_equality(walk.visits, !equal);
        equal
    }

    pub(crate) fn kinds(a: &ExprKind, b: &ExprKind) -> bool {
        let mut walk = Self::new();
        let equal = walk.kind_pair(a, b);
        // A bare kind pair has no root metadata word to have collided on.
        crate::work_meter::charge_equality(walk.visits, false);
        equal
    }

    fn new() -> Self {
        Self {
            proven: None,
            completed: 0,
            visits: 0,
            #[cfg(test)]
            max_pending: 0,
            #[cfg(test)]
            spilled: false,
        }
    }

    fn root_exprs(&mut self, a: &Expr, b: &Expr) -> bool {
        self.run(Task::Enter(a, b, false))
    }

    fn kind_pair(&mut self, a: &ExprKind, b: &ExprKind) -> bool {
        self.run(Task::Kinds(a, b))
    }

    // Existing parent fixtures observe the walk through test-only adapters.
    // None of these entry points or state observations exists in release.
    #[cfg(test)]
    pub(super) fn test_new() -> Self {
        Self::new()
    }

    #[cfg(test)]
    pub(super) fn test_root_exprs(&mut self, a: &Expr, b: &Expr) -> bool {
        self.root_exprs(a, b)
    }

    #[cfg(test)]
    pub(super) fn test_kind_pair(&mut self, a: &ExprKind, b: &ExprKind) -> bool {
        self.kind_pair(a, b)
    }

    #[cfg(test)]
    pub(super) fn test_visits(&self) -> u64 {
        self.visits
    }

    #[cfg(test)]
    pub(super) fn test_has_memo(&self) -> bool {
        self.proven.is_some()
    }

    fn run(&mut self, first: Task<'_>) -> bool {
        let mut pending = Tasks::new();
        pending.push(first);
        while let Some(task) = pending.pop() {
            match task {
                Task::Enter(a, b, memoizable) => {
                    if !self.enter(a, b, memoizable, &mut pending) {
                        return false;
                    }
                }
                Task::Arcs(a, b) => {
                    if !Arc::ptr_eq(a, b) {
                        // Only pairs shared on both sides can be reached again
                        // without a shared ancestor already providing a memo.
                        // Counts choose whether to memoize, never a verdict.
                        let shared = Arc::strong_count(a) > 1 && Arc::strong_count(b) > 1;
                        if !self.enter(a, b, shared, &mut pending) {
                            return false;
                        }
                    }
                }
                Task::Kinds(a, b) => {
                    if !Self::schedule_kind(a, b, &mut pending) {
                        return false;
                    }
                }
                Task::Complete(key, memoizable) => {
                    self.completed = self.completed.saturating_add(1);
                    if memoizable && self.completed > EXPR_EQ_MEMO_AFTER {
                        self.proven.get_or_insert_with(Default::default).insert(key);
                    }
                }
                Task::Bool(a, b) => {
                    if a != b {
                        return false;
                    }
                }
            }
            #[cfg(test)]
            {
                self.max_pending = self.max_pending.max(pending.len());
                self.spilled |= pending.spilled();
            }
        }
        true
    }

    fn enter<'a>(
        &mut self,
        a: &'a Expr,
        b: &'a Expr,
        memoizable: bool,
        pending: &mut Tasks<'a>,
    ) -> bool {
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
            // SOUNDNESS: this exact live pair entered the single-use memo
            // only after all of its ordered structural fields returned true.
            return true;
        }
        self.visits = self.visits.saturating_add(1);
        // LIFO: completion happens only after this kind's whole ordered
        // conjunction succeeds. A false field aborts before any ancestor
        // completion can enter the proven-pair memo.
        pending.push(Task::Complete(key, memoizable));
        Self::schedule_kind(&a.kind, &b.kind, pending)
    }

    fn children<'a, const N: usize>(
        pending: &mut Tasks<'a>,
        pairs: [(&'a Arc<Expr>, &'a Arc<Expr>); N],
    ) {
        for (a, b) in pairs.into_iter().rev() {
            pending.push(Task::Arcs(a, b));
        }
    }

    /// The former conjunction order, including scalar checks before children
    /// and Let's non-dependent flag after its body.
    fn schedule_kind<'a>(a: &'a ExprKind, b: &'a ExprKind, pending: &mut Tasks<'a>) -> bool {
        match (a, b) {
            (ExprKind::BVar(a), ExprKind::BVar(b)) => a == b,
            (ExprKind::FVar(a), ExprKind::FVar(b)) => a == b,
            (ExprKind::Sort(a), ExprKind::Sort(b)) => a == b,
            (ExprKind::Const(n1, l1), ExprKind::Const(n2, l2)) => n1 == n2 && l1 == l2,
            (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => {
                Self::children(pending, [(f1, f2), (a1, a2)]);
                true
            }
            (ExprKind::Lam(b1, t1, bo1), ExprKind::Lam(b2, t2, bo2))
            | (ExprKind::Pi(b1, t1, bo1), ExprKind::Pi(b2, t2, bo2)) => {
                if b1 != b2 {
                    return false;
                }
                Self::children(pending, [(t1, t2), (bo1, bo2)]);
                true
            }
            (ExprKind::Let(n1, t1, v1, bo1, d1), ExprKind::Let(n2, t2, v2, bo2, d2)) => {
                if n1 != n2 {
                    return false;
                }
                pending.push(Task::Bool(*d1, *d2));
                Self::children(pending, [(t1, t2), (v1, v2), (bo1, bo2)]);
                true
            }
            (ExprKind::Lit(a), ExprKind::Lit(b)) => a == b,
            (ExprKind::Proj(n1, i1, e1), ExprKind::Proj(n2, i2, e2)) => {
                if n1 != n2 || i1 != i2 {
                    return false;
                }
                Self::children(pending, [(e1, e2)]);
                true
            }
            (ExprKind::MData(m1, e1), ExprKind::MData(m2, e2)) => {
                if m1 != m2 {
                    return false;
                }
                Self::children(pending, [(e1, e2)]);
                true
            }
            (ExprKind::SProp, ExprKind::SProp)
            | (ExprKind::CubicalInterval, ExprKind::CubicalInterval)
            | (ExprKind::CubicalI0, ExprKind::CubicalI0)
            | (ExprKind::CubicalI1, ExprKind::CubicalI1) => true,
            (ExprKind::Squash(e1), ExprKind::Squash(e2))
            | (ExprKind::CubicalPathLam { body: e1 }, ExprKind::CubicalPathLam { body: e2 }) => {
                Self::children(pending, [(e1, e2)]);
                true
            }
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
            ) => {
                Self::children(pending, [(t1, t2), (l1, l2), (r1, r2)]);
                true
            }
            (
                ExprKind::CubicalPathApp { path: p1, arg: a1 },
                ExprKind::CubicalPathApp { path: p2, arg: a2 },
            ) => {
                Self::children(pending, [(p1, p2), (a1, a2)]);
                true
            }
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
            ) => {
                Self::children(pending, [(t1, t2), (p1, p2), (u1, u2), (ba1, ba2)]);
                true
            }
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
            ) => {
                Self::children(pending, [(t1, t2), (p1, p2), (ba1, ba2)]);
                true
            }
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
            ) => {
                Self::children(pending, [(t1, t2), (r1, r2), (s1, s2), (ba1, ba2)]);
                true
            }
            // Deliberately delegated, exactly as before. Nested ZFCSet Expr
            // edges start their own Expr equality walk; no broader recursion
            // or DAG-work improvement is claimed for that delegation.
            (ExprKind::ZFCSet(a), ExprKind::ZFCSet(b)) => stack_safe(|| a == b),
            (
                ExprKind::ZFCMem {
                    element: e1,
                    set: s1,
                },
                ExprKind::ZFCMem {
                    element: e2,
                    set: s2,
                },
            ) => {
                Self::children(pending, [(e1, e2), (s1, s2)]);
                true
            }
            (
                ExprKind::ZFCComprehension {
                    domain: d1,
                    pred: p1,
                },
                ExprKind::ZFCComprehension {
                    domain: d2,
                    pred: p2,
                },
            ) => {
                Self::children(pending, [(d1, d2), (p1, p2)]);
                true
            }
            _ => false,
        }
    }
}
