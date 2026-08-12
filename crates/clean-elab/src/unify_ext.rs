// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended unification: Miller patterns, postponed constraints, eta expansion,
//! first-order approximation, and unification trace.

// Staged Lean4-parity scaffold with no caller yet (tests included): kept per the
// keep-and-annotate doctrine — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#![allow(dead_code)]
use clean_kernel::{Expr, ExprKind, Level};

use crate::unify::{MetaId, MetaState, UnifyResult};

// ============================================================================
// Configuration & types
// ============================================================================

/// Configuration for extended unification behavior.
#[derive(Debug, Clone)]
pub(crate) struct UnifyExtConfig {
    pub(crate) max_simplify_passes: u32,
    pub(crate) eta_expansion: bool,
    pub(crate) first_order_approx: bool,
    pub(crate) trace_enabled: bool,
    pub(crate) max_postponed: usize,
}

impl Default for UnifyExtConfig {
    fn default() -> Self {
        Self {
            max_simplify_passes: 10,
            eta_expansion: true,
            first_order_approx: true,
            trace_enabled: false,
            max_postponed: 256,
        }
    }
}

/// A single entry in the unification trace.
#[derive(Debug, Clone)]
pub(crate) struct TraceEntry {
    pub(crate) kind: TraceKind,
    pub(crate) left: Expr,
    pub(crate) right: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum TraceKind {
    Attempt,
    MillerAssign,
    OccursCheckFail,
    Postpone,
    Simplify,
    EtaExpand,
    FirstOrderApprox,
    Stuck,
    Success,
    Failure,
}

/// A constraint that could not be solved immediately.
#[derive(Debug, Clone)]
pub(crate) struct PostponedConstraint {
    pub(crate) left: Expr,
    pub(crate) right: Expr,
    pub(crate) reason: StuckReason,
}

/// Why a constraint was postponed or stuck.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum StuckReason {
    BothMeta,
    NonPatternArgs,
    HigherOrder,
    PendingDelta,
}

// ============================================================================
// Extended Unifier
// ============================================================================

/// Extended unifier with Miller patterns and postponed constraints.
pub(crate) struct UnifyExt<'a> {
    metas: &'a mut MetaState,
    config: UnifyExtConfig,
    postponed: Vec<PostponedConstraint>,
    trace: Vec<TraceEntry>,
}

impl<'a> UnifyExt<'a> {
    pub(crate) fn new(metas: &'a mut MetaState, config: UnifyExtConfig) -> Self {
        Self {
            metas,
            config,
            postponed: Vec::new(),
            trace: Vec::new(),
        }
    }

    pub(crate) fn with_defaults(metas: &'a mut MetaState) -> Self {
        Self::new(metas, UnifyExtConfig::default())
    }

    pub(crate) fn postponed(&self) -> &[PostponedConstraint] {
        &self.postponed
    }
    pub(crate) fn trace(&self) -> &[TraceEntry] {
        &self.trace
    }
    pub(crate) fn postponed_count(&self) -> usize {
        self.postponed.len()
    }

    fn record(&mut self, kind: TraceKind, left: &Expr, right: &Expr) {
        if self.config.trace_enabled {
            self.trace.push(TraceEntry {
                kind,
                left: left.clone(),
                right: right.clone(),
            });
        }
    }

    // ========================================================================
    // Core
    // ========================================================================

    pub(crate) fn unify(&mut self, left: &Expr, right: &Expr) -> UnifyResult {
        let left = self.metas.instantiate(left);
        let right = self.metas.instantiate(right);
        self.record(TraceKind::Attempt, &left, &right);

        if left == right {
            self.record(TraceKind::Success, &left, &right);
            return UnifyResult::Success;
        }

        if let Some(r) = self.try_miller(&left, &right) {
            return r;
        }
        if let Some(r) = self.try_miller(&right, &left) {
            return r;
        }

        if self.config.eta_expansion {
            if let Some(r) = self.try_eta(&left, &right) {
                return r;
            }
        }

        let result = self.unify_structural(&left, &right);
        if let UnifyResult::Failure(_) = &result {
            if self.config.first_order_approx {
                if let Some(r) = self.try_fo_approx(&left, &right) {
                    return r;
                }
            }
        }
        result
    }

    pub(crate) fn unify_levels(&mut self, l1: &Level, l2: &Level) -> UnifyResult {
        // Delegates to THE shared level solver (`unify::level_solve`, U2
        // rung 3a): this secondary site previously maintained a WEAKER arm
        // subset (no rigid-preference direction, no Miller Max/IMax slice,
        // no occurs-checks) — one behavior, two entry points.
        crate::unify::level_solve::solve_level_eq(self.metas, l1, l2)
    }

    // ========================================================================
    // Miller pattern fragment
    // ========================================================================

    fn try_miller(&mut self, lhs: &Expr, rhs: &Expr) -> Option<UnifyResult> {
        let (meta_id, args) = self.decompose_meta_app(lhs)?;

        if let Some(existing) = self.metas.get_assignment(meta_id).cloned() {
            return Some(self.unify(&apply_args(&existing, &args), rhs));
        }

        if !are_distinct_bvars(&args) {
            if self.expr_has_meta(rhs) {
                self.postpone(lhs, rhs, StuckReason::NonPatternArgs);
                return Some(UnifyResult::Stuck);
            }
            // Non-pattern args, rhs is meta-free: when rhs is a
            // sort (`Prop`/`Type u`) commit a constant imitation
            // `?m := fun _ ... _ => rhs`. Sorts are structurally
            // unique (no other valid solution at this position), so
            // committing here is unambiguous and matches the gap's
            // motivating example (`?m (Const "a") = Prop`). For other
            // non-pattern shapes we still fall through to structural
            // / first-order approximation to avoid masking later
            // higher-order constraints with an overly committal
            // imitation.
            if matches!(rhs.kind(), ExprKind::Sort(_)) {
                if MetaState::occurs_in(rhs, meta_id) {
                    self.record(TraceKind::OccursCheckFail, lhs, rhs);
                    return Some(UnifyResult::Failure(format!(
                        "occurs check: ?{}",
                        meta_id.as_u64()
                    )));
                }
                let mut solution = rhs.clone();
                for _ in args.iter().rev() {
                    solution = Expr::lam(clean_kernel::BinderInfo::Default, Expr::prop(), solution);
                }
                self.metas.assign(meta_id, solution);
                self.record(TraceKind::FirstOrderApprox, lhs, rhs);
                return Some(UnifyResult::Success);
            }
            return None;
        }

        if MetaState::occurs_in(rhs, meta_id) {
            self.record(TraceKind::OccursCheckFail, lhs, rhs);
            return Some(UnifyResult::Failure(format!(
                "occurs check: ?{}",
                meta_id.as_u64()
            )));
        }

        let mut solution = rhs.clone();
        for _ in args.iter().rev() {
            solution = Expr::lam(clean_kernel::BinderInfo::Default, Expr::prop(), solution);
        }
        self.metas.assign(meta_id, solution);
        self.record(TraceKind::MillerAssign, lhs, rhs);
        Some(UnifyResult::Success)
    }

    fn decompose_meta_app(&self, expr: &Expr) -> Option<(MetaId, Vec<Expr>)> {
        let mut args = Vec::new();
        let mut head = expr;
        while let ExprKind::App(f, a) = head.kind() {
            args.push(a.as_ref().clone());
            head = f;
        }
        let meta_id = self.as_meta(head)?;
        args.reverse();
        Some((meta_id, args))
    }

    fn as_meta(&self, expr: &Expr) -> Option<MetaId> {
        if let ExprKind::FVar(id) = expr.kind() {
            if let Some(mid) = MetaState::from_fvar(*id) {
                if self.metas.get(mid).is_some() && !self.metas.is_assigned(mid) {
                    return Some(mid);
                }
            }
        }
        None
    }

    // ========================================================================
    // Eta expansion
    // ========================================================================

    fn try_eta(&mut self, left: &Expr, right: &Expr) -> Option<UnifyResult> {
        if let ExprKind::Lam(_bi, _ty, body) = left.kind() {
            if !matches!(right.kind(), ExprKind::Lam(..)) {
                let expanded_body = Expr::app(right.clone(), Expr::bvar(0));
                self.record(TraceKind::EtaExpand, left, right);
                return Some(self.unify(body, &expanded_body));
            }
        }
        if let ExprKind::Lam(_bi, _ty, body) = right.kind() {
            if !matches!(left.kind(), ExprKind::Lam(..)) {
                let expanded_body = Expr::app(left.clone(), Expr::bvar(0));
                self.record(TraceKind::EtaExpand, left, right);
                return Some(self.unify(&expanded_body, body));
            }
        }
        None
    }

    // ========================================================================
    // First-order approximation
    // ========================================================================

    fn try_fo_approx(&mut self, left: &Expr, right: &Expr) -> Option<UnifyResult> {
        let (meta_id, l_args) = self.decompose_meta_app(left)?;
        if self.metas.is_assigned(meta_id) {
            return None;
        }
        let r_args = collect_app_args(right);
        if l_args.len() != r_args.len() {
            return None;
        }
        let r_head = peel_app_head(right);
        if MetaState::occurs_in(&r_head, meta_id) {
            return None;
        }
        self.metas.assign(meta_id, r_head);
        self.record(TraceKind::FirstOrderApprox, left, right);
        for (la, ra) in l_args.iter().zip(r_args.iter()) {
            match self.unify(la, ra) {
                UnifyResult::Success => {}
                other => return Some(other),
            }
        }
        Some(UnifyResult::Success)
    }

    // ========================================================================
    // Structural unification
    // ========================================================================

    fn unify_structural(&mut self, left: &Expr, right: &Expr) -> UnifyResult {
        if let Some(mid) = self.as_meta(left) {
            return self.assign_meta(mid, right);
        }
        if let Some(mid) = self.as_meta(right) {
            return self.assign_meta(mid, left);
        }

        match (left.kind(), right.kind()) {
            (ExprKind::Sort(l1), ExprKind::Sort(l2)) => self.unify_levels(l1, l2),
            (ExprKind::Const(n1, ls1), ExprKind::Const(n2, ls2)) => {
                if n1 != n2 || ls1.len() != ls2.len() {
                    return UnifyResult::Failure(format!("const mismatch: {n1:?} vs {n2:?}"));
                }
                for (l1, l2) in ls1.iter().zip(ls2.iter()) {
                    if let r @ UnifyResult::Failure(_) = self.unify_levels(l1, l2) {
                        return r;
                    }
                }
                UnifyResult::Success
            }
            (ExprKind::BVar(i1), ExprKind::BVar(i2)) if i1 == i2 => UnifyResult::Success,
            (ExprKind::BVar(i1), ExprKind::BVar(i2)) => {
                UnifyResult::Failure(format!("bvar mismatch: {i1} vs {i2}"))
            }
            (ExprKind::FVar(a), ExprKind::FVar(b)) if a == b => UnifyResult::Success,
            (ExprKind::FVar(a), ExprKind::FVar(b)) => {
                UnifyResult::Failure(format!("fvar mismatch: {a:?} vs {b:?}"))
            }
            (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => {
                if let r @ UnifyResult::Failure(_) = self.unify(f1, f2) {
                    return r;
                }
                self.unify(a1, a2)
            }
            // BinderInfo deliberately ignored, mirroring Lean 4's `isDefEq`
            // and the live unifier (`unify/unifier/unify_expr.rs` Lam/Pi
            // case) — implicitness is elaboration metadata, not term
            // structure; the kernel re-check is the safety net (its defeq,
            // `tc/def_eq/binding.rs`, never compares binder infos either).
            (ExprKind::Lam(_, ty1, b1), ExprKind::Lam(_, ty2, b2))
            | (ExprKind::Pi(_, ty1, b1), ExprKind::Pi(_, ty2, b2)) => {
                if let r @ UnifyResult::Failure(_) = self.unify(ty1, ty2) {
                    return r;
                }
                self.unify(b1, b2)
            }
            (ExprKind::Let(_, ty1, v1, b1, _), ExprKind::Let(_, ty2, v2, b2, _)) => {
                if let r @ UnifyResult::Failure(_) = self.unify(ty1, ty2) {
                    return r;
                }
                if let r @ UnifyResult::Failure(_) = self.unify(v1, v2) {
                    return r;
                }
                self.unify(b1, b2)
            }
            (ExprKind::Lit(a), ExprKind::Lit(b)) if a == b => UnifyResult::Success,
            (ExprKind::Lit(a), ExprKind::Lit(b)) => {
                UnifyResult::Failure(format!("literal mismatch: {a:?} vs {b:?}"))
            }
            (ExprKind::Proj(n1, i1, e1), ExprKind::Proj(n2, i2, e2)) if n1 == n2 && i1 == i2 => {
                self.unify(e1, e2)
            }
            _ => {
                if self.expr_has_meta(left) || self.expr_has_meta(right) {
                    self.postpone(left, right, StuckReason::BothMeta);
                    self.record(TraceKind::Stuck, left, right);
                    UnifyResult::Stuck
                } else {
                    self.record(TraceKind::Failure, left, right);
                    UnifyResult::Failure(format!(
                        "shape mismatch: {:?} vs {:?}",
                        std::mem::discriminant(left.kind()),
                        std::mem::discriminant(right.kind())
                    ))
                }
            }
        }
    }

    fn assign_meta(&mut self, meta_id: MetaId, value: &Expr) -> UnifyResult {
        let value = self.metas.instantiate(value);
        if MetaState::occurs_in(&value, meta_id) {
            self.record(
                TraceKind::OccursCheckFail,
                &Expr::fvar(MetaState::to_fvar(meta_id)),
                &value,
            );
            return UnifyResult::Failure(format!("occurs check failed for ?{}", meta_id.as_u64()));
        }
        self.metas.assign(meta_id, value);
        UnifyResult::Success
    }

    // ========================================================================
    // Postponed constraints
    // ========================================================================

    fn postpone(&mut self, left: &Expr, right: &Expr, reason: StuckReason) {
        self.record(TraceKind::Postpone, left, right);
        self.postponed.push(PostponedConstraint {
            left: left.clone(),
            right: right.clone(),
            reason,
        });
    }

    /// Process postponed constraints. Returns `true` if all were resolved.
    pub(crate) fn process_postponed(&mut self) -> bool {
        for pass in 0..self.config.max_simplify_passes {
            if self.postponed.is_empty() {
                return true;
            }
            let queue = std::mem::take(&mut self.postponed);
            let mut progress = false;
            for c in queue {
                let l = self.metas.instantiate(&c.left);
                let r = self.metas.instantiate(&c.right);
                self.record(TraceKind::Simplify, &l, &r);
                match self.unify(&l, &r) {
                    UnifyResult::Success => progress = true,
                    UnifyResult::Stuck => {} // re-postponed inside unify
                    UnifyResult::Failure(_) => {
                        self.postponed.push(PostponedConstraint {
                            left: l,
                            right: r,
                            reason: c.reason,
                        });
                    }
                }
            }
            if !progress {
                return self.postponed.is_empty();
            }
            if pass + 1 >= self.config.max_simplify_passes {
                break;
            }
        }
        self.postponed.is_empty()
    }

    /// Report stuck constraints as a diagnostic string.
    pub(crate) fn stuck_report(&self) -> Option<String> {
        if self.postponed.is_empty() {
            return None;
        }
        let mut s = String::from("stuck constraints:\n");
        for (i, c) in self.postponed.iter().enumerate() {
            s.push_str(&format!(
                "  [{i}] {:?}: {:?} =?= {:?}\n",
                c.reason, c.left, c.right
            ));
        }
        Some(s)
    }

    // ========================================================================
    // Helpers
    // ========================================================================

    fn expr_has_meta(&self, expr: &Expr) -> bool {
        match expr.kind() {
            ExprKind::FVar(id) => MetaState::from_fvar(*id)
                .is_some_and(|mid| self.metas.get(mid).is_some() && !self.metas.is_assigned(mid)),
            ExprKind::App(f, a) => self.expr_has_meta(f) || self.expr_has_meta(a),
            ExprKind::Lam(_, ty, b) | ExprKind::Pi(_, ty, b) => {
                self.expr_has_meta(ty) || self.expr_has_meta(b)
            }
            ExprKind::Let(_, ty, v, b, _) => {
                self.expr_has_meta(ty) || self.expr_has_meta(v) || self.expr_has_meta(b)
            }
            ExprKind::Proj(_, _, e) => self.expr_has_meta(e),
            _ => false,
        }
    }
}

// ============================================================================
// Free helpers
// ============================================================================

fn are_distinct_bvars(args: &[Expr]) -> bool {
    let mut seen = Vec::with_capacity(args.len());
    for arg in args {
        match arg.kind() {
            ExprKind::BVar(idx) if !seen.contains(idx) => seen.push(*idx),
            _ => return false,
        }
    }
    true
}

fn collect_app_args(expr: &Expr) -> Vec<Expr> {
    let mut args = Vec::new();
    let mut h = expr;
    while let ExprKind::App(f, a) = h.kind() {
        args.push(a.as_ref().clone());
        h = f;
    }
    args.reverse();
    args
}

fn peel_app_head(expr: &Expr) -> Expr {
    let mut h = expr;
    while let ExprKind::App(f, _) = h.kind() {
        h = f;
    }
    h.clone()
}

fn apply_args(head: &Expr, args: &[Expr]) -> Expr {
    args.iter()
        .fold(head.clone(), |acc, a| Expr::app(acc, a.clone()))
}
