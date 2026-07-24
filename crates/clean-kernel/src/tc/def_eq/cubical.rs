// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Definitional equality for cubical-mode constructs.
//!
//! The classical structural comparison (`is_def_eq_structural`) has no arms for
//! the cubical `ExprKind`s, so two cubical terms previously fell through to the
//! structure-eta fallback and compared *unequal* unless they happened to be
//! syntactically identical (caught earlier by the `equiv_manager` quick check).
//!
//! This module supplies proper component-wise definitional comparison that
//! recurses through `is_def_eq_impl` — strictly stronger than the syntactic
//! `equiv_manager` check, because subterms are compared up to full definitional
//! equality (e.g. `Path A a b ≡ Path A' a' b'` whenever `A ≡ A'`, `a ≡ a'`,
//! `b ≡ b'`). Path-lambdas open their interval binder with a fresh interval
//! `FVar` exactly like `is_def_eq_binding` does for `Lam`/`Pi`, and path-eta
//! (`p ≡ <i> p @ i`) fires only when the non-path-lam side is known to have a
//! `CubicalPath` type — mirroring the Pi-type guard in `try_eta_expansion_impl`.
//!
//! This is the *structural* cubical conversion (build-order Step 1). The
//! Kan-aware upgrade (comparing terms up to `transp`/`hcomp` reduction and
//! interval-cofibration equality) layers on top of this in a later step.

use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::name::Name;
use crate::tc::TypeChecker;
use std::sync::Arc;

impl<'env> TypeChecker<'env> {
    /// Component-wise / path-eta definitional equality for cubical constructs.
    ///
    /// Returns `Some(result)` when at least one side is a cubical construct this
    /// routine handles, and `None` to let the caller fall through to its
    /// remaining fallbacks (structure eta, etc.). Subterm comparisons go through
    /// `is_def_eq_impl`, so reduction and caching apply uniformly.
    pub(in crate::tc::def_eq) fn is_def_eq_cubical(&self, a: &Expr, b: &Expr) -> Option<bool> {
        // Neutral path-endpoint reduction: `p @ i0 ≡ left(p)`, `p @ i1 ≡ right(p)`
        // where `p : Path ty left right`. Path-*lambdas* are already path-beta'd by
        // WHNF before reaching here, so this fires for *neutral* paths whose
        // endpoints are recoverable only from their type — the rule that lets e.g.
        // `funext` type-check (`h x @ i0 ≡ f x` because `h x : Path _ (f x) (g x)`).
        if let ExprKind::CubicalPathApp { path, arg } = a.kind() {
            if let Some(endpoint) = self.reduce_path_app_endpoint(path, arg) {
                return Some(self.is_def_eq_impl(&endpoint, b));
            }
        }
        if let ExprKind::CubicalPathApp { path, arg } = b.kind() {
            if let Some(endpoint) = self.reduce_path_app_endpoint(path, arg) {
                return Some(self.is_def_eq_impl(a, &endpoint));
            }
        }

        // Deep path-beta: a path application `P @ arg` whose head `P` only becomes
        // a `<i> …` after *delta* unfolding (a named `cong`/`decode` helper) or after
        // a nested *typed* endpoint projection (`q @ i1 ↝ right(q)`, e.g. the IH
        // variable `ih @ i1` of a diagonal lemma). WHNF's untyped path-beta and the
        // literal-endpoint rule above each handle only one of these; chaining them
        // (see `whnf_path_to_pathlam`) exposes the path-lam so the application
        // reduces under a binder. Sound: delta + path-beta + the endpoint rule are
        // all meaning-preserving definitional rules.
        if let ExprKind::CubicalPathApp { path, arg } = a.kind() {
            if let Some(body) = self.whnf_path_to_pathlam(path) {
                return Some(self.is_def_eq_impl(&body.instantiate(arg), b));
            }
        }
        if let ExprKind::CubicalPathApp { path, arg } = b.kind() {
            if let Some(body) = self.whnf_path_to_pathlam(path) {
                return Some(self.is_def_eq_impl(a, &body.instantiate(arg)));
            }
        }

        match (a.kind(), b.kind()) {
            (ExprKind::CubicalInterval, ExprKind::CubicalInterval)
            | (ExprKind::CubicalI0, ExprKind::CubicalI0)
            | (ExprKind::CubicalI1, ExprKind::CubicalI1) => Some(true),

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
            ) => Some(
                self.is_def_eq_impl(t1, t2)
                    && self.is_def_eq_impl(l1, l2)
                    && self.is_def_eq_impl(r1, r2),
            ),

            (ExprKind::CubicalPathLam { body: b1 }, ExprKind::CubicalPathLam { body: b2 }) => {
                Some(self.is_def_eq_path_lam_bodies(b1, b2))
            }

            (
                ExprKind::CubicalPathApp { path: p1, arg: a1 },
                ExprKind::CubicalPathApp { path: p2, arg: a2 },
            ) => Some(self.is_def_eq_impl(p1, p2) && self.is_def_eq_impl(a1, a2)),

            (
                ExprKind::CubicalHComp {
                    ty: t1,
                    phi: f1,
                    u: u1,
                    base: x1,
                },
                ExprKind::CubicalHComp {
                    ty: t2,
                    phi: f2,
                    u: u2,
                    base: x2,
                },
            ) => {
                // Fast path: fully structural component-wise equality.
                if self.is_def_eq_impl(t1, t2)
                    && self.is_def_eq_impl(f1, f2)
                    && self.is_def_eq_impl(u1, u2)
                    && self.is_def_eq_impl(x1, x2)
                {
                    return Some(true);
                }
                // Kan-aware fallback: two `hcomp`s denote the same composite when
                // they share the floor/type and their systems agree *up to dropping
                // ⊥-faced branches and reordering* (a ⊥ tube is never active). This
                // makes e.g. a collapse-square slice `hcomp [(k=0),(k=1),(i0=1)↦…]`
                // def-eq to the 2-branch `path_compose` it restricts to.
                Some(
                    self.is_def_eq_impl(t1, t2)
                        && self.is_def_eq_impl(x1, x2)
                        && self.hcomp_systems_match(f1, u1, f2, u2),
                )
            }

            (
                ExprKind::CubicalTransp {
                    ty: t1,
                    phi: f1,
                    base: x1,
                },
                ExprKind::CubicalTransp {
                    ty: t2,
                    phi: f2,
                    base: x2,
                },
            ) => Some(
                self.is_def_eq_impl(t1, t2)
                    && self.is_def_eq_impl(f1, f2)
                    && self.is_def_eq_impl(x1, x2),
            ),

            (
                ExprKind::CubicalCoe {
                    ty: t1,
                    r: r1,
                    s: s1,
                    base: x1,
                },
                ExprKind::CubicalCoe {
                    ty: t2,
                    r: r2,
                    s: s2,
                    base: x2,
                },
            ) => Some(
                self.is_def_eq_impl(t1, t2)
                    && self.is_def_eq_impl(r1, r2)
                    && self.is_def_eq_impl(s1, s2)
                    && self.is_def_eq_impl(x1, x2),
            ),

            // Path-eta: `<i> (p @ i) ≡ p`. Fire only when one side is a path-lam
            // and the other is a value of `CubicalPath` type. The (PathLam,
            // PathLam) case is handled above, so these only catch the mixed case.
            //
            // Before eta, full-delta-WHNF the non-path-lam side: a *reducible*
            // head there (e.g. a named `cong`/`decode` helper) may itself unfold
            // to a `<i> …`, in which case the honest comparison is path-lam vs
            // path-lam — NOT eta on a head that path-eta cannot see through. The
            // no-delta Phase-1 WHNF and the App-spine lazy-delta loop both miss
            // this unfold when the other side is a bare path-lam with no Const
            // head to pair against, so do it here. Sound: WHNF is meaning-
            // preserving; this only ever *adds* equalities.
            (ExprKind::CubicalPathLam { .. }, _) => {
                let b_whnf = self.whnf_impl(b);
                if matches!(b_whnf.kind(), ExprKind::CubicalPathLam { .. }) {
                    Some(self.is_def_eq_impl(a, &b_whnf))
                } else {
                    self.try_path_eta(a, b)
                }
            }
            (_, ExprKind::CubicalPathLam { .. }) => {
                let a_whnf = self.whnf_impl(a);
                if matches!(a_whnf.kind(), ExprKind::CubicalPathLam { .. }) {
                    Some(self.is_def_eq_impl(&a_whnf, b))
                } else {
                    self.try_path_eta(b, a)
                }
            }

            _ => None,
        }
    }

    /// Kan-aware comparison of two `hcomp` systems `(phi1,u1)` / `(phi2,u2)`:
    /// parse both against **one shared interner** (so interval-variable atom ids
    /// are comparable), drop ⊥-faced branches from each (an inactive tube never
    /// contributes), and require a face-respecting bijection — every surviving
    /// branch of one side pairs with a branch of the other whose cofibration is
    /// equivalent (`entails` both ways) and whose head is definitionally equal.
    ///
    /// SOUNDNESS: this only ever *accepts*. Two systems matched this way are active
    /// on the same extent (same non-⊥ faces) with definitionally-equal tubes, so
    /// the two `hcomp`s (with equal floor and type, checked by the caller) reduce
    /// identically on every face — they denote the same composite. Dropping a
    /// ⊥-faced branch is sound because the whnf rule only fires a branch on a
    /// *true* face, which a ⊥ face never is. Reordering is sound because
    /// `validate_hcomp_system` forces simultaneously-total branches to agree.
    fn hcomp_systems_match(&self, phi1: &Expr, u1: &Expr, phi2: &Expr, u2: &Expr) -> bool {
        use crate::tc::reduction::cofib::Cofib;
        use crate::tc::whnf::WhnfMode;
        let mut interner: Vec<Expr> = Vec::new();
        let Some(s1) = self.parse_system_into(phi1, u1, WhnfMode::Full, &mut interner) else {
            return false;
        };
        let Some(s2) = self.parse_system_into(phi2, u2, WhnfMode::Full, &mut interner) else {
            return false;
        };
        let live1: Vec<&(Cofib, Expr)> = s1.iter().filter(|(c, _)| !c.is_bot()).collect();
        let live2: Vec<&(Cofib, Expr)> = s2.iter().filter(|(c, _)| !c.is_bot()).collect();
        if live1.len() != live2.len() {
            return false;
        }
        // Greedy face-respecting bijection: each branch of `live1` consumes a
        // distinct, still-unused branch of `live2` whose cofibration is equivalent
        // and whose head agrees — either globally, or (the partial-element notion)
        // restricted to the shared face. On-face agreement is the correct `hcomp`
        // equality: a tube is a `Partial φ A`, so its off-face values are immaterial.
        let mut used = vec![false; live2.len()];
        for (c1, h1) in &live1 {
            let mut matched = false;
            for (j, (c2, h2)) in live2.iter().enumerate() {
                if used[j] || !(c1.entails(c2) && c2.entails(c1)) {
                    continue;
                }
                if self.is_def_eq_impl(h1, h2) || self.heads_agree_on_face(h1, h2, c1, &interner) {
                    used[j] = true;
                    matched = true;
                    break;
                }
            }
            if !matched {
                return false;
            }
        }
        true
    }

    /// Reduce a neutral path application at a literal interval endpoint:
    /// `p @ i0 ↝ left(p)`, `p @ i1 ↝ right(p)`, reading the endpoints off `p`'s
    /// `Path ty left right` type. Returns `None` when `p` is a path-lambda
    /// (handled by path-beta in WHNF), `arg` is not a literal endpoint, or `p`'s
    /// type is not a `Path`.
    ///
    /// Soundness: this is the definitional endpoint rule of the path type —
    /// `p @ i0 : ty i0` and `left : ty i0`, so the rewrite is type-preserving.
    ///
    /// Shared with the recursor iota machinery (`reduction::mod`), which uses it
    /// to reduce a neutral path-endpoint major premise `q @ i0` to its (point
    /// constructor) endpoint so the eliminator can fire — e.g. `helix (q @ i0) ↝
    /// helix base ↝ MyZ`, the typing of `winding`/`encode` over an abstract loop.
    pub(crate) fn reduce_path_app_endpoint(&self, path: &Expr, arg: &Expr) -> Option<Expr> {
        if matches!(path.kind(), ExprKind::CubicalPathLam { .. }) {
            return None;
        }
        let at_left = match self.whnf_impl(arg).kind() {
            ExprKind::CubicalI0 => true,
            ExprKind::CubicalI1 => false,
            _ => return None,
        };
        let path_ty = self
            .try_infer_type_quick(path)
            .or_else(|| self.infer_type_infer_only(path).ok())?;
        let path_ty_whnf = self.whnf_impl(&path_ty);
        let ExprKind::CubicalPath { left, right, .. } = path_ty_whnf.kind() else {
            return None;
        };
        Some(if at_left {
            left.as_ref().clone()
        } else {
            right.as_ref().clone()
        })
    }

    /// Reduce a path expression toward a `CubicalPathLam`, chaining full-delta
    /// WHNF with the typed neutral-endpoint rule (`q @ i0/i1 ↝ left/right(q)`).
    /// Returns the path-lam's **body** (ready for `instantiate`) if it gets there,
    /// else `None`. Each loop iteration strictly makes progress (one WHNF or one
    /// literal-endpoint projection), so it terminates; the cap is purely defensive.
    ///
    /// Soundness: every step is a meaning-preserving definitional reduction (delta,
    /// beta/iota via WHNF, or the path endpoint rule), so the returned body `B`
    /// satisfies `path ≡ <i> B`; the caller's `(path @ arg) ↝ B[arg]` is then valid
    /// path-beta.
    fn whnf_path_to_pathlam(&self, path: &Expr) -> Option<Expr> {
        let mut cur = self.whnf_impl(path);
        for _ in 0..64 {
            match cur.kind() {
                ExprKind::CubicalPathLam { body } => return Some(body.as_ref().clone()),
                ExprKind::CubicalPathApp { path: p, arg } => {
                    let ep = self.reduce_path_app_endpoint(p, arg)?;
                    cur = self.whnf_impl(&ep);
                }
                _ => return None,
            }
        }
        None
    }

    /// Compare two path-lambda bodies by opening their shared interval binder
    /// with one fresh interval `FVar` (mirrors `is_def_eq_binding` for Lam/Pi).
    fn is_def_eq_path_lam_bodies(&self, body1: &Expr, body2: &Expr) -> bool {
        let save_len = self.ctx_len();
        let interval = Expr::from_kind(ExprKind::CubicalInterval);
        let id = self.ctx_push(Name::anon(), interval, BinderInfo::Default);
        let a_open = self.open_bvar(body1, id);
        let b_open = self.open_bvar(body2, id);
        let result = self.is_def_eq_impl(&a_open, &b_open);
        self.ctx_truncate_to(save_len);
        result
    }

    /// Path-eta expansion. `path_lam` is the path-lambda side; `other` is the
    /// opposite side. Returns `Some(_)` only when `other` has a `CubicalPath`
    /// type (so eta is type-correct), mirroring the Pi-type guard in
    /// `try_eta_expansion_impl`; otherwise `None` (defer to other fallbacks).
    fn try_path_eta(&self, path_lam: &Expr, other: &Expr) -> Option<bool> {
        let other_ty = self
            .try_infer_type_quick(other)
            .or_else(|| self.infer_type_infer_only(other).ok())?;
        if !matches!(
            self.whnf_impl(&other_ty).kind(),
            ExprKind::CubicalPath { .. }
        ) {
            return None;
        }
        // Eta-expand `other` into `<i> (other @ i)` and compare path-lambdas.
        // `other.lift_from(0, 1)` makes room for the new interval binder; the
        // bound interval variable is `BVar(0)`. The resulting (PathLam, PathLam)
        // comparison reduces to `body[i] ≟ other @ i` under the binder.
        let eta = Expr::from_kind(ExprKind::CubicalPathLam {
            body: Arc::new(Expr::from_kind(ExprKind::CubicalPathApp {
                path: Arc::new(other.lift_from(0, 1)),
                arg: Arc::new(Expr::bvar(0)),
            })),
        });
        Some(self.is_def_eq_impl(path_lam, &eta))
    }
}
