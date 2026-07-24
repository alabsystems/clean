// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared recursive equality engine for cert subsystem.
//!
//! Both `CertBuilder` and `CertVerifier` need the same recursive definitional
//! equality algorithm, differing only in their WHNF reduction strategy.
//! This trait captures the shared equality logic, requiring each implementor
//! to supply its own `whnf_impl`.
//!
//! Extracted per design `designs/2026-03-10-2485-cert-builder-equality-extraction-and-module-split.md`.
//! Fixes the duplicate bug lane that produced #2478 (verifier) and #2481 (builder).

use crate::expr::{stack_safe, Expr, ExprKind, ZFCSetExpr};
use crate::level::Level;

/// Cert-internal trait for recursive definitional equality.
///
/// Implementors supply `whnf_impl` (which legitimately differs between
/// builder and verifier). All recursive equality methods are provided
/// as default implementations.
pub(super) trait CertExprEqContext {
    /// Reduce expression to weak head normal form.
    ///
    /// Builder uses simplified WHNF (beta, zeta, delta, mdata/squash).
    /// Verifier uses full WHNF (+ projection, iota, quotient reduction).
    ///
    /// Named `whnf_for_eq` to avoid collision with the inherent `whnf_impl`
    /// methods on both `CertBuilder` and `CertVerifier`.
    fn whnf_for_eq(&self, e: &Expr) -> Expr;

    /// Universe level equality via normalization.
    fn level_eq(&self, l1: &Level, l2: &Level) -> bool {
        Level::is_def_eq(l1, l2)
    }

    /// Recursive definitional equality after WHNF.
    ///
    /// After WHNF, decomposes matching heads and recursively calls `def_eq_impl`
    /// on subterms. This ensures nested subterms that are definitionally equal
    /// but not structurally equal are correctly handled.
    ///
    /// Fix for #2478/#2481: the previous per-type implementations delegated to
    /// `structural_eq_impl` which compared subterms without WHNF.
    fn def_eq_impl(&self, a: &Expr, b: &Expr) -> bool {
        stack_safe(|| self.def_eq_inner(a, b))
    }

    /// Recursive definitional equality inner loop.
    fn def_eq_inner(&self, a: &Expr, b: &Expr) -> bool {
        // Fast path: pointer/value equality before WHNF
        if a == b {
            return true;
        }
        let a_whnf = self.whnf_for_eq(a);
        let b_whnf = self.whnf_for_eq(b);
        // Fast path: value equality after WHNF
        if a_whnf == b_whnf {
            return true;
        }
        // Deep comparison: recurse with def_eq_impl on subterms so each level
        // gets WHNF + semantic equality, not just structural matching.
        let matched = match (&a_whnf.kind, &b_whnf.kind) {
            (ExprKind::BVar(i), ExprKind::BVar(j)) => i == j,
            (ExprKind::FVar(i), ExprKind::FVar(j)) => i == j,
            (ExprKind::Sort(l1), ExprKind::Sort(l2)) => self.level_eq(l1, l2),
            (ExprKind::Const(n1, ls1), ExprKind::Const(n2, ls2)) => {
                n1 == n2
                    && ls1.len() == ls2.len()
                    && ls1
                        .iter()
                        .zip(ls2.iter())
                        .all(|(l1, l2)| self.level_eq(l1, l2))
            }
            (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => {
                self.def_eq_impl(f1, f2) && self.def_eq_impl(a1, a2)
            }
            // Binder info is irrelevant for definitional equality in CIC.
            (ExprKind::Lam(_bi1, ty1, b1), ExprKind::Lam(_bi2, ty2, b2))
            | (ExprKind::Pi(_bi1, ty1, b1), ExprKind::Pi(_bi2, ty2, b2)) => {
                self.def_eq_impl(ty1, ty2) && self.def_eq_impl(b1, b2)
            }
            (ExprKind::Let(_, ty1, v1, b1, _), ExprKind::Let(_, ty2, v2, b2, _)) => {
                self.def_eq_impl(ty1, ty2) && self.def_eq_impl(v1, v2) && self.def_eq_impl(b1, b2)
            }
            (ExprKind::Lit(l1), ExprKind::Lit(l2)) => l1 == l2,
            (ExprKind::Proj(n1, i1, e1), ExprKind::Proj(n2, i2, e2)) => {
                n1 == n2 && i1 == i2 && self.def_eq_impl(e1, e2)
            }
            (ExprKind::MData(_, inner1), ExprKind::MData(_, inner2)) => {
                self.def_eq_impl(inner1, inner2)
            }
            // Mode-specific: leaf-like mode exprs (no subterms needing WHNF)
            (ExprKind::CubicalInterval, ExprKind::CubicalInterval)
            | (ExprKind::CubicalI0, ExprKind::CubicalI0)
            | (ExprKind::CubicalI1, ExprKind::CubicalI1)
            | (ExprKind::SProp, ExprKind::SProp) => true,
            (
                ExprKind::CubicalPath {
                    ty: ty1,
                    left: l1,
                    right: r1,
                },
                ExprKind::CubicalPath {
                    ty: ty2,
                    left: l2,
                    right: r2,
                },
            ) => self.def_eq_impl(ty1, ty2) && self.def_eq_impl(l1, l2) && self.def_eq_impl(r1, r2),
            (ExprKind::CubicalPathLam { body: b1 }, ExprKind::CubicalPathLam { body: b2 }) => {
                self.def_eq_impl(b1, b2)
            }
            (
                ExprKind::CubicalPathApp { path: p1, arg: a1 },
                ExprKind::CubicalPathApp { path: p2, arg: a2 },
            ) => self.def_eq_impl(p1, p2) && self.def_eq_impl(a1, a2),
            (
                ExprKind::CubicalHComp {
                    ty: ty1,
                    phi: phi1,
                    u: u1,
                    base: base1,
                },
                ExprKind::CubicalHComp {
                    ty: ty2,
                    phi: phi2,
                    u: u2,
                    base: base2,
                },
            ) => {
                self.def_eq_impl(ty1, ty2)
                    && self.def_eq_impl(phi1, phi2)
                    && self.def_eq_impl(u1, u2)
                    && self.def_eq_impl(base1, base2)
            }
            (
                ExprKind::CubicalTransp {
                    ty: ty1,
                    phi: phi1,
                    base: base1,
                },
                ExprKind::CubicalTransp {
                    ty: ty2,
                    phi: phi2,
                    base: base2,
                },
            ) => {
                self.def_eq_impl(ty1, ty2)
                    && self.def_eq_impl(phi1, phi2)
                    && self.def_eq_impl(base1, base2)
            }
            (
                ExprKind::CubicalCoe {
                    ty: ty1,
                    r: r1,
                    s: s1,
                    base: base1,
                },
                ExprKind::CubicalCoe {
                    ty: ty2,
                    r: r2,
                    s: s2,
                    base: base2,
                },
            ) => {
                self.def_eq_impl(ty1, ty2)
                    && self.def_eq_impl(r1, r2)
                    && self.def_eq_impl(s1, s2)
                    && self.def_eq_impl(base1, base2)
            }
            (ExprKind::ZFCSet(s1), ExprKind::ZFCSet(s2)) => self.zfc_set_def_eq(s1, s2),
            (
                ExprKind::ZFCMem {
                    element: e1,
                    set: s1,
                },
                ExprKind::ZFCMem {
                    element: e2,
                    set: s2,
                },
            ) => self.def_eq_impl(e1, e2) && self.def_eq_impl(s1, s2),
            (
                ExprKind::ZFCComprehension {
                    domain: d1,
                    pred: p1,
                },
                ExprKind::ZFCComprehension {
                    domain: d2,
                    pred: p2,
                },
            ) => self.def_eq_impl(d1, d2) && self.def_eq_impl(p1, p2),
            (ExprKind::Squash(a), ExprKind::Squash(b)) => self.def_eq_impl(a, b),
            _ => false,
        };
        if matched {
            return true;
        }
        // Structural Nat offset equality (Lean 4 `is_def_eq_offset` parity):
        // `0 ≟ 0` and `succ a ≟ succ b → a ≟ b` on the WHNF'd sides. This
        // decides mixed literal/`Nat.succ` and OPEN-successor forms that the
        // closed-only native `reduce_nat` (in each side's WHNF) cannot evaluate
        // — e.g. `4` vs `Nat.succ a` with `a` an fvar that is def-eq to `3`.
        // Part of the cert-replay Nat-defeq fix (see `cert/nat_reduce.rs`).
        if let Some(off) =
            super::nat_reduce::is_def_eq_offset(&a_whnf, &b_whnf, &|x, y| self.def_eq_impl(x, y))
        {
            return off;
        }
        // Eta expansion: (λ x : A. f x) ≡ f when x ∉ FV(f)
        self.try_eta_expansion(&a_whnf, &b_whnf)
    }

    /// Try eta expansion to prove equality.
    ///
    /// If one side is `Lam(bi, ty, body)` and the other is not, check whether
    /// `body ≡ other.lift(1) @ BVar(0)`. This is the standard eta rule:
    /// `(λ x. f x) ≡ f` when `x ∉ FV(f)`.
    fn try_eta_expansion(&self, a: &Expr, b: &Expr) -> bool {
        match (&a.kind, &b.kind) {
            (ExprKind::Lam(_, _ty, body), _) => {
                let other_lifted = b.lift_from(0, 1);
                let other_applied = Expr::app(other_lifted, Expr::bvar(0));
                self.def_eq_impl(body, &other_applied)
            }
            (_, ExprKind::Lam(_, _ty, body)) => {
                let other_lifted = a.lift_from(0, 1);
                let other_applied = Expr::app(other_lifted, Expr::bvar(0));
                self.def_eq_impl(body, &other_applied)
            }
            _ => false,
        }
    }

    /// Structural equality (no WHNF). Test-only.
    #[cfg(test)]
    fn structural_eq_impl(&self, a: &Expr, b: &Expr) -> bool {
        stack_safe(|| self.structural_eq_inner(a, b))
    }

    /// Structural equality inner loop (no WHNF). Test-only.
    #[cfg(test)]
    fn structural_eq_inner(&self, a: &Expr, b: &Expr) -> bool {
        match (&a.kind, &b.kind) {
            (ExprKind::BVar(i), ExprKind::BVar(j)) => i == j,
            (ExprKind::FVar(i), ExprKind::FVar(j)) => i == j,
            (ExprKind::Sort(l1), ExprKind::Sort(l2)) => self.level_eq(l1, l2),
            (ExprKind::Const(n1, ls1), ExprKind::Const(n2, ls2)) => {
                n1 == n2
                    && ls1.len() == ls2.len()
                    && ls1
                        .iter()
                        .zip(ls2.iter())
                        .all(|(l1, l2)| self.level_eq(l1, l2))
            }
            (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => {
                self.structural_eq_impl(f1, f2) && self.structural_eq_impl(a1, a2)
            }
            // Binder info is irrelevant for definitional equality in CIC.
            (ExprKind::Lam(_bi1, ty1, b1), ExprKind::Lam(_bi2, ty2, b2))
            | (ExprKind::Pi(_bi1, ty1, b1), ExprKind::Pi(_bi2, ty2, b2)) => {
                self.structural_eq_impl(ty1, ty2) && self.structural_eq_impl(b1, b2)
            }
            (ExprKind::Let(_, ty1, v1, b1, _), ExprKind::Let(_, ty2, v2, b2, _)) => {
                self.structural_eq_impl(ty1, ty2)
                    && self.structural_eq_impl(v1, v2)
                    && self.structural_eq_impl(b1, b2)
            }
            (ExprKind::Lit(l1), ExprKind::Lit(l2)) => l1 == l2,
            (ExprKind::Proj(n1, i1, e1), ExprKind::Proj(n2, i2, e2)) => {
                n1 == n2 && i1 == i2 && self.structural_eq_impl(e1, e2)
            }
            (ExprKind::MData(_, inner1), ExprKind::MData(_, inner2)) => {
                self.structural_eq_impl(inner1, inner2)
            }
            // Mode-specific expressions
            (ExprKind::CubicalInterval, ExprKind::CubicalInterval)
            | (ExprKind::CubicalI0, ExprKind::CubicalI0)
            | (ExprKind::CubicalI1, ExprKind::CubicalI1)
            | (ExprKind::SProp, ExprKind::SProp) => true,
            (
                ExprKind::CubicalPath {
                    ty: ty1,
                    left: l1,
                    right: r1,
                },
                ExprKind::CubicalPath {
                    ty: ty2,
                    left: l2,
                    right: r2,
                },
            ) => {
                self.structural_eq_impl(ty1, ty2)
                    && self.structural_eq_impl(l1, l2)
                    && self.structural_eq_impl(r1, r2)
            }
            (ExprKind::CubicalPathLam { body: b1 }, ExprKind::CubicalPathLam { body: b2 }) => {
                self.structural_eq_impl(b1, b2)
            }
            (
                ExprKind::CubicalPathApp { path: p1, arg: a1 },
                ExprKind::CubicalPathApp { path: p2, arg: a2 },
            ) => self.structural_eq_impl(p1, p2) && self.structural_eq_impl(a1, a2),
            (
                ExprKind::CubicalHComp {
                    ty: ty1,
                    phi: phi1,
                    u: u1,
                    base: base1,
                },
                ExprKind::CubicalHComp {
                    ty: ty2,
                    phi: phi2,
                    u: u2,
                    base: base2,
                },
            ) => {
                self.structural_eq_impl(ty1, ty2)
                    && self.structural_eq_impl(phi1, phi2)
                    && self.structural_eq_impl(u1, u2)
                    && self.structural_eq_impl(base1, base2)
            }
            (
                ExprKind::CubicalTransp {
                    ty: ty1,
                    phi: phi1,
                    base: base1,
                },
                ExprKind::CubicalTransp {
                    ty: ty2,
                    phi: phi2,
                    base: base2,
                },
            ) => {
                self.structural_eq_impl(ty1, ty2)
                    && self.structural_eq_impl(phi1, phi2)
                    && self.structural_eq_impl(base1, base2)
            }
            (
                ExprKind::CubicalCoe {
                    ty: ty1,
                    r: r1,
                    s: s1,
                    base: base1,
                },
                ExprKind::CubicalCoe {
                    ty: ty2,
                    r: r2,
                    s: s2,
                    base: base2,
                },
            ) => {
                self.structural_eq_impl(ty1, ty2)
                    && self.structural_eq_impl(r1, r2)
                    && self.structural_eq_impl(s1, s2)
                    && self.structural_eq_impl(base1, base2)
            }
            (ExprKind::ZFCSet(s1), ExprKind::ZFCSet(s2)) => self.zfc_set_eq(s1, s2),
            (
                ExprKind::ZFCMem {
                    element: e1,
                    set: s1,
                },
                ExprKind::ZFCMem {
                    element: e2,
                    set: s2,
                },
            ) => self.structural_eq_impl(e1, e2) && self.structural_eq_impl(s1, s2),
            (
                ExprKind::ZFCComprehension {
                    domain: d1,
                    pred: p1,
                },
                ExprKind::ZFCComprehension {
                    domain: d2,
                    pred: p2,
                },
            ) => self.structural_eq_impl(d1, d2) && self.structural_eq_impl(p1, p2),
            (ExprKind::Squash(a), ExprKind::Squash(b)) => self.structural_eq_impl(a, b),
            _ => false,
        }
    }

    /// Structural equality for ZFC set expressions. Test-only.
    #[cfg(test)]
    fn zfc_set_eq(&self, a: &ZFCSetExpr, b: &ZFCSetExpr) -> bool {
        match (a, b) {
            (ZFCSetExpr::Empty, ZFCSetExpr::Empty) => true,
            (ZFCSetExpr::Infinity, ZFCSetExpr::Infinity) => true,
            (ZFCSetExpr::Singleton(e1), ZFCSetExpr::Singleton(e2)) => {
                self.structural_eq_impl(e1, e2)
            }
            (ZFCSetExpr::Pair(a1, b1), ZFCSetExpr::Pair(a2, b2)) => {
                self.structural_eq_impl(a1, a2) && self.structural_eq_impl(b1, b2)
            }
            (ZFCSetExpr::Union(e1), ZFCSetExpr::Union(e2)) => self.structural_eq_impl(e1, e2),
            (ZFCSetExpr::PowerSet(e1), ZFCSetExpr::PowerSet(e2)) => self.structural_eq_impl(e1, e2),
            (
                ZFCSetExpr::Separation { set: s1, pred: p1 },
                ZFCSetExpr::Separation { set: s2, pred: p2 },
            ) => self.structural_eq_impl(s1, s2) && self.structural_eq_impl(p1, p2),
            (
                ZFCSetExpr::Replacement { set: s1, func: f1 },
                ZFCSetExpr::Replacement { set: s2, func: f2 },
            ) => self.structural_eq_impl(s1, s2) && self.structural_eq_impl(f1, f2),
            (ZFCSetExpr::Choice(e1), ZFCSetExpr::Choice(e2)) => self.structural_eq_impl(e1, e2),
            _ => false,
        }
    }

    /// Definitional equality for ZFC set expressions.
    ///
    /// Unlike `zfc_set_eq` (which uses `structural_eq_impl`), this recurses
    /// with `def_eq_impl` so nested subterms get WHNF reduction.
    fn zfc_set_def_eq(&self, a: &ZFCSetExpr, b: &ZFCSetExpr) -> bool {
        match (a, b) {
            (ZFCSetExpr::Empty, ZFCSetExpr::Empty) => true,
            (ZFCSetExpr::Infinity, ZFCSetExpr::Infinity) => true,
            (ZFCSetExpr::Singleton(e1), ZFCSetExpr::Singleton(e2)) => self.def_eq_impl(e1, e2),
            (ZFCSetExpr::Pair(a1, b1), ZFCSetExpr::Pair(a2, b2)) => {
                self.def_eq_impl(a1, a2) && self.def_eq_impl(b1, b2)
            }
            (ZFCSetExpr::Union(e1), ZFCSetExpr::Union(e2)) => self.def_eq_impl(e1, e2),
            (ZFCSetExpr::PowerSet(e1), ZFCSetExpr::PowerSet(e2)) => self.def_eq_impl(e1, e2),
            (
                ZFCSetExpr::Separation { set: s1, pred: p1 },
                ZFCSetExpr::Separation { set: s2, pred: p2 },
            ) => self.def_eq_impl(s1, s2) && self.def_eq_impl(p1, p2),
            (
                ZFCSetExpr::Replacement { set: s1, func: f1 },
                ZFCSetExpr::Replacement { set: s2, func: f2 },
            ) => self.def_eq_impl(s1, s2) && self.def_eq_impl(f1, f2),
            (ZFCSetExpr::Choice(e1), ZFCSetExpr::Choice(e2)) => self.def_eq_impl(e1, e2),
            _ => false,
        }
    }
}
