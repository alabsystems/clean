// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bonami-Beckner campaign — B6 coefficient-bound proof-term builders.
//!
//! The two scalar `Rat`-order bounds the (2,4)-hypercontractivity B6 step
//! consumes once the spectral sum has been split into its degree-graded legs:
//!
//! - `6·ρ²·t ≤ 2·t`   (from `3·ρ² ≤ 1`, `0 ≤ t`)
//! - `ρ⁴·t  ≤ t`      (from `3·ρ² ≤ 1`, `0 ≤ t`)
//!
//! Every term here is built from the genuinely-`Constructive` `Rat` order
//! surface registered by the B1 toolkit (`Rat.mul_le_mul_of_nonneg_left`,
//! `Rat.mul_le_mul_of_nonneg_right`, `Rat.sq_nonneg`) plus the constructive
//! `Rat.le_trans`, `Rat.mul_assoc`, `Rat.mul_comm`, `Rat.mul_one`,
//! `Rat.one_mul`, `Rat.le_add_of_nonneg_right` and the `Rat.zero_lt_one` /
//! `Rat.lt_iff_le_not_le` bridge to `0 ≤ 1`. Because every dependency is itself
//! `ProofQuality::Constructive` (empty domain-axiom closure), so is every bound
//! registered through these builders.
//!
//! Split from `boolean_analysis_hc_bounds.rs` to keep each file under the
//! 500-line limit (mirrors the order-toolkit / ring-identity splits). The
//! registration entry points live in the parent module; this file holds the
//! pure proof-term construction and the `HcBoundsConsts` plumbing.

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Cached kernel constants + numerals for the B6 bound proof terms. Wraps an
/// `OrderConsts` (for `Rat`, `add`, `mul`, `rat_le`, `subst`, …) and adds the
/// order/ring lemmas the bounds consume.
pub(super) struct HcBoundsConsts {
    pub(super) o: OrderConsts,
    pub(super) mul_le_left: Expr,
    pub(super) mul_le_right: Expr,
    pub(super) le_trans: Expr,
    pub(super) sq_nonneg: Expr,
    pub(super) mul_assoc: Expr,
    pub(super) mul_comm: Expr,
    pub(super) mul_one: Expr,
    pub(super) one_mul: Expr,
    pub(super) le_add_nonneg_right: Expr,
}

impl HcBoundsConsts {
    pub(super) fn new() -> Self {
        Self {
            o: OrderConsts::new(),
            mul_le_left: Expr::const_(Name::from_string("Rat.mul_le_mul_of_nonneg_left"), vec![]),
            mul_le_right: Expr::const_(Name::from_string("Rat.mul_le_mul_of_nonneg_right"), vec![]),
            le_trans: Expr::const_(Name::from_string("Rat.le_trans"), vec![]),
            sq_nonneg: Expr::const_(Name::from_string("Rat.sq_nonneg"), vec![]),
            mul_assoc: Expr::const_(Name::from_string("Rat.mul_assoc"), vec![]),
            mul_comm: Expr::const_(Name::from_string("Rat.mul_comm"), vec![]),
            mul_one: Expr::const_(Name::from_string("Rat.mul_one"), vec![]),
            one_mul: Expr::const_(Name::from_string("Rat.one_mul"), vec![]),
            le_add_nonneg_right: Expr::const_(
                Name::from_string("Rat.le_add_of_nonneg_right"),
                vec![],
            ),
        }
    }

    // ── re-exported atoms ───────────────────────────────────────────────────
    pub(super) fn rat(&self) -> Expr {
        self.o.rat.clone()
    }
    pub(super) fn zero(&self) -> Expr {
        self.o.rat_zero.clone()
    }
    pub(super) fn one(&self) -> Expr {
        self.o.rat_one.clone()
    }
    pub(super) fn mul(&self, a: Expr, b: Expr) -> Expr {
        self.o.mul(a, b)
    }
    pub(super) fn add(&self, a: Expr, b: Expr) -> Expr {
        self.o.add(a, b)
    }
    pub(super) fn le(&self, a: Expr, b: Expr) -> Expr {
        self.o.rat_le(a, b)
    }
    pub(super) fn add_c(&self) -> Expr {
        self.o.rat_add.clone()
    }
    pub(super) fn mul_c(&self) -> Expr {
        self.o.rat_mul.clone()
    }

    /// `2 := 1 + 1`.
    pub(super) fn two(&self) -> Expr {
        self.add(self.one(), self.one())
    }
    /// `3 := (1 + 1) + 1`.
    pub(super) fn three(&self) -> Expr {
        self.add(self.two(), self.one())
    }
    /// `6 := 2 · 3`.
    pub(super) fn six(&self) -> Expr {
        self.mul(self.two(), self.three())
    }

    // ── lemma instances ─────────────────────────────────────────────────────
    /// `Rat.mul_le_mul_of_nonneg_left a b c h_bc h_a : a·b ≤ a·c`.
    pub(super) fn mll(&self, a: Expr, b: Expr, cc: Expr, h_bc: Expr, h_a: Expr) -> Expr {
        Expr::apps(self.mul_le_left.clone(), [a, b, cc, h_bc, h_a])
    }
    /// `Rat.mul_le_mul_of_nonneg_right a b c h_bc h_a : b·a ≤ c·a`.
    pub(super) fn mlr(&self, a: Expr, b: Expr, cc: Expr, h_bc: Expr, h_a: Expr) -> Expr {
        Expr::apps(self.mul_le_right.clone(), [a, b, cc, h_bc, h_a])
    }
    /// `Rat.le_trans a b c h_ab h_bc : a ≤ c`.
    pub(super) fn ltrans(&self, a: Expr, b: Expr, cc: Expr, h_ab: Expr, h_bc: Expr) -> Expr {
        Expr::apps(self.le_trans.clone(), [a, b, cc, h_ab, h_bc])
    }
    /// `Rat.sq_nonneg a : 0 ≤ a·a`.
    pub(super) fn sqnn(&self, a: Expr) -> Expr {
        Expr::app(self.sq_nonneg.clone(), a)
    }
    /// `Rat.mul_assoc a b c : (a·b)·c = a·(b·c)`.
    pub(super) fn massoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.mul_assoc.clone(), [a, b, cc])
    }
    /// `Rat.mul_comm a b : a·b = b·a`.
    pub(super) fn mcomm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.mul_comm.clone(), [a, b])
    }
    /// `Rat.mul_one a : a·1 = a`.
    pub(super) fn mul_one(&self, a: Expr) -> Expr {
        Expr::app(self.mul_one.clone(), a)
    }
    /// `Rat.one_mul a : 1·a = a`.
    pub(super) fn one_mul(&self, a: Expr) -> Expr {
        Expr::app(self.one_mul.clone(), a)
    }
    /// `Rat.le_add_of_nonneg_right a b h : a ≤ a + b`.
    pub(super) fn le_add_nn(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.le_add_nonneg_right.clone(), [a, b, h])
    }

    /// `subst` with motive `fun x => l ≤ x` along `h_eq : from = to`, given
    /// `h : l ≤ from`, producing `l ≤ to`.
    pub(super) fn subst_le_right(
        &self,
        parent: &EnvDeclBuilder,
        l: Expr,
        from: Expr,
        to: Expr,
        h_eq: Expr,
        h: Expr,
    ) -> Expr {
        let motive = {
            let mut ch = EnvDeclBuilder::child_of(parent);
            let (x_id, x) = ch.fresh_local(self.rat());
            let body = self.le(l.clone(), x);
            let r = ch.mk_lam(x_id, BinderInfo::Default, self.rat(), body);
            ch.finish_child(r)
        };
        self.o.subst(motive, from, to, h_eq, h)
    }

    /// `subst` with motive `fun x => x ≤ r` along `h_eq : from = to`, given
    /// `h : from ≤ r`, producing `to ≤ r`.
    pub(super) fn subst_le_left(
        &self,
        parent: &EnvDeclBuilder,
        r: Expr,
        from: Expr,
        to: Expr,
        h_eq: Expr,
        h: Expr,
    ) -> Expr {
        let motive = {
            let mut ch = EnvDeclBuilder::child_of(parent);
            let (x_id, x) = ch.fresh_local(self.rat());
            let body = self.le(x, r.clone());
            let r2 = ch.mk_lam(x_id, BinderInfo::Default, self.rat(), body);
            ch.finish_child(r2)
        };
        self.o.subst(motive, from, to, h_eq, h)
    }

    /// `0 ≤ 1`, from `Rat.zero_lt_one` via `Rat.lt_iff_le_not_le`:
    /// `(lt_iff_le_not_le 0 1).mp zero_lt_one : (0 ≤ 1) ∧ ¬(1 ≤ 0)`, then
    /// `And.left`.
    pub(super) fn zero_le_one(&self) -> Expr {
        let zero = self.zero();
        let one = self.one();
        let lt_01 = Expr::apps(
            Expr::const_(Name::from_string("Rat.lt"), vec![]),
            [zero.clone(), one.clone()],
        );
        let le_01 = self.le(zero.clone(), one.clone());
        let le_10 = self.le(one.clone(), zero.clone());
        let not_le_10 = Expr::app(Expr::const_(Name::from_string("Not"), vec![]), le_10);
        let and_prop = Expr::apps(
            Expr::const_(Name::from_string("And"), vec![]),
            [le_01.clone(), not_le_10.clone()],
        );
        let lt_iff = Expr::apps(
            Expr::const_(Name::from_string("Rat.lt_iff_le_not_le"), vec![]),
            [zero.clone(), one.clone()],
        );
        let zlo = Expr::const_(Name::from_string("Rat.zero_lt_one"), vec![]);
        let mp = Expr::apps(
            Expr::const_(Name::from_string("Iff.mp"), vec![]),
            [lt_01, and_prop, lt_iff, zlo],
        );
        Expr::apps(
            Expr::const_(Name::from_string("And.left"), vec![]),
            [le_01, not_le_10, mp],
        )
    }

    /// `0 ≤ 2` via `le_trans 0 1 2 (0≤1) (1≤2)` with
    /// `1 ≤ 2 = le_add_of_nonneg_right 1 1 (0≤1)`.
    pub(super) fn zero_le_two(&self) -> Expr {
        let zero = self.zero();
        let one = self.one();
        let two = self.two();
        let zle1 = self.zero_le_one();
        let one_le_two = self.le_add_nn(one.clone(), one.clone(), zle1.clone());
        self.ltrans(zero, one, two, zle1, one_le_two)
    }

    /// `1 ≤ 3` via `le_trans 1 2 3 (1≤2) (2≤3)`:
    /// `1 ≤ 2 = le_add_of_nonneg_right 1 1 (0≤1)`,
    /// `2 ≤ 3 = le_add_of_nonneg_right 2 1 (0≤1)`.
    pub(super) fn one_le_three(&self) -> Expr {
        let one = self.one();
        let two = self.two();
        let three = self.three();
        let zle1 = self.zero_le_one();
        let one_le_two = self.le_add_nn(one.clone(), one.clone(), zle1.clone());
        let two_le_three = self.le_add_nn(two.clone(), one.clone(), zle1);
        self.ltrans(one, two, three, one_le_two, two_le_three)
    }
}

// ---------------------------------------------------------------------------
// Type builders
// ---------------------------------------------------------------------------

/// Type of `BoolAnalysis.hc_six_rho_sq_t_le_two_t`:
/// `∀ ρ t, Rat.le (3·(ρ·ρ)) 1 → Rat.le 0 t → Rat.le ((6·(ρ·ρ))·t) (2·t)`.
pub(super) fn six_rho_sq_type(c: &HcBoundsConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat());
    let (t_id, t) = b.fresh_local(c.rat());
    let rho_sq = c.mul(rho.clone(), rho.clone());
    let h_bound_ty = c.le(c.mul(c.three(), rho_sq.clone()), c.one());
    let h_t_ty = c.le(c.zero(), t.clone());
    let lhs = c.mul(c.mul(c.six(), rho_sq), t.clone());
    let rhs = c.mul(c.two(), t.clone());
    let concl = c.le(lhs, rhs);
    let (ht_id, _) = b.fresh_local(h_t_ty.clone());
    let (hb_id, _) = b.fresh_local(h_bound_ty.clone());
    let e = b.mk_pi(ht_id, BinderInfo::Default, h_t_ty, concl);
    let e = b.mk_pi(hb_id, BinderInfo::Default, h_bound_ty, e);
    let e = b.mk_pi(t_id, BinderInfo::Default, c.rat(), e);
    let e = b.mk_pi(rho_id, BinderInfo::Default, c.rat(), e);
    b.finish(e)
}

/// Type of `BoolAnalysis.hc_rho_four_t_le_t`:
/// `∀ ρ t, Rat.le (3·(ρ·ρ)) 1 → Rat.le 0 t → Rat.le (((ρ·ρ)·(ρ·ρ))·t) t`.
pub(super) fn rho_four_type(c: &HcBoundsConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat());
    let (t_id, t) = b.fresh_local(c.rat());
    let rho_sq = c.mul(rho.clone(), rho.clone());
    let rho_four = c.mul(rho_sq.clone(), rho_sq.clone());
    let h_bound_ty = c.le(c.mul(c.three(), rho_sq.clone()), c.one());
    let h_t_ty = c.le(c.zero(), t.clone());
    let lhs = c.mul(rho_four, t.clone());
    let concl = c.le(lhs, t.clone());
    let (ht_id, _) = b.fresh_local(h_t_ty.clone());
    let (hb_id, _) = b.fresh_local(h_bound_ty.clone());
    let e = b.mk_pi(ht_id, BinderInfo::Default, h_t_ty, concl);
    let e = b.mk_pi(hb_id, BinderInfo::Default, h_bound_ty, e);
    let e = b.mk_pi(t_id, BinderInfo::Default, c.rat(), e);
    let e = b.mk_pi(rho_id, BinderInfo::Default, c.rat(), e);
    b.finish(e)
}

// ---------------------------------------------------------------------------
// Proof builders
// ---------------------------------------------------------------------------

/// Build the proof term for `BoolAnalysis.hc_six_rho_sq_t_le_two_t`.
///
/// Let `s := ρ·ρ`. From `h_bound : 3·s ≤ 1`:
///   1. `mul_le_left 2 (3·s) 1 h_bound (0≤2) : 2·(3·s) ≤ 2·1`.
///   2. `mul_assoc 2 3 s : (2·3)·s = 2·(3·s)`, i.e. `6·s = 2·(3·s)` since
///      `6 := 2·3`. subst LHS `2·(3·s) → 6·s` gives `6·s ≤ 2·1`.
///   3. `mul_one 2 : 2·1 = 2`. subst RHS gives `6·s ≤ 2`.
///   4. `mul_le_right t (6·s) 2 (6·s ≤ 2) (0≤t) : (6·s)·t ≤ 2·t`.
pub(super) fn build_six_rho_sq_proof(c: &HcBoundsConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat());
    let (t_id, t) = b.fresh_local(c.rat());
    let rho_sq = c.mul(rho.clone(), rho.clone());
    let h_bound_ty = c.le(c.mul(c.three(), rho_sq.clone()), c.one());
    let h_t_ty = c.le(c.zero(), t.clone());
    let (hb_id, h_bound) = b.fresh_local(h_bound_ty.clone());
    let (ht_id, h_t) = b.fresh_local(h_t_ty.clone());

    let two = c.two();
    let three = c.three();
    let six = c.six();
    let three_s = c.mul(three.clone(), rho_sq.clone()); // 3·s
    let two_three_s = c.mul(two.clone(), three_s.clone()); // 2·(3·s)
    let two_one = c.mul(two.clone(), c.one()); // 2·1
    let six_s = c.mul(six.clone(), rho_sq.clone()); // 6·s = (2·3)·s

    // 1. 2·(3·s) ≤ 2·1.
    let zle2 = c.zero_le_two();
    let step1 = c.mll(two.clone(), three_s.clone(), c.one(), h_bound, zle2); // 2·(3·s) ≤ 2·1

    // 2. (2·3)·s = 2·(3·s) ; subst LHS from 2·(3·s) to 6·s needs the SYMM
    //    orientation 2·(3·s) = (2·3)·s.
    let h_assoc = c.massoc(two.clone(), three.clone(), rho_sq.clone()); // (2·3)·s = 2·(3·s)
    let h_assoc_sym = c.o.symm(six_s.clone(), two_three_s.clone(), h_assoc); // 2·(3·s) = (2·3)·s
    let step2 = c.subst_le_left(
        &b,
        two_one.clone(),
        two_three_s.clone(),
        six_s.clone(),
        h_assoc_sym,
        step1,
    ); // 6·s ≤ 2·1

    // 3. 2·1 = 2 ; subst RHS.
    let h_mul_one = c.mul_one(two.clone()); // 2·1 = 2
    let step3 = c.subst_le_right(
        &b,
        six_s.clone(),
        two_one.clone(),
        two.clone(),
        h_mul_one,
        step2,
    ); // 6·s ≤ 2

    // 4. (6·s)·t ≤ 2·t.
    let body = c.mlr(t.clone(), six_s.clone(), two.clone(), step3, h_t);

    let e = b.mk_lam(ht_id, BinderInfo::Default, h_t_ty, body);
    let e = b.mk_lam(hb_id, BinderInfo::Default, h_bound_ty, e);
    let e = b.mk_lam(t_id, BinderInfo::Default, c.rat(), e);
    let e = b.mk_lam(rho_id, BinderInfo::Default, c.rat(), e);
    b.finish(e)
}

/// Build the proof term for `BoolAnalysis.hc_rho_four_t_le_t`.
///
/// Let `s := ρ·ρ`. From `h_bound : 3·s ≤ 1`:
///   A. `s ≤ 1`:
///      - `s ≤ 3·s`: `mul_le_left s 1 3 (1≤3) (0≤s) : s·1 ≤ s·3`,
///        rewrite `s·1 → s` (`mul_one`) and `s·3 → 3·s` (`mul_comm`).
///      - `le_trans s (3·s) 1 (s ≤ 3·s) h_bound : s ≤ 1`.
///   B. `s·s ≤ 1`:
///      - `mul_le_left s s 1 (s≤1) (0≤s) : s·s ≤ s·1`,
///      - `mul_le_right 1 s 1 (s≤1) (0≤1) : s·1 ≤ 1·1`,
///      - `le_trans` → `s·s ≤ 1·1`; rewrite `1·1 → 1` (`one_mul`) → `s·s ≤ 1`.
///   C. `mul_le_right t (s·s) 1 (s·s≤1) (0≤t) : (s·s)·t ≤ 1·t`,
///      rewrite `1·t → t` (`one_mul`) → `(s·s)·t ≤ t`.
pub(super) fn build_rho_four_proof(c: &HcBoundsConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat());
    let (t_id, t) = b.fresh_local(c.rat());
    let s = c.mul(rho.clone(), rho.clone()); // s := ρ·ρ
    let h_bound_ty = c.le(c.mul(c.three(), s.clone()), c.one());
    let h_t_ty = c.le(c.zero(), t.clone());
    let (hb_id, h_bound) = b.fresh_local(h_bound_ty.clone());
    let (ht_id, h_t) = b.fresh_local(h_t_ty.clone());

    let one = c.one();
    let three = c.three();
    let s_nn = c.sqnn(rho.clone()); // 0 ≤ s
    let zle1 = c.zero_le_one();

    // ── A. s ≤ 1 ────────────────────────────────────────────────────────────
    // s·1 ≤ s·3   [mul_le_left s 1 3 (1≤3) (0≤s)]
    let one_le_three = c.one_le_three();
    let s1_le_s3 = c.mll(
        s.clone(),
        one.clone(),
        three.clone(),
        one_le_three,
        s_nn.clone(),
    );
    let s_times_1 = c.mul(s.clone(), one.clone()); // s·1
    let s_times_3 = c.mul(s.clone(), three.clone()); // s·3
    let three_s = c.mul(three.clone(), s.clone()); // 3·s
                                                   // rewrite LHS s·1 → s
    let h_s1 = c.mul_one(s.clone()); // s·1 = s
    let a1 = c.subst_le_left(&b, s_times_3.clone(), s_times_1, s.clone(), h_s1, s1_le_s3); // s ≤ s·3
                                                                                           // rewrite RHS s·3 → 3·s
    let h_s3 = c.mcomm(s.clone(), three.clone()); // s·3 = 3·s
    let s_le_3s = c.subst_le_right(&b, s.clone(), s_times_3, three_s.clone(), h_s3, a1); // s ≤ 3·s
                                                                                         // le_trans s (3·s) 1
    let s_le_1 = c.ltrans(s.clone(), three_s, one.clone(), s_le_3s, h_bound); // s ≤ 1

    // ── B. s·s ≤ 1 ──────────────────────────────────────────────────────────
    let ss = c.mul(s.clone(), s.clone()); // s·s
    let s_times_1b = c.mul(s.clone(), one.clone()); // s·1
    let one_one = c.mul(one.clone(), one.clone()); // 1·1
                                                   // s·s ≤ s·1   [mul_le_left s s 1 (s≤1) (0≤s)]
    let ss_le_s1 = c.mll(
        s.clone(),
        s.clone(),
        one.clone(),
        s_le_1.clone(),
        s_nn.clone(),
    );
    // s·1 ≤ 1·1   [mul_le_right 1 s 1 (s≤1) (0≤1)]
    let s1_le_11 = c.mlr(one.clone(), s.clone(), one.clone(), s_le_1, zle1.clone());
    // le_trans s·s s·1 1·1
    let ss_le_11 = c.ltrans(ss.clone(), s_times_1b, one_one.clone(), ss_le_s1, s1_le_11);
    // rewrite RHS 1·1 → 1
    let h_11 = c.one_mul(one.clone()); // 1·1 = 1
    let ss_le_1 = c.subst_le_right(&b, ss.clone(), one_one, one.clone(), h_11, ss_le_11); // s·s ≤ 1

    // ── C. (s·s)·t ≤ t ──────────────────────────────────────────────────────
    let one_t = c.mul(one.clone(), t.clone()); // 1·t
                                               // (s·s)·t ≤ 1·t   [mul_le_right t (s·s) 1 (s·s≤1) (0≤t)]
    let sst_le_1t = c.mlr(t.clone(), ss.clone(), one.clone(), ss_le_1, h_t);
    let sst = c.mul(ss.clone(), t.clone()); // (s·s)·t
                                            // rewrite RHS 1·t → t
    let h_1t = c.one_mul(t.clone()); // 1·t = t
    let body = c.subst_le_right(&b, sst, one_t, t.clone(), h_1t, sst_le_1t); // (s·s)·t ≤ t

    let e = b.mk_lam(ht_id, BinderInfo::Default, h_t_ty, body);
    let e = b.mk_lam(hb_id, BinderInfo::Default, h_bound_ty, e);
    let e = b.mk_lam(t_id, BinderInfo::Default, c.rat(), e);
    let e = b.mk_lam(rho_id, BinderInfo::Default, c.rat(), e);
    b.finish(e)
}
