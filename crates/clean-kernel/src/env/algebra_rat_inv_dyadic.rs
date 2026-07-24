// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — the `Rat.inv` quotient bridge (Stage B3, sqrt run #3).
//!
//! # Why this module exists
//!
//! The dyadic-floor sqrt construction (plan
//! `designs/2026-06-18-kkl-real-sqrt-layer-plan.md` §8.4 items 4/4a/4c) needs
//! the Cauchy modulus `Rat.inv (ofNat 2^n) < ε`. The frontier the prior runs
//! hit is reasoning about `Rat.inv` on the QUOTIENT carrier — its body is a
//! sign-split `Quot.lift` and never reduces. The unblock is: NEVER reason about
//! `Rat.inv` directly; reason about it ONLY through multiplication by the
//! positive argument, via the axiom-free quotient theorem `Rat.mul_inv_cancel`
//! (`b ≠ 0 → b · inv b = 1`).
//!
//! # What this module registers (axiom-free, kernel-checked)
//!
//! - `Rat.ne_zero_of_pos : ∀ b : Rat, Rat.lt Rat.zero b → @Eq Rat b Rat.zero → False`.
//! - `Rat.inv_pos : ∀ b : Rat, Rat.lt Rat.zero b → Rat.lt Rat.zero (Rat.inv b)`.
//! - `Rat.inv_lt_of_one_lt_mul : ∀ b c : Rat, Rat.lt Rat.zero b →
//!       Rat.lt Rat.one (Rat.mul c b) → Rat.lt (Rat.inv b) c`
//!   — the consumer direction of the inv↔mul bridge: `1 < c·b ⟹ inv b < c`.
//!   Combined with `Rat.exists_pow_gt` (`∀ε>0, ∃N, 1 < ε·2^N`) this is the whole
//!   dyadic modulus `inv(2^N) < ε`.
//!
//! Every declaration is a checked `Theorem` through `self.add_decl`; every
//! theorem's transitive admitted-axiom closure is empty (foundational only).
//! NO `sorry` / `add_decl_unchecked` / `add_decl_structural`.
//!
//! # Proof idioms (the multiplicative bridge)
//!
//! Both `inv` proofs reduce a goal about `inv b` to a goal about `c · b` (or
//! `0 · b`) via the cancellation `(inv b) · b = 1`:
//!   `inv_mul_eq_one : (inv b)·b = 1`
//!     = `Eq.trans (mul_comm (inv b) b) (mul_inv_cancel b (b ≠ 0))`,
//! where `b ≠ 0` is `Rat.ne_zero_of_pos b (0 < b)` (substitute the `b = 0`
//! hypothesis into `0 < b` to get `0 < 0`, then refute via `lt_iff_le_not_le`).
//!
//! `inv_lt_of_one_lt_mul`: goal `inv b < c` opens via `lt_iff_le_not_le.mpr` on
//! `And (inv b ≤ c) (¬ c ≤ inv b)`. The `¬ c ≤ inv b` half: from `c ≤ inv b`,
//! `mul_le_mul_of_nonneg_right c (inv b) b · (0 ≤ b)` gives `c·b ≤ (inv b)·b`,
//! transport the RHS to `1` (the cancellation), so `c·b ≤ 1`, contradicting the
//! hypothesis `1 < c·b` (`not_le_of_lt 1 (c·b)`). The `inv b ≤ c` half: by
//! `le_total (inv b) c`, the left disjunct is it directly; the right disjunct
//! (`c ≤ inv b`) feeds the contradiction → `False.elim`.
//!
//! `inv_pos`: identical skeleton with `c := 0`; `0·b = 0` (`zero_mul`) so the
//! contradiction is `1 ≤ 0` against `0 < 1` (`zero_lt_one`).
//!
//! # Universe note
//!
//! `Eq` / `Eq.symm` / `Eq.trans` / `Eq.subst` over `Rat : Type 0 = Sort 1` are
//! all at universe **1**. `Or.rec` / `False.elim` motives over `Rat.le … : Prop`
//! are at universe **0**.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved constant handles + smart-constructors for the `Rat.inv` bridge.
pub(crate) struct InvBridgeConsts {
    rat: Expr,
    rat_zero: Expr,
    rat_one: Expr,
    rat_mul: Expr,
    rat_inv: Expr,
    rat_lt: Expr,
    rat_le: Expr,
    rat_mul_comm: Expr,
    rat_mul_inv_cancel: Expr,
    rat_zero_mul: Expr,
    rat_zero_lt_one: Expr,
    rat_le_total: Expr,
    rat_lt_iff_le_not_le: Expr,
    rat_mul_le_mul_of_nonneg_right: Expr,
    eq_rat: Expr,
    eq_trans: Expr,
    eq_subst: Expr,
    and_c: Expr,
    and_intro: Expr,
    and_left: Expr,
    and_right: Expr,
    or_c: Expr,
    or_rec: Expr,
    not_c: Expr,
    iff_mp: Expr,
    iff_mpr: Expr,
    false_c: Expr,
    false_elim: Expr,
}

impl InvBridgeConsts {
    pub(crate) fn new() -> Self {
        let l0 = Level::zero();
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_one: k("Rat.one"),
            rat_mul: k("Rat.mul"),
            rat_inv: k("Rat.inv"),
            rat_lt: k("Rat.lt"),
            rat_le: k("Rat.le"),
            rat_mul_comm: k("Rat.mul_comm"),
            rat_mul_inv_cancel: k("Rat.mul_inv_cancel"),
            rat_zero_mul: k("Rat.zero_mul"),
            rat_zero_lt_one: k("Rat.zero_lt_one"),
            rat_le_total: k("Rat.le_total"),
            rat_lt_iff_le_not_le: k("Rat.lt_iff_le_not_le"),
            rat_mul_le_mul_of_nonneg_right: k("Rat.mul_le_mul_of_nonneg_right"),
            eq_rat: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![l1]),
            and_c: k("And"),
            and_intro: k("And.intro"),
            and_left: k("And.left"),
            and_right: k("And.right"),
            or_c: k("Or"),
            or_rec: k("Or.rec"),
            not_c: k("Not"),
            iff_mp: k("Iff.mp"),
            iff_mpr: k("Iff.mpr"),
            false_c: k("False"),
            false_elim: Expr::const_(Name::from_string("False.elim"), vec![l0]),
        }
    }

    // ── term constructors ───────────────────────────────────────────────────
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn inv(&self, a: Expr) -> Expr {
        Expr::app(self.rat_inv.clone(), a)
    }
    fn lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a, b])
    }
    fn not_(&self, p: Expr) -> Expr {
        Expr::app(self.not_c.clone(), p)
    }
    fn and(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.and_c.clone(), [p, q])
    }
    fn or(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.or_c.clone(), [p, q])
    }
    fn eq_ty(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq_rat.clone(), [self.rat.clone(), a, b])
    }

    // ── proof constructors ──────────────────────────────────────────────────
    fn eq_trans(&self, a: Expr, b: Expr, cc: Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(
            self.eq_trans.clone(),
            [self.rat.clone(), a, b, cc, hab, hbc],
        )
    }
    /// `@Eq.subst Rat motive a b h_eq h : motive b`.
    fn eq_subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h],
        )
    }
    fn mul_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul_comm.clone(), [a, b])
    }
    /// `Rat.mul_inv_cancel a h : a·(inv a) = 1`  (h : a = 0 → False).
    fn mul_inv_cancel(&self, a: Expr, h: Expr) -> Expr {
        Expr::apps(self.rat_mul_inv_cancel.clone(), [a, h])
    }
    fn zero_mul(&self, a: Expr) -> Expr {
        Expr::app(self.rat_zero_mul.clone(), a)
    }
    /// `Rat.mul_le_mul_of_nonneg_right a b c (h_bc:b≤c)(h_a:0≤a) : b·a ≤ c·a`.
    /// NOTE: the FIRST positional arg `a` is the RIGHT multiplier; `b`/`c` are
    /// the compared operands.
    fn mul_le_right(&self, a: Expr, b: Expr, cc: Expr, hbc: Expr, ha: Expr) -> Expr {
        Expr::apps(
            self.rat_mul_le_mul_of_nonneg_right.clone(),
            [a, b, cc, hbc, ha],
        )
    }
    /// `0 ≤ x` from `0 < x`:  `And.left (Iff.mp (lt_iff_le_not_le 0 x) h)`.
    fn le_of_pos(&self, x: Expr, h_pos: Expr) -> Expr {
        let le0x = self.le(self.rat_zero.clone(), x.clone());
        let not_le_x0 = self.not_(self.le(x.clone(), self.rat_zero.clone()));
        let and_ty = self.and(le0x.clone(), not_le_x0.clone());
        let lt0x = self.lt(self.rat_zero.clone(), x.clone());
        let iff = Expr::apps(
            self.rat_lt_iff_le_not_le.clone(),
            [self.rat_zero.clone(), x],
        );
        let mp = Expr::apps(self.iff_mp.clone(), [lt0x, and_ty, iff, h_pos]);
        Expr::apps(self.and_left.clone(), [le0x, not_le_x0, mp])
    }
    /// `¬(b ≤ a)` from `h : a < b` via `And.right (Iff.mp (lt_iff_le_not_le a b) h)`.
    fn not_le_of_lt(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        let le_ab = self.le(a.clone(), b.clone());
        let not_le_ba = self.not_(self.le(b.clone(), a.clone()));
        let and_ty = self.and(le_ab.clone(), not_le_ba.clone());
        let lt_ab = self.lt(a.clone(), b.clone());
        let iff = Expr::apps(self.rat_lt_iff_le_not_le.clone(), [a, b]);
        let mp = Expr::apps(self.iff_mp.clone(), [lt_ab, and_ty, iff, h]);
        Expr::apps(self.and_right.clone(), [le_ab, not_le_ba, mp])
    }
    /// `(inv b)·b = 1`  := `Eq.trans (mul_comm (inv b) b) (mul_inv_cancel b hb_ne)`.
    fn inv_mul_eq_one(&self, b: Expr, inv_b: Expr, hb_ne: Expr) -> Expr {
        let invb_b = self.mul(inv_b.clone(), b.clone());
        let b_invb = self.mul(b.clone(), inv_b.clone());
        let comm = self.mul_comm(inv_b, b.clone()); // (inv b)·b = b·(inv b)
        let cancel = self.mul_inv_cancel(b, hb_ne); // b·(inv b) = 1
        self.eq_trans(invb_b, b_invb, self.rat_one.clone(), comm, cancel)
    }
}

impl Environment {
    /// Register the `Rat.inv` multiplicative bridge: `Rat.ne_zero_of_pos`,
    /// `Rat.inv_pos`, `Rat.inv_lt_of_one_lt_mul`. Idempotent.
    pub fn init_algebra_rat_inv_dyadic(&mut self) -> Result<(), EnvError> {
        self.init_eq()?;
        self.init_and()?;
        self.init_or()?;
        self.init_iff()?;
        self.init_true_false()?;
        // Live `Rat` field lemmas: zero_mul, mul_comm, mul_inv_cancel.
        self.init_rat_field_inst()?;
        // Rat.le_total, Rat.lt_iff_le_not_le.
        self.init_rat_linear_order()?;
        // Rat.zero_lt_one, Rat.lt_iff_le_not_le, Rat.le_total.
        self.register_rat_order_proofs()?;
        // Rat.mul_le_mul_of_nonneg_right.
        self.init_boolean_analysis_order_toolkit()?;

        let c = InvBridgeConsts::new();
        self.register_rat_ne_zero_of_pos(&c)?;
        self.register_rat_inv_pos(&c)?;
        self.register_rat_inv_lt_of_one_lt_mul(&c)?;
        Ok(())
    }

    /// `Rat.ne_zero_of_pos : ∀ b : Rat,
    ///     Rat.lt Rat.zero b → @Eq Rat b Rat.zero → False`.
    fn register_rat_ne_zero_of_pos(&mut self, c: &InvBridgeConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.ne_zero_of_pos");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let zero = c.rat_zero.clone();
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let pos = c.lt(zero.clone(), bv.clone());
            let (hp_id, _hp) = b.fresh_local(pos.clone());
            let eq0 = c.eq_ty(bv.clone(), zero.clone());
            let (he_id, _he) = b.fresh_local(eq0.clone());
            let e = b.mk_pi(he_id, BinderInfo::Default, eq0, c.false_c.clone());
            let e = b.mk_pi(hp_id, BinderInfo::Default, pos, e);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let pos = c.lt(zero.clone(), bv.clone());
            let (hp_id, hp) = b.fresh_local(pos.clone());
            let eq0 = c.eq_ty(bv.clone(), zero.clone());
            let (he_id, he) = b.fresh_local(eq0.clone());

            // Substitute b := 0 (via he : b = 0): motive t := Rat.lt 0 t.
            let motive = {
                let mut mb = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = mb.fresh_local(c.rat.clone());
                let body = c.lt(zero.clone(), t);
                mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
            };
            let lt00 = c.eq_subst(motive, bv.clone(), zero.clone(), he, hp);
            let not_le_00 = c.not_le_of_lt(zero.clone(), zero.clone(), lt00.clone());
            let le_00 = c.le_of_pos(zero.clone(), lt00);
            let false_proof = Expr::app(not_le_00, le_00);

            let e = b.mk_lam(he_id, BinderInfo::Default, eq0, false_proof);
            let e = b.mk_lam(hp_id, BinderInfo::Default, pos, e);
            let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.inv_pos : ∀ b : Rat, Rat.lt Rat.zero b → Rat.lt Rat.zero (Rat.inv b)`.
    fn register_rat_inv_pos(&mut self, c: &InvBridgeConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.inv_pos");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let zero = c.rat_zero.clone();
        let one = c.rat_one.clone();
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let pos = c.lt(zero.clone(), bv.clone());
            let (hp_id, _hp) = b.fresh_local(pos.clone());
            let concl = c.lt(zero.clone(), c.inv(bv.clone()));
            let e = b.mk_pi(hp_id, BinderInfo::Default, pos, concl);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let pos = c.lt(zero.clone(), bv.clone());
            let (hp_id, hp) = b.fresh_local(pos.clone());
            let inv_b = c.inv(bv.clone());

            let hb_le = c.le_of_pos(bv.clone(), hp.clone());
            let hb_ne = Expr::apps(
                Expr::const_(Name::from_string("Rat.ne_zero_of_pos"), vec![]),
                [bv.clone(), hp.clone()],
            );
            let cancel = c.inv_mul_eq_one(bv.clone(), inv_b.clone(), hb_ne);
            let invb_b = c.mul(inv_b.clone(), bv.clone());
            let zero_b = c.mul(zero.clone(), bv.clone());
            let zm = c.zero_mul(bv.clone()); // 0·b = 0

            // not_one_le_zero : ¬(1 ≤ 0).
            let not_one_le_zero =
                c.not_le_of_lt(zero.clone(), one.clone(), c.rat_zero_lt_one.clone());

            // ── ¬(inv b ≤ 0) ────────────────────────────────────────────────
            let le_iv0 = c.le(inv_b.clone(), zero.clone());
            let not_inv_le_zero = {
                let mut nb = EnvDeclBuilder::child_of(&b);
                let (h_id, h) = nb.fresh_local(le_iv0.clone());
                // mul_le_right b (inv b) 0 (h : inv b ≤ 0)(hb_le : 0 ≤ b)
                //   : (inv b)·b ≤ 0·b.
                let step =
                    c.mul_le_right(bv.clone(), inv_b.clone(), zero.clone(), h, hb_le.clone());
                // transport LHS (inv b)·b → 1 (cancel): motive t := t ≤ 0·b.
                let motive_l = {
                    let mut mb = EnvDeclBuilder::child_of(&nb);
                    let (t_id, t) = mb.fresh_local(c.rat.clone());
                    let body = c.le(t, zero_b.clone());
                    mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                let one_le_zerob =
                    c.eq_subst(motive_l, invb_b.clone(), one.clone(), cancel.clone(), step);
                // transport RHS 0·b → 0 (zm): motive t := 1 ≤ t.
                let motive_r = {
                    let mut mb = EnvDeclBuilder::child_of(&nb);
                    let (t_id, t) = mb.fresh_local(c.rat.clone());
                    let body = c.le(one.clone(), t);
                    mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                let one_le_zero = c.eq_subst(
                    motive_r,
                    zero_b.clone(),
                    zero.clone(),
                    zm.clone(),
                    one_le_zerob,
                );
                let body = Expr::app(not_one_le_zero.clone(), one_le_zero);
                nb.finish_child(nb.mk_lam(h_id, BinderInfo::Default, le_iv0.clone(), body))
            };

            // ── 0 ≤ inv b (via le_total 0 (inv b), right branch → False) ─────
            let le_0_inv = c.le(zero.clone(), inv_b.clone());
            let tot = Expr::apps(c.rat_le_total.clone(), [zero.clone(), inv_b.clone()]);
            let or_motive = {
                let mut mb = EnvDeclBuilder::child_of(&b);
                let or_ty = c.or(le_0_inv.clone(), le_iv0.clone());
                let (z_id, _z) = mb.fresh_local(or_ty.clone());
                mb.finish_child(mb.mk_lam(z_id, BinderInfo::Default, or_ty, le_0_inv.clone()))
            };
            let left = {
                let mut lb = EnvDeclBuilder::child_of(&b);
                let (h_id, h) = lb.fresh_local(le_0_inv.clone());
                lb.finish_child(lb.mk_lam(h_id, BinderInfo::Default, le_0_inv.clone(), h))
            };
            let right = {
                let mut rb = EnvDeclBuilder::child_of(&b);
                let (h_id, h) = rb.fresh_local(le_iv0.clone());
                let false_val = Expr::app(not_inv_le_zero.clone(), h);
                let body = Expr::apps(c.false_elim.clone(), [le_0_inv.clone(), false_val]);
                rb.finish_child(rb.mk_lam(h_id, BinderInfo::Default, le_iv0.clone(), body))
            };
            let h_0_le_inv = Expr::apps(
                c.or_rec.clone(),
                [
                    le_0_inv.clone(),
                    le_iv0.clone(),
                    or_motive,
                    left,
                    right,
                    tot,
                ],
            );

            let conj = Expr::apps(
                c.and_intro.clone(),
                [
                    le_0_inv.clone(),
                    c.not_(le_iv0.clone()),
                    h_0_le_inv,
                    not_inv_le_zero,
                ],
            );
            let lt_0_inv = c.lt(zero.clone(), inv_b.clone());
            let and_ty = c.and(le_0_inv, c.not_(le_iv0));
            let iff = Expr::apps(
                c.rat_lt_iff_le_not_le.clone(),
                [zero.clone(), inv_b.clone()],
            );
            let body = Expr::apps(c.iff_mpr.clone(), [lt_0_inv, and_ty, iff, conj]);

            let e = b.mk_lam(hp_id, BinderInfo::Default, pos, body);
            let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.inv_lt_of_one_lt_mul : ∀ b c : Rat, Rat.lt Rat.zero b →
    ///     Rat.lt Rat.one (Rat.mul c b) → Rat.lt (Rat.inv b) c`.
    fn register_rat_inv_lt_of_one_lt_mul(&mut self, c: &InvBridgeConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.inv_lt_of_one_lt_mul");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let zero = c.rat_zero.clone();
        let one = c.rat_one.clone();
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let (cv_id, cv) = b.fresh_local(c.rat.clone());
            let pos = c.lt(zero.clone(), bv.clone());
            let (hp_id, _hp) = b.fresh_local(pos.clone());
            let hm = c.lt(one.clone(), c.mul(cv.clone(), bv.clone()));
            let (hm_id, _hm) = b.fresh_local(hm.clone());
            let concl = c.lt(c.inv(bv.clone()), cv.clone());
            let e = b.mk_pi(hm_id, BinderInfo::Default, hm, concl);
            let e = b.mk_pi(hp_id, BinderInfo::Default, pos, e);
            let e = b.mk_pi(cv_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let (cv_id, cv) = b.fresh_local(c.rat.clone());
            let pos = c.lt(zero.clone(), bv.clone());
            let (hp_id, hp) = b.fresh_local(pos.clone());
            let cb = c.mul(cv.clone(), bv.clone());
            let hm_ty = c.lt(one.clone(), cb.clone());
            let (hm_id, hm) = b.fresh_local(hm_ty.clone());
            let inv_b = c.inv(bv.clone());

            let hb_le = c.le_of_pos(bv.clone(), hp.clone());
            let hb_ne = Expr::apps(
                Expr::const_(Name::from_string("Rat.ne_zero_of_pos"), vec![]),
                [bv.clone(), hp.clone()],
            );
            let cancel = c.inv_mul_eq_one(bv.clone(), inv_b.clone(), hb_ne);
            let invb_b = c.mul(inv_b.clone(), bv.clone());
            // not_cb_le_one : ¬(c·b ≤ 1) from hm : 1 < c·b.
            let not_cb_le_one = c.not_le_of_lt(one.clone(), cb.clone(), hm);

            // ── ¬(c ≤ inv b) ────────────────────────────────────────────────
            let le_c_inv = c.le(cv.clone(), inv_b.clone());
            let not_c_le_inv = {
                let mut nb = EnvDeclBuilder::child_of(&b);
                let (h_id, h) = nb.fresh_local(le_c_inv.clone());
                // mul_le_right b c (inv b) (h : c ≤ inv b)(hb_le : 0 ≤ b)
                //   : c·b ≤ (inv b)·b.
                let cb_le = c.mul_le_right(bv.clone(), cv.clone(), inv_b.clone(), h, hb_le.clone());
                // transport RHS (inv b)·b → 1 (cancel): motive t := c·b ≤ t.
                let motive = {
                    let mut mb = EnvDeclBuilder::child_of(&nb);
                    let (t_id, t) = mb.fresh_local(c.rat.clone());
                    let body = c.le(cb.clone(), t);
                    mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                let cb_le_one =
                    c.eq_subst(motive, invb_b.clone(), one.clone(), cancel.clone(), cb_le);
                let body = Expr::app(not_cb_le_one.clone(), cb_le_one);
                nb.finish_child(nb.mk_lam(h_id, BinderInfo::Default, le_c_inv.clone(), body))
            };

            // ── inv b ≤ c (via le_total (inv b) c, right branch → False) ─────
            let le_inv_c = c.le(inv_b.clone(), cv.clone());
            let tot = Expr::apps(c.rat_le_total.clone(), [inv_b.clone(), cv.clone()]);
            let or_motive = {
                let mut mb = EnvDeclBuilder::child_of(&b);
                let or_ty = c.or(le_inv_c.clone(), le_c_inv.clone());
                let (z_id, _z) = mb.fresh_local(or_ty.clone());
                mb.finish_child(mb.mk_lam(z_id, BinderInfo::Default, or_ty, le_inv_c.clone()))
            };
            let left = {
                let mut lb = EnvDeclBuilder::child_of(&b);
                let (h_id, h) = lb.fresh_local(le_inv_c.clone());
                lb.finish_child(lb.mk_lam(h_id, BinderInfo::Default, le_inv_c.clone(), h))
            };
            let right = {
                let mut rb = EnvDeclBuilder::child_of(&b);
                let (h_id, h) = rb.fresh_local(le_c_inv.clone());
                let false_val = Expr::app(not_c_le_inv.clone(), h);
                let body = Expr::apps(c.false_elim.clone(), [le_inv_c.clone(), false_val]);
                rb.finish_child(rb.mk_lam(h_id, BinderInfo::Default, le_c_inv.clone(), body))
            };
            let h_inv_le_c = Expr::apps(
                c.or_rec.clone(),
                [
                    le_inv_c.clone(),
                    le_c_inv.clone(),
                    or_motive,
                    left,
                    right,
                    tot,
                ],
            );

            let conj = Expr::apps(
                c.and_intro.clone(),
                [
                    le_inv_c.clone(),
                    c.not_(le_c_inv.clone()),
                    h_inv_le_c,
                    not_c_le_inv,
                ],
            );
            let lt_inv_c = c.lt(inv_b.clone(), cv.clone());
            let and_ty = c.and(le_inv_c, c.not_(le_c_inv));
            let iff = Expr::apps(c.rat_lt_iff_le_not_le.clone(), [inv_b.clone(), cv.clone()]);
            let body = Expr::apps(c.iff_mpr.clone(), [lt_inv_c, and_ty, iff, conj]);

            let e = b.mk_lam(hm_id, BinderInfo::Default, hm_ty, body);
            let e = b.mk_lam(hp_id, BinderInfo::Default, pos, e);
            let e = b.mk_lam(cv_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const THEOREMS: &[&str] = &[
        "Rat.ne_zero_of_pos",
        "Rat.inv_pos",
        "Rat.inv_lt_of_one_lt_mul",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_rat_inv_dyadic()
            .expect("init_algebra_rat_inv_dyadic");
        env.init_algebra_rat_inv_dyadic().expect("idempotent");
        env
    }

    #[test]
    fn test_rat_inv_dyadic_present_and_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in THEOREMS {
            let nm = Name::from_string(name);
            let info = env
                .get_const(&nm)
                .unwrap_or_else(|| panic!("{name} registered"));
            let value = info.value.clone().expect("value present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
        }
    }

    #[test]
    fn test_rat_inv_dyadic_theorems_constructive_empty_closure() {
        let env = env();
        for name in THEOREMS {
            let nm = Name::from_string(name);
            let info = env.get_const(&nm).expect("registered");
            assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be Theorem");
            assert_eq!(
                env.proof_quality(&nm),
                Some(ProofQuality::Constructive),
                "{name} must be Constructive"
            );
            assert!(
                env.axiom_deps(&nm).expect("deps").is_empty(),
                "{name} closure must be foundational-only: {:?}",
                env.axiom_deps(&nm)
            );
        }
    }
}
