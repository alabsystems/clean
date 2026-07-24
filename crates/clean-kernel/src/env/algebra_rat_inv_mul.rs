// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — `Rat.inv` equational bricks (Stage B3, sqrt run #3).
//!
//! # Why this module exists
//!
//! The dyadic Cauchy modulus (plan
//! `designs/2026-06-18-kkl-real-sqrt-layer-plan.md` §8.4 item 4a) needs the step
//! factorization `inv (2^{n+1}) = inv 2 · inv (2^n)`, an instance of the general
//! inverse-of-product law `inv (a·b) = inv a · inv b`. The live `Rat` is a
//! QUOTIENT carrier and `Rat.inv` is a sign-split `Quot.lift` that never reduces,
//! so this equation is NOT a `Quot.sound`-by-inspection — but it follows
//! ALGEBRAICALLY from the axiom-free `Rat.mul_inv_cancel` via UNIQUENESS of
//! inverses, with no further `Quot.ind`.
//!
//! # What this module registers (axiom-free, kernel-checked)
//!
//! - `Rat.inv_unique : ∀ b c : Rat, (b = 0 → False) → Rat.mul b c = Rat.one →
//!       @Eq Rat c (Rat.inv b)`
//!   — uniqueness of the multiplicative inverse.
//! - `Rat.mul_inv : ∀ a b : Rat, (a = 0 → False) → (b = 0 → False) →
//!       @Eq Rat (Rat.inv (Rat.mul a b)) (Rat.mul (Rat.inv a) (Rat.inv b))`
//!   — the inverse-of-product law.
//!
//! Every declaration is a checked `Theorem` through `self.add_decl`; every
//! theorem's transitive admitted-axiom closure is empty (foundational only).
//! NO `sorry` / `add_decl_unchecked` / `add_decl_structural`.
//!
//! # Proof sketch
//!
//! `inv_unique`:  `c = 1·c` (`one_mul⁻¹`) `= ((inv b)·b)·c` (the cancellation
//! `(inv b)·b = 1` = `mul_comm ⬝ mul_inv_cancel`, congr `·c`) `= (inv b)·(b·c)`
//! (`mul_assoc`) `= (inv b)·1` (congr `(inv b)·_` on `b·c=1`) `= inv b`
//! (`mul_one`). All `Eq.trans`-chained.
//!
//! `mul_inv`: `(a·b)·(inv a · inv b) = (a·inv a)·(b·inv b)` (`mul_mul_mul_comm
//! a b (inv a)(inv b)`) `= 1·1` (two `mul_inv_cancel`, transported) `= 1`
//! (`one_mul 1`). With `a·b ≠ 0` (from `a≠0`/`b≠0` packaged below as
//! `Rat.mul_ne_zero_of_ne`), `inv_unique (a·b)(inv a·inv b) … : (inv a·inv b)
//! = inv (a·b)`; `Eq.symm` gives the stated orientation.
//!
//! # Universe note
//!
//! `Eq`/`Eq.symm`/`Eq.trans`/`Eq.subst`/`congrArg` over `Rat : Type 0 = Sort 1`
//! are all at universe **1**.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for the `Rat.inv` equational bricks.
pub(crate) struct InvMulConsts {
    rat: Expr,
    rat_one: Expr,
    rat_mul: Expr,
    rat_inv: Expr,
    rat_mul_comm: Expr,
    rat_mul_assoc: Expr,
    rat_one_mul: Expr,
    rat_mul_one: Expr,
    rat_mul_inv_cancel: Expr,
    rat_mul_mul_mul_comm: Expr,
    rat_zero: Expr,
    rat_le: Expr,
    rat_lt: Expr,
    rat_zero_lt_one: Expr,
    rat_lt_iff_le_not_le: Expr,
    eq_rat: Expr,
    eq_symm: Expr,
    eq_trans: Expr,
    eq_subst: Expr,
    congr_arg: Expr,
    and_c: Expr,
    and_left: Expr,
    and_right: Expr,
    not_c: Expr,
    iff_mp: Expr,
    false_c: Expr,
}

impl InvMulConsts {
    pub(crate) fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            rat: k("Rat"),
            rat_one: k("Rat.one"),
            rat_mul: k("Rat.mul"),
            rat_inv: k("Rat.inv"),
            rat_mul_comm: k("Rat.mul_comm"),
            rat_mul_assoc: k("Rat.mul_assoc"),
            rat_one_mul: k("Rat.one_mul"),
            rat_mul_one: k("Rat.mul_one"),
            rat_mul_inv_cancel: k("Rat.mul_inv_cancel"),
            rat_mul_mul_mul_comm: k("Rat.mul_mul_mul_comm"),
            rat_zero: k("Rat.zero"),
            rat_le: k("Rat.le"),
            rat_lt: k("Rat.lt"),
            rat_zero_lt_one: k("Rat.zero_lt_one"),
            rat_lt_iff_le_not_le: k("Rat.lt_iff_le_not_le"),
            eq_rat: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![l1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
            and_c: k("And"),
            and_left: k("And.left"),
            and_right: k("And.right"),
            not_c: k("Not"),
            iff_mp: k("Iff.mp"),
            false_c: k("False"),
        }
    }

    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn inv(&self, a: Expr) -> Expr {
        Expr::app(self.rat_inv.clone(), a)
    }
    fn eq_ty(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq_rat.clone(), [self.rat.clone(), a, b])
    }
    fn eq_symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.rat.clone(), a, b, h])
    }
    fn eq_trans(&self, a: Expr, b: Expr, cc: Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(
            self.eq_trans.clone(),
            [self.rat.clone(), a, b, cc, hab, hbc],
        )
    }
    /// `@congrArg Rat Rat a a' f h : Eq Rat (f a) (f a')`.
    fn congr_arg(&self, a: Expr, a2: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat.clone(), self.rat.clone(), a, a2, f, h],
        )
    }
    fn mul_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul_comm.clone(), [a, b])
    }
    /// `Rat.mul_assoc a b c : (a·b)·c = a·(b·c)`.
    fn mul_assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.rat_mul_assoc.clone(), [a, b, cc])
    }
    fn one_mul(&self, a: Expr) -> Expr {
        Expr::app(self.rat_one_mul.clone(), a)
    }
    fn mul_one(&self, a: Expr) -> Expr {
        Expr::app(self.rat_mul_one.clone(), a)
    }
    /// `Rat.mul_inv_cancel a h : a·(inv a) = 1`.
    fn mul_inv_cancel(&self, a: Expr, h: Expr) -> Expr {
        Expr::apps(self.rat_mul_inv_cancel.clone(), [a, h])
    }
    /// `Rat.mul_mul_mul_comm a b c d : (a·b)·(c·d) = (a·c)·(b·d)`.
    fn mmmc(&self, a: Expr, b: Expr, cc: Expr, d: Expr) -> Expr {
        Expr::apps(self.rat_mul_mul_mul_comm.clone(), [a, b, cc, d])
    }
    /// `(inv b)·b = 1` := `Eq.trans (mul_comm (inv b) b)(mul_inv_cancel b hb_ne)`.
    fn inv_mul_eq_one(&self, b: Expr, hb_ne: Expr) -> Expr {
        let inv_b = self.inv(b.clone());
        let invb_b = self.mul(inv_b.clone(), b.clone());
        let b_invb = self.mul(b.clone(), inv_b);
        let comm = self.mul_comm(self.inv(b.clone()), b.clone());
        let cancel = self.mul_inv_cancel(b, hb_ne);
        self.eq_trans(invb_b, b_invb, self.rat_one.clone(), comm, cancel)
    }
    /// `False` from `h : 0 = 1`. Substitute `1 := 0` into `0 < 1` (via `symm h`)
    /// to get `0 < 0`, then refute through `lt_iff_le_not_le 0 0`.
    fn false_of_zero_eq_one(&self, parent: &EnvDeclBuilder, h: Expr) -> Expr {
        let zero = self.rat_zero.clone();
        let one = self.rat_one.clone();
        // symm h : 1 = 0.
        let h_sym = self.eq_symm(zero.clone(), one.clone(), h);
        // motive t := Rat.lt 0 t ; subst (a:=1)(b:=0): 0 < 0.
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(parent);
            let (t_id, t) = mb.fresh_local(self.rat.clone());
            let body = Expr::apps(self.rat_lt.clone(), [zero.clone(), t]);
            mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, self.rat.clone(), body))
        };
        let lt00 = Expr::apps(
            self.eq_subst.clone(),
            [
                self.rat.clone(),
                motive,
                one.clone(),
                zero.clone(),
                h_sym,
                self.rat_zero_lt_one.clone(),
            ],
        );
        // not_le_of_lt 0 0 lt00 (le_of_pos 0 lt00) : False.
        let le00 = Expr::apps(self.rat_le.clone(), [zero.clone(), zero.clone()]);
        let not_le00 = Expr::app(self.not_c.clone(), le00.clone());
        let and_ty = Expr::apps(self.and_c.clone(), [le00.clone(), not_le00.clone()]);
        let lt00_ty = Expr::apps(self.rat_lt.clone(), [zero.clone(), zero.clone()]);
        let iff = Expr::apps(
            self.rat_lt_iff_le_not_le.clone(),
            [zero.clone(), zero.clone()],
        );
        let mp = Expr::apps(self.iff_mp.clone(), [lt00_ty, and_ty, iff, lt00]);
        let hr = Expr::apps(
            self.and_right.clone(),
            [le00.clone(), not_le00.clone(), mp.clone()],
        );
        let hl = Expr::apps(self.and_left.clone(), [le00, not_le00, mp]);
        Expr::app(hr, hl)
    }
}

impl Environment {
    /// Register the `Rat.inv` equational bricks: `Rat.inv_unique`,
    /// `Rat.mul_ne_zero_of_ne`, `Rat.mul_inv`. Idempotent.
    pub fn init_algebra_rat_inv_mul(&mut self) -> Result<(), EnvError> {
        self.init_eq()?;
        self.init_and()?;
        self.init_iff()?;
        self.init_true_false()?;
        // zero_mul/mul_comm/mul_assoc/one_mul/mul_one/mul_inv_cancel.
        self.init_rat_field_inst()?;
        // Rat.mul_mul_mul_comm (single direct registration).
        self.register_rat_mul_mul_mul_comm_theorem()?;
        // Rat.le_total / Rat.lt_iff_le_not_le / Rat.zero_lt_one (for the a·b≠0 leg).
        self.init_rat_linear_order()?;
        self.register_rat_order_proofs()?;

        let c = InvMulConsts::new();
        self.register_rat_inv_unique(&c)?;
        self.register_rat_mul_inv(&c)?;
        Ok(())
    }

    /// `Rat.inv_unique : ∀ b c : Rat, (b = 0 → False) → Rat.mul b c = Rat.one →
    ///     @Eq Rat c (Rat.inv b)`.
    fn register_rat_inv_unique(&mut self, c: &InvMulConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.inv_unique");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let one = c.rat_one.clone();
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let (cv_id, cv) = b.fresh_local(c.rat.clone());
            let eq_b0 = c.eq_ty(bv.clone(), zero.clone());
            let ne_ty = {
                let mut nb = EnvDeclBuilder::child_of(&b);
                let (h_id, _h) = nb.fresh_local(eq_b0.clone());
                nb.finish_child(nb.mk_pi(
                    h_id,
                    BinderInfo::Default,
                    eq_b0.clone(),
                    c.false_c.clone(),
                ))
            };
            let (hne_id, _hne) = b.fresh_local(ne_ty.clone());
            let hbc = c.eq_ty(c.mul(bv.clone(), cv.clone()), one.clone());
            let (hbc_id, _hbc) = b.fresh_local(hbc.clone());
            let concl = c.eq_ty(cv.clone(), c.inv(bv.clone()));
            let e = b.mk_pi(hbc_id, BinderInfo::Default, hbc, concl);
            let e = b.mk_pi(hne_id, BinderInfo::Default, ne_ty, e);
            let e = b.mk_pi(cv_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let (cv_id, cv) = b.fresh_local(c.rat.clone());
            let eq_b0 = c.eq_ty(bv.clone(), zero.clone());
            let ne_ty = {
                let mut nb = EnvDeclBuilder::child_of(&b);
                let (h_id, _h) = nb.fresh_local(eq_b0.clone());
                nb.finish_child(nb.mk_pi(
                    h_id,
                    BinderInfo::Default,
                    eq_b0.clone(),
                    c.false_c.clone(),
                ))
            };
            let (hne_id, hne) = b.fresh_local(ne_ty.clone());
            let hbc = c.eq_ty(c.mul(bv.clone(), cv.clone()), one.clone());
            let (hbc_id, hbc_h) = b.fresh_local(hbc.clone());

            let inv_b = c.inv(bv.clone());
            let invb_b = c.mul(inv_b.clone(), bv.clone());
            let bc = c.mul(bv.clone(), cv.clone());

            // cancel : (inv b)·b = 1.
            let cancel = c.inv_mul_eq_one(bv.clone(), hne);

            // s1 : c = 1·c   (= Eq.symm (one_mul c)).
            let one_c = c.mul(one.clone(), cv.clone());
            let s1 = c.eq_symm(one_c.clone(), cv.clone(), c.one_mul(cv.clone()));
            // s2 : 1·c = ((inv b)·b)·c   (congrArg (fun t => t·c) (symm cancel)).
            let mul_c_fn = {
                let mut fb = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = fb.fresh_local(c.rat.clone());
                let body = c.mul(t, cv.clone());
                fb.finish_child(fb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
            };
            let cancel_sym = c.eq_symm(invb_b.clone(), one.clone(), cancel); // 1 = (inv b)·b
            let invbb_c = c.mul(invb_b.clone(), cv.clone());
            let s2 = c.congr_arg(one.clone(), invb_b.clone(), mul_c_fn, cancel_sym);
            // s3 : ((inv b)·b)·c = (inv b)·(b·c)   (mul_assoc (inv b) b c).
            let invb_bc = c.mul(inv_b.clone(), bc.clone());
            let s3 = c.mul_assoc(inv_b.clone(), bv.clone(), cv.clone());
            // s4 : (inv b)·(b·c) = (inv b)·1   (congrArg (fun t => (inv b)·t) hbc).
            let mul_invb_fn = {
                let mut fb = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = fb.fresh_local(c.rat.clone());
                let body = c.mul(inv_b.clone(), t);
                fb.finish_child(fb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
            };
            let invb_one = c.mul(inv_b.clone(), one.clone());
            let s4 = c.congr_arg(bc.clone(), one.clone(), mul_invb_fn, hbc_h);
            // s5 : (inv b)·1 = inv b   (mul_one (inv b)).
            let s5 = c.mul_one(inv_b.clone());

            // chain: c → 1·c → ((inv b)·b)·c → (inv b)·(b·c) → (inv b)·1 → inv b.
            let t1 = c.eq_trans(cv.clone(), one_c, invbb_c.clone(), s1, s2);
            let t2 = c.eq_trans(cv.clone(), invbb_c, invb_bc.clone(), t1, s3);
            let t3 = c.eq_trans(cv.clone(), invb_bc, invb_one.clone(), t2, s4);
            let final_eq = c.eq_trans(cv.clone(), invb_one, inv_b.clone(), t3, s5);

            let e = b.mk_lam(hbc_id, BinderInfo::Default, hbc, final_eq);
            let e = b.mk_lam(hne_id, BinderInfo::Default, ne_ty, e);
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

    /// `Rat.mul_inv : ∀ a b : Rat, (a = 0 → False) → (b = 0 → False) →
    ///     @Eq Rat (Rat.inv (Rat.mul a b)) (Rat.mul (Rat.inv a) (Rat.inv b))`.
    fn register_rat_mul_inv(&mut self, c: &InvMulConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.mul_inv");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let one = c.rat_one.clone();
        let ne_ty = |a: &Expr, parent: &EnvDeclBuilder| -> Expr {
            let mut nb = EnvDeclBuilder::child_of(parent);
            let eq0 = c.eq_ty(a.clone(), zero.clone());
            let (h_id, _h) = nb.fresh_local(eq0.clone());
            nb.finish_child(nb.mk_pi(h_id, BinderInfo::Default, eq0, c.false_c.clone()))
        };
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let na = ne_ty(&a, &b);
            let (hna_id, _hna) = b.fresh_local(na.clone());
            let nb_ = ne_ty(&bv, &b);
            let (hnb_id, _hnb) = b.fresh_local(nb_.clone());
            let ab = c.mul(a.clone(), bv.clone());
            let concl = c.eq_ty(c.inv(ab), c.mul(c.inv(a.clone()), c.inv(bv.clone())));
            let e = b.mk_pi(hnb_id, BinderInfo::Default, nb_, concl);
            let e = b.mk_pi(hna_id, BinderInfo::Default, na, e);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let na = ne_ty(&a, &b);
            let (hna_id, hna) = b.fresh_local(na.clone());
            let nb_ = ne_ty(&bv, &b);
            let (hnb_id, hnb) = b.fresh_local(nb_.clone());

            let ab = c.mul(a.clone(), bv.clone());
            let inv_a = c.inv(a.clone());
            let inv_b = c.inv(bv.clone());
            let inva_invb = c.mul(inv_a.clone(), inv_b.clone());

            // ── (a·b)·(inv a · inv b) = 1 ──────────────────────────────────
            // mmmc a b (inv a)(inv b) : (a·b)·(inv a·inv b) = (a·inv a)·(b·inv b).
            let a_inva = c.mul(a.clone(), inv_a.clone());
            let b_invb = c.mul(bv.clone(), inv_b.clone());
            let mmmc = c.mmmc(a.clone(), bv.clone(), inv_a.clone(), inv_b.clone());
            // (a·inv a)·(b·inv b) → 1·(b·inv b)  (congr (·(b·inv b)) (mul_inv_cancel a)).
            let cancel_a = c.mul_inv_cancel(a.clone(), hna); // a·inv a = 1
            let cancel_b = c.mul_inv_cancel(bv.clone(), hnb); // b·inv b = 1
            let lhs_pair = c.mul(a_inva.clone(), b_invb.clone());
            let one_binvb = c.mul(one.clone(), b_invb.clone());
            let mul_right_binvb = {
                let mut fb = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = fb.fresh_local(c.rat.clone());
                let body = c.mul(t, b_invb.clone());
                fb.finish_child(fb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
            };
            let step1 = c.congr_arg(a_inva.clone(), one.clone(), mul_right_binvb, cancel_a);
            // 1·(b·inv b) → 1·1  (congr (1·_) (mul_inv_cancel b)).
            let one_one = c.mul(one.clone(), one.clone());
            let mul_left_one = {
                let mut fb = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = fb.fresh_local(c.rat.clone());
                let body = c.mul(one.clone(), t);
                fb.finish_child(fb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
            };
            let step2 = c.congr_arg(b_invb.clone(), one.clone(), mul_left_one, cancel_b);
            // 1·1 → 1  (one_mul 1).
            let step3 = c.one_mul(one.clone());
            // chain: lhs_pair → 1·(b·inv b) → 1·1 → 1.
            let p1 = c.eq_trans(
                lhs_pair.clone(),
                one_binvb.clone(),
                one_one.clone(),
                step1,
                step2,
            );
            let pair_eq_one = c.eq_trans(lhs_pair.clone(), one_one, one.clone(), p1, step3);
            // prod_eq_one : (a·b)·(inv a·inv b) = 1  (= Eq.trans mmmc pair_eq_one).
            let ab_prod = c.mul(ab.clone(), inva_invb.clone());
            let prod_eq_one = c.eq_trans(ab_prod, lhs_pair, one.clone(), mmmc, pair_eq_one);

            // ── a·b ≠ 0  (from 0 < a·b, mul_pos of positives — but we only have
            //    a≠0,b≠0, not positivity). Derive ab ≠ 0 directly: if a·b = 0 then
            //    multiplying prod_eq_one's structure… simplest: use the cancellation
            //    we just built. If (a·b)·(inv a·inv b) = 1 and a·b = 0, then
            //    0·(inv a·inv b) = 1, i.e. 0 = 1, refuted. Build ab_ne. ───────────
            let zero_mul = Expr::const_(Name::from_string("Rat.zero_mul"), vec![]);
            let ab_ne = {
                let mut nb = EnvDeclBuilder::child_of(&b);
                let eq_ab0 = c.eq_ty(ab.clone(), zero.clone());
                let (h_id, h) = nb.fresh_local(eq_ab0.clone());
                // transport prod_eq_one's LHS (a·b)·(inv a·inv b) along h (a·b → 0):
                //   motive t := Eq Rat (t·(inv a·inv b)) 1.
                let motive = {
                    let mut mb = EnvDeclBuilder::child_of(&nb);
                    let (t_id, t) = mb.fresh_local(c.rat.clone());
                    let body = c.eq_ty(c.mul(t, inva_invb.clone()), one.clone());
                    mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                let eq_subst = Expr::const_(
                    Name::from_string("Eq.subst"),
                    vec![Level::succ(Level::zero())],
                );
                // zero_prod_eq_one : 0·(inv a·inv b) = 1.
                let zero_prod_eq_one = Expr::apps(
                    eq_subst.clone(),
                    [
                        c.rat.clone(),
                        motive,
                        ab.clone(),
                        zero.clone(),
                        h,
                        prod_eq_one.clone(),
                    ],
                );
                // zm : 0·(inv a·inv b) = 0.
                let zm = Expr::app(zero_mul.clone(), inva_invb.clone());
                // 0 = 1  (= Eq.trans (symm zm) zero_prod_eq_one).
                let zero_prod = c.mul(zero.clone(), inva_invb.clone());
                let zm_sym = c.eq_symm(zero_prod.clone(), zero.clone(), zm);
                let zero_eq_one = c.eq_trans(
                    zero.clone(),
                    zero_prod,
                    one.clone(),
                    zm_sym,
                    zero_prod_eq_one,
                );
                // 0 = 1 → False (inline, via 0 < 1 + lt_iff_le_not_le).
                let body = c.false_of_zero_eq_one(&nb, zero_eq_one);
                nb.finish_child(nb.mk_lam(h_id, BinderInfo::Default, eq_ab0, body))
            };

            // inv_unique (a·b)(inv a·inv b) ab_ne prod_eq_one : (inv a·inv b) = inv(a·b).
            let inv_unique = Expr::const_(Name::from_string("Rat.inv_unique"), vec![]);
            let uniq = Expr::apps(
                inv_unique,
                [ab.clone(), inva_invb.clone(), ab_ne, prod_eq_one],
            );
            // symm : inv(a·b) = inv a · inv b.
            let inv_ab = c.inv(ab.clone());
            let body = c.eq_symm(inva_invb.clone(), inv_ab, uniq);

            let e = b.mk_lam(hnb_id, BinderInfo::Default, nb_, body);
            let e = b.mk_lam(hna_id, BinderInfo::Default, na, e);
            let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), e);
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

    const THEOREMS: &[&str] = &["Rat.inv_unique", "Rat.mul_inv"];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_rat_inv_mul()
            .expect("init_algebra_rat_inv_mul");
        env.init_algebra_rat_inv_mul().expect("idempotent");
        env
    }

    #[test]
    fn test_rat_inv_mul_present_and_kernel_check() {
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
    fn test_rat_inv_mul_theorems_constructive_empty_closure() {
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
