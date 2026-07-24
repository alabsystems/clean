// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — Component A, Step (2): the δ-CHOICE for
//! `NNReal.IsCauchy_mul`.
//!
//! # Why this module exists
//!
//! `NNReal.IsCauchy_mul` needs, given a target tolerance `ε` and a combined
//! factor bound `D := Bf + Bg + 1` (`D ≥ 1 > 0`), a single Cauchy-band
//! tolerance `δ` with
//!
//! - `0 < δ`         (so the factor IsCauchy hypotheses can be instantiated)
//! - `δ · D ≤ ε/2`   (so the two cross terms `δ·Bg + Bf·δ = δ·(Bf+Bg) ≤ δ·D`
//!   stay below `ε`).
//!
//! The plan's §7.5 flagged the naive route (expanding `(vfn+δ)(vgn+δ)`, which
//! emits a `δ²` term) as needing a `δ ≤ 1` min and a heavy division layer.
//! The CROSS-TERM split used by `IsCauchy_mul` (bounding one factor by `Bf`
//! instead of by `vfn+δ`) AVOIDS the `δ²` term entirely, so the only
//! arithmetic fact needed here is the EXACT cancellation `δ·D = ε/2` for
//! `δ := (ε/2)/D`, plus its positivity.
//!
//! # What this module registers (axiom-free, kernel-checked)
//!
//! - `Rat.pos_of_mul_pos_of_nonneg : ∀ a b, Rat.lt 0 (a·b) → Rat.le 0 b →
//!       Rat.lt 0 a`  — positivity transfer (contrapositive: `a≤0 ⟹ a·b≤0`).
//! - `Rat.deltaMul : Rat → Rat → Rat := fun ε D => Rat.div (Rat.div ε Rat.two) D`
//!   (reducible).
//! - `Rat.deltaMul_mul_eq : ∀ ε D, (D = 0 → False) →
//!       @Eq Rat (Rat.mul (Rat.deltaMul ε D) D) (Rat.div ε Rat.two)`
//!   (the exact cancellation `((ε/2)·inv D)·D = ε/2`).
//! - `Rat.deltaMul_pos : ∀ ε D, Rat.lt 0 ε → Rat.lt 0 D →
//!       Rat.lt 0 (Rat.deltaMul ε D)`.
//!
//! Every declaration is a checked `Definition`/`Theorem` through `self.add_decl`;
//! every theorem's transitive admitted-axiom closure is empty (foundational
//! only). NO `sorry` / `add_decl_unchecked` / `add_decl_structural`.
//!
//! # Proof sketches
//!
//! `pos_of_mul_pos_of_nonneg` (mirror of `Rat.half_pos`'s structure): from
//! `le_total 0 a` either `0≤a` is what we want (combined with `a≠0` from the
//! product being nonzero — but we want STRICT, so we instead refute `a≤0`):
//! the refutation is `a ≤ 0`, `0 ≤ b ⟹ a·b ≤ 0·b = 0` (via
//! `mul_le_mul_of_nonneg_right` then `zero_mul`), contradicting `0 < a·b`
//! (`¬(a·b ≤ 0)`). We build `0 < a` via
//! `Iff.mpr (lt_iff_le_not_le 0 a)` from `And (0≤a) (¬a≤0)`, where `0≤a` is the
//! `le_total` left branch (right branch `a≤0` is refuted) and `¬a≤0` is the
//! refutation lambda.
//!
//! `deltaMul_mul_eq`: `δ·D = ((ε/2)·inv D)·D = (ε/2)·(inv D · D)` [`mul_assoc`]
//! `= (ε/2)·(D · inv D)` [`congrArg ((ε/2)·) (mul_comm (inv D) D)`]
//! `= (ε/2)·1` [`congrArg ((ε/2)·) (mul_inv_cancel D D≠0)`] `= ε/2` [`mul_one`].
//!
//! `deltaMul_pos`: `δ·D = ε/2` (`deltaMul_mul_eq`, `D≠0` from `0<D`), and
//! `0 < ε/2` (`Rat.half_pos`), so `0 < δ·D`; with `0 ≤ D` (from `0<D`),
//! `pos_of_mul_pos_of_nonneg` gives `0 < δ`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for the δ-choice lemmas.
pub(crate) struct DeltaChoiceConsts {
    rat: Expr,
    rat_zero: Expr,
    rat_two: Expr,
    rat_one: Expr,
    rat_mul: Expr,
    rat_div: Expr,
    rat_inv: Expr,
    rat_le: Expr,
    rat_lt: Expr,
    // Field/order lemmas.
    rat_mul_assoc: Expr,
    rat_mul_comm: Expr,
    rat_mul_one: Expr,
    rat_mul_inv_cancel: Expr,
    rat_mul_le_right: Expr,
    rat_zero_mul: Expr,
    rat_le_total: Expr,
    rat_le_refl: Expr,
    rat_half_pos: Expr,
    rat_lt_iff_le_not_le: Expr,
    // Logic.
    and_c: Expr,
    and_intro: Expr,
    and_left: Expr,
    and_right: Expr,
    or_c: Expr,
    or_rec: Expr,
    not_c: Expr,
    false_c: Expr,
    false_elim: Expr,
    iff_mp: Expr,
    iff_mpr: Expr,
    // Eq.{1} over Rat.
    eq_rat: Expr,
    eq_symm: Expr,
    eq_trans: Expr,
    eq_subst: Expr,
    congr_arg: Expr,
}

impl DeltaChoiceConsts {
    pub(crate) fn new() -> Self {
        let lvl1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_two: k("Rat.two"),
            rat_one: k("Rat.one"),
            rat_mul: k("Rat.mul"),
            rat_div: k("Rat.div"),
            rat_inv: k("Rat.inv"),
            rat_le: k("Rat.le"),
            rat_lt: k("Rat.lt"),
            rat_mul_assoc: k("Rat.mul_assoc"),
            rat_mul_comm: k("Rat.mul_comm"),
            rat_mul_one: k("Rat.mul_one"),
            rat_mul_inv_cancel: k("Rat.mul_inv_cancel"),
            rat_mul_le_right: k("Rat.mul_le_mul_of_nonneg_right"),
            rat_zero_mul: k("Rat.zero_mul"),
            rat_le_total: k("Rat.le_total"),
            rat_le_refl: k("Rat.le_refl"),
            rat_half_pos: k("Rat.half_pos"),
            rat_lt_iff_le_not_le: k("Rat.lt_iff_le_not_le"),
            and_c: k("And"),
            and_intro: k("And.intro"),
            and_left: k("And.left"),
            and_right: k("And.right"),
            or_c: k("Or"),
            or_rec: k("Or.rec"),
            not_c: k("Not"),
            false_c: k("False"),
            false_elim: Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
            iff_mp: k("Iff.mp"),
            iff_mpr: k("Iff.mpr"),
            eq_rat: Expr::const_(Name::from_string("Eq"), vec![lvl1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![lvl1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![lvl1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![lvl1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![lvl1.clone(), lvl1]),
        }
    }

    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn div(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_div.clone(), [a, b])
    }
    fn inv(&self, a: Expr) -> Expr {
        Expr::app(self.rat_inv.clone(), a)
    }
    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a, b])
    }
    fn lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    fn nonneg(&self, a: Expr) -> Expr {
        self.le(self.rat_zero.clone(), a)
    }
    fn not_(&self, p: Expr) -> Expr {
        Expr::app(self.not_c.clone(), p)
    }
    fn half(&self, eps: Expr) -> Expr {
        self.div(eps, self.rat_two.clone())
    }
    fn eq_ty(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq_rat.clone(), [self.rat.clone(), a, b])
    }
    /// `Rat.mul_assoc a b c : Eq Rat ((a·b)·c) (a·(b·c))`.
    fn mul_assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.rat_mul_assoc.clone(), [a, b, cc])
    }
    /// `Rat.mul_comm a b : Eq Rat (a·b) (b·a)`.
    fn mul_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul_comm.clone(), [a, b])
    }
    /// `Rat.mul_one a : Eq Rat (a·1) a`.
    fn mul_one(&self, a: Expr) -> Expr {
        Expr::app(self.rat_mul_one.clone(), a)
    }
    /// `Rat.mul_inv_cancel a (h : a=0→False) : Eq Rat (a · inv a) 1`.
    fn mul_inv_cancel(&self, a: Expr, h: Expr) -> Expr {
        Expr::apps(self.rat_mul_inv_cancel.clone(), [a, h])
    }
    /// `Rat.mul_le_mul_of_nonneg_right a b c (h: b≤c)(h0: 0≤a) : b·a ≤ c·a`.
    fn mul_le_right(&self, a: Expr, b: Expr, cc: Expr, hbc: Expr, h0: Expr) -> Expr {
        Expr::apps(self.rat_mul_le_right.clone(), [a, b, cc, hbc, h0])
    }
    /// `Rat.zero_mul a : Eq Rat (0·a) 0`.
    fn zero_mul(&self, a: Expr) -> Expr {
        Expr::app(self.rat_zero_mul.clone(), a)
    }
    /// `Rat.half_pos eps (h: 0<eps) : Rat.lt 0 (eps/2)`.
    fn half_pos(&self, eps: Expr, h: Expr) -> Expr {
        Expr::apps(self.rat_half_pos.clone(), [eps, h])
    }
    /// `@Eq.symm Rat a b h : Eq Rat b a`.
    fn eq_symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.rat.clone(), a, b, h])
    }
    /// `@Eq.trans Rat a b c hab hbc : Eq Rat a c`.
    fn eq_trans(&self, a: Expr, b: Expr, cc: Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(
            self.eq_trans.clone(),
            [self.rat.clone(), a, b, cc, hab, hbc],
        )
    }
    /// `@Eq.subst Rat motive a b h_eq h : motive b`.
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h],
        )
    }
    /// `@congrArg Rat Rat a a' f h : Eq Rat (f a)(f a')`.
    fn congr_arg(&self, a: Expr, a2: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat.clone(), self.rat.clone(), a, a2, f, h],
        )
    }
    /// `Rat.deltaMul ε D : Rat`  (= `(ε/2)/D`).
    fn delta_mul(&self, eps: Expr, d: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.deltaMul"), vec![]),
            [eps, d],
        )
    }
    /// The `a ≠ 0` proposition `Eq Rat a 0 → False`.
    fn ne_zero_ty(&self, parent: &EnvDeclBuilder, a: &Expr) -> Expr {
        let mut bb = EnvDeclBuilder::child_of(parent);
        let eq0 = self.eq_ty(a.clone(), self.rat_zero.clone());
        let (h_id, _h) = bb.fresh_local(eq0.clone());
        bb.finish_child(bb.mk_pi(h_id, BinderInfo::Default, eq0, self.false_c.clone()))
    }
    /// Extract `¬(b ≤ a)` from `h : Rat.lt a b` via
    /// `And.right (Iff.mp (Rat.lt_iff_le_not_le a b) h)`.
    fn not_le_of_lt(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        let le_ab = self.le(a.clone(), b.clone());
        let not_le_ba = self.not_(self.le(b.clone(), a.clone()));
        let and_ty = Expr::apps(self.and_c.clone(), [le_ab.clone(), not_le_ba.clone()]);
        let lt_ab = self.lt(a.clone(), b.clone());
        let iff = Expr::apps(self.rat_lt_iff_le_not_le.clone(), [a, b]);
        let mp = Expr::apps(self.iff_mp.clone(), [lt_ab, and_ty, iff, h]);
        Expr::apps(self.and_right.clone(), [le_ab, not_le_ba, mp])
    }
}

impl Environment {
    /// Register the δ-choice surface. Idempotent.
    pub fn init_algebra_rat_delta_choice(&mut self) -> Result<(), EnvError> {
        // mul_le_mul_of_nonneg_right, lt_iff_le_not_le, le_total, mul lemmas.
        self.init_boolean_analysis_order_toolkit()?; // mul_le_mul_of_nonneg_right
        self.init_boolean_analysis_order_toolkit_b1b()?; // lt_iff_le_not_le
        self.register_rat_order_proofs()?; // Rat.le_total, Rat.le_refl, Rat.mul_pos
        self.register_rat_mul_assoc_proof()?; // Rat.mul_assoc
        self.register_rat_mul_comm_proof()?; // Rat.mul_comm
        self.init_rat_field_inst()?; // Rat.mul_one, Rat.one_mul, Rat.zero_mul, Rat.div, Rat.inv
        self.init_algebra_rat_half_pos()?; // Rat.half_pos, Rat.two, Rat.div
        self.init_or()?;
        self.init_and()?;
        self.init_iff()?;
        self.init_true_false()?;

        let c = DeltaChoiceConsts::new();
        self.register_rat_pos_of_mul_pos_of_nonneg(&c)?;
        self.register_rat_delta_mul(&c)?;
        self.register_rat_delta_mul_mul_eq(&c)?;
        self.register_rat_delta_mul_pos(&c)?;
        Ok(())
    }

    /// `Rat.pos_of_mul_pos_of_nonneg : ∀ a b, Rat.lt 0 (a·b) → Rat.le 0 b →
    ///     Rat.lt 0 a`.
    fn register_rat_pos_of_mul_pos_of_nonneg(
        &mut self,
        c: &DeltaChoiceConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.pos_of_mul_pos_of_nonneg");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let hmul = c.lt(c.rat_zero.clone(), c.mul(a.clone(), bv.clone()));
            let (hm_id, _) = b.fresh_local(hmul.clone());
            let h0b = c.nonneg(bv.clone());
            let (h0b_id, _) = b.fresh_local(h0b.clone());
            let concl = c.lt(c.rat_zero.clone(), a.clone());
            let e = b.mk_pi(h0b_id, BinderInfo::Default, h0b, concl);
            let e = b.mk_pi(hm_id, BinderInfo::Default, hmul, e);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        let value = build_pos_of_mul_pos_proof(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.deltaMul : Rat → Rat → Rat := fun ε D => (ε/2)/D`.
    fn register_rat_delta_mul(&mut self, c: &DeltaChoiceConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.deltaMul");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = Expr::pi(
            BinderInfo::Default,
            c.rat.clone(),
            Expr::pi(BinderInfo::Default, c.rat.clone(), c.rat.clone()),
        );
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (e_id, eps) = b.fresh_local(c.rat.clone());
            let (d_id, d) = b.fresh_local(c.rat.clone());
            let body = c.div(c.half(eps.clone()), d);
            let e = b.mk_lam(d_id, BinderInfo::Default, c.rat.clone(), body);
            let e = b.mk_lam(e_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `Rat.deltaMul_mul_eq : ∀ ε D, (D = 0 → False) →
    ///     @Eq Rat (Rat.mul (Rat.deltaMul ε D) D) (Rat.div ε Rat.two)`.
    fn register_rat_delta_mul_mul_eq(&mut self, c: &DeltaChoiceConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.deltaMul_mul_eq");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (e_id, eps) = b.fresh_local(c.rat.clone());
            let (d_id, d) = b.fresh_local(c.rat.clone());
            let ne = c.ne_zero_ty(&b, &d);
            let (ne_id, _) = b.fresh_local(ne.clone());
            let lhs = c.mul(c.delta_mul(eps.clone(), d.clone()), d.clone());
            let concl = c.eq_ty(lhs, c.half(eps.clone()));
            let e = b.mk_pi(ne_id, BinderInfo::Default, ne, concl);
            let e = b.mk_pi(d_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(e_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        let value = build_delta_mul_mul_eq_proof(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.deltaMul_pos : ∀ ε D, Rat.lt 0 ε → Rat.lt 0 D →
    ///     Rat.lt 0 (Rat.deltaMul ε D)`.
    fn register_rat_delta_mul_pos(&mut self, c: &DeltaChoiceConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.deltaMul_pos");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (e_id, eps) = b.fresh_local(c.rat.clone());
            let (d_id, d) = b.fresh_local(c.rat.clone());
            let h0e = c.lt(c.rat_zero.clone(), eps.clone());
            let (h0e_id, _) = b.fresh_local(h0e.clone());
            let h0d = c.lt(c.rat_zero.clone(), d.clone());
            let (h0d_id, _) = b.fresh_local(h0d.clone());
            let concl = c.lt(c.rat_zero.clone(), c.delta_mul(eps.clone(), d.clone()));
            let e = b.mk_pi(h0d_id, BinderInfo::Default, h0d, concl);
            let e = b.mk_pi(h0e_id, BinderInfo::Default, h0e, e);
            let e = b.mk_pi(d_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(e_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        let value = build_delta_mul_pos_proof(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// Build `Rat.pos_of_mul_pos_of_nonneg`.
fn build_pos_of_mul_pos_proof(c: &DeltaChoiceConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (bv_id, bv) = b.fresh_local(c.rat.clone());
    let hmul_ty = c.lt(c.rat_zero.clone(), c.mul(a.clone(), bv.clone()));
    let (hm_id, hmul) = b.fresh_local(hmul_ty.clone());
    let h0b_ty = c.nonneg(bv.clone());
    let (h0b_id, h0b) = b.fresh_local(h0b_ty.clone());

    let ab = c.mul(a.clone(), bv.clone());
    // not_ab_le_0 : ¬ (a·b ≤ 0)  (from hmul : 0 < a·b).
    let not_ab_le_0 = c.not_le_of_lt(c.rat_zero.clone(), ab.clone(), hmul);

    // contra : (a ≤ 0) → False.
    //   mul_le_mul_of_nonneg_right b a 0 (ha: a≤0)(h0b: 0≤b) : a·b ≤ 0·b
    //   zero_mul b : 0·b = 0 ; subst (motive t := a·b ≤ t) (0·b) 0 (zero_mul b)
    //     ⟹ a·b ≤ 0 ; not_ab_le_0 ⟹ False.
    let contra = {
        let mut bc = EnvDeclBuilder::child_of(&b);
        let hle_ty = c.le(a.clone(), c.rat_zero.clone());
        let (hle_id, hle) = bc.fresh_local(hle_ty.clone());
        // a·b ≤ 0·b.
        let ab_le_zerob =
            c.mul_le_right(bv.clone(), a.clone(), c.rat_zero.clone(), hle, h0b.clone());
        let zerob = c.mul(c.rat_zero.clone(), bv.clone());
        // motive t := a·b ≤ t.
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&bc);
            let (t_id, t) = mb.fresh_local(c.rat.clone());
            let body = c.le(ab.clone(), t);
            mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let ab_le_0 = c.subst(
            motive,
            zerob,
            c.rat_zero.clone(),
            c.zero_mul(bv.clone()),
            ab_le_zerob,
        );
        let false_pf = Expr::app(not_ab_le_0.clone(), ab_le_0);
        bc.finish_child(bc.mk_lam(hle_id, BinderInfo::Default, hle_ty, false_pf))
    };

    // p1 : 0 ≤ a  via Or.rec over (le_total 0 a):
    //   left  (w : 0≤a) => w
    //   right (hle: a≤0) => False.elim (0≤a) (contra hle).
    let le_0a = c.nonneg(a.clone());
    let le_a0 = c.le(a.clone(), c.rat_zero.clone());
    let or_total = Expr::apps(c.rat_le_total.clone(), [c.rat_zero.clone(), a.clone()]);
    let or_motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let or_ty = Expr::apps(c.or_c.clone(), [le_0a.clone(), le_a0.clone()]);
        let (h_id, _) = mb.fresh_local(or_ty.clone());
        mb.finish_child(mb.mk_lam(h_id, BinderInfo::Default, or_ty, le_0a.clone()))
    };
    let left_fn = {
        let mut lb = EnvDeclBuilder::child_of(&b);
        let (w_id, w) = lb.fresh_local(le_0a.clone());
        lb.finish_child(lb.mk_lam(w_id, BinderInfo::Default, le_0a.clone(), w))
    };
    let right_fn = {
        let mut rb = EnvDeclBuilder::child_of(&b);
        let (hle_id, hle) = rb.fresh_local(le_a0.clone());
        let false_pf = Expr::app(contra.clone(), hle);
        let body = Expr::apps(c.false_elim.clone(), [le_0a.clone(), false_pf]);
        rb.finish_child(rb.mk_lam(hle_id, BinderInfo::Default, le_a0.clone(), body))
    };
    let p1 = Expr::apps(
        c.or_rec.clone(),
        [
            le_0a.clone(),
            le_a0.clone(),
            or_motive,
            left_fn,
            right_fn,
            or_total,
        ],
    );

    // 0 < a := Iff.mpr (lt_iff_le_not_le 0 a) (And.intro (0≤a)(¬a≤0) p1 contra).
    let not_a_le_0 = c.not_(le_a0.clone());
    let and_ty = Expr::apps(c.and_c.clone(), [le_0a.clone(), not_a_le_0.clone()]);
    let and_pf = Expr::apps(c.and_intro.clone(), [le_0a.clone(), not_a_le_0, p1, contra]);
    let lt_0a = c.lt(c.rat_zero.clone(), a.clone());
    let iff_0a = Expr::apps(
        c.rat_lt_iff_le_not_le.clone(),
        [c.rat_zero.clone(), a.clone()],
    );
    let proof = Expr::apps(c.iff_mpr.clone(), [lt_0a, and_ty, iff_0a, and_pf]);

    let e = b.mk_lam(h0b_id, BinderInfo::Default, h0b_ty, proof);
    let e = b.mk_lam(hm_id, BinderInfo::Default, hmul_ty, e);
    let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// Build `Rat.deltaMul_mul_eq`.
fn build_delta_mul_mul_eq_proof(c: &DeltaChoiceConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (e_id, eps) = b.fresh_local(c.rat.clone());
    let (d_id, d) = b.fresh_local(c.rat.clone());
    let ne_ty = c.ne_zero_ty(&b, &d);
    let (ne_id, ne) = b.fresh_local(ne_ty.clone());

    let h = c.half(eps.clone()); // ε/2
    let inv_d = c.inv(d.clone());
    // δ ≡ (ε/2)/D ≡ (ε/2)·inv D  (Rat.div reducible). The goal LHS is
    // `(deltaMul ε D)·D`, which reduces to `((ε/2)·inv D)·D`.
    let h_invd = c.mul(h.clone(), inv_d.clone()); // (ε/2)·inv D

    // step1 : ((ε/2)·inv D)·D = (ε/2)·(inv D · D)   [mul_assoc (ε/2) (inv D) D].
    let step1 = c.mul_assoc(h.clone(), inv_d.clone(), d.clone());
    // step2 : (ε/2)·(inv D · D) = (ε/2)·(D · inv D)
    //   [congrArg ((ε/2)·) (mul_comm (inv D) D)].
    let invd_d = c.mul(inv_d.clone(), d.clone());
    let d_invd = c.mul(d.clone(), inv_d.clone());
    let mul_h_fn = {
        let mut fb = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = fb.fresh_local(c.rat.clone());
        let body = c.mul(h.clone(), t);
        fb.finish_child(fb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let step2 = c.congr_arg(
        invd_d.clone(),
        d_invd.clone(),
        mul_h_fn.clone(),
        c.mul_comm(inv_d.clone(), d.clone()),
    );
    // step3 : (ε/2)·(D · inv D) = (ε/2)·1   [congrArg ((ε/2)·) (mul_inv_cancel D ne)].
    let one = c.rat_one.clone();
    let step3 = c.congr_arg(
        d_invd.clone(),
        one.clone(),
        mul_h_fn,
        c.mul_inv_cancel(d.clone(), ne),
    );
    // step4 : (ε/2)·1 = ε/2   [mul_one (ε/2)].
    let step4 = c.mul_one(h.clone());

    // chain: ((ε/2)·inv D)·D  → (ε/2)·(inv D·D) → (ε/2)·(D·inv D) → (ε/2)·1 → ε/2.
    let t0 = c.mul(h_invd.clone(), d.clone());
    let t1 = c.mul(h.clone(), invd_d);
    let t2 = c.mul(h.clone(), d_invd);
    let t3 = c.mul(h.clone(), one);
    let t4 = h.clone();
    let c1 = c.eq_trans(t0.clone(), t1.clone(), t2.clone(), step1, step2);
    let c2 = c.eq_trans(t0.clone(), t2.clone(), t3.clone(), c1, step3);
    let proof = c.eq_trans(t0, t3, t4, c2, step4);

    let e = b.mk_lam(ne_id, BinderInfo::Default, ne_ty, proof);
    let e = b.mk_lam(d_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(e_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// Build `Rat.deltaMul_pos`.
fn build_delta_mul_pos_proof(c: &DeltaChoiceConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (e_id, eps) = b.fresh_local(c.rat.clone());
    let (d_id, d) = b.fresh_local(c.rat.clone());
    let h0e_ty = c.lt(c.rat_zero.clone(), eps.clone());
    let (h0e_id, h0e) = b.fresh_local(h0e_ty.clone());
    let h0d_ty = c.lt(c.rat_zero.clone(), d.clone());
    let (h0d_id, h0d) = b.fresh_local(h0d_ty.clone());

    let delta = c.delta_mul(eps.clone(), d.clone());
    let half = c.half(eps.clone());

    // D ≠ 0 : (D = 0 → False).  from h0d : 0 < D.
    //   not_d_le_0 : ¬(D ≤ 0) := And.right (Iff.mp (lt_iff 0 D) h0d).
    //   given hD0 : D = 0, subst D→0 in (0≤D from And.left) gives 0≤0... simpler:
    //   from hD0 : D = 0, transport h0d : 0 < D to 0 < 0 (motive t := 0<t), then
    //   ¬(0≤0) from lt_iff applied to 0<0, contradict le_refl 0.
    let ne_proof = {
        let mut nb = EnvDeclBuilder::child_of(&b);
        let hd0_ty = c.eq_ty(d.clone(), c.rat_zero.clone());
        let (hd0_id, hd0) = nb.fresh_local(hd0_ty.clone());
        // lt_0_0 : 0 < 0  := subst (motive t := 0 < t) D 0 hd0 h0d.
        let motive_lt = {
            let mut mb = EnvDeclBuilder::child_of(&nb);
            let (t_id, t) = mb.fresh_local(c.rat.clone());
            let body = c.lt(c.rat_zero.clone(), t);
            mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let lt_0_0 = c.subst(motive_lt, d.clone(), c.rat_zero.clone(), hd0, h0d.clone());
        // not_0_le_0 : ¬(0≤0) := And.right (Iff.mp (lt_iff 0 0) lt_0_0).
        let not_0_le_0 = c.not_le_of_lt(c.rat_zero.clone(), c.rat_zero.clone(), lt_0_0);
        // le_refl 0 : 0 ≤ 0.
        let le00 = Expr::app(c.rat_le_refl.clone(), c.rat_zero.clone());
        let false_pf = Expr::app(not_0_le_0, le00);
        nb.finish_child(nb.mk_lam(hd0_id, BinderInfo::Default, hd0_ty, false_pf))
    };

    // delta_mul_mul_eq ε D ne : δ·D = ε/2.
    let dmme = Expr::apps(
        Expr::const_(Name::from_string("Rat.deltaMul_mul_eq"), vec![]),
        [eps.clone(), d.clone(), ne_proof],
    );
    // half_pos : 0 < ε/2.
    let half_pos = c.half_pos(eps.clone(), h0e);
    // 0 < δ·D := subst (motive t := 0 < t) (ε/2) (δ·D) (symm dmme) half_pos.
    let delta_d = c.mul(delta.clone(), d.clone());
    let motive_pos = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = mb.fresh_local(c.rat.clone());
        let body = c.lt(c.rat_zero.clone(), t);
        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let pos_delta_d = c.subst(
        motive_pos,
        half.clone(),
        delta_d.clone(),
        c.eq_symm(delta_d.clone(), half.clone(), dmme),
        half_pos,
    );

    // 0 ≤ D from h0d : 0 < D  (And.left (Iff.mp (lt_iff 0 D) h0d)).
    let le_0d = {
        let le_ab = c.nonneg(d.clone());
        let not_le_ba = c.not_(c.le(d.clone(), c.rat_zero.clone()));
        let and_ty = Expr::apps(c.and_c.clone(), [le_ab.clone(), not_le_ba.clone()]);
        let lt_0d = c.lt(c.rat_zero.clone(), d.clone());
        let iff = Expr::apps(
            c.rat_lt_iff_le_not_le.clone(),
            [c.rat_zero.clone(), d.clone()],
        );
        let mp = Expr::apps(c.iff_mp.clone(), [lt_0d, and_ty, iff, h0d]);
        Expr::apps(c.and_left.clone(), [le_ab, not_le_ba, mp])
    };

    // pos_of_mul_pos_of_nonneg δ D pos_delta_d le_0d : 0 < δ.
    let proof = Expr::apps(
        Expr::const_(Name::from_string("Rat.pos_of_mul_pos_of_nonneg"), vec![]),
        [delta.clone(), d.clone(), pos_delta_d, le_0d],
    );

    let e = b.mk_lam(h0d_id, BinderInfo::Default, h0d_ty, proof);
    let e = b.mk_lam(h0e_id, BinderInfo::Default, h0e_ty, e);
    let e = b.mk_lam(d_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(e_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const DEFS: &[&str] = &["Rat.deltaMul"];
    const THEOREMS: &[&str] = &[
        "Rat.pos_of_mul_pos_of_nonneg",
        "Rat.deltaMul_mul_eq",
        "Rat.deltaMul_pos",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_rat_delta_choice()
            .expect("init_algebra_rat_delta_choice");
        env.init_algebra_rat_delta_choice().expect("idempotent");
        env
    }

    #[test]
    fn test_delta_choice_present_and_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in DEFS.iter().chain(THEOREMS.iter()) {
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
    fn test_delta_choice_theorems_constructive_empty_closure() {
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
