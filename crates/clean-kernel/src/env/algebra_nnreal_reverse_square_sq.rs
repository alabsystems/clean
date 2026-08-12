// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — the de-square keystone `NNReal.le_of_sq_le_sq`
//! (`mul a a ≤ mul b b → a ≤ b`), plus the two pure-`Rat` bricks it stands on.
//!
//! # Why this module exists
//!
//! The de-square `W² ≤ 16·Inf³` (over Rat) ⟹ `W ≤ 4·Inf^{3/2}` (over NNReal):
//! writing the RHS square as `(4·Inf^{3/2})² = ofRat(16·Inf³)`
//! (`sqrtRat_mul_self`+`ofRat_mul`), `le_of_sq_le_sq` supplies `W ≤ 4·Inf^{3/2}`.
//!
//! # The keystone (fully constructive, boundedness-free, POINTWISE)
//!
//! ```text
//!   NNReal.le_of_sq_le_sq : ∀ a b : NNReal,
//!     NNReal.le (NNReal.mul a a)(NNReal.mul b b) → NNReal.le a b
//! ```
//!
//! At the representative level the CauSeq core is genuinely pointwise: given
//! `CauSeq.le (mul f f)(mul g g)` (i.e. `∀ε∃N∀n≥N, (vf n)² < (vg n)² + ε`) and a
//! goal tolerance `ε`, instantiate the hypothesis at `ε·ε` (`> 0` by
//! `Rat.mul_pos`); at each `n ≥ N` we have `(vf n)² < (vg n)² + ε²`, and since
//! `(vg n)² + ε² ≤ (vg n + ε)²` (`Rat.sq_add_le_add_sq`), `(vf n)² < (vg n + ε)²`,
//! whence `vf n < vg n + ε` (`Rat.lt_of_sq_lt_sq`). No boundedness, no limit
//! argument — the squared `+ε²` slack is exactly the additive `+ε` slack after
//! the square root, which the two `Rat` bricks make rigorous:
//!
//! - `Rat.sq_add_le_add_sq : ∀ y d, 0≤y → 0≤d →
//!     Rat.le (Rat.add (Rat.mul y y)(Rat.mul d d)) (Rat.mul (Rat.add y d)(Rat.add y d))`
//!   (expand `(y+d)² = (y² + d²) + (y·d + d·y)`, then `+ nonneg`).
//! - `Rat.lt_of_sq_lt_sq : ∀ x z, 0≤x → 0≤z → Rat.mul x x < Rat.mul z z → Rat.lt x z`
//!   (the strict square-root order: `le_of_sq_le_sq` gives `x ≤ z`; `x = z` would
//!   force `x² = z²`, contradicting strictness, so `x < z` via the `lt_iff` engine).
//!
//! `NNReal.le_of_sq_le_sq` is the nested `Quot.ind`² lift reducing each leaf to
//! `NNReal.CauSeq.le_of_sq_le_sq`.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (foundational only). NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for the de-square keystone.
#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
pub(crate) struct SqConsts {
    nat: Expr,
    rat: Expr,
    rat_zero: Expr,
    #[cfg(test)]
    nnrat: Expr,
    nnrat_val: Expr,
    #[cfg(test)]
    nnrat_mul: Expr,
    nnrat_property: Expr,
    causeq: Expr,
    causeq_seq: Expr,
    causeq_equiv: Expr,
    causeq_le: Expr,
    causeq_mul: Expr,
    rat_add: Expr,
    rat_mul: Expr,
    rat_lt: Expr,
    rat_le: Expr,
    nat_le: Expr,
    // Rat lemmas.
    #[cfg(test)]
    rat_mul_comm: Expr,
    rat_left_distrib: Expr,
    rat_right_distrib: Expr,
    rat_add_assoc: Expr,
    rat_add_comm: Expr,
    rat_le_refl: Expr,
    rat_add_le_add: Expr,
    rat_mul_nonneg: Expr,
    rat_mul_pos: Expr,
    rat_le_add_of_nonneg_right: Expr,
    rat_le_of_sq_le_sq: Expr,
    rat_le_antisymm: Expr,
    rat_lt_iff_le_not_le: Expr,
    rat_lt_of_lt_of_le: Expr,
    // Logic.
    and_c: Expr,
    and_intro: Expr,
    and_left: Expr,
    not_c: Expr,
    iff_mp: Expr,
    iff_mpr: Expr,
    exists_c: Expr,
    exists_intro: Expr,
    exists_elim: Expr,
    #[cfg(test)]
    eq_rat: Expr,
    eq_trans: Expr,
    eq_symm: Expr,
    eq_subst: Expr,
    congr_arg: Expr,
    quot_mk: Expr,
    quot_ind: Expr,
}

#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
impl SqConsts {
    pub(crate) fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            #[cfg(test)]
            nnrat: k("NNRat"),
            nnrat_val: k("NNRat.val"),
            #[cfg(test)]
            nnrat_mul: k("NNRat.mul"),
            nnrat_property: k("NNRat.property"),
            causeq: k("NNReal.CauSeq"),
            causeq_seq: k("NNReal.CauSeq.seq"),
            causeq_equiv: k("NNReal.CauSeq.Equiv"),
            causeq_le: k("NNReal.CauSeq.le"),
            causeq_mul: k("NNReal.CauSeq.mul"),
            rat_add: k("Rat.add"),
            rat_mul: k("Rat.mul"),
            rat_lt: k("Rat.lt"),
            rat_le: k("Rat.le"),
            nat_le: k("Nat.le"),
            #[cfg(test)]
            rat_mul_comm: k("Rat.mul_comm"),
            rat_left_distrib: k("Rat.left_distrib"),
            rat_right_distrib: k("Rat.right_distrib"),
            rat_add_assoc: k("Rat.add_assoc"),
            rat_add_comm: k("Rat.add_comm"),
            rat_le_refl: k("Rat.le_refl"),
            rat_add_le_add: k("Rat.add_le_add"),
            rat_mul_nonneg: k("Rat.mul_nonneg"),
            rat_mul_pos: k("Rat.mul_pos"),
            rat_le_add_of_nonneg_right: k("Rat.le_add_of_nonneg_right"),
            rat_le_of_sq_le_sq: k("Rat.le_of_sq_le_sq"),
            rat_le_antisymm: k("Rat.le_antisymm"),
            rat_lt_iff_le_not_le: k("Rat.lt_iff_le_not_le"),
            rat_lt_of_lt_of_le: k("Rat.lt_of_lt_of_le"),
            and_c: k("And"),
            and_intro: k("And.intro"),
            and_left: k("And.left"),
            not_c: k("Not"),
            iff_mp: k("Iff.mp"),
            iff_mpr: k("Iff.mpr"),
            exists_c: Expr::const_(Name::from_string("Exists"), vec![l1.clone()]),
            exists_intro: Expr::const_(Name::from_string("Exists.intro"), vec![l1.clone()]),
            exists_elim: Expr::const_(Name::from_string("Exists.elim"), vec![l1.clone()]),
            #[cfg(test)]
            eq_rat: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![l1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]),
            quot_mk: Expr::const_(Name::from_string("Quot.mk"), vec![l1.clone()]),
            quot_ind: Expr::const_(Name::from_string("Quot.ind"), vec![l1]),
        }
    }

    fn radd(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn rmul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn rlt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    fn rle(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a, b])
    }
    fn nonneg(&self, a: Expr) -> Expr {
        self.rle(self.rat_zero.clone(), a)
    }
    fn nat_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a, b])
    }
    fn vseq(&self, x: &Expr, n: &Expr) -> Expr {
        let seq = Expr::app(Expr::app(self.causeq_seq.clone(), x.clone()), n.clone());
        Expr::app(self.nnrat_val.clone(), seq)
    }
    fn property_seq(&self, x: &Expr, n: &Expr) -> Expr {
        let seq = Expr::app(Expr::app(self.causeq_seq.clone(), x.clone()), n.clone());
        Expr::app(self.nnrat_property.clone(), seq)
    }
    fn causeq_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.causeq_le.clone(), [a, b])
    }
    fn cau_mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.causeq_mul.clone(), [a, b])
    }
    fn left_distrib(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.rat_left_distrib.clone(), [a, b, cc])
    }
    fn right_distrib(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.rat_right_distrib.clone(), [a, b, cc])
    }
    fn add_assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.rat_add_assoc.clone(), [a, b, cc])
    }
    fn add_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add_comm.clone(), [a, b])
    }
    fn le_refl(&self, a: Expr) -> Expr {
        Expr::app(self.rat_le_refl.clone(), a)
    }
    fn add_le_add(&self, a: Expr, b: Expr, cc: Expr, d: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.rat_add_le_add.clone(), [a, b, cc, d, h1, h2])
    }
    fn mul_nonneg(&self, a: Expr, b: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(self.rat_mul_nonneg.clone(), [a, b, ha, hb])
    }
    fn mul_pos(&self, a: Expr, b: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(self.rat_mul_pos.clone(), [a, b, ha, hb])
    }
    fn le_add_of_nonneg_right(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.rat_le_add_of_nonneg_right.clone(), [a, b, h])
    }
    fn le_of_sq_le_sq(&self, a: Expr, b: Expr, ha: Expr, hb: Expr, hsq: Expr) -> Expr {
        Expr::apps(self.rat_le_of_sq_le_sq.clone(), [a, b, ha, hb, hsq])
    }
    fn le_antisymm(&self, a: Expr, b: Expr, hab: Expr, hba: Expr) -> Expr {
        Expr::apps(self.rat_le_antisymm.clone(), [a, b, hab, hba])
    }
    fn lt_of_lt_of_le(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.rat_lt_of_lt_of_le.clone(), [a, b, cc, h1, h2])
    }
    #[cfg(test)]
    fn eq_ty(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq_rat.clone(), [self.rat.clone(), a, b])
    }
    fn eq_trans(&self, a: Expr, b: Expr, cc: Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(
            self.eq_trans.clone(),
            [self.rat.clone(), a, b, cc, hab, hbc],
        )
    }
    fn eq_symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.rat.clone(), a, b, h])
    }
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h],
        )
    }
    fn congr_arg(&self, a: Expr, a2: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat.clone(), self.rat.clone(), a, a2, f, h],
        )
    }
    /// `Rat.le a b` from `hlt : Rat.lt a b`.
    fn le_of_lt(&self, a: Expr, b: Expr, hlt: Expr) -> Expr {
        let le_ab = self.rle(a.clone(), b.clone());
        let not_le_ba = Expr::app(self.not_c.clone(), self.rle(b.clone(), a.clone()));
        let and_ty = Expr::apps(self.and_c.clone(), [le_ab.clone(), not_le_ba.clone()]);
        let lt_ab = self.rlt(a.clone(), b.clone());
        let iff = Expr::apps(self.rat_lt_iff_le_not_le.clone(), [a, b]);
        let mp = Expr::apps(self.iff_mp.clone(), [lt_ab, and_ty, iff, hlt]);
        Expr::apps(self.and_left.clone(), [le_ab, not_le_ba, mp])
    }
    fn nnreal(&self) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Quot"), vec![Level::succ(Level::zero())]),
            [self.causeq.clone(), self.causeq_equiv.clone()],
        )
    }
    fn quot_mk(&self, l: Expr) -> Expr {
        Expr::apps(
            self.quot_mk.clone(),
            [self.causeq.clone(), self.causeq_equiv.clone(), l],
        )
    }
    #[cfg(test)]
    fn nnmul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nnrat_mul.clone(), [a, b])
    }
    fn pred_n(&self, parent: &EnvDeclBuilder, a: &Expr, b: &Expr, eps: &Expr) -> Expr {
        let mut bn = EnvDeclBuilder::child_of(parent);
        let (n_id, cap) = bn.fresh_local(self.nat.clone());
        let inner = self.pred_n_at(&bn, a, b, eps, &cap);
        bn.finish_child(bn.mk_lam(n_id, BinderInfo::Default, self.nat.clone(), inner))
    }
    fn pred_n_at(
        &self,
        parent: &EnvDeclBuilder,
        a: &Expr,
        b: &Expr,
        eps: &Expr,
        cap: &Expr,
    ) -> Expr {
        let mut bn = EnvDeclBuilder::child_of(parent);
        let (m_id, m) = bn.fresh_local(self.nat.clone());
        let hle = self.nat_le(cap.clone(), m.clone());
        let (hle_id, _h) = bn.fresh_local(hle.clone());
        let concl = self.rlt(self.vseq(a, &m), self.radd(self.vseq(b, &m), eps.clone()));
        let e = bn.mk_pi(hle_id, BinderInfo::Default, hle, concl);
        let e = bn.mk_pi(m_id, BinderInfo::Default, self.nat.clone(), e);
        bn.finish_child(e)
    }
    /// pred for the SQUARED hypothesis at tolerance `eps`:
    ///   `fun N => ∀ n, N≤n → (vseq (mul a a) n) < (vseq (mul b b) n) + eps`.
    fn pred_sq(&self, parent: &EnvDeclBuilder, ff: &Expr, gg: &Expr, eps: &Expr) -> Expr {
        self.pred_n(parent, ff, gg, eps)
    }
    fn exists_pred(&self, parent: &EnvDeclBuilder, a: &Expr, b: &Expr, eps: &Expr) -> Expr {
        Expr::apps(
            self.exists_c.clone(),
            [self.nat.clone(), self.pred_n(parent, a, b, eps)],
        )
    }
}

impl Environment {
    /// Register the two `Rat` bricks, the `CauSeq` core, and the `NNReal`
    /// de-square keystone `NNReal.le_of_sq_le_sq`. Idempotent.
    pub fn init_algebra_nnreal_reverse_square_sq(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_mul_lift()?; // NNReal.mul, CauSeq.mul, NNRat.*
        self.init_algebra_nnreal_le()?; // CauSeq.le, NNReal.le
        self.init_algebra_nnreal_nnrat()?; // Rat.le_of_sq_le_sq, NNRat.property/mul
        self.init_rat_field_inst()?; // left/right_distrib, add_assoc, add_comm
        self.init_rat_linear_order()?; // le_antisymm, lt_iff_le_not_le
        self.register_rat_order_proofs()?; // Rat.mul_pos, le_refl, mul_nonneg
        self.init_boolean_analysis_order_toolkit_b1c()?; // Rat.lt_of_lt_of_le
        self.init_iff()?;
        self.init_and()?;
        self.init_exists()?;

        let c = SqConsts::new();
        self.register_rat_sq_add_le_add_sq(&c)?;
        self.register_rat_lt_of_sq_lt_sq(&c)?;
        self.register_causeq_le_of_sq_le_sq(&c)?;
        self.register_nnreal_le_of_sq_le_sq(&c)?;
        Ok(())
    }

    /// `Rat.sq_add_le_add_sq : ∀ y d, 0≤y → 0≤d →
    ///     Rat.le (y·y + d·d) ((y+d)·(y+d))`.
    fn register_rat_sq_add_le_add_sq(&mut self, c: &SqConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.sq_add_le_add_sq");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (y_id, y) = b.fresh_local(c.rat.clone());
            let (d_id, d) = b.fresh_local(c.rat.clone());
            let h0y_ty = c.nonneg(y.clone());
            let (h0y_id, _h) = b.fresh_local(h0y_ty.clone());
            let h0d_ty = c.nonneg(d.clone());
            let (h0d_id, _h2) = b.fresh_local(h0d_ty.clone());
            let lhs = c.radd(c.rmul(y.clone(), y.clone()), c.rmul(d.clone(), d.clone()));
            let yd = c.radd(y.clone(), d.clone());
            let rhs = c.rmul(yd.clone(), yd);
            let concl = c.rle(lhs, rhs);
            let e = b.mk_pi(h0d_id, BinderInfo::Default, h0d_ty, concl);
            let e = b.mk_pi(h0y_id, BinderInfo::Default, h0y_ty, e);
            let e = b.mk_pi(d_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(y_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        let value = build_sq_add_le_add_sq(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.lt_of_sq_lt_sq : ∀ x z, 0≤x → 0≤z → x·x < z·z → Rat.lt x z`.
    fn register_rat_lt_of_sq_lt_sq(&mut self, c: &SqConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.lt_of_sq_lt_sq");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let (z_id, z) = b.fresh_local(c.rat.clone());
            let h0x_ty = c.nonneg(x.clone());
            let (h0x_id, _h) = b.fresh_local(h0x_ty.clone());
            let h0z_ty = c.nonneg(z.clone());
            let (h0z_id, _h2) = b.fresh_local(h0z_ty.clone());
            let hsq_ty = c.rlt(c.rmul(x.clone(), x.clone()), c.rmul(z.clone(), z.clone()));
            let (hsq_id, _h3) = b.fresh_local(hsq_ty.clone());
            let concl = c.rlt(x.clone(), z.clone());
            let e = b.mk_pi(hsq_id, BinderInfo::Default, hsq_ty, concl);
            let e = b.mk_pi(h0z_id, BinderInfo::Default, h0z_ty, e);
            let e = b.mk_pi(h0x_id, BinderInfo::Default, h0x_ty, e);
            let e = b.mk_pi(z_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        let value = build_lt_of_sq_lt_sq(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNReal.CauSeq.le_of_sq_le_sq : ∀ f g,
    ///     CauSeq.le (CauSeq.mul f f)(CauSeq.mul g g) → CauSeq.le f g`.
    fn register_causeq_le_of_sq_le_sq(&mut self, c: &SqConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.CauSeq.le_of_sq_le_sq");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(c.causeq.clone());
            let (g_id, g) = b.fresh_local(c.causeq.clone());
            let hyp = c.causeq_le(
                c.cau_mul(f.clone(), f.clone()),
                c.cau_mul(g.clone(), g.clone()),
            );
            let (h_id, _h) = b.fresh_local(hyp.clone());
            let concl = c.causeq_le(f.clone(), g.clone());
            let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
            let e = b.mk_pi(g_id, BinderInfo::Default, c.causeq.clone(), e);
            let e = b.mk_pi(f_id, BinderInfo::Default, c.causeq.clone(), e);
            b.finish(e)
        };
        let value = build_causeq_le_of_sq_le_sq(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNReal.le_of_sq_le_sq : ∀ a b, NNReal.le (mul a a)(mul b b) → NNReal.le a b`.
    fn register_nnreal_le_of_sq_le_sq(&mut self, c: &SqConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.le_of_sq_le_sq");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let nnreal = c.nnreal();
        let nnle = Expr::const_(Name::from_string("NNReal.le"), vec![]);
        let nnmul = Expr::const_(Name::from_string("NNReal.mul"), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nnreal.clone());
            let (bv_id, bv) = b.fresh_local(nnreal.clone());
            let aa = Expr::apps(nnmul.clone(), [a.clone(), a.clone()]);
            let bb = Expr::apps(nnmul.clone(), [bv.clone(), bv.clone()]);
            let hyp = Expr::apps(nnle.clone(), [aa, bb]);
            let (h_id, _h) = b.fresh_local(hyp.clone());
            let concl = Expr::apps(nnle.clone(), [a.clone(), bv.clone()]);
            let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
            let e = b.mk_pi(bv_id, BinderInfo::Default, nnreal.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, nnreal.clone(), e);
            b.finish(e)
        };
        let value = build_nnreal_le_of_sq_le_sq(c, &nnreal);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// `Rat.sq_add_le_add_sq`: `(y·y+d·d) ≤ (y+d)·(y+d)`.
///
/// Build the equation `E : (y+d)·(y+d) = (y·y+d·d)+(y·d+d·y)`, then
/// `le_add_of_nonneg_right (y·y+d·d)(y·d+d·y)(0≤y·d+d·y)` gives
/// `(y·y+d·d) ≤ (y·y+d·d)+(y·d+d·y)`; subst RHS back along `E`.
fn build_sq_add_le_add_sq(c: &SqConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (y_id, y) = b.fresh_local(c.rat.clone());
    let (d_id, d) = b.fresh_local(c.rat.clone());
    let h0y_ty = c.nonneg(y.clone());
    let (h0y_id, h0y) = b.fresh_local(h0y_ty.clone());
    let h0d_ty = c.nonneg(d.clone());
    let (h0d_id, h0d) = b.fresh_local(h0d_ty.clone());

    let yy = c.rmul(y.clone(), y.clone());
    let dd = c.rmul(d.clone(), d.clone());
    let yd = c.rmul(y.clone(), d.clone());
    let dy = c.rmul(d.clone(), y.clone());
    let yysum_dd = c.radd(yy.clone(), dd.clone()); // y·y + d·d
    let yd_dy = c.radd(yd.clone(), dy.clone()); // y·d + d·y
    let sum = c.radd(y.clone(), d.clone()); // y+d
    let prod = c.rmul(sum.clone(), sum.clone()); // (y+d)·(y+d)

    // E : (y+d)·(y+d) = (y·y + d·d) + (y·d + d·y).
    let e_eq = build_sq_expand_eq(c, &b, &y, &d);

    // 0 ≤ y·d + d·y.
    let h0yd = c.mul_nonneg(y.clone(), d.clone(), h0y.clone(), h0d.clone());
    let h0dy = c.mul_nonneg(d.clone(), y.clone(), h0d, h0y);
    let h0sum = {
        // 0 ≤ (y·d)+(d·y) : add_le_add 0 (y·d) 0 (d·y) → 0+0 ≤ (y·d)+(d·y); subst 0+0→0.
        let step = c.add_le_add(
            c.rat_zero.clone(),
            yd.clone(),
            c.rat_zero.clone(),
            dy.clone(),
            h0yd,
            h0dy,
        );
        let zz = c.radd(c.rat_zero.clone(), c.rat_zero.clone());
        // 0+0 = 0 via add_comm? use add_assoc? simplest: Rat.add_zero/zero_add 0.
        // zero_add 0 : 0+0 = 0 ; but we only imported add_comm/add_assoc. Use
        // congr-free: 0+0 reduces? Not definitional. Build via add_le_add on a
        // refl + the (0+0=0) we get from... use `c.add_comm`? No. Reuse
        // `Rat.add_zero 0`? not imported. Instead transport via `zero_add` is
        // cleanest but unimported. We import add_assoc/add_comm + field_inst gives
        // add_zero. Use add_zero 0 : 0+0 = 0.
        let add_zero0 = Expr::app(
            Expr::const_(Name::from_string("Rat.add_zero"), vec![]),
            c.rat_zero.clone(),
        );
        let motive = {
            let mut m = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = m.fresh_local(c.rat.clone());
            let body = c.rle(t, yd_dy.clone());
            m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        c.subst(motive, zz, c.rat_zero.clone(), add_zero0, step)
    };

    // le_step : (y·y+d·d) ≤ (y·y+d·d) + (y·d+d·y).
    let le_step = c.le_add_of_nonneg_right(yysum_dd.clone(), yd_dy.clone(), h0sum);
    // subst RHS (y·y+d·d)+(y·d+d·y) → (y+d)·(y+d) along symm E.
    let rhs_expanded = c.radd(yysum_dd.clone(), yd_dy.clone());
    let motive = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = m.fresh_local(c.rat.clone());
        let body = c.rle(yysum_dd.clone(), t);
        m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let e_symm = c.eq_symm(prod.clone(), rhs_expanded.clone(), e_eq);
    let proof = c.subst(motive, rhs_expanded, prod, e_symm, le_step);

    let e = b.mk_lam(h0d_id, BinderInfo::Default, h0d_ty, proof);
    let e = b.mk_lam(h0y_id, BinderInfo::Default, h0y_ty, e);
    let e = b.mk_lam(d_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(y_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// `E : (y+d)·(y+d) = (y·y + d·d) + (y·d + d·y)`.
///
/// `(y+d)·(y+d) = (y+d)·y + (y+d)·d`        [left_distrib (y+d) y d]
///             = (y·y + d·y) + (y·d + d·d)  [congrArg² right_distrib y d y / y d d]
///             = (y·y + d·d) + (y·d + d·y)  [4-term reassoc, add_assoc/add_comm]
fn build_sq_expand_eq(c: &SqConsts, parent: &EnvDeclBuilder, y: &Expr, d: &Expr) -> Expr {
    let yy = c.rmul(y.clone(), y.clone());
    let dd = c.rmul(d.clone(), d.clone());
    let yd = c.rmul(y.clone(), d.clone());
    let dy = c.rmul(d.clone(), y.clone());
    let sum = c.radd(y.clone(), d.clone());
    let prod = c.rmul(sum.clone(), sum.clone());

    // s1 : (y+d)·(y+d) = (y+d)·y + (y+d)·d   [left_distrib (y+d) y d].
    let t1 = c.radd(
        c.rmul(sum.clone(), y.clone()),
        c.rmul(sum.clone(), d.clone()),
    );
    let s1 = c.left_distrib(sum.clone(), y.clone(), d.clone());

    // inner_a : (y+d)·y = y·y + d·y   [right_distrib y d y].
    let sum_y = c.rmul(sum.clone(), y.clone());
    let yy_dy = c.radd(yy.clone(), dy.clone());
    let ra = c.right_distrib(y.clone(), d.clone(), y.clone());
    // inner_b : (y+d)·d = y·d + d·d   [right_distrib y d d].
    let sum_d = c.rmul(sum.clone(), d.clone());
    let yd_dd = c.radd(yd.clone(), dd.clone());
    let rb = c.right_distrib(y.clone(), d.clone(), d.clone());

    // s2 : (y+d)·y + (y+d)·d = (y·y+d·y) + (y+d)·d   [congrArg (·+(y+d)·d) ra].
    let add_right_fn = |t: &Expr| -> Expr {
        let mut fb = EnvDeclBuilder::child_of(parent);
        let (v_id, v) = fb.fresh_local(c.rat.clone());
        let body = c.radd(v, t.clone());
        fb.finish_child(fb.mk_lam(v_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let add_left_fn = |t: &Expr| -> Expr {
        let mut fb = EnvDeclBuilder::child_of(parent);
        let (v_id, v) = fb.fresh_local(c.rat.clone());
        let body = c.radd(t.clone(), v);
        fb.finish_child(fb.mk_lam(v_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let t2 = c.radd(yy_dy.clone(), sum_d.clone());
    let s2 = c.congr_arg(sum_y.clone(), yy_dy.clone(), add_right_fn(&sum_d), ra);
    // s3 : (y·y+d·y) + (y+d)·d = (y·y+d·y) + (y·d+d·d)   [congrArg ((y·y+d·y)+·) rb].
    let t3 = c.radd(yy_dy.clone(), yd_dd.clone());
    let s3 = c.congr_arg(sum_d.clone(), yd_dd.clone(), add_left_fn(&yy_dy), rb);

    // Now reassoc t3 = (y·y+d·y)+(y·d+d·d) → (y·y+d·d)+(y·d+d·y).
    // Use add_comm on the two inner pairs and reassoc. Do it as:
    //   (y·y+d·y)+(y·d+d·d)
    //   = y·y + (d·y + (y·d + d·d))        [add_assoc y·y d·y (y·d+d·d)]
    //   = y·y + ((d·y + y·d) + d·d)        [congr (y·y+·) symm(add_assoc d·y y·d d·d)]
    //   = y·y + ((y·d + d·y) + d·d)        [congr (y·y+·)(congr(·+d·d)(add_comm d·y y·d))]
    //   = y·y + (d·d + (y·d + d·y))        [congr (y·y+·)(add_comm (y·d+d·y) d·d)]
    //   = (y·y + d·d) + (y·d + d·y)        [symm(add_assoc y·y d·d (y·d+d·y))]
    let dy_yd_dd = c.radd(dy.clone(), yd_dd.clone()); // d·y + (y·d+d·d)
    let r1 = c.add_assoc(yy.clone(), dy.clone(), yd_dd.clone()); // (y·y+d·y)+(y·d+d·d) = y·y+(d·y+(y·d+d·d))
    let t_r1 = c.radd(yy.clone(), dy_yd_dd.clone());

    // inner: d·y+(y·d+d·d) = (d·y+y·d)+d·d  via symm(add_assoc d·y y·d d·d).
    let dyyd = c.radd(dy.clone(), yd.clone()); // d·y+y·d
    let dyyd_dd = c.radd(dyyd.clone(), dd.clone()); // (d·y+y·d)+d·d
    let assoc_dyyddd = c.add_assoc(dy.clone(), yd.clone(), dd.clone()); // (d·y+y·d)+d·d = d·y+(y·d+d·d)
    let inner2 = c.eq_symm(dyyd_dd.clone(), dy_yd_dd.clone(), assoc_dyyddd);
    let r2 = c.congr_arg(dy_yd_dd.clone(), dyyd_dd.clone(), add_left_fn(&yy), inner2);
    let t_r2 = c.radd(yy.clone(), dyyd_dd.clone());

    // inner: (d·y+y·d) = (y·d+d·y)  via add_comm d·y y·d.
    let ydddy = c.radd(yd.clone(), dy.clone()); // y·d+d·y
    let comm_dyyd = c.add_comm(dy.clone(), yd.clone()); // d·y+y·d = y·d+d·y
    let inner3 = c.congr_arg(dyyd.clone(), ydddy.clone(), add_right_fn(&dd), comm_dyyd);
    // r3 : y·y + ((d·y+y·d)+d·d) = y·y + ((y·d+d·y)+d·d).
    let ydddy_dd = c.radd(ydddy.clone(), dd.clone()); // (y·d+d·y)+d·d
    let r3 = c.congr_arg(dyyd_dd.clone(), ydddy_dd.clone(), add_left_fn(&yy), inner3);
    let t_r3 = c.radd(yy.clone(), ydddy_dd.clone());

    // inner: (y·d+d·y)+d·d = d·d+(y·d+d·y)  via add_comm (y·d+d·y) d·d.
    let dd_ydddy = c.radd(dd.clone(), ydddy.clone()); // d·d+(y·d+d·y)
    let comm4 = c.add_comm(ydddy.clone(), dd.clone()); // (y·d+d·y)+d·d = d·d+(y·d+d·y)
    let r4 = c.congr_arg(ydddy_dd.clone(), dd_ydddy.clone(), add_left_fn(&yy), comm4);
    let t_r4 = c.radd(yy.clone(), dd_ydddy.clone());

    // r5 : y·y + (d·d+(y·d+d·y)) = (y·y+d·d) + (y·d+d·y)  via symm(add_assoc y·y d·d (y·d+d·y)).
    let final_rhs = c.radd(c.radd(yy.clone(), dd.clone()), ydddy.clone());
    let assoc5 = c.add_assoc(yy.clone(), dd.clone(), ydddy.clone()); // (y·y+d·d)+(y·d+d·y) = y·y+(d·d+(y·d+d·y))
    let r5 = c.eq_symm(final_rhs.clone(), t_r4.clone(), assoc5);

    // Chain: prod =s1= t1 =s2= t2 =s3= t3 =r1= t_r1 =r2= t_r2 =r3= t_r3 =r4= t_r4 =r5= final_rhs.
    let ch = c.eq_trans(prod.clone(), t1.clone(), t2.clone(), s1, s2);
    let ch = c.eq_trans(prod.clone(), t2.clone(), t3.clone(), ch, s3);
    let ch = c.eq_trans(prod.clone(), t3.clone(), t_r1.clone(), ch, r1);
    let ch = c.eq_trans(prod.clone(), t_r1.clone(), t_r2.clone(), ch, r2);
    let ch = c.eq_trans(prod.clone(), t_r2.clone(), t_r3.clone(), ch, r3);
    let ch = c.eq_trans(prod.clone(), t_r3.clone(), t_r4.clone(), ch, r4);
    c.eq_trans(prod, t_r4, final_rhs, ch, r5)
}

/// `Rat.lt_of_sq_lt_sq`: `x < z` from `x·x < z·z` (nonneg `x,z`).
fn build_lt_of_sq_lt_sq(c: &SqConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(c.rat.clone());
    let (z_id, z) = b.fresh_local(c.rat.clone());
    let h0x_ty = c.nonneg(x.clone());
    let (h0x_id, h0x) = b.fresh_local(h0x_ty.clone());
    let h0z_ty = c.nonneg(z.clone());
    let (h0z_id, h0z) = b.fresh_local(h0z_ty.clone());
    let xx = c.rmul(x.clone(), x.clone());
    let zz = c.rmul(z.clone(), z.clone());
    let hsq_ty = c.rlt(xx.clone(), zz.clone());
    let (hsq_id, hsq) = b.fresh_local(hsq_ty.clone());

    // h_le : x ≤ z  := le_of_sq_le_sq x z h0x h0z (le_of_lt hsq).
    let hsq_le = c.le_of_lt(xx.clone(), zz.clone(), hsq.clone());
    let h_le = c.le_of_sq_le_sq(x.clone(), z.clone(), h0x.clone(), h0z.clone(), hsq_le);

    // not_zx : ¬ (z ≤ x).
    let not_zx = {
        let mut nb = EnvDeclBuilder::child_of(&b);
        let hzx_ty = c.rle(z.clone(), x.clone());
        let (hzx_id, hzx) = nb.fresh_local(hzx_ty.clone());
        // x = z via antisymm x z h_le hzx.
        let x_eq_z = c.le_antisymm(x.clone(), z.clone(), h_le.clone(), hzx);
        // x·x = z·z : congrArg² — first x·x = x·z (congr (x··) x_eq_z), then x·z=z·z.
        // Build x·x = z·z directly: motive t := (x·x = t·t)? Use subst on hsq.
        // Transport hsq : x·x < z·z to z·z < z·z by rewriting x·x → z·z via
        //   xx_eq_zz : x·x = z·z. Build xx_eq_zz from x_eq_z.
        //   xx_eq_xz : x·x = x·z  (congr (x··) x_eq_z) ; xz_eq_zz : x·z = z·z (congr (·z) x_eq_z).
        let mul_xleft = |_t: &Expr| -> Expr {
            let mut fb = EnvDeclBuilder::child_of(&nb);
            let (v_id, v) = fb.fresh_local(c.rat.clone());
            let body = c.rmul(x.clone(), v);
            fb.finish_child(fb.mk_lam(v_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let mul_zright = |_t: &Expr| -> Expr {
            let mut fb = EnvDeclBuilder::child_of(&nb);
            let (v_id, v) = fb.fresh_local(c.rat.clone());
            let body = c.rmul(v, z.clone());
            fb.finish_child(fb.mk_lam(v_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let xz = c.rmul(x.clone(), z.clone());
        let xx_eq_xz = c.congr_arg(x.clone(), z.clone(), mul_xleft(&x), x_eq_z.clone()); // x·x = x·z
        let xz_eq_zz = c.congr_arg(x.clone(), z.clone(), mul_zright(&z), x_eq_z); // x·z = z·z
        let xx_eq_zz = c.eq_trans(xx.clone(), xz, zz.clone(), xx_eq_xz, xz_eq_zz);
        // subst hsq : x·x < z·z  along xx_eq_zz to get z·z < z·z.
        let motive = {
            let mut m = EnvDeclBuilder::child_of(&nb);
            let (t_id, t) = m.fresh_local(c.rat.clone());
            let body = c.rlt(t, zz.clone());
            m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let zz_lt_zz = c.subst(motive, xx.clone(), zz.clone(), xx_eq_zz, hsq.clone());
        // ¬(z·z ≤ z·z) := And.right (Iff.mp (lt_iff z·z z·z) zz_lt_zz).
        let le_zz = c.rle(zz.clone(), zz.clone());
        let not_le_zz = Expr::app(c.not_c.clone(), le_zz.clone());
        let and_zz = Expr::apps(c.and_c.clone(), [le_zz.clone(), not_le_zz.clone()]);
        let lt_zz_ty = c.rlt(zz.clone(), zz.clone());
        let iff_zz = Expr::apps(c.rat_lt_iff_le_not_le.clone(), [zz.clone(), zz.clone()]);
        let mp_zz = Expr::apps(c.iff_mp.clone(), [lt_zz_ty, and_zz, iff_zz, zz_lt_zz]);
        let and_right = Expr::const_(Name::from_string("And.right"), vec![]);
        let not_le_zz_pf = Expr::apps(and_right, [le_zz.clone(), not_le_zz, mp_zz]);
        // apply to le_refl (z·z) : False.
        let false_pf = Expr::app(not_le_zz_pf, c.le_refl(zz.clone()));
        nb.finish_child(nb.mk_lam(hzx_id, BinderInfo::Default, hzx_ty, false_pf))
    };

    // x < z := Iff.mpr (lt_iff x z) (And.intro (x≤z) ¬(z≤x) h_le not_zx).
    let le_xz = c.rle(x.clone(), z.clone());
    let not_le_zx = Expr::app(c.not_c.clone(), c.rle(z.clone(), x.clone()));
    let and_pf = Expr::apps(
        c.and_intro.clone(),
        [le_xz.clone(), not_le_zx.clone(), h_le, not_zx],
    );
    let and_ty = Expr::apps(c.and_c.clone(), [le_xz, not_le_zx]);
    let lt_xz_ty = c.rlt(x.clone(), z.clone());
    let iff_xz = Expr::apps(c.rat_lt_iff_le_not_le.clone(), [x.clone(), z.clone()]);
    let proof = Expr::apps(c.iff_mpr.clone(), [lt_xz_ty, and_ty, iff_xz, and_pf]);

    let e = b.mk_lam(hsq_id, BinderInfo::Default, hsq_ty, proof);
    let e = b.mk_lam(h0z_id, BinderInfo::Default, h0z_ty, e);
    let e = b.mk_lam(h0x_id, BinderInfo::Default, h0x_ty, e);
    let e = b.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// `NNReal.CauSeq.le_of_sq_le_sq` proof value.
fn build_causeq_le_of_sq_le_sq(c: &SqConsts) -> Expr {
    let lt_of_sq = Expr::const_(Name::from_string("Rat.lt_of_sq_lt_sq"), vec![]);
    let sq_add = Expr::const_(Name::from_string("Rat.sq_add_le_add_sq"), vec![]);

    let mut b = EnvDeclBuilder::new();
    let (f_id, f) = b.fresh_local(c.causeq.clone());
    let (g_id, g) = b.fresh_local(c.causeq.clone());
    let ff = c.cau_mul(f.clone(), f.clone());
    let gg = c.cau_mul(g.clone(), g.clone());
    let hyp_ty = c.causeq_le(ff.clone(), gg.clone());
    let (hyp_id, hyp) = b.fresh_local(hyp_ty.clone());

    // goal: CauSeq.le f g = ∀ ε, 0<ε → ∃ N, ∀ n, N≤n → vf n < vg n + ε.
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let hpos_ty = c.rlt(c.rat_zero.clone(), eps.clone());
    let (hpos_id, hpos) = b.fresh_local(hpos_ty.clone());

    // ε·ε > 0 (mul_pos eps eps hpos hpos).
    let eps_sq = c.rmul(eps.clone(), eps.clone());
    let h_eps_sq_pos = c.mul_pos(eps.clone(), eps.clone(), hpos.clone(), hpos.clone());

    // hyp (ε·ε) (>0) : ∃ N, ∀ n, N≤n → vseq(mul f f) n < vseq(mul g g) n + ε·ε.
    let exists_src = Expr::apps(hyp.clone(), [eps_sq.clone(), h_eps_sq_pos]);
    let pred_src = c.pred_sq(&b, &ff, &gg, &eps_sq);
    let goal_exists = c.exists_pred(&b, &f, &g, &eps);

    let elim_fn = {
        let mut be = EnvDeclBuilder::child_of(&b);
        let (cap_id, cap) = be.fresh_local(c.nat.clone());
        let hn_ty = c.pred_n_at(&be, &ff, &gg, &eps_sq, &cap);
        let (hn_id, hn) = be.fresh_local(hn_ty.clone());

        let witness = {
            let mut bw = EnvDeclBuilder::child_of(&be);
            let (m_id, m) = bw.fresh_local(c.nat.clone());
            let hle_ty = c.nat_le(cap.clone(), m.clone());
            let (hle_id, hle) = bw.fresh_local(hle_ty.clone());

            // base : vseq(mul f f) m < vseq(mul g g) m + ε·ε := hn m hle.
            // vseq(mul f f) m ≡ vf·vf ; vseq(mul g g) m ≡ vg·vg (val_mul defeq).
            let base = Expr::apps(hn.clone(), [m.clone(), hle]);
            let vf = c.vseq(&f, &m);
            let vg = c.vseq(&g, &m);
            let vf_sq = c.rmul(vf.clone(), vf.clone());
            let vg_sq = c.rmul(vg.clone(), vg.clone());

            // 0≤vf, 0≤vg (property); 0≤ε from hpos? need 0≤ε for sq_add d=ε.
            let h0vf = c.property_seq(&f, &m);
            let h0vg = c.property_seq(&g, &m);
            let h0eps = c.le_of_lt(c.rat_zero.clone(), eps.clone(), hpos.clone());

            // sq_add vg ε (0≤vg)(0≤ε) : vg·vg + ε·ε ≤ (vg+ε)·(vg+ε).
            let h_sqadd = Expr::apps(
                sq_add.clone(),
                [vg.clone(), eps.clone(), h0vg.clone(), h0eps],
            );

            // base : vf·vf < vg·vg + ε·ε (defeq). Chain with sq_add via lt_of_lt_of_le:
            //   vf·vf < (vg+ε)·(vg+ε).
            let vgg_eps = c.radd(vg_sq.clone(), eps_sq.clone()); // vg·vg + ε·ε
            let vg_eps = c.radd(vg.clone(), eps.clone());
            let vg_eps_sq = c.rmul(vg_eps.clone(), vg_eps.clone());
            let vf_sq_lt_prod = c.lt_of_lt_of_le(
                vf_sq.clone(),
                vgg_eps.clone(),
                vg_eps_sq.clone(),
                base,
                h_sqadd,
            );

            // 0 ≤ vg+ε := le? need 0≤vg+ε. add_le_add 0 vg 0 ε → 0+0≤vg+ε; subst 0+0→0.
            let h0vgeps = {
                let step = c.add_le_add(
                    c.rat_zero.clone(),
                    vg.clone(),
                    c.rat_zero.clone(),
                    eps.clone(),
                    h0vg.clone(),
                    c.le_of_lt(c.rat_zero.clone(), eps.clone(), hpos.clone()),
                );
                let zz = c.radd(c.rat_zero.clone(), c.rat_zero.clone());
                let add_zero0 = Expr::app(
                    Expr::const_(Name::from_string("Rat.add_zero"), vec![]),
                    c.rat_zero.clone(),
                );
                let motive = {
                    let mut m2 = EnvDeclBuilder::child_of(&bw);
                    let (t_id, t) = m2.fresh_local(c.rat.clone());
                    let body = c.rle(t, vg_eps.clone());
                    m2.finish_child(m2.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                c.subst(motive, zz, c.rat_zero.clone(), add_zero0, step)
            };

            // lt_of_sq_lt_sq vf (vg+ε) (0≤vf)(0≤vg+ε)(vf·vf < (vg+ε)²) : vf < vg+ε.
            let proof = Expr::apps(
                lt_of_sq.clone(),
                [vf.clone(), vg_eps.clone(), h0vf, h0vgeps, vf_sq_lt_prod],
            );
            let _ = vf_sq;

            let e = bw.mk_lam(hle_id, BinderInfo::Default, hle_ty, proof);
            let e = bw.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
            bw.finish_child(e)
        };

        let intro = Expr::apps(
            c.exists_intro.clone(),
            [
                c.nat.clone(),
                c.pred_n(&be, &f, &g, &eps),
                cap.clone(),
                witness,
            ],
        );
        let e = be.mk_lam(hn_id, BinderInfo::Default, hn_ty, intro);
        let e = be.mk_lam(cap_id, BinderInfo::Default, c.nat.clone(), e);
        be.finish_child(e)
    };

    let elim = Expr::apps(
        c.exists_elim.clone(),
        [c.nat.clone(), pred_src, goal_exists, exists_src, elim_fn],
    );

    let e = b.mk_lam(hpos_id, BinderInfo::Default, hpos_ty, elim);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(hyp_id, BinderInfo::Default, hyp_ty, e);
    let e = b.mk_lam(g_id, BinderInfo::Default, c.causeq.clone(), e);
    let e = b.mk_lam(f_id, BinderInfo::Default, c.causeq.clone(), e);
    b.finish(e)
}

/// `NNReal.le_of_sq_le_sq` via nested `Quot.ind` reducing the leaf to the core.
fn build_nnreal_le_of_sq_le_sq(c: &SqConsts, nnreal: &Expr) -> Expr {
    let core = Expr::const_(Name::from_string("NNReal.CauSeq.le_of_sq_le_sq"), vec![]);
    let nnle = Expr::const_(Name::from_string("NNReal.le"), vec![]);
    let nnmul = Expr::const_(Name::from_string("NNReal.mul"), vec![]);
    let mul = |x: Expr, y: Expr| Expr::apps(nnmul.clone(), [x, y]);

    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(nnreal.clone());
    let (bv_id, bv) = b.fresh_local(nnreal.clone());
    let hyp_ty = Expr::apps(
        nnle.clone(),
        [mul(a.clone(), a.clone()), mul(bv.clone(), bv.clone())],
    );
    let (hyp_id, hyp) = b.fresh_local(hyp_ty.clone());

    // motive over a: P a := nnle (mul a a)(mul bv bv) → nnle a bv.
    let motive_a = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = mb.fresh_local(nnreal.clone());
        let h = Expr::apps(
            nnle.clone(),
            [mul(x.clone(), x.clone()), mul(bv.clone(), bv.clone())],
        );
        let concl = Expr::apps(nnle.clone(), [x.clone(), bv.clone()]);
        let imp = Expr::pi(BinderInfo::Default, h, concl);
        mb.finish_child(mb.mk_lam(x_id, BinderInfo::Default, nnreal.clone(), imp))
    };
    let minor_a = {
        let mut mf = EnvDeclBuilder::child_of(&b);
        let (f_id, f) = mf.fresh_local(c.causeq.clone());
        let mkf = c.quot_mk(f.clone());
        // descend on bv.
        let motive_b = {
            let mut mb = EnvDeclBuilder::child_of(&mf);
            let (y_id, y) = mb.fresh_local(nnreal.clone());
            let h = Expr::apps(
                nnle.clone(),
                [mul(mkf.clone(), mkf.clone()), mul(y.clone(), y.clone())],
            );
            let concl = Expr::apps(nnle.clone(), [mkf.clone(), y.clone()]);
            let imp = Expr::pi(BinderInfo::Default, h, concl);
            mb.finish_child(mb.mk_lam(y_id, BinderInfo::Default, nnreal.clone(), imp))
        };
        let minor_b = {
            let mut mg = EnvDeclBuilder::child_of(&mf);
            let (g_id, g) = mg.fresh_local(c.causeq.clone());
            // leaf: hyp reduces to CauSeq.le (mul f f)(mul g g); goal to CauSeq.le f g.
            let h_ty = c.causeq_le(
                c.cau_mul(f.clone(), f.clone()),
                c.cau_mul(g.clone(), g.clone()),
            );
            let (h_id, h) = mg.fresh_local(h_ty.clone());
            let body = Expr::apps(core.clone(), [f.clone(), g.clone(), h]);
            let e = mg.mk_lam(h_id, BinderInfo::Default, h_ty, body);
            mg.finish_child(mg.mk_lam(g_id, BinderInfo::Default, c.causeq.clone(), e))
        };
        let ind_b = Expr::apps(
            c.quot_ind.clone(),
            [
                c.causeq.clone(),
                c.causeq_equiv.clone(),
                motive_b,
                minor_b,
                bv.clone(),
            ],
        );
        mf.finish_child(mf.mk_lam(f_id, BinderInfo::Default, c.causeq.clone(), ind_b))
    };
    let ind_a = Expr::apps(
        c.quot_ind.clone(),
        [
            c.causeq.clone(),
            c.causeq_equiv.clone(),
            motive_a,
            minor_a,
            a.clone(),
        ],
    );
    let applied = Expr::apps(ind_a, [hyp.clone()]);

    let e = b.mk_lam(hyp_id, BinderInfo::Default, hyp_ty, applied);
    let e = b.mk_lam(bv_id, BinderInfo::Default, nnreal.clone(), e);
    let e = b.mk_lam(a_id, BinderInfo::Default, nnreal.clone(), e);
    b.finish(e)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const THEOREMS: &[&str] = &[
        "Rat.sq_add_le_add_sq",
        "Rat.lt_of_sq_lt_sq",
        "NNReal.CauSeq.le_of_sq_le_sq",
        "NNReal.le_of_sq_le_sq",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_reverse_square_sq()
            .expect("init_algebra_nnreal_reverse_square_sq");
        env.init_algebra_nnreal_reverse_square_sq()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_reverse_square_sq_kernel_check() {
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
    fn test_reverse_square_sq_constructive_empty_closure() {
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
