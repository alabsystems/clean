// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — left-multiplicative monotonicity on `NNReal`:
//! `NNReal.mul_le_mul_left`.
//!
//! # Why this module exists
//!
//! The de-square keystone `NNReal.le_of_sq_le_sq` needs the strict/non-strict
//! product monotonicity of the carrier. The non-strict left version
//!
//! ```text
//!   NNReal.mul_le_mul_left : ∀ a c d : NNReal,
//!     NNReal.le c d → NNReal.le (NNReal.mul a c)(NNReal.mul a d)
//! ```
//!
//! is the load-bearing building block. Its genuine content is the `CauSeq`-level
//! one-sided estimate (a single forward slice of the `NNReal.mul` respect proof):
//!
//! ```text
//!   CauSeq.le_mul_left : ∀ s c d, CauSeq.le c d → CauSeq.le (mul s c)(mul s d)
//! ```
//!
//! whose body, for `ε>0`, sets bounds `Bs`,`Bd` (`IsCauchy_bounded`), the band
//! `D := (Bsr+Bdr)+1`, `δ := deltaMul ε D` with `δ·(Bsr+Bdr) ≤ ε/2`, feeds the
//! one-sided closeness `vc ≤ vd+δ` (from `CauSeq.le c d` at δ) and the trivial
//! self-closeness `vs ≤ vs+δ` into `Rat.mul_close_of_close` (fixed first factor
//! `s`), obtaining `vs·vc < vs·vd + ε`, then transports both endpoints to
//! `val(seq (mul s ·) m)` via `NNRat.val_mul`. `NNReal.mul_le_mul_left` is the
//! triple `Quot.ind` lift (mirroring `NNReal.add_le_add`).
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (foundational only). NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for left mul-monotonicity.
pub(crate) struct MulMonoConsts {
    nat: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_one: Expr,
    rat_two: Expr,
    nnrat: Expr,
    nnrat_val: Expr,
    nnrat_val_mul: Expr,
    nnrat_mul: Expr,
    nnrat_property: Expr,
    causeq: Expr,
    causeq_seq: Expr,
    causeq_equiv: Expr,
    causeq_le: Expr,
    causeq_mul: Expr,
    causeq_property: Expr,
    is_cauchy_bounded: Expr,
    rat_add: Expr,
    rat_mul: Expr,
    rat_div: Expr,
    rat_lt: Expr,
    rat_le: Expr,
    nat_le: Expr,
    // Rat lemmas.
    rat_zero_lt_one: Expr,
    rat_zero_le_one: Expr,
    rat_zero_add: Expr,
    rat_add_zero: Expr,
    rat_add_le_add: Expr,
    rat_add_lt_add_left: Expr,
    rat_le_refl: Expr,
    rat_lt_of_le_of_lt: Expr,
    rat_mul_le_left: Expr,
    rat_lt_iff_le_not_le: Expr,
    rat_le_add_of_nonneg_right: Expr,
    rat_deltamul: Expr,
    rat_deltamul_pos: Expr,
    rat_deltamul_mul_eq: Expr,
    rat_mul_close: Expr,
    // Nat lemmas.
    nat_le_trans: Expr,
    // Logic.
    and_c: Expr,
    and_left: Expr,
    and_right: Expr,
    not_c: Expr,
    iff_mp: Expr,
    exists_c: Expr,
    exists_intro: Expr,
    exists_elim: Expr,
    eq_rat: Expr,
    eq_symm: Expr,
    eq_subst: Expr,
    quot_mk: Expr,
    quot_ind: Expr,
}

impl MulMonoConsts {
    pub(crate) fn new() -> Self {
        let lvl1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_one: k("Rat.one"),
            rat_two: k("Rat.two"),
            nnrat: k("NNRat"),
            nnrat_val: k("NNRat.val"),
            nnrat_val_mul: k("NNRat.val_mul"),
            nnrat_mul: k("NNRat.mul"),
            nnrat_property: k("NNRat.property"),
            causeq: k("NNReal.CauSeq"),
            causeq_seq: k("NNReal.CauSeq.seq"),
            causeq_equiv: k("NNReal.CauSeq.Equiv"),
            causeq_le: k("NNReal.CauSeq.le"),
            causeq_mul: k("NNReal.CauSeq.mul"),
            causeq_property: k("NNReal.CauSeq.property"),
            is_cauchy_bounded: k("NNReal.IsCauchy_bounded"),
            rat_add: k("Rat.add"),
            rat_mul: k("Rat.mul"),
            rat_div: k("Rat.div"),
            rat_lt: k("Rat.lt"),
            rat_le: k("Rat.le"),
            nat_le: k("Nat.le"),
            rat_zero_lt_one: k("Rat.zero_lt_one"),
            rat_zero_le_one: k("Rat.zero_le_one"),
            rat_zero_add: k("Rat.zero_add"),
            rat_add_zero: k("Rat.add_zero"),
            rat_add_le_add: k("Rat.add_le_add"),
            rat_add_lt_add_left: k("Rat.add_lt_add_left"),
            rat_le_refl: k("Rat.le_refl"),
            rat_lt_of_le_of_lt: k("Rat.lt_of_le_of_lt"),
            rat_mul_le_left: k("Rat.mul_le_mul_of_nonneg_left"),
            rat_lt_iff_le_not_le: k("Rat.lt_iff_le_not_le"),
            rat_le_add_of_nonneg_right: k("Rat.le_add_of_nonneg_right"),
            rat_deltamul: k("Rat.deltaMul"),
            rat_deltamul_pos: k("Rat.deltaMul_pos"),
            rat_deltamul_mul_eq: k("Rat.deltaMul_mul_eq"),
            rat_mul_close: k("Rat.mul_close_of_close"),
            nat_le_trans: k("Nat.le_trans"),
            and_c: k("And"),
            and_left: k("And.left"),
            and_right: k("And.right"),
            not_c: k("Not"),
            iff_mp: k("Iff.mp"),
            exists_c: Expr::const_(Name::from_string("Exists"), vec![lvl1.clone()]),
            exists_intro: Expr::const_(Name::from_string("Exists.intro"), vec![lvl1.clone()]),
            exists_elim: Expr::const_(Name::from_string("Exists.elim"), vec![lvl1.clone()]),
            eq_rat: Expr::const_(Name::from_string("Eq"), vec![lvl1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![lvl1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![lvl1.clone()]),
            quot_mk: Expr::const_(Name::from_string("Quot.mk"), vec![lvl1.clone()]),
            quot_ind: Expr::const_(Name::from_string("Quot.ind"), vec![lvl1]),
        }
    }

    fn at(&self, f: &Expr, n: &Expr) -> Expr {
        Expr::app(f.clone(), n.clone())
    }
    fn val(&self, q: Expr) -> Expr {
        Expr::app(self.nnrat_val.clone(), q)
    }
    fn seq_at(&self, x: &Expr, n: &Expr) -> Expr {
        Expr::app(Expr::app(self.causeq_seq.clone(), x.clone()), n.clone())
    }
    fn vseq(&self, x: &Expr, n: &Expr) -> Expr {
        self.val(self.seq_at(x, n))
    }
    fn radd(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn rmul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn rdiv(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_div.clone(), [a, b])
    }
    fn rlt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    fn rle(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a, b])
    }
    fn half(&self, eps: Expr) -> Expr {
        self.rdiv(eps, self.rat_two.clone())
    }
    fn nat_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a, b])
    }
    fn causeq_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.causeq_le.clone(), [a, b])
    }
    fn cau_mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.causeq_mul.clone(), [a, b])
    }
    fn property_seq(&self, x: &Expr, n: &Expr) -> Expr {
        Expr::app(self.nnrat_property.clone(), self.seq_at(x, n))
    }
    fn cau_property(&self, x: &Expr) -> Expr {
        Expr::app(self.causeq_property.clone(), x.clone())
    }
    fn seq_of(&self, x: &Expr) -> Expr {
        Expr::app(self.causeq_seq.clone(), x.clone())
    }
    fn val_mul(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.nnrat_val_mul.clone(), [p, q])
    }
    fn nnmul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nnrat_mul.clone(), [a, b])
    }
    fn nat_le_trans(&self, a: Expr, b: Expr, cc: Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(self.nat_le_trans.clone(), [a, b, cc, hab, hbc])
    }
    fn mul_le_left(&self, a: Expr, b: Expr, cc: Expr, hbc: Expr, ha: Expr) -> Expr {
        Expr::apps(self.rat_mul_le_left.clone(), [a, b, cc, hbc, ha])
    }
    fn add_le_add(&self, a: Expr, b: Expr, cc: Expr, d: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.rat_add_le_add.clone(), [a, b, cc, d, h1, h2])
    }
    fn add_lt_add_left(&self, a: Expr, b: Expr, cc: Expr, h: Expr) -> Expr {
        Expr::apps(self.rat_add_lt_add_left.clone(), [a, b, cc, h])
    }
    fn le_refl(&self, a: Expr) -> Expr {
        Expr::app(self.rat_le_refl.clone(), a)
    }
    fn lt_of_le_of_lt(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.rat_lt_of_le_of_lt.clone(), [a, b, cc, h1, h2])
    }
    fn add_zero(&self, a: Expr) -> Expr {
        Expr::app(self.rat_add_zero.clone(), a)
    }
    fn zero_add(&self, a: Expr) -> Expr {
        Expr::app(self.rat_zero_add.clone(), a)
    }
    fn le_add_of_nonneg_right(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.rat_le_add_of_nonneg_right.clone(), [a, b, h])
    }
    fn eq_ty(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq_rat.clone(), [self.rat.clone(), a, b])
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
    fn delta(&self, eps: &Expr, d: &Expr) -> Expr {
        Expr::apps(self.rat_deltamul.clone(), [eps.clone(), d.clone()])
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
    /// `∃ B, ∀ n, NNRat.le (seq f n) B` predicate body (for the bounded result).
    fn bounded_pred(&self, parent: &EnvDeclBuilder, f: &Expr) -> Expr {
        let mut pb = EnvDeclBuilder::child_of(parent);
        let (bb_id, bb) = pb.fresh_local(self.nnrat.clone());
        let inner = {
            let mut ib = EnvDeclBuilder::child_of(&pb);
            let (n_id, n) = ib.fresh_local(self.nat.clone());
            let nle = Expr::apps(
                Expr::const_(Name::from_string("NNRat.le"), vec![]),
                [self.seq_at(f, &n), bb.clone()],
            );
            ib.finish_child(ib.mk_pi(n_id, BinderInfo::Default, self.nat.clone(), nle))
        };
        pb.finish_child(pb.mk_lam(bb_id, BinderInfo::Default, self.nnrat.clone(), inner))
    }
    /// `∀ n, NNRat.le (seq f n) B` — the bound-hyp type at witness B.
    fn bound_hyp_at(&self, parent: &EnvDeclBuilder, f: &Expr, big_b: &Expr) -> Expr {
        let mut ib = EnvDeclBuilder::child_of(parent);
        let (n_id, n) = ib.fresh_local(self.nat.clone());
        let nle = Expr::apps(
            Expr::const_(Name::from_string("NNRat.le"), vec![]),
            [self.seq_at(f, &n), big_b.clone()],
        );
        ib.finish_child(ib.mk_pi(n_id, BinderInfo::Default, self.nat.clone(), nle))
    }
    /// `fun N => ∀ n, N≤n → vseq a n < vseq b n + ε`.
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
    fn exists_pred(&self, parent: &EnvDeclBuilder, a: &Expr, b: &Expr, eps: &Expr) -> Expr {
        Expr::apps(
            self.exists_c.clone(),
            [self.nat.clone(), self.pred_n(parent, a, b, eps)],
        )
    }
}

impl Environment {
    /// Register `NNReal.CauSeq.le_mul_left` and `NNReal.mul_le_mul_left`.
    /// Idempotent.
    pub fn init_algebra_nnreal_reverse_square_mono(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_mul_lift()?; // NNReal.mul, CauSeq.mul
        self.init_algebra_nnreal_le()?; // NNReal.CauSeq.le, NNReal.le (eps-form)
        self.init_algebra_nnreal_bounded()?; // IsCauchy_bounded
        self.init_algebra_rat_delta_choice()?; // deltaMul + lemmas
        self.init_algebra_rat_mul_close()?; // mul_close_of_close + the order/field surface
        self.register_rat_order_proofs()?; // zero_lt_one, le_refl
        self.register_nat_le_trans_proof()?; // Nat.le_trans
        self.init_exists()?;

        let c = MulMonoConsts::new();
        self.register_causeq_le_mul_left(&c)?;
        self.register_nnreal_mul_le_mul_left(&c)?;
        Ok(())
    }

    /// `NNReal.CauSeq.le_mul_left : ∀ s c d, CauSeq.le c d →
    ///     CauSeq.le (CauSeq.mul s c)(CauSeq.mul s d)`.
    fn register_causeq_le_mul_left(&mut self, c: &MulMonoConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.CauSeq.le_mul_left");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, s) = b.fresh_local(c.causeq.clone());
            let (cv_id, cv) = b.fresh_local(c.causeq.clone());
            let (dv_id, dv) = b.fresh_local(c.causeq.clone());
            let hcd = c.causeq_le(cv.clone(), dv.clone());
            let (hcd_id, _h) = b.fresh_local(hcd.clone());
            let concl = c.causeq_le(
                c.cau_mul(s.clone(), cv.clone()),
                c.cau_mul(s.clone(), dv.clone()),
            );
            let e = b.mk_pi(hcd_id, BinderInfo::Default, hcd, concl);
            let e = b.mk_pi(dv_id, BinderInfo::Default, c.causeq.clone(), e);
            let e = b.mk_pi(cv_id, BinderInfo::Default, c.causeq.clone(), e);
            let e = b.mk_pi(s_id, BinderInfo::Default, c.causeq.clone(), e);
            b.finish(e)
        };
        let value = build_causeq_le_mul_left(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNReal.mul_le_mul_left : ∀ a c d, NNReal.le c d →
    ///     NNReal.le (NNReal.mul a c)(NNReal.mul a d)`. Triple `Quot.ind` lift.
    fn register_nnreal_mul_le_mul_left(&mut self, c: &MulMonoConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.mul_le_mul_left");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let nnreal = c.nnreal();
        let nnle = Expr::const_(Name::from_string("NNReal.le"), vec![]);
        let nnmul = Expr::const_(Name::from_string("NNReal.mul"), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nnreal.clone());
            let (cv_id, cv) = b.fresh_local(nnreal.clone());
            let (dv_id, dv) = b.fresh_local(nnreal.clone());
            let hcd = Expr::apps(nnle.clone(), [cv.clone(), dv.clone()]);
            let (hcd_id, _h) = b.fresh_local(hcd.clone());
            let mul_ac = Expr::apps(nnmul.clone(), [a.clone(), cv.clone()]);
            let mul_ad = Expr::apps(nnmul.clone(), [a.clone(), dv.clone()]);
            let concl = Expr::apps(nnle.clone(), [mul_ac, mul_ad]);
            let e = b.mk_pi(hcd_id, BinderInfo::Default, hcd, concl);
            let e = b.mk_pi(dv_id, BinderInfo::Default, nnreal.clone(), e);
            let e = b.mk_pi(cv_id, BinderInfo::Default, nnreal.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, nnreal.clone(), e);
            b.finish(e)
        };
        let value = build_nnreal_mul_le_mul_left(c, &nnreal);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// Build the `CauSeq.le_mul_left` proof value.
fn build_causeq_le_mul_left(c: &MulMonoConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (s_id, s) = b.fresh_local(c.causeq.clone());
    let (cv_id, cv) = b.fresh_local(c.causeq.clone());
    let (dv_id, dv) = b.fresh_local(c.causeq.clone());
    let hcd_ty = c.causeq_le(cv.clone(), dv.clone());
    let (hcd_id, hcd) = b.fresh_local(hcd_ty.clone());

    // goal: CauSeq.le (mul s c)(mul s d) = ∀ ε, 0<ε → ∃ N, ∀ n, N≤n →
    //   vseq(mul s c) n < vseq(mul s d) n + ε.
    let cl = c.cau_mul(s.clone(), cv.clone());
    let cr = c.cau_mul(s.clone(), dv.clone());

    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let hpos_ty = c.rlt(c.rat_zero.clone(), eps.clone());
    let (hpos_id, hpos) = b.fresh_local(hpos_ty.clone());

    let goal_exists = c.exists_pred(&b, &cl, &cr, &eps);

    // IsCauchy_bounded (seq s)(property s) : ∃ Bs, ∀ n, NNRat.le (seq s n) Bs.
    let exists_bs = Expr::apps(
        c.is_cauchy_bounded.clone(),
        [c.seq_of(&s), c.cau_property(&s)],
    );
    let exists_bd = Expr::apps(
        c.is_cauchy_bounded.clone(),
        [c.seq_of(&dv), c.cau_property(&dv)],
    );
    let pred_bs = c.bounded_pred(&b, &s);
    let pred_bd = c.bounded_pred(&b, &dv);

    let elim_bs = {
        let mut bs = EnvDeclBuilder::child_of(&b);
        let (big_bs_id, big_bs) = bs.fresh_local(c.nnrat.clone());
        let hbs_ty = c.bound_hyp_at(&bs, &s, &big_bs);
        let (hbs_id, hbs) = bs.fresh_local(hbs_ty.clone());

        let elim_bd = {
            let mut bg = EnvDeclBuilder::child_of(&bs);
            let (big_bd_id, big_bd) = bg.fresh_local(c.nnrat.clone());
            let hbd_ty = c.bound_hyp_at(&bg, &dv, &big_bd);
            let (hbd_id, hbd) = bg.fresh_local(hbd_ty.clone());

            let bsr = c.val(big_bs.clone());
            let bdr = c.val(big_bd.clone());
            let bs_bd = c.radd(bsr.clone(), bdr.clone()); // Bsr+Bdr
            let big_d = c.radd(bs_bd.clone(), c.rat_one.clone()); // D = (Bsr+Bdr)+1
            let delta = c.delta(&eps, &big_d);
            let half_eps = c.half(eps.clone());

            // 0≤Bsr, 0≤Bdr.
            let h0bsr = Expr::app(c.nnrat_property.clone(), big_bs.clone());
            let h0bdr = Expr::app(c.nnrat_property.clone(), big_bd.clone());

            // h0bsbd : 0 ≤ Bsr+Bdr.
            let h0bsbd = {
                let step = c.add_le_add(
                    c.rat_zero.clone(),
                    bsr.clone(),
                    c.rat_zero.clone(),
                    bdr.clone(),
                    h0bsr,
                    h0bdr,
                );
                let zz = c.radd(c.rat_zero.clone(), c.rat_zero.clone());
                let motive = {
                    let mut m = EnvDeclBuilder::child_of(&bg);
                    let (t_id, t) = m.fresh_local(c.rat.clone());
                    let body = c.rle(t, bs_bd.clone());
                    m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                c.subst(
                    motive,
                    zz,
                    c.rat_zero.clone(),
                    c.zero_add(c.rat_zero.clone()),
                    step,
                )
            };

            // bsbd_lt_D : Bsr+Bdr < D.
            let bsbd_lt_d = {
                let raw = c.add_lt_add_left(
                    c.rat_zero.clone(),
                    c.rat_one.clone(),
                    bs_bd.clone(),
                    c.rat_zero_lt_one.clone(),
                );
                let bsbd_plus_zero = c.radd(bs_bd.clone(), c.rat_zero.clone());
                let motive = {
                    let mut m = EnvDeclBuilder::child_of(&bg);
                    let (t_id, t) = m.fresh_local(c.rat.clone());
                    let body = c.rlt(t, big_d.clone());
                    m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                c.subst(
                    motive,
                    bsbd_plus_zero,
                    bs_bd.clone(),
                    c.add_zero(bs_bd.clone()),
                    raw,
                )
            };

            // h0D : 0 < D.
            let h0d = c.lt_of_le_of_lt(
                c.rat_zero.clone(),
                bs_bd.clone(),
                big_d.clone(),
                h0bsbd,
                bsbd_lt_d,
            );

            // hDne : D = 0 → False.
            let hdne = {
                let mut nb = EnvDeclBuilder::child_of(&bg);
                let hd0_ty = c.eq_ty(big_d.clone(), c.rat_zero.clone());
                let (hd0_id, hd0) = nb.fresh_local(hd0_ty.clone());
                let motive = {
                    let mut m = EnvDeclBuilder::child_of(&nb);
                    let (t_id, t) = m.fresh_local(c.rat.clone());
                    let body = c.rlt(c.rat_zero.clone(), t);
                    m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                let lt00 = c.subst(motive, big_d.clone(), c.rat_zero.clone(), hd0, h0d.clone());
                let le00 = c.rle(c.rat_zero.clone(), c.rat_zero.clone());
                let not_le00 = Expr::app(c.not_c.clone(), le00.clone());
                let and00 = Expr::apps(c.and_c.clone(), [le00.clone(), not_le00.clone()]);
                let lt00ty = c.rlt(c.rat_zero.clone(), c.rat_zero.clone());
                let iff00 = Expr::apps(
                    c.rat_lt_iff_le_not_le.clone(),
                    [c.rat_zero.clone(), c.rat_zero.clone()],
                );
                let mp00 = Expr::apps(c.iff_mp.clone(), [lt00ty, and00, iff00, lt00]);
                let not_le00_pf = Expr::apps(c.and_right.clone(), [le00.clone(), not_le00, mp00]);
                let refl00 = c.le_refl(c.rat_zero.clone());
                let false_pf = Expr::app(not_le00_pf, refl00);
                nb.finish_child(nb.mk_lam(hd0_id, BinderInfo::Default, hd0_ty, false_pf))
            };

            // hδpos, h0δ, hδD.
            let hdelta_pos = Expr::apps(
                c.rat_deltamul_pos.clone(),
                [eps.clone(), big_d.clone(), hpos.clone(), h0d],
            );
            let h0delta = c.le_of_lt(c.rat_zero.clone(), delta.clone(), hdelta_pos.clone());
            let hdelta_d = Expr::apps(
                c.rat_deltamul_mul_eq.clone(),
                [eps.clone(), big_d.clone(), hdne],
            );

            // hbudget : δ·(Bsr+Bdr) ≤ ε/2.
            let hbudget = {
                let bsbd_le_d = {
                    let raw = c.add_le_add(
                        bs_bd.clone(),
                        bs_bd.clone(),
                        c.rat_zero.clone(),
                        c.rat_one.clone(),
                        c.le_refl(bs_bd.clone()),
                        c.rat_zero_le_one.clone(),
                    );
                    let bsbd_plus_zero = c.radd(bs_bd.clone(), c.rat_zero.clone());
                    let motive = {
                        let mut m = EnvDeclBuilder::child_of(&bg);
                        let (t_id, t) = m.fresh_local(c.rat.clone());
                        let body = c.rle(t, big_d.clone());
                        m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                    };
                    c.subst(
                        motive,
                        bsbd_plus_zero,
                        bs_bd.clone(),
                        c.add_zero(bs_bd.clone()),
                        raw,
                    )
                };
                let prod_le = c.mul_le_left(
                    delta.clone(),
                    bs_bd.clone(),
                    big_d.clone(),
                    bsbd_le_d,
                    h0delta.clone(),
                );
                let delta_d = c.rmul(delta.clone(), big_d.clone());
                let delta_bsbd = c.rmul(delta.clone(), bs_bd.clone());
                let motive = {
                    let mut m = EnvDeclBuilder::child_of(&bg);
                    let (t_id, t) = m.fresh_local(c.rat.clone());
                    let body = c.rle(delta_bsbd.clone(), t);
                    m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                c.subst(motive, delta_d, half_eps.clone(), hdelta_d, prod_le)
            };

            // hcd δ hδpos : ∃ Ncd, ∀ n, Ncd≤n → vc n < vd n + δ.
            let exists_ncd = Expr::apps(hcd.clone(), [delta.clone(), hdelta_pos]);
            let pred_cd = c.pred_n(&bg, &cv, &dv, &delta);

            let elim_ncd = {
                let mut bo = EnvDeclBuilder::child_of(&bg);
                let (ncd_id, ncd) = bo.fresh_local(c.nat.clone());
                let hncd_ty = c.pred_n_at(&bo, &cv, &dv, &delta, &ncd);
                let (hncd_id, hncd) = bo.fresh_local(hncd_ty.clone());

                let witness = build_witness_left(
                    c, &bo, &s, &cv, &dv, &cl, &cr, &eps, &delta, &bsr, &bdr, &hbudget, &h0delta,
                    &hpos, &hbs, &hbd, &ncd, &hncd,
                );

                let intro = Expr::apps(
                    c.exists_intro.clone(),
                    [
                        c.nat.clone(),
                        c.pred_n(&bo, &cl, &cr, &eps),
                        ncd.clone(),
                        witness,
                    ],
                );
                let e = bo.mk_lam(hncd_id, BinderInfo::Default, hncd_ty, intro);
                let e = bo.mk_lam(ncd_id, BinderInfo::Default, c.nat.clone(), e);
                bo.finish_child(e)
            };

            let elim_cd = Expr::apps(
                c.exists_elim.clone(),
                [
                    c.nat.clone(),
                    pred_cd,
                    goal_exists.clone(),
                    exists_ncd,
                    elim_ncd,
                ],
            );
            let e = bg.mk_lam(hbd_id, BinderInfo::Default, hbd_ty, elim_cd);
            let e = bg.mk_lam(big_bd_id, BinderInfo::Default, c.nnrat.clone(), e);
            bg.finish_child(e)
        };

        let elim = Expr::apps(
            c.exists_elim.clone(),
            [
                c.nnrat.clone(),
                pred_bd,
                goal_exists.clone(),
                exists_bd,
                elim_bd,
            ],
        );
        let e = bs.mk_lam(hbs_id, BinderInfo::Default, hbs_ty, elim);
        let e = bs.mk_lam(big_bs_id, BinderInfo::Default, c.nnrat.clone(), e);
        bs.finish_child(e)
    };

    let elim_outer = Expr::apps(
        c.exists_elim.clone(),
        [c.nnrat.clone(), pred_bs, goal_exists, exists_bs, elim_bs],
    );

    let e = b.mk_lam(hpos_id, BinderInfo::Default, hpos_ty, elim_outer);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(hcd_id, BinderInfo::Default, hcd_ty, e);
    let e = b.mk_lam(dv_id, BinderInfo::Default, c.causeq.clone(), e);
    let e = b.mk_lam(cv_id, BinderInfo::Default, c.causeq.clone(), e);
    let e = b.mk_lam(s_id, BinderInfo::Default, c.causeq.clone(), e);
    b.finish(e)
}

/// The witness `∀ m, N≤m → vseq(mul s c) m < vseq(mul s d) m + ε`.
#[allow(clippy::too_many_arguments)]
fn build_witness_left(
    c: &MulMonoConsts,
    parent: &EnvDeclBuilder,
    s: &Expr,
    cv: &Expr,
    dv: &Expr,
    cl: &Expr,
    cr: &Expr,
    eps: &Expr,
    delta: &Expr,
    bsr: &Expr,
    bdr: &Expr,
    hbudget: &Expr,
    h0delta: &Expr,
    hpos: &Expr,
    hbs: &Expr,
    hbd: &Expr,
    ncd: &Expr,
    hncd: &Expr,
) -> Expr {
    let mut bw = EnvDeclBuilder::child_of(parent);
    let (m_id, m) = bw.fresh_local(c.nat.clone());
    let hle_ty = c.nat_le(ncd.clone(), m.clone());
    let (hle_id, hle) = bw.fresh_local(hle_ty.clone());

    // base : vc m < vd m + δ := hncd m hle.
    let base = Expr::apps(hncd.clone(), [m.clone(), hle]);

    let vs = c.vseq(s, &m);
    let vc = c.vseq(cv, &m);
    let vd = c.vseq(dv, &m);

    // closeness le: vc ≤ vd+δ.
    let cle_cd = c.le_of_lt(vc.clone(), c.radd(vd.clone(), delta.clone()), base);
    // self-closeness: vs ≤ vs+δ.
    let cle_ss = c.le_add_of_nonneg_right(vs.clone(), delta.clone(), h0delta.clone());

    // nonneg.
    let h0vs = c.property_seq(s, &m);
    let h0vc = c.property_seq(cv, &m);
    let h0vd = c.property_seq(dv, &m);

    // bounds: vs ≤ Bsr := hbs m ; vd ≤ Bdr := hbd m.
    let bnd_vs = Expr::app(hbs.clone(), m.clone());
    let bnd_vd = Expr::app(hbd.clone(), m.clone());

    // mul_close_of_close a a' b b' Ba Bb ε δ … : a·b < a'·b' + ε.
    //   a=a'=vs, b=vc, b'=vd, Ba=Bsr, Bb=Bdr.
    //   0≤a=h0vs ; 0≤b=h0vc ; 0≤b'=h0vd ; 0≤δ=h0delta
    //   a≤Ba=bnd_vs ; b'≤Bb=bnd_vd ; a≤a'+δ=cle_ss ; b≤b'+δ=cle_cd ;
    //   budget δ·(Bsr+Bdr)≤ε/2=hbudget ; 0<ε=hpos.
    let fwd = Expr::apps(
        c.rat_mul_close.clone(),
        [
            vs.clone(),
            vs.clone(),
            vc.clone(),
            vd.clone(),
            bsr.clone(),
            bdr.clone(),
            eps.clone(),
            delta.clone(),
            h0vs,
            h0vc,
            h0vd,
            h0delta.clone(),
            bnd_vs,
            bnd_vd,
            cle_ss,
            cle_cd,
            hbudget.clone(),
            hpos.clone(),
        ],
    );

    // Transport endpoints vs·vc → val(seq(mul s c) m), vs·vd → val(seq(mul s d) m)
    // via symm (val_mul (seq s m)(seq c m)) etc.
    let vs_vc = c.rmul(vs.clone(), vc.clone());
    let vs_vd = c.rmul(vs.clone(), vd.clone());
    let seq_s = c.seq_at(s, &m);
    let seq_c = c.seq_at(cv, &m);
    let seq_d = c.seq_at(dv, &m);
    let vmul_c = c.val(c.nnmul(seq_s.clone(), seq_c.clone())); // val(mul (seq s)(seq c))
    let vmul_d = c.val(c.nnmul(seq_s.clone(), seq_d.clone()));
    let valmul_c = c.val_mul(seq_s.clone(), seq_c); // val(mul..) = vs·vc
    let valmul_d = c.val_mul(seq_s, seq_d);

    // step1: rewrite RHS summand vs·vd → vmul_d.
    let m_rhs = {
        let mut mb = EnvDeclBuilder::child_of(&bw);
        let (t_id, t) = mb.fresh_local(c.rat.clone());
        let body = c.rlt(vs_vc.clone(), c.radd(t, eps.clone()));
        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let step1 = c.subst(
        m_rhs,
        vs_vd.clone(),
        vmul_d.clone(),
        c.eq_symm(vmul_d.clone(), vs_vd.clone(), valmul_d),
        fwd,
    );
    // step2: rewrite LHS vs·vc → vmul_c.
    let m_lhs = {
        let mut mb = EnvDeclBuilder::child_of(&bw);
        let (t_id, t) = mb.fresh_local(c.rat.clone());
        let body = c.rlt(t, c.radd(vmul_d.clone(), eps.clone()));
        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let proof = c.subst(
        m_lhs,
        vs_vc.clone(),
        vmul_c.clone(),
        c.eq_symm(vmul_c, vs_vc, valmul_c),
        step1,
    );

    // `proof : val(mul (seq s)(seq c)) m < val(mul (seq s)(seq d)) m + ε`, defeq to
    // `vseq cl m < vseq cr m + ε` (cl = mul s c, cr = mul s d).
    let _ = (cl, cr);
    let e = bw.mk_lam(hle_id, BinderInfo::Default, hle_ty, proof);
    let e = bw.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
    bw.finish_child(e)
}

/// `NNReal.mul_le_mul_left` via triple `Quot.ind` reducing each leaf to the
/// `CauSeq.le_mul_left` core (mirroring `NNReal.add_le_add`).
fn build_nnreal_mul_le_mul_left(c: &MulMonoConsts, nnreal: &Expr) -> Expr {
    let core = Expr::const_(Name::from_string("NNReal.CauSeq.le_mul_left"), vec![]);
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(nnreal.clone());
    let (cv_id, cv) = b.fresh_local(nnreal.clone());
    let (dv_id, dv) = b.fresh_local(nnreal.clone());
    let nnle = Expr::const_(Name::from_string("NNReal.le"), vec![]);
    let hcd_ty = Expr::apps(nnle.clone(), [cv.clone(), dv.clone()]);
    let (hcd_id, hcd) = b.fresh_local(hcd_ty.clone());

    let body = descend_a(c, &b, nnreal, &a, &cv, &dv, &hcd, &core);

    let e = b.mk_lam(hcd_id, BinderInfo::Default, hcd_ty, body);
    let e = b.mk_lam(dv_id, BinderInfo::Default, nnreal.clone(), e);
    let e = b.mk_lam(cv_id, BinderInfo::Default, nnreal.clone(), e);
    let e = b.mk_lam(a_id, BinderInfo::Default, nnreal.clone(), e);
    b.finish(e)
}

/// Descend on `a`: motive `P a := nnle c d → nnle (mul a c)(mul a d)`.
#[allow(clippy::too_many_arguments)]
fn descend_a(
    c: &MulMonoConsts,
    parent: &EnvDeclBuilder,
    nnreal: &Expr,
    a: &Expr,
    cv: &Expr,
    dv: &Expr,
    hcd: &Expr,
    core: &Expr,
) -> Expr {
    let nnle = Expr::const_(Name::from_string("NNReal.le"), vec![]);
    let nnmul = Expr::const_(Name::from_string("NNReal.mul"), vec![]);
    let mul = |x: Expr, y: Expr| Expr::apps(nnmul.clone(), [x, y]);

    let motive = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (x_id, x) = mb.fresh_local(nnreal.clone());
        let h = Expr::apps(nnle.clone(), [cv.clone(), dv.clone()]);
        let concl = Expr::apps(
            nnle.clone(),
            [mul(x.clone(), cv.clone()), mul(x.clone(), dv.clone())],
        );
        let imp = Expr::pi(BinderInfo::Default, h, concl);
        mb.finish_child(mb.mk_lam(x_id, BinderInfo::Default, nnreal.clone(), imp))
    };
    let minor = {
        let mut mf = EnvDeclBuilder::child_of(parent);
        let (sf_id, sf) = mf.fresh_local(c.causeq.clone());
        let mks = c.quot_mk(sf.clone());
        let body = descend_c(c, &mf, nnreal, &mks, &sf, cv, dv, core);
        mf.finish_child(mf.mk_lam(sf_id, BinderInfo::Default, c.causeq.clone(), body))
    };
    let ind = Expr::apps(
        c.quot_ind.clone(),
        [
            c.causeq.clone(),
            c.causeq_equiv.clone(),
            motive,
            minor,
            a.clone(),
        ],
    );
    Expr::apps(ind, [hcd.clone()])
}

/// Descend on `c`: motive `R z := nnle z dv → nnle (mul (mk sf) z)(mul (mk sf) dv)`.
#[allow(clippy::too_many_arguments)]
fn descend_c(
    c: &MulMonoConsts,
    parent: &EnvDeclBuilder,
    nnreal: &Expr,
    mks: &Expr,
    sf: &Expr,
    cv: &Expr,
    dv: &Expr,
    core: &Expr,
) -> Expr {
    let nnle = Expr::const_(Name::from_string("NNReal.le"), vec![]);
    let nnmul = Expr::const_(Name::from_string("NNReal.mul"), vec![]);
    let mul = |x: Expr, y: Expr| Expr::apps(nnmul.clone(), [x, y]);

    let motive = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = mb.fresh_local(nnreal.clone());
        let h = Expr::apps(nnle.clone(), [z.clone(), dv.clone()]);
        let concl = Expr::apps(
            nnle.clone(),
            [mul(mks.clone(), z.clone()), mul(mks.clone(), dv.clone())],
        );
        let imp = Expr::pi(BinderInfo::Default, h, concl);
        mb.finish_child(mb.mk_lam(z_id, BinderInfo::Default, nnreal.clone(), imp))
    };
    let minor = {
        let mut mc = EnvDeclBuilder::child_of(parent);
        let (cf_id, cf) = mc.fresh_local(c.causeq.clone());
        let mkc = c.quot_mk(cf.clone());
        let body = descend_d(c, &mc, nnreal, mks, sf, &mkc, &cf, dv, core);
        mc.finish_child(mc.mk_lam(cf_id, BinderInfo::Default, c.causeq.clone(), body))
    };
    Expr::apps(
        c.quot_ind.clone(),
        [
            c.causeq.clone(),
            c.causeq_equiv.clone(),
            motive,
            minor,
            cv.clone(),
        ],
    )
}

/// Descend on `d`: motive `S w := nnle (mk cf) w → nnle (mul (mk sf)(mk cf))(mul (mk sf) w)`.
/// Leaf supplies rep `df`; the hyp reduces to `CauSeq.le cf df` and the goal to
/// `CauSeq.le (mul sf cf)(mul sf df)`, closed by `core sf cf df`.
#[allow(clippy::too_many_arguments)]
fn descend_d(
    c: &MulMonoConsts,
    parent: &EnvDeclBuilder,
    nnreal: &Expr,
    mks: &Expr,
    sf: &Expr,
    mkc: &Expr,
    cf: &Expr,
    dv: &Expr,
    core: &Expr,
) -> Expr {
    let nnle = Expr::const_(Name::from_string("NNReal.le"), vec![]);
    let nnmul = Expr::const_(Name::from_string("NNReal.mul"), vec![]);
    let mul = |x: Expr, y: Expr| Expr::apps(nnmul.clone(), [x, y]);

    let motive = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (w_id, w) = mb.fresh_local(nnreal.clone());
        let h = Expr::apps(nnle.clone(), [mkc.clone(), w.clone()]);
        let concl = Expr::apps(
            nnle.clone(),
            [mul(mks.clone(), mkc.clone()), mul(mks.clone(), w.clone())],
        );
        let imp = Expr::pi(BinderInfo::Default, h, concl);
        mb.finish_child(mb.mk_lam(w_id, BinderInfo::Default, nnreal.clone(), imp))
    };
    let minor = {
        let mut md = EnvDeclBuilder::child_of(parent);
        let (df_id, df) = md.fresh_local(c.causeq.clone());
        // hyp reduces: nnle (mk cf)(mk df) ≡ CauSeq.le cf df.
        let h_ty = c.causeq_le(cf.clone(), df.clone());
        let (h_id, h) = md.fresh_local(h_ty.clone());
        // core sf cf df h : CauSeq.le (mul sf cf)(mul sf df)
        //   ≡ nnle (mul (mk sf)(mk cf))(mul (mk sf)(mk df)).
        let body = Expr::apps(core.clone(), [sf.clone(), cf.clone(), df.clone(), h]);
        let e = md.mk_lam(h_id, BinderInfo::Default, h_ty, body);
        md.finish_child(md.mk_lam(df_id, BinderInfo::Default, c.causeq.clone(), e))
    };
    Expr::apps(
        c.quot_ind.clone(),
        [
            c.causeq.clone(),
            c.causeq_equiv.clone(),
            motive,
            minor,
            dv.clone(),
        ],
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const THEOREMS: &[&str] = &["NNReal.CauSeq.le_mul_left", "NNReal.mul_le_mul_left"];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_reverse_square_mono()
            .expect("init_algebra_nnreal_reverse_square_mono");
        env.init_algebra_nnreal_reverse_square_mono()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_reverse_square_mono_kernel_check() {
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
    fn test_reverse_square_mono_constructive_empty_closure() {
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
